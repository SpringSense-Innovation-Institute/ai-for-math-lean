#!/usr/bin/env python3
"""Repeatable local audit. This is not Palomar's protected Linux workflow."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parent.parent


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def inputs():
    files = [p for p in ROOT.rglob('*.lean') if '.lake' not in p.parts]
    files += [ROOT / n for n in ('lean-toolchain', 'lakefile.toml',
              'lake-manifest.json', 'comparator.json', 'formalization.yaml')]
    files += list((ROOT / 'scripts').glob('*.py'))
    if (ROOT / 'LICENSE').exists():
        files.append(ROOT / 'LICENSE')
    return {str(p.relative_to(ROOT)): digest(p) for p in sorted(set(files))}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True,
                        help='Fresh directory for complete logs and receipt')
    parser.add_argument('--skip-build', action='store_true',
                        help='Reuse an existing project build; receipt records this')
    args = parser.parse_args()
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=False)
    before = inputs()
    receipt = {'profile': 'local-unsandboxed-macos', 'input_sha256': before,
               'checks': {}, 'official_protected_preflight': 'NOT_RUN',
               'build_reused': args.skip_build}
    identity = subprocess.run(['git', 'rev-parse', 'HEAD'], cwd=ROOT,
                              capture_output=True, text=True)
    receipt['verified_code_commit'] = identity.stdout.strip() if identity.returncode == 0 else None
    receipt['lean_version'] = subprocess.check_output(['lean', '--version'], cwd=ROOT, text=True).strip()
    prefix = Path(subprocess.check_output(['lean', '--print-prefix'], cwd=ROOT, text=True).strip())
    tool_names = ['lean', 'lake', 'leanexport', 'leanchecker', 'nanoda_bin', 'con-ron']
    receipt['tool_sha256'] = {name: digest(prefix / 'bin' / name) for name in tool_names}
    failed = False

    def run(name, command, *, cwd=ROOT, env=None):
        nonlocal failed
        start = time.monotonic()
        log = out / (name + '.log')
        with log.open('w') as stream:
            proc = subprocess.run(command, cwd=cwd, env=env,
                                  stdout=stream, stderr=subprocess.STDOUT)
        receipt['checks'][name] = {'status': 'PASS' if proc.returncode == 0 else 'FAIL',
            'command': command, 'exit_code': proc.returncode,
            'elapsed_seconds': round(time.monotonic() - start, 2),
            'evidence': str(log), 'transcript_sha256': digest(log)}
        print(name, receipt['checks'][name]['status'], flush=True)
        failed |= proc.returncode != 0
        return proc.returncode == 0

    try:
        lean_path = subprocess.check_output(['lake', 'env', 'printenv', 'LEAN_PATH'],
                                            cwd=ROOT, text=True).strip()
        dependency_paths = [p for p in lean_path.split(os.pathsep)
                            if Path(p).resolve() != (ROOT / '.lake/build/lib/lean').resolve()]
        with tempfile.TemporaryDirectory(prefix='erdos448-statement-') as temporary:
            statement = Path(temporary) / 'Challenge.lean'
            statement.write_bytes((ROOT / 'Challenge.lean').read_bytes())
            env = dict(os.environ, LEAN_PATH=os.pathsep.join(dependency_paths))
            proceed = run('independent_challenge', [str(prefix / 'bin/lean'),
                '--root=' + temporary, str(statement)], cwd=Path(temporary), env=env)
            receipt['checks']['independent_challenge']['dependency_paths'] = dependency_paths
        proceed = proceed and (args.skip_build or run('project_build', ['lake', 'build']))
        if proceed:
            proceed = run('exact_type_and_axioms', ['lake', 'env', 'lean', 'scripts/Check.lean'])
            if proceed:
                log_text = (out / 'exact_type_and_axioms.log').read_text()
                reports = re.findall(r"depends on axioms: \[([^\]]*)\]", log_text)
                allowed = {'propext', 'Classical.choice', 'Quot.sound'}
                proceed = len(reports) == 2 and all(
                    set(x.strip() for x in report.split(',')) <= allowed for report in reports)
                if not proceed:
                    failed = True
                    receipt['checks']['exact_type_and_axioms']['status'] = 'FAIL'
                    receipt['checks']['exact_type_and_axioms']['reason'] = 'Missing or forbidden transitive-axiom report'
        if proceed:
            config = json.loads((ROOT / 'comparator.json').read_text())
            config['external_kernels'] = {
                'nanoda': [str(prefix / 'bin' / 'nanoda_bin')],
                'con-ron': [str(prefix / 'bin' / 'con-ron')]}
            with tempfile.TemporaryDirectory(prefix='erdos448-kernels-') as temporary:
                temporary_config = Path(temporary) / 'comparator.json'
                temporary_config.write_text(json.dumps(config, indent=2) + '\n')
                run('comparator_and_independent_kernels', ['lake', 'comparator',
                    '--inadvisably-no-sandbox', '--config', str(temporary_config)])
    finally:
        receipt['inputs_unchanged'] = inputs() == before
        if not receipt['inputs_unchanged']:
            failed = True
        receipt['status'] = 'FAIL' if failed else 'PASS'
        (out / 'receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
    return int(failed)


if __name__ == '__main__':
    sys.exit(main())
