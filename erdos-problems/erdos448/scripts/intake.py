#!/usr/bin/env python3
"""Read-only local use of the pinned official intake functions, not preflight."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parent.parent


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--contract', required=True, type=Path,
                        help='Checkout of the pinned PalomarSubmission revision')
    args = parser.parse_args()
    contract = args.contract.resolve()
    lock = json.loads((ROOT / 'stage8/policy-lock.json').read_text())
    revision = subprocess.check_output(['git', '-C', str(contract), 'rev-parse', 'HEAD'], text=True).strip()
    if revision != lock['PalomarSubmission']['revision']:
        raise SystemExit('Contract revision differs from policy-lock.json')
    for name in ['toolchains.json', 'formalization-profile.json',
                 'verification-profile.json', 'allowed-challenge-repositories.json',
                 'browser-preflight-policy.json']:
        actual = hashlib.sha256((contract / name).read_bytes()).hexdigest()
        if actual != lock[name]['sha256']:
            raise SystemExit('Contract contents differ: ' + name)
    if subprocess.check_output(['git', '-C', str(contract), 'status', '--porcelain'], text=True).strip():
        raise SystemExit('Contract checkout has modifications')
    sys.path.insert(0, str(contract))
    from scripts.source_requirements import inspect_lean_sources
    from scripts.submission_contract import load_formalization_metadata
    from scripts.verify_submission import (load_comparator_config,
        manifest_packages, supported_toolchain, repository_license_file)
    from scripts.verification_errors import FormalizationValidationError, VerificationError
    summary, issues = inspect_lean_sources(ROOT)
    print('source_requirements:', json.dumps(summary), flush=True)
    checks = {
        'metadata': lambda: load_formalization_metadata(ROOT / 'formalization.yaml'),
        'comparator_config': lambda: load_comparator_config(ROOT / 'comparator.json'),
        'toolchain_floor': lambda: supported_toolchain((ROOT / 'lean-toolchain').read_text().strip()),
        'dependency_pins': lambda: manifest_packages(ROOT),
        'root_license_presence': lambda: repository_license_file(ROOT),
    }
    for name, action in checks.items():
        try:
            action()
            print(name + ': PASS', flush=True)
        except FormalizationValidationError as error:
            issues.extend(error.issues)
        except VerificationError as error:
            issues.append(error)
    for issue in issues:
        print(json.dumps(issue.diagnostic('local-intake'), ensure_ascii=False), flush=True)
    print('This is an intake subset. SPDX detection, trusted Challenge isolation,')
    print('Linux protection and official workflow execution are separate gates.')
    return int(bool(issues))


if __name__ == '__main__':
    sys.exit(main())
