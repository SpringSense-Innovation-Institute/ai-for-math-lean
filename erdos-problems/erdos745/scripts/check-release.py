#!/usr/bin/env python3
"""Audit release sources; --official invokes the pinned Palomar intake validators."""
import argparse
import hashlib
import json
import os
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
BASELINE = "d3c8e613b32839d1221d79d1bf5b5fb7da06fe87"
REFERENCE_TOKEN_HASH = '0baa7554722c91b8b4ef9f5499abdcf06d27cb3af977936fcb1c7b1c2db95a78'
SUBMISSION_REVISION = "65f0154ed776cd26c224254aa57b379137f28b0d"

def strip_comments(text):
    """Remove nested Lean comments while preserving strings and newlines."""
    output, i, depth, string = [], 0, 0, False
    while i < len(text):
        if depth:
            if text[i:i+2] == '/-': depth += 1; i += 2
            elif text[i:i+2] == '-/': depth -= 1; i += 2
            else:
                if text[i] == '\n': output.append('\n')
                i += 1
        elif string:
            output.append(text[i])
            if text[i] == '\\' and i+1 < len(text): output.append(text[i+1]); i += 2
            else:
                if text[i] == '"': string = False
                i += 1
        elif text[i:i+2] == '/-': depth = 1; output.append(' '); i += 2
        elif text[i:i+2] == '--':
            end = text.find('\n', i); i = len(text) if end < 0 else end
        else:
            if text[i] == '"': string = True
            output.append(text[i]); i += 1
    assert depth == 0
    return ''.join(output)

def definitions(path):
    text = strip_comments(path.read_text())
    text = re.sub(r'^local instance.*\n', '', text, flags=re.M)
    starts = list(re.finditer(r'^(?:def|abbrev) (\w+)', text, re.M))
    result = {}
    for i, match in enumerate(starts):
        end = starts[i+1].start() if i+1 < len(starts) else text.index('\nend', match.start())
        result[match[1]] = re.sub(r'\s+', '', text[match.start():end])
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--official", type=Path, help="checkout of the pinned PalomarSubmission")
    parser.add_argument("--schema", type=Path, help="published formalization.yaml v0.4 JSON schema")
    args = parser.parse_args()
    os.chdir(ROOT)
    report = {"full_protected_palomar_workflow_passed": False}
    core = definitions(ROOT / "Erdos745/WrapUp/Core.lean")
    challenge = definitions(ROOT / "Challenge.lean")
    assert "boundedBy" not in challenge
    assert all(core.get(name) == body for name, body in challenge.items())
    report["public_definitions"] = {"status": "PASS", "count": len(challenge)}
    sources = sorted([ROOT / "Erdos745.lean", ROOT / "Challenge.lean", ROOT / "Solution.lean",
                      *(ROOT / "Erdos745").rglob("*.lean")])
    normalized = {}
    forbidden = []
    for path in sources:
        text = strip_comments(path.read_text())
        relative = path.relative_to(ROOT).as_posix()
        normalized[relative] = re.sub(r"\s+", "", text)
        if relative != "Challenge.lean":
            forbidden.extend((relative, match.group()) for match in re.finditer(
                r"\b(?:sorry|admit|axiom|unsafe|extern|native_decide)\b", text))
    assert hashlib.sha256(json.dumps(normalized, sort_keys=True).encode()).hexdigest() == REFERENCE_TOKEN_HASH
    assert not forbidden, forbidden
    assert len(re.findall(r"\bsorry\b", strip_comments((ROOT / "Challenge.lean").read_text()))) == 1
    assert re.findall(r"^public import (.+)$", (ROOT / "Challenge.lean").read_text(), re.M) == ["Mathlib"]
    report["lean_cleanup"] = {"status": "PASS", "baseline_commit": BASELINE,
        "source_files": len(sources), "only_comments_or_whitespace_changed": True,
        "normalized_sources_sha256": hashlib.sha256(json.dumps(normalized, sort_keys=True).encode()).hexdigest(),
        "solution_cone_forbidden_tokens": forbidden, "challenge_protocol_placeholders": 1}
    manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    packages = manifest["packages"]
    for package in packages:
        directory = ROOT / manifest.get("packagesDir", ".lake/packages") / package["name"]
        actual = subprocess.check_output(["git", "-C", str(directory), "rev-parse", "HEAD"], text=True).strip()
        assert actual == package["rev"], package["name"]
        assert not subprocess.check_output(["git", "-C", str(directory), "status", "--porcelain"], text=True).strip()
    report["dependency_checkouts"] = {"status": "PASS", "count": len(packages)}
    configurations = ["lean-toolchain", "lakefile.toml", "lake-manifest.json", "comparator.json", "formalization.yaml"]
    assert all(not re.search(r"/Users/|/tmp/|/home/", (ROOT / path).read_text()) for path in configurations)
    report["configuration_paths"] = "PASS"
    passed = True
    if args.official:
        official = args.official.resolve()
        assert subprocess.check_output(["git", "-C", str(official), "rev-parse", "HEAD"], text=True).strip() == SUBMISSION_REVISION
        sys.path.insert(0, str(official))
        from scripts.submission_contract import load_formalization_metadata
        from scripts.source_requirements import inspect_lean_sources
        from scripts.verify_submission import load_comparator_config, supported_toolchain, repository_license_file
        from scripts.verification_errors import VerificationError
        report["official_submission_revision"] = SUBMISSION_REVISION
        for label, check in [
            ("metadata", lambda: load_formalization_metadata(ROOT / "formalization.yaml")),
            ("comparator_configuration", lambda: load_comparator_config(ROOT / "comparator.json")),
            ("supported_toolchain", lambda: supported_toolchain((ROOT / "lean-toolchain").read_text().strip())),
            ("root_license_file", lambda: repository_license_file(ROOT)),
        ]:
            try:
                check()
                report[label] = {"status": "PASS"}
            except VerificationError as error:
                report[label] = {"status": "FAIL", "diagnostics": [item.diagnostic(label) for item in getattr(error, "issues", [error])]}
                passed = False
        source_report, issues = inspect_lean_sources(ROOT)
        report["official_source_policy"] = {"status": "FAIL" if issues else "PASS", "report": source_report,
            "diagnostics": [item.diagnostic("source_policy") for item in issues]}
        passed = passed and not issues
        if args.schema:
            import jsonschema
            import yaml
            errors = list(jsonschema.Draft7Validator(json.loads(args.schema.read_text())).iter_errors(
                yaml.safe_load((ROOT / "formalization.yaml").read_text())))
            report["published_v04_schema"] = {"status": "FAIL" if errors else "PASS",
                "diagnostics": [{"path": ".".join(map(str, error.absolute_path)), "message": error.message} for error in errors]}
            passed = passed and not errors
    output = ROOT / "stage8/evidence/intake.json"
    output.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
