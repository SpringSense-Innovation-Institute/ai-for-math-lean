#!/usr/bin/env python3
"""Run source/pin checks and the pinned Palomar intake validators (not full preflight)."""
import argparse
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SUBMISSION_REVISION = "65f0154ed776cd26c224254aa57b379137f28b0d"


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--official", type=Path, required=True)
    parser.add_argument("--schema", type=Path, required=True)
    args = parser.parse_args()
    official = args.official.resolve()
    actual = subprocess.check_output(["git", "-C", str(official), "rev-parse", "HEAD"], text=True).strip()
    if actual != SUBMISSION_REVISION:
        raise SystemExit(f"PalomarSubmission revision mismatch: {actual}")
    sys.path.insert(0, str(official))
    from scripts.submission_contract import load_formalization_metadata
    from scripts.source_requirements import inspect_lean_sources
    from scripts.verify_submission import load_comparator_config, supported_toolchain, repository_license_file
    from scripts.verification_errors import VerificationError
    import jsonschema
    import yaml

    source_paths = [ROOT / "LeanProject.lean", ROOT / "Challenge.lean", ROOT / "Solution.lean",
                    *sorted((ROOT / "LeanProject").rglob("*.lean")),
                    *sorted((ROOT / "scripts").glob("*"))]
    inputs = [*source_paths, *(ROOT / name for name in
              ["lean-toolchain", "lakefile.toml", "lake-manifest.json", "formalization.yaml", "comparator.json"])]
    if (ROOT / "LICENSE").exists():
        inputs.append(ROOT / "LICENSE")
    input_hashes = {p.relative_to(ROOT).as_posix(): digest(p) for p in sorted(inputs) if p.is_file()}
    report = {
        "profile": "local-static-intake",
        "official_protected_preflight": "NOT_RUN",
        "official_submission_revision": SUBMISSION_REVISION,
        "schema_sha256": digest(args.schema),
        "input_files_sha256": input_hashes,
        "input_identity_sha256": hashlib.sha256(json.dumps(input_hashes, sort_keys=True).encode()).hexdigest(),
        "checks": {},
    }
    passed = True
    for label, check in [
        ("metadata", lambda: load_formalization_metadata(ROOT / "formalization.yaml")),
        ("comparator_configuration", lambda: load_comparator_config(ROOT / "comparator.json")),
        ("supported_toolchain", lambda: supported_toolchain((ROOT / "lean-toolchain").read_text().strip())),
        ("root_license_file", lambda: repository_license_file(ROOT)),
    ]:
        try:
            check()
            report["checks"][label] = {"status": "PASS"}
        except VerificationError as error:
            report["checks"][label] = {"status": "FAIL", "diagnostics": [str(item) for item in getattr(error, "issues", [error])]}
            passed = False
    source_report, issues = inspect_lean_sources(ROOT)
    report["checks"]["official_source_policy"] = {
        "status": "FAIL" if issues else "PASS", "report": source_report,
        "diagnostics": [str(item) for item in issues]}
    passed = passed and not issues
    errors = list(jsonschema.Draft7Validator(json.loads(args.schema.read_text())).iter_errors(
        yaml.safe_load((ROOT / "formalization.yaml").read_text())))
    report["checks"]["v04_schema"] = {"status": "FAIL" if errors else "PASS", "diagnostics": [
        {"path": ".".join(map(str, error.absolute_path)), "message": error.message} for error in errors]}
    passed = passed and not errors
    deps = json.loads((ROOT / "lake-manifest.json").read_text())
    mismatches = []
    for p in deps["packages"]:
        d = ROOT / deps["packagesDir"] / p["name"]
        head = subprocess.check_output(["git", "-C", str(d), "rev-parse", "HEAD"], text=True).strip()
        status = subprocess.check_output(["git", "-C", str(d), "status", "--porcelain"], text=True)
        if head != p["rev"] or status.strip() or not re.fullmatch(r"[0-9a-f]{40}", p["rev"]):
            mismatches.append({"package": p["name"], "actual_revision": head, "status": status})
    report["checks"]["dependency_pins"] = {"status": "FAIL" if mismatches else "PASS", "count": len(deps["packages"]), "diagnostics": mismatches}
    passed = passed and not mismatches
    config_names = ["lean-toolchain", "lakefile.toml", "lake-manifest.json", "formalization.yaml", "comparator.json"]
    absolute = [n for n in config_names if re.search(r"/Users/|/tmp/|/home/", (ROOT / n).read_text())]
    report["checks"]["configuration_paths"] = {"status": "FAIL" if absolute else "PASS", "diagnostics": absolute}
    passed = passed and not absolute
    print(json.dumps(report, indent=2))
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
