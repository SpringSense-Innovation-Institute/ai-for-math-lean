# Palomar verification

**S8_ROOT_CLOSED / MATH_CLOSED / KERNEL_CLOSED.** The completed five-regime
atlas retains the uniform center-error constant, with witness 12. This cleanup
changes only documentation paths and Lean comments; it does not rerun mathematical
worker stages or alter theorem semantics.

| Check | Result | Evidence |
|---|---|---|
| `python3 scripts/check-release.py` | PASS: all 74 statement/proof sources have the approved executable tokens; all 57 Challenge bodies equal Core | `evidence/intake.json` |
| Official intake validators from pinned PalomarSubmission | Metadata, source policy, toolchain and Comparator config PASS | `evidence/intake.json` |
| Published metadata schema v0.4 | PASS | `evidence/intake.json` |
| Root license file | PASS: exactly one nonempty UTF-8 file; authorized MIT metadata matches SPDX standard terms | `LICENSE`; license hashes in release manifest |
| Official SPDX detector | NOT_RUN locally: pinned Ruby/Bundler dependencies unavailable; pending official Linux workflow | Release manifest |
| Dependency checkout pins | PASS, nine clean exact revisions | `evidence/intake.json` |
| `lake build` after cleanup | PASS, exit 0, 9007 jobs | Build log hash in release manifest |
| `lake env lean Challenge.lean` | PASS, one intentional protocol placeholder | Challenge.lean:248 |
| `lake env lean scripts/AxiomAudit.lean` | PASS, 20 reports; exact uniform-type and witness-12 examples | `evidence/axioms.log` |
| `./scripts/verify-comparator.sh --local` | PASS, exit 0; exact correspondence and all three kernels | `evidence/comparator.log` |

Comparator uses the toolchain's bundled NanoDa and con-ron, as the official
workflow does. The `--local` flag disables sandboxing on macOS. A local pass
is not an official protected Linux preflight.

The approved proof baseline is `d3c8e613b32839d1221d79d1bf5b5fb7da06fe87`.
Its clean checkout passed all 9007 build jobs and exact uniform-type/axiom checks;
project build artifacts were initially empty and only pinned dependency caches
were reused. Those historical receipts remain available in that Git commit.

Policy retrieved 2026-10-03, reconfirmed during this cleanup:
PalomarPolicy `96b034cc31a72a63d4f4041911dce337a85c9a04`,
PalomarSubmission `65f0154ed776cd26c224254aa57b379137f28b0d`,
PalomarTemplate `2891de4c48955af824969a263d31b25e7a9a1406`.
The repository's GitHub workflow is pinned to that official submission workflow.

**Publication gates:** the owner confirmed Jingxuan Ding as author and responsible
maintainer, affiliated with SpringSense Innovation Institute, and authorized MIT.
Official intake and published schema validation now pass. The public GitHub
repository URL remains unknown; no public push, independent human review or
official acceptance is claimed. `PALOMAR_READY` remains false while the official
protected Linux preflight, including its SPDX detector, is outstanding. These
are publication gates, not open mathematical obligations.

Current con-ron replay accepted 73872 declarations in verified mode. NanoDa and
Lean default kernel replay passed. The Comparator evidence keeps the actual
verification lines, omits compiler-warning noise and records the full transcript
SHA256. All 20 axiom reports contain only the three permitted axioms.

Cleanup code/configuration checkpoint: `1e5ca866823ef162d54573fe89796b836fd4408a`. Its clean submission archive
passed `python3 scripts/check-release.py` without a main `.git` directory and
compiled Challenge independently with no project build cache. Only pinned
dependency caches were reused. A full fresh Solution rebuild was not repeated
for this comment-only change; current build and all three kernel replays passed,
and the approved mathematical baseline has its full fresh-build receipt in Git.
No public repository push occurred.

Metadata/license checkpoint: `b8fec11a636dbced52ab76ca778a03ec455bd4d5`. Its clean Git archive
passed the pinned official intake validators and published v0.4 schema; the
resulting intake receipt is byte-identical to the working checkout receipt.
Lean sources, toolchain/dependency pins, Comparator configuration and verifier
scripts are byte-identical to `de1169de28bedffe446f6ef4ed2f6201cce38ae4`; the
existing proof/kernel receipts remain applicable. No mathematical stages or
full Solution rebuild were repeated for this metadata-only update. MIT
permission and disclaimer text matches the SPDX canonical text; this comparison
is distinct from the pending official Ruby SPDX detector.
