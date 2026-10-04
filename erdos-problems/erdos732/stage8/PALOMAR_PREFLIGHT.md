# Palomar preflight

**S8_ROOT_CLOSED; local technical checks PASS; PALOMAR_READY = false.**
The execution profile is a local macOS audit without sandbox protection.
Formalization author and responsible maintainer: Jingxuan Ding, SpringSense
Innovation Institute. The authorized root license is MIT. The user's instruction
“与erdos745一致” confirms reuse of these fields.

| Gate | Result | Evidence |
|---|---|---|
| Fresh full project build (8950 jobs; no project artifacts copied) | PASS | `evidence/clean-build.log` |
| Independent Mathlib-only Challenge compile | PASS | `evidence/standalone-challenge.log` |
| Public exact type and transitive axioms | PASS, only propext, Classical.choice, Quot.sound | `evidence/axioms.log` |
| Comparator / statement correspondence | PASS | `evidence/comparator.log` |
| Lean kernel | PASS | `evidence/comparator.log` |
| NanoDa | PASS | `evidence/comparator.log` |
| con-ron | PASS, 43,703 declarations in verified mode | `evidence/comparator.log` |
| Official intake functions, v0.4 schema, source policy, nine exact clean dependency pins | PASS | `evidence/intake.json` |
| Official Challenge allowlist and Mathlib/toolchain correspondence | PASS | `evidence/allowlist.log` |
| Metadata source archive without project Git history or project artifacts | PASS | `evidence/archive-intake.json` |
| MIT permission/disclaimer match to pinned SPDX text | PASS | `evidence/license.json` |
| Official Ruby/licensee detector | NOT_RUN | Pending official Linux workflow |
| Official protected Palomar workflow, palomar-standard-v1 | NOT_RUN | Public repository and Linux run required |

The clean build and exact-type audit bind `06bed6b36023f900a90d5c9f88fd229721c45df3`.
The repaired verifier wrapper and successful Comparator bind `d8bcd2e47eec34a92a067d8558c559003259d828`.
The source/metadata/license checkpoint is `bdfb632c601fdda9792f904ae65fa62bd6136858`.
`evidence/input-identity.json` checks identical Lean source, complete dependency
pins, toolchain and Comparator configuration across these commits. The wrapper
is identical between the kernel and metadata checkpoints. No proof rebuild or
kernel rerun is claimed for metadata-only changes. Final HEAD carries receipts
only; its complete SHA and byte comparison are stored in a `palomar-release`
Git note. The official preflight must run on the actual selected final SHA.

Challenge has one deliberate protocol placeholder. Solution and its substantive
proof development have no proof placeholders. All original theorem signature
texts were compared unchanged; necessary version-port proof edits are recorded
in `evidence/source-port.diff`. Source comparison is auxiliary to Lean and
Comparator, and does not substitute for them.

Full final transcripts are retained, including the Comparator warning:
`WARNING: Sandbox disabled, this run is not trustworthy.` This local audit is
not the official protected workflow or a registry acceptance.

No public remote is configured. Nothing has been pushed or submitted. Remaining
actions: provide/authorize the public repository, publish the immutable
candidate, run the pinned protected workflow, and authorize registry submission.
