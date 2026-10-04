# Erdős problem 448

This Lean development proves the negative answer to Erdős problem 448.
Let tau(n) be the number of positive divisors of n, and tauPlus(n) the number
of dyadic intervals [2^k,2^(k+1)) that contain a divisor. The theorem refutes
the assertion that, for every epsilon > 0, tauPlus(n) < epsilon * tau(n)
for almost all positive integers n. Almost all means natural density one.

The advertised statement is in [Challenge.lean](Challenge.lean). Its single
`sorry` is the Comparator protocol placeholder. [Solution.lean](Solution.lean)
proves the identical statement by applying the premise-free canonical theorem
`Erdos448.WrapupFinal.negativeAnswer`. The retained proof development and both
proved analytic providers are under [Erdos448](Erdos448).

## Build and audit

From the repository root, first run `cd erdos-problems/erdos448`.
Install the exact release named by `lean-toolchain`. Dependencies are pinned
in `lake-manifest.json`; the direct Mathlib pin is a full commit in the TOML
Lakefile. From this directory run:

```sh
lake exe cache get
lake build
lake env lean scripts/Check.lean
python3 scripts/verify.py --output /tmp/erdos448-audit
```

The output directory must be new. The last command runs the exact-type and
transitive-axiom checks, Comparator and the bundled NanoDa and con-ron kernels.
On macOS it runs without Linux protection. It records every source/config hash,
compiler and verifier binary hash, full logs and exits, and rejects changes to
its inputs while running. This local profile is not the official Palomar
protected preflight. No historical commit is required to build the project.

For read-only intake checks, obtain a clean checkout of PalomarSubmission at
the full revision in [policy-lock.json](stage8/policy-lock.json), install its
Python dependencies for your platform, then run:

```sh
python3 scripts/intake.py --contract /path/to/PalomarSubmission
```

That command calls the pinned official source, metadata, toolchain, Comparator
configuration, dependency-pin and root-license-presence validators. It does
not claim to execute the complete official workflow or SPDX license detector.
The Linux reusable workflow and registry submission must judge the actual
selected immutable Git commit.

## Mathematical sources and scope

The development adapts Erdős and Tenenbaum, *Sur la structure de la suite des
diviseurs d'un entier*, selected pages 18–19 and 22–32, and Halberstam and
Richert, *On a Result of R. R. Hall*, pages 77–82. The supplied transcription
is preserved in [selected-source-pages.md](docs/selected-source-pages.md).
The [claim ledger](stage8/claim-ledger.md) documents source relationships,
quantifiers, endpoints, internal providers and scope differences. The proof
counts positive integers in [1,x), normalized by x, uses strict inequality and
keeps epsilon strictly positive. This entry submits only the final negative
answer; internal quantitative estimates remain proof dependencies.

The candidate is extracted from the input project's live proof closure.
Original module paths and namespaces are preserved, including literal dots in
escaped module-name segments. Historical scheduling files, editor databases,
unrelated archives and compiled project artifacts are excluded. A compressed
original proof snapshot is retained solely as provenance evidence. The
[source map](stage8/source-map.json) and release records document extraction
and the module-system/API compatibility port. Source-authority snapshots
retain historical status notes; current verification is recorded separately.

## Automation, review and release status

The original construction used MathMiner and Codex agents for mathematical
reconstruction and Lean proof engineering. This release reuses the completed
proofs and performs a toolchain/module compatibility port and mechanical
verification. Historical model identities and costs are not established by
the retained records. No independent human review is claimed.

[formalization.yaml](formalization.yaml) records the metadata.
[release-manifest.json](stage8/release-manifest.json) and
[preflight.json](stage8/preflight.json) state the actual readiness and checks.
Author and responsible maintainer: Jingxuan Ding, SpringSense Innovation
Institute. The project is released under the [MIT license](LICENSE), confirmed
by the user by reference to the Erdős 745 release. This project is proposed for inclusion in
[ai-for-math-lean](https://github.com/SpringSense-Innovation-Institute/ai-for-math-lean)
under `erdos-problems/erdos448/`. The protected workflow and registry submission
remain pending.

The frozen code checkpoint is `5a2796ba0421cf48dd2f08c3424697e46abfc4de`. A fresh project build,
independent Challenge compilation, exact-type/axiom audit, Comparator, NanoDa,
con-ron in verified mode (59,293 declarations) and the Lean default kernel all
passed under `local-unsandboxed-macos`. The complete logs and source/binary
fingerprints are in [the verification receipt](stage8/evidence/local-5a2796ba0421/receipt.json).
The imported standalone snapshot is `d79c1c1637e1f2a9a1c67a5ff37114d104647e3b`;
its Lean sources and audited configuration match the frozen receipt byte for
byte. The imported `stage8/` records describe that standalone snapshot, so
their unpublished status and Git identities are historical, not the identity
of this repository commit. Status is `S8_ROOT_CLOSED`; `PALOMAR_READY=false`
until the selected public submission commit passes the official protected
Linux preflight. No Palomar submission has been made.

The nested `.github/workflows/palomar-preflight.yml` is retained as a standalone
project workflow example. GitHub does not run nested workflow files in this
repository; this PR does not register or execute the protected workflow.
