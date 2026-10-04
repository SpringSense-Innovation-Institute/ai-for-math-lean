# Erdős 745: sparse random-graph evolution

A Lean formalization of component-size asymptotics for the uniform labelled
simple graph G(n,M). The principal theorem, `Erdos745.Palomar.sparseEvolution`,
combines five sparse regimes: fixed subcritical and supercritical lattice laws,
barely subcritical and supercritical exact-rate laws, and critical finite-rank
Brownian-excursion distribution limits.

The barely-supercritical deterministic center error is bounded by one absolute
constant across all admissible edge sequences; the proof supplies **C = 12**.
The eventual cutoff may depend on the sequence. The result is pointwise for
edge-count sequences and does not claim a simultaneous graph-process theorem
or a complete dense-regime classification.

The source papers are Erdős–Rényi (1960), Pittel (1990), Łuczak (1990) and Aldous
(1997). The near-critical laws use the exact rate **a(x) = x − 1 − log x**. The
printed quadratic normalization requires an additional hypothesis for its
unshifted limit. See [the mathematical statement](docs/STATEMENT.md),
[the normalization correction](docs/NORMALIZATION.md) and
[the source alignment ledger](stage8/CLAIM_LEDGER.md).

## Repository layout

| Path | Purpose |
|---|---|
| `Challenge.lean` | Public mathematical statement; imports only Mathlib |
| `Solution.lean` | Direct bridge to the proved atlas |
| `Erdos745/` | Substantive definitions and proofs |
| `comparator.json` | Palomar declaration correspondence |
| `formalization.yaml` | Authorship, sources, classification and methodology |
| `docs/` | Mathematical statement and source correction |
| `scripts/` | Reproducible source, axiom and Comparator checks |
| `stage8/` | Claim ledger, release manifest and verification evidence |

In this repository, the Palomar project path is `erdos-problems/erdos745`;
the repository-relative configuration path is
`erdos-problems/erdos745/comparator.json`. Submit an immutable commit in the
public GitHub repository through [Palomar's submission service](https://submit.palomar-registry.org/).

## Build and verify

Lean is pinned to `leanprover/lean4:v4.35.0-rc2`; Mathlib is pinned to
`065356127b1dc0016f66b7283ce0ce2c4055aa55`. With Elan installed, run from the
repository root:

```sh
cd erdos-problems/erdos745
lake exe cache get
lake build
lake env lean scripts/AxiomAudit.lean
python3 scripts/check-release.py
```

On Linux with bubblewrap, run the protected Comparator with both bundled
independent kernels:

```sh
./scripts/verify-comparator.sh
```

On macOS, `./scripts/verify-comparator.sh --local` performs an unsandboxed local
check. It is not an official protected preflight. The pinned
[GitHub workflow](../../.github/workflows/erdos745-palomar-preflight.yml) runs Palomar's full
verification against the selected commit. Actual results are in
[PALOMAR_PREFLIGHT.md](stage8/PALOMAR_PREFLIGHT.md).

Challenge's single deliberate `sorry` is the Palomar statement placeholder.
Solution and its proof closure contain no proof placeholders. The permitted
axioms are `propext`, `Classical.choice` and `Quot.sound`.

## Authorship and methodology

Formalization author: **Jingxuan Ding, SpringSense Innovation Institute**.
MathMiner orchestration and substantial LLM-assisted proof engineering were
used. Lean kernel and independent-kernel replay provide mechanical verification;
model review is not mathematical verification. No independent human review or
Palomar acceptance is claimed.

Responsible maintainer: **Jingxuan Ding**. Released under the [MIT license](LICENSE).
Dependencies retain their own licenses.

The files in `stage8/` are historical verification receipts from the standalone
project before this repository import. Their commit hashes, root-relative paths
and publication flags describe those checkpoints. The workflow above uses the
current repository paths; the historical receipts do not report a GitHub Actions
run for this PR.
