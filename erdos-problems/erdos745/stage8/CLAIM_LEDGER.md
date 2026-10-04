# Public claim ledger

The only submitted declaration is `Erdos745.Palomar.sparseEvolution`.
`Solution.lean` proves exactly `Erdos745.WrapUp.AtlasStatement` by
`Erdos745.WrapUp.atlas`, with no representation conversion or added assumptions.
The mathematical authority is [STATEMENT.md](../docs/STATEMENT.md),
`Core.lean`, and the accepted completed proof. The uniform constant was restored
by the authorized interface repair, using the existing witness 12.

| Branch | Public mathematical claim | Canonical definition | Source relationship |
|---|---|---|---|
| FINAL-01 | Fixed subcritical rank-two lattice CDF and tight logarithmic center | `fixedSubcriticalLaw` | Erdős–Rényi (1960), background |
| FINAL-02 | Fixed supercritical rank-two lattice CDF, giant center and separation | `fixedSupercriticalLaw` | Erdős–Rényi (1960) and Pittel (1990), background |
| FINAL-03 | Barely subcritical exact-rate CDF and exclusion of positive excess | `barelySubcriticalLaw` | Adapts Łuczak (1990), Theorem 3 (2.8), printed p. 294 |
| FINAL-04 | Barely supercritical exact-rate CDF, conjugacy, center bound and giant windows | `barelySupercriticalLaw` | Adapts Łuczak (1990), Theorem 3 (2.10), printed p. 294 |
| FINAL-05 | Critical fixed-edge finite-rank Brownian-excursion CDF limits and positive finite ranks | `criticalLaw` | Adapts Aldous (1997), Corollary 2 |

The combined source relationship is **adapts**. The near-critical rate is
`a(x) = x − 1 − log x`; the printed quadratic rate needs an additional
`epsilon log(n epsilon³) → 0` hypothesis for its unshifted law. This additional
hypothesis is not imposed on the published exact-rate theorem. The source
correction and counterexample are explained in [NORMALIZATION.md](../docs/NORMALIZATION.md).
The critical result uses fixed-edge sequences and finite-rank continuity
rectangles; no full l² topology, all-moment or simultaneous graph-process result
is claimed. No assumptions have otherwise been added or removed.

Representation and endpoint conventions:

- Graphs are finite labelled simple graphs on `Fin n`, with ordered edge endpoints.
- Admissibility is eventual `M(n) ≤ binom(n,2)`; finite probability expressions
  use totalized real division, including `0/0 = 0` outside the relevant domains.
- Component ranks start at one, count multiplicities and are zero padded; rank
  zero is defined as zero. A single vertex is a tree.
- Fixed-density centers use `2M(n)/n`. Lattice limits use increasing subsequences
  and integer thresholds; near-critical thresholds use the exact rate.
- Critical scaling is `(2M−n)/n^(2/3) → lambda`; CDF limits are at coordinate
  marginal continuity points.
- The center-error bound is `∃ C > 0, ∀ M, bareSuper M → eventually
  |giantCenter M n − 4 * displacement M n| ≤ C * (displacement M n)^2/n`.
  The proof supplies the absolute witness **12**. Only the eventual cutoff may
  depend on M. There is no per-sequence Palomar `boundedBy` wrapper.
- Giant windows quantify over every eventually positive divergent `omega`.

All 57 public definitions have mathematical documentation and exactly the Core
bodies. Challenge imports only Mathlib. Solution imports the completed proof.
The prior interface repair and clean-checkout verification are frozen in commit
`d3c8e613b32839d1221d79d1bf5b5fb7da06fe87`; the present cleanup changes only
Lean comments and documentation paths. Source/token comparison is reproducible
with `scripts/check-release.py`. Earlier operational records remain in Git
history; the original proof snapshot is retained in `evidence/` for provenance.
