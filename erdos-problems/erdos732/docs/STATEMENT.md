# Statement and source audit

The authority is Noga Alon,
[Blocking partial designs and block-compatible sequences](https://web.math.princeton.edu/~nalon/PDFS/remark191.pdf),
Problem 1.2 on PDF p. 1 and Theorem 2.3 on PDF p. 3.

The public theorem quantifies `∃ c : ℝ, 0 < c ∧ eventually ...`; its constant is
independent of `n`. `Filter.atTop` means all sufficiently large natural numbers.
The existing estimate uses `c = 1/4096` and a cutoff `1024^2`; the public theorem
advertises existence, without claiming an optimized coefficient.

A list is nonincreasing, with each entry in `[2,n]`. A finite type of cardinality
`n` serves as the point set, interchangeable with a labeled `n`-point set for
existence. An indexed family of finite subsets realizes the list and covers
every pair of distinct points exactly once. The count is `Set.ncard` of lists;
`blockCompatibleSequence_set_finite` proves finiteness, so this is an actual
finite count. Designs themselves are not counted. No small-`n` lower bound is
asserted; empty lists and the vacuous `n=0,1` cases are allowed by the definitions
and do not affect the eventual result.

Theorem 2.3 supplies a lower bound on prime-power plane sizes. The formalization
also proves monotonicity under enlargement and uses Bertrand's postulate to
reach every sufficiently large `n`. The source uses base-2 logarithms and a
sharper asymptotic estimate; the public result uses natural logarithms and only
a fixed positive constant, preserving the question's strength.

The first sentence of the proof of Theorem 2.3 says plane order `q+1`; its
stated point count `q^2+q+1` and line size `q+1` require order `q`. The formalization
uses order `q`, consistent with the theorem and the preceding construction.
This corrects that local typographical inconsistency without changing the
mathematical claim. Problem 1.1, Theorem 2.1, and the concluding conjectures are
outside the submitted result.

The release port adds `module`, `public import`, and `@[expose] public section`
to preserve the old cross-module unfolding behavior. It pins one supported
Lean/Mathlib pair and adjusts affected simplification proofs. No canonical
mathematical statement is strengthened or weakened.
