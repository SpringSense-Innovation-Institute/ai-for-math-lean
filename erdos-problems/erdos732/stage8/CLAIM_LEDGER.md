# Claim Ledger

| Claim | Public surface | Internal provider | Mathematical authority | Relationship and scope |
|---|---|---|---|---|
| For some absolute `c>0`, eventually the number of block-compatible lists on `n` points is at least `exp(c sqrt(n) log(n))`. | `ErdosProblems.P732.Palomar.erdos732_yes`, Challenge/Solution | `ErdosProblems.P732.erdos732_yes`, `LeanProject/ErdosProblems/P732/LowerBound.lean` | Alon, Problem 1.2, PDF p. 1; Theorem 2.3, PDF p. 3 | Formalizes the affirmative answer; natural logarithm and coarse constant. |

Authority was recovered from the supplied completed development, checked
against the author's PDF at <https://web.math.princeton.edu/~nalon/PDFS/remark191.pdf>.
No pre-existing S3/S4 stage records or accepted-stage manifest were supplied.
This ledger records the recovered mathematical and representation authority;
it does not claim those missing historical records exist.

Definitions: indexed pairwise balanced design; arbitrary finite carrier of
cardinality `n`; nonincreasing finite lists with entries `2 ≤ x ≤ n`.
The counter is a set cardinality of lists. Finiteness follows from the proved
length bound `length ≤ choose n 2`. Empty and small-carrier cases are admitted
by the definitions; the theorem has an eventual cutoff.

Provider chain: finite fields → projective planes → Alon's augmented lists →
exact binomial count → monotone extension → prime selection and exponential
estimate → final theorem. The constant witness `1/4096` precedes the eventual
quantifier. No geometric existence hypothesis remains in the public theorem.

Comparator and the direct type-check in `scripts/AxiomAudit.lean` provide
mechanical correspondence evidence. See `docs/STATEMENT.md` for the plane-order
typo, logarithm convention, and excluded parts of the source.
