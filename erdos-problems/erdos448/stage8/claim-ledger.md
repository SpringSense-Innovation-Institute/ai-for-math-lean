# Claim ledger

## FT-448-NEG-017 / Erdos448.negativeAnswer

**Mathematical claim.** The universal assertion that, for every real epsilon > 0,
the strict event tauPlus(n,2) < epsilon * tau(n) has natural density one is false.
The public theorem is premise-free. This is a negative answer to Erdős problem
448, not a statement that the ratio has a specified limit or a specific density.

**Authority.** The retained S3 authority snapshot is
[mathematical-authority.md](../docs/mathematical-authority.md), with scoped
corrections W0–W8. The representation conventions are recorded in
[representation.md](../docs/representation.md). Actual binder-faithful
statements are the retained Stage4 Interfaces and GroupA–GroupD Lean modules.
Historical pending/rejected review states remain historical; the newer S7/S8
completion recorded in the input MODULE.json is the operational closure claim.
This release verifies that closure against fresh inputs.

**Sources and relationship.** Erdős–Tenenbaum, *Sur la structure de la suite des
diviseurs d'un entier*, selected pp. 18–19 and 22–32, Theorem 1 and its
negative-resolution consequence; adapted through the existing reconstruction.
Halberstam–Richert, *On a Result of R. R. Hall*, pp. 77–82, supplies the
mean-value estimate, formally proved by the retained DP-MEAN development.
Mertens estimates are likewise proved by the retained DP-MERTENS development.
The supplied page transcription is in [selected-source-pages.md](../docs/selected-source-pages.md).

**Internal provider.** `Erdos448.WrapupFinal.negativeAnswer`, from
`Erdos448.stage8.Integration`, links ROOT-01 through ROOT-13, the two
foundations, the mean adapter and the two proved providers. `Solution.lean`
bridges directly to that theorem. No conditional provider is assumed at the
public boundary.

**Definitions and endpoints.** The domain is positive natural numbers.
`Nat.divisors` gives positive divisors. Dyadic bins are half-open
`[2^k,2^(k+1))`; k is natural, which covers all positive integer divisors.
The finite search uses `ceil(log n/log 2)+1`. Density counts positive n in
`[1,x)` and divides by x. The x=0 value is total and irrelevant to the limit.
The event uses a strict inequality; epsilon=0 is excluded. No quantifier or
constant order is changed by the public bridge.

**Scope differences.** The public face states only the final negative answer.
The quantitative interior density bound remains internal. Internal uniform
Euler-product estimates use the repaired all-prime positive floor described
in W1–W3. This premise is discharged for the actual consumers; it is not an
extra hypothesis of the submitted theorem. The source is ported to the
current module system with public imports/declarations and exposed definition
bodies; namespace and proof-module names are preserved.

**Mechanical correspondence.** `scripts/Check.lean` directly extracts the
explicit negated density assertion from the public theorem and prints
transitive axioms of both facade and provider. Comparator selects the final
theorem plus the twelve definitions of its statement. Only `propext`,
`Classical.choice` and `Quot.sound` are permitted. Challenge's deliberate one
`sorry` is a protocol placeholder; all Solution closure proof gaps are counted
separately. Actual commands, exits, fingerprints and logs are in preflight.json.

**Human review.** No independent human review is established by the available
records. Mechanical acceptance does not establish such review or Palomar
registration.
