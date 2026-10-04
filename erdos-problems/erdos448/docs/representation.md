> Preserved authority snapshot from the input project. Historical paths and
> statuses below refer to that project; current release evidence is in
> `../stage8/preflight.json`. Original snapshot SHA-256: `adb184a0041d5d9523f8d5254fda400dce8f645847c3ea14a9a207e834715918`.

> 2026-09-19 scoped wrap-up: CURRENT.md W0--W8 and the actual GroupA--GroupD
> contracts govern the repaired cone. P008 now requires an all-prime uniform
> floor; WrapupFamilies.lean supplies exact carriers. Existing 13 ROOT ownerships
> and completed proofs are retained. Old hashes, CU waits and unsupported typed
> proxies below are not gates. Independent delta acceptance remains pending.

# S4 representation authority — Erdős 448

```yaml
stage: S4
status: COMPLETE
lean_mode: LEAN_DESIGN
root_module: Erdos448
final_target: FT-448-NEG-017
s3_authority: Erdos448/stage3/canonical/CURRENT.md
s3_content_sha256: 07b55262f273e07042e14b2b054ed5cbf63ff71dcc6720161151c8a3b133c047
whole_cone_audit: Erdos448/stage3/audits/current/S3_WHOLE_REQUIRED_CONE_FINAL_AUDIT_2026-09-13_A1.md
whole_cone_audit_sha256: 5d6e88cd04dd99c2f55f627346e0dd943e79a9ffdf5433b0d56104f1783f143b
lean_interface: Erdos448/stage4/Interfaces.lean
root_objects: Erdos448/stage4/RootObjects.lean
dependency_adapters: Erdos448/stage4/DependencyAdapters.lean
contract_modules:
  - Erdos448/stage4/contracts/GroupA.lean
  - Erdos448/stage4/contracts/GroupB.lean
  - Erdos448/stage4/contracts/GroupC.lean
  - Erdos448/stage4/contracts/GroupD.lean
provider_policy: FOUNDATION_CLOSED
```

This is a lossless Lean-design projection of the pinned S3 authority, not a
new mathematical authority.  Every formula, premise map, derivation
certificate, transformation, witness order, constant dependence, and source
anchor remains owned by the exact S3 section bearing the same object ID.
Neither this file nor `Interfaces.lean` may be used to shorten or reinterpret
that payload.  S6 materializes the selected exact S3 sections into each task.

## Frozen representation decisions

- Positive integer binders use `PosNat := {n : ℕ // 0 < n}`.  The raw
  prefix-density sequence is indexed by `ℕ`, excludes zero explicitly, and
  counts `[1,x)` exactly.
- Divisors use `Nat.divisors`; `tau` is its card.  No quotient-generated
  divisor is admitted without a divisibility proof.
- Roughness is represented directly by the universal prime-divisor predicate
  `IsRough`; this faithfully makes `1` rough without encoding `+∞` as a
  fabricated natural number.
- Truncated multiplicity uses `Nat.factorization` over `Nat.primeFactors` and
  the strict real cutoff `(p : ℝ) < u`.
- Occupied bins use the exact half-open predicate
  `theta^k ≤ d ∧ d < theta^(k+1)`.  On `theta > 1`, `occupiedBins` searches
  through `ceil(log n/log theta)`, the correct finite coverage bound even for
  `1 < theta < 2`; outside the S3 domain its total Lean value is empty.
  Coverage is an explicit P-031/P-110 proof obligation, not a definitional
  assumption.
- `Close` is ordered, unequal, and strict at both ratio endpoints.  No
  symmetry quotient is taken.
- Natural density is a `Tendsto` statement for the normalized prefix count.
  The audited upper-density inequalities use the epsilon/eventually
  characterization `UpperDensityAtMost`, avoiding an arbitrary default value
  for a limsup.  P-120 exports `UpperDensityLtOne` and S8 connects it to
  failure of density one.
- `densityEvent` preserves the non-strict event used in P-112--P-117;
  `strictEvent` is distinct and preserves the strict event in P-120 and the
  literal problem.  Zero is excluded from both sets.
- Existence results whose witnesses cross task cuts use
  `WitnessWithSpec`; two-sided estimates use `PositiveComparison`.
  `InteriorDensityBound` fixes `C_delta` before uniform `alpha`, and
  `CounterexampleWitness` forces the same positive epsilon to be used in the
  strict event and in the final refutation.
- Every unproved cross-task theorem is a local theorem parameter of its
  consumer's parametric output.  There are no global theorem axioms.

## Exact contract coverage

The following IDs are frozen as same-named Lean statement declarations in the
four `stage4/contracts/Group*.lean` modules. Their complete Lean binder order,
hypotheses, conclusions, witness outputs, and local derived definitions are
the literal contract in the corresponding S3 heading; the S6 payload includes
that entire heading verbatim.  This mapping is one-to-one and does not create
new propositions.

- Definitions and scoped data: `D-001`--`D-020`, `D-021a`--`D-021e`,
  `D-022`, and scoped `P070-C4`.
- External/provider frames: `EXT-001`, `DP-MEAN-017`, `EXT-002`, and
  `DP-MERTENS-017`.
- Shifted-mean/Euler infrastructure: `P-001`, `P-001A`--`P-001D`,
  `P-002`--`P-008`, including the construction-critical `P-005A` convergence
  and factorization payload and `P-006A`.
- Lemma-4 chain: `P-010`--`P-020`.
- Propositions 1 and 2: `P-030`--`P-034`, `P-040`--`P-044`.
- Proposition-3 common infrastructure: `P-050`, `P-051A`--`P-051E`,
  `P-051V`, `P-051F1`--`P-051F4`, `P-051G`, `P-051H`, `P-052`--`P-059`,
  and `P-054A`.
- Regular branch: `P-060`--`P-074`.
- Transition/empty branches and Proposition 3: `P-075`--`P-089`.
- Proposition 4: `P-090`--`P-102`.
- Optimization and target: `P-110`--`P-120` and `FT-448-NEG-017`.

`P-118` and `P-119` remain `CROSS_CHECK` declarations and are not required
providers for `FT-448-NEG-017`.  All other IDs above are required or are
definitions used in the required cone exactly as recorded in S3 §13.6.

## Assumption-closure and well-posedness round trip

For every mapped ID, the Lean declaration checklist is fixed as follows:

1. Preserve the S3 prenex order verbatim.  Producer-selected constants and
   witnesses become output structure fields or existential outputs, never
   caller-supplied parameters.
2. Carry every binder-domain condition as a subtype field or explicit
   hypothesis.  In particular retain positivity/nonzero, compact-family,
   prime, coprimality, divisibility, support, convergence, and cutoff facts.
3. Keep half-open/strict/weak endpoints literal.  The regular
   `B_k^#` and enlarged `B_k^enl` subjects are different definitions.
4. Preserve all authored premise maps as local parameter substitutions in
   downstream theorem declarations.  S3 §13.5 is a derived navigation view;
   the owning premise-map paragraphs remain authoritative.
5. Preserve witness identity across consumers.  Especially keep the common
   P-051G family witnesses, the P-070 `C_4(C_fam,theta)`, the P-102
   pointwise remainder, and the P-112--P-120 constant chain.
6. Any total Lean division must carry the S3 positive-denominator fact in the
   usable interface.  Infinite sums/products must expose summability or the
   exact finite truncation.  Multiplicative extensions must expose their
   prime-power specification and multiplicativity fields.
7. Every transformation-result proposition keeps its bijection/reindexing,
   domain, multiplicity, inequality-direction, and endpoint certificate
   available to its consumer.

The canonical parent provider identities for `EXT-001` and `EXT-002` are the
transparent aliases in `ExternalProviderInterfaces.lean`; they are
definitionally identical to the dependency outputs named by the typed S3
provider edges. The parent consumer representation of `EXT-001` remains
distinct. `DependencyAdapters.lean` freezes the exact `DPMeanEXT001Adapter`
certificate: it must reconcile the parameter-range,
nonnegative-multiplicative, prime-power-bound, strict-domain, strict-mean, and
strict-Euler-product representations, then convert
`DPMean.T001Statement` to the unchanged parent `EXT001Statement`.

The round trip found no semantic mismatch in the chosen representations.
Every theorem proposition is a transparent `Prop` definition or a
witness/specification structure; none is installed as an unproved theorem or
global axiom. S6 curries these exact declarations into local task targets.

The frozen S4 declaration identities are:

| File | SHA-256 |
|---|---|
| `RootObjects.lean` | `6b02851467f1a9a4580162bcc2006afb99a1ef946c3e288a242cf79c1d813434` |
| `contracts/GroupA.lean` | `01e005dc5f2a14b35822a740473ff2ec568bc82eaaa25dec3b1b034e68b4f96e` |
| `DependencyAdapters.lean` | `f544ac8456f3f78f8418466ad42540519bda3cfae83789f1b3779ee1ccf5233c` |
| `contracts/GroupB.lean` | `46cb7e72de2f9436999d94d9544c2e1e54072e56adc472c47f32467e7ff95558` |
| `contracts/GroupC.lean` | `c776021ff1edd5be95c098dc44272cd7ba6ad5cdffa1e1082f891df44220c720` |
| `contracts/GroupD.lean` | `d70e4ca48cfb5a4e3183b2ea9bcf0bdedbc66d66b4ffff694225118b80aaf3e9` |

## High-risk construction interfaces

- `D-004/P-031/P-110`: finite occupied-bin coverage and the half-open bin at
  `k=0` were stress-checked against the `PosNat`/`Finset.range` design.
- `D-006/P-112/P-120/FT`: the compiled interface distinguishes convergence to
  density one, an upper-density bound, non-strict `E_alpha`, and the strict
  counterevent.
- `D-014/D-015/P-051*`: shift denominators, prime-power maxima, and
  multiplicative extensions must be structures carrying positivity and
  specification fields; no arbitrary `Classical.choose` is frozen without
  its specification.
- `P-005A/P-005`: `P005ASummabilityPayload` exposes both local summability
  families, the strict `d < X` finite-support endpoint, the nonnegative
  enlarged-majorant summability/factorization, and positive shift
  denominators. `P005Output` continues to select one positive constant from
  `(lambdaSeq,lambda)` before all `u,v,Ksh,X`.
- `P-007/P-008`: endpoint comparison uses `PositiveComparison` and retains
  finite-prefix/empty-product branches.
- `P-055`--`P-089`: endpoint-indexed families include the endpoint `z` in the
  family index, and negative powers never pass through monotonicity without
  an explicit direction lemma.
- `P-102`--`P-120`: the compiled `InteriorDensityBound` and
  `CounterexampleWitness` probes preserve the order
  `delta -> witnesses/constants -> alpha -> epsilon instantiation`.

Focused elaboration of `Interfaces.lean`, `RootObjects.lean`,
`DependencyAdapters.lean`, and all four contract modules is the S4 mechanical
gate for these shared choices.

## Provider record

| Contract family | Provider class | S4 disposition |
|---|---|---|
| finite sets, `Nat.divisors`, `Nat.primeFactors`, `Nat.factorization`, real powers/logs, filters and limits | `MATHLIB` | import and adapt without changing S3 domains |
| `EXT-001` / DP-MEAN | `NEW_FOUNDATION_REQUIRED` | mathematics closed; project dependency S4/S5/S6 owns formal provider |
| `EXT-002` / DP-MERTENS including sum constant | `NEW_FOUNDATION_REQUIRED` | mathematics closed; project dependency S4/S5/S6 owns formal provider |
| all parent P/FT contracts | `PROJECT` | task-local parametric construction in S7, real linking in S8 |
| authorized trust boundaries | none | no mathematical theorem may be admitted |

No missing mathematical source was discovered.  Missing proof terms are S7
construction obligations, not S0--S3 defects.

## Completion gate

- Assumption closure: PASS by the one-to-one contract rule and explicit
  high-risk round trip above.
- Well-posedness: PASS; every totalization hazard is either represented with
  an explicit specification/invariant or retained as an owned S7 obligation.
- Construction payload preservation: PASS; exact S3 sections are mandatory
  task payload, not summaries.
- Interface sufficiency: PASS for task planning; shared definitions, witness
  structures, density/event distinctions, and provider frames are frozen.
- Provider classification: PASS.
- Focused Lean elaboration: required before S4 acceptance.
