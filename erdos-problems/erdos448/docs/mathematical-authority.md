> Preserved authority snapshot from the input project. Historical paths and
> statuses below refer to that project; current release evidence is in
> `../stage8/preflight.json`. Original snapshot SHA-256: `ae083039dd5ab4813632c5cb61aa15e271b0a6e00394edad61d2f20c022db383`.

# Current S3 Mathematical Authority — Erdős 448

## 0. Status and scope, 2026-09-19 wrap-up

- Status: MATHEMATICAL_REPAIR_CONSTRUCTED; independent delta acceptance pending.
- Final target remains FT-448-NEG-017 / `NegativeAnswer`.
- Operational authority: `Erdos448/MODULE.json`; S7 ownership remains thirteen ROOTs.
- Mathematical authority: this file, with W0--W8 replacing only the failed
  representation/proof cone listed in `stage6/wrapup/RETIRED_TYPED_RECORDS.json`.
- The immutable report `S3_TYPED_REPAIR_ACCEPTANCE_2026-09-18.md` actually
  rejects the proxy repairs. Its earlier MODULE-level PASS label was incorrect
  and has been removed; the finding report itself is unchanged.
- No new independent audit, Lean compilation, or kernel closure is claimed.
- No whole-project rollback, content-hash gate, or provider literature restart
  is authorized by this scoped repair.

## W0. Scoped wrap-up authority and exact closure boundary

This section replaces the rejected proxy-based proof constructions in the
116 records enumerated in `stage6/wrapup/RETIRED_TYPED_RECORDS.json`, and
replaces the P-008 proof and its family-domain convention. Their old JSON
blocks remain under `mathminer-s3-legacy`, below or in the preserved
`stage3/revisions/WRAPUP_RETIRED_P008_2026-09-19.md`, solely as audit history.
They are not active proof premises, and neither their names nor an old parser
PASS supplies a theorem. Unaffected mathematical statements and proofs remain
in force. This is a bounded representation migration for this run, not a new
pipeline version or a request to reconstruct S0--S6.

For the migrated propositions, the complete, binder-faithful statement is the
corresponding `PxxxStatement` in `stage4/contracts/GroupA.lean` through
`GroupD.lean`. The construction evidence is W1--W8 below plus the preserved
S7 source identified in `stage6/wrapup/PROOF_INVENTORY.json`. In particular,
these sources replace nullary symbolic constants and unguarded selectors by
proof-bearing structures. Declaration types are statements, not proofs.
This section is a constructed mathematical repair, **not** a fresh independent
semantic-acceptance report or a new Lean/kernel verification result.

The parent task contracts remain the same thirteen ROOT ownership units plus
the existing two foundations and mean adapter. Only the P008 premise has
changed; no final-target conclusion is weakened. Preserve the old accepted
conditional proofs and recheck their changed import cone instead of requiring
all thirteen workers to prove their modules again.

## W1. Why both earlier P-008 repairs fail

The old Lean contract used pointwise positivity and uniform finite-prefix
bounds for `p<P0`. Let Q=N, c(q)=0, eta=1, C=4, P0=2, m=M=1, and
L_q(2)=1/(q+1), L_q(p)=1 for p!=2. All old premises hold, while the interval
[2,3) has product 1/(q+1). A positive family-uniform lower comparison constant
is impossible. The original Lean proof of this counterexample is retained as
`ROOT01.not_legacy_p008`, against an explicit copy of the OLD proposition.
It is not a claim that the new proposition is false.

Changing only the prefix to `p<=P0` does not fix the theorem. Instead take
C=9, P0=2, m=M=1, L_q(2)=1, L_q(3)=1/(q+1), and L_q(p)=1 otherwise.
At p=3, |L_q(3)-1|<1=9*3^(-2), so the tail premise holds; the enlarged prefix
at 2 is uniformly 1. Nevertheless [3,4) again has no positive common lower
bound. The defect is the entire finite interval before the error becomes
small, not just the equality endpoint.

**Corrected contract.** Keep the old argument order and finite-prefix upper
bound, but replace `forall q p, Prime p -> 0<L_q(p)` by

    forall q p, Prime p -> mFin <= L_q(p),    with mFin>0.

The prefix is again `2<=p<P0`; it is not used to manufacture a lower bound in
the gap. A uniform lower bound over all primes is a sufficient premise that
all actual consumers can prove: moment factors have floor 1/2; the normalized
weight Euler factors and their exact-model extensions have floor 1. Thus this
is not an extra assumption on the Erdős problem. Its discharge is W3.

## W2. Complete quantitative product proof: P-007 and corrected P-008

We prove the slightly more general lemma without the unnecessary restriction
`1+cMinus/2>0`. That restriction remains in the public P008 signature for
compatibility; it need not be used by the proof.

Fix a nonempty family Q, |c(q)|<=K with K>=0, eta,C>0, P0>=2,
0<m<=M, L_q(p)>=m for every prime p, the uniform error

    |L_q(p) - (1+c(q)/p)| <= C p^(-1-eta)    (p>=P0),

and L_q(p)<=M for 2<=p<P0. Every constant below is chosen before q,A,B.
Write mu=min(eta,1)>0 and U=max(M,1+K/2+C). The error inequality and p>=2
prove L_q(p)<=U in the tail; the prefix bound proves it elsewhere. Hence
m<=L_q(p)<=U for every prime, including any dangerous prime above P0.

Choose a real cutoff

    T=max(2,P0,4*K,(4*C)^(1/(1+eta))),     N=ceil(T).

For p>=T, delta=L_q(p)-1 satisfies
|delta|<=K/p+C p^(-1-eta)<=1/2. Taylor's formula with integral remainder gives

    |log(1+delta)-delta| <= 2 delta^2,
    |log(1-1/p)+1/p| <= 2/p^2.

For clarity, the first follows by integrating
|(1/(1+t))-1|<=2|t| between 0 and delta, and even the weaker displayed
constant 2 is valid. The second follows identically on [-1/2,0].
Set G_q(p)=L_q(p)(1-1/p)^(c(q)). Cancellation of c(q)/p gives

    |log G_q(p)|
      <= C p^(-1-eta)+4K^2 p^(-2)+4C^2 p^(-2-2eta)+2K p^(-2)
      <= E p^(-1-mu),      E=C+4K^2+4C^2+2K.

The last inequality uses p>=2 and mu<=eta,mu<=1, so every exponent on the
first line decays at least as fast as p^(-1-mu). For ANY finite subset of
tail primes, its sum of absolute logarithms is at most E/mu: dominate by
sum_{n>=2} n^(-1-mu)<=integral_1^infinity t^(-1-mu)dt=1/mu.
Thus its product of G_q lies in [exp(-E/mu),exp(E/mu)], uniformly in the
family member and both interval endpoints.

For every prime, 1/2<=1-1/p<=1 and |c(q)|<=K imply
2^(-K)<= (1-1/p)^(c(q)) <=2^K. Put

    a=min(1,m*2^(-K))>0,   b=max(1,U*2^K)>=1.

A subset of primes below T has at most N elements. Its product of G_q is
therefore between a^N and b^N. This finite-prefix argument uses the actual
uniform floor m, not a compactness assertion about an arbitrary family.
Combining both disjoint pieces, for every 2<=A<B,

    a^N exp(-E/mu) <= product_{A<=p<B}G_q(p) <= b^N exp(E/mu).       (W2.1)

Now extend EXT002's Mertens interval comparison down to 2 explicitly. Let
S(x)=product_{p<x}(1-1/p), let XM,cM-,cM+ be its supplied witnesses, and
sM=S(XM)>0. For x>=XM its interval comparison, with equality handled by the
empty product, bounds H(x)=S(x)log x between
min(1,cM-)*sM*log XM and max(1,cM+)*sM*log XM. For 2<=x<=XM, monotonicity
of the finite product gives sM<=S(x)<=1. Consequently, for all x>=2,

    hminus=min(sM*log 2, min(1,cM-)*sM*log XM)>0,
    hplus=max(log XM, max(1,cM+)*sM*log XM)>0,
    hminus <= H(x) <= hplus.

We have hminus<=hplus. Put R=hplus/hminus>=1. The exact strict-cutoff
identity S(B)/S(A)=product_{A<=p<B}(1-1/p) yields

    R^(-1) <= product_{A<=p<B}(1-1/p) / (log A/log B) <= R.

Raising this positive ratio to -c(q) places it between R^(-K) and R^K.
Since L_q=G_q*(1-1/p)^(-c(q)), (W2.1) gives the required comparison with

    Cminus=a^N*exp(-E/mu)*R^(-K),
    Cplus =b^N*exp( E/mu)*R^K.                                  (W2.2)

These explicit positive witnesses precede every q,A,B. For B<=A the filtered
prime interval is empty, so its product is exactly 1. No limit exchanging
q, no q-dependent cutoff, and no unproved uniform minimum was used.

**P008 instantiation.** Take K=max(|cMinus|,|cPlus|), m=mFin, M=MFin,
C=C_errStar, eta=etaStar, and the unchanged prefix threshold P0. Equations
(W2.1)--(W2.2) construct every field of P008Output, with the exact strict
endpoints in the Lean definition.

**P007 instantiation.** This contract permits arbitrary real c, so do not
specialize the PUBLIC P008 theorem with cMinus=c when c<=-2. Instead use the
more general proof just established with K=|c|. The P007 error holds at every
prime. Select T by the same formula with P0=2. On p>=T we have L(p)>=1/2.
The finite set `{1} union {L(p):p prime,p<T}` has a positive minimum by the
pointwise positivity hypothesis. Let m be its minimum with 1/2. This is a
legitimate choice for one FIXED L and supplies a global positive floor.
The error supplies the global upper U=1+K/2+C. Use the singleton family in
the general lemma, and set P_err=T. This constructs P007Output. The existing
`Normalization.lean` lemmas are useful alternative implementation steps,
not a reason to discard their proved estimates.

## W3. Exact consumers, fixed witnesses, and shift-product repair

### W3.1. Moment family

Use the actual `ROOT02.Mean.MomentIndex Y hY`: the index contains y in the
compact Y subset (0,2), theta>=2, sigma>=theta, and u>sigma. Inside
sigma<=p<u the local factor is

    L_i(p)=(1-1/p) sum_{j>=0} momentWeight_i(p^j)/p^j.

The supplied local-series summability theorem, nonnegative terms, and the
j=0 term=1 prove the series>=1. Thus L_i(p)>=1-1/p>=1/2. Outside that
interval the extension is 1+(y-1)/(2p), which is >=3/4 and in particular
>=1/2. Coefficients lie in [-1/2,1/2]; the existing uniform error proof and
`localFamilyConstant Y` are unchanged. P008 is instantiated with
P0=2,mFin=MFin=1/2; the finite prefix is empty, and the global lower bound is
now a real proof obligation, discharged by `localFactor_lower_half`.
All constants precede theta,sigma,u and the interval endpoints, as required.

### W3.2. Weight family and proof-bearing constants

Obtain ONE `W : CommonWeightWitnesses` from the already-constructed ROOT05
package, before theta,y,k,sigma,K,z. Do not introduce independent nullary
CSTAR/LAMBDASTAR symbols. Define

    eta=min(W.cStar,1), Cerr=W.CStar+2*W.LambdaStar,
    lambdaSeq(i)=W.LambdaStar, lambda=1.

The fields of this same W prove positivity and every common weight-type
bound. W.LambdaStar>=1 follows from its `LambdaStar_lower` field. For
w=selectedWeight(q,member) and b=modifierWeight(q), its j=0 term and
summability give localEulerFactor(w,b,p)>=1. This is also the reusable
source lemma `stage7/shared/LocalFactorFloor.lean`.

For prime p and j>=1, the exact modifier formula is

    b(p^j)=0                 if p<sigma,
           y^j               if sigma<=p<theta^k,
           1                 if max(sigma,theta^k)<=p.

Here omegaBelow counts prime factors WITH multiplicity (the factorization
exponent), so the middle factor is y^j. In particular b(p)=y. The term j=0
is always 1. The tail bound uses only 0<=y^j<=1, not an incorrect equality
b(p^j)=y for j>1. P051H therefore supplies a uniform error around
1+b(p)/(2p), with the single eta,Cerr above. `WrapupFamilies.lean` gives
literal parameter carriers and piecewise extensions. Outside the active
interval a factor is the exact model 1+y/(2p) or 1+1/(2p), hence has zero
error and floor 1. The coefficient y/2 is computed from the FAMILY INDEX;
it is not an outer y fixed before the claimed uniform constant.

The regular carrier has a concrete member theta=2,y=1/2,k=1,sigma=2,z=2,
with any WeightMember. The transition carrier has theta=2,y=1/2,k=1,
sigma=3,z=3. Thus both carriers are nonempty without invoking the theorem
being proved. Every application uses P0=2,mFin=MFin=1. All finite-prefix
premises are vacuous, but the new all-prime floor premise is not vacuous.

### W3.3. Exact shifted product, including large primes of K

Keep the current P005 formula:

    product_{p|K,p<X} localShift(u,v,p,v_p(K))
      * product_{p|K,p>=X} u(p^(v_p(K))).

The second product must not be deleted: in the exact finite expansion of
n<X, a prime p>=X can only occur at exponent zero in n, but its contribution
from K remains u(p^i). For nonnegative u,v, the existing source proves the
finite-support enlargement and termwise comparison before applying EXT001.
`ShiftedMean.lean:p005` and `Summability.lean:p005A` retain their bodies.

For any WeightTypeSpec family and a normalized modifier with 0<=b<=1, choose
lambda=1 and lambdaSeq identically max(1,Lambda). If i+j=0, the normalized
term is 1; otherwise the prime-power bound applies. W already has Lambda>=1,
so lambdaSeq=W.LambdaStar suffices for its five weights. The P005 constant
is selected now, before the shifted function, K, or X. Each small-prime
shift and each LARGE-prime u(p^i) is <=maxShift(u,v,p^i). Multiplying by
nonnegative factors bounds the entire displayed product by maxShift(u,v)(K).
There is no gcd-one assumption between n and K at this final stage.

## W4. Closed derivations for the remaining regular-mean ROOT06 nodes

Write H=theta^k, ell(z)=max(1,log z), E_w(q,z)=product_{p<z}Euler(w,b_q,p).
Using the actual factor families of W3 and corrected P008, select one B>=1
such that, uniformly in all family parameters and both relevant weights
w1,w3,

    E_w(q,z) <= B*(log z/log sigma)^(y/2)                  (sigma<=z<=H),
    E_w(q,z) <= B^2*(log H/log sigma)^(y/2)
                        *(log z/log H)^(1/2)             (sigma<=H<=z). (W4.1)

Below sigma all factors are exactly 1. The two products are over
[sigma,min(z,H)) and [H,z), so equality endpoints cause no double counting.
Empty products are exact, including sigma=H or z=H. B is obtained by taking
max(1, the TWO family upper witnesses), not by a supremum over separately
chosen pointwise witnesses.

Let D be the common P005 constant selected in W3. Then for z>=2,

    sum_{n<z} w(Kn)b_q(n) <= D*maxShift(w,b_q)(K)*z/log z*E_w(q,z). (W4.2)

For z>=2 and e in [-1,0],
(log z)^e <= L*ell(z)^e where L=max(1,(log 2)^(-1)). This follows directly
by splitting log z>=1 and log z<1. Thus all safe-log replacements have a
single absolute loss, independent of y.

**P055.** Apply the upper branch of (W4.1) to w1, then (W4.2):

    T_q(z,K) <= D B^2 w2_q(K) z (log sigma)^(-y/2)
                         (log H)^((y-1)/2)(log z)^(-1/2).

Since log H=k log theta, split its real power into k^((y-1)/2) times
(log theta)^((y-1)/2). For e=(y-1)/2 in [-1/2,0], the latter factor is at
most Atheta=max(1,(log theta)^(-1/2)). Therefore Cup=D B^2 L Atheta is
positive, is selected after theta but before q,K,z, and proves P055.

**P056.** The middle branch of (W4.1) gives

    T_q(z,K) <= D B w2_q(K) z (log sigma)^(-y/2)(log z)^(y/2-1).

Take Cmid=D B L. Since z>=sigma>=theta>=2 the safe-log replacement is
valid. The strict upper endpoint z<H is preserved; no positive gap from H
is assumed.

**P057.** Retain the existing proof. For 0<z<sigma, a positive sigma-rough
integer below z can only be 1. If z<=1 the sum is empty; if z>1 its possible
single term is w1(K), giving precisely the stated upper bound.

**P058.** In the double outer sum, P054 puts d' in the strict window
(theta^(k-1),theta^(k+2)). Keep that window. For each such d', enlarge ONLY
the d-sum from its bin/close restriction to all 0<d<theta*H; all coefficients
are nonnegative. The inner sum is (W4.2) with w3, K=d', z=theta*H.
The upper branch applies because sigma<=H. At this endpoint

    (log H)^((y-1)/2)(log(theta*H))^(-1/2)
      = k^((y-1)/2)(k+1)^(-1/2)(log theta)^(y/2-1)
      <= k^(y/2-1)*max(1,(log theta)^(-1)).

The inequality uses k>=1 and (k+1)^(-1/2)<=k^(-1/2). Summing the resulting
w4_q(d') over the RETAINED strict window gives P058 with
Cout=theta D B^2 max(1,(log theta)^(-1)). No replacement of this window by
an unrelated prefix, and no loss depending on k or y, is permitted.

**P059.** For an arbitrary nonempty family w_q with the stated common
cw,Cw,LambdaW, take lambda1=max(1,LambdaW),lambda2=1 in EXT001. This bounds
all exponents including zero. The Euler factors have floor 1 and uniform
expansion 1+1/(2p)+O((Cw+2LambdaW)p^(-1-min(cw,1))). Corrected P008 with
coefficient 1/2 gives product_{p<Z}Euler(w_q,1,p)<=B_w*(log Z/log 2)^(1/2).
Together with EXT001 this gives P059 with
Cmean=C_EXT B_w*(log 2)^(-1/2), for EVERY q and Z>=2. All constants are
selected after the family bounds and before q,Z.

For completeness, the generic P059 expansion follows directly from its own
WeightTypeSpec hypotheses and does not require putting an arbitrary family
inside W. Summability follows by comparison with max(1,LambdaW)*p^(-j).
The j>=2 tail is at most LambdaW/(p*(p-1))<=2*LambdaW/p^2. The j=1 error
is at most Cw*p^(-1-cw), while j=0 is exactly 1. Adding these two errors
and taking eta=min(cw,1) proves the stated bound, uniformly over q. The same
j=0 term proves the floor 1, so no family-wise minimum is invoked.

**P052.** Apply (W4.2) with u=a0,v=1, so its shifted product is <=w1(K),
and use the coefficient-1/2 Euler bound. For z>=2 this gives
reciprocalDivisorSum(z,K)<=C w1(K) z/sqrt(log z). There is a needed LOWER
bound on safeLogHalfSum; P053's upper bound alone would not suffice.
The number of positive integers below z is ceil(z)-1>=z/2 for z>=2.
Each m<z satisfies ell(m)<=ell(z), whence

    safeLogHalfSum(z)>=z/(2*sqrt(ell(z))).

Since ell(z)/log z<=max(1,1/log 2), the mean bound is at most
2C max(1,(log 2)^(-1/2))*w1(K)*safeLogHalfSum(z). For 0<z<=1 both sums
are zero; for 1<z<2 both have the sole integer 1, and a0(K)<=w1(K).
Taking the maximum of 1 and the displayed constant proves P052, uniformly
in K,z (in fact independent of theta). This includes z=2 without a gap.

P053, P054, and P054A are already constructed in the foundation and ROOT06
sources; retain them. ROOT06 only needs to formalize P052/P055/P056/P058/P059,
reuse the supplied P053, and assemble its existing export structure.

## W5. Closed derivations for ROOT09: P077, P082, P084

Let q be transitional: H=theta^k<sigma<theta^(k+1). Any positive sigma-rough
integer has no prime factor below H. Consequently b_q(n)=roughIndicator(n,
sigma) for n>0, and the dependence on y disappears from this modifier.
For w1 and w3, W3's transition family and P008 give one Btr>=1 such that

    E_w(q,z)<=Btr*(log z/log sigma)^(1/2)       (z>=sigma).          (W5.1)

Below sigma the Euler factor is exactly 1. Thus for the appropriate next
weight wnext (w2 or w4), (W4.2) gives

    sum_{n<z}w(Kn)b_q(n) <= D Btr wnext(K)
                              z/(sqrt(log sigma)*sqrt(log z)).  (W5.2)

The already-written `transitionEulerComparisons` calls are retained and
patched to supply lower bounds 1, not positivity. The endpoint-indexed
version in `WrapupFamilies.lean` is equivalent on the consumed intervals.

**P077.** For every high summand put z=x/(m*d*d')>=sigma. Equation (W5.2)
with w1 and the safe-log loss L proves the pointwise shifted-mean estimate
with a single CtrHigh=D Btr L. Multiply by the nonnegative outer coefficient
and ell(m)^(-1/2), then sum. This is EXACTLY
transitionRestricted.high <= CtrHigh*transitionSubstituted.high.
The constant is fixed before q,x,d,d',m; no separately chosen bound for each
z may be used. When the restricted sum is empty the assertion is immediate.

**P082.** Do not re-prove the beta integral. The existing foundation proof,
now exposed without modifying its body as `logBetaConvolutionBound`, says
for 1<M and 0<beta<=1/2,

    sum_{0<m<M} ell(m)^(-1/2)/m * ell(M/m)^(beta-1)
        <= (128/beta)*ell(2M)^(beta-1/2).

At beta=1/2 its right side is 256. For each retained pair d,d', let
M=x/(d*d'). If M<=1 the inner positive-integer sum is empty. If M>1, discard
the high restriction sigma<=M/m using nonnegativity and apply the bound:

    sum_{0<m<M, sigma<=M/m} ell(m)^(-1/2)*(M/m)*ell(M/m)^(-1/2)
        <=256 M.

P054 gives d*d'>theta^(2k-1), hence M<=theta*x/theta^(2k). Multiply by
(log sigma)^(-1/2), the actual outer coefficient and w3_q(d*d'), and sum.
This proves P082 with the explicit theta-only constant CtrH=256 theta.
The target does NOT need a new external theorem or another foundation worker.
The already-completed foundation becomes a proof-source import for ROOT09.

**P084.** As in P058, retain d' in its strict window and enlarge the d-sum
to 0<d<theta*H. Apply (W5.2) with w3, K=d', z=theta*H. Transition gives
sigma<z, so log z>log sigma>0 and

    z/(sqrt(log sigma)*sqrt(log z)) <= theta*H/log sigma.

Summing yields transitionOuter(q)<=theta D Btr H*(log sigma)^(-1)
*w4WindowSum(q). Take CtrOuter=theta D Btr, selected before q. No 1/y loss
or invented family witness is needed.

Retain ROOT09's existing P075,P076,P078,P079,P080,P081,P083 proof bodies.
After these three constructions, assemble ROOT09Target with precisely the
curried inputs in TaskContracts.lean. The extra foundation import proves a
closed theorem; it is not an extra unproved assumption on the target.

## W6. Repair the circular foundation selections using existing proofs

There is no reason to choose a member of a set whose nonemptiness is the
theorem currently being established. The preserved foundation source already
constructs concrete provider records: P053 has Cps=8; P068 has CA=256;
P069 has Cmc=256 and contains separate sharp AND enlarged middle bounds.

Use `FoundationP053.Work.result` and
`FoundationP068P069.Work.result.p068` / `.p069`. These are proof terms, not
nullary definitions that describe supposed existence. Eliminate their
Nonempty values once to obtain the witness-bearing record, and thereafter
use that SAME record's constant and bound. The inherited source constructions
are not newly kernel-certified in this environment; they are retained for
source replay. The rejected D-S811-ADM/CHOOSE loop is not a fallback.

The foundations' explicit formulas prove positivity without a choice.
P069's two subjects remain different functions with one common constant;
no sharp=enlarged identification is introduced. The public beta-convolution
wrapper is a direct application of the preexisting private theorem, and does
not alter either provider or its proof body.

## W7. Repair P090 and P112 witness scope without changing valid S7 proofs

**P090.** The canonical contract already has the necessary antecedent:
for q,k>=1 and positive n, `0<fkSharp q n` implies Nonempty(P090Witness q n).
Expand the finite nonnegative sum defining fkSharp. Its positivity implies
at least one strictly positive summand. Select d,d',t ONLY inside this
antecedent's proof. The summation membership yields positive integers,
d*d'*t|n, the bin inequalities and Close. P054 gives

    theta^(2k-1)<d*d'<=d*d'*t<=n<x.

Thus every witness field and the cutoff consequence follows. If fkSharp=0,
no tuple is needed. If a total helper function is desired, its input must
include the positive-summand proof; choosing d=d'=t=1 on an invalid branch
does not authorize a P054 application there. The live GroupD contract is
retained; unconditional W-P-090 selectors and their guard maps are retired.
ROOT11's direct finite-support argument is preserved, not re-proved merely
to conform to the rejected selector representation.

**P112.** The current P020 contract has the order

    forall epsilon (0<epsilon<=1/10),
      exists l4 : P020Output epsilon,  l4 contains Cgrid,Xi0,
        and a bound for every later xi,sigma,theta.

Obtain this ONE l4 package first. For fixed (epsilon,y), obtain the P102
package at theta=2 and its positive coefficient CP4. Put
K=(5/2)*CP4*(log 2)^(-1), Cden=1+K. The P112 result uses Cgrid=l4.Cgrid and
Xi0=l4.Xi0 literally, and its density-bound field introduces xi only AFTER
these fields have been selected. The preserved proof
`ROOT13/recovered/P110112.lean:p112_proof` follows exactly this order.
There is no evaluation of P020 at xi=sigma=theta=2 and no attempt to identify
two independently chosen existential witnesses. The old fixed-W proxy is
retired, while the already-correct proof stays unchanged.

## W8. Readiness and the work that genuinely remains

Mathematical construction is supplied above for the identified live defects
and all currently missing main-node proofs. This is not a statement that an
independent auditor has accepted it, that Lean has compiled the new patches,
or that the final negative-answer theorem is already closed.

Formal construction still owned by ROOT01: P007,P008 and final root export.
Formal construction still owned by ROOT06: P052,P055,P056,P058,P059 and its
export, reusing P053/P054/P054A/P057.
Formal construction still owned by ROOT09: P077,P082,P084 and its export,
reusing its seven completed nodes and the public beta estimate.
ROOT02 is a compatibility replay, not a new mathematical construction task.

An independent reviewer must check W1--W7 and the changed caller/definition
cone. A verifier must then compile from real Lean source (including the
restored dependency import paths), inspect assumptions, and replay the
changed import cone. Retained acceptance lineage is evidence of prior work,
not a substitute for these checks. Final S8 linking consumes the same ROOT05
weight package and the same P020 package throughout, and eliminates every
curried supplier premise. `S7_READY_CERTIFIED` must remain false until those
entry checks actually pass. No worker has been launched by this artifact.


## 1. Contract notation and global conventions

All integer variables are positive unless their domain explicitly includes
zero. All sums are over integers. Logs are natural. Empty sums equal \(0\),
empty products equal \(1\), and

\[
\ell(t):=\max(1,\log t)\qquad(t>0).
\]

The notation \(A\ll_{\mathcal P}B\) abbreviates

\[
\exists C_{\mathcal P}>0\;\forall \mathcal V:\quad A\le C_{\mathcal P}B,
\]

where the parameters in \(\mathcal P\) are quantified before the constant and
the uniform variables \(\mathcal V\) after it. Each record below gives the
actual order; the notation never supplies a hidden binder.

For premise maps, the five required entries have fixed meanings:

1. Binders: every producer binder is replaced by the displayed consumer term;
2. Hypotheses: every producer hypothesis is discharged by a displayed
   consumer fact;
3. Consumed: the exact producer conclusion used;
4. Subject: literal equality or a named adapter between producer and consumer
   subjects;
5. Constants: identity or an explicit specialization of dependence and
   uniformity.

### Hygienic symbol lineage

| Source object | Active symbol | Scope rule |
|---|---|---|
| internal source \(\varepsilon\) | \(\varepsilon_{\rm int}\) | Lemma 4 and Propositions 2–4 only |
| theorem loss \(\varepsilon\) | \(\delta\) | final density theorem only |
| Euler's base | \(\mathrm e\) | standard constant, never a binder |
| Lemma-4 grid index \(k\) | \(j\) | never a theta-bin index |
| theta-bin index | \(k\) | Propositions 1–4 |
| original close divisors | \(D,D'\) | before gcd reduction |
| reduced close divisors | \(d,d'\) | after gcd reduction |
| generic shifted integer | \(K_{\rm sh}\) | never the cutoff \(K_0\) |
| Proposition-4 power | \(a_{\rm pow}\) | never a divisor |
| final balancing powers | \(a_{\rm bal},b_{\rm bal}\) | fixed by \(y\), not free aliases |

No active normalized symbol denotes two source objects.

## 2. Active definitions — exact prenex contracts

Every definition is a root record; therefore its premise map is empty.

### D-001 — divisor count

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-001","kind":"DEFINITION","binders":[{"key":"n","type":"Nat"}],"uses_definitions":[],"source_anchors":[],"result_type":"Nat","body":"tau(n) is the cardinality of the positive divisors d of the positive integer n."}
```

- Prenex statement: \(\forall n\in\mathbb N_{>0}\), define
  \(\tau(n)=\#\{d\in\mathbb N_{>0}:d\mid n\}\).
- Local equalities: the displayed equality only.
- Domain/range: \(\tau(n)\in\mathbb N_{>0}\).
- Input subject: \(n\). Output subject: the finite divisor set and its card.
- Premise maps: none (definition root).
- Source/S2 anchor: ET pp. 18, 22; S2 R1 opening convention.

### D-002 — roughness and rough-divisor count

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-002","kind":"DEFINITION","binders":[{"key":"n","type":"Nat"},{"key":"s","type":"Real"}],"uses_definitions":[],"source_anchors":[],"result_type":{"tuple":["Real","Nat","Nat"]},"body":"For positive n and s>=2, this bundle is P^-(n), the roughness indicator chi(n,s), and tau(n,s)=sum_{d|n} chi(d,s), with P^-(1)=+infinity."}
```

- Prenex statement: \(\forall n\in\mathbb N_{>0}\;\forall s\in\mathbb R_{\ge2}\),
  define \(P^-(1)=+\infty\), \(P^-(n)\) as the least prime divisor for
  \(n>1\), \(\chi(n,s)=1_{P^-(n)\ge s}\), and
  \(\tau(n,s)=\sum_{d\mid n}\chi(d,s)\).
- Local equalities: all four displayed definitions.
- Domain/range: \(\chi\in\{0,1\}\), \(\tau(n,s)\in\mathbb N_{>0}\).
- Input subject: \((n,s)\). Output subject: roughness indicator and count.
- Premise maps: none.
- Source/S2 anchor: ET p. 22; S2 E3 and §§2–7.

### D-003 — truncated prime-factor count

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-003","kind":"DEFINITION","binders":[{"key":"n","type":"Nat"},{"key":"u","type":"Real"}],"uses_definitions":[],"source_anchors":[],"result_type":"Nat","body":"For positive n and u>0, Omega(n,u) is the sum of prime-power exponents nu over p^nu exactly dividing n with the strict cutoff p<u."}
```

- Prenex statement: \(\forall n\in\mathbb N_{>0}\;\forall u\in\mathbb R_{>0}\),
  define \(\Omega(n,u)=\sum_{p^\nu\parallel n,\ p<u}\nu\).
- Local equalities: strict prime cutoff \(p<u\).
- Domain/range: \(\Omega(n,u)\in\mathbb N\).
- Input subject: \((n,u)\). Output subject: the displayed finite sum.
- Premise maps: none.
- Source/S2 anchor: ET p. 22; S2 R1 §2 and R2.2–R2.5.

### D-004 — occupied multiplicative bins

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-004","kind":"DEFINITION","binders":[{"key":"n","type":"Nat"},{"key":"theta","type":"Real"}],"uses_definitions":["D-001"],"source_anchors":[],"result_type":"Nat","body":"For positive n and theta>1, tau^+(n,theta) is the number of natural k for which a divisor d of n lies in [theta^k,theta^(k+1)); tau^+(n)=tau^+(n,2)."}
```

- Prenex statement: \(\forall n\in\mathbb N_{>0}\;\forall\theta\in\mathbb R_{>1}\),
  define
  \[
  \tau^+(n,\theta)=\#\{k\in\mathbb N:\exists d\mid n,\
  \theta^k\le d<\theta^{k+1}\},\qquad \tau^+(n)=\tau^+(n,2).
  \]
- Local equalities: half-open bin \([\theta^k,\theta^{k+1})\).
- Domain/range: finite card in \(\mathbb N_{>0}\).
- Input subject: \((n,\theta)\). Output subject: occupied-bin set/card.
- Premise maps: none.
- Source/S2 anchor: ET pp. 18, 22; S2 R2.3.

### D-005 — strict close-pair predicate

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-005","kind":"DEFINITION","binders":[{"key":"d","type":"Nat"},{"key":"d_prime","type":"Nat"},{"key":"theta","type":"Real"}],"uses_definitions":[],"source_anchors":[],"result_type":"Prop","body":"For positive d,d' and theta>1, Close_theta(d,d') means d!=d' and 1/theta<d'/d<theta; ordered close-pair sums use this predicate."}
```

- Prenex statement: \(\forall d,d'\in\mathbb N_{>0}\;\forall\theta>1\), define
  \({\rm Close}_\theta(d,d')\) iff
  \(d\ne d'\land 1/\theta<d'/d<\theta\).
- Local equalities: \(\sum_{d,d'}^\theta\) means an ordered sum restricted by
  this predicate.
- Domain/range: Boolean predicate on ordered pairs.
- Input subject: \((d,d',\theta)\). Output subject: strict pair relation.
- Premise maps: none.
- Source/S2 anchor: ET p. 22; S2 R1 §3 and R2.3.

### D-006 — density, safe logarithm, and rough density

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-006","kind":"DEFINITION","binders":[{"key":"A","type":{"set":"Nat"}},{"key":"t","type":"Real"},{"key":"theta","type":"Real"}],"uses_definitions":[],"source_anchors":[],"result_type":{"tuple":["Real","Real","Real","Real"]},"body":"For A contained in the positive integers, t>0 and theta>=2, this bundle is upper density, lower density, ell(t)=max(1,log t), and rho_theta=product_{p<theta}(1-1/p)."}
```

- Prenex statement: \(\forall A\subseteq\mathbb N_{>0}\;\forall t>0\;
  \forall\theta\ge2\), define
  \[
  \bar d(A)=\limsup_{x\to\infty}{\#(A\cap[1,x))\over x},\quad
  \underline d(A)=\liminf_{x\to\infty}{\#(A\cap[1,x))\over x},
  \]
  \(\ell(t)=\max(1,\log t)\), and
  \(\rho_\theta=\prod_{p<\theta}(1-1/p)\).
- Local equalities: exactly the displayed formulas.
- Domain/range: densities in \([0,1]\), \(\ell(t)\ge1\), \(\rho_\theta>0\).
- Input subject: \((A,t,\theta)\). Output subject: four scalar functions.
- Premise maps: none.
- Source/S2 anchor: ET Lemma 4 and Theorem 1; ET p. 31 convention; S2 E3.

### D-007 — ambient good-divisor predicate

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-007","kind":"DEFINITION","binders":[{"key":"epsilon_int","type":"Real"},{"key":"xi","type":"Real"},{"key":"sigma","type":"Real"},{"key":"n","type":"Nat"},{"key":"d","type":"Nat"},{"key":"u","type":"Real"}],"uses_definitions":["D-003"],"source_anchors":[],"result_type":{"tuple":["Prop","Nat"]},"body":"With U0=exp(log xi log sigma), Good(n,d;epsilon_int,xi,sigma) is the displayed all-u deviation predicate on U0<=u<n, and chi_n^*(d) is its indicator."}
```

- Prenex statement:
  \(\forall\varepsilon_{\rm int}\in(0,1/10]\;\forall\xi>1\;
  \forall\sigma\ge2\;\forall n,d\in\mathbb N_{>0}\) with \(d\mid n\),
  put \(U_0=\exp((\log\xi)(\log\sigma))\) and define
  \({\rm Good}(n,d;\varepsilon_{\rm int},\xi,\sigma)\) by
  \[
  \forall u\in\mathbb R:\ U_0\le u<n\Longrightarrow
  \left|\Omega(d,u)-\tfrac12\log{\log u\over\log\sigma}\right|
  \le\varepsilon_{\rm int}\log{\log u\over\log\sigma}.
  \]
  Define \(\chi_n^*(d)\) as its indicator.
- Local equalities: \(U_0\) and the indicator equality.
- Domain/range: the predicate is used only for \(n>U_0\); \(n\le U_0\) is
  a finite exceptional range, not an empty-supremum convention.
- Input subject: \((\varepsilon_{\rm int},\xi,\sigma,n,d)\).
  Output subject: exact all-\(u\) deviation predicate.
- Premise maps: none.
- Source/S2 anchor: ET (2), pp. 25–27; S2 R1 §2.4 and R2.2–R2.3.

### D-008 — moment function

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-008","kind":"DEFINITION","binders":[{"key":"y","type":"Real"},{"key":"sigma","type":"Real"},{"key":"theta","type":"Real"},{"key":"u","type":"Real"},{"key":"n","type":"Nat"}],"uses_definitions":["D-002","D-003"],"source_anchors":[],"result_type":"Real","body":"F_{y,u}(n)=chi(n,theta)/tau(n,sigma) times sum_{d|n} y^Omega(d,u) chi(d,sigma), on 0<y<2, sigma>=theta>=2, u>sigma and positive n."}
```

- Prenex statement: \(\forall y\in(0,2)\;\forall\sigma\ge\theta\ge2\;
  \forall u>\sigma\;\forall n>0\), define
  \[
  F_{y,u}(n)={\chi(n,\theta)\over\tau(n,\sigma)}
  \sum_{d\mid n}y^{\Omega(d,u)}\chi(d,\sigma).
  \]
- Local equalities: the displayed equality.
- Domain/range: nonnegative real.
- Input subject: \((y,u,n,\sigma,\theta)\). Output: exact divisor moment.
- Premise maps: none.
- Source/S2 anchor: ET p. 25; S2 R1 (2.1), R2.1.

### D-009 — sampled grid and threshold specifications

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-009","kind":"DEFINITION","binders":[{"key":"epsilon_int","type":"Real"},{"key":"C_grid","type":"Real"},{"key":"Xi_0","type":"Real"},{"key":"xi","type":"Real"},{"key":"sigma","type":"Real"},{"key":"theta","type":"Real"},{"key":"x","type":"Real"},{"key":"j","type":"Nat"},{"key":"n","type":"Nat"},{"key":"d","type":"Nat"}],"uses_definitions":["D-002","D-003","D-006"],"source_anchors":[],"result_type":{"tuple":["Prop","Prop"]},"body":"This pair is the exact GridBound and ThresholdSpec predicates, with U0, u_j, Lambda_sigma and the upper-only terminal sample E_x^term exactly as displayed in the adjacent authority."}
```

- Prenex statement:
  \(\forall\varepsilon_{\rm int}\in(0,1/10]\;\forall C_{\rm grid}>0\;
  \forall\Xi_0>1\), define GridBound and ThresholdSpec as follows.
  GridBound\((\varepsilon_{\rm int},C_{\rm grid})\) means that for every
  \(\xi>\mathrm e\), \(\sigma\ge\theta\ge2\), \(x>U_0\), with
  \(u_j=\exp(\mathrm e^j\log\sigma\log\xi)\) and
  \[
  \Lambda_\sigma(d,u)=
  {\Omega(d,u)-\tfrac12\log(\log u/\log\sigma)
   \over\log(\log u/\log\sigma)},
  \]
  if the exact one-sided terminal-grid subject is
  \[
  E_x^{\rm term}(d)\iff
  \bigl(\exists j\in\mathbb N,\ u_j<x\ \land
    (\Lambda_\sigma(d,u_j)>0.98\varepsilon_{\rm int}
     \ \lor\ \Lambda_\sigma(d,u_j)<-0.98\varepsilon_{\rm int})\bigr)
  \ \lor\ \Lambda_\sigma(d,x)>0.98\varepsilon_{\rm int},
  \]
  then
  \[
  \sum_{n<x}{\chi(n,\theta)\over\tau(n,\sigma)}
  \#\{d\mid n:\chi(d,\sigma)=1\land E_x^{\rm term}(d)\}
  \le C_{\rm grid}x\rho_\theta
  (\log\xi)^{-0.901\varepsilon_{\rm int}^2}.
  \]
  ThresholdSpec\((\varepsilon_{\rm int},C_{\rm grid},\Xi_0)\) means that
  for every \(\xi\ge\Xi_0\),
  \[
  \xi>\mathrm e,\quad {1\over\log\log\xi}\le0.01\varepsilon_{\rm int},
  \quad 10C_{\rm grid}(\log\xi)^{-0.901\varepsilon_{\rm int}^2}
  \le(\log\xi)^{-0.9\varepsilon_{\rm int}^2}.
  \]
- Local equalities: \(U_0,u_j,\Lambda_\sigma,E_x^{\rm term}\) exactly as
  displayed. The terminal sample \(x\) occurs only in the strict upper tail;
  lower-tail terminal interpolation returns to the left grid sample.
- Domain/range: all sums finite; terminal sample is the legal \(u=x\).
- Input subject: endpoint exceptional mass. Output: two exact predicates.
- Premise maps: none.
- Source/S2 anchor: ET pp. 26–27; S2 R2.1–R2.2.

### D-010 — Lemma-4 set specification

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-010","kind":"DEFINITION","binders":[{"key":"epsilon_int","type":"Real"},{"key":"xi","type":"Real"},{"key":"sigma","type":"Real"},{"key":"theta","type":"Real"},{"key":"A","type":{"set":"Nat"}}],"uses_definitions":["D-002","D-006","D-007"],"source_anchors":[],"result_type":"Prop","body":"L4Spec(A) is the exact rough-support, lower-density and nine-tenths good-divisor-mass specification displayed in this section."}
```

- Prenex statement:
  \(\forall\varepsilon_{\rm int}\in(0,1/10]\;\forall\xi>1\;
  \forall\sigma\ge\theta\ge2\;\forall\mathcal A\subseteq\mathbb N_{>0}\),
  define L4Spec\((\varepsilon_{\rm int},\xi,\sigma,\theta,\mathcal A)\)
  to be the conjunction
  \[
  \forall n\in\mathcal A,\ \chi(n,\theta)=1,
  \]
  \[
  \underline d(\mathcal A)\ge
  \bigl(1-(\log\xi)^{-(9/10)\varepsilon_{\rm int}^2}\bigr)\rho_\theta,
  \]
  \[
  \forall n\in\mathcal A,\quad
  \sum_{d\mid n}\chi(d,\sigma)\chi_n^*(d)
  \ge{9\over10}\tau(n,\sigma).
  \]
- Local equalities: the three clauses only.
- Domain/range: set predicate.
- Input subject: \((\varepsilon_{\rm int},\xi,\sigma,\theta,\mathcal A)\).
  Output subject: exact Lemma-4 witness specification.
- Premise maps: none.
- Source/S2 anchor: ET Lemma 4, pp. 25–27; S2 R1 (2.9)–(2.10), R2.2.

### D-011 — occupied good-bin data

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-011","kind":"DEFINITION","binders":[{"key":"epsilon_int","type":"Real"},{"key":"xi","type":"Real"},{"key":"sigma","type":"Real"},{"key":"theta","type":"Real"},{"key":"A","type":{"set":"Nat"}},{"key":"n","type":"Nat"},{"key":"k","type":"Nat"}],"uses_definitions":["D-004","D-007","D-010"],"source_anchors":[],"result_type":{"tuple":[{"fn":{"args":["Nat"],"return":"Nat"}},{"set":"Nat"},"Nat",{"fn":{"args":["Nat"],"return":"Nat"}}]},"body":"For n in the Lemma-4 set and k natural, this ordered bundle is the occupied good-bin count function nu, its finite occupied-bin index set I, the cardinality r, and the canonical increasing enumeration i |-> k_i."}
```

- Prenex statement:
  \(\forall\varepsilon_{\rm int}\in(0,1/10]\;\forall\xi>1\;
  \forall\sigma\ge\theta\ge2\;\forall\mathcal A\subseteq\mathbb N_{>0}\;
  \forall n\in\mathcal A\;\forall k\in\mathbb N\), define
  \[
  \nu_{n,\mathcal A}(k)=
  \#\{d\mid n:\theta^k\le d<\theta^{k+1},\
  \chi(d,\sigma)=1,\ {\rm Good}(n,d;\varepsilon_{\rm int},\xi,\sigma)\},
  \]
  \(I_{n,\mathcal A}=\{k\in\mathbb N:\nu_{n,\mathcal A}(k)>0\}\),
  \(r=\#I_{n,\mathcal A}\), and
  \(k_1<\cdots<k_r\) is the increasing enumeration of this finite set.
- Local equalities: all four displayed definitions, including \(r=\#I\).
- Domain/range: \(\nu,r\in\mathbb N\); enumeration length is exactly \(r\).
- Input subject: selected Lemma-4 set and one member \(n\).
  Output subject: count function, support set, card, enumeration.
- Premise maps: none.
- Source/S2 anchor: ET Proposition 1, p. 28; S2 R1 §3.

### D-012 — close-pair sum and normalized function

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-012","kind":"DEFINITION","binders":[{"key":"epsilon_int","type":"Real"},{"key":"xi","type":"Real"},{"key":"sigma","type":"Real"},{"key":"theta","type":"Real"},{"key":"n","type":"Nat"}],"uses_definitions":["D-001","D-002","D-005","D-007"],"source_anchors":[],"result_type":{"tuple":["Real","Real"]},"body":"This pair is the exact ordered close-pair sum Q(n) and f(n)=chi(n,theta)Q(n)/tau(n), with the displayed good-divisor weight."}
```

- Prenex statement:
  \(\forall\varepsilon_{\rm int}\in(0,1/10]\;\forall\xi>1\;
  \forall\sigma\ge\theta\ge2\;\forall n>0\), define
  \[
  Q(n)=\sum_{\substack{d,d'\mid n\\{\rm Close}_\theta(d,d')}}
  \chi(d,\sigma)\chi_n^*(d),\qquad
  f(n)={\chi(n,\theta)Q(n)\over\tau(n)}.
  \]
- Local equalities: exact asymmetric ordered pair sum and normalized function.
- Domain/range: nonnegative reals.
- Input subject: \((n,\varepsilon_{\rm int},\xi,\sigma,\theta)\).
  Output subject: \(Q(n),f(n)\).
- Premise maps: none.
- Source/S2 anchor: ET pp. 28–29; S2 R1 §§3–4.

### D-013 — typed half-open \(f_k^\#\)

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-013","kind":"DEFINITION","binders":[{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"},{"key":"theta","type":"Real"},{"key":"n","type":"Nat"}],"uses_definitions":["D-001","D-002","D-003","D-005"],"source_anchors":[],"result_type":"Real","body":"f_k^#(y,n) is the exact finite half-open divisor/triple sum displayed here, with theta^k<=d<theta^(k+1), strict Close_theta, and the stated rough/moment weights."}
```

- Prenex statement: \(\forall y\in(0,1)\;\forall k\in\mathbb N\;
  \forall\sigma\ge\theta\ge2\;\forall n>0\), define
  \[
  f_k^\#(y,n)={1\over\tau(n)}
  \sum_{\substack{d,d',t>0:\ dd't\mid n\\
  \theta^k\le d<\theta^{k+1}\\{\rm Close}_\theta(d,d')}}
  \chi(d,\sigma)y^{\Omega(dt,\theta^k)}\chi(t,\sigma).
  \]
- Local equalities: \(dd't\mid n\) is part of the index; no untyped quotient.
- Domain/range: finite nonnegative sum.
- Input subject: \((y,k,n,\sigma,\theta)\). Output subject: exact \(f_k^\#\).
- Premise maps: none.
- Source/S2 anchor: ET pp. 29–30; S2 R1 (5.1), R2.3–R2.4.

### D-014 — type-\(\tau^{-1}\) predicate and shifts

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-014","kind":"DEFINITION","binders":[{"key":"w","type":{"fn":{"args":["Nat"],"return":"Real"}}},{"key":"a","type":{"fn":{"args":["Nat"],"return":"Real"}}},{"key":"b","type":{"fn":{"args":["Nat"],"return":"Real"}}},{"key":"p","type":"Nat"},{"key":"i","type":"Nat"},{"key":"j","type":"Nat"}],"uses_definitions":[],"source_anchors":[],"result_type":{"tuple":["Prop","Real",{"fn":{"args":["Nat"],"return":"Real"}},{"fn":{"args":["Nat"],"return":"Real"}}]},"body":"This bundle is the exact TauInvType predicate, local shift quotient S[a,b](p^i), its multiplicative extension, and the hatted prime-power maximum/extension, including the displayed local conditions and existential c,C order."}
```

- Prenex statement: \(\forall w:\mathbb N_{>0}\to\mathbb R_{\ge0}\), define
  TauInvType\((w)\) by
  \[
  \exists c,C>0\;\forall p\ {\rm prime}\;\forall i\ge1:\quad
  |w(p^i)-1/(i+1)|\le Cp^{-c}.
  \]
  For nonnegative multiplicative \(a,b\) satisfying the ET-L2 local bounds,
  define for every prime \(p\) and \(i\ge1\)
  \[
  \mathcal S[a,b](p^i)=
  {\sum_{j\ge0}a(p^{i+j})b(p^j)(1+j\log p)p^{-j}
   \over\sum_{j\ge0}a(p^j)b(p^j)p^{-j}},
  \]
  \(\widehat{\mathcal S}[a,b](p^i)=
  \max(\mathcal S[a,b](p^i),a(p^i))\), extending both multiplicatively.
- Local equalities: exact local quotient and prime-power maximum.
- Domain/range: denominator positive; nonnegative multiplicative outputs.
- Input subject: \(w\) or \((a,b,p,i)\). Output: predicate/operators.
- Premise maps: none.
- Source/S2 anchor: ET Lemma 2, pp. 23–24 and p. 30; S2 R2.4.

### D-015 — exact weight-witness chain

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-015","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"},{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"}],"uses_definitions":["D-001","D-002","D-003","D-014"],"source_anchors":[],"result_type":{"tuple":[{"fn":{"args":["Nat"],"return":"Real"}},{"fn":{"args":["Nat"],"return":"Real"}},{"fn":{"args":["Nat"],"return":"Real"}},{"fn":{"args":["Nat"],"return":"Real"}},{"fn":{"args":["Nat"],"return":"Real"}},{"fn":{"args":["Nat"],"return":"Real"}}]},"body":"This ordered bundle is the exact weight-witness chain a0,v_k,w1,w2_k,w3_k,w4_k defined in the adjacent authority, without identifying any distinct weight."}
```

- Prenex statement: \(\forall y\in(0,1)\;\forall k\ge1\;
  \forall\sigma\ge\theta\ge2\), define
  \[
  a_0(n)=1/\tau(n),\quad w_1=\widehat{\mathcal S}[a_0,1],\quad
  v_k(t)=y^{\Omega(t,\theta^k)}\chi(t,\sigma),
  \]
  \[
  w_{2,k}=\widehat{\mathcal S}[w_1,v_k],\quad
  w_{3,k}(p^i)=\max(w_1(p^i),w_{2,k}(p^i))
  \text{ with multiplicative extension},
  \]
  and \(w_{4,k}=\widehat{\mathcal S}[w_{3,k},v_k]\).
- Local equalities: the complete deterministic chain above.
- Domain/range: nonnegative multiplicative functions once the applicable
  P-051F1--P-051F4 construction record is applied.
- Input subject: \((y,k,\sigma,\theta)\). Output: all six functions.
- Premise maps: none.
- Source/S2 anchor: ET pp. 30–31; S2 R2.4.

### D-016 — shifted \(t\)-mean

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-016","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"},{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"},{"key":"z","type":"Real"},{"key":"K_sh","type":"Nat"}],"uses_definitions":["D-015"],"source_anchors":[],"result_type":"Real","body":"T_k(z,K_sh)=sum_{t<z} v_k(t) w1(t K_sh), on the displayed positive domains."}
```

- Prenex statement: \(\forall y\in(0,1)\;\forall k\ge1\;
  \forall\sigma\ge\theta\ge2\;\forall z>0\;\forall K_{\rm sh}\ge1\), define
  \[
  T_k(z,K_{\rm sh})=\sum_{t<z}v_k(t)w_1(tK_{\rm sh}).
  \]
- Local equalities: \(v_k,w_1\) are exactly D-015.
- Domain/range: finite nonnegative sum.
- Input subject: \((z,K_{\rm sh})\). Output: exact shifted mean subject.
- Premise maps: none.
- Source/S2 anchor: ET pp. 30–31; S2 R2.5.

### D-017 — lower bin index and Proposition-3 subject

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-017","kind":"DEFINITION","binders":[{"key":"sigma","type":"Real"},{"key":"theta","type":"Real"},{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"x","type":"Real"}],"uses_definitions":["D-013"],"source_anchors":[],"result_type":{"tuple":["Nat","Real"]},"body":"This pair is K0(sigma,theta)=max(1,ceil((log sigma)/(2 log theta))) and S_k(x,y;sigma,theta)=sum_{n<x} f_k^#(y,n)."}
```

- Prenex statement: \(\forall\sigma\ge\theta\ge2\), define
  \(K_0(\sigma,\theta)=\max(1,\lceil\frac12\log\sigma/\log\theta\rceil)\).
  For every \(0<y<1,k\ge1,x>0\), define
  \(S_k(x,y;\sigma,\theta)=\sum_{n<x}f_k^\#(y,n)\).
- Local equalities: exact \(K_0\) and \(S_k\).
- Domain/range: \(K_0\in\mathbb N_{>0}\); \(S_k\ge0\).
- Input subject: \((\sigma,\theta,y,k,x)\). Output: cutoff and exact mean.
- Premise maps: none.
- Source/S2 anchor: ET pp. 29–31; S2 R2.7 and R1 (5.1).

### D-018 — regular outer and convolution subjects

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-018","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"},{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"},{"key":"x","type":"Real"}],"uses_definitions":["D-002","D-003","D-005","D-006","D-015"],"source_anchors":[],"result_type":{"tuple":["Real","Real","Real","Real","Real","Real","Real","Real"]},"body":"The ordered eight-real bundle is O_k,A_k,B_k^#,B_k^enl,C_k,R_k^A,R_k^B,R_k^C with the exact half-open endpoints and distinct sharp/enlarged middle subjects displayed here."}
```

- Prenex statement: \(\forall y\in(0,1)\;\forall k\ge1\;
  \forall\sigma\ge\theta\ge2\;\forall x>0\), define
  \[
  O_k=\sum_{\substack{d,d'>0\\\theta^k\le d<\theta^{k+1}\\
  {\rm Close}_\theta(d,d')}}
  \chi(d,\sigma)y^{\Omega(d,\theta^k)}w_{3,k}(dd'),
  \]
  \[
  A_k={x\over\theta^{2k}}k^{(y-1)/2}
  \sum_{m<x\theta^{1-3k}}{\ell(m)^{-1/2}\over m}
  \ell(x\theta^{1-2k}/m)^{-1/2},
  \]
  \[
  B_k^{\#}(x;y)={x\over\theta^{2k}}
  \sum_{x\theta^{1-3k}\le m<x\theta^{1-2k}}
  {\ell(m)^{-1/2}\over m}
  \ell(x\theta^{1-2k}/m)^{y/2-1},
  \]
  \[
  B_k^{\rm enl}(x;y)={x\over\theta^{2k}}
  \sum_{x\theta^{-3k-3}<m<x\theta^{1-2k}}
  {\ell(m)^{-1/2}\over m}
  \ell(x\theta^{1-2k}/m)^{y/2-1},
  \]
  \[
  C_k={x\over\theta^{2k}}(\log\sigma)^{y/2}
  \ell(2x\theta^{1-2k})^{-1/2},
  \]
  and \(R_k^A=(\log\sigma)^{-y/2}O_kA_k\),
  \(R_k^B=(\log\sigma)^{-y/2}O_kB_k^{\rm enl}\),
  \(R_k^C=(\log\sigma)^{-y/2}O_kC_k\).
- Local equalities: all eight exact subjects above. \(B_k^{\#}\) is the exact
  accepted R3 middle convolution with weak lower and strict upper endpoint.
  The different subject \(B_k^{\rm enl}\) has lower endpoint
  \(x\theta^{-3k-3}\), the uniform product-window endpoint
  induced by \(dd'<\theta^{2k+3}\); P-065 supplies the explicit nonnegative
  restriction/enlargement adapter from the variable-\(dd'\) subject to
  \(B_k^{\rm enl}\). The two subjects are never identified.
- Domain/range: finite nonnegative sums/products; literal half-open bin and
  strict close-pair window.
- Input subject: \((y,k,\sigma,\theta,x)\). Output: the eight subjects.
- Premise maps: none.
- Source/S2 anchor: ET pp. 30–31; S2 R1 (5.5)–(5.10), R2.6.

### D-019 — exact smoothed regular subject and partition

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-019","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"},{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"},{"key":"x","type":"Real"}],"uses_definitions":["D-002","D-003","D-005","D-006","D-015","D-016"],"source_anchors":[],"result_type":{"tuple":["Real","Real","Real","Real"]},"body":"With z_m=x/(mdd'), this bundle is U_k and its exact upper, middle and terminal restrictions on z_m, all with identical outer indices and weights."}
```

- Prenex statement: \(\forall y\in(0,1)\;\forall k\ge1\;
  \forall\sigma\ge\theta\ge2\) with \(\sigma\le\theta^k\),
  \(\forall x>\theta^{2k-1}\), put \(z_m=x/(mdd')\) locally and define
  \[
  U_k=\sum_{\substack{d,d'>0\\\theta^k\le d<\theta^{k+1}\\
  {\rm Close}_\theta(d,d')}}
  \chi(d,\sigma)y^{\Omega(d,\theta^k)}
  \sum_{m<x/(dd')}\ell(m)^{-1/2}T_k(z_m,dd').
  \]
  Define \(U_k^{\rm up},U_k^{\rm mid},U_k^{\rm term}\) by the same
  formula with the inner \(m\)-sum restricted respectively to
  \(z_m\ge\theta^k\), \(\sigma\le z_m<\theta^k\), and \(z_m<\sigma\).
- Local equalities: \(z_m=x/(mdd')\); all four formulas use identical outer
  indices and weights.
- Domain/range: exact finite nonnegative subjects.
- Input subject: smoothed four-variable regular mean. Output: whole and three
  restricted subjects.
- Premise maps: none.
- Source/S2 anchor: ET pp. 30–31; S2 R1 (5.1)–(5.5), R2.5a.

### D-020 — exact regular substituted subjects

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-020","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"},{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"},{"key":"x","type":"Real"}],"uses_definitions":["D-002","D-003","D-005","D-006","D-015"],"source_anchors":[],"result_type":{"tuple":["Real","Real","Real"]},"body":"This triple is the exact regular substituted subjects M_k^up,M_k^mid,M_k^term, including their displayed z_m branches, weights and endpoints."}
```

- Prenex statement: \(\forall y\in(0,1)\;\forall k\ge1\;
  \forall\theta\ge2\;\forall\sigma\in[\theta,\theta^k]\;
  \forall x>\theta^{2k-1}\), define
  \[
  M_k^{\rm up}=(\log\sigma)^{-y/2}k^{(y-1)/2}
  \sum_{d,d'}^{\theta,[k]}\chi(d,\sigma)y^{\Omega(d,\theta^k)}w_{2,k}(dd')
  \sum_{\substack{m<x/(dd')\\z_m\ge\theta^k}}
  \ell(m)^{-1/2}z_m\ell(z_m)^{-1/2},
  \]
  \[
  M_k^{\rm mid}=(\log\sigma)^{-y/2}
  \sum_{d,d'}^{\theta,[k]}\chi(d,\sigma)y^{\Omega(d,\theta^k)}w_{2,k}(dd')
  \sum_{\substack{m<x/(dd')\\\sigma\le z_m<\theta^k}}
  \ell(m)^{-1/2}z_m\ell(z_m)^{y/2-1},
  \]
  \[
  M_k^{\rm term}=
  \sum_{d,d'}^{\theta,[k]}\chi(d,\sigma)y^{\Omega(d,\theta^k)}w_1(dd')
  \sum_{\substack{m<x/(dd')\\z_m<\sigma}}\ell(m)^{-1/2},
  \]
  where \(\sum_{d,d'}^{\theta,[k]}\) is the literal index
  \(\theta^k\le d<\theta^{k+1}\land{\rm Close}_\theta(d,d')\) and
  \(z_m=x/(mdd')\).
- Local equalities: exact index expansion and \(z_m\).
- Domain/range: three exact nonnegative mixed sums.
- Input subject: the three restricted U-subjects. Output: three mixed sums.
- Premise maps: none.
- Source/S2 anchor: ET p. 30; S2 R1 (5.3), R2.14.

### D-021a — transition smoothed subject

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-021a","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"},{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"},{"key":"x","type":"Real"}],"uses_definitions":["D-002","D-003","D-005","D-006","D-015","D-016"],"source_anchors":[],"result_type":"Real","body":"V_k is the exact transition smoothed subject on theta^k<sigma<theta^(k+1) and x>theta^(2k-1)."}
```

- Prenex statement: \(\forall y\in(0,1)\;\forall k\in\mathbb N_{\ge1}\;
  \forall\theta\in\mathbb R_{\ge2}\;\forall\sigma\in\mathbb R\;
  \forall x\in\mathbb R_{>\theta^{2k-1}}\), if
  \(\theta^k<\sigma<\theta^{k+1}\), define
  \[
  V_k=\sum_{d,d'}^{\theta,[k]}\chi(d,\sigma)y^{\Omega(d,\theta^k)}
  \sum_{m<x/(dd')}\ell(m)^{-1/2}T_k(x/(mdd'),dd').
  \]
- Premise maps: none. Source/S2 anchor: S2 R2.5c.

### D-021b — exact transition high/low restrictions

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-021b","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"},{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"},{"key":"x","type":"Real"}],"uses_definitions":["D-021a"],"source_anchors":[],"result_type":{"tuple":["Real","Real"]},"body":"With z_m=x/(mdd'), this pair is the exact transition restrictions V_k^ge and V_k^lt at z_m>=sigma and z_m<sigma."}
```

- Prenex statement: on the complete typed domain of D-021a, put
  \(z_m=x/(mdd')\) and define
  \[
  V_k^{\ge}=\sum_{d,d'}^{\theta,[k]}\chi(d,\sigma)y^{\Omega(d,\theta^k)}
  \sum_{\substack{m<x/(dd')\\z_m\ge\sigma}}
  \ell(m)^{-1/2}T_k(z_m,dd'),
  \]
  \[
  V_k^{<}=\sum_{d,d'}^{\theta,[k]}\chi(d,\sigma)y^{\Omega(d,\theta^k)}
  \sum_{\substack{m<x/(dd')\\z_m<\sigma}}
  \ell(m)^{-1/2}T_k(z_m,dd').
  \]
- Premise maps: none. Source/S2 anchor: S2 R2.15.

### D-021c — transition substituted subjects

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-021c","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"},{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"},{"key":"x","type":"Real"}],"uses_definitions":["D-002","D-003","D-005","D-006","D-015"],"source_anchors":[],"result_type":{"tuple":["Real","Real"]},"body":"This pair is the exact substituted transition subjects H_tilde_k and L_tilde_k with the displayed weights and high/low z_m restrictions."}
```

- Prenex statement: on the complete typed domain of D-021a, define
  \[
  \widetilde H_k=(\log\sigma)^{-1/2}
  \sum_{d,d'}^{\theta,[k]}\chi(d,\sigma)y^{\Omega(d,\theta^k)}w_{2,k}(dd')
  \sum_{\substack{m<x/(dd')\\z_m\ge\sigma}}
  \ell(m)^{-1/2}z_m\ell(z_m)^{-1/2},
  \]
  \[
  \widetilde L_k=
  \sum_{d,d'}^{\theta,[k]}\chi(d,\sigma)y^{\Omega(d,\theta^k)}w_1(dd')
  \sum_{\substack{m<x/(dd')\\z_m<\sigma}}\ell(m)^{-1/2},
  \]
- Premise maps: none. Source/S2 anchor: S2 R2.15.

### D-021d — transition weight-transported subjects

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-021d","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"},{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"},{"key":"x","type":"Real"}],"uses_definitions":["D-002","D-003","D-005","D-006","D-015"],"source_anchors":[],"result_type":{"tuple":["Real","Real"]},"body":"This pair is the exact weight-transported transition subjects H_k and L_k, using w3_k and the displayed high/low restrictions."}
```

- Prenex statement: on the complete typed domain of D-021a, define
  \[
  H_k=(\log\sigma)^{-1/2}
  \sum_{d,d'}^{\theta,[k]}\chi(d,\sigma)y^{\Omega(d,\theta^k)}w_{3,k}(dd')
  \sum_{\substack{m<x/(dd')\\z_m\ge\sigma}}
  \ell(m)^{-1/2}z_m\ell(z_m)^{-1/2},
  \]
  \[
  L_k=\sum_{d,d'}^{\theta,[k]}\chi(d,\sigma)y^{\Omega(d,\theta^k)}w_{3,k}(dd')
  \sum_{\substack{m<x/(dd')\\z_m<\sigma}}\ell(m)^{-1/2}.
  \]
- Premise maps: none. Source/S2 anchor: S2 R2.4 and R2.15.

### D-021e — transition outer subject

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-021e","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"},{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"},{"key":"d","type":"Nat"},{"key":"d_prime","type":"Nat"}],"uses_definitions":["D-002","D-003","D-005","D-015"],"source_anchors":[],"result_type":"Real","body":"O_k^tr is the exact outer transition sum, independent of x, on theta^k<sigma<theta^(k+1)."}
```

- Prenex statement: \(\forall y\in(0,1)\;\forall k\in\mathbb N_{\ge1}\;
  \forall\theta\in\mathbb R_{\ge2}\;\forall\sigma\in\mathbb R\), if
  \(\theta^k<\sigma<\theta^{k+1}\), define, independently of \(x\),
  \[
  O_k^{\rm tr}=\sum_{d,d'}^{\theta,[k]}
  \chi(d,\sigma)y^{\Omega(d,\theta^k)}w_{3,k}(dd').
  \]
- Premise maps: none. Source/S2 anchor: S2 R2.16.

### D-022 — moving cutoff and target event

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-022","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"},{"key":"x","type":"Real"},{"key":"alpha","type":"Real"}],"uses_definitions":["D-001","D-004"],"source_anchors":[],"result_type":{"tuple":["Real","Int",{"set":"Nat"}]},"body":"This bundle is X_theta(x)=(1+log x/log theta)/2, N_theta(x)=ceil(X_theta(x))-1, and E_alpha={positive n: tau^+(n)<=alpha tau(n)}."}
```

- Prenex statement: \(\forall\theta\ge2\;\forall x>0\), define
  \[
  X_\theta(x)=\tfrac12\left(1+{\log x\over\log\theta}\right),\qquad
  N_\theta(x)=\lceil X_\theta(x)\rceil-1.
  \]
  For \(0\le\alpha\le1\), define
  \(E_\alpha=\{n>0:\tau^+(n)\le\alpha\tau(n)\}\).
- Local equalities: both cutoff formulas and exact event.
- Domain/range: \(X_\theta(x)\in\mathbb R\), \(N_\theta(x)\in\mathbb Z\).
- Input subject: \((\theta,x,\alpha)\). Output: moving endpoint and event.
- Premise maps: none.
- Source/S2 anchor: ET pp. 31–32; S2 R1 §6 and R2.7.

## 3. External leaves and recursive provider frames

### EXT-001 — nonnegative multiplicative mean theorem

```mathminer-s3
{"schema":"mathminer.s3/1","id":"EXT-001","kind":"EXTERNAL_THEOREM","binders":[{"key":"h","type":{"fn":{"args":["Nat"],"return":"Real"}}},{"key":"lambda_1","type":"Real"},{"key":"lambda_2","type":"Real"},{"key":"X","type":"Real"}],"uses_definitions":["DP-MEAN::DP-MEAN-DEF-006","DP-MEAN::DP-MEAN-DEF-007","DP-MEAN::DP-MEAN-DEF-008","DP-MEAN::DP-MEAN-DEF-025"],"source_anchors":[],"hypotheses":[{"key":"h_nonnegative_multiplicative","proposition":{"op":{"name":"and","args":[{"def":{"id":"DP-MEAN::DP-MEAN-DEF-006","args":[{"var":"h"}]}},{"def":{"id":"DP-MEAN::DP-MEAN-DEF-007","args":[{"var":"h"}]}}]}}},{"key":"prime_power_geometric_bound","proposition":{"def":{"id":"DP-MEAN::DP-MEAN-DEF-008","args":[{"var":"h"},{"var":"lambda_1"},{"var":"lambda_2"}]}}},{"key":"lambda_1_nonnegative","proposition":{"op":{"name":"ge","args":[{"var":"lambda_1"},{"lit":{"type":"Real","value":"0"}}]}}},{"key":"lambda_2_range","proposition":{"op":{"name":"and","args":[{"op":{"name":"ge","args":[{"var":"lambda_2"},{"lit":{"type":"Real","value":"0"}}]}},{"op":{"name":"lt","args":[{"var":"lambda_2"},{"lit":{"type":"Real","value":"2"}}]}}]}}},{"key":"X_at_least_2","proposition":{"op":{"name":"ge","args":[{"var":"X"},{"lit":{"type":"Real","value":"2"}}]}}}],"witnesses":[{"key":"C_EXT","type":"Real","depends_on":["lambda_1","lambda_2"]}],"conclusions":[{"key":"mean_bound","proposition":{"def":{"id":"DP-MEAN::DP-MEAN-DEF-025","args":[{"var":"h"},{"var":"lambda_1"},{"var":"lambda_2"},{"var":"X"},{"var":"C_EXT"}]}}}],"premises":[],"witness_realizations":{},"proof_ref":"### EXT-001 — nonnegative multiplicative mean theorem","provider":{"dependency":"DP-MEAN-017","export":"DP-MEAN-T001","contract_hash":"4b7a4e7df2cb622f6cca1920b2bb43dbb41c9c5aef18cd206b6fcc2a4ff1e2a2"}}
```

- Prenex statement:
  \[
  \forall h\ {\rm nonnegative\ multiplicative}\;
  \forall\lambda_1\ge0\;\forall\lambda_2\in[0,2)\;
  \forall X\in\mathbb R_{\ge2},
  \]
  if \(\forall p\) prime \(\forall j\ge0,\ 
  0\le h(p^j)\le\lambda_1\lambda_2^j\), then
  \[
  \sum_{n<X}h(n)\ll_{\lambda_1,\lambda_2}
  {X\over\log X}\prod_{p<X}\sum_{j\ge0}h(p^j)p^{-j}.
  \]
- Local equalities: none.
- Domain/range: all displayed local series converge by the geometric bound.
- Input subject: \(h\) and its prime-power bounds. Output: exact mean bound.
- Premise maps: none (external root).
- Derivation certificate: opaque only in the parent problem.
- Source/S2 anchor: ET Lemma 1, pp. 22–23; S2 E1.
- Definitions used: none.

### EXT-002 — Mertens product asymptotic and interval comparison

```mathminer-s3
{"schema":"mathminer.s3/1","id":"EXT-002","kind":"EXTERNAL_THEOREM","binders":[],"uses_definitions":["DP-MERTENS::D-MERT-01","DP-MERTENS::S-FT-MERTENS","DP-MERTENS::S-MERT-08"],"source_anchors":[],"hypotheses":[],"witnesses":[{"key":"X_0","type":"Real","depends_on":[]},{"key":"c_minus","type":"Real","depends_on":[]},{"key":"c_plus","type":"Real","depends_on":[]}],"conclusions":[{"key":"mertens_prime_product_asymptotic","proposition":{"def":{"id":"DP-MERTENS::S-FT-MERTENS","args":[]}}},{"key":"moving_endpoint_comparison","proposition":{"def":{"id":"DP-MERTENS::S-MERT-08","args":[{"var":"X_0"},{"var":"c_minus"},{"var":"c_plus"}]}}}],"premises":[],"witness_realizations":{},"proof_ref":"### EXT-002 — Mertens product asymptotic and interval comparison","provider":{"dependency":"DP-MERTENS-017","export":"FT-MERTENS","contract_hash":"c5a8355dfe3de1d078d6db208f87bea59168b516e753369226ce39f640bf188d"}}
```

- Prenex statement: for \(x\ge2\), put
  \(Q_{<}(x)=\prod_{p<x}(1-1/p)\).  Then, as \(x\to\infty\),
  \[
  Q_{<}(x)\sim {\mathrm e^{-\gamma}\over\log x}.
  \tag{EXT002-asymp}
  \]
  Consequently there exist \(X_{\rm M}\ge2\) and
  \(c_{{\rm M},-},c_{{\rm M},+}>0\) such that, uniformly for
  \(B>A\ge X_{\rm M}\),
  \[
  c_{{\rm M},-}{\log A\over\log B}
  \le\prod_{A\le p<B}(1-1/p)
  \le c_{{\rm M},+}{\log A\over\log B}.
  \tag{EXT002-interval}
  \]
- Local equalities: the strict-endpoint product \(Q_{<}\) displayed above.
- Domain/range: positive real asymptotic and positive finite interval products.
- Input subject: strict prime product through \(x\). Output: the asymptotic
  and its exact large-endpoint interval comparison.
- Premise maps: none (external root).
- Derivation certificate: opaque only in the parent problem.
- Source/S2 anchor: DP-MERTENS `FT-MERTENS`, exact endpoint adapter
  `P-MERT-06B`, and parent-consumer comparison `P-MERT-08`; S2 E2.
- Definitions used: none.

### DP-MEAN-017

    dependency_problem_id: DP-MEAN-017
    semantic_key: nonnegative-multiplicative-geometric-local-bound-implies-euler-product-mean-bound
    target_statement: EXT-001 exactly
    binders: [EXT-001.b.h, EXT-001.b.lambda_1, EXT-001.b.lambda_2, EXT-001.b.X]
    hypotheses: [EXT-001.h.01]
    required_closure: KERNEL_CLOSED
    closure_role: REQUIRED
    parent_problem_id: ERDOS-448
    parent_obligation: EXT-001
    consumer_nodes: [P-002, P-011, P-059]
    continuation:
      action: resume ERDOS-448 S4 provider resolution and all semantic descendants
      entry_stage: S1
      current_stage: S3_AUDIT_PASSED
    source_authority_status:
      status: AVAILABLE_CERTIFIED
      proof_context_available: true
      anchor: Halberstam-Richert pp. 77-82
    provider_status: unresolved; S4 not entered
    authority_paths: [Erdos448/dependencies/DP-MEAN, Erdos448/dependencies/DP-MEAN/stage3/audits/S3_AUDIT_A1_2026-09-13.md]
    child_dependency_problems: []
    status: MATH_CLOSED
    last_semantic_commit: UNAVAILABLE_NO_GIT_REPOSITORY
    last_semantic_content_sha256: fcd9df4488662826b9599be2902b0cd9a79e6da0d6f46213c1ccb86d3667c920
    blocking_reason: null
    lineage_parent_revision: S3-REVISION-016
    lineage_parent_path: Erdos448/stage3/revisions/S3_REVISION_016.md
    lineage_parent_sha256: 5b0c1ddeeb981f05a740eb8c781498c67ea24610b3dbc0d2bd3c5404c2635ef6
    current_container: Erdos448/stage3/canonical/CURRENT.md

### DP-MERTENS-017

    dependency_problem_id: DP-MERTENS-017
    semantic_key: mertens-prime-product-asymptotic
    target_statement: EXT-002 exactly; DP-MERTENS FT-MERTENS plus parent-facing P-MERT-08
    binders: [EXT-002.b.x, EXT-002.b.A, EXT-002.b.B]
    hypotheses: []
    required_closure: KERNEL_CLOSED
    closure_role: REQUIRED
    parent_problem_id: ERDOS-448
    parent_obligation: EXT-002
    consumer_nodes: [P-007]
    continuation:
      action: resume ERDOS-448 S4 provider resolution and all semantic descendants
      entry_stage: S0_INCREMENTAL
      current_stage: S3_AUDIT_PASSED
    source_authority_status:
      status: AVAILABLE_CERTIFIED
      proof_context_available: true
      note: Villarino 2005 supplies the reconstructed proof; Lagarias 2013 independently confirms the theorem and constant
    provider_status: unresolved; S4 not entered
    authority_paths: [Erdos448/dependencies/DP-MERTENS, Erdos448/dependencies/DP-MERTENS/stage3/audits/S3_AUDIT_A2_ACCEPT_2026-09-13.md]
    child_dependency_problems: [DP-MERTENS-SUM-CONSTANT]
    status: MATH_CLOSED
    last_semantic_commit: UNAVAILABLE_NO_GIT_REPOSITORY
    last_semantic_content_sha256: c4856b6ffaaa560302f3c172acc92bf181f25ef305cb7809d35747a66107685f
    blocking_reason: null
    lineage_parent_revision: S3-REVISION-016
    lineage_parent_path: Erdos448/stage3/revisions/S3_REVISION_016.md
    lineage_parent_sha256: 5b0c1ddeeb981f05a740eb8c781498c67ea24610b3dbc0d2bd3c5404c2635ef6
    current_container: Erdos448/stage3/canonical/CURRENT.md

These frames are parent abstraction boundaries, not construction tasks.

## 4. Shifted-mean and Euler-product contracts

### Sections 4-5 typed support definitions

These parameterized definitions name the exact analytic subjects and domain predicates used by the existing Sections 4-5 contracts. Their mathematical bodies are authored in the records; they do not create proof premises.

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S45-NONNEG-MULT","kind":"DEFINITION","binders":[{"key":"f","type":{"fn":{"args":["Nat"],"return":"Real"}}}],"uses_definitions":[],"source_anchors":[],"result_type":"Prop","body":"f is a nonnegative multiplicative function on the positive integers."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S45-LAMBDA-SEQUENCE","kind":"DEFINITION","binders":[{"key":"lambda_seq","type":{"fn":{"args":["Nat"],"return":"Real"}}}],"uses_definitions":[],"source_anchors":[],"result_type":"Prop","body":"For every i in Nat, lambda_seq(i) is nonnegative."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S45-SHIFT-MAJORANT","kind":"DEFINITION","binders":[{"key":"lambda_seq","type":{"fn":{"args":["Nat"],"return":"Real"}}},{"key":"lambda","type":"Real"},{"key":"u","type":{"fn":{"args":["Nat"],"return":"Real"}}},{"key":"v","type":{"fn":{"args":["Nat"],"return":"Real"}}}],"uses_definitions":[],"source_anchors":[],"result_type":"Prop","body":"For every prime p and i,j in Nat, 0 <= u(p^(i+j))v(p^j) <= lambda_seq(i) lambda^j."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S45-REAL-RATIO","kind":"DEFINITION","binders":[{"key":"x","type":"Real"},{"key":"d","type":"Nat"}],"uses_definitions":[],"source_anchors":[],"result_type":"Real","body":"The exact real quotient x/d, using the positive-integer-to-real embedding."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S45-BFIRST-G","kind":"DEFINITION","binders":[{"key":"u","type":{"fn":{"args":["Nat"],"return":"Real"}}},{"key":"v","type":{"fn":{"args":["Nat"],"return":"Real"}}},{"key":"K_sh","type":"Nat"}],"uses_definitions":[],"source_anchors":[],"result_type":{"fn":{"args":["Nat"],"return":"Real"}},"body":"m maps to u(m)v(m) times the coprimality indicator 1_(gcd(m,K_sh)=1)."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S45-RECIP-G","kind":"DEFINITION","binders":[{"key":"K_sh","type":"Nat"}],"uses_definitions":["D-001"],"source_anchors":[],"result_type":{"fn":{"args":["Nat"],"return":"Real"}},"body":"m maps to 1/tau(m K_sh)."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S45-ELL-G","kind":"DEFINITION","binders":[],"uses_definitions":["D-006"],"source_anchors":[],"result_type":{"fn":{"args":["Nat"],"return":"Real"}},"body":"m maps to ell(m)^(-1/2)."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S45-P007-ERROR-FAMILY","kind":"DEFINITION","binders":[{"key":"c","type":"Real"},{"key":"C_err","type":"Real"},{"key":"L","type":{"fn":{"args":["Nat"],"return":"Real"}}}],"uses_definitions":[],"source_anchors":[],"result_type":{"fn":{"args":["Nat"],"return":"Real"}},"body":"p maps to L(p)(1-1/p)^c-1, the exact P-007 error factor family."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S45-P007-CFAC","kind":"DEFINITION","binders":[{"key":"c","type":"Real"},{"key":"C_err","type":"Real"}],"uses_definitions":[],"source_anchors":[],"result_type":"Real","body":"1 + 2^|c| C_err + (1/2)|c(c-1)|2^(|c|+2)(1+|c|/2) + c^2."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S45-MIN-ETA-ONE","kind":"DEFINITION","binders":[{"key":"eta","type":"Real"}],"uses_definitions":[],"source_anchors":[],"result_type":"Real","body":"min(eta,1)."}
```

```mathminer-s3-legacy
{"schema":"mathminer.s3/1","id":"D-S45-P008-Q","kind":"DEFINITION","binders":[{"key":"Y","type":{"set":"Real"}}],"uses_definitions":[],"source_anchors":[],"result_type":"Type","body":"The nonempty family index type {(q,S,U): q in Y and 2 <= S < U}."}
```

```mathminer-s3-legacy
{"schema":"mathminer.s3/1","id":"D-S45-P008-C","kind":"DEFINITION","binders":[{"key":"Y","type":{"set":"Real"}}],"uses_definitions":["D-S45-P008-Q"],"source_anchors":[],"result_type":{"fn":{"args":[{"named":{"id":"D-S45-P008-Q","args":[{"var":"Y"}]}}],"return":"Real"}},"body":"The coefficient map (q,S,U) maps to (q-1)/2."}
```

```mathminer-s3-legacy
{"schema":"mathminer.s3/1","id":"D-S45-P008-L","kind":"DEFINITION","binders":[{"key":"Y","type":{"set":"Real"}}],"uses_definitions":["D-008","D-S45-P008-Q"],"source_anchors":[],"result_type":{"fn":{"args":[{"named":{"id":"D-S45-P008-Q","args":[{"var":"Y"}]}},"Nat"],"return":"Real"}},"body":"The exact-model moment local factor family from MAP-P011-P008-MOM."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S45-P011-YPLUS","kind":"DEFINITION","binders":[{"key":"y","type":"Real"}],"uses_definitions":[],"source_anchors":[],"result_type":{"set":"Real"},"body":"The closed interval [(1+y)/2,(2+y)/2]."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S45-P011-YMINUS","kind":"DEFINITION","binders":[{"key":"y","type":"Real"}],"uses_definitions":[],"source_anchors":[],"result_type":{"set":"Real"},"body":"The closed interval [y/2,(1+y)/2]."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S45-P011-AMB-L","kind":"DEFINITION","binders":[],"uses_definitions":[],"source_anchors":[],"result_type":{"fn":{"args":["Nat"],"return":"Real"}},"body":"For each prime p, (1-1/p)^(-1); arbitrary positive extension off primes."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S45-P011-ROUGH-L","kind":"DEFINITION","binders":[],"uses_definitions":[],"source_anchors":[],"result_type":{"fn":{"args":["Nat"],"return":"Real"}},"body":"For each prime p, 1-1/p; arbitrary positive extension off primes."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S45-P011-MOM-L","kind":"DEFINITION","binders":[{"key":"Y","type":{"set":"Real"}}],"uses_definitions":["D-008"],"source_anchors":[],"result_type":{"fn":{"args":["Nat"],"return":"Real"}},"body":"The exact-model moment factor at a current member of the Y-family, with model extension outside [sigma,u)."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S45-MOMENT-FN","kind":"DEFINITION","binders":[{"key":"y","type":"Real"},{"key":"sigma","type":"Real"},{"key":"theta","type":"Real"},{"key":"u","type":"Real"}],"uses_definitions":["D-008"],"source_anchors":[],"result_type":{"fn":{"args":["Nat"],"return":"Real"}},"body":"n maps to the exact D-008 moment F_(y,u)(n)."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S45-P011-LAMBDA","kind":"DEFINITION","binders":[{"key":"Y","type":{"set":"Real"}}],"uses_definitions":[],"source_anchors":[],"result_type":"Real","body":"max(1,sup Y)."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S45-P011-CLOC","kind":"DEFINITION","binders":[{"key":"Y","type":{"set":"Real"}}],"uses_definitions":["D-S45-P011-LAMBDA"],"source_anchors":[],"result_type":"Real","body":"4 + 2 Lambda_Y^2/(2-Lambda_Y)."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S45-P016-YPLUS","kind":"DEFINITION","binders":[{"key":"epsilon_int","type":"Real"}],"uses_definitions":[],"source_anchors":[],"result_type":"Real","body":"1 + 1.96 epsilon_int."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S45-P016-YMINUS","kind":"DEFINITION","binders":[{"key":"epsilon_int","type":"Real"}],"uses_definitions":[],"source_anchors":[],"result_type":"Real","body":"1 - 1.96 epsilon_int."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S45-EXT001-DOMAIN","kind":"DEFINITION","binders":[{"key":"h","type":{"fn":{"args":["Nat"],"return":"Real"}}},{"key":"lambda_1","type":"Real"},{"key":"lambda_2","type":"Real"},{"key":"X","type":"Real"}],"uses_definitions":[],"source_anchors":[],"result_type":"Prop","body":"h is nonnegative multiplicative; 0 <= h(p^j) <= lambda_1 lambda_2^j; lambda_1 >= 0; 0 <= lambda_2 < 2; X >= 2."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S45-EXT001-MEAN-BOUND","kind":"DEFINITION","binders":[{"key":"h","type":{"fn":{"args":["Nat"],"return":"Real"}}},{"key":"lambda_1","type":"Real"},{"key":"lambda_2","type":"Real"},{"key":"X","type":"Real"},{"key":"C_EXT","type":"Real"}],"uses_definitions":[],"source_anchors":[],"result_type":"Prop","body":"The exact DP-MEAN-T001 bound: sum_(n<X) h(n) <= C_EXT X/log(X) product_(p<X) sum_(j>=0) h(p^j)p^(-j)."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S45-EXT001-C","kind":"DEFINITION","binders":[{"key":"lambda_1","type":"Real"},{"key":"lambda_2","type":"Real"}],"uses_definitions":[],"source_anchors":[],"result_type":"Real","body":"The DP-MEAN-T001 uniform positive comparison constant."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S45-EXT002-X0","kind":"DEFINITION","binders":[],"uses_definitions":[],"source_anchors":[],"result_type":"Real","body":"A threshold X_M >= 2 from the strict-endpoint Mertens interval theorem."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S45-EXT002-CMINUS","kind":"DEFINITION","binders":[],"uses_definitions":[],"source_anchors":[],"result_type":"Real","body":"A positive lower comparison constant from EXT-002."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S45-EXT002-CPLUS","kind":"DEFINITION","binders":[],"uses_definitions":[],"source_anchors":[],"result_type":"Real","body":"A positive upper comparison constant from EXT-002."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S45-EXT002-ASYMPTOTIC","kind":"DEFINITION","binders":[],"uses_definitions":[],"source_anchors":[],"result_type":"Prop","body":"For x>=2, Q_<(x)=product_(p<x)(1-1/p) is asymptotic to exp(-gamma)/log x."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S45-EXT002-INTERVAL","kind":"DEFINITION","binders":[{"key":"X_0","type":"Real"},{"key":"c_minus","type":"Real"},{"key":"c_plus","type":"Real"}],"uses_definitions":[],"source_anchors":[],"result_type":"Prop","body":"X_0>=2 and c_minus,c_plus>0, and uniformly for B>A>=X_0 the exact strict interval product lies between c_minus log A/log B and c_plus log A/log B."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S45-P051F1-DOMINATION","kind":"DEFINITION","binders":[],"uses_definitions":["D-001","D-015"],"source_anchors":[],"result_type":"Prop","body":"For every positive K, w1(K) >= a0(K)=1/tau(K), with w1 the exact D-015 weight."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S45-P051F1-C","kind":"DEFINITION","binders":[],"uses_definitions":[],"source_anchors":[],"result_type":"Real","body":"The absolute positive type exponent witness from P-051F1."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S45-P051F1-CERR","kind":"DEFINITION","binders":[],"uses_definitions":[],"source_anchors":[],"result_type":"Real","body":"The absolute positive type error witness from P-051F1."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S45-P051F1-LAMBDA","kind":"DEFINITION","binders":[],"uses_definitions":[],"source_anchors":[],"result_type":"Real","body":"The absolute positive local bound witness from P-051F1."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S45-P001-DOMAIN","kind":"DEFINITION","binders":[{"key":"u","type":{"fn":{"args":["Nat"],"return":"Real"}}},{"key":"v","type":{"fn":{"args":["Nat"],"return":"Real"}}},{"key":"K_sh","type":"Nat"},{"key":"x","type":"Real"}],"uses_definitions":[],"source_anchors":[],"result_type":"Prop","body":"u and v are nonnegative multiplicative; K_sh>=1; x>=2; all displayed sums converge."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S45-P001-DECOMPOSITION","kind":"DEFINITION","binders":[{"key":"u","type":{"fn":{"args":["Nat"],"return":"Real"}}},{"key":"v","type":{"fn":{"args":["Nat"],"return":"Real"}}},{"key":"K_sh","type":"Nat"},{"key":"x","type":"Real"}],"uses_definitions":[],"source_anchors":[],"result_type":"Prop","body":"The exact common-prime decomposition of P-001, including both logarithmic components and d | K_sh^infinity."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S45-P001A-DOMAIN","kind":"DEFINITION","binders":[{"key":"g","type":{"fn":{"args":["Nat"],"return":"Real"}}},{"key":"X","type":"Real"}],"uses_definitions":[],"source_anchors":[],"result_type":"Prop","body":"X>0 and g is nonnegative on positive integers."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S45-P001A-EMPTY-CASE","kind":"DEFINITION","binders":[{"key":"g","type":{"fn":{"args":["Nat"],"return":"Real"}}},{"key":"X","type":"Real"}],"uses_definitions":[],"source_anchors":[],"result_type":"Prop","body":"If 0<X<=1 then IS(g;X)=0."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S45-P001A-SINGLETON-CASE","kind":"DEFINITION","binders":[{"key":"g","type":{"fn":{"args":["Nat"],"return":"Real"}}},{"key":"X","type":"Real"}],"uses_definitions":[],"source_anchors":[],"result_type":"Prop","body":"If 1<X<2 then IS(g;X)=g(1)."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S45-P001B-DOMAIN","kind":"DEFINITION","binders":[{"key":"u","type":{"fn":{"args":["Nat"],"return":"Real"}}},{"key":"v","type":{"fn":{"args":["Nat"],"return":"Real"}}},{"key":"K_sh","type":"Nat"},{"key":"d","type":"Nat"},{"key":"x","type":"Real"},{"key":"X","type":"Real"}],"uses_definitions":[],"source_anchors":[],"result_type":"Prop","body":"u,v are nonnegative multiplicative; K_sh,d>=1; x>=2; X=x/d and 0<X<2."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S45-P001B-BOUNDED-FIRST","kind":"DEFINITION","binders":[{"key":"u","type":{"fn":{"args":["Nat"],"return":"Real"}}},{"key":"v","type":{"fn":{"args":["Nat"],"return":"Real"}}},{"key":"K_sh","type":"Nat"},{"key":"d","type":"Nat"},{"key":"x","type":"Real"},{"key":"X","type":"Real"}],"uses_definitions":[],"source_anchors":[],"result_type":"Prop","body":"AD-BFIRST exactly, with the literal coprime first logarithmic component and Euler product through p<x."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S45-P001D-DOMAIN","kind":"DEFINITION","binders":[{"key":"u","type":{"fn":{"args":["Nat"],"return":"Real"}}},{"key":"v","type":{"fn":{"args":["Nat"],"return":"Real"}}},{"key":"K_sh","type":"Nat"},{"key":"X","type":"Real"},{"key":"x","type":"Real"}],"uses_definitions":[],"source_anchors":[],"result_type":"Prop","body":"u,v are nonnegative multiplicative; K_sh>=1; 2<=X<=x; every local Euler factor L_p(u,v)>=1."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S45-P001D-ENLARGEMENT","kind":"DEFINITION","binders":[{"key":"u","type":{"fn":{"args":["Nat"],"return":"Real"}}},{"key":"v","type":{"fn":{"args":["Nat"],"return":"Real"}}},{"key":"K_sh","type":"Nat"},{"key":"X","type":"Real"},{"key":"x","type":"Real"}],"uses_definitions":[],"source_anchors":[],"result_type":"Prop","body":"AD-EULER-ENLARGE exactly, from SUB-P002-EULER-X to SUB-P002-EULER-x."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S45-SHIFT-FAMILY-DOMAIN","kind":"DEFINITION","binders":[{"key":"lambda_seq","type":{"fn":{"args":["Nat"],"return":"Real"}}},{"key":"lambda","type":"Real"},{"key":"u","type":{"fn":{"args":["Nat"],"return":"Real"}}},{"key":"v","type":{"fn":{"args":["Nat"],"return":"Real"}}},{"key":"K_sh","type":"Nat"},{"key":"X","type":"Real"}],"uses_definitions":[],"source_anchors":[],"result_type":"Prop","body":"lambda_seq is nonnegative; 0<=lambda<2; u,v are nonnegative multiplicative and satisfy the full prime-power majorant; K_sh>=1; X>=2."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S45-P005A-DOMAIN","kind":"DEFINITION","binders":[{"key":"lambda_seq","type":{"fn":{"args":["Nat"],"return":"Real"}}},{"key":"lambda","type":"Real"},{"key":"u","type":{"fn":{"args":["Nat"],"return":"Real"}}},{"key":"v","type":{"fn":{"args":["Nat"],"return":"Real"}}},{"key":"K_sh","type":"Nat"},{"key":"X","type":"Real"}],"uses_definitions":["D-014"],"source_anchors":[],"result_type":"Prop","body":"The exact shared shifted-mean domain D-S45-SHIFT-FAMILY-DOMAIN holds."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S45-P005A-SUMMABILITY","kind":"DEFINITION","binders":[{"key":"lambda_seq","type":{"fn":{"args":["Nat"],"return":"Real"}}},{"key":"lambda","type":"Real"},{"key":"u","type":{"fn":{"args":["Nat"],"return":"Real"}}},{"key":"v","type":{"fn":{"args":["Nat"],"return":"Real"}}},{"key":"K_sh","type":"Nat"},{"key":"X","type":"Real"}],"uses_definitions":["D-014"],"source_anchors":[],"result_type":"Prop","body":"Both exact local series converge; the P-001 outer family has finite support; the nonnegative d-majorant is summable and equals its finite shifted-local product."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S45-P001C-DOMAIN","kind":"DEFINITION","binders":[{"key":"K_sh","type":"Nat"},{"key":"z","type":"Real"}],"uses_definitions":["D-001","D-006","D-015"],"source_anchors":[],"result_type":"Prop","body":"K_sh>=1 and 0<z<2."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S45-P001C-SMOOTHING","kind":"DEFINITION","binders":[{"key":"K_sh","type":"Nat"},{"key":"z","type":"Real"}],"uses_definitions":["D-001","D-006","D-015"],"source_anchors":[],"result_type":"Prop","body":"sum_(m<z) 1/tau(m K_sh) <= w1(K_sh) sum_(m<z) ell(m)^(-1/2), exactly."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S45-EXT001-EXISTS","kind":"DEFINITION","binders":[{"key":"h","type":{"fn":{"args":["Nat"],"return":"Real"}}},{"key":"lambda_1","type":"Real"},{"key":"lambda_2","type":"Real"},{"key":"X","type":"Real"}],"uses_definitions":[],"source_anchors":[],"result_type":"Prop","body":"There exists a positive constant depending only on lambda_1,lambda_2 for the exact EXT-001 mean bound."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S45-P002-DOMAIN","kind":"DEFINITION","binders":[{"key":"lambda_seq","type":{"fn":{"args":["Nat"],"return":"Real"}}},{"key":"lambda","type":"Real"},{"key":"u","type":{"fn":{"args":["Nat"],"return":"Real"}}},{"key":"v","type":{"fn":{"args":["Nat"],"return":"Real"}}},{"key":"K_sh","type":"Nat"},{"key":"x","type":"Real"}],"uses_definitions":[],"source_anchors":[],"result_type":"Prop","body":"The exact shifted-family domain holds with x in place of X."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S45-P002-FIRST-LOG-FAMILY","kind":"DEFINITION","binders":[{"key":"lambda_seq","type":{"fn":{"args":["Nat"],"return":"Real"}}},{"key":"lambda","type":"Real"},{"key":"u","type":{"fn":{"args":["Nat"],"return":"Real"}}},{"key":"v","type":{"fn":{"args":["Nat"],"return":"Real"}}},{"key":"K_sh","type":"Nat"},{"key":"x","type":"Real"},{"key":"C_2","type":"Real"}],"uses_definitions":[],"source_anchors":[],"result_type":"Prop","body":"There is one C_2(lambda_seq,lambda)>0 such that for every d | K_sh^infinity the exact P-002 first logarithmic component is bounded by C_2 (x/d) times the Euler product through p<x, including both x/d>=2 and 0<x/d<2 branches."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S45-P002-C","kind":"DEFINITION","binders":[{"key":"lambda_seq","type":{"fn":{"args":["Nat"],"return":"Real"}}},{"key":"lambda","type":"Real"}],"uses_definitions":[],"source_anchors":[],"result_type":"Real","body":"The uniform P-002 comparison constant obtained from DP-MEAN-T001 and the bounded branch."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S45-P003-DOMAIN","kind":"DEFINITION","binders":[{"key":"u","type":{"fn":{"args":["Nat"],"return":"Real"}}},{"key":"v","type":{"fn":{"args":["Nat"],"return":"Real"}}},{"key":"K_sh","type":"Nat"},{"key":"x","type":"Real"}],"uses_definitions":[],"source_anchors":[],"result_type":"Prop","body":"u,v nonnegative multiplicative; K_sh>=1; x>=2; local Euler series converge."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S45-P003-SECOND-LOG-FAMILY","kind":"DEFINITION","binders":[{"key":"u","type":{"fn":{"args":["Nat"],"return":"Real"}}},{"key":"v","type":{"fn":{"args":["Nat"],"return":"Real"}}},{"key":"K_sh","type":"Nat"},{"key":"x","type":"Real"}],"uses_definitions":[],"source_anchors":[],"result_type":"Prop","body":"For every d | K_sh^infinity, the exact second logarithmic component is at most (x/d) log d times the Euler product through p<x."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S45-P004-DOMAIN","kind":"DEFINITION","binders":[],"uses_definitions":[],"source_anchors":[],"result_type":"Prop","body":"The positive-integer factorization domain."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S45-P004-FACTORIZATION","kind":"DEFINITION","binders":[],"uses_definitions":[],"source_anchors":[],"result_type":"Prop","body":"For every positive d, 1+log d <= product_(p^j || d)(1+j log p)."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S45-P005-DOMAIN","kind":"DEFINITION","binders":[{"key":"lambda_seq","type":{"fn":{"args":["Nat"],"return":"Real"}}},{"key":"lambda","type":"Real"},{"key":"u","type":{"fn":{"args":["Nat"],"return":"Real"}}},{"key":"v","type":{"fn":{"args":["Nat"],"return":"Real"}}},{"key":"K_sh","type":"Nat"},{"key":"X","type":"Real"}],"uses_definitions":["D-014"],"source_anchors":[],"result_type":"Prop","body":"The exact shared shifted-family domain holds."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S45-P005-SHIFTED-MEAN","kind":"DEFINITION","binders":[{"key":"lambda_seq","type":{"fn":{"args":["Nat"],"return":"Real"}}},{"key":"lambda","type":"Real"},{"key":"u","type":{"fn":{"args":["Nat"],"return":"Real"}}},{"key":"v","type":{"fn":{"args":["Nat"],"return":"Real"}}},{"key":"K_sh","type":"Nat"},{"key":"X","type":"Real"},{"key":"C_5","type":"Real"}],"uses_definitions":["D-014"],"source_anchors":[],"result_type":"Prop","body":"The exact P-005 shifted mean bound with local shift quotients S[u,v](p^i), one C_5 depending only on (lambda_0,lambda), and uniform u,v,K_sh,X."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S45-P005-C","kind":"DEFINITION","binders":[{"key":"lambda_seq","type":{"fn":{"args":["Nat"],"return":"Real"}}},{"key":"lambda","type":"Real"}],"uses_definitions":[],"source_anchors":[],"result_type":"Real","body":"The P-005 positive uniform comparison constant selected before u,v,K_sh,X."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S45-P006-DOMAIN","kind":"DEFINITION","binders":[{"key":"C_err","type":"Real"},{"key":"eta","type":"Real"},{"key":"r","type":{"fn":{"args":["Nat"],"return":"Real"}}}],"uses_definitions":[],"source_anchors":[],"result_type":"Prop","body":"C_err,eta>0; for every prime p, |r(p)|<=C_err p^(-1-eta) and 1+r(p)>0."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S45-P006-PRODUCT-BOUNDS","kind":"DEFINITION","binders":[{"key":"C_err","type":"Real"},{"key":"eta","type":"Real"},{"key":"r","type":{"fn":{"args":["Nat"],"return":"Real"}}},{"key":"P_0","type":"Real"},{"key":"C_minus","type":"Real"},{"key":"C_plus","type":"Real"}],"uses_definitions":[],"source_anchors":[],"result_type":"Prop","body":"P_0>=2 and C_minus,C_plus>0 uniformly bound every product_(P_0<=p<B)(1+r(p)) for B>P_0."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S45-P006-P0","kind":"DEFINITION","binders":[{"key":"C_err","type":"Real"},{"key":"eta","type":"Real"},{"key":"r","type":{"fn":{"args":["Nat"],"return":"Real"}}}],"uses_definitions":[],"source_anchors":[],"result_type":"Real","body":"The P0 witness selected in P-006 from absolute convergence."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S45-P006-CMINUS","kind":"DEFINITION","binders":[{"key":"C_err","type":"Real"},{"key":"eta","type":"Real"},{"key":"r","type":{"fn":{"args":["Nat"],"return":"Real"}}}],"uses_definitions":[],"source_anchors":[],"result_type":"Real","body":"The CMINUS witness selected in P-006 from absolute convergence."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S45-P006-CPLUS","kind":"DEFINITION","binders":[{"key":"C_err","type":"Real"},{"key":"eta","type":"Real"},{"key":"r","type":{"fn":{"args":["Nat"],"return":"Real"}}}],"uses_definitions":[],"source_anchors":[],"result_type":"Real","body":"The CPLUS witness selected in P-006 from absolute convergence."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S45-P006-EXISTS","kind":"DEFINITION","binders":[{"key":"C_err","type":"Real"},{"key":"eta","type":"Real"},{"key":"r","type":{"fn":{"args":["Nat"],"return":"Real"}}}],"uses_definitions":[],"source_anchors":[],"result_type":"Prop","body":"The exact P-006 threshold and two positive uniform product bounds exist."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S45-P006A-DOMAIN","kind":"DEFINITION","binders":[{"key":"c","type":"Real"},{"key":"P_0","type":"Real"},{"key":"L","type":{"fn":{"args":["Nat"],"return":"Real"}}}],"uses_definitions":[],"source_anchors":[],"result_type":"Prop","body":"P_0>=2 and L(p)>0 for primes p."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S45-P006A-INDEX-ADAPTERS","kind":"DEFINITION","binders":[{"key":"c","type":"Real"},{"key":"P_0","type":"Real"},{"key":"L","type":{"fn":{"args":["Nat"],"return":"Real"}}}],"uses_definitions":[],"source_anchors":[],"result_type":"Prop","body":"AD-PRIME-INDEX and AD-FINITE-PREFIX exactly for all A,B,t>=2, including every empty interval product."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S45-P007-DOMAIN","kind":"DEFINITION","binders":[{"key":"c","type":"Real"},{"key":"eta","type":"Real"},{"key":"C_err","type":"Real"},{"key":"L","type":{"fn":{"args":["Nat"],"return":"Real"}}}],"uses_definitions":[],"source_anchors":[],"result_type":"Prop","body":"eta,C_err>0; L(p)>0 and |L(p)-(1+c/p)|<=C_err p^(-1-eta) for every prime p>=2."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S45-P007-PRODUCT-COMPARISON","kind":"DEFINITION","binders":[{"key":"c","type":"Real"},{"key":"eta","type":"Real"},{"key":"C_err","type":"Real"},{"key":"L","type":{"fn":{"args":["Nat"],"return":"Real"}}},{"key":"P_err","type":"Real"},{"key":"C_minus","type":"Real"},{"key":"C_plus","type":"Real"}],"uses_definitions":[],"source_anchors":[],"result_type":"Prop","body":"P_err>=2 and C_minus,C_plus>0, depending only on fixed data, give the exact two-sided logarithmic quotient comparison for every A,B>=2, with the B<=A empty-product branch."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S45-P007-PERR","kind":"DEFINITION","binders":[{"key":"c","type":"Real"},{"key":"eta","type":"Real"},{"key":"C_err","type":"Real"},{"key":"L","type":{"fn":{"args":["Nat"],"return":"Real"}}}],"uses_definitions":[],"source_anchors":[],"result_type":"Real","body":"The PERR witness from the exact P-007 proof, including EXT-002 and the finite prefix."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S45-P007-CMINUS","kind":"DEFINITION","binders":[{"key":"c","type":"Real"},{"key":"eta","type":"Real"},{"key":"C_err","type":"Real"},{"key":"L","type":{"fn":{"args":["Nat"],"return":"Real"}}}],"uses_definitions":[],"source_anchors":[],"result_type":"Real","body":"The CMINUS witness from the exact P-007 proof, including EXT-002 and the finite prefix."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S45-P007-CPLUS","kind":"DEFINITION","binders":[{"key":"c","type":"Real"},{"key":"eta","type":"Real"},{"key":"C_err","type":"Real"},{"key":"L","type":{"fn":{"args":["Nat"],"return":"Real"}}}],"uses_definitions":[],"source_anchors":[],"result_type":"Real","body":"The CPLUS witness from the exact P-007 proof, including EXT-002 and the finite prefix."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S45-P007-EXISTS","kind":"DEFINITION","binders":[{"key":"c","type":"Real"},{"key":"eta","type":"Real"},{"key":"C_err","type":"Real"},{"key":"L","type":{"fn":{"args":["Nat"],"return":"Real"}}}],"uses_definitions":[],"source_anchors":[],"result_type":"Prop","body":"The exact P-007 threshold and two positive comparison constants exist for the full endpoint family."}
```

```mathminer-s3-legacy
{"schema":"mathminer.s3/1","id":"D-S45-P008-DOMAIN","kind":"DEFINITION","binders":[{"key":"Q","type":"Type"},{"key":"c_minus","type":"Real"},{"key":"c_plus","type":"Real"},{"key":"eta_star","type":"Real"},{"key":"C_err_star","type":"Real"},{"key":"P_0","type":"Real"},{"key":"m_fin","type":"Real"},{"key":"M_fin","type":"Real"},{"key":"coeff","type":{"fn":{"args":[{"var":"Q"}],"return":"Real"}}},{"key":"local_factor","type":{"fn":{"args":[{"var":"Q"},"Nat"],"return":"Real"}}}],"uses_definitions":[],"source_anchors":[],"result_type":"Prop","body":"Q is nonempty; c_minus<=c_plus; 1+c_minus/2>0; eta_star,C_err_star>0; P_0>=2; 0<m_fin<=M_fin; for every q in Q, c_minus<=coeff(q)<=c_plus and local_factor(q,p)>0 for every prime p>=2; |local_factor(q,p)-(1+coeff(q)/p)|<=C_err_star*p^(-1-eta_star) for every prime p with P_0<=p; and m_fin<=local_factor(q,p)<=M_fin for every prime p with 2<=p<=P_0. The tail and finite-prefix domains intentionally overlap at p=P_0."}
```

```mathminer-s3-legacy
{"schema":"mathminer.s3/1","id":"D-S45-P008-FAMILY-COMPARISON","kind":"DEFINITION","binders":[{"key":"Q","type":"Type"},{"key":"c_minus","type":"Real"},{"key":"c_plus","type":"Real"},{"key":"eta_star","type":"Real"},{"key":"C_err_star","type":"Real"},{"key":"P_0","type":"Real"},{"key":"m_fin","type":"Real"},{"key":"M_fin","type":"Real"},{"key":"coeff","type":{"fn":{"args":[{"var":"Q"}],"return":"Real"}}},{"key":"local_factor","type":{"fn":{"args":[{"var":"Q"},"Nat"],"return":"Real"}}},{"key":"C_family_minus","type":"Real"},{"key":"C_family_plus","type":"Real"}],"uses_definitions":[],"source_anchors":[],"result_type":"Prop","body":"There exist C_family_minus,C_family_plus>0 depending only on fixed data and preceding every q,A,B, giving P008-family for all q in Q and 2<=A<B, plus the exact empty-product branch."}
```

```mathminer-s3-legacy
{"schema":"mathminer.s3/1","id":"D-S45-P008-CMINUS","kind":"DEFINITION","binders":[{"key":"Q","type":"Type"},{"key":"c_minus","type":"Real"},{"key":"c_plus","type":"Real"},{"key":"eta_star","type":"Real"},{"key":"C_err_star","type":"Real"},{"key":"P_0","type":"Real"},{"key":"m_fin","type":"Real"},{"key":"M_fin","type":"Real"},{"key":"coeff","type":{"fn":{"args":[{"var":"Q"}],"return":"Real"}}},{"key":"local_factor","type":{"fn":{"args":[{"var":"Q"},"Nat"],"return":"Real"}}}],"uses_definitions":[],"source_anchors":[],"result_type":"Real","body":"The CMINUS compact-family comparison witness from the quantitative replay of P-007."}
```

```mathminer-s3-legacy
{"schema":"mathminer.s3/1","id":"D-S45-P008-CPLUS","kind":"DEFINITION","binders":[{"key":"Q","type":"Type"},{"key":"c_minus","type":"Real"},{"key":"c_plus","type":"Real"},{"key":"eta_star","type":"Real"},{"key":"C_err_star","type":"Real"},{"key":"P_0","type":"Real"},{"key":"m_fin","type":"Real"},{"key":"M_fin","type":"Real"},{"key":"coeff","type":{"fn":{"args":[{"var":"Q"}],"return":"Real"}}},{"key":"local_factor","type":{"fn":{"args":[{"var":"Q"},"Nat"],"return":"Real"}}}],"uses_definitions":[],"source_anchors":[],"result_type":"Real","body":"The CPLUS compact-family comparison witness from the quantitative replay of P-007."}
```

```mathminer-s3-legacy
{"schema":"mathminer.s3/1","id":"D-S45-P008-EXISTS","kind":"DEFINITION","binders":[{"key":"Q","type":"Type"},{"key":"c_minus","type":"Real"},{"key":"c_plus","type":"Real"},{"key":"eta_star","type":"Real"},{"key":"C_err_star","type":"Real"},{"key":"P_0","type":"Real"},{"key":"m_fin","type":"Real"},{"key":"M_fin","type":"Real"},{"key":"coeff","type":{"fn":{"args":[{"var":"Q"}],"return":"Real"}}},{"key":"local_factor","type":{"fn":{"args":[{"var":"Q"},"Nat"],"return":"Real"}}}],"uses_definitions":[],"source_anchors":[],"result_type":"Prop","body":"The two exact family-uniform P-008 comparison constants exist before q,A,B."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S45-P010-DOMAIN","kind":"DEFINITION","binders":[{"key":"y","type":"Real"},{"key":"sigma","type":"Real"},{"key":"theta","type":"Real"},{"key":"u","type":"Real"}],"uses_definitions":["D-002","D-003","D-008"],"source_anchors":[],"result_type":"Prop","body":"0<y<2 and u>sigma>=theta>=2."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S45-P010-LOCAL-VALUES","kind":"DEFINITION","binders":[{"key":"y","type":"Real"},{"key":"sigma","type":"Real"},{"key":"theta","type":"Real"},{"key":"u","type":"Real"}],"uses_definitions":["D-002","D-003","D-008"],"source_anchors":[],"result_type":"Prop","body":"F_(y,u) is nonnegative multiplicative and has exactly the four displayed prime-power branches for every prime p and nu>=1."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S45-P011-DOMAIN","kind":"DEFINITION","binders":[{"key":"Y","type":{"set":"Real"}}],"uses_definitions":["D-006","D-008"],"source_anchors":[],"result_type":"Prop","body":"Y is a nonempty compact subset of (0,2)."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S45-P011-MOMENT-MEAN","kind":"DEFINITION","binders":[{"key":"Y","type":{"set":"Real"}},{"key":"C_Y","type":"Real"}],"uses_definitions":["D-006","D-008"],"source_anchors":[],"result_type":"Prop","body":"C_Y>0 and for every y in Y, sigma>=theta>=2, sigma<u<=x and x>=2, sum_(n<x) F_(y,u)(n) <= C_Y x rho_theta (log u/log sigma)^((y-1)/2), with no assertion outside the legal domain."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S45-P011-C","kind":"DEFINITION","binders":[{"key":"Y","type":{"set":"Real"}}],"uses_definitions":[],"source_anchors":[],"result_type":"Real","body":"The positive Y-uniform constant assembled from EXT-001, ambient, rough, and moment local products."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S45-P011-EXISTS","kind":"DEFINITION","binders":[{"key":"Y","type":{"set":"Real"}}],"uses_definitions":[],"source_anchors":[],"result_type":"Prop","body":"The exact positive compact-Y uniform P-011 constant exists."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S45-P012-DOMAIN","kind":"DEFINITION","binders":[{"key":"y","type":"Real"}],"uses_definitions":["D-002","D-003","D-006","D-008"],"source_anchors":[],"result_type":"Prop","body":"1<y<2."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S45-P012-POINTWISE","kind":"DEFINITION","binders":[{"key":"y","type":"Real"}],"uses_definitions":["D-002","D-003","D-006","D-008"],"source_anchors":[],"result_type":"Prop","body":"For every sigma>=theta>=2, sigma<u<=x and n>0, the exact upper-tail Omega(d,u)>(y/2)log R divisor count is bounded pointwise by F_(y,u)(n) R^(-(y/2)log y), R=log u/log sigma."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S45-P012-MEAN","kind":"DEFINITION","binders":[{"key":"y","type":"Real"},{"key":"C_y","type":"Real"}],"uses_definitions":["D-002","D-003","D-006","D-008"],"source_anchors":[],"result_type":"Prop","body":"There is C_y>0 depending only on y such that the sum of that exact pointwise subject over n<x is at most C_y x rho_theta R^((y-1-y log y)/2)."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S45-P012-C","kind":"DEFINITION","binders":[{"key":"y","type":"Real"}],"uses_definitions":[],"source_anchors":[],"result_type":"Real","body":"The positive P-012 tail constant specialized from P-011 at the exact compact interval."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S45-P012-EXISTS","kind":"DEFINITION","binders":[{"key":"y","type":"Real"}],"uses_definitions":[],"source_anchors":[],"result_type":"Prop","body":"The exact positive P-012 constant and both pointwise/mean tail conclusions exist."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S45-P013-DOMAIN","kind":"DEFINITION","binders":[{"key":"y","type":"Real"}],"uses_definitions":["D-002","D-003","D-006","D-008"],"source_anchors":[],"result_type":"Prop","body":"0<y<1."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S45-P013-POINTWISE","kind":"DEFINITION","binders":[{"key":"y","type":"Real"}],"uses_definitions":["D-002","D-003","D-006","D-008"],"source_anchors":[],"result_type":"Prop","body":"For every sigma>=theta>=2, sigma<u<=x and n>0, the exact lower-tail Omega(d,u)<(y/2)log R divisor count is bounded pointwise by F_(y,u)(n) R^(-(y/2)log y), R=log u/log sigma."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S45-P013-MEAN","kind":"DEFINITION","binders":[{"key":"y","type":"Real"},{"key":"C_y","type":"Real"}],"uses_definitions":["D-002","D-003","D-006","D-008"],"source_anchors":[],"result_type":"Prop","body":"There is C_y>0 depending only on y such that the sum of that exact pointwise subject over n<x is at most C_y x rho_theta R^((y-1-y log y)/2)."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S45-P013-C","kind":"DEFINITION","binders":[{"key":"y","type":"Real"}],"uses_definitions":[],"source_anchors":[],"result_type":"Real","body":"The positive P-013 tail constant specialized from P-011 at the exact compact interval."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S45-P013-EXISTS","kind":"DEFINITION","binders":[{"key":"y","type":"Real"}],"uses_definitions":[],"source_anchors":[],"result_type":"Prop","body":"The exact positive P-013 constant and both pointwise/mean tail conclusions exist."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S45-EPS-DOMAIN","kind":"DEFINITION","binders":[{"key":"epsilon_int","type":"Real"}],"uses_definitions":[],"source_anchors":[],"result_type":"Prop","body":"0 < epsilon_int <= 1/10."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S45-P014-NUMERICAL","kind":"DEFINITION","binders":[{"key":"epsilon_int","type":"Real"}],"uses_definitions":[],"source_anchors":[],"result_type":"Prop","body":"With t=1.96 epsilon_int, t-(1+t)log(1+t) <= -1.802 epsilon_int^2."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S45-P015-NUMERICAL","kind":"DEFINITION","binders":[{"key":"epsilon_int","type":"Real"}],"uses_definitions":[],"source_anchors":[],"result_type":"Prop","body":"With t=1.96 epsilon_int, -t-(1-t)log(1-t) <= -1.802 epsilon_int^2."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S45-P016-GRID-BOUND","kind":"DEFINITION","binders":[{"key":"epsilon_int","type":"Real"},{"key":"C_grid","type":"Real"}],"uses_definitions":["D-006","D-009"],"source_anchors":[],"result_type":"Prop","body":"C_grid>0 and GridBound(epsilon_int,C_grid) exactly as D-009: the union of upper grid, upper terminal, and lower grid events has the displayed 0.901 exponent bound, with no lower terminal sample."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S45-P016-C","kind":"DEFINITION","binders":[{"key":"epsilon_int","type":"Real"}],"uses_definitions":[],"source_anchors":[],"result_type":"Real","body":"The positive grid constant assembled from P-012, P-013, P-014, and P-015."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S45-P017-DOMAIN","kind":"DEFINITION","binders":[{"key":"epsilon_int","type":"Real"},{"key":"C_grid","type":"Real"}],"uses_definitions":[],"source_anchors":[],"result_type":"Prop","body":"0<epsilon_int<=1/10 and C_grid>0."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S45-P017-THRESHOLD","kind":"DEFINITION","binders":[{"key":"epsilon_int","type":"Real"},{"key":"C_grid","type":"Real"},{"key":"Xi_0","type":"Real"}],"uses_definitions":["D-009"],"source_anchors":[],"result_type":"Prop","body":"Xi_0>1 and ThresholdSpec(epsilon_int,C_grid,Xi_0) exactly as D-009, uniformly for xi>=Xi_0."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S45-P017-XI0","kind":"DEFINITION","binders":[{"key":"epsilon_int","type":"Real"},{"key":"C_grid","type":"Real"}],"uses_definitions":[],"source_anchors":[],"result_type":"Real","body":"The threshold enlarged so xi>e and both D-009 scalar smallness requirements hold."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S45-P018-BAD-MEAN","kind":"DEFINITION","binders":[{"key":"epsilon_int","type":"Real"},{"key":"C_grid","type":"Real"},{"key":"Xi_0","type":"Real"}],"uses_definitions":["D-003","D-006","D-007","D-009"],"source_anchors":[],"result_type":"Prop","body":"For every xi>=Xi_0, sigma>=theta>=2 and x>U0, the exact mean of rough divisors failing Good is at most (1/10)x rho_theta (log xi)^(-0.9 epsilon_int^2)."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S45-P019-DOMAIN","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"}],"uses_definitions":["D-002","D-006"],"source_anchors":[],"result_type":"Prop","body":"theta>=2."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S45-P019-ROUGH-DENSITY","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"}],"uses_definitions":["D-002","D-006"],"source_anchors":[],"result_type":"Prop","body":"The set R_theta={n>0: chi(n,theta)=1} has exact natural density rho_theta."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S45-P020-DOMAIN","kind":"DEFINITION","binders":[{"key":"epsilon_int","type":"Real"},{"key":"xi","type":"Real"},{"key":"sigma","type":"Real"},{"key":"theta","type":"Real"}],"uses_definitions":[],"source_anchors":[],"result_type":"Prop","body":"0<epsilon_int<=1/10; xi is at least the selected Xi_0; sigma>=theta>=2."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S45-P020-A","kind":"DEFINITION","binders":[{"key":"epsilon_int","type":"Real"},{"key":"xi","type":"Real"},{"key":"sigma","type":"Real"},{"key":"theta","type":"Real"},{"key":"C_grid","type":"Real"},{"key":"Xi_0","type":"Real"}],"uses_definitions":["D-002","D-007"],"source_anchors":[],"result_type":{"set":"Nat"},"body":"The exact set of remaining rough integers after removing the finite n<=U0 range and the Markov-bad set, as specified in the P-020 derivation."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S45-P020-L4SPEC","kind":"DEFINITION","binders":[{"key":"epsilon_int","type":"Real"},{"key":"xi","type":"Real"},{"key":"sigma","type":"Real"},{"key":"theta","type":"Real"},{"key":"C_grid","type":"Real"},{"key":"Xi_0","type":"Real"},{"key":"A","type":{"set":"Nat"}}],"uses_definitions":["D-010"],"source_anchors":[],"result_type":"Prop","body":"C_grid>0, Xi_0>1, xi>=Xi_0, and A satisfies L4Spec(epsilon_int,xi,sigma,theta,A) exactly, with rough support, the lower-density bound, and nine-tenths good-divisor mass."}
```

### Existential adapter A-S45-EXT001-EXISTS

```mathminer-s3
{"schema":"mathminer.s3/1","id":"A-S45-EXT001-EXISTS","kind":"DERIVATION","binders":[{"key":"h","type":{"fn":{"args":["Nat"],"return":"Real"}}},{"key":"lambda_1","type":"Real"},{"key":"lambda_2","type":"Real"},{"key":"X","type":"Real"}],"uses_definitions":["D-S45-EXT001-DOMAIN","D-S45-EXT001-EXISTS","DP-MEAN::DP-MEAN-DEF-006","DP-MEAN::DP-MEAN-DEF-007","DP-MEAN::DP-MEAN-DEF-008"],"source_anchors":[],"hypotheses":[{"key":"h_nonnegative_multiplicative","proposition":{"op":{"name":"and","args":[{"def":{"id":"DP-MEAN::DP-MEAN-DEF-006","args":[{"var":"h"}]}},{"def":{"id":"DP-MEAN::DP-MEAN-DEF-007","args":[{"var":"h"}]}}]}}},{"key":"prime_power_geometric_bound","proposition":{"def":{"id":"DP-MEAN::DP-MEAN-DEF-008","args":[{"var":"h"},{"var":"lambda_1"},{"var":"lambda_2"}]}}},{"key":"lambda_1_nonnegative","proposition":{"op":{"name":"ge","args":[{"var":"lambda_1"},{"lit":{"type":"Real","value":"0"}}]}}},{"key":"lambda_2_range","proposition":{"op":{"name":"and","args":[{"op":{"name":"ge","args":[{"var":"lambda_2"},{"lit":{"type":"Real","value":"0"}}]}},{"op":{"name":"lt","args":[{"var":"lambda_2"},{"lit":{"type":"Real","value":"2"}}]}}]}}},{"key":"X_at_least_2","proposition":{"op":{"name":"ge","args":[{"var":"X"},{"lit":{"type":"Real","value":"2"}}]}}}],"witnesses":[],"conclusions":[{"key":"mean_bound_exists","proposition":{"def":{"id":"D-S45-EXT001-EXISTS","args":[{"var":"h"},{"var":"lambda_1"},{"var":"lambda_2"},{"var":"X"}]}}}],"premises":[{"id":"use-ext001","producer":"EXT-001","closure_role":"REQUIRED","binder_map":{"h":{"var":"h"},"lambda_1":{"var":"lambda_1"},"lambda_2":{"var":"lambda_2"},"X":{"var":"X"}},"hypothesis_map":{"h_nonnegative_multiplicative":{"hypothesis":"h_nonnegative_multiplicative"},"prime_power_geometric_bound":{"hypothesis":"prime_power_geometric_bound"},"lambda_1_nonnegative":{"hypothesis":"lambda_1_nonnegative"},"lambda_2_range":{"hypothesis":"lambda_2_range"},"X_at_least_2":{"hypothesis":"X_at_least_2"}},"witness_map":{"C_EXT":"adapter_C_EXT"},"consume":["mean_bound"]}],"witness_realizations":{},"proof_ref":"### Existential adapter A-S45-EXT001-EXISTS"}
```

This adapter exposes the exact witness specialization used by the adjacent Section 4-5 proof; it introduces no additional mathematical assumption.

### Existential adapter A-S45-P006-EXISTS

```mathminer-s3
{"schema":"mathminer.s3/1","id":"A-S45-P006-EXISTS","kind":"DERIVATION","binders":[{"key":"C_err","type":"Real"},{"key":"eta","type":"Real"},{"key":"r","type":{"fn":{"args":["Nat"],"return":"Real"}}}],"uses_definitions":["D-S45-P006-DOMAIN","D-S45-P006-EXISTS"],"source_anchors":[],"hypotheses":[{"key":"domain","proposition":{"def":{"id":"D-S45-P006-DOMAIN","args":[{"var":"C_err"},{"var":"eta"},{"var":"r"}]}}}],"witnesses":[],"conclusions":[{"key":"existentialized","proposition":{"def":{"id":"D-S45-P006-EXISTS","args":[{"var":"C_err"},{"var":"eta"},{"var":"r"}]}}}],"premises":[{"id":"producer","producer":"P-006","closure_role":"REQUIRED","binder_map":{"C_err":{"var":"C_err"},"eta":{"var":"eta"},"r":{"var":"r"}},"hypothesis_map":{"domain":{"hypothesis":"domain"}},"witness_map":{"P_0":"received_P_0","C_minus":"received_C_minus","C_plus":"received_C_plus"},"consume":["uniform_error_product_bounds"]}],"witness_realizations":{},"proof_ref":"### Existential adapter A-S45-P006-EXISTS"}
```

This adapter exposes the exact witness specialization used by the adjacent Section 4-5 proof; it introduces no additional mathematical assumption.

### Existential adapter A-S45-P007-EXISTS

```mathminer-s3
{"schema":"mathminer.s3/1","id":"A-S45-P007-EXISTS","kind":"DERIVATION","binders":[{"key":"c","type":"Real"},{"key":"eta","type":"Real"},{"key":"C_err","type":"Real"},{"key":"L","type":{"fn":{"args":["Nat"],"return":"Real"}}}],"uses_definitions":["D-S45-P007-DOMAIN","D-S45-P007-EXISTS"],"source_anchors":[],"hypotheses":[{"key":"domain","proposition":{"def":{"id":"D-S45-P007-DOMAIN","args":[{"var":"c"},{"var":"eta"},{"var":"C_err"},{"var":"L"}]}}}],"witnesses":[],"conclusions":[{"key":"existentialized","proposition":{"def":{"id":"D-S45-P007-EXISTS","args":[{"var":"c"},{"var":"eta"},{"var":"C_err"},{"var":"L"}]}}}],"premises":[{"id":"producer","producer":"P-007","closure_role":"REQUIRED","binder_map":{"c":{"var":"c"},"eta":{"var":"eta"},"C_err":{"var":"C_err"},"L":{"var":"L"}},"hypothesis_map":{"domain":{"hypothesis":"domain"}},"witness_map":{"P_err":"received_P_err","C_minus":"received_C_minus","C_plus":"received_C_plus"},"consume":["local_product_comparison"]}],"witness_realizations":{},"proof_ref":"### Existential adapter A-S45-P007-EXISTS"}
```

This adapter exposes the exact witness specialization used by the adjacent Section 4-5 proof; it introduces no additional mathematical assumption.

### Existential adapter A-S45-P008-EXISTS

```mathminer-s3-legacy
{"schema":"mathminer.s3/1","id":"A-S45-P008-EXISTS","kind":"DERIVATION","binders":[{"key":"Q","type":"Type"},{"key":"c_minus","type":"Real"},{"key":"c_plus","type":"Real"},{"key":"eta_star","type":"Real"},{"key":"C_err_star","type":"Real"},{"key":"P_0","type":"Real"},{"key":"m_fin","type":"Real"},{"key":"M_fin","type":"Real"},{"key":"coeff","type":{"fn":{"args":[{"var":"Q"}],"return":"Real"}}},{"key":"local_factor","type":{"fn":{"args":[{"var":"Q"},"Nat"],"return":"Real"}}}],"uses_definitions":["D-S45-P008-DOMAIN","D-S45-P008-EXISTS"],"source_anchors":[],"hypotheses":[{"key":"domain","proposition":{"def":{"id":"D-S45-P008-DOMAIN","args":[{"var":"Q"},{"var":"c_minus"},{"var":"c_plus"},{"var":"eta_star"},{"var":"C_err_star"},{"var":"P_0"},{"var":"m_fin"},{"var":"M_fin"},{"var":"coeff"},{"var":"local_factor"}]}}}],"witnesses":[],"conclusions":[{"key":"existentialized","proposition":{"def":{"id":"D-S45-P008-EXISTS","args":[{"var":"Q"},{"var":"c_minus"},{"var":"c_plus"},{"var":"eta_star"},{"var":"C_err_star"},{"var":"P_0"},{"var":"m_fin"},{"var":"M_fin"},{"var":"coeff"},{"var":"local_factor"}]}}}],"premises":[{"id":"producer","producer":"P-008","closure_role":"REQUIRED","binder_map":{"Q":{"var":"Q"},"c_minus":{"var":"c_minus"},"c_plus":{"var":"c_plus"},"eta_star":{"var":"eta_star"},"C_err_star":{"var":"C_err_star"},"P_0":{"var":"P_0"},"m_fin":{"var":"m_fin"},"M_fin":{"var":"M_fin"},"coeff":{"var":"coeff"},"local_factor":{"var":"local_factor"}},"hypothesis_map":{"domain":{"hypothesis":"domain"}},"witness_map":{"C_family_minus":"received_C_family_minus","C_family_plus":"received_C_family_plus"},"consume":["family_product_comparison"]}],"witness_realizations":{},"proof_ref":"### Existential adapter A-S45-P008-EXISTS"}
```

This adapter exposes the exact witness specialization used by the adjacent Section 4-5 proof; it introduces no additional mathematical assumption.

### Existential adapter A-S45-P011-EXISTS

```mathminer-s3-legacy
{"schema":"mathminer.s3/1","id":"A-S45-P011-EXISTS","kind":"DERIVATION","binders":[{"key":"Y","type":{"set":"Real"}}],"uses_definitions":["D-S45-P011-DOMAIN","D-S45-P011-EXISTS"],"source_anchors":[],"hypotheses":[{"key":"domain","proposition":{"def":{"id":"D-S45-P011-DOMAIN","args":[{"var":"Y"}]}}}],"witnesses":[],"conclusions":[{"key":"existentialized","proposition":{"def":{"id":"D-S45-P011-EXISTS","args":[{"var":"Y"}]}}}],"premises":[{"id":"producer","producer":"P-011","closure_role":"REQUIRED","binder_map":{"Y":{"var":"Y"}},"hypothesis_map":{"domain":{"hypothesis":"domain"}},"witness_map":{"C_Y":"received_C_Y"},"consume":["legal_domain_moment_mean"]}],"witness_realizations":{},"proof_ref":"### Existential adapter A-S45-P011-EXISTS"}
```

This adapter exposes the exact witness specialization used by the adjacent Section 4-5 proof; it introduces no additional mathematical assumption.

### Existential adapter A-S45-P012-EXISTS

```mathminer-s3-legacy
{"schema":"mathminer.s3/1","id":"A-S45-P012-EXISTS","kind":"DERIVATION","binders":[{"key":"y","type":"Real"}],"uses_definitions":["D-S45-P012-DOMAIN","D-S45-P012-EXISTS"],"source_anchors":[],"hypotheses":[{"key":"domain","proposition":{"def":{"id":"D-S45-P012-DOMAIN","args":[{"var":"y"}]}}}],"witnesses":[],"conclusions":[{"key":"existentialized","proposition":{"def":{"id":"D-S45-P012-EXISTS","args":[{"var":"y"}]}}}],"premises":[{"id":"producer","producer":"P-012","closure_role":"REQUIRED","binder_map":{"y":{"var":"y"}},"hypothesis_map":{"domain":{"hypothesis":"domain"}},"witness_map":{"C_y":"received_C_y"},"consume":["mean_tail"]}],"witness_realizations":{},"proof_ref":"### Existential adapter A-S45-P012-EXISTS"}
```

This adapter exposes the exact witness specialization used by the adjacent Section 4-5 proof; it introduces no additional mathematical assumption.

### Existential adapter A-S45-P013-EXISTS

```mathminer-s3-legacy
{"schema":"mathminer.s3/1","id":"A-S45-P013-EXISTS","kind":"DERIVATION","binders":[{"key":"y","type":"Real"}],"uses_definitions":["D-S45-P013-DOMAIN","D-S45-P013-EXISTS"],"source_anchors":[],"hypotheses":[{"key":"domain","proposition":{"def":{"id":"D-S45-P013-DOMAIN","args":[{"var":"y"}]}}}],"witnesses":[],"conclusions":[{"key":"existentialized","proposition":{"def":{"id":"D-S45-P013-EXISTS","args":[{"var":"y"}]}}}],"premises":[{"id":"producer","producer":"P-013","closure_role":"REQUIRED","binder_map":{"y":{"var":"y"}},"hypothesis_map":{"domain":{"hypothesis":"domain"}},"witness_map":{"C_y":"received_C_y"},"consume":["mean_tail"]}],"witness_realizations":{},"proof_ref":"### Existential adapter A-S45-P013-EXISTS"}
```

This adapter exposes the exact witness specialization used by the adjacent Section 4-5 proof; it introduces no additional mathematical assumption.

### P-001 — common-prime decomposition

```mathminer-s3
{"schema":"mathminer.s3/1","id":"P-001","kind":"PROPOSITION","binders":[{"key":"u","type":{"fn":{"args":["Nat"],"return":"Real"}}},{"key":"v","type":{"fn":{"args":["Nat"],"return":"Real"}}},{"key":"K_sh","type":"Nat"},{"key":"x","type":"Real"}],"uses_definitions":["D-S45-P001-DECOMPOSITION","D-S45-P001-DOMAIN"],"source_anchors":[],"hypotheses":[{"key":"domain","proposition":{"def":{"id":"D-S45-P001-DOMAIN","args":[{"var":"u"},{"var":"v"},{"var":"K_sh"},{"var":"x"}]}}}],"witnesses":[],"conclusions":[{"key":"common_prime_decomposition","proposition":{"def":{"id":"D-S45-P001-DECOMPOSITION","args":[{"var":"u"},{"var":"v"},{"var":"K_sh"},{"var":"x"}]}}}],"premises":[],"witness_realizations":{},"proof_ref":"### P-001 — common-prime decomposition"}
```

- Prenex statement: for every nonnegative multiplicative \(u,v\), every
  integer \(K_{\rm sh}\ge1\), and every real \(x\ge2\), assuming all displayed
  sums converge,
  \[
  \sum_{n<x}u(K_{\rm sh}n)v(n)\log x
  =\sum_{d\mid K_{\rm sh}^{\infty}}u(K_{\rm sh}d)v(d)
  \sum_{\substack{m<x/d\\(m,K_{\rm sh})=1}}u(m)v(m)
  \{\log(x/d)+\log d\}.
  \]
- Local equalities: \(n=dm\), \(d\mid K_{\rm sh}^{\infty}\),
  \((m,K_{\rm sh})=1\).
- Domain/range: \(d,m,n,K_{\rm sh}\) positive integers.
- Input subject: the left shifted mean times \(\log x\).
  Output subject: exact two-logarithm decomposition.
- Premise maps: none (root).
- Derivation certificate: separate from \(n\) exactly the prime powers whose
  primes divide \(K_{\rm sh}\); use
  \(\log x=\log(x/d)+\log d\).
- Source/S2 anchor: ET pp. 23–24; S2 R1 E4 and R2.8(1).
- Definitions used: none.

### P-001A — bounded positive-integer initial segments

```mathminer-s3
{"schema":"mathminer.s3/1","id":"P-001A","kind":"PROPOSITION","binders":[{"key":"g","type":{"fn":{"args":["Nat"],"return":"Real"}}},{"key":"X","type":"Real"}],"uses_definitions":["D-S45-P001A-DOMAIN","D-S45-P001A-EMPTY-CASE","D-S45-P001A-SINGLETON-CASE"],"source_anchors":[],"hypotheses":[{"key":"domain","proposition":{"def":{"id":"D-S45-P001A-DOMAIN","args":[{"var":"g"},{"var":"X"}]}}}],"witnesses":[],"conclusions":[{"key":"empty_case","proposition":{"def":{"id":"D-S45-P001A-EMPTY-CASE","args":[{"var":"g"},{"var":"X"}]}}},{"key":"singleton_case","proposition":{"def":{"id":"D-S45-P001A-SINGLETON-CASE","args":[{"var":"g"},{"var":"X"}]}}}],"premises":[],"witness_realizations":{},"proof_ref":"### P-001A — bounded positive-integer initial segments"}
```

- Prenex statement: for every \(X\in\mathbb R_{>0}\) and every
  \(g:\mathbb N_{>0}\to\mathbb R_{\ge0}\), define
  \({\sf IS}(g;X)=\sum_{n<X}g(n)\). If \(0<X\le1\), then
  \({\sf IS}(g;X)=0\); if \(1<X<2\), then
  \({\sf IS}(g;X)=g(1)\).
- Dependency order: fixed \(g\) -> no witnesses -> uniform \(X\).
- Premise maps: none. Subject IDs: `SUB-IS`, `SUB-IS-EMPTY`,
  `SUB-IS-ONE`.
- Derivation certificate: there is no positive integer below \(X\le1\), and
  the only positive integer below \(1<X<2\) is \(1\).

### P-001B — bounded first-logarithmic component adapter

```mathminer-s3
{"schema":"mathminer.s3/1","id":"P-001B","kind":"PROPOSITION","binders":[{"key":"u","type":{"fn":{"args":["Nat"],"return":"Real"}}},{"key":"v","type":{"fn":{"args":["Nat"],"return":"Real"}}},{"key":"K_sh","type":"Nat"},{"key":"d","type":"Nat"},{"key":"x","type":"Real"},{"key":"X","type":"Real"}],"uses_definitions":["D-S45-BFIRST-G","D-S45-P001A-DOMAIN","D-S45-P001B-BOUNDED-FIRST","D-S45-P001B-DOMAIN"],"source_anchors":[],"hypotheses":[{"key":"domain","proposition":{"def":{"id":"D-S45-P001B-DOMAIN","args":[{"var":"u"},{"var":"v"},{"var":"K_sh"},{"var":"d"},{"var":"x"},{"var":"X"}]}}}],"witnesses":[],"conclusions":[{"key":"bounded_first_log","proposition":{"def":{"id":"D-S45-P001B-BOUNDED-FIRST","args":[{"var":"u"},{"var":"v"},{"var":"K_sh"},{"var":"d"},{"var":"x"},{"var":"X"}]}}}],"premises":[{"id":"initial-segment","producer":"P-001A","closure_role":"REQUIRED","guards":[{"key":"initial_segment_domain","proposition":{"def":{"id":"D-S45-P001A-DOMAIN","args":[{"def":{"id":"D-S45-BFIRST-G","args":[{"var":"u"},{"var":"v"},{"var":"K_sh"}]}},{"var":"X"}]}}}],"binder_map":{"g":{"def":{"id":"D-S45-BFIRST-G","args":[{"var":"u"},{"var":"v"},{"var":"K_sh"}]}},"X":{"var":"X"}},"hypothesis_map":{"domain":{"guard":"initial_segment_domain"}},"witness_map":{},"consume":["empty_case","singleton_case"]}],"witness_realizations":{},"proof_ref":"### P-001B — bounded first-logarithmic component adapter"}
```

- Prenex statement: for every nonnegative multiplicative \(u,v\),
  \(K_{\rm sh},d\in\mathbb N_{>0}\), \(x\in\mathbb R_{\ge2}\), and
  \(X:=x/d\in(0,2)\), put
  \(L_p(u,v):=\sum_{j\ge0}u(p^j)v(p^j)p^{-j}\). Then
  \[
  \sum_{\substack{m<X\\(m,K_{\rm sh})=1}}u(m)v(m)\log X
  \le X\prod_{\substack{p<x\\p\nmid K_{\rm sh}}}L_p(u,v).
  \tag{AD-BFIRST}
  \]
- Dependency order: fixed local majorants -> no new constant -> uniform
  \(K_{\rm sh},d,x,X\).
- Premise maps: the map to P-001A has producer slots
  \(X:=x/d\), \(g(m):=u(m)v(m)1_{(m,K_{\rm sh})=1}\);
  domain evidence is \(0<x/d<2\). For \(x/d\le1\) the subject is empty.
  For \(1<x/d<2\), multiply the singleton equality by the nonnegative scalar
  \(\log(x/d)\). The resulting subject equals the literal first P-001
  component. The right side is exactly the displayed majorant because each
  \(L_p(u,v)\ge1\) and \(\log X\le X\) on \(1<X<2\).

### P-001D — exact nonnegative Euler-product enlargement

```mathminer-s3
{"schema":"mathminer.s3/1","id":"P-001D","kind":"PROPOSITION","binders":[{"key":"u","type":{"fn":{"args":["Nat"],"return":"Real"}}},{"key":"v","type":{"fn":{"args":["Nat"],"return":"Real"}}},{"key":"K_sh","type":"Nat"},{"key":"X","type":"Real"},{"key":"x","type":"Real"}],"uses_definitions":["D-S45-P001D-DOMAIN","D-S45-P001D-ENLARGEMENT"],"source_anchors":[],"hypotheses":[{"key":"domain","proposition":{"def":{"id":"D-S45-P001D-DOMAIN","args":[{"var":"u"},{"var":"v"},{"var":"K_sh"},{"var":"X"},{"var":"x"}]}}}],"witnesses":[],"conclusions":[{"key":"euler_enlargement","proposition":{"def":{"id":"D-S45-P001D-ENLARGEMENT","args":[{"var":"u"},{"var":"v"},{"var":"K_sh"},{"var":"X"},{"var":"x"}]}}}],"premises":[],"witness_realizations":{},"proof_ref":"### P-001D — exact nonnegative Euler-product enlargement"}
```

- Prenex statement: for every nonnegative multiplicative \(u,v\), every
  \(K_{\rm sh}\in\mathbb N_{>0}\), and every \(2\le X\le x\), with
  \(L_p(u,v):=\sum_{j\ge0}u(p^j)v(p^j)p^{-j}\ge1\),
  \[
  \prod_{\substack{p<X\\p\nmid K_{\rm sh}}}L_p(u,v)
  \le\prod_{\substack{p<x\\p\nmid K_{\rm sh}}}L_p(u,v).
  \tag{AD-EULER-ENLARGE}
  \]
- Dependency order: fixed \(u,v\) -> no witnesses -> uniform
  \(K_{\rm sh},X,x\).
- Exact subject map: `SUB-P002-EULER-X` maps to `SUB-P002-EULER-x`; the
  extra literal factors have \(X\le p<x\) and are at least one.
- Premise maps: none.

### P-005A — geometric and common-prime summability adapters

```mathminer-s3
{"schema":"mathminer.s3/1","id":"P-005A","kind":"PROPOSITION","binders":[{"key":"lambda_seq","type":{"fn":{"args":["Nat"],"return":"Real"}}},{"key":"lambda","type":"Real"},{"key":"u","type":{"fn":{"args":["Nat"],"return":"Real"}}},{"key":"v","type":{"fn":{"args":["Nat"],"return":"Real"}}},{"key":"K_sh","type":"Nat"},{"key":"X","type":"Real"}],"uses_definitions":["D-014","D-S45-P005A-SUMMABILITY","D-S45-SHIFT-FAMILY-DOMAIN"],"source_anchors":[],"hypotheses":[{"key":"domain","proposition":{"def":{"id":"D-S45-SHIFT-FAMILY-DOMAIN","args":[{"var":"lambda_seq"},{"var":"lambda"},{"var":"u"},{"var":"v"},{"var":"K_sh"},{"var":"X"}]}}}],"witnesses":[],"conclusions":[{"key":"summability_and_factorization","proposition":{"def":{"id":"D-S45-P005A-SUMMABILITY","args":[{"var":"lambda_seq"},{"var":"lambda"},{"var":"u"},{"var":"v"},{"var":"K_sh"},{"var":"X"}]}}}],"premises":[],"witness_realizations":{},"proof_ref":"### P-005A — geometric and common-prime summability adapters"}
```

- Prenex statement: fix a nonnegative sequence
  \((\lambda_i)_{i\in\mathbb N}\) and \(0\le\lambda<2\). Uniformly for all
  nonnegative multiplicative \(u,v\) satisfying
  \(0\le u(p^{i+j})v(p^j)\le\lambda_i\lambda^j\), both prime-local series
  \[
  \sum_{j\ge0}u(p^j)v(p^j)p^{-j},\qquad
  \sum_{j\ge0}u(p^{i+j})v(p^j)(1+j\log p)p^{-j}
  \]
  converge; for every \(K_{\rm sh}\ge1\), \(X\ge2\), the exact outer
  common-prime decomposition family in P-001 has finite support; and the
  nonnegative infinite \(d\)-majorant used in P-005 is summable and equals
  the finite product of its shifted local series over
  \(p^i\parallel K_{\rm sh}\).
- Dependency order: fixed \((\lambda_i),\lambda\) -> no witnesses -> uniform
  \(u,v,p,K_{\rm sh},X\).
- Domain/range: \(p\) is prime, hence \(p\ge2>\lambda\); all summands are
  nonnegative real numbers.
- Premise maps: none.
- Derivation certificate: the \(i=0\) majorant gives geometric comparison
  with \(\lambda_0(\lambda/p)^j\). For fixed \(i\), put
  \(q:=\lambda/p<1\); the shifted series is bounded by
  \(\lambda_i\{(1-q)^{-1}+q\log p(1-q)^{-2}\}\). In the exact common-prime
  family the inner positive-integer sum is empty for \(d\ge X\), so that
  family has finite support inside the positive integers \(d<X\). After the
  component bounds and P-004, nonnegative-series factorization identifies the
  enlarged \(d\)-majorant with a finite product of the convergent shifted
  local series.
- Source/S2 anchor: ET Lemma 2, pp. 23--24; S2 R1 E4a.
- Definitions used: D-014.

### P-001C — bounded reciprocal-smoothing adapter

```mathminer-s3
{"schema":"mathminer.s3/1","id":"P-001C","kind":"PROPOSITION","binders":[{"key":"K_sh","type":"Nat"},{"key":"z","type":"Real"}],"uses_definitions":["D-001","D-006","D-015","D-S45-ELL-G","D-S45-P001A-DOMAIN","D-S45-P001C-DOMAIN","D-S45-P001C-SMOOTHING","D-S45-RECIP-G"],"source_anchors":[],"hypotheses":[{"key":"domain","proposition":{"def":{"id":"D-S45-P001C-DOMAIN","args":[{"var":"K_sh"},{"var":"z"}]}}}],"witnesses":[],"conclusions":[{"key":"bounded_reciprocal_smoothing","proposition":{"def":{"id":"D-S45-P001C-SMOOTHING","args":[{"var":"K_sh"},{"var":"z"}]}}}],"premises":[{"id":"recip-initial","producer":"P-001A","closure_role":"REQUIRED","guards":[{"key":"recip_domain","proposition":{"def":{"id":"D-S45-P001A-DOMAIN","args":[{"def":{"id":"D-S45-RECIP-G","args":[{"var":"K_sh"}]}},{"var":"z"}]}}}],"binder_map":{"g":{"def":{"id":"D-S45-RECIP-G","args":[{"var":"K_sh"}]}},"X":{"var":"z"}},"hypothesis_map":{"domain":{"guard":"recip_domain"}},"witness_map":{},"consume":["empty_case","singleton_case"]},{"id":"ell-initial","producer":"P-001A","closure_role":"REQUIRED","guards":[{"key":"ell_domain","proposition":{"def":{"id":"D-S45-P001A-DOMAIN","args":[{"def":{"id":"D-S45-ELL-G","args":[]}},{"var":"z"}]}}}],"binder_map":{"g":{"def":{"id":"D-S45-ELL-G","args":[]}},"X":{"var":"z"}},"hypothesis_map":{"domain":{"guard":"ell_domain"}},"witness_map":{},"consume":["empty_case","singleton_case"]},{"id":"w1-domination","producer":"P-051F1","closure_role":"REQUIRED","binder_map":{},"hypothesis_map":{},"witness_map":{"c_1":"p001c_c_w1","C_1":"p001c_C_w1","Lambda_1":"p001c_Lambda_w1"},"consume":["weight_type","dominates_base","dominates_shift"]}],"witness_realizations":{},"proof_ref":"### P-001C — bounded reciprocal-smoothing adapter"}
```

- Prenex statement: for every \(K_{\rm sh}\in\mathbb N_{>0}\) and
  \(z\in(0,2)\),
  \[
  \sum_{m<z}\tau(mK_{\rm sh})^{-1}
  \le w_1(K_{\rm sh})\sum_{m<z}\ell(m)^{-1/2}.
  \]
- Dependency order: no fixed parameters -> no constants -> uniform
  \(K_{\rm sh},z\).
- Premise maps: P-001A with \(X:=z\) on both sides; P-051F1 domination
  \(w_1(K_{\rm sh})\ge a_0(K_{\rm sh})\). The empty and singleton subjects
  agree literally.

### P-002 — first logarithmic component

```mathminer-s3
{"schema":"mathminer.s3/1","id":"P-002","kind":"PROPOSITION","binders":[{"key":"lambda_seq","type":{"fn":{"args":["Nat"],"return":"Real"}}},{"key":"lambda","type":"Real"},{"key":"u","type":{"fn":{"args":["Nat"],"return":"Real"}}},{"key":"v","type":{"fn":{"args":["Nat"],"return":"Real"}}},{"key":"K_sh","type":"Nat"},{"key":"x","type":"Real"}],"uses_definitions":["D-S45-BFIRST-G","D-S45-EXT001-DOMAIN","D-S45-P001B-DOMAIN","D-S45-P001D-DOMAIN","D-S45-P002-C","D-S45-P002-FIRST-LOG-FAMILY","D-S45-REAL-RATIO","D-S45-SHIFT-FAMILY-DOMAIN","DP-MEAN::DP-MEAN-DEF-006","DP-MEAN::DP-MEAN-DEF-007","DP-MEAN::DP-MEAN-DEF-008"],"source_anchors":[],"hypotheses":[{"key":"domain","proposition":{"def":{"id":"D-S45-SHIFT-FAMILY-DOMAIN","args":[{"var":"lambda_seq"},{"var":"lambda"},{"var":"u"},{"var":"v"},{"var":"K_sh"},{"var":"x"}]}}}],"witnesses":[{"key":"C_2","type":"Real","depends_on":["lambda_seq","lambda"]}],"conclusions":[{"key":"C_2_positive","proposition":{"op":{"name":"gt","args":[{"var":"C_2"},{"lit":{"type":"Real","value":"0"}}]}}},{"key":"first_log_bound_family","proposition":{"def":{"id":"D-S45-P002-FIRST-LOG-FAMILY","args":[{"var":"lambda_seq"},{"var":"lambda"},{"var":"u"},{"var":"v"},{"var":"K_sh"},{"var":"x"},{"var":"C_2"}]}}}],"premises":[{"id":"large-mean","producer":"A-S45-EXT001-EXISTS","closure_role":"REQUIRED","scope_binders":[{"key":"d","type":"Nat"}],"guards":[{"key":"ext_h_nonnegative_multiplicative","proposition":{"op":{"name":"and","args":[{"def":{"id":"DP-MEAN::DP-MEAN-DEF-006","args":[{"def":{"id":"D-S45-BFIRST-G","args":[{"var":"u"},{"var":"v"},{"var":"K_sh"}]}}]}},{"def":{"id":"DP-MEAN::DP-MEAN-DEF-007","args":[{"def":{"id":"D-S45-BFIRST-G","args":[{"var":"u"},{"var":"v"},{"var":"K_sh"}]}}]}}]}}},{"key":"ext_prime_power_geometric_bound","proposition":{"def":{"id":"DP-MEAN::DP-MEAN-DEF-008","args":[{"def":{"id":"D-S45-BFIRST-G","args":[{"var":"u"},{"var":"v"},{"var":"K_sh"}]}},{"app":{"fn":{"var":"lambda_seq"},"args":[{"lit":{"type":"Nat","value":"0"}}]}},{"var":"lambda"}]}}},{"key":"ext_lambda_1_nonnegative","proposition":{"op":{"name":"ge","args":[{"app":{"fn":{"var":"lambda_seq"},"args":[{"lit":{"type":"Nat","value":"0"}}]}},{"lit":{"type":"Real","value":"0"}}]}}},{"key":"ext_lambda_2_range","proposition":{"op":{"name":"and","args":[{"op":{"name":"ge","args":[{"var":"lambda"},{"lit":{"type":"Real","value":"0"}}]}},{"op":{"name":"lt","args":[{"var":"lambda"},{"lit":{"type":"Real","value":"2"}}]}}]}}},{"key":"ext_X_at_least_2","proposition":{"op":{"name":"ge","args":[{"def":{"id":"D-S45-REAL-RATIO","args":[{"var":"x"},{"var":"d"}]}},{"lit":{"type":"Real","value":"2"}}]}}}],"binder_map":{"h":{"def":{"id":"D-S45-BFIRST-G","args":[{"var":"u"},{"var":"v"},{"var":"K_sh"}]}},"lambda_1":{"app":{"fn":{"var":"lambda_seq"},"args":[{"lit":{"type":"Nat","value":"0"}}]}},"lambda_2":{"var":"lambda"},"X":{"def":{"id":"D-S45-REAL-RATIO","args":[{"var":"x"},{"var":"d"}]}}},"hypothesis_map":{"h_nonnegative_multiplicative":{"guard":"ext_h_nonnegative_multiplicative"},"prime_power_geometric_bound":{"guard":"ext_prime_power_geometric_bound"},"lambda_1_nonnegative":{"guard":"ext_lambda_1_nonnegative"},"lambda_2_range":{"guard":"ext_lambda_2_range"},"X_at_least_2":{"guard":"ext_X_at_least_2"}},"witness_map":{},"consume":["mean_bound_exists"]},{"id":"large-enlarge","producer":"P-001D","closure_role":"REQUIRED","scope_binders":[{"key":"d","type":"Nat"}],"guards":[{"key":"enlarge_domain","proposition":{"def":{"id":"D-S45-P001D-DOMAIN","args":[{"var":"u"},{"var":"v"},{"var":"K_sh"},{"def":{"id":"D-S45-REAL-RATIO","args":[{"var":"x"},{"var":"d"}]}},{"var":"x"}]}}}],"binder_map":{"u":{"var":"u"},"v":{"var":"v"},"K_sh":{"var":"K_sh"},"X":{"def":{"id":"D-S45-REAL-RATIO","args":[{"var":"x"},{"var":"d"}]}},"x":{"var":"x"}},"hypothesis_map":{"domain":{"guard":"enlarge_domain"}},"witness_map":{},"consume":["euler_enlargement"]},{"id":"small-branch","producer":"P-001B","closure_role":"REQUIRED","scope_binders":[{"key":"d","type":"Nat"}],"guards":[{"key":"small_domain","proposition":{"def":{"id":"D-S45-P001B-DOMAIN","args":[{"var":"u"},{"var":"v"},{"var":"K_sh"},{"var":"d"},{"var":"x"},{"def":{"id":"D-S45-REAL-RATIO","args":[{"var":"x"},{"var":"d"}]}}]}}}],"binder_map":{"u":{"var":"u"},"v":{"var":"v"},"K_sh":{"var":"K_sh"},"d":{"var":"d"},"x":{"var":"x"},"X":{"def":{"id":"D-S45-REAL-RATIO","args":[{"var":"x"},{"var":"d"}]}}},"hypothesis_map":{"domain":{"guard":"small_domain"}},"witness_map":{},"consume":["bounded_first_log"]}],"witness_realizations":{"C_2":{"def":{"id":"D-S45-P002-C","args":[{"var":"lambda_seq"},{"var":"lambda"}]}}},"proof_ref":"### P-002 — first logarithmic component"}
```

- Prenex statement: for every nonnegative multiplicative \(u,v\), every
  \(K_{\rm sh},d\ge1\), \(x\ge2\), sequences \(\lambda_i\ge0\) and
  \(\lambda\in[0,2)\), if \(d\mid K_{\rm sh}^{\infty}\) and
  \(0\le u(p^{i+j})v(p^j)\le\lambda_i\lambda^j\), then
  \[
  \sum_{\substack{m<x/d\\(m,K_{\rm sh})=1}}u(m)v(m)\log(x/d)
  \ll {x\over d}\prod_{\substack{p<x\\p\nmid K_{\rm sh}}}
  \sum_{j\ge0}u(p^j)v(p^j)p^{-j}.
  \]
- Local equalities: \(h(r)=u(r)v(r)1_{(r,K_{\rm sh})=1}\).
- Domain/range: if \(x/d<2\), the finite cutoff is handled directly.
- Input subject: first inner component of P-001. Output: exact Euler majorant.
- Premise maps:
  - `MAP-P002-EXT001` (used only when \(x/d\ge2\)):

    | producer | producer slot | producer domain | consumer term | domain evidence |
    |---|---|---|---|---|
    | EXT-001 | `h` | nonnegative multiplicative | \(r\mapsto u(r)v(r)1_{(r,K_{\rm sh})=1}\) | multiplicativity and nonnegativity from the P-002 hypotheses |
    | EXT-001 | `lambda_1` | \(\mathbb R_{\ge0}\) | \(\lambda_0\) | local bound at exponent zero |
    | EXT-001 | `lambda_2` | \([0,2)\) | \(\lambda\) | P-002 hypothesis |
    | EXT-001 | `X` | \(\mathbb R_{\ge2}\) | \(x/d\) | branch hypothesis \(x/d\ge2\) |

    Producer hypothesis: the local bound is the P-002 local bound, and a prime
    dividing \(K_{\rm sh}\) has positive-exponent local value zero.
    Consumed conclusion: the EXT-001 upper bound for `SUB-P002-MEAN`.
    Subject: `SUB-P002-MEAN` is literally the P-002 inner sum without the
    scalar \(\log(x/d)\); its producer Euler subject is
    `SUB-P002-EULER-X` with \(X=x/d\).
    Constants/uniformity: \((\lambda_0,\lambda)\to C\to(x,d,K_{\rm sh})\).
  - `MAP-P002-P001D`: slots \(u:=u,v:=v,K_{\rm sh}:=K_{\rm sh},
    X:=x/d,x:=x\); \(2\le X\le x\) follows from the current branch and
    \(d\ge1\). Consumed conclusion is (AD-EULER-ENLARGE), mapping
    `SUB-P002-EULER-X` to the exact conclusion subject
    `SUB-P002-EULER-x`. It introduces no constant and is uniform in
    \(x,d,K_{\rm sh}\).
  - `MAP-P002-P001B`: slots \(u:=u,v:=v,K_{\rm sh}:=K_{\rm sh},d:=d,
    x:=x,X:=x/d\); domain evidence \(0<x/d<2\); consumed conclusion is
    (AD-BFIRST), whose subject is literally `SUB-P002-FIRST-LOG`. It has no
    constant and is uniform in \((x,d,K_{\rm sh})\).
- Derivation certificate: use `MAP-P002-EXT001` on \(x/d\ge2\), enlarge its
  Euler product by P-001D, and multiply by \(\log(x/d)\). Use P-001B on
  \(0<x/d<2\).
- Source/S2 anchor: ET p. 24; S2 R1 E4, R2.8(2).
- Definitions used: none.

### P-003 — second logarithmic component

```mathminer-s3
{"schema":"mathminer.s3/1","id":"P-003","kind":"PROPOSITION","binders":[{"key":"u","type":{"fn":{"args":["Nat"],"return":"Real"}}},{"key":"v","type":{"fn":{"args":["Nat"],"return":"Real"}}},{"key":"K_sh","type":"Nat"},{"key":"x","type":"Real"}],"uses_definitions":["D-S45-P003-DOMAIN","D-S45-P003-SECOND-LOG-FAMILY"],"source_anchors":[],"hypotheses":[{"key":"domain","proposition":{"def":{"id":"D-S45-P003-DOMAIN","args":[{"var":"u"},{"var":"v"},{"var":"K_sh"},{"var":"x"}]}}}],"witnesses":[],"conclusions":[{"key":"second_log_bound_family","proposition":{"def":{"id":"D-S45-P003-SECOND-LOG-FAMILY","args":[{"var":"u"},{"var":"v"},{"var":"K_sh"},{"var":"x"}]}}}],"premises":[],"witness_realizations":{},"proof_ref":"### P-003 — second logarithmic component"}
```

- Prenex statement: for every nonnegative multiplicative \(u,v\), every
  \(K_{\rm sh},d\ge1\), \(x\ge2\), with \(d\mid K_{\rm sh}^{\infty}\),
  \[
  \sum_{\substack{m<x/d\\(m,K_{\rm sh})=1}}u(m)v(m)\log d
  \le {x\over d}\log d\prod_{\substack{p<x\\p\nmid K_{\rm sh}}}
  \sum_{j\ge0}u(p^j)v(p^j)p^{-j}.
  \]
- Local equalities: none.
- Domain/range: nonnegative series.
- Input subject: second inner component of P-001. Output: harmonic Euler bound.
- Premise maps: none (root).
- Derivation certificate: enlarge to \(m<x\), use \(1/m\ge d/x\), then
  expand the nonnegative harmonic sum primewise.
- Source/S2 anchor: ET p. 24; S2 R1 E4, R2.8(3).
- Definitions used: none.

### P-004 — logarithmic factorization

```mathminer-s3
{"schema":"mathminer.s3/1","id":"P-004","kind":"PROPOSITION","binders":[],"uses_definitions":["D-S45-P004-DOMAIN","D-S45-P004-FACTORIZATION"],"source_anchors":[],"hypotheses":[{"key":"domain","proposition":{"def":{"id":"D-S45-P004-DOMAIN","args":[]}}}],"witnesses":[],"conclusions":[{"key":"log_factorization","proposition":{"def":{"id":"D-S45-P004-FACTORIZATION","args":[]}}}],"premises":[],"witness_realizations":{},"proof_ref":"### P-004 — logarithmic factorization"}
```

- Prenex statement: \(\forall d\in\mathbb N_{>0}\),
  \[
  1+\log d\le\prod_{p^j\parallel d}(1+j\log p).
  \]
- Local equalities: \(\log d=\sum_{p^j\parallel d}j\log p\).
- Domain/range: finite positive product.
- Input subject: \(1+\log d\). Output: primewise product.
- Premise maps: none (root).
- Derivation certificate: retain constant and linear terms of the expansion.
- Source/S2 anchor: ET p. 24; S2 R2.8(4).
- Definitions used: none.

### P-005 — shifted mean theorem

```mathminer-s3
{"schema":"mathminer.s3/1","id":"P-005","kind":"PROPOSITION","binders":[{"key":"lambda_seq","type":{"fn":{"args":["Nat"],"return":"Real"}}},{"key":"lambda","type":"Real"},{"key":"u","type":{"fn":{"args":["Nat"],"return":"Real"}}},{"key":"v","type":{"fn":{"args":["Nat"],"return":"Real"}}},{"key":"K_sh","type":"Nat"},{"key":"X","type":"Real"}],"uses_definitions":["D-014","D-S45-P001-DOMAIN","D-S45-P003-DOMAIN","D-S45-P004-DOMAIN","D-S45-P005-C","D-S45-P005-SHIFTED-MEAN","D-S45-SHIFT-FAMILY-DOMAIN"],"source_anchors":[],"hypotheses":[{"key":"domain","proposition":{"def":{"id":"D-S45-SHIFT-FAMILY-DOMAIN","args":[{"var":"lambda_seq"},{"var":"lambda"},{"var":"u"},{"var":"v"},{"var":"K_sh"},{"var":"X"}]}}}],"witnesses":[{"key":"C_5","type":"Real","depends_on":["lambda_seq","lambda"]}],"conclusions":[{"key":"C_5_positive","proposition":{"op":{"name":"gt","args":[{"var":"C_5"},{"lit":{"type":"Real","value":"0"}}]}}},{"key":"shifted_mean_bound","proposition":{"def":{"id":"D-S45-P005-SHIFTED-MEAN","args":[{"var":"lambda_seq"},{"var":"lambda"},{"var":"u"},{"var":"v"},{"var":"K_sh"},{"var":"X"},{"var":"C_5"}]}}}],"premises":[{"id":"summability","producer":"P-005A","closure_role":"REQUIRED","binder_map":{"lambda_seq":{"var":"lambda_seq"},"lambda":{"var":"lambda"},"u":{"var":"u"},"v":{"var":"v"},"K_sh":{"var":"K_sh"},"X":{"var":"X"}},"hypothesis_map":{"domain":{"hypothesis":"domain"}},"witness_map":{},"consume":["summability_and_factorization"]},{"id":"decompose","producer":"P-001","closure_role":"REQUIRED","guards":[{"key":"p001_domain","proposition":{"def":{"id":"D-S45-P001-DOMAIN","args":[{"var":"u"},{"var":"v"},{"var":"K_sh"},{"var":"X"}]}}}],"binder_map":{"u":{"var":"u"},"v":{"var":"v"},"K_sh":{"var":"K_sh"},"x":{"var":"X"}},"hypothesis_map":{"domain":{"guard":"p001_domain"}},"witness_map":{},"consume":["common_prime_decomposition"]},{"id":"first-component","producer":"P-002","closure_role":"REQUIRED","binder_map":{"lambda_seq":{"var":"lambda_seq"},"lambda":{"var":"lambda"},"u":{"var":"u"},"v":{"var":"v"},"K_sh":{"var":"K_sh"},"x":{"var":"X"}},"hypothesis_map":{"domain":{"hypothesis":"domain"}},"witness_map":{"C_2":"p005_C2"},"consume":["C_2_positive","first_log_bound_family"]},{"id":"second-component","producer":"P-003","closure_role":"REQUIRED","guards":[{"key":"p003_domain","proposition":{"def":{"id":"D-S45-P003-DOMAIN","args":[{"var":"u"},{"var":"v"},{"var":"K_sh"},{"var":"X"}]}}}],"binder_map":{"u":{"var":"u"},"v":{"var":"v"},"K_sh":{"var":"K_sh"},"x":{"var":"X"}},"hypothesis_map":{"domain":{"guard":"p003_domain"}},"witness_map":{},"consume":["second_log_bound_family"]},{"id":"factorization","producer":"P-004","closure_role":"REQUIRED","guards":[{"key":"p004_domain","proposition":{"def":{"id":"D-S45-P004-DOMAIN","args":[]}}}],"binder_map":{},"hypothesis_map":{"domain":{"guard":"p004_domain"}},"witness_map":{},"consume":["log_factorization"]}],"witness_realizations":{"C_5":{"def":{"id":"D-S45-P005-C","args":[{"var":"lambda_seq"},{"var":"lambda"}]}}},"proof_ref":"### P-005 — shifted mean theorem"}
```

- Prenex statement: for every sequence
  \((\lambda_i)_{i\in\mathbb N}\) with \(\lambda_i\ge0\) and every
  \(\lambda\in[0,2)\), there is a constant \(C_5>0\), selected before and
  independent of the nonnegative multiplicative functions \(u,v\), such
  that for every such \(u,v\) satisfying
  \(0\le u(p^{i+j})v(p^j)\le\lambda_i\lambda^j\), every
  \(K_{\rm sh}\in\mathbb N_{>0}\), and every
  \(X\in\mathbb R_{\ge2}\),
  \[
  \sum_{n<X}u(K_{\rm sh}n)v(n)\ll
  \prod_{\substack{p^i\parallel K_{\rm sh}\\p<X}}\mathcal S[u,v](p^i)
  \prod_{\substack{p^i\parallel K_{\rm sh}\\p\ge X}}u(p^i)
  {X\over\log X}\prod_{p<X}\sum_{j\ge0}u(p^j)v(p^j)p^{-j}.
  \]
- Constant order: \((\lambda_i),\lambda\to C_5\to u,v,K_{\rm sh},X\).
  The proof permits \(C_5\) to depend only on \((\lambda_0,\lambda)\): the
  sole nontrivial comparison constant is the EXT-001 constant for
  \(h_K(n)=u(n)v(n)1_{(n,K_{\rm sh})=1}\), which is independent of
  \(h_K\) and hence of \(u,v,K_{\rm sh}\). All remaining comparisons have
  absolute constant one, apart from one fixed enlargement for \(X/d<2\).
- Local equalities: \(\mathcal S\) is D-014.
- Domain/range: convergent local series; uniform in
  \(u,v,K_{\rm sh},X\) for the fixed majorants.
- Input subject: shifted mean. Output: exact ET-L2 product.
- Premise maps:
  - `MAP-P005-P005A`: slots
    \((\lambda_i):=(\lambda_i),\lambda:=\lambda,u:=u,v:=v,
    K_{\rm sh}:=K_{\rm sh},X:=X\), with the prime slot universally
    instantiated where a local series is used. The nonnegativity, parameter
    range, multiplicativity, and prime-power majorant hypotheses are exactly
    the P-005 hypotheses. Consumed conclusions are local Euler-series
    convergence, finite support of the exact common-prime outer family, and
    convergence and factorization of its enlarged \(d\)-majorant; no new
    witness or comparison constant is introduced.
  - `MAP-P005-P001`:

    | producer | slot | domain | consumer term | evidence |
    |---|---|---|---|---|
    | P-001 | `u` | nonnegative multiplicative | \(u\) | P-005 hypothesis |
    | P-001 | `v` | nonnegative multiplicative | \(v\) | P-005 hypothesis |
    | P-001 | `K_sh` | \(\mathbb N_{>0}\) | \(K_{\rm sh}\) | P-005 binder |
    | P-001 | `x` | \(\mathbb R_{\ge2}\) | \(X\) | P-005 binder |

    Hypotheses: P-005A supplies the local geometric convergence and the
    finite-support summability premise.
    Conclusion/subject: `SUB-P001-SHIFTED-LOG` equals the P-001 left side;
    no adapter. Constants: none.
  - `MAP-P005-P002`:

    | producer | slot | domain | consumer term | evidence |
    |---|---|---|---|---|
    | P-002 | `u` | nonnegative multiplicative | \(u\) | P-005 hypothesis |
    | P-002 | `v` | nonnegative multiplicative | \(v\) | P-005 hypothesis |
    | P-002 | `K_sh` | \(\mathbb N_{>0}\) | \(K_{\rm sh}\) | P-005 binder |
    | P-002 | `d` | \(\mathbb N_{>0}\) | current \(d\mid K_{\rm sh}^{\infty}\) | P-001 index |
    | P-002 | `x` | \(\mathbb R_{\ge2}\) | \(X\) | P-005 binder |
    | P-002 | `(lambda_i)` | nonnegative sequence | \((\lambda_i)_i\) | P-005 binder |
    | P-002 | `lambda` | \([0,2)\) | \(\lambda\) | P-005 binder |

    Hypotheses/subject: literal first P-001 component; P-002 itself dispatches
    its bounded inner cutoff. Constants are uniform in the current \(d\).
  - `MAP-P005-P003`: slots \(u:=u,v:=v,K_{\rm sh}:=K_{\rm sh},d:=d,
    x:=X\); domains are P-005 binders and the P-001 index; the consumed
    subject is literally the second logarithmic component.
  - `MAP-P005-P004`: slot \(d:=d\in\mathbb N_{>0}\), from the P-001 index;
    consumed subject is the exact factor \(1+\log d\).
- Derivation certificate: substitute component bounds into P-001, apply
  P-004, factor the \(d\)-sum primewise, and divide by each unshifted local
  denominator; primes \(p\ge x\) give \(u(p^i)\). P-005A supplies convergence
  of both local series, finite support of the exact decomposition, and
  summability plus factorization of the enlarged \(d\)-majorant. EXT-001 applied
  with \((\lambda_0,\lambda)\) supplies one constant independent of the
  auxiliary coprimality-truncated function, which proves the stated family
  uniformity.
- Source/S2 anchor: ET Lemma 2, pp. 23--24; DP-MEAN-T001; S2 R1 E4--E4a,
  R2.8(5).
- Definitions used: D-014.

### P-006 — convergent Euler error product

```mathminer-s3
{"schema":"mathminer.s3/1","id":"P-006","kind":"PROPOSITION","binders":[{"key":"C_err","type":"Real"},{"key":"eta","type":"Real"},{"key":"r","type":{"fn":{"args":["Nat"],"return":"Real"}}}],"uses_definitions":["D-S45-P006-CMINUS","D-S45-P006-CPLUS","D-S45-P006-DOMAIN","D-S45-P006-P0","D-S45-P006-PRODUCT-BOUNDS"],"source_anchors":[],"hypotheses":[{"key":"domain","proposition":{"def":{"id":"D-S45-P006-DOMAIN","args":[{"var":"C_err"},{"var":"eta"},{"var":"r"}]}}}],"witnesses":[{"key":"P_0","type":"Real","depends_on":["C_err","eta","r"]},{"key":"C_minus","type":"Real","depends_on":["C_err","eta","r"]},{"key":"C_plus","type":"Real","depends_on":["C_err","eta","r"]}],"conclusions":[{"key":"uniform_error_product_bounds","proposition":{"def":{"id":"D-S45-P006-PRODUCT-BOUNDS","args":[{"var":"C_err"},{"var":"eta"},{"var":"r"},{"var":"P_0"},{"var":"C_minus"},{"var":"C_plus"}]}}}],"premises":[],"witness_realizations":{"P_0":{"def":{"id":"D-S45-P006-P0","args":[{"var":"C_err"},{"var":"eta"},{"var":"r"}]}},"C_minus":{"def":{"id":"D-S45-P006-CMINUS","args":[{"var":"C_err"},{"var":"eta"},{"var":"r"}]}},"C_plus":{"def":{"id":"D-S45-P006-CPLUS","args":[{"var":"C_err"},{"var":"eta"},{"var":"r"}]}}},"proof_ref":"### P-006 — convergent Euler error product"}
```

- Prenex statement: for every \(C,\eta>0\), every real family \(r_p\) with
  \(|r_p|\le Cp^{-1-\eta}\) and \(1+r_p>0\), there exists \(P_0\) such that
  all \(\prod_{P_0\le p<B}(1+r_p)\) are bounded above and below by positive
  constants uniformly in \(B>P_0\).
- Local equalities: none.
- Domain/range: prime products.
- Input subject: absolutely summable local errors. Output: uniform product
  comparison.
- Premise maps: none (root).
- Derivation certificate: \(|\log(1+r_p)|\le2|r_p|\) beyond \(P_0\), and
  \(\sum_p p^{-1-\eta}<\infty\); retain the finite prefix exactly.
- Source/S2 anchor: S2 E2a and R2.8(6).
- Definitions used: none.

### P-006A — exact prime-index and finite-prefix adapters

```mathminer-s3
{"schema":"mathminer.s3/1","id":"P-006A","kind":"PROPOSITION","binders":[{"key":"c","type":"Real"},{"key":"P_0","type":"Real"},{"key":"L","type":{"fn":{"args":["Nat"],"return":"Real"}}}],"uses_definitions":["D-S45-P006A-DOMAIN","D-S45-P006A-INDEX-ADAPTERS"],"source_anchors":[],"hypotheses":[{"key":"domain","proposition":{"def":{"id":"D-S45-P006A-DOMAIN","args":[{"var":"c"},{"var":"P_0"},{"var":"L"}]}}}],"witnesses":[],"conclusions":[{"key":"prime_index_and_prefix","proposition":{"def":{"id":"D-S45-P006A-INDEX-ADAPTERS","args":[{"var":"c"},{"var":"P_0"},{"var":"L"}]}}}],"premises":[],"witness_realizations":{},"proof_ref":"### P-006A — exact prime-index and finite-prefix adapters"}
```

- Prenex statement: for \(t\in\mathbb R_{\ge2}\), define
  \[
  M_{\le}(t):=\prod_{p\le t}(1-1/p),\qquad
  b(t):=\prod_{p=t}(1-1/p),\qquad
  M_{<}(t):=M_{\le}(t)/b(t).
  \]
  The product defining \(b(t)\) is empty unless \(t\) itself is prime.
  For \(2\le A<B\) and every \(c\in\mathbb R\),
  \[
  \prod_{A\le p<B}(1-1/p)^{-c}
  =\left({M_{<}(B)\over M_{<}(A)}\right)^{-c}
  =\left({M_{\le}(B)b(A)\over M_{\le}(A)b(B)}\right)^{-c}.
  \tag{AD-PRIME-INDEX}
  \]
  For any threshold \(P_0\in\mathbb R_{\ge2}\) and positive prime family \(L_p\),
  \[
  \prod_{A\le p<B}L_p=
  \left(\prod_{A\le p<\min(B,P_0)}L_p\right)
  \left(\prod_{\max(A,P_0)\le p<B}L_p\right).
  \tag{AD-FINITE-PREFIX}
  \]
  If \(B\le A\), every displayed interval product is interpreted as the
  exact empty product \(1\).
- Dependency order: fixed \(c,P_0,(L_p)\) -> no witnesses -> uniform \(A,B\).
- Premise maps: none. These are finite index-partition identities.

### P-007 — exact local-factor product with large and finite endpoint branches

```mathminer-s3
{"schema":"mathminer.s3/1","id":"P-007","kind":"PROPOSITION","binders":[{"key":"c","type":"Real"},{"key":"eta","type":"Real"},{"key":"C_err","type":"Real"},{"key":"L","type":{"fn":{"args":["Nat"],"return":"Real"}}}],"uses_definitions":["D-S45-MIN-ETA-ONE","D-S45-P006-DOMAIN","D-S45-P006A-DOMAIN","D-S45-P007-CFAC","D-S45-P007-CMINUS","D-S45-P007-CPLUS","D-S45-P007-DOMAIN","D-S45-P007-ERROR-FAMILY","D-S45-P007-PERR","D-S45-P007-PRODUCT-COMPARISON"],"source_anchors":[],"hypotheses":[{"key":"domain","proposition":{"def":{"id":"D-S45-P007-DOMAIN","args":[{"var":"c"},{"var":"eta"},{"var":"C_err"},{"var":"L"}]}}}],"witnesses":[{"key":"P_err","type":"Real","depends_on":["c","eta","C_err","L"]},{"key":"C_minus","type":"Real","depends_on":["c","eta","C_err","L"]},{"key":"C_plus","type":"Real","depends_on":["c","eta","C_err","L"]}],"conclusions":[{"key":"local_product_comparison","proposition":{"def":{"id":"D-S45-P007-PRODUCT-COMPARISON","args":[{"var":"c"},{"var":"eta"},{"var":"C_err"},{"var":"L"},{"var":"P_err"},{"var":"C_minus"},{"var":"C_plus"}]}}}],"premises":[{"id":"mertens","producer":"EXT-002","closure_role":"REQUIRED","binder_map":{},"hypothesis_map":{},"witness_map":{"X_0":"mertens_X0","c_minus":"mertens_cminus","c_plus":"mertens_cplus"},"consume":["moving_endpoint_comparison"]},{"id":"error-product","producer":"A-S45-P006-EXISTS","closure_role":"REQUIRED","guards":[{"key":"p006_domain","proposition":{"def":{"id":"D-S45-P006-DOMAIN","args":[{"def":{"id":"D-S45-P007-CFAC","args":[{"var":"c"},{"var":"C_err"}]}},{"def":{"id":"D-S45-MIN-ETA-ONE","args":[{"var":"eta"}]}},{"def":{"id":"D-S45-P007-ERROR-FAMILY","args":[{"var":"c"},{"var":"C_err"},{"var":"L"}]}}]}}}],"binder_map":{"C_err":{"def":{"id":"D-S45-P007-CFAC","args":[{"var":"c"},{"var":"C_err"}]}},"eta":{"def":{"id":"D-S45-MIN-ETA-ONE","args":[{"var":"eta"}]}},"r":{"def":{"id":"D-S45-P007-ERROR-FAMILY","args":[{"var":"c"},{"var":"C_err"},{"var":"L"}]}}},"hypothesis_map":{"domain":{"guard":"p006_domain"}},"witness_map":{},"consume":["existentialized"]},{"id":"prefix","producer":"P-006A","closure_role":"REQUIRED","guards":[{"key":"prefix_domain","proposition":{"def":{"id":"D-S45-P006A-DOMAIN","args":[{"lit":{"type":"Real","value":"0"}},{"def":{"id":"D-S45-P007-PERR","args":[{"var":"c"},{"var":"eta"},{"var":"C_err"},{"var":"L"}]}},{"var":"L"}]}}}],"binder_map":{"c":{"lit":{"type":"Real","value":"0"}},"P_0":{"def":{"id":"D-S45-P007-PERR","args":[{"var":"c"},{"var":"eta"},{"var":"C_err"},{"var":"L"}]}},"L":{"var":"L"}},"hypothesis_map":{"domain":{"guard":"prefix_domain"}},"witness_map":{},"consume":["prime_index_and_prefix"]}],"witness_realizations":{"P_err":{"def":{"id":"D-S45-P007-PERR","args":[{"var":"c"},{"var":"eta"},{"var":"C_err"},{"var":"L"}]}},"C_minus":{"def":{"id":"D-S45-P007-CMINUS","args":[{"var":"c"},{"var":"eta"},{"var":"C_err"},{"var":"L"}]}},"C_plus":{"def":{"id":"D-S45-P007-CPLUS","args":[{"var":"c"},{"var":"eta"},{"var":"C_err"},{"var":"L"}]}}},"proof_ref":"### P-007 — exact local-factor product with large and finite endpoint branches"}
```

- Prenex statement (fixed slots):
  \[
  \forall c\in\mathbb R\;\forall\eta\in\mathbb R_{>0}\;
  \forall C_{\rm err}\in\mathbb R_{>0}\;
  \forall (L_p)_{p\ {\rm prime}}\in(\mathbb R_{>0})^{\mathcal P},
  \]
  assume
  \[
  \forall p\text{ prime with }p\ge2,\qquad
  |L_p-(1+c/p)|\le C_{\rm err}p^{-1-\eta},
  \]
  put
  \[
  T_c:={1\over2}|c(c-1)|2^{|c|+2},\qquad
  C_{\rm fac}:=1+2^{|c|}C_{\rm err}
    +T_c(1+|c|/2)+c^2.
  \tag{P007-fac}
  \]
  Then there exist a threshold \(P_{\rm err}\ge2\) and positive comparison
  constants \(C_-,C_+\), depending only on
  \((c,\eta,C_{\rm err},(L_p))\), such that uniformly for every
  \(A,B\in\mathbb R_{\ge2}\) with \(A<B\),
  \[
  C_-\left({\log B\over\log A}\right)^c
  \le \prod_{A\le p<B}L_p\le
  C_+\left({\log B\over\log A}\right)^c.
  \]
  If \(B\le A\), the product is exactly empty and
  equals \(1\). For \(A,B\) beyond the error threshold, use the Mertens
  quotient branch; if either endpoint is bounded, isolate the finite positive
  prefix and apply the large-endpoint branch only to the remaining range.
- Local equalities: none.
- Domain/range: positive products, including \(A=2\).
- Input subject: local-factor product. Output: logarithmic quotient.
- Premise maps:
  - `MAP-P007-EXT002-INTERVAL`: select the EXT-002 witnesses
    \(X_{\rm M},c_{{\rm M},-},c_{{\rm M},+}\), enlarge the P-007 error
    threshold so that \(P_{\rm err}\ge X_{\rm M}\), and on the nonempty
    large-prime branch put \(A':=\max(A,P_{\rm err})\).

    | producer | slot | domain | consumer term | evidence |
    |---|---|---|---|---|
    | EXT-002 | `x` | \(\mathbb R_{\ge2}\), asymptotic variable | \(2\) | unused asymptotic-output slot; literal admissible value |
    | EXT-002 | `A` | \(\mathbb R_{\ge2}\) | \(A'\) | \(A'\ge P_{\rm err}\ge X_{\rm M}\) |
    | EXT-002 | `B` | \(\mathbb R_{\ge2}\) | \(B\) | current nonempty branch has \(B>A'\) |

    Consumed conclusion is exactly (EXT002-interval) for
    \(\prod_{A'\le p<B}(1-1/p)\).  Since this product is positive,
    raising its two-sided comparison to the fixed real power \(-c\), with
    the inequality direction reversed when necessary, gives the required
    comparison for the large-prime \((1-1/p)^{-c}\) product.  Its constants
    depend only on the fixed \(c\) and the absolute EXT-002 witnesses.
  - `MAP-P007-P006`:

    | producer | slot | domain | consumer term | evidence |
    |---|---|---|---|---|
    | P-006 | `C` | \(\mathbb R_{>0}\) | \(C_{\rm fac}\) from (P007-fac) | explicit Taylor/product bound |
    | P-006 | `eta` | \(\mathbb R_{>0}\) | \(\min(\eta,1)\) | positive since \(\eta>0\) |
    | P-006 | `(r_p)` | real prime family | \(L_p(1-1/p)^c-1\) | exact definition |

    Hypotheses: Taylor's theorem on \(0\le1/p\le1/2\) gives
    \(|(1-1/p)^c-(1-c/p)|\le T_cp^{-2}\); the P-007 error inequality then
    gives \(|L_p(1-1/p)^c-1|\le C_{\rm fac}p^{-1-\min(\eta,1)}\).
    Positivity follows from \(L_p>0\). Consumed subject is the
    exact error product. Dependency order is
    \((c,\eta,C_{\rm err},(L_p))\to(P_{\rm err},C_-,C_+)\to(A,B)\).
  - `MAP-P007-P006A`:

    | producer | slot | domain | consumer term | evidence |
    |---|---|---|---|---|
    | P-006A | `c` | \(\mathbb R\) | \(0\) | unused AD-PRIME-INDEX slot; literal admissible value |
    | P-006A | `P_0` | \(\mathbb R_{\ge2}\) | \(P_{\rm err}\) | P-006 threshold |
    | P-006A | `(L_p)` | positive prime family | \((L_p)_p\) | P-007 fixed positive family |
    | P-006A | `A` | \(\mathbb R_{\ge2}\) | \(A\) | P-007 uniform endpoint |
    | P-006A | `B` | \(\mathbb R_{\ge2}\) | \(B\) | P-007 uniform endpoint |
    | P-006A | `t` | \(\mathbb R_{\ge2}\) | \(2\) | unused AD-PRIME-INDEX slot; literal admissible value |

    Hypotheses are \(2\le A,B\) and positivity of \(L_p\). The consumed
    conclusion is exactly (AD-FINITE-PREFIX), with threshold enlarged to
    include \(X_{\rm M}\). Subject is the literal finite/large product
    partition. The adapter adds no constant or uniform variable.
- Derivation certificate: split first into \(B\le A\) and \(A<B\). In the
  latter case choose the P-006 threshold \(P_0\), apply P-006A
  (AD-FINITE-PREFIX), factor each large-prime \(L_p\), apply P-006 and
  EXT-002's direct interval comparison on the large range, and multiply the
  exact finite positive prefix \(\prod_{A\le p<\min(B,P_0)}L_p\). No
  asymptotic statement is applied at a bounded endpoint.
- Source/S2 anchor: HR p. 78; S2 E2a and R2.8(7).
- Definitions used: none.

### P-008 — family-uniform local-product specialization

**Current statement:** `stage4/contracts/GroupA.lean:P008Statement`, with the
all-prime, all-member lower bound `mFin <= L q p`. The complete constructive
proof and explicit constants are W1--W2 above. The old pointwise-positive
contract and the failed `p<=P0` repair are not active statements.
The moment instantiation is W3.1; weight instantiations are W3.2--W5.
The replaced proof attempt is preserved under `stage3/revisions/WRAPUP_RETIRED_P008_2026-09-19.md`.


### P-010 — moment local values

```mathminer-s3
{"schema":"mathminer.s3/1","id":"P-010","kind":"PROPOSITION","binders":[{"key":"y","type":"Real"},{"key":"sigma","type":"Real"},{"key":"theta","type":"Real"},{"key":"u","type":"Real"}],"uses_definitions":["D-002","D-003","D-008","D-S45-P010-DOMAIN","D-S45-P010-LOCAL-VALUES"],"source_anchors":[],"hypotheses":[{"key":"domain","proposition":{"def":{"id":"D-S45-P010-DOMAIN","args":[{"var":"y"},{"var":"sigma"},{"var":"theta"},{"var":"u"}]}}}],"witnesses":[],"conclusions":[{"key":"moment_local_values","proposition":{"def":{"id":"D-S45-P010-LOCAL-VALUES","args":[{"var":"y"},{"var":"sigma"},{"var":"theta"},{"var":"u"}]}}}],"premises":[],"witness_realizations":{},"proof_ref":"### P-010 — moment local values"}
```

- Prenex statement: for every \(y\in(0,2)\), every
  \(u>\sigma\ge\theta\ge2\), every prime \(p\), and every \(\nu\ge1\),
  \(F_{y,u}\) is nonnegative multiplicative and
  \[
  F_{y,u}(p^\nu)=
  \begin{cases}
  0,&p<\theta,\\
  1,&\theta\le p<\sigma,\\
  (\nu+1)^{-1}\sum_{j=0}^{\nu}y^j,&\sigma\le p<u,\\
  1,&u\le p.
  \end{cases}
  \]
- Local equalities: the four prime ranges.
- Domain/range: values are nonnegative and at most \(\max(1,y)^\nu\).
- Input subject: D-008 at \(p^\nu\). Output: exact local values.
- Premise maps: none (root).
- Derivation certificate: enumerate divisors \(p^j\mid p^\nu\).
- Source/S2 anchor: ET pp. 25–26; S2 R1 L4.1.
- Definitions used: D-002, D-003, D-008.

### P-011 — legal-domain moment mean

Current construction binding: the exact `P011Statement` in the GroupA--GroupD source contracts, W0--W8, and the retained S7 provider. Any `mathminer-s3-legacy` block here is historical, not a proof.

```mathminer-s3-legacy
{"schema":"mathminer.s3/1","id":"P-011","kind":"PROPOSITION","binders":[{"key":"Y","type":{"set":"Real"}}],"uses_definitions":["D-006","D-008","D-S45-EXT001-DOMAIN","D-S45-MOMENT-FN","D-S45-P007-DOMAIN","D-S45-P008-C","D-S45-P008-DOMAIN","D-S45-P008-L","D-S45-P008-Q","D-S45-P010-DOMAIN","D-S45-P011-AMB-L","D-S45-P011-C","D-S45-P011-CLOC","D-S45-P011-DOMAIN","D-S45-P011-LAMBDA","D-S45-P011-MOM-L","D-S45-P011-MOMENT-MEAN","D-S45-P011-ROUGH-L","DP-MEAN::DP-MEAN-DEF-006","DP-MEAN::DP-MEAN-DEF-007","DP-MEAN::DP-MEAN-DEF-008"],"source_anchors":[],"hypotheses":[{"key":"domain","proposition":{"def":{"id":"D-S45-P011-DOMAIN","args":[{"var":"Y"}]}}}],"witnesses":[{"key":"C_Y","type":"Real","depends_on":["Y"]}],"conclusions":[{"key":"C_Y_positive","proposition":{"op":{"name":"gt","args":[{"var":"C_Y"},{"lit":{"type":"Real","value":"0"}}]}}},{"key":"legal_domain_moment_mean","proposition":{"def":{"id":"D-S45-P011-MOMENT-MEAN","args":[{"var":"Y"},{"var":"C_Y"}]}}}],"premises":[{"id":"local-values","producer":"P-010","closure_role":"REQUIRED","scope_binders":[{"key":"y","type":"Real"},{"key":"sigma","type":"Real"},{"key":"theta","type":"Real"},{"key":"u","type":"Real"}],"guards":[{"key":"local_domain","proposition":{"def":{"id":"D-S45-P010-DOMAIN","args":[{"var":"y"},{"var":"sigma"},{"var":"theta"},{"var":"u"}]}}}],"binder_map":{"y":{"var":"y"},"sigma":{"var":"sigma"},"theta":{"var":"theta"},"u":{"var":"u"}},"hypothesis_map":{"domain":{"guard":"local_domain"}},"witness_map":{},"consume":["moment_local_values"]},{"id":"mean-exists","producer":"A-S45-EXT001-EXISTS","closure_role":"REQUIRED","scope_binders":[{"key":"y","type":"Real"},{"key":"sigma","type":"Real"},{"key":"theta","type":"Real"},{"key":"u","type":"Real"},{"key":"x","type":"Real"}],"guards":[{"key":"ext_h_nonnegative_multiplicative","proposition":{"op":{"name":"and","args":[{"def":{"id":"DP-MEAN::DP-MEAN-DEF-006","args":[{"def":{"id":"D-S45-MOMENT-FN","args":[{"var":"y"},{"var":"sigma"},{"var":"theta"},{"var":"u"}]}}]}},{"def":{"id":"DP-MEAN::DP-MEAN-DEF-007","args":[{"def":{"id":"D-S45-MOMENT-FN","args":[{"var":"y"},{"var":"sigma"},{"var":"theta"},{"var":"u"}]}}]}}]}}},{"key":"ext_prime_power_geometric_bound","proposition":{"def":{"id":"DP-MEAN::DP-MEAN-DEF-008","args":[{"def":{"id":"D-S45-MOMENT-FN","args":[{"var":"y"},{"var":"sigma"},{"var":"theta"},{"var":"u"}]}},{"lit":{"type":"Real","value":"1"}},{"def":{"id":"D-S45-P011-LAMBDA","args":[{"var":"Y"}]}}]}}},{"key":"ext_lambda_1_nonnegative","proposition":{"op":{"name":"ge","args":[{"lit":{"type":"Real","value":"1"}},{"lit":{"type":"Real","value":"0"}}]}}},{"key":"ext_lambda_2_range","proposition":{"op":{"name":"and","args":[{"op":{"name":"ge","args":[{"def":{"id":"D-S45-P011-LAMBDA","args":[{"var":"Y"}]}},{"lit":{"type":"Real","value":"0"}}]}},{"op":{"name":"lt","args":[{"def":{"id":"D-S45-P011-LAMBDA","args":[{"var":"Y"}]}},{"lit":{"type":"Real","value":"2"}}]}}]}}},{"key":"ext_X_at_least_2","proposition":{"op":{"name":"ge","args":[{"var":"x"},{"lit":{"type":"Real","value":"2"}}]}}}],"binder_map":{"h":{"def":{"id":"D-S45-MOMENT-FN","args":[{"var":"y"},{"var":"sigma"},{"var":"theta"},{"var":"u"}]}},"lambda_1":{"lit":{"type":"Real","value":"1"}},"lambda_2":{"def":{"id":"D-S45-P011-LAMBDA","args":[{"var":"Y"}]}},"X":{"var":"x"}},"hypothesis_map":{"h_nonnegative_multiplicative":{"guard":"ext_h_nonnegative_multiplicative"},"prime_power_geometric_bound":{"guard":"ext_prime_power_geometric_bound"},"lambda_1_nonnegative":{"guard":"ext_lambda_1_nonnegative"},"lambda_2_range":{"guard":"ext_lambda_2_range"},"X_at_least_2":{"guard":"ext_X_at_least_2"}},"witness_map":{},"consume":["mean_bound_exists"]},{"id":"ambient","producer":"A-S45-P007-EXISTS","closure_role":"REQUIRED","guards":[{"key":"ambient_domain","proposition":{"def":{"id":"D-S45-P007-DOMAIN","args":[{"lit":{"type":"Real","value":"1"}},{"lit":{"type":"Real","value":"1"}},{"lit":{"type":"Real","value":"2"}},{"def":{"id":"D-S45-P011-AMB-L","args":[]}}]}}}],"binder_map":{"c":{"lit":{"type":"Real","value":"1"}},"eta":{"lit":{"type":"Real","value":"1"}},"C_err":{"lit":{"type":"Real","value":"2"}},"L":{"def":{"id":"D-S45-P011-AMB-L","args":[]}}},"hypothesis_map":{"domain":{"guard":"ambient_domain"}},"witness_map":{},"consume":["existentialized"]},{"id":"rough","producer":"A-S45-P007-EXISTS","closure_role":"REQUIRED","guards":[{"key":"rough_domain","proposition":{"def":{"id":"D-S45-P007-DOMAIN","args":[{"lit":{"type":"Real","value":"-1"}},{"lit":{"type":"Real","value":"1"}},{"lit":{"type":"Real","value":"1"}},{"def":{"id":"D-S45-P011-ROUGH-L","args":[]}}]}}}],"binder_map":{"c":{"lit":{"type":"Real","value":"-1"}},"eta":{"lit":{"type":"Real","value":"1"}},"C_err":{"lit":{"type":"Real","value":"1"}},"L":{"def":{"id":"D-S45-P011-ROUGH-L","args":[]}}},"hypothesis_map":{"domain":{"guard":"rough_domain"}},"witness_map":{},"consume":["existentialized"]},{"id":"moment-pointwise","producer":"A-S45-P007-EXISTS","closure_role":"REQUIRED","scope_binders":[{"key":"c","type":"Real"}],"guards":[{"key":"moment_domain","proposition":{"def":{"id":"D-S45-P007-DOMAIN","args":[{"var":"c"},{"lit":{"type":"Real","value":"1"}},{"def":{"id":"D-S45-P011-CLOC","args":[{"var":"Y"}]}},{"def":{"id":"D-S45-P011-MOM-L","args":[{"var":"Y"}]}}]}}}],"binder_map":{"c":{"var":"c"},"eta":{"lit":{"type":"Real","value":"1"}},"C_err":{"def":{"id":"D-S45-P011-CLOC","args":[{"var":"Y"}]}},"L":{"def":{"id":"D-S45-P011-MOM-L","args":[{"var":"Y"}]}}},"hypothesis_map":{"domain":{"guard":"moment_domain"}},"witness_map":{},"consume":["existentialized"]},{"id":"moment-family","producer":"A-S45-P008-EXISTS","closure_role":"REQUIRED","guards":[{"key":"family_domain","proposition":{"def":{"id":"D-S45-P008-DOMAIN","args":[{"type":{"named":{"id":"D-S45-P008-Q","args":[{"var":"Y"}]}}},{"lit":{"type":"Real","value":"-1/2"}},{"lit":{"type":"Real","value":"1/2"}},{"lit":{"type":"Real","value":"1"}},{"def":{"id":"D-S45-P011-CLOC","args":[{"var":"Y"}]}},{"lit":{"type":"Real","value":"2"}},{"lit":{"type":"Real","value":"1"}},{"lit":{"type":"Real","value":"1"}},{"def":{"id":"D-S45-P008-C","args":[{"var":"Y"}]}},{"def":{"id":"D-S45-P008-L","args":[{"var":"Y"}]}}]}}}],"binder_map":{"Q":{"type":{"named":{"id":"D-S45-P008-Q","args":[{"var":"Y"}]}}},"c_minus":{"lit":{"type":"Real","value":"-1/2"}},"c_plus":{"lit":{"type":"Real","value":"1/2"}},"eta_star":{"lit":{"type":"Real","value":"1"}},"C_err_star":{"def":{"id":"D-S45-P011-CLOC","args":[{"var":"Y"}]}},"P_0":{"lit":{"type":"Real","value":"2"}},"m_fin":{"lit":{"type":"Real","value":"1"}},"M_fin":{"lit":{"type":"Real","value":"1"}},"coeff":{"def":{"id":"D-S45-P008-C","args":[{"var":"Y"}]}},"local_factor":{"def":{"id":"D-S45-P008-L","args":[{"var":"Y"}]}}},"hypothesis_map":{"domain":{"guard":"family_domain"}},"witness_map":{},"consume":["existentialized"]}],"witness_realizations":{"C_Y":{"def":{"id":"D-S45-P011-C","args":[{"var":"Y"}]}}},"proof_ref":"### P-011 — legal-domain moment mean"}
```

- Prenex statement: for every nonempty compact \(Y\Subset(0,2)\), put
  \[
  \Lambda_Y:=\max(1,\sup Y)<2,\qquad
  C_Y^{\rm loc}:=4+{2\Lambda_Y^2\over2-\Lambda_Y}>0.
  \]
  There exists \(C_Y>0\) such that for all \(y\in Y\), all
  \(\sigma\ge\theta\ge2\), all \(\sigma<u\le x\), \(x\ge2\),
  \[
  \sum_{n<x}F_{y,u}(n)
  \le C_Yx\rho_\theta(\log u/\log\sigma)^{(y-1)/2}.
  \]
- Local equalities: none.
- Domain/range: no assertion for \(y<1,u>x\).
- Input subject: mean of D-008. Output: exact legal-domain bound.
- Premise maps:
  - `MAP-P011-P010`:

    | producer | slot | domain | consumer term | evidence |
    |---|---|---|---|---|
    | P-010 | `y` | \((0,2)\) | \(y\) | \(y\in Y\Subset(0,2)\) |
    | P-010 | `u` | \(>\sigma\) | \(u\) | P-011 hypothesis |
    | P-010 | `sigma` | \(\ge\theta\) | \(\sigma\) | P-011 hypothesis |
    | P-010 | `theta` | \(\ge2\) | \(\theta\) | P-011 hypothesis |
    | P-010 | `p` | prime | current \(p\) | Euler local index |
    | P-010 | `nu` | \(\mathbb N_{\ge1}\) | current \(\nu\) | Euler exponent |

    Conclusion/subject: literal D-008 prime-power local values; no adapter.
  - `MAP-P011-EXT001` with \(\Lambda_Y:=\max(1,\sup Y)<2\):

    | producer | slot | domain | consumer term | evidence |
    |---|---|---|---|---|
    | EXT-001 | `h` | nonnegative multiplicative | \(F_{y,u}\) | P-010 |
    | EXT-001 | `lambda_1` | \(\mathbb R_{\ge0}\) | \(1\) | local bound |
    | EXT-001 | `lambda_2` | \([0,2)\) | \(\Lambda_Y\) | compactness of \(Y\) |
    | EXT-001 | `X` | \(\mathbb R_{\ge2}\) | \(x\) | P-011 hypothesis |

    Producer hypothesis: P-010 gives
    \(0\le F_{y,u}(p^j)\le\Lambda_Y^j\).
    Consumed conclusion/subject: `SUB-P011-MEAN` is literally the D-008
    mean and `SUB-P011-EULER` its Euler product. Dependency order:
    fixed compact \(Y\) -> \(C_Y\) -> \(y,\theta,\sigma,u,x\).
  - `MAP-P011-P007-AMBIENT`: define, for every prime \(p\),
    \[
    L_p^{\rm amb}:=(1-1/p)^{-1},\qquad
    {\tt SUB-P011-AMBIENT}:=\prod_{2\le p<x}L_p^{\rm amb}.
    \]

    | producer | slot | domain | consumer term | evidence |
    |---|---|---|---|---|
    | P-007 | `c` | \(\mathbb R\) | \(1\) | exact first coefficient |
    | P-007 | `eta` | \(\mathbb R_{>0}\) | \(1\) | positive |
    | P-007 | `C_err` | \(\mathbb R_{>0}\) | \(2\) | global error bound below |
    | P-007 | `(L_p)` | positive prime family | \(L_p^{\rm amb}\) for every prime \(p\) | \(p\ge2\Rightarrow1-1/p>0\) |
    | P-007 | `A` | \(\mathbb R_{\ge2}\) | \(2\) | literal |
    | P-007 | `B` | \(\mathbb R_{\ge2}\) | \(x\) | P-011 hypothesis |

    This is a total P-007 map, not merely an asymptotic reference: for every
    prime \(p\),
    \[
    \left|L_p^{\rm amb}-(1+1/p)\right|
      ={1\over p(p-1)}\le 2p^{-2}.
    \]
    The consumed conclusion is the literal bound
    `SUB-P011-AMBIENT` \(\le C_{\rm amb}(\log x/\log2)\), including
    P-007's bounded-endpoint and empty-product branches.  The fixed
    \(\log2\) and the absolute \(C_{\rm amb}\) are absorbed before the
    displayed \(Y\)-family constant is selected.  This internal use of P-007
    is not a direct P-011 use of EXT-002.
  - `MAP-P011-P007-ROUGH`:

    | producer | slot | domain | consumer term | evidence |
    |---|---|---|---|---|
    | P-007 | `c` | \(\mathbb R\) | \(-1\) | exact factor |
    | P-007 | `eta` | \(>0\) | \(1\) | positive |
    | P-007 | `C_err` | \(>0\) | \(1\) | zero error is bounded by it |
    | P-007 | `(L_p)` | positive prime family | \(\widetilde L_p^{\rm rough}:=1-1/p\) for every prime \(p\) | positive exact model |
    | P-007 | `A` | \(\ge2\) | \(2\) | literal |
    | P-007 | `B` | \(\ge2\) | \(\theta\) | \(\theta\ge2\) |

    On the consumed interval \(2\le p<\theta\), P-010 gives
    \((1-1/p)\sum_{j\ge0}F_{y,u}(p^j)p^{-j}=1-1/p
    =\widetilde L_p^{\rm rough}\); outside that interval the global family is
    its exact model extension. Hence the P-007 error is zero for every prime.
    If \(\theta\le2\), P-007's empty-range branch is used.
  - `MAP-P011-P007-MOM`:

    | producer | slot | domain | consumer term | evidence |
    |---|---|---|---|---|
    | P-007 | `c` | \(\mathbb R\) | \((y-1)/2\) | exact first coefficient |
    | P-007 | `eta` | \(>0\) | \(1\) | positive |
    | P-007 | `C_err` | \(>0\) | \(C_Y^{\rm loc}\) | compact-local tail bound |
    | P-007 | `(L_p)` | positive prime family | \(\widetilde L_p^{\rm mom}\), equal to \((1-1/p)\sum_{j\ge0}F_{y,u}(p^j)p^{-j}\) on \(\sigma\le p<u\) and to \(1+(y-1)/(2p)\) outside | exact-model extension |
    | P-007 | `A` | \(\ge2\) | \(\sigma\) | \(\sigma\ge2\) |
    | P-007 | `B` | \(\ge2\) | \(u\) | \(u>\sigma\) |

    P-010's exact local values give, on \(\sigma\le p<u\),
    \(|\widetilde L_p^{\rm mom}-(1+(y-1)/(2p))|
    \le C_Y^{\rm loc}p^{-2}\); outside that interval the error is zero by
    definition of the extension.
    Indeed the \(j\ge2\) local tail is at most
    \(\sum_{j\ge2}(\Lambda_Y/p)^j\le
    \Lambda_Y^2p^{-2}/(1-\Lambda_Y/2)\), and the remaining normalization
    terms are covered by the added \(4\).
  - `MAP-P011-P008-MOM`: take
    \(Q_{Y}^{\rm mom}:=\{(q,S,U):q\in Y,\ 2\le S<U\}\),
    \(c_-:=-1/2,c_+:=1/2,\eta_*:=1,
    C_{\rm err,*}:=C_Y^{\rm loc},P_0:=2,
    m_{\rm fin}:=M_{\rm fin}:=1,c(q,S,U):=(q-1)/2\), and let
    \(L_{(q,S,U),p}\) be the exact-model extension just displayed, with
    \((y,\sigma,u):=(q,S,U)\). The finite-prefix hypothesis is vacuous.
    The error hypothesis holds for every prime, uniformly over
    \(Q_Y^{\rm mom}\). The P-008 uniform variables map as
    \((q,A,B):=((y,\sigma,u),\sigma,u)\). Its consumed conclusion is the
    family product estimate for the exact moment-factor subject; its constants
    depend on \(Y\) but precede the uniform \(y,\sigma,u\). This is the
    license for the \(C_Y\) order.

    | producer | slot | domain | consumer term | evidence |
    |---|---|---|---|---|
    | P-008 | `Q` | nonempty index set | \(Q_Y^{\rm mom}\) | \(Y\ne\varnothing\), and choose any \(2\le S<U\) |
    | P-008 | `c_-` | \(\mathbb R\) | \(-1/2\) | fixed compact lower endpoint |
    | P-008 | `c_+` | \(\mathbb R\), \(c_-\le c_+\), \(1+c_-/2>0\) | \(1/2\) | \(-1/2\le1/2\), \(3/4>0\) |
    | P-008 | `eta_*` | \(\mathbb R_{>0}\) | \(1\) | positive |
    | P-008 | `C_err,*` | \(\mathbb R_{>0}\) | \(C_Y^{\rm loc}\) | displayed positive family witness |
    | P-008 | `P_0` | \(\mathbb R_{\ge2}\) | \(2\) | literal |
    | P-008 | `m_fin` | \(\mathbb R_{>0}\) | \(1\) | prefix is empty |
    | P-008 | `M_fin` | \(\mathbb R_{\ge m_{\rm fin}}\) | \(1\) | prefix is empty |
    | P-008 | `c` | map into \([c_-,c_+]\) | \((q,S,U)\mapsto(q-1)/2\) | \(q\in Y\Subset(0,2)\) |
    | P-008 | `L` | positive local-factor family | exact-model family \(L_{(q,S,U),p}\) above | P-010 and the extension |
    | P-008 | `q` | \(Q_Y^{\rm mom}\) | \((y,\sigma,u)\) | P-011 binders |
    | P-008 | `A` | \(\mathbb R_{\ge2}\) | \(\sigma\) | P-011 domain |
    | P-008 | `B` | \(\mathbb R_{\ge2}\) | \(u\) | \(u>\sigma\) |
- Direct-map semantic fields: P-010 discharges all P-011 local-value
  hypotheses. The ambient P-007 map produces `SUB-P011-AMBIENT`; the rough
  P-007 map consumes its exact product comparison on the normalized rough
  factors; the moment P-007 map consumes its exact pointwise comparison,
  while P-008 supplies the uniform-family reduction.  The literal adapter is
  the equality
  \[
  \begin{aligned}
  {\tt SUB-P011-EULER}
  &=\prod_{p<x}\sum_{j\ge0}{F_{y,u}(p^j)\over p^j}\\
  &=\underbrace{\prod_{2\le p<x}(1-1/p)^{-1}}
       _{{\tt SUB-P011-AMBIENT}}
    \underbrace{\prod_{2\le p<\theta}(1-1/p)}
       _{{\tt SUB-P011-ROUGH}}\\
  &\quad\cdot
    \underbrace{\prod_{\sigma\le p<u}
       \left((1-1/p)\sum_{j\ge0}{F_{y,u}(p^j)\over p^j}\right)}
       _{{\tt SUB-P011-MOM}}
    \cdot\underbrace{\prod_{\theta\le p<\sigma}1
      \prod_{u\le p<x}1}_{{\tt SUB-P011-ZERO}} .
  \tag{AD-P011-EULER-SPLIT}
  \end{aligned}
  \]
  P-010 proves this prime by prime in its four exact ranges, including all
  empty ranges.  Thus the adapter names every produced subject and no
  cancellation is hidden in prose.  Constants map exactly as
  \[
  Y\longmapsto(\Lambda_Y,C_Y^{\rm loc})\longmapsto C_Y
    \longmapsto(y,\theta,\sigma,u,x),
  \]
  with the absolute ambient comparison absorbed inside \(C_Y\); producer
  uniform variables \((A,B)\) become the displayed literal endpoints.
- Derivation certificate: insert the four factors from
  (AD-P011-EULER-SPLIT) into the EXT-001 bound.  The produced ambient estimate
  cancels the denominator \(\log x\) up to its fixed \(\log2\) constant, the
  rough product is \(\rho_\theta\), and the moment product gives the stated
  logarithmic quotient.
- Source/S2 anchor: ET (3), pp. 25–26; S2 R2.1.
- Definitions used: D-006, D-008.

### P-012 — upper divisor tail

Current construction binding: the exact `P012Statement` in the GroupA--GroupD source contracts, W0--W8, and the retained S7 provider. Any `mathminer-s3-legacy` block here is historical, not a proof.

```mathminer-s3-legacy
{"schema":"mathminer.s3/1","id":"P-012","kind":"PROPOSITION","binders":[{"key":"y","type":"Real"}],"uses_definitions":["D-002","D-003","D-006","D-008","D-S45-P011-DOMAIN","D-S45-P011-YPLUS","D-S45-P012-C","D-S45-P012-DOMAIN","D-S45-P012-MEAN","D-S45-P012-POINTWISE"],"source_anchors":[],"hypotheses":[{"key":"domain","proposition":{"def":{"id":"D-S45-P012-DOMAIN","args":[{"var":"y"}]}}}],"witnesses":[{"key":"C_y","type":"Real","depends_on":["y"]}],"conclusions":[{"key":"C_y_positive","proposition":{"op":{"name":"gt","args":[{"var":"C_y"},{"lit":{"type":"Real","value":"0"}}]}}},{"key":"pointwise_tail","proposition":{"def":{"id":"D-S45-P012-POINTWISE","args":[{"var":"y"}]}}},{"key":"mean_tail","proposition":{"def":{"id":"D-S45-P012-MEAN","args":[{"var":"y"},{"var":"C_y"}]}}}],"premises":[{"id":"moment-mean","producer":"A-S45-P011-EXISTS","closure_role":"REQUIRED","guards":[{"key":"interval_domain","proposition":{"def":{"id":"D-S45-P011-DOMAIN","args":[{"def":{"id":"D-S45-P011-YPLUS","args":[{"var":"y"}]}}]}}}],"binder_map":{"Y":{"def":{"id":"D-S45-P011-YPLUS","args":[{"var":"y"}]}}},"hypothesis_map":{"domain":{"guard":"interval_domain"}},"witness_map":{},"consume":["existentialized"]}],"witness_realizations":{"C_y":{"def":{"id":"D-S45-P012-C","args":[{"var":"y"}]}}},"proof_ref":"### P-012 — upper divisor tail"}
```

- Prenex statement: for every \(1<y<2\), every
  \(\sigma\ge\theta\ge2\), every \(\sigma<u\le x\), put
  \(R=\log u/\log\sigma>1\). For every \(n>0\),
  \[
  {\chi(n,\theta)\over\tau(n,\sigma)}
  \#\{d\mid n:\chi(d,\sigma)=1,\
  \Omega(d,u)>(y/2)\log R\}
  \le F_{y,u}(n)R^{-(y/2)\log y},
  \]
  and there exists \(C_y>0\), before the uniform variables
  \(\sigma,\theta,u,x\), such that its sum over \(n<x\) is at most
  \(C_yx\rho_\theta R^{(y-1-y\log y)/2}\).
- Local equalities: \(R=\log u/\log\sigma\).
- Domain/range: pointwise subject explicitly binds \(n\).
- Input subject: exact counted divisor set. Output: pointwise and mean bound.
- Premise maps:
  - `MAP-P012-P011`:

    | producer slot | consumer term | domain evidence |
    |---|---|---|
    | `Y` | \([(1+y)/2,(2+y)/2]\) | compact nonempty subset of \((0,2)\) containing \(y\) |
    | `y` | \(y\) | \(1<y<2\) |
    | `sigma` | \(\sigma\) | \(\sigma\ge\theta\ge2\) |
    | `theta` | \(\theta\) | same |
    | `u` | \(u\) | \(\sigma<u\le x\) |
    | `x` | \(x\) | \(x\ge2\) |

    Hypotheses: \(\sigma<u\le x\).
    Consumed: mean of \(F_{y,u}\). Subject: literal right side after summing
    the pointwise inequality. Constants: \(C_Y\) specializes to \(C_y\),
    uniform in \(\sigma,\theta,u,x,n\).
- Derivation certificate: Markov for increasing \(m\mapsto y^m\), then P-011.
- Source/S2 anchor: ET p. 26; S2 R2.2+.
- Definitions used: D-002, D-003, D-006, D-008.

### P-013 — lower divisor tail

Current construction binding: the exact `P013Statement` in the GroupA--GroupD source contracts, W0--W8, and the retained S7 provider. Any `mathminer-s3-legacy` block here is historical, not a proof.

```mathminer-s3-legacy
{"schema":"mathminer.s3/1","id":"P-013","kind":"PROPOSITION","binders":[{"key":"y","type":"Real"}],"uses_definitions":["D-002","D-003","D-006","D-008","D-S45-P011-DOMAIN","D-S45-P011-YMINUS","D-S45-P013-C","D-S45-P013-DOMAIN","D-S45-P013-MEAN","D-S45-P013-POINTWISE"],"source_anchors":[],"hypotheses":[{"key":"domain","proposition":{"def":{"id":"D-S45-P013-DOMAIN","args":[{"var":"y"}]}}}],"witnesses":[{"key":"C_y","type":"Real","depends_on":["y"]}],"conclusions":[{"key":"C_y_positive","proposition":{"op":{"name":"gt","args":[{"var":"C_y"},{"lit":{"type":"Real","value":"0"}}]}}},{"key":"pointwise_tail","proposition":{"def":{"id":"D-S45-P013-POINTWISE","args":[{"var":"y"}]}}},{"key":"mean_tail","proposition":{"def":{"id":"D-S45-P013-MEAN","args":[{"var":"y"},{"var":"C_y"}]}}}],"premises":[{"id":"moment-mean","producer":"A-S45-P011-EXISTS","closure_role":"REQUIRED","guards":[{"key":"interval_domain","proposition":{"def":{"id":"D-S45-P011-DOMAIN","args":[{"def":{"id":"D-S45-P011-YMINUS","args":[{"var":"y"}]}}]}}}],"binder_map":{"Y":{"def":{"id":"D-S45-P011-YMINUS","args":[{"var":"y"}]}}},"hypothesis_map":{"domain":{"guard":"interval_domain"}},"witness_map":{},"consume":["existentialized"]}],"witness_realizations":{"C_y":{"def":{"id":"D-S45-P013-C","args":[{"var":"y"}]}}},"proof_ref":"### P-013 — lower divisor tail"}
```

- Prenex statement: for every \(0<y<1\), every
  \(\sigma\ge\theta\ge2\), every \(\sigma<u\le x\), put
  \(R=\log u/\log\sigma>1\). For every \(n>0\),
  \[
  {\chi(n,\theta)\over\tau(n,\sigma)}
  \#\{d\mid n:\chi(d,\sigma)=1,\
  \Omega(d,u)<(y/2)\log R\}
  \le F_{y,u}(n)R^{-(y/2)\log y},
  \]
  and there exists \(C_y>0\), before the uniform variables, such that its
  sum over \(n<x\) is at most
  \(C_yx\rho_\theta R^{(y-1-y\log y)/2}\).
- Local equalities: \(R=\log u/\log\sigma\).
- Domain/range: pointwise subject explicitly binds \(n\).
- Input subject: exact counted divisor set. Output: pointwise and mean bound.
- Premise maps:
  - `MAP-P013-P011`:

    | producer slot | consumer term | domain evidence |
    |---|---|---|
    | `Y` | \([y/2,(1+y)/2]\) | compact nonempty subset of \((0,2)\) containing \(y\) |
    | `y` | \(y\) | \(0<y<1\) |
    | `sigma` | \(\sigma\) | \(\sigma\ge\theta\ge2\) |
    | `theta` | \(\theta\) | same |
    | `u` | \(u\) | \(\sigma<u\le x\) |
    | `x` | \(x\) | \(x\ge2\) |

    Hypotheses: legal domain.
    Consumed: mean of \(F_{y,u}\). Subject: literal summed right side.
    Constants: \(C_Y\mapsto C_y\), uniform in all displayed variables.
- Derivation certificate: Markov for decreasing \(m\mapsto y^m\), then P-011.
- Source/S2 anchor: ET p. 26; S2 R2.2−.
- Definitions used: D-002, D-003, D-006, D-008.

### P-014 — plus numerical certificate

```mathminer-s3
{"schema":"mathminer.s3/1","id":"P-014","kind":"PROPOSITION","binders":[{"key":"epsilon_int","type":"Real"}],"uses_definitions":["D-S45-EPS-DOMAIN","D-S45-P014-NUMERICAL"],"source_anchors":[],"hypotheses":[{"key":"domain","proposition":{"def":{"id":"D-S45-EPS-DOMAIN","args":[{"var":"epsilon_int"}]}}}],"witnesses":[],"conclusions":[{"key":"numerical_exponent_bound","proposition":{"def":{"id":"D-S45-P014-NUMERICAL","args":[{"var":"epsilon_int"}]}}}],"premises":[],"witness_realizations":{},"proof_ref":"### P-014 — plus numerical certificate"}
```

- Prenex statement: \(\forall\varepsilon_{\rm int}\in(0,1/10]\), put
  \(t=1.96\varepsilon_{\rm int}\); then
  \(t-(1+t)\log(1+t)\le-1.802\varepsilon_{\rm int}^2\).
- Local equalities: \(t=1.96\varepsilon_{\rm int}\).
- Domain/range: \(0<t\le0.196\).
- Input subject: plus Chernoff exponent. Output: numerical upper bound.
- Premise maps: none (root).
- Derivation certificate: monotonic quotient checked at \(t=0.196\), with
  six-term alternating lower bound giving coefficient \(>1.8061\).
- Source/S2 anchor: ET (4), p. 26; S2 R1 (2.6), S2B R1.
- Definitions used: none.

### P-015 — minus numerical certificate

```mathminer-s3
{"schema":"mathminer.s3/1","id":"P-015","kind":"PROPOSITION","binders":[{"key":"epsilon_int","type":"Real"}],"uses_definitions":["D-S45-EPS-DOMAIN","D-S45-P015-NUMERICAL"],"source_anchors":[],"hypotheses":[{"key":"domain","proposition":{"def":{"id":"D-S45-EPS-DOMAIN","args":[{"var":"epsilon_int"}]}}}],"witnesses":[],"conclusions":[{"key":"numerical_exponent_bound","proposition":{"def":{"id":"D-S45-P015-NUMERICAL","args":[{"var":"epsilon_int"}]}}}],"premises":[],"witness_realizations":{},"proof_ref":"### P-015 — minus numerical certificate"}
```

- Prenex statement: \(\forall\varepsilon_{\rm int}\in(0,1/10]\), put
  \(t=1.96\varepsilon_{\rm int}\); then
  \(-t-(1-t)\log(1-t)\le-1.802\varepsilon_{\rm int}^2\).
- Local equalities: \(t=1.96\varepsilon_{\rm int}\).
- Domain/range: \(0<t<1\).
- Input subject: minus Chernoff exponent. Output: numerical upper bound.
- Premise maps: none (root).
- Derivation certificate:
  \((1-t)\log(1-t)+t\ge t^2/2=1.9208\varepsilon_{\rm int}^2\).
- Source/S2 anchor: ET (4), p. 26; S2 R1 (2.6), S2B R1.
- Definitions used: none.

### P-016 — uniform sampled-grid constant

Current construction binding: the exact `P016Statement` in the GroupA--GroupD source contracts, W0--W8, and the retained S7 provider. Any `mathminer-s3-legacy` block here is historical, not a proof.

```mathminer-s3-legacy
{"schema":"mathminer.s3/1","id":"P-016","kind":"PROPOSITION","binders":[{"key":"epsilon_int","type":"Real"}],"uses_definitions":["D-006","D-009","D-S45-EPS-DOMAIN","D-S45-P012-DOMAIN","D-S45-P013-DOMAIN","D-S45-P016-C","D-S45-P016-GRID-BOUND","D-S45-P016-YMINUS","D-S45-P016-YPLUS"],"source_anchors":[],"hypotheses":[{"key":"domain","proposition":{"def":{"id":"D-S45-EPS-DOMAIN","args":[{"var":"epsilon_int"}]}}}],"witnesses":[{"key":"C_grid","type":"Real","depends_on":["epsilon_int"]}],"conclusions":[{"key":"C_grid_positive","proposition":{"op":{"name":"gt","args":[{"var":"C_grid"},{"lit":{"type":"Real","value":"0"}}]}}},{"key":"grid_bound","proposition":{"def":{"id":"D-S45-P016-GRID-BOUND","args":[{"var":"epsilon_int"},{"var":"C_grid"}]}}}],"premises":[{"id":"upper-tail","producer":"A-S45-P012-EXISTS","closure_role":"REQUIRED","guards":[{"key":"upper_domain","proposition":{"def":{"id":"D-S45-P012-DOMAIN","args":[{"def":{"id":"D-S45-P016-YPLUS","args":[{"var":"epsilon_int"}]}}]}}}],"binder_map":{"y":{"def":{"id":"D-S45-P016-YPLUS","args":[{"var":"epsilon_int"}]}}},"hypothesis_map":{"domain":{"guard":"upper_domain"}},"witness_map":{},"consume":["existentialized"]},{"id":"lower-tail","producer":"A-S45-P013-EXISTS","closure_role":"REQUIRED","guards":[{"key":"lower_domain","proposition":{"def":{"id":"D-S45-P013-DOMAIN","args":[{"def":{"id":"D-S45-P016-YMINUS","args":[{"var":"epsilon_int"}]}}]}}}],"binder_map":{"y":{"def":{"id":"D-S45-P016-YMINUS","args":[{"var":"epsilon_int"}]}}},"hypothesis_map":{"domain":{"guard":"lower_domain"}},"witness_map":{},"consume":["existentialized"]},{"id":"plus-exponent","producer":"P-014","closure_role":"REQUIRED","binder_map":{"epsilon_int":{"var":"epsilon_int"}},"hypothesis_map":{"domain":{"hypothesis":"domain"}},"witness_map":{},"consume":["numerical_exponent_bound"]},{"id":"minus-exponent","producer":"P-015","closure_role":"REQUIRED","binder_map":{"epsilon_int":{"var":"epsilon_int"}},"hypothesis_map":{"domain":{"hypothesis":"domain"}},"witness_map":{},"consume":["numerical_exponent_bound"]}],"witness_realizations":{"C_grid":{"def":{"id":"D-S45-P016-C","args":[{"var":"epsilon_int"}]}}},"proof_ref":"### P-016 — uniform sampled-grid constant"}
```

- Prenex statement:
  \[
  \forall\varepsilon_{\rm int}\in(0,1/10]\;
  \exists C_{\rm grid}>0:\ {\rm GridBound}
  (\varepsilon_{\rm int},C_{\rm grid}).
  \]
- Local equalities: D-009 supplies
  \(u_j,\Lambda_\sigma,E_x^{\rm term},U_0\).
- Domain/range: \(C_{\rm grid}\) is chosen before
  \(\xi,\sigma,\theta,x,n,d,u,j\), so it is uniform in all of them.
- Input subject: the two tail means at every legal sample.
  Output subject: exact GridBound predicate.
- Premise maps:
  - `MAP-P016-P012-GRID`: slots
    \(y:=1+1.96\varepsilon_{\rm int},\sigma:=\sigma,
    \theta:=\theta,u:=u_j,x:=x,n:=n\); domain evidence is
    \(1<y<2\), \(\sigma<u_j<x\), and the D-009 grid definition. The
    consumed subject is exactly
    \(\Lambda_\sigma(d,u_j)>0.98\varepsilon_{\rm int}\).
  - `MAP-P016-P012-TERMINAL`: the same complete slots with \(u:=x\).
    Domain evidence is \(\sigma<x\) and \(u=x\le x\). The consumed subject
    is exactly the one-sided terminal event
    \(\Lambda_\sigma(d,x)>0.98\varepsilon_{\rm int}\).
  - `MAP-P016-P013-GRID`: slots
    \(y:=1-1.96\varepsilon_{\rm int},\sigma:=\sigma,
    \theta:=\theta,u:=u_j,x:=x,n:=n\); domain evidence is
    \(0<y<1\) and \(\sigma<u_j<x\). The consumed subject is exactly
    \(\Lambda_\sigma(d,u_j)<-0.98\varepsilon_{\rm int}\). There is no
    P-013 application at \(u=x\).
  - P-014 — Binders:
    \(\varepsilon_{\rm int}:=\varepsilon_{\rm int}\).
    Hypotheses: domain. Consumed: plus exponent. Subject: P-012 exponent.
    Constants: none.
  - P-015 — Binders:
    \(\varepsilon_{\rm int}:=\varepsilon_{\rm int}\).
    Hypotheses: domain. Consumed: minus exponent. Subject: P-013 exponent.
    Constants: none.
- Exact subject equality: the literal union of the three preceding producer
  subjects is exactly `SUB-E-TERM`, the predicate
  \(E_x^{\rm term}(d)\) in D-009, including strict inequalities and the
  one-sided terminal sample.
- Derivation certificate: substitute
  \(\log u_j/\log\sigma=\mathrm e^j\log\xi\), sum the geometric series,
  and add the legal endpoint \(u=x\).
- Source/S2 anchor: ET pp. 26–27; S2 R1 (2.7)–(2.8), R2.2.
- Definitions used: D-006, D-009.

### P-017 — threshold witness

```mathminer-s3
{"schema":"mathminer.s3/1","id":"P-017","kind":"PROPOSITION","binders":[{"key":"epsilon_int","type":"Real"},{"key":"C_grid","type":"Real"}],"uses_definitions":["D-009","D-S45-EPS-DOMAIN","D-S45-P017-THRESHOLD","D-S45-P017-XI0"],"source_anchors":[],"hypotheses":[{"key":"epsilon_domain","proposition":{"def":{"id":"D-S45-EPS-DOMAIN","args":[{"var":"epsilon_int"}]}}},{"key":"C_grid_positive","proposition":{"op":{"name":"gt","args":[{"var":"C_grid"},{"lit":{"type":"Real","value":"0"}}]}}}],"witnesses":[{"key":"Xi_0","type":"Real","depends_on":["epsilon_int","C_grid"]}],"conclusions":[{"key":"Xi_0_gt_one","proposition":{"op":{"name":"gt","args":[{"var":"Xi_0"},{"lit":{"type":"Real","value":"1"}}]}}},{"key":"threshold_spec","proposition":{"def":{"id":"D-S45-P017-THRESHOLD","args":[{"var":"epsilon_int"},{"var":"C_grid"},{"var":"Xi_0"}]}}}],"premises":[],"witness_realizations":{"Xi_0":{"def":{"id":"D-S45-P017-XI0","args":[{"var":"epsilon_int"},{"var":"C_grid"}]}}},"proof_ref":"### P-017 — threshold witness"}
```

- Prenex statement:
  \[
  \forall\varepsilon_{\rm int}\in(0,1/10]\;
  \forall C_{\rm grid}>0\;
  \exists\Xi_0>1:\ {\rm ThresholdSpec}
  (\varepsilon_{\rm int},C_{\rm grid},\Xi_0).
  \]
- Local equalities: ThresholdSpec is D-009.
- Domain/range: \(\Xi_0\) depends only on
  \((\varepsilon_{\rm int},C_{\rm grid})\), before \(\xi\).
- Input subject: two scalar smallness requirements. Output: one threshold.
- Premise maps: none (root).
- Derivation certificate: both
  \(1/\log\log\xi\) and
  \(10C_{\rm grid}(\log\xi)^{-0.001\varepsilon_{\rm int}^2}\)
  tend to zero; enlarge the threshold to force \(\xi>\mathrm e\).
- Source/S2 anchor: ET pp. 26–27; S2 R1 §2.4, R2.2.
- Definitions used: D-009.

### P-018 — all-\(u\) bad-divisor mean

Current construction binding: the exact `P018Statement` in the GroupA--GroupD source contracts, W0--W8, and the retained S7 provider. Any `mathminer-s3-legacy` block here is historical, not a proof.

```mathminer-s3-legacy
{"schema":"mathminer.s3/1","id":"P-018","kind":"PROPOSITION","binders":[{"key":"epsilon_int","type":"Real"}],"uses_definitions":["D-003","D-006","D-007","D-009","D-S45-EPS-DOMAIN","D-S45-P016-GRID-BOUND","D-S45-P017-THRESHOLD","D-S45-P018-BAD-MEAN"],"source_anchors":[],"hypotheses":[{"key":"domain","proposition":{"def":{"id":"D-S45-EPS-DOMAIN","args":[{"var":"epsilon_int"}]}}}],"witnesses":[{"key":"C_grid","type":"Real","depends_on":["epsilon_int"]},{"key":"Xi_0","type":"Real","depends_on":["epsilon_int"]}],"conclusions":[{"key":"C_grid_positive","proposition":{"op":{"name":"gt","args":[{"var":"C_grid"},{"lit":{"type":"Real","value":"0"}}]}}},{"key":"Xi_0_gt_one","proposition":{"op":{"name":"gt","args":[{"var":"Xi_0"},{"lit":{"type":"Real","value":"1"}}]}}},{"key":"grid_bound","proposition":{"def":{"id":"D-S45-P016-GRID-BOUND","args":[{"var":"epsilon_int"},{"var":"C_grid"}]}}},{"key":"threshold_spec","proposition":{"def":{"id":"D-S45-P017-THRESHOLD","args":[{"var":"epsilon_int"},{"var":"C_grid"},{"var":"Xi_0"}]}}},{"key":"bad_divisor_mean","proposition":{"def":{"id":"D-S45-P018-BAD-MEAN","args":[{"var":"epsilon_int"},{"var":"C_grid"},{"var":"Xi_0"}]}}}],"premises":[{"id":"grid","producer":"P-016","closure_role":"REQUIRED","binder_map":{"epsilon_int":{"var":"epsilon_int"}},"hypothesis_map":{"domain":{"hypothesis":"domain"}},"witness_map":{"C_grid":"received_C_grid"},"consume":["C_grid_positive","grid_bound"]},{"id":"threshold","producer":"P-017","closure_role":"REQUIRED","binder_map":{"epsilon_int":{"var":"epsilon_int"},"C_grid":{"var":"received_C_grid"}},"hypothesis_map":{"epsilon_domain":{"hypothesis":"domain"},"C_grid_positive":{"premise":"grid","conclusion":"C_grid_positive"}},"witness_map":{"Xi_0":"received_Xi_0"},"consume":["Xi_0_gt_one","threshold_spec"]}],"witness_realizations":{"C_grid":{"var":"received_C_grid"},"Xi_0":{"var":"received_Xi_0"}},"proof_ref":"### P-018 — all-\\(u\\) bad-divisor mean"}
```

- Prenex statement:
  \[
  \forall\varepsilon_{\rm int}\in(0,1/10]\;
  \exists C_{\rm grid}>0\;\exists\Xi_0>1\;
  \forall\xi\ge\Xi_0\;\forall\sigma\ge\theta\ge2\;\forall x>U_0,
  \]
  \[
  \sum_{n<x}{\chi(n,\theta)\over\tau(n,\sigma)}
  \#\{d\mid n:\chi(d,\sigma)=1\land
  \neg{\rm Good}(n,d;\varepsilon_{\rm int},\xi,\sigma)\}
  \le {1\over10}x\rho_\theta
  (\log\xi)^{-0.9\varepsilon_{\rm int}^2}.
  \]
- Local equalities: \(U_0\) is D-007; the grid cell is the unique
  \(j\) with \(u_j\le u<u_{j+1}\).
- Domain/range: every moment endpoint is \(\le x\); the last cell uses \(x\).
- Input subject: exact all-\(u\) bad-divisor mass. Output: exact mean bound.
- Premise maps:
  - P-016 — Binders:
    \(\varepsilon_{\rm int}:=\varepsilon_{\rm int}\); choose its
    \(C_{\rm grid}\). Hypotheses: domain. Consumed: GridBound.
    Subject: sampled exceptional mass is D-009 exactly. Constants:
    \(C_{\rm grid}\) is not changed.
  - P-017 — Binders:
    \(\varepsilon_{\rm int}:=\varepsilon_{\rm int},
    C_{\rm grid}:=C_{\rm grid}\);
    choose its \(\Xi_0\). Hypotheses: positivity and the P-016 witness.
    Consumed: ThresholdSpec. Subject: exact numerical
    inequalities. Constants: threshold identity.
- Derivation certificate: for every \(U_0\le u<n<x\), use the unique cell.
  Ordinary cells use \(u_j,u_{j+1}<x\); the terminal cell uses \(u_j,x\).
  Monotonicity of \(\Omega\) and center displacement at most one converts
  \(0.98\varepsilon_{\rm int}\) to \(\varepsilon_{\rm int}\);
  ThresholdSpec absorbs \(10C_{\rm grid}\).
- Source/S2 anchor: ET p. 27; S2 R2.2 and S2B R2(1).
- Definitions used: D-003, D-006, D-007, D-009.

### P-019 — exact rough-number density

```mathminer-s3
{"schema":"mathminer.s3/1","id":"P-019","kind":"PROPOSITION","binders":[{"key":"theta","type":"Real"}],"uses_definitions":["D-002","D-006","D-S45-P019-DOMAIN","D-S45-P019-ROUGH-DENSITY"],"source_anchors":[],"hypotheses":[{"key":"domain","proposition":{"def":{"id":"D-S45-P019-DOMAIN","args":[{"var":"theta"}]}}}],"witnesses":[],"conclusions":[{"key":"exact_rough_density","proposition":{"def":{"id":"D-S45-P019-ROUGH-DENSITY","args":[{"var":"theta"}]}}}],"premises":[],"witness_realizations":{},"proof_ref":"### P-019 — exact rough-number density"}
```

- Prenex statement: \(\forall\theta\ge2\), the set
  \(R_\theta=\{n>0:\chi(n,\theta)=1\}\) has density \(\rho_\theta\).
- Local equalities: \(Q_\theta=\prod_{p<\theta}p\).
- Domain/range: finite prime product.
- Input subject: rough-number set. Output: exact natural density.
- Premise maps: none (root).
- Derivation certificate: periodic inclusion–exclusion modulo \(Q_\theta\);
  exactly \(\prod_{p<\theta}(p-1)\) residue classes are allowed.
- Source/S2 anchor: ET Lemma 4(ii); S2 E3.
- Definitions used: D-002, D-006.

### P-020 — combined Lemma-4 witness theorem

Current construction binding: the exact `P020Statement` in the GroupA--GroupD source contracts, W0--W8, and the retained S7 provider. Any `mathminer-s3-legacy` block here is historical, not a proof.

```mathminer-s3-legacy
{"schema":"mathminer.s3/1","id":"P-020","kind":"PROPOSITION","binders":[{"key":"epsilon_int","type":"Real"},{"key":"xi","type":"Real"},{"key":"sigma","type":"Real"},{"key":"theta","type":"Real"}],"uses_definitions":["D-002","D-006","D-007","D-009","D-010","D-S45-EPS-DOMAIN","D-S45-P019-DOMAIN","D-S45-P020-A","D-S45-P020-DOMAIN","D-S45-P020-L4SPEC"],"source_anchors":[],"hypotheses":[{"key":"domain","proposition":{"def":{"id":"D-S45-P020-DOMAIN","args":[{"var":"epsilon_int"},{"var":"xi"},{"var":"sigma"},{"var":"theta"}]}}},{"key":"epsilon_domain","proposition":{"def":{"id":"D-S45-EPS-DOMAIN","args":[{"var":"epsilon_int"}]}}}],"witnesses":[{"key":"C_grid","type":"Real","depends_on":["epsilon_int"]},{"key":"Xi_0","type":"Real","depends_on":["epsilon_int"]},{"key":"A","type":{"set":"Nat"},"depends_on":["epsilon_int","xi","sigma","theta"]}],"conclusions":[{"key":"lemma4_witness","proposition":{"def":{"id":"D-S45-P020-L4SPEC","args":[{"var":"epsilon_int"},{"var":"xi"},{"var":"sigma"},{"var":"theta"},{"var":"C_grid"},{"var":"Xi_0"},{"var":"A"}]}}}],"premises":[{"id":"bad-mean","producer":"P-018","closure_role":"REQUIRED","binder_map":{"epsilon_int":{"var":"epsilon_int"}},"hypothesis_map":{"domain":{"hypothesis":"epsilon_domain"}},"witness_map":{"C_grid":"p020_C_grid","Xi_0":"p020_Xi_0"},"consume":["C_grid_positive","Xi_0_gt_one","grid_bound","threshold_spec","bad_divisor_mean"]},{"id":"rough-density","producer":"P-019","closure_role":"REQUIRED","guards":[{"key":"theta_domain","proposition":{"def":{"id":"D-S45-P019-DOMAIN","args":[{"var":"theta"}]}}}],"binder_map":{"theta":{"var":"theta"}},"hypothesis_map":{"domain":{"guard":"theta_domain"}},"witness_map":{},"consume":["exact_rough_density"]}],"witness_realizations":{"C_grid":{"var":"p020_C_grid"},"Xi_0":{"var":"p020_Xi_0"},"A":{"def":{"id":"D-S45-P020-A","args":[{"var":"epsilon_int"},{"var":"xi"},{"var":"sigma"},{"var":"theta"},{"var":"p020_C_grid"},{"var":"p020_Xi_0"}]}}},"proof_ref":"### P-020 — combined Lemma-4 witness theorem"}
```

- Prenex statement:
  \[
  \forall\varepsilon_{\rm int}\in(0,1/10]\;
  \exists C_{\rm grid}>0\;\exists\Xi_0>1\;
  \forall\xi\ge\Xi_0\;\forall\sigma\ge\theta\ge2\;
  \exists\mathcal A\subseteq\mathbb N_{>0}:\quad
  {\rm L4Spec}(\varepsilon_{\rm int},\xi,\sigma,\theta,\mathcal A).
  \]
- Local equalities: no hidden threshold function; every witness is in the
  displayed prefix.
- Domain/range: \(C_{\rm grid},\Xi_0\) precede
  \(\xi,\sigma,\theta,\mathcal A\).
- Input subject: sampled tail estimates, interpolation, rough density.
  Output subject: exact L4Spec witness.
- Premise maps:
  - P-018 — Binders:
    \(\varepsilon_{\rm int}:=\varepsilon_{\rm int}\); select its
    \(C_{\rm grid},\Xi_0\), then map
    \(\xi:=\xi,\sigma:=\sigma,\theta:=\theta,x:=x\).
    Hypotheses: \(\xi\ge\Xi_0\), \(\sigma\ge\theta\ge2\), \(x>U_0\).
    Consumed: all-\(u\) bad-divisor mean with its GridBound and ThresholdSpec
    witnesses. Subject: bad divisor is exactly
    negation of D-007 Good. Constants: exponent weakens from \(0.901\) to
    \(0.9\) inside ThresholdSpec, uniformly in \(x\).
  - P-019 — Binders: \(\theta:=\theta\). Hypotheses: \(\theta\ge2\).
    Consumed: density \(\rho_\theta\). Subject: the rough ambient set in
    L4Spec. Constants: exact.
- Derivation certificate: Markov at bad proportion \(1/10\), subtract the
  resulting upper density from P-019, discard the finite \(n\le U_0\) set,
  and define \(\mathcal A\) as the remaining rough integers.
- Source/S2 anchor: ET Lemma 4, pp. 25–27; S2 R1 §2, R2.2.
- Definitions used: D-002, D-006, D-007, D-009, D-010.

## 6. Proposition 1 and Proposition 2

The following support definitions give typed names to the exact analytic
predicates stated in this section.  Their bodies are notation declarations;
the proposition records below retain the proof obligations and premise maps.

```mathminer-s3
{"schema":"mathminer.s3/1","id":"S-P-030","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"},{"key":"k","type":"Nat"},{"key":"d","type":"Nat"},{"key":"d_prime","type":"Nat"}],"uses_definitions":["D-005"],"source_anchors":[],"result_type":{"tuple":["Prop","Prop"]},"body":"Component 0 is theta>1, d,d'>0, d!=d', and theta^k<=d,d'<theta^(k+1). Component 1 is Close_theta(d,d')."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"S-P-031","kind":"DEFINITION","binders":[{"key":"epsilon_int","type":"Real"},{"key":"xi","type":"Real"},{"key":"sigma","type":"Real"},{"key":"theta","type":"Real"},{"key":"A","type":{"set":"Nat"}},{"key":"n","type":"Nat"}],"uses_definitions":["D-004","D-007","D-010","D-011"],"source_anchors":[],"result_type":{"tuple":["Prop","Prop","Prop"]},"body":"Component 0 is the exact domain epsilon_int in (0,1/10], xi>1, sigma>=theta>=2, L4Spec(epsilon_int,xi,sigma,theta,A), and n in A. Component 1 is the three occupied-bin identities for the D-011 data. Component 2 is r<=tau^+(n,theta)."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"S-P-032","kind":"DEFINITION","binders":[{"key":"epsilon_int","type":"Real"},{"key":"xi","type":"Real"},{"key":"sigma","type":"Real"},{"key":"theta","type":"Real"},{"key":"A","type":{"set":"Nat"}},{"key":"n","type":"Nat"}],"uses_definitions":["D-002","D-005","D-007","D-010","D-011","D-012"],"source_anchors":[],"result_type":"Prop","body":"For the exact D-011 data, Q(n)>=sum_i nu_i(nu_i-1) and (9/10)tau(n,sigma)<=sum_i nu_i<=tau(n,sigma), with ordered distinct pairs and the literal D-012 Q-subject."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"S-P-033","kind":"DEFINITION","binders":[{"key":"r","type":"Nat"},{"key":"nu","type":{"fn":{"args":["Nat"],"return":"Real"}}}],"uses_definitions":[],"source_anchors":[],"result_type":{"tuple":["Prop","Prop"]},"body":"Component 0 is r>=1 and nu_i>=0 for 1<=i<=r. Component 1 is (sum_{i=1}^r nu_i)^2 <= r sum_{i=1}^r nu_i^2."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"S-P-034","kind":"DEFINITION","binders":[{"key":"epsilon_int","type":"Real"},{"key":"xi","type":"Real"},{"key":"sigma","type":"Real"},{"key":"theta","type":"Real"},{"key":"A","type":{"set":"Nat"}},{"key":"n","type":"Nat"}],"uses_definitions":["D-002","D-004","D-010","D-011","D-012"],"source_anchors":[],"result_type":"Prop","body":"The exact Proposition-1 inequality (4/5) tau(n,sigma)/tau^+(n,theta) <= 1 + Q(n)/tau(n,sigma), for the D-011 count vector and D-012 Q."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"S-P-040","kind":"DEFINITION","binders":[{"key":"n","type":"Nat"},{"key":"D","type":"Nat"},{"key":"D_prime","type":"Nat"},{"key":"theta","type":"Real"},{"key":"t","type":"Nat"},{"key":"d","type":"Nat"},{"key":"d_prime","type":"Nat"}],"uses_definitions":["D-005"],"source_anchors":[],"result_type":{"tuple":["Prop","Prop"]},"body":"Component 0 is n,D,D'>0, theta>1, D,D' divide n, Close_theta(D,D'), t=gcd(D,D'), d=D/t, d'=D'/t. Component 1 is gcd(d,d')=1, dd't divides n, Close_theta(d,d'), the ordered multiplicity-preserving inverse (d,d',t)->(dt,d't), and for every real-valued W on positive integers W(D)=W(dt)."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"S-P-041","kind":"DEFINITION","binders":[{"key":"n","type":"Nat"},{"key":"D","type":"Nat"},{"key":"D_prime","type":"Nat"},{"key":"t","type":"Nat"},{"key":"d","type":"Nat"},{"key":"d_prime","type":"Nat"},{"key":"sigma","type":"Real"},{"key":"theta","type":"Real"}],"uses_definitions":["D-002","D-005","D-017"],"source_anchors":[],"result_type":{"tuple":["Prop","Prop"]},"body":"Component 0 is sigma>=theta>=2 together with chi(n,theta)=1 and chi(dt,sigma)=1. Component 1 is d>1, chi(d,sigma)=1, d>=sigma, and for the unique k with theta^k<=d<theta^(k+1), k>=floor(log sigma/log theta)>=(1/2)log sigma/log theta."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"S-P-042","kind":"DEFINITION","binders":[{"key":"epsilon_int","type":"Real"},{"key":"xi","type":"Real"},{"key":"sigma","type":"Real"},{"key":"theta","type":"Real"},{"key":"y","type":"Real"},{"key":"n","type":"Nat"},{"key":"m","type":"Nat"},{"key":"k","type":"Nat"}],"uses_definitions":["D-003","D-007"],"source_anchors":[],"result_type":{"tuple":["Prop","Prop"]},"body":"Component 0 is the exact P-042 domain and high-bin assumptions: epsilon_int in (0,1/10], xi>1, sigma>=theta>=2, y in (0,1), n>U0, m|n, k>=1, Good(n,m), k>=(log sigma/log theta)log xi, and theta^k<=m. Component 1 is 1 <= (2k log xi log theta/log sigma)^(-(1/2+epsilon_int)log y) y^Omega(m,theta^k)."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"S-P-043","kind":"DEFINITION","binders":[{"key":"epsilon_int","type":"Real"},{"key":"xi","type":"Real"},{"key":"sigma","type":"Real"},{"key":"theta","type":"Real"},{"key":"y","type":"Real"},{"key":"n","type":"Nat"},{"key":"m","type":"Nat"},{"key":"k","type":"Nat"}],"uses_definitions":["D-003","D-007"],"source_anchors":[],"result_type":{"tuple":["Prop","Prop"]},"body":"Component 0 is the exact P-043 domain and low-bin assumptions: epsilon_int in (0,1/10], xi>1, sigma>=theta>=2, y in (0,1), n>U0, m|n, k>=1, Good(n,m), and (1/2)log sigma/log theta <= k < (log sigma/log theta)log xi. Component 1 is the same pointwise power bound as P-042."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"S-P-044","kind":"DEFINITION","binders":[{"key":"epsilon_int","type":"Real"},{"key":"xi","type":"Real"},{"key":"sigma","type":"Real"},{"key":"theta","type":"Real"},{"key":"y","type":"Real"},{"key":"n","type":"Nat"}],"uses_definitions":["D-005","D-007","D-012","D-013","D-017"],"source_anchors":[],"result_type":{"tuple":["Prop","Prop"]},"body":"Component 0 is epsilon_int in (0,1/10], xi>1, sigma>=theta>=2, y in (0,1), and n>U0. Component 1 is f(n) <= (2 log xi log theta/log sigma)^(-(1/2+epsilon_int)log y) sum_{k>=K0(sigma,theta)} k^(-(1/2+epsilon_int)log y) f_k#(y,n), with the exact D-012 and D-013 subjects."}
```

### P-030 — same-bin closeness

```mathminer-s3
{"schema":"mathminer.s3/1","id":"P-030","kind":"PROPOSITION","binders":[{"key":"theta","type":"Real"},{"key":"k","type":"Nat"},{"key":"d","type":"Nat"},{"key":"d_prime","type":"Nat"}],"uses_definitions":["D-005","S-P-030"],"source_anchors":[],"hypotheses":[{"key":"same_bin_data","proposition":{"proj":{"value":{"def":{"id":"S-P-030","args":[{"var":"theta"},{"var":"k"},{"var":"d"},{"var":"d_prime"}]}},"index":0}}}],"witnesses":[],"conclusions":[{"key":"close","proposition":{"proj":{"value":{"def":{"id":"S-P-030","args":[{"var":"theta"},{"var":"k"},{"var":"d"},{"var":"d_prime"}]}},"index":1}}}],"premises":[],"witness_realizations":{},"proof_ref":"### P-030 — same-bin closeness"}
```

- Prenex statement: for every \(\theta>1\), \(k\in\mathbb N\), and distinct
  \(d,d'>0\), if
  \(\theta^k\le d,d'<\theta^{k+1}\), then
  \({\rm Close}_\theta(d,d')\).
- Local equalities: none.
- Domain/range: strict ratio conclusion.
- Input subject: two distinct divisors in one half-open bin.
  Output subject: D-005.
- Premise maps: none (root).
- Derivation certificate: divide the two endpoint inequalities in both orders.
- Source/S2 anchor: ET p. 28; S2 R1 §3.
- Definitions used: D-005.

### P-031 — occupied-bin identities

```mathminer-s3
{"schema":"mathminer.s3/1","id":"P-031","kind":"PROPOSITION","binders":[{"key":"epsilon_int","type":"Real"},{"key":"xi","type":"Real"},{"key":"sigma","type":"Real"},{"key":"theta","type":"Real"},{"key":"A","type":{"set":"Nat"}},{"key":"n","type":"Nat"}],"uses_definitions":["D-004","D-007","D-010","D-011","S-P-031"],"source_anchors":[],"hypotheses":[{"key":"l4_member","proposition":{"proj":{"value":{"def":{"id":"S-P-031","args":[{"var":"epsilon_int"},{"var":"xi"},{"var":"sigma"},{"var":"theta"},{"var":"A"},{"var":"n"}]}},"index":0}}}],"witnesses":[],"conclusions":[{"key":"occupied_identities","proposition":{"proj":{"value":{"def":{"id":"S-P-031","args":[{"var":"epsilon_int"},{"var":"xi"},{"var":"sigma"},{"var":"theta"},{"var":"A"},{"var":"n"}]}},"index":1}}},{"key":"occupied_bound","proposition":{"proj":{"value":{"def":{"id":"S-P-031","args":[{"var":"epsilon_int"},{"var":"xi"},{"var":"sigma"},{"var":"theta"},{"var":"A"},{"var":"n"}]}},"index":2}}}],"premises":[],"witness_realizations":{},"proof_ref":"### P-031 — occupied-bin identities"}
```

- Prenex statement: for every
  \(\varepsilon_{\rm int}\in(0,1/10]\), \(\xi>1\),
  \(\sigma\ge\theta\ge2\), \(\mathcal A\subseteq\mathbb N_{>0}\)
  satisfying L4Spec\((\varepsilon_{\rm int},\xi,\sigma,\theta,\mathcal A)\),
  and every \(n\in\mathcal A\), with
  \(\nu_{n,\mathcal A},I_{n,\mathcal A},r,k_1,\ldots,k_r\) defined by D-011,
  \[
  r=\#I_{n,\mathcal A},\quad
  I_{n,\mathcal A}=\{k_1<\cdots<k_r\},\quad
  \sum_{i=1}^r\nu_{n,\mathcal A}(k_i)
  =\sum_{d\mid n}\chi(d,\sigma)\chi_n^*(d),
  \]
  and \(r\le\tau^+(n,\theta)\).
- Local equalities: \(\nu,I,r,k_i\) are exactly D-011.
- Domain/range: finite support because \(d\mid n\).
- Input subject: exact occupied good-bin enumeration.
  Output subject: sum identity and occupied-bin inequality.
- Premise maps: none (root; L4Spec is a local predicate assumption).
- Derivation certificate: disjoint exhaustive half-open bins partition the
  good divisors; each occupied good bin is an occupied divisor bin.
- Source/S2 anchor: ET p. 28; S2 R1 §3.
- Definitions used: D-004, D-007, D-010, D-011.

### P-032 — ordered same-bin pair count

```mathminer-s3
{"schema":"mathminer.s3/1","id":"P-032","kind":"PROPOSITION","binders":[{"key":"epsilon_int","type":"Real"},{"key":"xi","type":"Real"},{"key":"sigma","type":"Real"},{"key":"theta","type":"Real"},{"key":"A","type":{"set":"Nat"}},{"key":"n","type":"Nat"}],"uses_definitions":["D-002","D-005","D-007","D-010","D-011","D-012","S-P-030","S-P-031","S-P-032"],"source_anchors":[],"hypotheses":[{"key":"l4_member","proposition":{"proj":{"value":{"def":{"id":"S-P-031","args":[{"var":"epsilon_int"},{"var":"xi"},{"var":"sigma"},{"var":"theta"},{"var":"A"},{"var":"n"}]}},"index":0}}}],"witnesses":[],"conclusions":[{"key":"pair_mass_bounds","proposition":{"def":{"id":"S-P-032","args":[{"var":"epsilon_int"},{"var":"xi"},{"var":"sigma"},{"var":"theta"},{"var":"A"},{"var":"n"}]}}}],"premises":[{"id":"MAP-P032-P030","producer":"P-030","closure_role":"REQUIRED","scope_binders":[{"key":"i_scope","type":"Nat"},{"key":"d_scope","type":"Nat"},{"key":"d_prime_scope","type":"Nat"}],"guards":[{"key":"same_bin_scope","proposition":{"proj":{"value":{"def":{"id":"S-P-030","args":[{"var":"theta"},{"app":{"fn":{"proj":{"value":{"def":{"id":"D-011","args":[{"var":"epsilon_int"},{"var":"xi"},{"var":"sigma"},{"var":"theta"},{"var":"A"},{"var":"n"},{"lit":{"type":"Nat","value":"0"}}]}},"index":3}},"args":[{"var":"i_scope"}]}},{"var":"d_scope"},{"var":"d_prime_scope"}]}},"index":0}}}],"binder_map":{"theta":{"var":"theta"},"k":{"app":{"fn":{"proj":{"value":{"def":{"id":"D-011","args":[{"var":"epsilon_int"},{"var":"xi"},{"var":"sigma"},{"var":"theta"},{"var":"A"},{"var":"n"},{"lit":{"type":"Nat","value":"0"}}]}},"index":3}},"args":[{"var":"i_scope"}]}},"d":{"var":"d_scope"},"d_prime":{"var":"d_prime_scope"}},"hypothesis_map":{"same_bin_data":{"guard":"same_bin_scope"}},"witness_map":{},"consume":["close"]},{"id":"MAP-P032-P031","producer":"P-031","closure_role":"REQUIRED","binder_map":{"epsilon_int":{"var":"epsilon_int"},"xi":{"var":"xi"},"sigma":{"var":"sigma"},"theta":{"var":"theta"},"A":{"var":"A"},"n":{"var":"n"}},"hypothesis_map":{"l4_member":{"hypothesis":"l4_member"}},"witness_map":{},"consume":["occupied_identities","occupied_bound"]}],"witness_realizations":{},"proof_ref":"### P-032 — ordered same-bin pair count"}
```

- Prenex statement: for every
  \(\varepsilon_{\rm int}\in(0,1/10]\), \(\xi>1\),
  \(\sigma\ge\theta\ge2\), \(\mathcal A\subseteq\mathbb N_{>0}\)
  satisfying L4Spec\((\varepsilon_{\rm int},\xi,\sigma,\theta,\mathcal A)\),
  every \(n\in\mathcal A\), and the exact
  \(\nu_{n,\mathcal A},I_{n,\mathcal A},r,k_1,\ldots,k_r\) of D-011,
  \[
  Q(n)\ge\sum_{i=1}^r
  \nu_{n,\mathcal A}(k_i)
  \bigl(\nu_{n,\mathcal A}(k_i)-1\bigr),
  \]
  and
  \[
  {9\over10}\tau(n,\sigma)
  \le\sum_{i=1}^r\nu_{n,\mathcal A}(k_i)
  \le\tau(n,\sigma).
  \]
- Local equalities: the \(i\)-th local count is
  \(\nu_i:=\nu_{n,\mathcal A}(k_i)\).
- Domain/range: ordered distinct pairs; asymmetric Q-weight is one because
  the first member is good.
- Input subject: D-011 counts. Output subject: exact pair and mass bounds.
- Premise maps:
  - P-030 — Binders:
    \(\theta:=\theta,k:=k_i,d:=d,d':=d'\) for each ordered distinct pair
    counted in bin \(k_i\). Hypotheses: D-011 membership supplies both
    half-open inequalities and distinctness is the pair index.
    Consumed: Close predicate. Subject: exact D-005 restriction in Q.
    Constants: none.
  - P-031 — Binders:
    \(\varepsilon_{\rm int}:=\varepsilon_{\rm int},\xi:=\xi,
    \sigma:=\sigma,\theta:=\theta,\mathcal A:=\mathcal A,n:=n,
    \nu_{n,\mathcal A}:=\nu_{n,\mathcal A},
    I_{n,\mathcal A}:=I_{n,\mathcal A},r:=r,k_i:=k_i\).
    Hypotheses: L4Spec and \(n\in\mathcal A\).
    Consumed: sum identity and \(r\le\tau^+\). Subject: literal D-011 data.
    Constants: none.
- Derivation certificate: count ordered distinct pairs within each occupied
  good bin; use L4Spec clause 3 and inclusion among all rough divisors.
- Source/S2 anchor: ET Proposition 1, p. 28; S2 R1 (3.1).
- Definitions used: D-002, D-005, D-007, D-010, D-011, D-012.

### P-033 — Cauchy inequality with explicit instantiation

```mathminer-s3
{"schema":"mathminer.s3/1","id":"P-033","kind":"PROPOSITION","binders":[{"key":"r","type":"Nat"},{"key":"nu","type":{"fn":{"args":["Nat"],"return":"Real"}}}],"uses_definitions":["S-P-033"],"source_anchors":[],"hypotheses":[{"key":"vector_domain","proposition":{"proj":{"value":{"def":{"id":"S-P-033","args":[{"var":"r"},{"var":"nu"}]}},"index":0}}}],"witnesses":[],"conclusions":[{"key":"cauchy","proposition":{"proj":{"value":{"def":{"id":"S-P-033","args":[{"var":"r"},{"var":"nu"}]}},"index":1}}}],"premises":[],"witness_realizations":{},"proof_ref":"### P-033 — Cauchy inequality with explicit instantiation"}
```

- Prenex statement:
  \[
  \forall r\in\mathbb N_{\ge1}\;
  \forall\nu:\{1,\ldots,r\}\to\mathbb R_{\ge0},
  \]
  \[
  (\sum_{i=1}^r\nu_i)^2\le r\sum_{i=1}^r\nu_i^2.
  \]
- Local equalities: none.
- Domain/range: finite real vectors.
- Input subject: the typed finite vector \(\nu\). Output: scalar inequality.
- Premise maps: none (root).
- Derivation certificate: Cauchy–Schwarz with the all-ones vector.
- Source/S2 anchor: ET p. 28; S2 R1 §3.
- Definitions used: none.

### P-034 — Proposition 1

```mathminer-s3
{"schema":"mathminer.s3/1","id":"P-034","kind":"PROPOSITION","binders":[{"key":"epsilon_int","type":"Real"},{"key":"xi","type":"Real"},{"key":"sigma","type":"Real"},{"key":"theta","type":"Real"},{"key":"A","type":{"set":"Nat"}},{"key":"n","type":"Nat"}],"uses_definitions":["D-002","D-004","D-010","D-011","D-012","S-P-031","S-P-033","S-P-034"],"source_anchors":[],"hypotheses":[{"key":"l4_member","proposition":{"proj":{"value":{"def":{"id":"S-P-031","args":[{"var":"epsilon_int"},{"var":"xi"},{"var":"sigma"},{"var":"theta"},{"var":"A"},{"var":"n"}]}},"index":0}}}],"witnesses":[],"conclusions":[{"key":"proposition_1","proposition":{"def":{"id":"S-P-034","args":[{"var":"epsilon_int"},{"var":"xi"},{"var":"sigma"},{"var":"theta"},{"var":"A"},{"var":"n"}]}}}],"premises":[{"id":"MAP-P034-P032","producer":"P-032","closure_role":"REQUIRED","binder_map":{"epsilon_int":{"var":"epsilon_int"},"xi":{"var":"xi"},"sigma":{"var":"sigma"},"theta":{"var":"theta"},"A":{"var":"A"},"n":{"var":"n"}},"hypothesis_map":{"l4_member":{"hypothesis":"l4_member"}},"witness_map":{},"consume":["pair_mass_bounds"]},{"id":"MAP-P034-P033","producer":"P-033","closure_role":"REQUIRED","guards":[{"key":"count_vector_domain","proposition":{"proj":{"value":{"def":{"id":"S-P-033","args":[{"proj":{"value":{"def":{"id":"D-011","args":[{"var":"epsilon_int"},{"var":"xi"},{"var":"sigma"},{"var":"theta"},{"var":"A"},{"var":"n"},{"lit":{"type":"Nat","value":"0"}}]}},"index":2}},{"lambda":{"binders":[{"key":"i_vec","type":"Nat"}],"body":{"cast":{"value":{"app":{"fn":{"proj":{"value":{"def":{"id":"D-011","args":[{"var":"epsilon_int"},{"var":"xi"},{"var":"sigma"},{"var":"theta"},{"var":"A"},{"var":"n"},{"lit":{"type":"Nat","value":"0"}}]}},"index":0}},"args":[{"app":{"fn":{"proj":{"value":{"def":{"id":"D-011","args":[{"var":"epsilon_int"},{"var":"xi"},{"var":"sigma"},{"var":"theta"},{"var":"A"},{"var":"n"},{"lit":{"type":"Nat","value":"0"}}]}},"index":3}},"args":[{"var":"i_vec"}]}}]}},"to":"Real"}}}}]}},"index":0}}}],"binder_map":{"r":{"proj":{"value":{"def":{"id":"D-011","args":[{"var":"epsilon_int"},{"var":"xi"},{"var":"sigma"},{"var":"theta"},{"var":"A"},{"var":"n"},{"lit":{"type":"Nat","value":"0"}}]}},"index":2}},"nu":{"lambda":{"binders":[{"key":"i_vec_map","type":"Nat"}],"body":{"cast":{"value":{"app":{"fn":{"proj":{"value":{"def":{"id":"D-011","args":[{"var":"epsilon_int"},{"var":"xi"},{"var":"sigma"},{"var":"theta"},{"var":"A"},{"var":"n"},{"lit":{"type":"Nat","value":"0"}}]}},"index":0}},"args":[{"app":{"fn":{"proj":{"value":{"def":{"id":"D-011","args":[{"var":"epsilon_int"},{"var":"xi"},{"var":"sigma"},{"var":"theta"},{"var":"A"},{"var":"n"},{"lit":{"type":"Nat","value":"0"}}]}},"index":3}},"args":[{"var":"i_vec_map"}]}}]}},"to":"Real"}}}}},"hypothesis_map":{"vector_domain":{"guard":"count_vector_domain"}},"witness_map":{},"consume":["cauchy"]}],"witness_realizations":{},"proof_ref":"### P-034 — Proposition 1"}
```

- Prenex statement: for every
  \(\varepsilon_{\rm int}\in(0,1/10]\), \(\xi>1\),
  \(\sigma\ge\theta\ge2\), every \(\mathcal A\) satisfying L4Spec, and every
  \(n\in\mathcal A\),
  \[
  {4\over5}{\tau(n,\sigma)\over\tau^+(n,\theta)}
  \le1+{Q(n)\over\tau(n,\sigma)}.
  \]
- Local equalities: \(\nu_i:=\nu_{n,\mathcal A}(k_i)\),
  \(r:=\#I_{n,\mathcal A}\).
- Domain/range: divisor counts are positive.
- Input subject: exact D-011 count vector and D-012 Q.
  Output subject: Proposition-1 inequality.
- Premise maps:
  - P-032 — Binders:
    \(\varepsilon_{\rm int}:=\varepsilon_{\rm int},\xi:=\xi,
    \sigma:=\sigma,\theta:=\theta,\mathcal A:=\mathcal A,n:=n,
    \nu_{n,\mathcal A}:=\nu_{n,\mathcal A},
    I_{n,\mathcal A}:=I_{n,\mathcal A},r:=r,k_i:=k_i\).
    Hypotheses: L4Spec and membership. Consumed: pair and mass bounds.
    Subject: Q and count vector literally D-011/D-012. Constants: none.
  - P-033 — Binders:
    \(r:=\operatorname{card}(I_{n,\mathcal A})\in\mathbb N_{\ge1}\),
    \(\nu(i):=\nu_{n,\mathcal A}(k_i)\in\mathbb R_{\ge0}\) for
    \(i\in\{1,\ldots,r\}\).
    Hypotheses: nonnegativity from cardinalities; if \(r=0\), L4Spec's
    positive rough-divisor mass contradicts it, so \(r\ge1\).
    Consumed: Cauchy inequality. Subject: exact occupied count vector.
    Constants: none.
- Derivation certificate:
  \(Q+\tau(n,\sigma)\ge\sum_i\nu_i^2\); combine with Cauchy and
  \((9/10)^2\ge4/5\), then divide by positive counts.
- Source/S2 anchor: ET Proposition 1, p. 28; S2 R1 P1.
- Definitions used: D-002, D-004, D-010, D-011, D-012.

### P-040 — gcd reindexing transformation result

```mathminer-s3
{"schema":"mathminer.s3/1","id":"P-040","kind":"PROPOSITION","binders":[{"key":"n","type":"Nat"},{"key":"D","type":"Nat"},{"key":"D_prime","type":"Nat"},{"key":"theta","type":"Real"},{"key":"t","type":"Nat"},{"key":"d","type":"Nat"},{"key":"d_prime","type":"Nat"}],"uses_definitions":["D-005","S-P-040"],"source_anchors":[],"hypotheses":[{"key":"reindex_input","proposition":{"proj":{"value":{"def":{"id":"S-P-040","args":[{"var":"n"},{"var":"D"},{"var":"D_prime"},{"var":"theta"},{"var":"t"},{"var":"d"},{"var":"d_prime"}]}},"index":0}}}],"witnesses":[],"conclusions":[{"key":"reindex_result","proposition":{"proj":{"value":{"def":{"id":"S-P-040","args":[{"var":"n"},{"var":"D"},{"var":"D_prime"},{"var":"theta"},{"var":"t"},{"var":"d"},{"var":"d_prime"}]}},"index":1}}}],"premises":[],"witness_realizations":{},"proof_ref":"### P-040 — gcd reindexing transformation result"}
```

- Prenex statement: for every \(n,D,D'>0\), every real \(\theta>1\), if
  \(D,D'\mid n\) and \({\rm Close}_\theta(D,D')\), put
  \[
  t=\gcd(D,D'),\qquad d=D/t,\qquad d'=D'/t.
  \]
  Then \(\gcd(d,d')=1\), \(dd't\mid n\),
  \({\rm Close}_\theta(d,d')\), and the inverse
  \((d,d',t)\mapsto(dt,d't)\) is an ordered multiplicity-preserving
  bijection. For every function \(W\) on positive integers,
  \(W(D)=W(dt)\).
- Local equalities: all three defining equations.
- Domain/range: original and reduced divisors are positive integers.
- Input subject: ordered close divisor pair \((D,D')\).
  Output subject: exact coprime triple \((d,d',t)\).
- Premise maps: none (root transformation-result proposition).
- Derivation certificate: prime valuations show the divisibility equivalence;
  division by a common positive factor preserves ratio, strictness, order,
  distinctness, and multiplicity.
- Source/S2 anchor: ET p. 29; S2 R1 (4.1).
- Definitions used: D-005.

### P-041 — rough reduced divisor and exact index

```mathminer-s3
{"schema":"mathminer.s3/1","id":"P-041","kind":"PROPOSITION","binders":[{"key":"n","type":"Nat"},{"key":"D","type":"Nat"},{"key":"D_prime","type":"Nat"},{"key":"t","type":"Nat"},{"key":"d","type":"Nat"},{"key":"d_prime","type":"Nat"},{"key":"sigma","type":"Real"},{"key":"theta","type":"Real"}],"uses_definitions":["D-002","D-005","D-017","S-P-040","S-P-041"],"source_anchors":[],"hypotheses":[{"key":"reindex_input","proposition":{"proj":{"value":{"def":{"id":"S-P-040","args":[{"var":"n"},{"var":"D"},{"var":"D_prime"},{"var":"theta"},{"var":"t"},{"var":"d"},{"var":"d_prime"}]}},"index":0}}},{"key":"rough_input","proposition":{"proj":{"value":{"def":{"id":"S-P-041","args":[{"var":"n"},{"var":"D"},{"var":"D_prime"},{"var":"t"},{"var":"d"},{"var":"d_prime"},{"var":"sigma"},{"var":"theta"}]}},"index":0}}}],"witnesses":[],"conclusions":[{"key":"rough_index","proposition":{"proj":{"value":{"def":{"id":"S-P-041","args":[{"var":"n"},{"var":"D"},{"var":"D_prime"},{"var":"t"},{"var":"d"},{"var":"d_prime"},{"var":"sigma"},{"var":"theta"}]}},"index":1}}}],"premises":[{"id":"MAP-P041-P040","producer":"P-040","closure_role":"REQUIRED","binder_map":{"n":{"var":"n"},"D":{"var":"D"},"D_prime":{"var":"D_prime"},"theta":{"var":"theta"},"t":{"var":"t"},"d":{"var":"d"},"d_prime":{"var":"d_prime"}},"hypothesis_map":{"reindex_input":{"hypothesis":"reindex_input"}},"witness_map":{},"consume":["reindex_result"]}],"witness_realizations":{},"proof_ref":"### P-041 — rough reduced divisor and exact index"}
```

- Prenex statement: for every
  \(n,D,D',t,d,d'>0\), \(\sigma\ge\theta\ge2\), with
  \[
  D,D'\mid n,\quad {\rm Close}_\theta(D,D'),\quad
  t=\gcd(D,D'),\quad d=D/t,\quad d'=D'/t,
  \]
  if \(\chi(n,\theta)=1\) and \(\chi(dt,\sigma)=1\), then \(d>1\),
  \(\chi(d,\sigma)=1\), \(d\ge\sigma\); for the unique integer \(k\ge0\)
  with \(\theta^k\le d<\theta^{k+1}\),
  \[
  k\ge\lfloor\log\sigma/\log\theta\rfloor
  \ge\tfrac12\log\sigma/\log\theta.
  \]
- Local equalities: every gcd/reduction equation is in the prefix.
- Domain/range: unique half-open bin.
- Input subject: P-040 triple plus roughness. Output: exact lower index.
- Premise maps:
  - P-040 — Binders:
    \(n:=n,D:=D,D':=D',\theta:=\theta,t:=t,d:=d,d':=d'\).
    Hypotheses:
    divisor, close, and defining equations are consumer facts.
    Consumed: coprimality, \(dd't\mid n\), inverse, ratio preservation.
    Subject: literal reduced divisor \(d\). Constants: none.
- Derivation certificate: roughness descends from \(dt\) to \(d\); \(d=1\)
  would give \(1<d'<\theta\), impossible for a nontrivial divisor of a
  \(\theta\)-rough \(n\). Apply the half-open logarithmic partition and
  \(\lfloor r\rfloor\ge r/2\) for \(r\ge1\).
- Source/S2 anchor: ET p. 29; S2 R1 §4, R2.3.
- Definitions used: D-002, D-005, D-017.

### P-042 — high-bin good-divisor power bound

```mathminer-s3
{"schema":"mathminer.s3/1","id":"P-042","kind":"PROPOSITION","binders":[{"key":"epsilon_int","type":"Real"},{"key":"xi","type":"Real"},{"key":"sigma","type":"Real"},{"key":"theta","type":"Real"},{"key":"y","type":"Real"},{"key":"n","type":"Nat"},{"key":"m","type":"Nat"},{"key":"k","type":"Nat"}],"uses_definitions":["D-003","D-007","S-P-042"],"source_anchors":[],"hypotheses":[{"key":"high_bin_input","proposition":{"proj":{"value":{"def":{"id":"S-P-042","args":[{"var":"epsilon_int"},{"var":"xi"},{"var":"sigma"},{"var":"theta"},{"var":"y"},{"var":"n"},{"var":"m"},{"var":"k"}]}},"index":0}}}],"witnesses":[],"conclusions":[{"key":"power_bound","proposition":{"proj":{"value":{"def":{"id":"S-P-042","args":[{"var":"epsilon_int"},{"var":"xi"},{"var":"sigma"},{"var":"theta"},{"var":"y"},{"var":"n"},{"var":"m"},{"var":"k"}]}},"index":1}}}],"premises":[],"witness_realizations":{},"proof_ref":"### P-042 — high-bin good-divisor power bound"}
```

- Prenex statement: for every
  \(\varepsilon_{\rm int}\in(0,1/10]\), \(\xi>1\),
  \(\sigma\ge\theta\ge2\), \(y\in(0,1)\), \(n>U_0\), \(m\mid n\),
  integer \(k\ge1\), put \(q=1/2+\varepsilon_{\rm int}\). If
  Good\((n,m;\varepsilon_{\rm int},\xi,\sigma)\),
  \(k\ge(\log\sigma/\log\theta)\log\xi\), and \(\theta^k\le m\), then
  \[
  1\le
  (2k\log\xi\log\theta/\log\sigma)^{-q\log y}
  y^{\Omega(m,\theta^k)}.
  \]
- Local equalities: \(U_0\) is D-007; \(q=1/2+\varepsilon_{\rm int}\).
- Domain/range: equality \(\theta^k=n\) is covered by the strict prime cutoff.
- Input subject: ambient good divisor. Output: exact power bound.
- Premise maps: none (root).
- Derivation certificate: evaluate Good at \(\theta^k<n\), or take
  \(u\uparrow n\) if \(\theta^k=n\); use decreasing \(y^r\).
- Source/S2 anchor: ET (7), p. 29; S2 R1 (4.3), R2.3.
- Definitions used: D-003, D-007.

### P-043 — low-bin good-divisor power bound

```mathminer-s3
{"schema":"mathminer.s3/1","id":"P-043","kind":"PROPOSITION","binders":[{"key":"epsilon_int","type":"Real"},{"key":"xi","type":"Real"},{"key":"sigma","type":"Real"},{"key":"theta","type":"Real"},{"key":"y","type":"Real"},{"key":"n","type":"Nat"},{"key":"m","type":"Nat"},{"key":"k","type":"Nat"}],"uses_definitions":["D-003","D-007","S-P-043"],"source_anchors":[],"hypotheses":[{"key":"low_bin_input","proposition":{"proj":{"value":{"def":{"id":"S-P-043","args":[{"var":"epsilon_int"},{"var":"xi"},{"var":"sigma"},{"var":"theta"},{"var":"y"},{"var":"n"},{"var":"m"},{"var":"k"}]}},"index":0}}}],"witnesses":[],"conclusions":[{"key":"power_bound","proposition":{"proj":{"value":{"def":{"id":"S-P-043","args":[{"var":"epsilon_int"},{"var":"xi"},{"var":"sigma"},{"var":"theta"},{"var":"y"},{"var":"n"},{"var":"m"},{"var":"k"}]}},"index":1}}}],"premises":[],"witness_realizations":{},"proof_ref":"### P-043 — low-bin good-divisor power bound"}
```

- Prenex statement: for every
  \(\varepsilon_{\rm int}\in(0,1/10]\), \(\xi>1\),
  \(\sigma\ge\theta\ge2\), \(y\in(0,1)\), \(n>U_0\), \(m\mid n\),
  integer \(k\ge1\), put \(q=1/2+\varepsilon_{\rm int}\). If
  Good\((n,m;\varepsilon_{\rm int},\xi,\sigma)\) and
  \[
  \tfrac12{\log\sigma\over\log\theta}\le k<
  {\log\sigma\over\log\theta}\log\xi,
  \]
  then the same conclusion as P-042 holds.
- Local equalities: \(U_0,q\) exactly as P-042.
- Domain/range: \(U_0<n\).
- Input subject: ambient good divisor at the low bin. Output: same exact bound.
- Premise maps: none (root).
- Derivation certificate:
  \(\Omega(m,\theta^k)\le\Omega(m,U_0)\le q\log\log\xi\), and
  \(2k\log\theta/\log\sigma\ge1\).
- Source/S2 anchor: ET (7), p. 29; S2 R1 (4.3), R2.3.
- Definitions used: D-003, D-007.

### P-044 — Proposition 2

```mathminer-s3
{"schema":"mathminer.s3/1","id":"P-044","kind":"PROPOSITION","binders":[{"key":"epsilon_int","type":"Real"},{"key":"xi","type":"Real"},{"key":"sigma","type":"Real"},{"key":"theta","type":"Real"},{"key":"y","type":"Real"},{"key":"n","type":"Nat"}],"uses_definitions":["D-005","D-007","D-012","D-013","D-017","S-P-040","S-P-041","S-P-042","S-P-043","S-P-044"],"source_anchors":[],"hypotheses":[{"key":"proposition_2_domain","proposition":{"proj":{"value":{"def":{"id":"S-P-044","args":[{"var":"epsilon_int"},{"var":"xi"},{"var":"sigma"},{"var":"theta"},{"var":"y"},{"var":"n"}]}},"index":0}}}],"witnesses":[],"conclusions":[{"key":"proposition_2","proposition":{"proj":{"value":{"def":{"id":"S-P-044","args":[{"var":"epsilon_int"},{"var":"xi"},{"var":"sigma"},{"var":"theta"},{"var":"y"},{"var":"n"}]}},"index":1}}}],"premises":[{"id":"MAP-P044-P040","producer":"P-040","closure_role":"REQUIRED","scope_binders":[{"key":"D_scope","type":"Nat"},{"key":"D_prime_scope","type":"Nat"},{"key":"t_scope","type":"Nat"},{"key":"d_scope","type":"Nat"},{"key":"d_prime_scope","type":"Nat"}],"guards":[{"key":"reindex_scope","proposition":{"proj":{"value":{"def":{"id":"S-P-040","args":[{"var":"n"},{"var":"D_scope"},{"var":"D_prime_scope"},{"var":"theta"},{"var":"t_scope"},{"var":"d_scope"},{"var":"d_prime_scope"}]}},"index":0}}}],"binder_map":{"n":{"var":"n"},"D":{"var":"D_scope"},"D_prime":{"var":"D_prime_scope"},"theta":{"var":"theta"},"t":{"var":"t_scope"},"d":{"var":"d_scope"},"d_prime":{"var":"d_prime_scope"}},"hypothesis_map":{"reindex_input":{"guard":"reindex_scope"}},"witness_map":{},"consume":["reindex_result"]},{"id":"MAP-P044-P041","producer":"P-041","closure_role":"REQUIRED","scope_binders":[{"key":"D2_scope","type":"Nat"},{"key":"D2_prime_scope","type":"Nat"},{"key":"t2_scope","type":"Nat"},{"key":"d2_scope","type":"Nat"},{"key":"d2_prime_scope","type":"Nat"}],"guards":[{"key":"reindex2_scope","proposition":{"proj":{"value":{"def":{"id":"S-P-040","args":[{"var":"n"},{"var":"D2_scope"},{"var":"D2_prime_scope"},{"var":"theta"},{"var":"t2_scope"},{"var":"d2_scope"},{"var":"d2_prime_scope"}]}},"index":0}}},{"key":"rough2_scope","proposition":{"proj":{"value":{"def":{"id":"S-P-041","args":[{"var":"n"},{"var":"D2_scope"},{"var":"D2_prime_scope"},{"var":"t2_scope"},{"var":"d2_scope"},{"var":"d2_prime_scope"},{"var":"sigma"},{"var":"theta"}]}},"index":0}}}],"binder_map":{"n":{"var":"n"},"D":{"var":"D2_scope"},"D_prime":{"var":"D2_prime_scope"},"t":{"var":"t2_scope"},"d":{"var":"d2_scope"},"d_prime":{"var":"d2_prime_scope"},"sigma":{"var":"sigma"},"theta":{"var":"theta"}},"hypothesis_map":{"reindex_input":{"guard":"reindex2_scope"},"rough_input":{"guard":"rough2_scope"}},"witness_map":{},"consume":["rough_index"]},{"id":"MAP-P044-P042","producer":"P-042","closure_role":"REQUIRED","scope_binders":[{"key":"m_high_scope","type":"Nat"},{"key":"k_high_scope","type":"Nat"}],"guards":[{"key":"high_scope","proposition":{"proj":{"value":{"def":{"id":"S-P-042","args":[{"var":"epsilon_int"},{"var":"xi"},{"var":"sigma"},{"var":"theta"},{"var":"y"},{"var":"n"},{"var":"m_high_scope"},{"var":"k_high_scope"}]}},"index":0}}}],"binder_map":{"epsilon_int":{"var":"epsilon_int"},"xi":{"var":"xi"},"sigma":{"var":"sigma"},"theta":{"var":"theta"},"y":{"var":"y"},"n":{"var":"n"},"m":{"var":"m_high_scope"},"k":{"var":"k_high_scope"}},"hypothesis_map":{"high_bin_input":{"guard":"high_scope"}},"witness_map":{},"consume":["power_bound"]},{"id":"MAP-P044-P043","producer":"P-043","closure_role":"REQUIRED","scope_binders":[{"key":"m_low_scope","type":"Nat"},{"key":"k_low_scope","type":"Nat"}],"guards":[{"key":"low_scope","proposition":{"proj":{"value":{"def":{"id":"S-P-043","args":[{"var":"epsilon_int"},{"var":"xi"},{"var":"sigma"},{"var":"theta"},{"var":"y"},{"var":"n"},{"var":"m_low_scope"},{"var":"k_low_scope"}]}},"index":0}}}],"binder_map":{"epsilon_int":{"var":"epsilon_int"},"xi":{"var":"xi"},"sigma":{"var":"sigma"},"theta":{"var":"theta"},"y":{"var":"y"},"n":{"var":"n"},"m":{"var":"m_low_scope"},"k":{"var":"k_low_scope"}},"hypothesis_map":{"low_bin_input":{"guard":"low_scope"}},"witness_map":{},"consume":["power_bound"]}],"witness_realizations":{},"proof_ref":"### P-044 — Proposition 2"}
```

- Prenex statement: for every
  \(\varepsilon_{\rm int}\in(0,1/10]\), \(\xi>1\),
  \(\sigma\ge\theta\ge2\), \(y\in(0,1)\), \(n>U_0\), put
  \(q=1/2+\varepsilon_{\rm int}\). Then
  \[
  f(n)\le
  (2\log\xi\log\theta/\log\sigma)^{-q\log y}
  \sum_{k\ge K_0(\sigma,\theta)}k^{-q\log y}f_k^\#(y,n).
  \]
- Local equalities: \(U_0,q,K_0\) are explicit D-007/D-017 values.
- Domain/range: infinite nonnegative majorant.
- Input subject: exact D-012 \(f(n)\). Output: exact D-013 majorant.
- Premise maps:
  - P-040 — Binders:
    \(n:=n,D:=D,D':=D',\theta:=\theta\),
    \(t:=\gcd(D,D'),d:=D/t,d':=D'/t\).
    Hypotheses: each ordered close divisor term of Q.
    Consumed: exact bijection and weight identity.
    Subject: the Q-sum becomes the coprime \(dd't\mid n\) sum.
    Constants: none.
  - P-041 — Binders:
    \(n:=n,D:=D,D':=D',t:=\gcd(D,D'),d:=D/t,d':=D'/t,
    \sigma:=\sigma,\theta:=\theta\).
    Hypotheses: \(\chi(n,\theta)=1\) on nonzero \(f\) terms and
    \(\chi(dt,\sigma)=1\) from the Q weight.
    Consumed: rough divisor and index lower bound.
    Subject: \(d\) enters its unique D-013 half-open bin.
    Constants: none.
  - P-042 — Binders:
    \(\varepsilon_{\rm int}:=\varepsilon_{\rm int},\xi:=\xi,
    \sigma:=\sigma,\theta:=\theta,y:=y,n:=n,m:=dt,
    k:=\lfloor\log d/\log\theta\rfloor\),
    \(q:=1/2+\varepsilon_{\rm int}\).
    Hypotheses: high-bin inequality and Good from \(\chi_n^*(dt)=1\).
    Consumed: high-bin pointwise power bound.
    Subject: exact Q weight on \(D=dt\).
    Constants: none.
  - P-043 — Binders:
    \(\varepsilon_{\rm int}:=\varepsilon_{\rm int}\),
    \(\xi:=\xi,\sigma:=\sigma,\theta:=\theta,y:=y,n:=n,m:=dt,k:=k,
    q:=1/2+\varepsilon_{\rm int}\) in the complementary low-bin range.
    Hypotheses: P-041 lower index and failure of the high-bin predicate.
    Consumed: low-bin pointwise power bound.
    Subject: exact Q weight on \(D=dt\).
    Constants: none.
- Derivation certificate: apply gcd bijection; partition \(d\) by its unique
  half-open bin; apply one of the two pointwise bounds; enlarge the
  nonnegative sum by dropping coprimality and \(\chi(n,\theta)\).
- Source/S2 anchor: ET Proposition 2, pp. 28–29; S2 R1 §4, R2.3.
- Definitions used: D-005, D-007, D-012, D-013, D-017.

## 7. Proposition 3 common infrastructure

### Section 7 typed support definitions

These definitions name the exact Section 7 domains, analytic subjects, and canonical witness selections used below.

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S7A-PRIME","kind":"DEFINITION","binders":[{"key":"p","type":"Nat"}],"uses_definitions":[],"source_anchors":[],"result_type":"Prop","body":"p is a prime positive integer."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S7A-COPRIME","kind":"DEFINITION","binders":[{"key":"r","type":"Nat"},{"key":"s","type":"Nat"}],"uses_definitions":[],"source_anchors":[],"result_type":"Prop","body":"r and s are coprime positive integers."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S7A-NONNEG-MULT","kind":"DEFINITION","binders":[{"key":"f","type":{"fn":{"args":["Nat"],"return":"Real"}}}],"uses_definitions":[],"source_anchors":[],"result_type":"Prop","body":"On positive integers, f is nonnegative, f(1)=1, and f(rs)=f(r)f(s) whenever r,s are positive and coprime."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S7A-REAL-POWER","kind":"DEFINITION","binders":[{"key":"base","type":"Real"},{"key":"exponent","type":"Real"}],"uses_definitions":[],"source_anchors":[],"result_type":"Real","body":"For base>0, the exact real power base^exponent."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S7A-WEIGHT-TYPE","kind":"DEFINITION","binders":[{"key":"f","type":{"fn":{"args":["Nat"],"return":"Real"}}},{"key":"c","type":"Real"},{"key":"C","type":"Real"},{"key":"Lambda","type":"Real"}],"uses_definitions":["D-S7A-NONNEG-MULT","D-S7A-PRIME","D-S7A-REAL-POWER"],"source_anchors":[],"result_type":"Prop","body":"D-S7A-NONNEG-MULT(f), c,C,Lambda>0, and for every prime p and i>=1, |f(p^i)-1/(i+1)| <= C p^(-c) and 0 <= f(p^i) <= Lambda."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S7A-MODIFIER","kind":"DEFINITION","binders":[{"key":"b","type":{"fn":{"args":["Nat"],"return":"Real"}}}],"uses_definitions":["D-S7A-NONNEG-MULT","D-S7A-PRIME"],"source_anchors":[],"result_type":"Prop","body":"D-S7A-NONNEG-MULT(b), and for every prime p and every j in Nat, 0 <= b(p^j) <= 1."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S7A-ONE","kind":"DEFINITION","binders":[],"uses_definitions":[],"source_anchors":[],"result_type":{"fn":{"args":["Nat"],"return":"Real"}},"body":"The constant function n |-> 1 on positive integers."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S7A-A0","kind":"DEFINITION","binders":[],"uses_definitions":["D-001"],"source_anchors":[],"result_type":{"fn":{"args":["Nat"],"return":"Real"}},"body":"The exact function a0(n)=1/tau(n)."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S7A-V","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"},{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"}],"uses_definitions":["D-002","D-003"],"source_anchors":[],"result_type":{"fn":{"args":["Nat"],"return":"Real"}},"body":"The exact modifier v_k(n)=y^Omega(n,theta^k) chi(n,sigma)."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S7A-SHIFT","kind":"DEFINITION","binders":[{"key":"a","type":{"fn":{"args":["Nat"],"return":"Real"}}},{"key":"b","type":{"fn":{"args":["Nat"],"return":"Real"}}}],"uses_definitions":["D-014"],"source_anchors":[],"result_type":{"fn":{"args":["Nat"],"return":"Real"}},"body":"The multiplicative extension of the exact D-014 local quotient S[a,b](p^i)."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S7A-HAT","kind":"DEFINITION","binders":[{"key":"a","type":{"fn":{"args":["Nat"],"return":"Real"}}},{"key":"b","type":{"fn":{"args":["Nat"],"return":"Real"}}}],"uses_definitions":["D-014","D-S7A-SHIFT"],"source_anchors":[],"result_type":{"fn":{"args":["Nat"],"return":"Real"}},"body":"The multiplicative extension with prime-power values max(S[a,b](p^i),a(p^i))."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S7A-MAX","kind":"DEFINITION","binders":[{"key":"a_1","type":{"fn":{"args":["Nat"],"return":"Real"}}},{"key":"a_2","type":{"fn":{"args":["Nat"],"return":"Real"}}}],"uses_definitions":[],"source_anchors":[],"result_type":{"fn":{"args":["Nat"],"return":"Real"}},"body":"The multiplicative function with prime-power values max(a_1(p^i),a_2(p^i))."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S7A-W1","kind":"DEFINITION","binders":[],"uses_definitions":["D-S7A-A0","D-S7A-HAT","D-S7A-ONE"],"source_anchors":[],"result_type":{"fn":{"args":["Nat"],"return":"Real"}},"body":"The exact weight w1=hat(S[a0,1],a0)."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S7A-W2","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"},{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"}],"uses_definitions":["D-S7A-HAT","D-S7A-V","D-S7A-W1"],"source_anchors":[],"result_type":{"fn":{"args":["Nat"],"return":"Real"}},"body":"The exact weight w_{2,k}=hat(S[w1,v_k],w1)."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S7A-W3","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"},{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"}],"uses_definitions":["D-S7A-MAX","D-S7A-W1","D-S7A-W2"],"source_anchors":[],"result_type":{"fn":{"args":["Nat"],"return":"Real"}},"body":"The exact weight w_{3,k}, the prime-power maximum of w1 and w_{2,k}, extended multiplicatively."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S7A-W4","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"},{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"}],"uses_definitions":["D-S7A-HAT","D-S7A-V","D-S7A-W3"],"source_anchors":[],"result_type":{"fn":{"args":["Nat"],"return":"Real"}},"body":"The exact weight w_{4,k}=hat(S[w_{3,k},v_k],w_{3,k})."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S7A-DEN","kind":"DEFINITION","binders":[{"key":"a","type":{"fn":{"args":["Nat"],"return":"Real"}}},{"key":"b","type":{"fn":{"args":["Nat"],"return":"Real"}}},{"key":"p","type":"Nat"}],"uses_definitions":[],"source_anchors":[],"result_type":"Real","body":"The literal convergent denominator sum D_p[a,b]=sum_{j>=0} a(p^j)b(p^j)p^(-j)."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S7A-EULER","kind":"DEFINITION","binders":[{"key":"w","type":{"fn":{"args":["Nat"],"return":"Real"}}},{"key":"b","type":{"fn":{"args":["Nat"],"return":"Real"}}},{"key":"p","type":"Nat"}],"uses_definitions":[],"source_anchors":[],"result_type":"Real","body":"The literal local Euler factor L_p(w,b)=sum_{j>=0} w(p^j)b(p^j)p^(-j)."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S7A-TWO-K-MINUS-ONE","kind":"DEFINITION","binders":[{"key":"k","type":"Nat"}],"uses_definitions":[],"source_anchors":[],"result_type":"Nat","body":"For k>=1, the natural number 2k-1."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S7A-FOUR-SUM","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"},{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"},{"key":"x","type":"Real"}],"uses_definitions":["D-001","D-002","D-003","D-005"],"source_anchors":[],"result_type":"Real","body":"The exact finite nonnegative four-variable sum over positive d,d',t,m with theta^k<=d<theta^(k+1), Close_theta(d,d'), t<x/(dd'), m<x/(tdd'), and summand chi(dt,sigma)y^Omega(dt,theta^k)/tau(mtdd')."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S7A-SHIFT-W","kind":"DEFINITION","binders":[{"key":"a","type":{"fn":{"args":["Nat"],"return":"Real"}}},{"key":"c_a","type":"Real"},{"key":"C_a","type":"Real"},{"key":"Lambda_a","type":"Real"}],"uses_definitions":[],"source_anchors":[],"result_type":{"tuple":["Real","Real","Real"]},"body":"The canonical modifier-uniform witnesses: c_sh=min(c_a,1/2)>0 and the explicit positive C_sh,Lambda_sh obtained from the P-051C numerator-tail and denominator estimates."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S7A-HAT-W","kind":"DEFINITION","binders":[{"key":"a","type":{"fn":{"args":["Nat"],"return":"Real"}}},{"key":"c_a","type":"Real"},{"key":"C_a","type":"Real"},{"key":"Lambda_a","type":"Real"},{"key":"c_sh","type":"Real"},{"key":"C_sh","type":"Real"},{"key":"Lambda_sh","type":"Real"}],"uses_definitions":[],"source_anchors":[],"result_type":{"tuple":["Real","Real","Real"]},"body":"The canonical positive witnesses for hat(S[a,b],a), uniformly in b: exponent min(c_a,c_sh) and explicit maxima of the input/shift error and local bounds."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S7A-F4-W","kind":"DEFINITION","binders":[],"uses_definitions":[],"source_anchors":[],"result_type":{"tuple":["Real","Real","Real"]},"body":"The canonical positive witnesses selected before the entire theta,y,k,sigma family for w4, justified by the uniform w3 type and the modifier-uniform P-051C/P-051D estimates."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S7A-COMMON-TWO","kind":"DEFINITION","binders":[{"key":"c_1","type":"Real"},{"key":"C_1","type":"Real"},{"key":"Lambda_1","type":"Real"},{"key":"c_2","type":"Real"},{"key":"C_2","type":"Real"},{"key":"Lambda_2","type":"Real"}],"uses_definitions":[],"source_anchors":[],"result_type":{"tuple":["Real","Real","Real"]},"body":"The positive common witnesses (min(c_1,c_2), max(C_1,C_2), max(Lambda_1,Lambda_2))."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S7A-COMMON-FIVE","kind":"DEFINITION","binders":[{"key":"c_0","type":"Real"},{"key":"C_0","type":"Real"},{"key":"Lambda_0","type":"Real"},{"key":"c_1","type":"Real"},{"key":"C_1","type":"Real"},{"key":"Lambda_1","type":"Real"},{"key":"c_2","type":"Real"},{"key":"C_2","type":"Real"},{"key":"Lambda_2","type":"Real"},{"key":"c_3","type":"Real"},{"key":"C_3","type":"Real"},{"key":"Lambda_3","type":"Real"},{"key":"c_4","type":"Real"},{"key":"C_4","type":"Real"},{"key":"Lambda_4","type":"Real"}],"uses_definitions":["D-S7A-REAL-POWER"],"source_anchors":[],"result_type":{"tuple":["Real","Real","Real"]},"body":"The common witnesses: the minimum of c_0,...,c_4, the maximum of C_0,...,C_4, and the maximum of Lambda_0,...,Lambda_4 enlarged to at least 1+C_*2^(-c_*)."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S7A-ETA","kind":"DEFINITION","binders":[{"key":"c_star","type":"Real"}],"uses_definitions":[],"source_anchors":[],"result_type":"Real","body":"eta_*=min(c_*,1)."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S7A-CE","kind":"DEFINITION","binders":[{"key":"C_star","type":"Real"},{"key":"Lambda_star","type":"Real"}],"uses_definitions":[],"source_anchors":[],"result_type":"Real","body":"C_{E,*}=C_*+2 Lambda_*."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S7A-SELECTED-WEIGHT","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"},{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"},{"key":"w","type":{"fn":{"args":["Nat"],"return":"Real"}}}],"uses_definitions":["D-S7A-A0","D-S7A-W1","D-S7A-W2","D-S7A-W3","D-S7A-W4"],"source_anchors":[],"result_type":"Prop","body":"w is exactly one of a0,w1,w_{2,k},w_{3,k},w_{4,k}, with the parameterized weights evaluated at the displayed theta,y,k,sigma."}
```



























```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S7-P051V-DOMAIN","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"},{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"}],"uses_definitions":[],"source_anchors":[],"result_type":"Prop","body":"theta>=2, y in (0,1), k>=1, and sigma>=theta."}
```



















### P-050 — exact typed four-variable inversion

```mathminer-s3
{"schema":"mathminer.s3/1","id":"P-050","kind":"PROPOSITION","binders":[{"key":"theta","type":"Real"},{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"},{"key":"x","type":"Real"}],"uses_definitions":["D-017","D-S7A-FOUR-SUM","D-S7A-TWO-K-MINUS-ONE"],"source_anchors":[],"hypotheses":[{"key":"theta_ge_2","proposition":{"op":{"name":"ge","args":[{"var":"theta"},{"lit":{"type":"Real","value":"2"}}]}}},{"key":"y_pos","proposition":{"op":{"name":"gt","args":[{"var":"y"},{"lit":{"type":"Real","value":"0"}}]}}},{"key":"y_lt_1","proposition":{"op":{"name":"lt","args":[{"var":"y"},{"lit":{"type":"Real","value":"1"}}]}}},{"key":"k_ge_1","proposition":{"op":{"name":"ge","args":[{"var":"k"},{"lit":{"type":"Nat","value":"1"}}]}}},{"key":"sigma_ge_theta","proposition":{"op":{"name":"ge","args":[{"var":"sigma"},{"var":"theta"}]}}},{"key":"x_range","proposition":{"op":{"name":"gt","args":[{"var":"x"},{"op":{"name":"pow_nat","args":[{"var":"theta"},{"def":{"id":"D-S7A-TWO-K-MINUS-ONE","args":[{"var":"k"}]}}]}}]}}}],"witnesses":[],"conclusions":[{"key":"four_variable_inversion","proposition":{"op":{"name":"eq","args":[{"proj":{"value":{"def":{"id":"D-017","args":[{"var":"sigma"},{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"x"}]}},"index":1}},{"def":{"id":"D-S7A-FOUR-SUM","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"},{"var":"x"}]}}]}}}],"premises":[],"witness_realizations":{},"proof_ref":"### P-050 — exact typed four-variable inversion"}
```

- Prenex statement: for every \(y\in(0,1)\), \(k\ge1\),
  \(\sigma\ge\theta\ge2\), and \(x>\theta^{2k-1}\),
  \[
  S_k(x,y;\sigma,\theta)=
  \sum_{\substack{d,d'>0\\\theta^k\le d<\theta^{k+1}\\
  {\rm Close}_\theta(d,d')}}
  \sum_{t<x/(dd')}\chi(dt,\sigma)y^{\Omega(dt,\theta^k)}
  \sum_{m<x/(tdd')}\tau(mtdd')^{-1}.
  \]
- Local equalities: \(n=mtdd'\), \(m=n/(tdd')\), only after
  \(dd't\mid n\).
- Domain/range: all four indices positive integers; sums finite and
  nonnegative.
- Input subject: \(\sum_{n<x}f_k^\#(y,n)\).
  Output subject: exact four-variable sum.
- Premise maps: none (root transformation-result proposition).
- Derivation certificate: D-013 supplies \(dd't\mid n\); the map
  \((n,d,d',t)\leftrightarrow(m,d,d',t)\) is bijective, preserves the
  half-open \(d\)-bin, strict closeness, every weight, denominator, and
  multiplicity.
- Source/S2 anchor: ET (8), pp. 29–30; S2 R1 (5.1), R2.3–R2.4.
- Definitions used: D-001, D-002, D-003, D-005, D-013, D-017.

### P-051A — base type for \(a_0\)

```mathminer-s3
{"schema":"mathminer.s3/1","id":"P-051A","kind":"PROPOSITION","binders":[],"uses_definitions":["D-S7A-A0","D-S7A-MODIFIER","D-S7A-ONE","D-S7A-PRIME","D-S7A-WEIGHT-TYPE"],"source_anchors":[],"hypotheses":[],"witnesses":[{"key":"c_0","type":"Real","depends_on":[]},{"key":"C_0","type":"Real","depends_on":[]},{"key":"Lambda_0","type":"Real","depends_on":[]}],"conclusions":[{"key":"base_type","proposition":{"def":{"id":"D-S7A-WEIGHT-TYPE","args":[{"def":{"id":"D-S7A-A0","args":[]}},{"var":"c_0"},{"var":"C_0"},{"var":"Lambda_0"}]}}},{"key":"base_prime_power_exact","proposition":{"forall":{"binders":[{"key":"p","type":"Nat"},{"key":"i","type":"Nat"}],"body":{"op":{"name":"implies","args":[{"op":{"name":"and","args":[{"def":{"id":"D-S7A-PRIME","args":[{"var":"p"}]}},{"op":{"name":"ge","args":[{"var":"i"},{"lit":{"type":"Nat","value":"1"}}]}}]}},{"op":{"name":"eq","args":[{"app":{"fn":{"def":{"id":"D-S7A-A0","args":[]}},"args":[{"op":{"name":"pow_nat","args":[{"var":"p"},{"var":"i"}]}}]}},{"op":{"name":"div","args":[{"lit":{"type":"Real","value":"1"}},{"op":{"name":"add","args":[{"cast":{"value":{"var":"i"},"to":"Real"}},{"lit":{"type":"Real","value":"1"}}]}}]}}]}}]}}}}},{"key":"one_modifier","proposition":{"def":{"id":"D-S7A-MODIFIER","args":[{"def":{"id":"D-S7A-ONE","args":[]}}]}}}],"premises":[],"witness_realizations":{"c_0":{"lit":{"type":"Real","value":"1"}},"C_0":{"lit":{"type":"Real","value":"1"}},"Lambda_0":{"lit":{"type":"Real","value":"1"}}},"proof_ref":"### P-051A — base type for \\(a_0\\)"}
```

- Prenex statement: define \(a_0(n)=1/\tau(n)\).  Then \(a_0\) is
  nonnegative and multiplicative and, for every prime \(p\) and \(i\ge1\),
  \[
  a_0(p^i)={1\over i+1},\qquad 0\le a_0(p^i)\le1.
  \tag{P051A}
  \]
  Thus it has absolute common type witnesses, for example
  \(c_0=1,C_0=1,\Lambda_0=1\), with zero actual type error.
- Exact subject: `SUB-P051A-BASE` is the D-015 function \(a_0\), including
  its integer multiplicative extension.
- Premise maps: none (bounded root).
- Derivation certificate: \(\tau(p^i)=i+1\) and multiplicativity of \(\tau\)
  on coprime inputs.
- Source/S2 anchor: S2 R2.4, (R2.10), and S2B R2(3).
- Definitions used: D-001, D-015.

### P-051B — uniform shift-denominator estimate

```mathminer-s3
{"schema":"mathminer.s3/1","id":"P-051B","kind":"PROPOSITION","binders":[{"key":"a","type":{"fn":{"args":["Nat"],"return":"Real"}}},{"key":"c_a","type":"Real"},{"key":"C_a","type":"Real"},{"key":"Lambda_a","type":"Real"},{"key":"b","type":{"fn":{"args":["Nat"],"return":"Real"}}},{"key":"p","type":"Nat"}],"uses_definitions":["D-S7A-DEN","D-S7A-MODIFIER","D-S7A-PRIME","D-S7A-WEIGHT-TYPE"],"source_anchors":[],"hypotheses":[{"key":"typed_a","proposition":{"def":{"id":"D-S7A-WEIGHT-TYPE","args":[{"var":"a"},{"var":"c_a"},{"var":"C_a"},{"var":"Lambda_a"}]}}},{"key":"modifier_b","proposition":{"def":{"id":"D-S7A-MODIFIER","args":[{"var":"b"}]}}},{"key":"prime_p","proposition":{"def":{"id":"D-S7A-PRIME","args":[{"var":"p"}]}}}],"witnesses":[],"conclusions":[{"key":"denominator_lower","proposition":{"op":{"name":"le","args":[{"lit":{"type":"Real","value":"1"}},{"def":{"id":"D-S7A-DEN","args":[{"var":"a"},{"var":"b"},{"var":"p"}]}}]}}},{"key":"denominator_upper_geometric","proposition":{"op":{"name":"le","args":[{"def":{"id":"D-S7A-DEN","args":[{"var":"a"},{"var":"b"},{"var":"p"}]}},{"op":{"name":"add","args":[{"lit":{"type":"Real","value":"1"}},{"op":{"name":"div","args":[{"var":"Lambda_a"},{"op":{"name":"sub","args":[{"cast":{"value":{"var":"p"},"to":"Real"}},{"lit":{"type":"Real","value":"1"}}]}}]}}]}}]}}},{"key":"denominator_upper_prime","proposition":{"op":{"name":"le","args":[{"def":{"id":"D-S7A-DEN","args":[{"var":"a"},{"var":"b"},{"var":"p"}]}},{"op":{"name":"add","args":[{"lit":{"type":"Real","value":"1"}},{"op":{"name":"div","args":[{"op":{"name":"mul","args":[{"lit":{"type":"Real","value":"2"}},{"var":"Lambda_a"}]}},{"cast":{"value":{"var":"p"},"to":"Real"}}]}}]}}]}}}],"premises":[],"witness_realizations":{},"proof_ref":"### P-051B — uniform shift-denominator estimate"}
```

- Prenex statement: fix a nonnegative multiplicative \(a\), normalized by
  \(a(1)=1\), and witnesses
  \(c_a,C_a,\Lambda_a>0\) such that, for all primes \(p\) and \(i\ge1\),
  \[
  |a(p^i)-1/(i+1)|\le C_ap^{-c_a},\qquad
  0\le a(p^i)\le\Lambda_a.
  \]
  Uniformly for every nonnegative multiplicative \(b\), normalized by
  \(b(1)=1\), satisfying
  \(0\le b(p^j)\le1\) for all primes \(p\) and \(j\ge0\), define
  \(D_p[a,b]=\sum_{j\ge0}a(p^j)b(p^j)p^{-j}\).  Then
  \[
  1\le D_p[a,b]\le1+{\Lambda_a\over p-1}
      \le1+{2\Lambda_a\over p}.
  \tag{P051B}
  \]
  In particular every D-014 shift denominator is positive, and the estimate
  is uniform over the entire \(b\)-family.
- Exact subject: `SUB-P051B-DEN` is the literal D-014 denominator.
- Premise maps: `MAP-P051B-TYPE-a` takes the displayed type and bound
  witnesses for \(a\); no proposition premise is hidden.
- Derivation certificate: the \(j=0\) term is \(a(1)b(1)=1\), and the
  nonnegative \(j\ge1\) terms are bounded by
  \(\Lambda_a\sum_{j\ge1}p^{-j}=\Lambda_a/(p-1)\).
- Source/S2 anchor: S2 R2.4a and S2B R2(3).
- Definitions used: D-014.

### P-051C — generic uniform one-step shift stability

```mathminer-s3
{"schema":"mathminer.s3/1","id":"P-051C","kind":"PROPOSITION","binders":[{"key":"a","type":{"fn":{"args":["Nat"],"return":"Real"}}},{"key":"c_a","type":"Real"},{"key":"C_a","type":"Real"},{"key":"Lambda_a","type":"Real"},{"key":"b","type":{"fn":{"args":["Nat"],"return":"Real"}}}],"uses_definitions":["D-S7A-MODIFIER","D-S7A-PRIME","D-S7A-SHIFT","D-S7A-SHIFT-W","D-S7A-WEIGHT-TYPE"],"source_anchors":[],"hypotheses":[{"key":"typed_a","proposition":{"def":{"id":"D-S7A-WEIGHT-TYPE","args":[{"var":"a"},{"var":"c_a"},{"var":"C_a"},{"var":"Lambda_a"}]}}},{"key":"modifier_b","proposition":{"def":{"id":"D-S7A-MODIFIER","args":[{"var":"b"}]}}}],"witnesses":[{"key":"c_sh","type":"Real","depends_on":["a","c_a","C_a","Lambda_a"]},{"key":"C_sh","type":"Real","depends_on":["a","c_a","C_a","Lambda_a"]},{"key":"Lambda_sh","type":"Real","depends_on":["a","c_a","C_a","Lambda_a"]}],"conclusions":[{"key":"shift_type","proposition":{"def":{"id":"D-S7A-WEIGHT-TYPE","args":[{"def":{"id":"D-S7A-SHIFT","args":[{"var":"a"},{"var":"b"}]}},{"var":"c_sh"},{"var":"C_sh"},{"var":"Lambda_sh"}]}}}],"premises":[{"id":"MAP-P051C-P051B","producer":"P-051B","closure_role":"REQUIRED","scope_binders":[{"key":"p_scope","type":"Nat"}],"guards":[{"key":"prime_scope","proposition":{"def":{"id":"D-S7A-PRIME","args":[{"var":"p_scope"}]}}}],"binder_map":{"a":{"var":"a"},"c_a":{"var":"c_a"},"C_a":{"var":"C_a"},"Lambda_a":{"var":"Lambda_a"},"b":{"var":"b"},"p":{"var":"p_scope"}},"hypothesis_map":{"typed_a":{"hypothesis":"typed_a"},"modifier_b":{"hypothesis":"modifier_b"},"prime_p":{"guard":"prime_scope"}},"witness_map":{},"consume":["denominator_lower","denominator_upper_geometric","denominator_upper_prime"]}],"witness_realizations":{"c_sh":{"proj":{"value":{"def":{"id":"D-S7A-SHIFT-W","args":[{"var":"a"},{"var":"c_a"},{"var":"C_a"},{"var":"Lambda_a"}]}},"index":0}},"C_sh":{"proj":{"value":{"def":{"id":"D-S7A-SHIFT-W","args":[{"var":"a"},{"var":"c_a"},{"var":"C_a"},{"var":"Lambda_a"}]}},"index":1}},"Lambda_sh":{"proj":{"value":{"def":{"id":"D-S7A-SHIFT-W","args":[{"var":"a"},{"var":"c_a"},{"var":"C_a"},{"var":"Lambda_a"}]}},"index":2}}},"proof_ref":"### P-051C — generic uniform one-step shift stability"}
```

- Prenex statement: after fixing \(a,c_a,C_a,\Lambda_a\) as in P-051B,
  there exist \(c_{\rm sh},C_{\rm sh},\Lambda_{\rm sh}>0\), depending only
  on those fixed inputs, such that for every admissible modifier \(b\), every
  prime \(p\), and every \(i\ge1\), \(\mathcal S[a,b]\) is nonnegative and
  multiplicative and
  \[
  |\mathcal S[a,b](p^i)-1/(i+1)|
     \le C_{\rm sh}p^{-c_{\rm sh}},\qquad
  0\le\mathcal S[a,b](p^i)\le\Lambda_{\rm sh},
  \tag{P051C}
  \]
  where one may take \(c_{\rm sh}=\min(c_a,1/2)>0\).  The witnesses precede
  \(b,p,i\); hence they do not depend on a member of the \(b\)-family.
- Exact subjects: `SUB-P051C-NUM` is the literal D-014 numerator and
  `SUB-P051C-SHIFT` the literal quotient/multiplicative extension.
- Premise maps: `MAP-P051C-P051B` has producer slots
  \((a,c_a,C_a,\Lambda_a,b,p):=(a,c_a,C_a,\Lambda_a,b,p)\); the modifier
  hypotheses are identical.  Consumed conclusion is positivity and the
  uniform estimate for `SUB-P051B-DEN`.
- Derivation certificate: isolate the \(j=0\) numerator term \(a(p^i)\).
  The uniform \(j\ge1\) tail is bounded by a constant depending only on
  \(\Lambda_a\) times \((1+\log p)/p=O(p^{-1/2})\).  Divide by the positive
  P-051B denominator, whose deviation from one is \(O_{\Lambda_a}(1/p)\),
  and combine with the input \(p^{-c_a}\) error.  This is one bounded
  quotient-stability step.
- Source/S2 anchor: S2 R2.4a and S2B R2(3).
- Definitions used: D-014.

### P-051D — hat-shift maximum and integer domination

```mathminer-s3
{"schema":"mathminer.s3/1","id":"P-051D","kind":"PROPOSITION","binders":[{"key":"a","type":{"fn":{"args":["Nat"],"return":"Real"}}},{"key":"c_a","type":"Real"},{"key":"C_a","type":"Real"},{"key":"Lambda_a","type":"Real"},{"key":"b","type":{"fn":{"args":["Nat"],"return":"Real"}}}],"uses_definitions":["D-S7A-HAT","D-S7A-HAT-W","D-S7A-MODIFIER","D-S7A-SHIFT","D-S7A-WEIGHT-TYPE"],"source_anchors":[],"hypotheses":[{"key":"typed_a","proposition":{"def":{"id":"D-S7A-WEIGHT-TYPE","args":[{"var":"a"},{"var":"c_a"},{"var":"C_a"},{"var":"Lambda_a"}]}}},{"key":"modifier_b","proposition":{"def":{"id":"D-S7A-MODIFIER","args":[{"var":"b"}]}}}],"witnesses":[{"key":"c_hat","type":"Real","depends_on":["a","c_a","C_a","Lambda_a"]},{"key":"C_hat","type":"Real","depends_on":["a","c_a","C_a","Lambda_a"]},{"key":"Lambda_hat","type":"Real","depends_on":["a","c_a","C_a","Lambda_a"]}],"conclusions":[{"key":"hat_type","proposition":{"def":{"id":"D-S7A-WEIGHT-TYPE","args":[{"def":{"id":"D-S7A-HAT","args":[{"var":"a"},{"var":"b"}]}},{"var":"c_hat"},{"var":"C_hat"},{"var":"Lambda_hat"}]}}},{"key":"dominates_shift","proposition":{"forall":{"binders":[{"key":"K","type":"Nat"}],"body":{"op":{"name":"implies","args":[{"op":{"name":"gt","args":[{"var":"K"},{"lit":{"type":"Nat","value":"0"}}]}},{"op":{"name":"ge","args":[{"app":{"fn":{"def":{"id":"D-S7A-HAT","args":[{"var":"a"},{"var":"b"}]}},"args":[{"var":"K"}]}},{"app":{"fn":{"def":{"id":"D-S7A-SHIFT","args":[{"var":"a"},{"var":"b"}]}},"args":[{"var":"K"}]}}]}}]}}}}},{"key":"dominates_input","proposition":{"forall":{"binders":[{"key":"K","type":"Nat"}],"body":{"op":{"name":"implies","args":[{"op":{"name":"gt","args":[{"var":"K"},{"lit":{"type":"Nat","value":"0"}}]}},{"op":{"name":"ge","args":[{"app":{"fn":{"def":{"id":"D-S7A-HAT","args":[{"var":"a"},{"var":"b"}]}},"args":[{"var":"K"}]}},{"app":{"fn":{"var":"a"},"args":[{"var":"K"}]}}]}}]}}}}}],"premises":[{"id":"MAP-P051D-P051C","producer":"P-051C","closure_role":"REQUIRED","binder_map":{"a":{"var":"a"},"c_a":{"var":"c_a"},"C_a":{"var":"C_a"},"Lambda_a":{"var":"Lambda_a"},"b":{"var":"b"}},"hypothesis_map":{"typed_a":{"hypothesis":"typed_a"},"modifier_b":{"hypothesis":"modifier_b"}},"witness_map":{"c_sh":"p051d_c_sh","C_sh":"p051d_C_sh","Lambda_sh":"p051d_Lambda_sh"},"consume":["shift_type"]}],"witness_realizations":{"c_hat":{"proj":{"value":{"def":{"id":"D-S7A-HAT-W","args":[{"var":"a"},{"var":"c_a"},{"var":"C_a"},{"var":"Lambda_a"},{"var":"p051d_c_sh"},{"var":"p051d_C_sh"},{"var":"p051d_Lambda_sh"}]}},"index":0}},"C_hat":{"proj":{"value":{"def":{"id":"D-S7A-HAT-W","args":[{"var":"a"},{"var":"c_a"},{"var":"C_a"},{"var":"Lambda_a"},{"var":"p051d_c_sh"},{"var":"p051d_C_sh"},{"var":"p051d_Lambda_sh"}]}},"index":1}},"Lambda_hat":{"proj":{"value":{"def":{"id":"D-S7A-HAT-W","args":[{"var":"a"},{"var":"c_a"},{"var":"C_a"},{"var":"Lambda_a"},{"var":"p051d_c_sh"},{"var":"p051d_C_sh"},{"var":"p051d_Lambda_sh"}]}},"index":2}}},"proof_ref":"### P-051D — hat-shift maximum and integer domination"}
```

- Prenex statement: on the P-051C domain, let
  \(s=\mathcal S[a,b]\) with type witnesses supplied by P-051C and define
  \(\widehat s(p^i)=\max(s(p^i),a(p^i))\), extended multiplicatively.
  Then \(\widehat s\) is nonnegative multiplicative, is of type
  \(\tau^{-1}\) with witnesses depending only on the input and P-051C
  witnesses, and for every \(K\in\mathbb N_{>0}\),
  \[
  \widehat s(K)\ge s(K),\qquad \widehat s(K)\ge a(K).
  \tag{P051D}
  \]
- Exact subject: `SUB-P051D-HAT` is literally
  \(\widehat{\mathcal S}[a,b]\) from D-014.
- Premise maps: `MAP-P051D-P051C` consumes the exact type/bound conclusion
  for \(s\); `MAP-P051D-TYPE-a` consumes the displayed input type of \(a\).
- Derivation certificate: at each prime power the maximum of two quantities
  with the same main term has error bounded by the maximum of their two error
  bounds.  Multiplicative extension preserves nonnegativity, and multiplying
  the prime-power inequalities over the factorization of \(K\) proves both
  integer dominations.
- Source/S2 anchor: S2 R2.4, (R2.9), and S2B R2(3).
- Definitions used: D-014.

### P-051E — two-weight prime-power maximum

```mathminer-s3
{"schema":"mathminer.s3/1","id":"P-051E","kind":"PROPOSITION","binders":[{"key":"a_1","type":{"fn":{"args":["Nat"],"return":"Real"}}},{"key":"a_2","type":{"fn":{"args":["Nat"],"return":"Real"}}},{"key":"c","type":"Real"},{"key":"C","type":"Real"},{"key":"Lambda","type":"Real"}],"uses_definitions":["D-S7A-MAX","D-S7A-WEIGHT-TYPE"],"source_anchors":[],"hypotheses":[{"key":"typed_a_1","proposition":{"def":{"id":"D-S7A-WEIGHT-TYPE","args":[{"var":"a_1"},{"var":"c"},{"var":"C"},{"var":"Lambda"}]}}},{"key":"typed_a_2","proposition":{"def":{"id":"D-S7A-WEIGHT-TYPE","args":[{"var":"a_2"},{"var":"c"},{"var":"C"},{"var":"Lambda"}]}}}],"witnesses":[],"conclusions":[{"key":"maximum_type","proposition":{"def":{"id":"D-S7A-WEIGHT-TYPE","args":[{"def":{"id":"D-S7A-MAX","args":[{"var":"a_1"},{"var":"a_2"}]}},{"var":"c"},{"var":"C"},{"var":"Lambda"}]}}},{"key":"dominates_first","proposition":{"forall":{"binders":[{"key":"K","type":"Nat"}],"body":{"op":{"name":"implies","args":[{"op":{"name":"gt","args":[{"var":"K"},{"lit":{"type":"Nat","value":"0"}}]}},{"op":{"name":"ge","args":[{"app":{"fn":{"def":{"id":"D-S7A-MAX","args":[{"var":"a_1"},{"var":"a_2"}]}},"args":[{"var":"K"}]}},{"app":{"fn":{"var":"a_1"},"args":[{"var":"K"}]}}]}}]}}}}},{"key":"dominates_second","proposition":{"forall":{"binders":[{"key":"K","type":"Nat"}],"body":{"op":{"name":"implies","args":[{"op":{"name":"gt","args":[{"var":"K"},{"lit":{"type":"Nat","value":"0"}}]}},{"op":{"name":"ge","args":[{"app":{"fn":{"def":{"id":"D-S7A-MAX","args":[{"var":"a_1"},{"var":"a_2"}]}},"args":[{"var":"K"}]}},{"app":{"fn":{"var":"a_2"},"args":[{"var":"K"}]}}]}}]}}}}}],"premises":[],"witness_realizations":{},"proof_ref":"### P-051E — two-weight prime-power maximum"}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"P-051E0","kind":"DERIVATION","binders":[{"key":"a_1","type":{"fn":{"args":["Nat"],"return":"Real"}}},{"key":"a_2","type":{"fn":{"args":["Nat"],"return":"Real"}}},{"key":"c_1","type":"Real"},{"key":"C_1","type":"Real"},{"key":"Lambda_1","type":"Real"},{"key":"c_2","type":"Real"},{"key":"C_2","type":"Real"},{"key":"Lambda_2","type":"Real"}],"uses_definitions":["D-S7A-COMMON-TWO","D-S7A-WEIGHT-TYPE"],"source_anchors":[],"hypotheses":[{"key":"typed_a_1","proposition":{"def":{"id":"D-S7A-WEIGHT-TYPE","args":[{"var":"a_1"},{"var":"c_1"},{"var":"C_1"},{"var":"Lambda_1"}]}}},{"key":"typed_a_2","proposition":{"def":{"id":"D-S7A-WEIGHT-TYPE","args":[{"var":"a_2"},{"var":"c_2"},{"var":"C_2"},{"var":"Lambda_2"}]}}}],"witnesses":[{"key":"c","type":"Real","depends_on":["c_1","C_1","Lambda_1","c_2","C_2","Lambda_2"]},{"key":"C","type":"Real","depends_on":["c_1","C_1","Lambda_1","c_2","C_2","Lambda_2"]},{"key":"Lambda","type":"Real","depends_on":["c_1","C_1","Lambda_1","c_2","C_2","Lambda_2"]}],"conclusions":[{"key":"first_common_type","proposition":{"def":{"id":"D-S7A-WEIGHT-TYPE","args":[{"var":"a_1"},{"var":"c"},{"var":"C"},{"var":"Lambda"}]}}},{"key":"second_common_type","proposition":{"def":{"id":"D-S7A-WEIGHT-TYPE","args":[{"var":"a_2"},{"var":"c"},{"var":"C"},{"var":"Lambda"}]}}}],"premises":[],"witness_realizations":{"c":{"proj":{"value":{"def":{"id":"D-S7A-COMMON-TWO","args":[{"var":"c_1"},{"var":"C_1"},{"var":"Lambda_1"},{"var":"c_2"},{"var":"C_2"},{"var":"Lambda_2"}]}},"index":0}},"C":{"proj":{"value":{"def":{"id":"D-S7A-COMMON-TWO","args":[{"var":"c_1"},{"var":"C_1"},{"var":"Lambda_1"},{"var":"c_2"},{"var":"C_2"},{"var":"Lambda_2"}]}},"index":1}},"Lambda":{"proj":{"value":{"def":{"id":"D-S7A-COMMON-TWO","args":[{"var":"c_1"},{"var":"C_1"},{"var":"Lambda_1"},{"var":"c_2"},{"var":"C_2"},{"var":"Lambda_2"}]}},"index":2}}},"proof_ref":"### P-051E — two-weight prime-power maximum"}
```

- Prenex statement: fix nonnegative multiplicative \(a_1,a_2\) having
  common witnesses \(c,C,\Lambda>0\) for type \(\tau^{-1}\) and their local
  bounds. Define \(m(p^i)=\max(a_1(p^i),a_2(p^i))\), extended
  multiplicatively. Then \(m\) is nonnegative multiplicative, has the same
  type with common witnesses \((c,C,\Lambda)\), and for every positive
  integer \(K\),
  \[
  m(K)\ge a_1(K),\qquad m(K)\ge a_2(K).
  \tag{P051E}
  \]
- Exact subject: `SUB-P051E-MAX` is this literal prime-power maximum and its
  multiplicative extension.
- Premise maps: the two typed inputs map slotwise to \(a_1,a_2\) with the
  displayed common witnesses; no shift result is consumed.
- Derivation certificate: the maximum preserves the shared main term and
  common error bound prime-powerwise; multiply the local domination
  inequalities over the factorization of \(K\).
- Source/S2 anchor: S2 R2.4, (R2.12), and S2B R2(3).
- Definitions used: D-014, D-015.

### P-051V — full-domain modifier normalization

```mathminer-s3
{"schema":"mathminer.s3/1","id":"P-051V","kind":"PROPOSITION","binders":[{"key":"theta","type":"Real"},{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"}],"uses_definitions":["D-S7A-MODIFIER","D-S7A-V"],"source_anchors":[],"hypotheses":[{"key":"theta_ge_2","proposition":{"op":{"name":"ge","args":[{"var":"theta"},{"lit":{"type":"Real","value":"2"}}]}}},{"key":"y_pos","proposition":{"op":{"name":"gt","args":[{"var":"y"},{"lit":{"type":"Real","value":"0"}}]}}},{"key":"y_lt_1","proposition":{"op":{"name":"lt","args":[{"var":"y"},{"lit":{"type":"Real","value":"1"}}]}}},{"key":"k_ge_1","proposition":{"op":{"name":"ge","args":[{"var":"k"},{"lit":{"type":"Nat","value":"1"}}]}}},{"key":"sigma_ge_theta","proposition":{"op":{"name":"ge","args":[{"var":"sigma"},{"var":"theta"}]}}}],"witnesses":[],"conclusions":[{"key":"modifier_normalization","proposition":{"def":{"id":"D-S7A-MODIFIER","args":[{"def":{"id":"D-S7A-V","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"}]}}]}}}],"premises":[],"witness_realizations":{},"proof_ref":"### P-051V — full-domain modifier normalization"}
```

- Exact prefix:

  ```text
  forall theta in R_{>=2}, forall y in (0,1),
  forall k in N_{>=1}, forall sigma in R_{>=theta},
  define v_k(n)=y^{Omega(n,theta^k)} chi(n,sigma);
  v_k is nonnegative multiplicative, v_k(1)=1, and
  forall prime p, forall j in N, 0 <= v_k(p^j) <= 1.
  ```

- Prenex statement: for the displayed typed family and every
  \(n\in\mathbb N_{>0}\), define
  \(v_k(n)=y^{\Omega(n,\theta^k)}\chi(n,\sigma)\). Then \(v_k\) is a
  nonnegative multiplicative function on its full domain,
  \(v_k(1)=1\), and for every prime \(p\) and every
  \(j\in\mathbb N\),
  \[
  0\le v_k(p^j)\le1.
  \tag{P051V}
  \]
- Exact subject: `SUB-P051V-MODIFIER` is the literal D-015 modifier \(v_k\)
  on all positive integers, not only its prime-power restriction.
- Premise maps: none (bounded root).
- Derivation certificate: D-003 gives
  \(\Omega(1,\theta^k)=0\), while D-002 gives
  \(\chi(1,\sigma)=1\); hence
  \(v_k(1)=y^0\cdot1=1\). If \(r,s>0\) are coprime, coprime additivity of
  \(\Omega(\mathord\cdot,\theta^k)\) and multiplicativity of
  \(\chi(\mathord\cdot,\sigma)\) give
  \[
  v_k(rs)=y^{\Omega(r,\theta^k)+\Omega(s,\theta^k)}
           \chi(r,\sigma)\chi(s,\sigma)=v_k(r)v_k(s).
  \]
  Finally \(0<y<1\), \(\Omega(p^j,\theta^k)\in\mathbb N\), and
  \(\chi(p^j,\sigma)\in\{0,1\}\), so the displayed full \(j\ge0\)
  prime-power bound holds.
- Source/S2 anchor: accepted definitions D-002/D-003/D-015 and S2 R2.4,
  (R2.11).
- Definitions used: D-002, D-003, D-015.

### P-051F1 — exact instantiation \(a_0\to w_1\)

```mathminer-s3
{"schema":"mathminer.s3/1","id":"P-051F1","kind":"PROPOSITION","binders":[],"uses_definitions":["D-S7A-A0","D-S7A-ONE","D-S7A-SHIFT","D-S7A-W1","D-S7A-WEIGHT-TYPE"],"source_anchors":[],"hypotheses":[],"witnesses":[{"key":"c_1","type":"Real","depends_on":[]},{"key":"C_1","type":"Real","depends_on":[]},{"key":"Lambda_1","type":"Real","depends_on":[]}],"conclusions":[{"key":"weight_type","proposition":{"def":{"id":"D-S7A-WEIGHT-TYPE","args":[{"def":{"id":"D-S7A-W1","args":[]}},{"var":"c_1"},{"var":"C_1"},{"var":"Lambda_1"}]}}},{"key":"dominates_base","proposition":{"forall":{"binders":[{"key":"K","type":"Nat"}],"body":{"op":{"name":"implies","args":[{"op":{"name":"gt","args":[{"var":"K"},{"lit":{"type":"Nat","value":"0"}}]}},{"op":{"name":"ge","args":[{"app":{"fn":{"def":{"id":"D-S7A-W1","args":[]}},"args":[{"var":"K"}]}},{"app":{"fn":{"def":{"id":"D-S7A-A0","args":[]}},"args":[{"var":"K"}]}}]}}]}}}}},{"key":"dominates_shift","proposition":{"forall":{"binders":[{"key":"K","type":"Nat"}],"body":{"op":{"name":"implies","args":[{"op":{"name":"gt","args":[{"var":"K"},{"lit":{"type":"Nat","value":"0"}}]}},{"op":{"name":"ge","args":[{"app":{"fn":{"def":{"id":"D-S7A-W1","args":[]}},"args":[{"var":"K"}]}},{"app":{"fn":{"def":{"id":"D-S7A-SHIFT","args":[{"def":{"id":"D-S7A-A0","args":[]}},{"def":{"id":"D-S7A-ONE","args":[]}}]}},"args":[{"var":"K"}]}}]}}]}}}}}],"premises":[{"id":"MAP-P051F1-P051A","producer":"P-051A","closure_role":"REQUIRED","binder_map":{},"hypothesis_map":{},"witness_map":{"c_0":"f1_c0","C_0":"f1_C0","Lambda_0":"f1_L0"},"consume":["base_type","one_modifier"]},{"id":"MAP-P051F1-P051C","producer":"P-051C","closure_role":"REQUIRED","binder_map":{"a":{"def":{"id":"D-S7A-A0","args":[]}},"c_a":{"var":"f1_c0"},"C_a":{"var":"f1_C0"},"Lambda_a":{"var":"f1_L0"},"b":{"def":{"id":"D-S7A-ONE","args":[]}}},"hypothesis_map":{"typed_a":{"premise":"MAP-P051F1-P051A","conclusion":"base_type"},"modifier_b":{"premise":"MAP-P051F1-P051A","conclusion":"one_modifier"}},"witness_map":{"c_sh":"f1_csh","C_sh":"f1_Csh","Lambda_sh":"f1_Lsh"},"consume":["shift_type"]},{"id":"MAP-P051F1-P051D","producer":"P-051D","closure_role":"REQUIRED","binder_map":{"a":{"def":{"id":"D-S7A-A0","args":[]}},"c_a":{"var":"f1_c0"},"C_a":{"var":"f1_C0"},"Lambda_a":{"var":"f1_L0"},"b":{"def":{"id":"D-S7A-ONE","args":[]}}},"hypothesis_map":{"typed_a":{"premise":"MAP-P051F1-P051A","conclusion":"base_type"},"modifier_b":{"premise":"MAP-P051F1-P051A","conclusion":"one_modifier"}},"witness_map":{"c_hat":"f1_chat","C_hat":"f1_Chat","Lambda_hat":"f1_Lhat"},"consume":["hat_type","dominates_shift","dominates_input"]}],"witness_realizations":{"c_1":{"var":"f1_chat"},"C_1":{"var":"f1_Chat"},"Lambda_1":{"var":"f1_Lhat"}},"proof_ref":"### P-051F1 — exact instantiation \\(a_0\\to w_1\\)"}
```

- Prenex statement: the exact D-015 function
  \(w_1=\widehat{\mathcal S}[a_0,1]\) is nonnegative multiplicative, typed
  and locally bounded by absolute witnesses, and
  \[
  w_1(K)\ge a_0(K),\qquad
  w_1(K)\ge\mathcal S[a_0,1](K)
  \]
  for every \(K>0\).
- Exact subject: `SUB-P051F1-W1` is D-015's \(w_1\).
- Premise maps: `MAP-P051F1-P051A` supplies \(a:=a_0\) and its witnesses;
  `MAP-P051F1-P051C` uses \((a,b):=(a_0,1)\);
  `MAP-P051F1-P051D` uses the same pair and consumes the hat type and
  domination.  The bound \(0\le1\le1\) discharges the modifier hypothesis.
- Source/S2 anchor: S2 R2.4, (R2.10).
- Definitions used: D-015.

### P-051F2 — exact instantiation \((w_1,v_k)\to w_{2,k}\)

```mathminer-s3
{"schema":"mathminer.s3/1","id":"P-051F2","kind":"PROPOSITION","binders":[{"key":"theta","type":"Real"},{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"}],"uses_definitions":["D-S7A-SHIFT","D-S7A-V","D-S7A-W1","D-S7A-W2","D-S7A-WEIGHT-TYPE"],"source_anchors":[],"hypotheses":[{"key":"theta_ge_2","proposition":{"op":{"name":"ge","args":[{"var":"theta"},{"lit":{"type":"Real","value":"2"}}]}}},{"key":"y_pos","proposition":{"op":{"name":"gt","args":[{"var":"y"},{"lit":{"type":"Real","value":"0"}}]}}},{"key":"y_lt_1","proposition":{"op":{"name":"lt","args":[{"var":"y"},{"lit":{"type":"Real","value":"1"}}]}}},{"key":"k_ge_1","proposition":{"op":{"name":"ge","args":[{"var":"k"},{"lit":{"type":"Nat","value":"1"}}]}}},{"key":"sigma_ge_theta","proposition":{"op":{"name":"ge","args":[{"var":"sigma"},{"var":"theta"}]}}}],"witnesses":[{"key":"c_2","type":"Real","depends_on":[]},{"key":"C_2","type":"Real","depends_on":[]},{"key":"Lambda_2","type":"Real","depends_on":[]}],"conclusions":[{"key":"weight_type","proposition":{"def":{"id":"D-S7A-WEIGHT-TYPE","args":[{"def":{"id":"D-S7A-W2","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"}]}},{"var":"c_2"},{"var":"C_2"},{"var":"Lambda_2"}]}}},{"key":"dominates_w1","proposition":{"forall":{"binders":[{"key":"K","type":"Nat"}],"body":{"op":{"name":"implies","args":[{"op":{"name":"gt","args":[{"var":"K"},{"lit":{"type":"Nat","value":"0"}}]}},{"op":{"name":"ge","args":[{"app":{"fn":{"def":{"id":"D-S7A-W2","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"}]}},"args":[{"var":"K"}]}},{"app":{"fn":{"def":{"id":"D-S7A-W1","args":[]}},"args":[{"var":"K"}]}}]}}]}}}}},{"key":"dominates_shift","proposition":{"forall":{"binders":[{"key":"K","type":"Nat"}],"body":{"op":{"name":"implies","args":[{"op":{"name":"gt","args":[{"var":"K"},{"lit":{"type":"Nat","value":"0"}}]}},{"op":{"name":"ge","args":[{"app":{"fn":{"def":{"id":"D-S7A-W2","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"}]}},"args":[{"var":"K"}]}},{"app":{"fn":{"def":{"id":"D-S7A-SHIFT","args":[{"def":{"id":"D-S7A-W1","args":[]}},{"def":{"id":"D-S7A-V","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"}]}}]}},"args":[{"var":"K"}]}}]}}]}}}}}],"premises":[{"id":"MAP-P051F2-P051F1","producer":"P-051F1","closure_role":"REQUIRED","binder_map":{},"hypothesis_map":{},"witness_map":{"c_1":"f2_c1","C_1":"f2_C1","Lambda_1":"f2_L1"},"consume":["weight_type"]},{"id":"MAP-P051F2-P051V","producer":"P-051V","closure_role":"REQUIRED","binder_map":{"theta":{"var":"theta"},"y":{"var":"y"},"k":{"var":"k"},"sigma":{"var":"sigma"}},"hypothesis_map":{"theta_ge_2":{"hypothesis":"theta_ge_2"},"y_pos":{"hypothesis":"y_pos"},"y_lt_1":{"hypothesis":"y_lt_1"},"k_ge_1":{"hypothesis":"k_ge_1"},"sigma_ge_theta":{"hypothesis":"sigma_ge_theta"}},"witness_map":{},"consume":["modifier_normalization"]},{"id":"MAP-P051F2-P051C","producer":"P-051C","closure_role":"REQUIRED","binder_map":{"a":{"def":{"id":"D-S7A-W1","args":[]}},"c_a":{"var":"f2_c1"},"C_a":{"var":"f2_C1"},"Lambda_a":{"var":"f2_L1"},"b":{"def":{"id":"D-S7A-V","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"}]}}},"hypothesis_map":{"typed_a":{"premise":"MAP-P051F2-P051F1","conclusion":"weight_type"},"modifier_b":{"premise":"MAP-P051F2-P051V","conclusion":"modifier_normalization"}},"witness_map":{"c_sh":"f2_csh","C_sh":"f2_Csh","Lambda_sh":"f2_Lsh"},"consume":["shift_type"]},{"id":"MAP-P051F2-P051D","producer":"P-051D","closure_role":"REQUIRED","binder_map":{"a":{"def":{"id":"D-S7A-W1","args":[]}},"c_a":{"var":"f2_c1"},"C_a":{"var":"f2_C1"},"Lambda_a":{"var":"f2_L1"},"b":{"def":{"id":"D-S7A-V","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"}]}}},"hypothesis_map":{"typed_a":{"premise":"MAP-P051F2-P051F1","conclusion":"weight_type"},"modifier_b":{"premise":"MAP-P051F2-P051V","conclusion":"modifier_normalization"}},"witness_map":{"c_hat":"f2_chat","C_hat":"f2_Chat","Lambda_hat":"f2_Lhat"},"consume":["hat_type","dominates_shift","dominates_input"]}],"witness_realizations":{"c_2":{"var":"f2_chat"},"C_2":{"var":"f2_Chat"},"Lambda_2":{"var":"f2_Lhat"}},"proof_ref":"### P-051F2 — exact instantiation \\((w_1,v_k)\\to w_{2,k}\\)"}
```

- Prenex statement: using the absolute witnesses of P-051F1, there exist
  witnesses chosen before the entire
  \((\theta,y,k,\sigma)\)-family such that, for
  \(\theta\ge2,0<y<1,k\ge1,\sigma\ge\theta\), P-051V supplies the exact
  D-015 modifier \(v_k\) as nonnegative multiplicative, normalized by
  \(v_k(1)=1\), with \(0\le v_k(p^j)\le1\) for every prime \(p\) and
  every \(j\in\mathbb N\), and
  \(w_{2,k}=\widehat{\mathcal S}[w_1,v_k]\) is nonnegative multiplicative,
  typed and locally bounded by those witnesses, with
  \[
  w_{2,k}(K)\ge w_1(K),\qquad
  w_{2,k}(K)\ge\mathcal S[w_1,v_k](K)
  \]
  for all \(K>0\).
- Exact subject: `SUB-P051F2-W2` is the D-015 family \(w_{2,k}\).
- Premise maps: `MAP-P051F2-P051F1` supplies \(w_1\) and its witnesses.
  `MAP-P051F2-P051V` binds \((\theta,y,k,\sigma)\) identically and consumes,
  slot by slot, \(b:=v_k\), \(b\) nonnegative multiplicative,
  \(b(1)=1\), and
  \(\forall p\text{ prime}\;\forall j\in\mathbb N,
  0\le b(p^j)\le1\). `MAP-P051F2-P051C` takes
  \((a,b):=(w_1,v_k)\), with those three modifier hypotheses discharged by
  P-051V, and selects its output witnesses before
  \((\theta,y,k,\sigma)\); `MAP-P051F2-P051D` consumes the exact hat
  type/domination with the identical modifier map.
- Source/S2 anchor: S2 R2.4, (R2.11).
- Definitions used: D-002, D-003, D-015.

### P-051F3 — exact instantiation \((w_1,w_{2,k})\to w_{3,k}\)

```mathminer-s3
{"schema":"mathminer.s3/1","id":"P-051F3","kind":"PROPOSITION","binders":[{"key":"theta","type":"Real"},{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"}],"uses_definitions":["D-S7A-W1","D-S7A-W2","D-S7A-W3","D-S7A-WEIGHT-TYPE"],"source_anchors":[],"hypotheses":[{"key":"theta_ge_2","proposition":{"op":{"name":"ge","args":[{"var":"theta"},{"lit":{"type":"Real","value":"2"}}]}}},{"key":"y_pos","proposition":{"op":{"name":"gt","args":[{"var":"y"},{"lit":{"type":"Real","value":"0"}}]}}},{"key":"y_lt_1","proposition":{"op":{"name":"lt","args":[{"var":"y"},{"lit":{"type":"Real","value":"1"}}]}}},{"key":"k_ge_1","proposition":{"op":{"name":"ge","args":[{"var":"k"},{"lit":{"type":"Nat","value":"1"}}]}}},{"key":"sigma_ge_theta","proposition":{"op":{"name":"ge","args":[{"var":"sigma"},{"var":"theta"}]}}}],"witnesses":[{"key":"c_3","type":"Real","depends_on":[]},{"key":"C_3","type":"Real","depends_on":[]},{"key":"Lambda_3","type":"Real","depends_on":[]}],"conclusions":[{"key":"weight_type","proposition":{"def":{"id":"D-S7A-WEIGHT-TYPE","args":[{"def":{"id":"D-S7A-W3","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"}]}},{"var":"c_3"},{"var":"C_3"},{"var":"Lambda_3"}]}}},{"key":"dominates_w1","proposition":{"forall":{"binders":[{"key":"K","type":"Nat"}],"body":{"op":{"name":"implies","args":[{"op":{"name":"gt","args":[{"var":"K"},{"lit":{"type":"Nat","value":"0"}}]}},{"op":{"name":"ge","args":[{"app":{"fn":{"def":{"id":"D-S7A-W3","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"}]}},"args":[{"var":"K"}]}},{"app":{"fn":{"def":{"id":"D-S7A-W1","args":[]}},"args":[{"var":"K"}]}}]}}]}}}}},{"key":"dominates_w2","proposition":{"forall":{"binders":[{"key":"K","type":"Nat"}],"body":{"op":{"name":"implies","args":[{"op":{"name":"gt","args":[{"var":"K"},{"lit":{"type":"Nat","value":"0"}}]}},{"op":{"name":"ge","args":[{"app":{"fn":{"def":{"id":"D-S7A-W3","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"}]}},"args":[{"var":"K"}]}},{"app":{"fn":{"def":{"id":"D-S7A-W2","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"}]}},"args":[{"var":"K"}]}}]}}]}}}}}],"premises":[{"id":"MAP-P051F3-P051F1","producer":"P-051F1","closure_role":"REQUIRED","binder_map":{},"hypothesis_map":{},"witness_map":{"c_1":"f3_c1","C_1":"f3_C1","Lambda_1":"f3_L1"},"consume":["weight_type"]},{"id":"MAP-P051F3-P051F2","producer":"P-051F2","closure_role":"REQUIRED","binder_map":{"theta":{"var":"theta"},"y":{"var":"y"},"k":{"var":"k"},"sigma":{"var":"sigma"}},"hypothesis_map":{"theta_ge_2":{"hypothesis":"theta_ge_2"},"y_pos":{"hypothesis":"y_pos"},"y_lt_1":{"hypothesis":"y_lt_1"},"k_ge_1":{"hypothesis":"k_ge_1"},"sigma_ge_theta":{"hypothesis":"sigma_ge_theta"}},"witness_map":{"c_2":"f3_c2","C_2":"f3_C2","Lambda_2":"f3_L2"},"consume":["weight_type"]},{"id":"MAP-P051F3-P051E0","producer":"P-051E0","closure_role":"REQUIRED","binder_map":{"a_1":{"def":{"id":"D-S7A-W1","args":[]}},"a_2":{"def":{"id":"D-S7A-W2","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"}]}},"c_1":{"var":"f3_c1"},"C_1":{"var":"f3_C1"},"Lambda_1":{"var":"f3_L1"},"c_2":{"var":"f3_c2"},"C_2":{"var":"f3_C2"},"Lambda_2":{"var":"f3_L2"}},"hypothesis_map":{"typed_a_1":{"premise":"MAP-P051F3-P051F1","conclusion":"weight_type"},"typed_a_2":{"premise":"MAP-P051F3-P051F2","conclusion":"weight_type"}},"witness_map":{"c":"f3_c","C":"f3_C","Lambda":"f3_L"},"consume":["first_common_type","second_common_type"]},{"id":"MAP-P051F3-P051E","producer":"P-051E","closure_role":"REQUIRED","binder_map":{"a_1":{"def":{"id":"D-S7A-W1","args":[]}},"a_2":{"def":{"id":"D-S7A-W2","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"}]}},"c":{"var":"f3_c"},"C":{"var":"f3_C"},"Lambda":{"var":"f3_L"}},"hypothesis_map":{"typed_a_1":{"premise":"MAP-P051F3-P051E0","conclusion":"first_common_type"},"typed_a_2":{"premise":"MAP-P051F3-P051E0","conclusion":"second_common_type"}},"witness_map":{},"consume":["maximum_type","dominates_first","dominates_second"]}],"witness_realizations":{"c_3":{"var":"f3_c"},"C_3":{"var":"f3_C"},"Lambda_3":{"var":"f3_L"}},"proof_ref":"### P-051F3 — exact instantiation \\((w_1,w_{2,k})\\to w_{3,k}\\)"}
```

- Prenex statement: after choosing common witnesses for P-051F1 and
  P-051F2, the exact D-015 prime-power maximum \(w_{3,k}\), extended
  multiplicatively, is nonnegative multiplicative, typed and locally bounded
  uniformly before \((\theta,y,k,\sigma)\), and for every \(K>0\),
  \[
  w_{3,k}(K)\ge w_1(K),\qquad w_{3,k}(K)\ge w_{2,k}(K).
  \]
- Exact subject: `SUB-P051F3-W3` is D-015's \(w_{3,k}\).
- Premise maps: `MAP-P051F3-P051F1` and `MAP-P051F3-P051F2` supply the two
  typed weights and commonized witnesses; `MAP-P051F3-P051E` takes
  \((a_1,a_2,m):=(w_1,w_{2,k},w_{3,k})\) and consumes its exact type and two
  integer dominations.
- Source/S2 anchor: S2 R2.4, (R2.12).
- Definitions used: D-015.

### P-051F4 — exact instantiation \((w_{3,k},v_k)\to w_{4,k}\)

```mathminer-s3
{"schema":"mathminer.s3/1","id":"P-051F4","kind":"PROPOSITION","binders":[{"key":"theta","type":"Real"},{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"}],"uses_definitions":["D-S7A-F4-W","D-S7A-SHIFT","D-S7A-V","D-S7A-W3","D-S7A-W4","D-S7A-WEIGHT-TYPE"],"source_anchors":[],"hypotheses":[{"key":"theta_ge_2","proposition":{"op":{"name":"ge","args":[{"var":"theta"},{"lit":{"type":"Real","value":"2"}}]}}},{"key":"y_pos","proposition":{"op":{"name":"gt","args":[{"var":"y"},{"lit":{"type":"Real","value":"0"}}]}}},{"key":"y_lt_1","proposition":{"op":{"name":"lt","args":[{"var":"y"},{"lit":{"type":"Real","value":"1"}}]}}},{"key":"k_ge_1","proposition":{"op":{"name":"ge","args":[{"var":"k"},{"lit":{"type":"Nat","value":"1"}}]}}},{"key":"sigma_ge_theta","proposition":{"op":{"name":"ge","args":[{"var":"sigma"},{"var":"theta"}]}}}],"witnesses":[{"key":"c_4","type":"Real","depends_on":[]},{"key":"C_4","type":"Real","depends_on":[]},{"key":"Lambda_4","type":"Real","depends_on":[]}],"conclusions":[{"key":"weight_type","proposition":{"def":{"id":"D-S7A-WEIGHT-TYPE","args":[{"def":{"id":"D-S7A-W4","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"}]}},{"var":"c_4"},{"var":"C_4"},{"var":"Lambda_4"}]}}},{"key":"dominates_w3","proposition":{"forall":{"binders":[{"key":"K","type":"Nat"}],"body":{"op":{"name":"implies","args":[{"op":{"name":"gt","args":[{"var":"K"},{"lit":{"type":"Nat","value":"0"}}]}},{"op":{"name":"ge","args":[{"app":{"fn":{"def":{"id":"D-S7A-W4","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"}]}},"args":[{"var":"K"}]}},{"app":{"fn":{"def":{"id":"D-S7A-W3","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"}]}},"args":[{"var":"K"}]}}]}}]}}}}},{"key":"dominates_shift","proposition":{"forall":{"binders":[{"key":"K","type":"Nat"}],"body":{"op":{"name":"implies","args":[{"op":{"name":"gt","args":[{"var":"K"},{"lit":{"type":"Nat","value":"0"}}]}},{"op":{"name":"ge","args":[{"app":{"fn":{"def":{"id":"D-S7A-W4","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"}]}},"args":[{"var":"K"}]}},{"app":{"fn":{"def":{"id":"D-S7A-SHIFT","args":[{"def":{"id":"D-S7A-W3","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"}]}},{"def":{"id":"D-S7A-V","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"}]}}]}},"args":[{"var":"K"}]}}]}}]}}}}}],"premises":[{"id":"MAP-P051F4-P051F3","producer":"P-051F3","closure_role":"REQUIRED","binder_map":{"theta":{"var":"theta"},"y":{"var":"y"},"k":{"var":"k"},"sigma":{"var":"sigma"}},"hypothesis_map":{"theta_ge_2":{"hypothesis":"theta_ge_2"},"y_pos":{"hypothesis":"y_pos"},"y_lt_1":{"hypothesis":"y_lt_1"},"k_ge_1":{"hypothesis":"k_ge_1"},"sigma_ge_theta":{"hypothesis":"sigma_ge_theta"}},"witness_map":{"c_3":"f4_c3","C_3":"f4_C3","Lambda_3":"f4_L3"},"consume":["weight_type"]},{"id":"MAP-P051F4-P051V","producer":"P-051V","closure_role":"REQUIRED","binder_map":{"theta":{"var":"theta"},"y":{"var":"y"},"k":{"var":"k"},"sigma":{"var":"sigma"}},"hypothesis_map":{"theta_ge_2":{"hypothesis":"theta_ge_2"},"y_pos":{"hypothesis":"y_pos"},"y_lt_1":{"hypothesis":"y_lt_1"},"k_ge_1":{"hypothesis":"k_ge_1"},"sigma_ge_theta":{"hypothesis":"sigma_ge_theta"}},"witness_map":{},"consume":["modifier_normalization"]},{"id":"MAP-P051F4-P051C","producer":"P-051C","closure_role":"REQUIRED","binder_map":{"a":{"def":{"id":"D-S7A-W3","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"}]}},"c_a":{"var":"f4_c3"},"C_a":{"var":"f4_C3"},"Lambda_a":{"var":"f4_L3"},"b":{"def":{"id":"D-S7A-V","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"}]}}},"hypothesis_map":{"typed_a":{"premise":"MAP-P051F4-P051F3","conclusion":"weight_type"},"modifier_b":{"premise":"MAP-P051F4-P051V","conclusion":"modifier_normalization"}},"witness_map":{"c_sh":"f4_csh","C_sh":"f4_Csh","Lambda_sh":"f4_Lsh"},"consume":["shift_type"]},{"id":"MAP-P051F4-P051D","producer":"P-051D","closure_role":"REQUIRED","binder_map":{"a":{"def":{"id":"D-S7A-W3","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"}]}},"c_a":{"var":"f4_c3"},"C_a":{"var":"f4_C3"},"Lambda_a":{"var":"f4_L3"},"b":{"def":{"id":"D-S7A-V","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"}]}}},"hypothesis_map":{"typed_a":{"premise":"MAP-P051F4-P051F3","conclusion":"weight_type"},"modifier_b":{"premise":"MAP-P051F4-P051V","conclusion":"modifier_normalization"}},"witness_map":{"c_hat":"f4_chat","C_hat":"f4_Chat","Lambda_hat":"f4_Lhat"},"consume":["hat_type","dominates_shift","dominates_input"]}],"witness_realizations":{"c_4":{"proj":{"value":{"def":{"id":"D-S7A-F4-W","args":[]}},"index":0}},"C_4":{"proj":{"value":{"def":{"id":"D-S7A-F4-W","args":[]}},"index":1}},"Lambda_4":{"proj":{"value":{"def":{"id":"D-S7A-F4-W","args":[]}},"index":2}}},"proof_ref":"### P-051F4 — exact instantiation \\((w_{3,k},v_k)\\to w_{4,k}\\)"}
```

- Prenex statement: using the uniform P-051F3 witnesses, there exist
  witnesses chosen before the entire \((\theta,y,k,\sigma)\)-family such
  that the exact D-015 function
  \(w_{4,k}=\widehat{\mathcal S}[w_{3,k},v_k]\) is nonnegative
  multiplicative, typed and locally bounded, and
  \[
  w_{4,k}(K)\ge w_{3,k}(K),\qquad
  w_{4,k}(K)\ge\mathcal S[w_{3,k},v_k](K)
  \]
  for every \(K>0\).
- Exact subject: `SUB-P051F4-W4` is D-015's \(w_{4,k}\).
- Premise maps: `MAP-P051F4-P051F3` supplies \(w_{3,k}\) and its uniform
  witnesses. `MAP-P051F4-P051V` binds \((\theta,y,k,\sigma)\) identically
  and consumes, slot by slot, \(b:=v_k\), \(b\) nonnegative multiplicative,
  \(b(1)=1\), and
  \(\forall p\text{ prime}\;\forall j\in\mathbb N,
  0\le b(p^j)\le1\). `MAP-P051F4-P051C` takes
  \((a,b):=(w_{3,k},v_k)\), with those modifier hypotheses discharged by
  P-051V; `MAP-P051F4-P051D` consumes the exact hat type and domination with
  the identical modifier map.
- Source/S2 anchor: S2 R2.4, (R2.13).
- Definitions used: D-002, D-003, D-015.

### P-051G — common-witness family consolidation

```mathminer-s3
{"schema":"mathminer.s3/1","id":"P-051G","kind":"PROPOSITION","binders":[{"key":"theta","type":"Real"},{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"}],"uses_definitions":["D-S7A-A0","D-S7A-COMMON-FIVE","D-S7A-MODIFIER","D-S7A-REAL-POWER","D-S7A-V","D-S7A-W1","D-S7A-W2","D-S7A-W3","D-S7A-W4","D-S7A-WEIGHT-TYPE"],"source_anchors":[],"hypotheses":[{"key":"theta_ge_2","proposition":{"op":{"name":"ge","args":[{"var":"theta"},{"lit":{"type":"Real","value":"2"}}]}}},{"key":"y_pos","proposition":{"op":{"name":"gt","args":[{"var":"y"},{"lit":{"type":"Real","value":"0"}}]}}},{"key":"y_lt_1","proposition":{"op":{"name":"lt","args":[{"var":"y"},{"lit":{"type":"Real","value":"1"}}]}}},{"key":"k_ge_1","proposition":{"op":{"name":"ge","args":[{"var":"k"},{"lit":{"type":"Nat","value":"1"}}]}}},{"key":"sigma_ge_theta","proposition":{"op":{"name":"ge","args":[{"var":"sigma"},{"var":"theta"}]}}}],"witnesses":[{"key":"c_star","type":"Real","depends_on":[]},{"key":"C_star","type":"Real","depends_on":[]},{"key":"Lambda_star","type":"Real","depends_on":[]}],"conclusions":[{"key":"base_type","proposition":{"def":{"id":"D-S7A-WEIGHT-TYPE","args":[{"def":{"id":"D-S7A-A0","args":[]}},{"var":"c_star"},{"var":"C_star"},{"var":"Lambda_star"}]}}},{"key":"w1_type","proposition":{"def":{"id":"D-S7A-WEIGHT-TYPE","args":[{"def":{"id":"D-S7A-W1","args":[]}},{"var":"c_star"},{"var":"C_star"},{"var":"Lambda_star"}]}}},{"key":"w2_type","proposition":{"def":{"id":"D-S7A-WEIGHT-TYPE","args":[{"def":{"id":"D-S7A-W2","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"}]}},{"var":"c_star"},{"var":"C_star"},{"var":"Lambda_star"}]}}},{"key":"w3_type","proposition":{"def":{"id":"D-S7A-WEIGHT-TYPE","args":[{"def":{"id":"D-S7A-W3","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"}]}},{"var":"c_star"},{"var":"C_star"},{"var":"Lambda_star"}]}}},{"key":"w4_type","proposition":{"def":{"id":"D-S7A-WEIGHT-TYPE","args":[{"def":{"id":"D-S7A-W4","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"}]}},{"var":"c_star"},{"var":"C_star"},{"var":"Lambda_star"}]}}},{"key":"common_lambda_floor","proposition":{"op":{"name":"ge","args":[{"var":"Lambda_star"},{"op":{"name":"add","args":[{"lit":{"type":"Real","value":"1"}},{"op":{"name":"mul","args":[{"var":"C_star"},{"def":{"id":"D-S7A-REAL-POWER","args":[{"lit":{"type":"Real","value":"2"}},{"op":{"name":"neg","args":[{"var":"c_star"}]}}]}}]}}]}}]}}},{"key":"modifier_normalization","proposition":{"def":{"id":"D-S7A-MODIFIER","args":[{"def":{"id":"D-S7A-V","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"}]}}]}}},{"key":"dominates_base","proposition":{"forall":{"binders":[{"key":"K","type":"Nat"}],"body":{"op":{"name":"implies","args":[{"op":{"name":"gt","args":[{"var":"K"},{"lit":{"type":"Nat","value":"0"}}]}},{"op":{"name":"ge","args":[{"app":{"fn":{"def":{"id":"D-S7A-W1","args":[]}},"args":[{"var":"K"}]}},{"app":{"fn":{"def":{"id":"D-S7A-A0","args":[]}},"args":[{"var":"K"}]}}]}}]}}}}},{"key":"dominates_w1_by_w2","proposition":{"forall":{"binders":[{"key":"K","type":"Nat"}],"body":{"op":{"name":"implies","args":[{"op":{"name":"gt","args":[{"var":"K"},{"lit":{"type":"Nat","value":"0"}}]}},{"op":{"name":"ge","args":[{"app":{"fn":{"def":{"id":"D-S7A-W2","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"}]}},"args":[{"var":"K"}]}},{"app":{"fn":{"def":{"id":"D-S7A-W1","args":[]}},"args":[{"var":"K"}]}}]}}]}}}}},{"key":"dominates_w1_by_w3","proposition":{"forall":{"binders":[{"key":"K","type":"Nat"}],"body":{"op":{"name":"implies","args":[{"op":{"name":"gt","args":[{"var":"K"},{"lit":{"type":"Nat","value":"0"}}]}},{"op":{"name":"ge","args":[{"app":{"fn":{"def":{"id":"D-S7A-W3","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"}]}},"args":[{"var":"K"}]}},{"app":{"fn":{"def":{"id":"D-S7A-W1","args":[]}},"args":[{"var":"K"}]}}]}}]}}}}},{"key":"dominates_w2_by_w3","proposition":{"forall":{"binders":[{"key":"K","type":"Nat"}],"body":{"op":{"name":"implies","args":[{"op":{"name":"gt","args":[{"var":"K"},{"lit":{"type":"Nat","value":"0"}}]}},{"op":{"name":"ge","args":[{"app":{"fn":{"def":{"id":"D-S7A-W3","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"}]}},"args":[{"var":"K"}]}},{"app":{"fn":{"def":{"id":"D-S7A-W2","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"}]}},"args":[{"var":"K"}]}}]}}]}}}}},{"key":"dominates_w3_by_w4","proposition":{"forall":{"binders":[{"key":"K","type":"Nat"}],"body":{"op":{"name":"implies","args":[{"op":{"name":"gt","args":[{"var":"K"},{"lit":{"type":"Nat","value":"0"}}]}},{"op":{"name":"ge","args":[{"app":{"fn":{"def":{"id":"D-S7A-W4","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"}]}},"args":[{"var":"K"}]}},{"app":{"fn":{"def":{"id":"D-S7A-W3","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"}]}},"args":[{"var":"K"}]}}]}}]}}}}}],"premises":[{"id":"MAP-P051G-P051A","producer":"P-051A","closure_role":"REQUIRED","binder_map":{},"hypothesis_map":{},"witness_map":{"c_0":"g_c0","C_0":"g_C0","Lambda_0":"g_L0"},"consume":["base_type"]},{"id":"MAP-P051G-P051F1","producer":"P-051F1","closure_role":"REQUIRED","binder_map":{},"hypothesis_map":{},"witness_map":{"c_1":"g_c1","C_1":"g_C1","Lambda_1":"g_L1"},"consume":["weight_type","dominates_base"]},{"id":"MAP-P051G-P051V","producer":"P-051V","closure_role":"REQUIRED","binder_map":{"theta":{"var":"theta"},"y":{"var":"y"},"k":{"var":"k"},"sigma":{"var":"sigma"}},"hypothesis_map":{"theta_ge_2":{"hypothesis":"theta_ge_2"},"y_pos":{"hypothesis":"y_pos"},"y_lt_1":{"hypothesis":"y_lt_1"},"k_ge_1":{"hypothesis":"k_ge_1"},"sigma_ge_theta":{"hypothesis":"sigma_ge_theta"}},"witness_map":{},"consume":["modifier_normalization"]},{"id":"MAP-P051G-P051F2","producer":"P-051F2","closure_role":"REQUIRED","binder_map":{"theta":{"var":"theta"},"y":{"var":"y"},"k":{"var":"k"},"sigma":{"var":"sigma"}},"hypothesis_map":{"theta_ge_2":{"hypothesis":"theta_ge_2"},"y_pos":{"hypothesis":"y_pos"},"y_lt_1":{"hypothesis":"y_lt_1"},"k_ge_1":{"hypothesis":"k_ge_1"},"sigma_ge_theta":{"hypothesis":"sigma_ge_theta"}},"witness_map":{"c_2":"g_c2","C_2":"g_C2","Lambda_2":"g_L2"},"consume":["weight_type","dominates_w1"]},{"id":"MAP-P051G-P051F3","producer":"P-051F3","closure_role":"REQUIRED","binder_map":{"theta":{"var":"theta"},"y":{"var":"y"},"k":{"var":"k"},"sigma":{"var":"sigma"}},"hypothesis_map":{"theta_ge_2":{"hypothesis":"theta_ge_2"},"y_pos":{"hypothesis":"y_pos"},"y_lt_1":{"hypothesis":"y_lt_1"},"k_ge_1":{"hypothesis":"k_ge_1"},"sigma_ge_theta":{"hypothesis":"sigma_ge_theta"}},"witness_map":{"c_3":"g_c3","C_3":"g_C3","Lambda_3":"g_L3"},"consume":["weight_type","dominates_w1","dominates_w2"]},{"id":"MAP-P051G-P051F4","producer":"P-051F4","closure_role":"REQUIRED","binder_map":{"theta":{"var":"theta"},"y":{"var":"y"},"k":{"var":"k"},"sigma":{"var":"sigma"}},"hypothesis_map":{"theta_ge_2":{"hypothesis":"theta_ge_2"},"y_pos":{"hypothesis":"y_pos"},"y_lt_1":{"hypothesis":"y_lt_1"},"k_ge_1":{"hypothesis":"k_ge_1"},"sigma_ge_theta":{"hypothesis":"sigma_ge_theta"}},"witness_map":{"c_4":"g_c4","C_4":"g_C4","Lambda_4":"g_L4"},"consume":["weight_type","dominates_w3"]}],"witness_realizations":{"c_star":{"proj":{"value":{"def":{"id":"D-S7A-COMMON-FIVE","args":[{"var":"g_c0"},{"var":"g_C0"},{"var":"g_L0"},{"var":"g_c1"},{"var":"g_C1"},{"var":"g_L1"},{"var":"g_c2"},{"var":"g_C2"},{"var":"g_L2"},{"var":"g_c3"},{"var":"g_C3"},{"var":"g_L3"},{"var":"g_c4"},{"var":"g_C4"},{"var":"g_L4"}]}},"index":0}},"C_star":{"proj":{"value":{"def":{"id":"D-S7A-COMMON-FIVE","args":[{"var":"g_c0"},{"var":"g_C0"},{"var":"g_L0"},{"var":"g_c1"},{"var":"g_C1"},{"var":"g_L1"},{"var":"g_c2"},{"var":"g_C2"},{"var":"g_L2"},{"var":"g_c3"},{"var":"g_C3"},{"var":"g_L3"},{"var":"g_c4"},{"var":"g_C4"},{"var":"g_L4"}]}},"index":1}},"Lambda_star":{"proj":{"value":{"def":{"id":"D-S7A-COMMON-FIVE","args":[{"var":"g_c0"},{"var":"g_C0"},{"var":"g_L0"},{"var":"g_c1"},{"var":"g_C1"},{"var":"g_L1"},{"var":"g_c2"},{"var":"g_C2"},{"var":"g_L2"},{"var":"g_c3"},{"var":"g_C3"},{"var":"g_L3"},{"var":"g_c4"},{"var":"g_C4"},{"var":"g_L4"}]}},"index":2}}},"proof_ref":"### P-051G — common-witness family consolidation"}
```

- Prenex statement: there exist \(c_*,C_*,\Lambda_*>0\), chosen before
  the literal typed list

  ```text
  theta in R_{>=2}, y in (0,1), k in N_{>=1},
  sigma in R_{>=theta}, p prime, i in N_{>=1},
  j in N, K in N_{>0}.
  ```

  such that the exact five weights
  \(a_0,w_1,w_{2,k},w_{3,k},w_{4,k}\) are nonnegative multiplicative,
  each is normalized by \(w(1)=1\), and
  satisfy
  \[
  |w(p^i)-1/(i+1)|\le C_*p^{-c_*},\qquad
  0\le w(p^i)\le\Lambda_*,
  \tag{P051G-type}
  \]
  with \(\Lambda_*\ge1+C_*2^{-c_*}\), while
  \[
  w_1(K)\ge a_0(K),\quad w_{2,k}(K)\ge w_1(K),\quad
  w_{3,k}(K)\ge w_1(K),w_{2,k}(K),\quad
  w_{4,k}(K)\ge w_{3,k}(K).
  \tag{P051G-dom}
  \]
  Also \(v_k\) is nonnegative multiplicative, \(v_k(1)=1\), and
  \(0\le v_k(p^j)\le1\) for every \(j\in\mathbb N\).
- Exact subjects: `SUB-P051G-FAMILY` is precisely the five D-015 weights;
  `SUB-P051G-DOM` is the four displayed integer dominations.
- Premise maps: `MAP-P051G-P051A`, `MAP-P051G-P051F1`,
  `MAP-P051G-P051F2`, `MAP-P051G-P051F3`, and `MAP-P051G-P051F4` consume,
  respectively, the base record and the four exact construction records.
  `MAP-P051G-P051V` binds \((\theta,y,k,\sigma,p,j)\) identically and
  consumes exactly nonnegative multiplicativity of \(v_k\), \(v_k(1)=1\),
  and the full \(j\in\mathbb N\) prime-power bound. No generic quotient or
  maximum is re-proved here.
- Derivation certificate: take the minimum of the finitely many positive type
  exponents and the maxima of their finitely many error/local-bound outputs,
  enlarging \(\Lambda_*\) to the displayed lower bound.  Every component
  output was already uniform over the modifier family, so this finite
  min/max is selected before the whole \((\theta,y,k,\sigma,p,i,K)\)-family.
  The base has \(a_0(1)=1\), and each shifted, hat-shifted, and prime-power
  maximum construction is extended multiplicatively with value \(1\) at
  the empty prime factorization; hence every selected weight has \(w(1)=1\).
- Source/S2 anchor: S2 R2.4 and S2B R2(3).
- Definitions used: D-015.

### P-051H — reusable Euler-tail and replaced-main-term bound

```mathminer-s3
{"schema":"mathminer.s3/1","id":"P-051H","kind":"PROPOSITION","binders":[{"key":"theta","type":"Real"},{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"},{"key":"w","type":{"fn":{"args":["Nat"],"return":"Real"}}},{"key":"b","type":{"fn":{"args":["Nat"],"return":"Real"}}},{"key":"p","type":"Nat"}],"uses_definitions":["D-S7A-CE","D-S7A-ETA","D-S7A-EULER","D-S7A-MODIFIER","D-S7A-PRIME","D-S7A-REAL-POWER","D-S7A-SELECTED-WEIGHT"],"source_anchors":[],"hypotheses":[{"key":"theta_ge_2","proposition":{"op":{"name":"ge","args":[{"var":"theta"},{"lit":{"type":"Real","value":"2"}}]}}},{"key":"y_pos","proposition":{"op":{"name":"gt","args":[{"var":"y"},{"lit":{"type":"Real","value":"0"}}]}}},{"key":"y_lt_1","proposition":{"op":{"name":"lt","args":[{"var":"y"},{"lit":{"type":"Real","value":"1"}}]}}},{"key":"k_ge_1","proposition":{"op":{"name":"ge","args":[{"var":"k"},{"lit":{"type":"Nat","value":"1"}}]}}},{"key":"sigma_ge_theta","proposition":{"op":{"name":"ge","args":[{"var":"sigma"},{"var":"theta"}]}}},{"key":"selected_weight","proposition":{"def":{"id":"D-S7A-SELECTED-WEIGHT","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"},{"var":"w"}]}}},{"key":"modifier_b","proposition":{"def":{"id":"D-S7A-MODIFIER","args":[{"var":"b"}]}}},{"key":"prime_p","proposition":{"def":{"id":"D-S7A-PRIME","args":[{"var":"p"}]}}}],"witnesses":[{"key":"c_star","type":"Real","depends_on":[]},{"key":"C_star","type":"Real","depends_on":[]},{"key":"Lambda_star","type":"Real","depends_on":[]}],"conclusions":[{"key":"eta_positive","proposition":{"op":{"name":"gt","args":[{"def":{"id":"D-S7A-ETA","args":[{"var":"c_star"}]}},{"lit":{"type":"Real","value":"0"}}]}}},{"key":"euler_constant_positive","proposition":{"op":{"name":"gt","args":[{"def":{"id":"D-S7A-CE","args":[{"var":"C_star"},{"var":"Lambda_star"}]}},{"lit":{"type":"Real","value":"0"}}]}}},{"key":"tail_bound","proposition":{"op":{"name":"le","args":[{"op":{"name":"abs","args":[{"op":{"name":"sub","args":[{"def":{"id":"D-S7A-EULER","args":[{"var":"w"},{"var":"b"},{"var":"p"}]}},{"op":{"name":"add","args":[{"lit":{"type":"Real","value":"1"}},{"op":{"name":"div","args":[{"op":{"name":"mul","args":[{"app":{"fn":{"var":"w"},"args":[{"var":"p"}]}},{"app":{"fn":{"var":"b"},"args":[{"var":"p"}]}}]}},{"cast":{"value":{"var":"p"},"to":"Real"}}]}}]}}]}}]}},{"op":{"name":"mul","args":[{"op":{"name":"mul","args":[{"lit":{"type":"Real","value":"2"}},{"var":"Lambda_star"}]}},{"def":{"id":"D-S7A-REAL-POWER","args":[{"cast":{"value":{"var":"p"},"to":"Real"}},{"lit":{"type":"Real","value":"-2"}}]}}]}}]}}},{"key":"tail_exponent_bound","proposition":{"op":{"name":"le","args":[{"op":{"name":"mul","args":[{"op":{"name":"mul","args":[{"lit":{"type":"Real","value":"2"}},{"var":"Lambda_star"}]}},{"def":{"id":"D-S7A-REAL-POWER","args":[{"cast":{"value":{"var":"p"},"to":"Real"}},{"lit":{"type":"Real","value":"-2"}}]}}]}},{"op":{"name":"mul","args":[{"op":{"name":"mul","args":[{"lit":{"type":"Real","value":"2"}},{"var":"Lambda_star"}]}},{"def":{"id":"D-S7A-REAL-POWER","args":[{"cast":{"value":{"var":"p"},"to":"Real"}},{"op":{"name":"neg","args":[{"op":{"name":"add","args":[{"lit":{"type":"Real","value":"1"}},{"def":{"id":"D-S7A-ETA","args":[{"var":"c_star"}]}}]}}]}}]}}]}}]}}},{"key":"replaced_main_bound","proposition":{"op":{"name":"le","args":[{"op":{"name":"abs","args":[{"op":{"name":"sub","args":[{"def":{"id":"D-S7A-EULER","args":[{"var":"w"},{"var":"b"},{"var":"p"}]}},{"op":{"name":"add","args":[{"lit":{"type":"Real","value":"1"}},{"op":{"name":"div","args":[{"app":{"fn":{"var":"b"},"args":[{"var":"p"}]}},{"op":{"name":"mul","args":[{"lit":{"type":"Real","value":"2"}},{"cast":{"value":{"var":"p"},"to":"Real"}}]}}]}}]}}]}}]}},{"op":{"name":"mul","args":[{"def":{"id":"D-S7A-CE","args":[{"var":"C_star"},{"var":"Lambda_star"}]}},{"def":{"id":"D-S7A-REAL-POWER","args":[{"cast":{"value":{"var":"p"},"to":"Real"}},{"op":{"name":"neg","args":[{"op":{"name":"add","args":[{"lit":{"type":"Real","value":"1"}},{"def":{"id":"D-S7A-ETA","args":[{"var":"c_star"}]}}]}}]}}]}}]}}]}}}],"premises":[{"id":"MAP-P051H-P051G","producer":"P-051G","closure_role":"REQUIRED","binder_map":{"theta":{"var":"theta"},"y":{"var":"y"},"k":{"var":"k"},"sigma":{"var":"sigma"}},"hypothesis_map":{"theta_ge_2":{"hypothesis":"theta_ge_2"},"y_pos":{"hypothesis":"y_pos"},"y_lt_1":{"hypothesis":"y_lt_1"},"k_ge_1":{"hypothesis":"k_ge_1"},"sigma_ge_theta":{"hypothesis":"sigma_ge_theta"}},"witness_map":{"c_star":"h_cstar","C_star":"h_Cstar","Lambda_star":"h_Lstar"},"consume":["base_type","w1_type","w2_type","w3_type","w4_type"]}],"witness_realizations":{"c_star":{"var":"h_cstar"},"C_star":{"var":"h_Cstar"},"Lambda_star":{"var":"h_Lstar"}},"proof_ref":"### P-051H — reusable Euler-tail and replaced-main-term bound"}
```

- Prenex statement: consume the fixed common witnesses from P-051G and put
  \(\eta_*:=\min(c_*,1)>0\),
  \(C_{E,*}:=C_*+2\Lambda_*>0\). Uniformly for every selected member
  \(w\in\{a_0,w_1,w_{2,k},w_{3,k},w_{4,k}\}\), with the P-051G facts that
  \(w\) is nonnegative multiplicative and \(w(1)=1\), and for the literal
  typed modifier hypotheses

  ```text
  b : N_{>0} -> R_{>=0};
  b is multiplicative; b(1)=1;
  forall prime p, forall j in N, 0 <= b(p^j) <= 1,
  ```

  for every prime \(p\), if
  \(L_p(w,b)=\sum_{j\ge0}w(p^j)b(p^j)p^{-j}\), then
  \[
  \left|L_p(w,b)-\left(1+{w(p)b(p)\over p}\right)\right|
    \le2\Lambda_*p^{-2}\le2\Lambda_*p^{-1-\eta_*},
  \tag{P051H-tail}
  \]
  and
  \[
  \left|L_p(w,b)-\left(1+{b(p)\over2p}\right)\right|
    \le C_{E,*}p^{-1-\eta_*}.
  \tag{P051H-main}
  \]
- Exact subject: `SUB-P051H-EULER` is the literal local Euler factor for the
  selected exact D-015 weight and modifier.
- Premise maps: `MAP-P051H-P051G` maps \((c_*,C_*,\Lambda_*,w,p,i)\) to the
  common witnesses, selected weight, current prime, and \(i=1\) for the
  replaced main term; it consumes exactly (P051G-type) and \(w(1)=1\), not
  the construction or domination conclusions. Specialization map
  `MAP-P051H-P051V` binds \((\theta,y,k,\sigma)\) identically whenever
  \(b:=v_k\), and discharges exactly that \(b\) is nonnegative
  multiplicative, \(b(1)=1\), and has the full prime-power bound.
- Derivation certificate: the constant term is
  \(w(1)b(1)=1\cdot1=1\), so
  \(L_p(w,b)=1+w(p)b(p)/p+\sum_{j\ge2}w(p^j)b(p^j)p^{-j}\).
  The \(j\ge2\) tail is at most
  \(\Lambda_*\sum_{j\ge2}p^{-j}=\Lambda_*/(p(p-1))\le2\Lambda_*p^{-2}\).
  At \(i=1\), P-051G gives
  \(|w(p)-1/2|/p\le C_*p^{-1-c_*}\); combine the two errors and use
  \(\eta_*=\min(c_*,1)\).
- Source/S2 anchor: S2 R2.4a and S2B R2(3).
- Definitions used: D-014, D-015.

### Section 7 bound support and existential adapters

These exact parameterized definitions and witness selectors support P-052 through P-059 and the branch-local P-005 adapter.

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S7B-P005-EXISTS","kind":"DEFINITION","binders":[{"key":"lambda_seq","type":{"fn":{"args":["Nat"],"return":"Real"}}},{"key":"lambda","type":"Real"},{"key":"u","type":{"fn":{"args":["Nat"],"return":"Real"}}},{"key":"v","type":{"fn":{"args":["Nat"],"return":"Real"}}},{"key":"K_sh","type":"Nat"},{"key":"X","type":"Real"}],"uses_definitions":["D-S45-P005-SHIFTED-MEAN"],"source_anchors":[],"result_type":"Prop","body":"There exists a positive C_5 depending only on lambda_seq,lambda for which the exact P-005 shifted mean bound holds for these u,v,K_sh,X."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S7B-P052-DOMAIN","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"},{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"},{"key":"K_sh","type":"Nat"},{"key":"z","type":"Real"}],"uses_definitions":[],"source_anchors":[],"result_type":"Prop","body":"theta>=2, y in (0,1), k>=1, sigma>=theta, K_sh>=1, and z>0."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S7B-P052-W","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"}],"uses_definitions":[],"source_anchors":[],"result_type":"Real","body":"The positive smoothing constant C_sm(theta) obtained from the P-005 comparison, exact Euler-factor estimates, and bounded z<2 adapter, chosen before y,k,sigma,K_sh,z."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S7B-P052-RESULT","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"},{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"},{"key":"K_sh","type":"Nat"},{"key":"z","type":"Real"},{"key":"C_sm","type":"Real"}],"uses_definitions":["D-001","D-006","D-015"],"source_anchors":[],"result_type":"Prop","body":"The exact reciprocal-divisor smoothing inequality sum_{m<z} tau(mK_sh)^(-1) <= C_sm(theta) w_1(K_sh) sum_{m<z} ell(m)^(-1/2)."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S7B-P053-DOMAIN","kind":"DEFINITION","binders":[{"key":"M","type":"Real"}],"uses_definitions":[],"source_anchors":[],"result_type":"Prop","body":"M>0."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S7B-P053-W","kind":"DEFINITION","binders":[],"uses_definitions":[],"source_anchors":[],"result_type":"Real","body":"The absolute positive partial-summation constant C_ps from P-053."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S7B-P053-RESULT","kind":"DEFINITION","binders":[{"key":"M","type":"Real"},{"key":"C_ps","type":"Real"}],"uses_definitions":[],"source_anchors":[],"result_type":"Prop","body":"For every nonnegative sequence with all partial sums at most M t, the exact square-root harmonic partial-summation bound in P-053 holds with C_ps."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S7B-P054-DOMAIN","kind":"DEFINITION","binders":[{"key":"d","type":"Nat"},{"key":"d_prime","type":"Nat"},{"key":"k","type":"Nat"},{"key":"theta","type":"Real"}],"uses_definitions":["D-005"],"source_anchors":[],"result_type":"Prop","body":"k>=1, theta>=2, d,d'>0, theta^k<=d<theta^(k+1), and Close_theta(d,d')."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S7B-P054-RESULT","kind":"DEFINITION","binders":[{"key":"d","type":"Nat"},{"key":"d_prime","type":"Nat"},{"key":"k","type":"Nat"},{"key":"theta","type":"Real"}],"uses_definitions":["D-005"],"source_anchors":[],"result_type":"Prop","body":"The exact close-pair window theta^(k-1)<d'<theta^(k+2)."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S7B-P054A-DOMAIN","kind":"DEFINITION","binders":[{"key":"k","type":"Nat"},{"key":"theta","type":"Real"},{"key":"sigma","type":"Real"},{"key":"g","type":{"fn":{"args":["Nat"],"return":"Real"}}}],"uses_definitions":[],"source_anchors":[],"result_type":"Prop","body":"k>=1, theta>=2, sigma>0, and g is nonnegative."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S7B-P054A-RESULT","kind":"DEFINITION","binders":[{"key":"k","type":"Nat"},{"key":"theta","type":"Real"},{"key":"sigma","type":"Real"},{"key":"g","type":{"fn":{"args":["Nat"],"return":"Real"}}}],"uses_definitions":[],"source_anchors":[],"result_type":"Prop","body":"The two exact nonnegative initial-segment enlargements AD-REG-INIT and AD-TR-INIT used in P-058 and P-084."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S7B-P055-DOMAIN","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"},{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"},{"key":"K_sh","type":"Nat"},{"key":"z","type":"Real"}],"uses_definitions":[],"source_anchors":[],"result_type":"Prop","body":"The exact P-055 upper-branch domain, including theta>=2, y in (0,1), k>=1, sigma>=theta, K_sh>=1, z>0 and the displayed endpoint inequalities."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S7B-P055-W","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"}],"uses_definitions":[],"source_anchors":[],"result_type":"Real","body":"The positive C_upper(theta), assembled from the family-uniform shifted mean and Euler constants before y,k,sigma,K_sh,z."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S7B-P055-RESULT","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"},{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"},{"key":"K_sh","type":"Nat"},{"key":"z","type":"Real"},{"key":"C_upper","type":"Real"}],"uses_definitions":["D-006","D-015","D-016"],"source_anchors":[],"result_type":"Prop","body":"The exact P-055 bound for T_k(z,K_sh) in the upper regime, with all displayed logarithmic factors and exact D-015/D-016 subjects."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S7B-P056-DOMAIN","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"},{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"},{"key":"K_sh","type":"Nat"},{"key":"z","type":"Real"}],"uses_definitions":[],"source_anchors":[],"result_type":"Prop","body":"The exact P-056 middle-branch domain, including theta>=2, y in (0,1), k>=1, sigma>=theta, K_sh>=1, z>0 and the displayed endpoint inequalities."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S7B-P056-W","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"}],"uses_definitions":[],"source_anchors":[],"result_type":"Real","body":"The positive C_middle(theta), assembled from the family-uniform shifted mean and Euler constants before y,k,sigma,K_sh,z."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S7B-P056-RESULT","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"},{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"},{"key":"K_sh","type":"Nat"},{"key":"z","type":"Real"},{"key":"C_middle","type":"Real"}],"uses_definitions":["D-006","D-015","D-016"],"source_anchors":[],"result_type":"Prop","body":"The exact P-056 bound for T_k(z,K_sh) in the middle regime, with all displayed logarithmic factors and exact D-015/D-016 subjects."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S7B-P057-DOMAIN","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"},{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"},{"key":"K_sh","type":"Nat"},{"key":"z","type":"Real"}],"uses_definitions":[],"source_anchors":[],"result_type":"Prop","body":"theta>=2, y in (0,1), k>=1, sigma>=theta, K_sh>=1, and 0<z<sigma."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S7B-P057-RESULT","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"},{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"},{"key":"K_sh","type":"Nat"},{"key":"z","type":"Real"}],"uses_definitions":["D-015","D-016"],"source_anchors":[],"result_type":"Prop","body":"The exact terminal bound T_k(z,K_sh)<=w_1(K_sh)."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S7B-P058-DOMAIN","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"},{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"},{"key":"x","type":"Real"}],"uses_definitions":[],"source_anchors":[],"result_type":"Prop","body":"theta>=2, y in (0,1), k>=1, theta<=sigma<=theta^k, and x>theta^(2k-1)."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S7B-P058-W","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"}],"uses_definitions":[],"source_anchors":[],"result_type":"Real","body":"The positive outer constant C_out(theta), chosen before y,k,sigma,x and all summation indices."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S7B-P058-RESULT","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"},{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"},{"key":"x","type":"Real"},{"key":"C_out","type":"Real"}],"uses_definitions":["D-015","D-018"],"source_anchors":[],"result_type":"Prop","body":"The exact regular outer shifted-mean inequality for O_k with the displayed theta^k, log-sigma, k-power and w_{4,k}(d') window sum."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S7B-P059-DOMAIN","kind":"DEFINITION","binders":[{"key":"Q","type":"Type"},{"key":"w_family","type":{"fn":{"args":[{"var":"Q"}],"return":{"fn":{"args":["Nat"],"return":"Real"}}}}},{"key":"c_w","type":"Real"},{"key":"C_w_err","type":"Real"},{"key":"Lambda_w","type":"Real"},{"key":"q","type":{"var":"Q"}},{"key":"Z","type":"Real"}],"uses_definitions":[],"source_anchors":[],"result_type":"Prop","body":"Q is nonempty; the w_q are nonnegative multiplicative; c_w,C_w_err,Lambda_w>0 give the displayed common type/local bounds; q in Q and Z>=2."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S7B-P059-W","kind":"DEFINITION","binders":[{"key":"Q","type":"Type"},{"key":"w_family","type":{"fn":{"args":[{"var":"Q"}],"return":{"fn":{"args":["Nat"],"return":"Real"}}}}},{"key":"c_w","type":"Real"},{"key":"C_w_err","type":"Real"},{"key":"Lambda_w","type":"Real"}],"uses_definitions":[],"source_anchors":[],"result_type":"Real","body":"The single positive family mean constant selected from the common EXT-001 and P-008 data before q and Z."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S7B-P059-RESULT","kind":"DEFINITION","binders":[{"key":"Q","type":"Type"},{"key":"w_family","type":{"fn":{"args":[{"var":"Q"}],"return":{"fn":{"args":["Nat"],"return":"Real"}}}}},{"key":"c_w","type":"Real"},{"key":"C_w_err","type":"Real"},{"key":"Lambda_w","type":"Real"},{"key":"q","type":{"var":"Q"}},{"key":"Z","type":"Real"},{"key":"C_mean","type":"Real"}],"uses_definitions":[],"source_anchors":[],"result_type":"Prop","body":"The exact family-uniform mean bound sum_{r<Z} w_q(r) <= C_mean Z (log Z)^(-1/2)."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S7B-P059-LAMBDA","kind":"DEFINITION","binders":[{"key":"Lambda_w","type":"Real"}],"uses_definitions":[],"source_anchors":[],"result_type":"Real","body":"max(1,Lambda_w)."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S7B-P059-ETA","kind":"DEFINITION","binders":[{"key":"c_w","type":"Real"}],"uses_definitions":[],"source_anchors":[],"result_type":"Real","body":"min(c_w,1)."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S7B-P059-CERR","kind":"DEFINITION","binders":[{"key":"C_w_err","type":"Real"},{"key":"Lambda_w","type":"Real"}],"uses_definitions":[],"source_anchors":[],"result_type":"Real","body":"C_w_err+2 Lambda_w."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S7B-P059-L","kind":"DEFINITION","binders":[{"key":"Q","type":"Type"},{"key":"w_family","type":{"fn":{"args":[{"var":"Q"}],"return":{"fn":{"args":["Nat"],"return":"Real"}}}}},{"key":"q","type":{"var":"Q"}}],"uses_definitions":[],"source_anchors":[],"result_type":{"fn":{"args":["Nat"],"return":"Real"}},"body":"The positive prime family p |-> sum_{j>=0} w_q(p^j)p^(-j)."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S7B-P059-COEFF","kind":"DEFINITION","binders":[{"key":"Q","type":"Type"}],"uses_definitions":[],"source_anchors":[],"result_type":{"fn":{"args":[{"var":"Q"}],"return":"Real"}},"body":"The constant coefficient map q |-> 1/2."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-S7B-P059-LOCAL","kind":"DEFINITION","binders":[{"key":"Q","type":"Type"},{"key":"w_family","type":{"fn":{"args":[{"var":"Q"}],"return":{"fn":{"args":["Nat"],"return":"Real"}}}}}],"uses_definitions":[],"source_anchors":[],"result_type":{"fn":{"args":[{"var":"Q"},"Nat"],"return":"Real"}},"body":"The exact family local-factor map (q,p) |-> sum_{j>=0} w_q(p^j)p^(-j)."}
```

### Exact existential adapter A-S7-P005-EXISTS

```mathminer-s3
{"schema":"mathminer.s3/1","id":"A-S7-P005-EXISTS","kind":"DERIVATION","binders":[{"key":"lambda_seq","type":{"fn":{"args":["Nat"],"return":"Real"}}},{"key":"lambda","type":"Real"},{"key":"u","type":{"fn":{"args":["Nat"],"return":"Real"}}},{"key":"v","type":{"fn":{"args":["Nat"],"return":"Real"}}},{"key":"K_sh","type":"Nat"},{"key":"X","type":"Real"}],"uses_definitions":["D-S45-SHIFT-FAMILY-DOMAIN","D-S7B-P005-EXISTS"],"source_anchors":[],"hypotheses":[{"key":"domain","proposition":{"def":{"id":"D-S45-SHIFT-FAMILY-DOMAIN","args":[{"var":"lambda_seq"},{"var":"lambda"},{"var":"u"},{"var":"v"},{"var":"K_sh"},{"var":"X"}]}}}],"witnesses":[],"conclusions":[{"key":"shifted_mean_exists","proposition":{"def":{"id":"D-S7B-P005-EXISTS","args":[{"var":"lambda_seq"},{"var":"lambda"},{"var":"u"},{"var":"v"},{"var":"K_sh"},{"var":"X"}]}}}],"premises":[{"id":"use-p005","producer":"P-005","closure_role":"REQUIRED","binder_map":{"lambda_seq":{"var":"lambda_seq"},"lambda":{"var":"lambda"},"u":{"var":"u"},"v":{"var":"v"},"K_sh":{"var":"K_sh"},"X":{"var":"X"}},"hypothesis_map":{"domain":{"hypothesis":"domain"}},"witness_map":{"C_5":"p005_exist_C5"},"consume":["C_5_positive","shifted_mean_bound"]}],"witness_realizations":{},"proof_ref":"### Exact existential adapter A-S7-P005-EXISTS"}
```

This witnessless adapter packages the exact P-005 existential for guarded branch applications without exporting a branch-local witness.

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-LATE-P051F2-W","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"},{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"}],"uses_definitions":["D-S7A-WEIGHT-TYPE"],"source_anchors":[],"result_type":{"tuple":["Real","Real","Real"]},"body":"The exact P-051F2 analytic witness triple, selected in c_2,C_2,Lambda_2 order from the P-051C/P-051D construction for the displayed family parameters."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-LATE-P051F3-W","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"},{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"}],"uses_definitions":["D-S7A-WEIGHT-TYPE"],"source_anchors":[],"result_type":{"tuple":["Real","Real","Real"]},"body":"The exact P-051F3 commonized maximum witness triple, in c_3,C_3,Lambda_3 order, obtained from P-051E0 and P-051E for the displayed family parameters."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-LATE-P051G-W","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"},{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"}],"uses_definitions":["D-S7A-COMMON-FIVE"],"source_anchors":[],"result_type":{"tuple":["Real","Real","Real"]},"body":"The exact P-051G five-weight common witness triple in c_star,C_star,Lambda_star order, including the stated common-lambda floor."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-LATE-P020-W","kind":"DEFINITION","binders":[{"key":"epsilon_int","type":"Real"},{"key":"xi","type":"Real"},{"key":"sigma","type":"Real"},{"key":"theta","type":"Real"}],"uses_definitions":["D-S45-P020-A"],"source_anchors":[],"result_type":{"tuple":["Real","Real",{"set":"Nat"}]},"body":"The exact P-020 witness package in C_grid,Xi_0,A order, assembled from P-018 and the canonical D-S45-P020-A selector."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-LATE-P051F2-EXISTS","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"},{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"}],"uses_definitions":[],"source_anchors":[],"result_type":"Prop","body":"The exact existential closure of P-051F2, preserving its witness order and all named conclusions for this fixed binder tuple."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-LATE-P051F3-EXISTS","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"},{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"}],"uses_definitions":[],"source_anchors":[],"result_type":"Prop","body":"The exact existential closure of P-051F3, preserving its witness order and all named conclusions for this fixed binder tuple."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-LATE-P051F4-EXISTS","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"},{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"}],"uses_definitions":[],"source_anchors":[],"result_type":"Prop","body":"The exact existential closure of P-051F4, preserving its witness order and all named conclusions for this fixed binder tuple."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-LATE-P051G-EXISTS","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"},{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"}],"uses_definitions":[],"source_anchors":[],"result_type":"Prop","body":"The exact existential closure of P-051G, preserving its witness order and all named conclusions for this fixed binder tuple."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-LATE-P051H-EXISTS","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"},{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"},{"key":"w","type":{"fn":{"args":["Nat"],"return":"Real"}}},{"key":"b","type":{"fn":{"args":["Nat"],"return":"Real"}}},{"key":"p","type":"Nat"}],"uses_definitions":[],"source_anchors":[],"result_type":"Prop","body":"The exact existential closure of P-051H, preserving its witness order and all named conclusions for this fixed binder tuple."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-LATE-P052-EXISTS","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"},{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"},{"key":"K_sh","type":"Nat"},{"key":"z","type":"Real"}],"uses_definitions":[],"source_anchors":[],"result_type":"Prop","body":"The exact existential closure of P-052, preserving its witness order and all named conclusions for this fixed binder tuple."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-LATE-P053-EXISTS","kind":"DEFINITION","binders":[{"key":"M","type":"Real"}],"uses_definitions":[],"source_anchors":[],"result_type":"Prop","body":"The exact existential closure of P-053, preserving its witness order and all named conclusions for this fixed binder tuple."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-LATE-P055-EXISTS","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"},{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"},{"key":"K_sh","type":"Nat"},{"key":"z","type":"Real"}],"uses_definitions":[],"source_anchors":[],"result_type":"Prop","body":"The exact existential closure of P-055, preserving its witness order and all named conclusions for this fixed binder tuple."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-LATE-P056-EXISTS","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"},{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"},{"key":"K_sh","type":"Nat"},{"key":"z","type":"Real"}],"uses_definitions":[],"source_anchors":[],"result_type":"Prop","body":"The exact existential closure of P-056, preserving its witness order and all named conclusions for this fixed binder tuple."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-LATE-P058-EXISTS","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"},{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"},{"key":"x","type":"Real"}],"uses_definitions":[],"source_anchors":[],"result_type":"Prop","body":"The exact existential closure of P-058, preserving its witness order and all named conclusions for this fixed binder tuple."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-LATE-P059-EXISTS","kind":"DEFINITION","binders":[{"key":"Q","type":"Type"},{"key":"w_family","type":{"fn":{"args":[{"var":"Q"}],"return":{"fn":{"args":["Nat"],"return":"Real"}}}}},{"key":"c_w","type":"Real"},{"key":"C_w_err","type":"Real"},{"key":"Lambda_w","type":"Real"},{"key":"q","type":{"var":"Q"}},{"key":"Z","type":"Real"}],"uses_definitions":[],"source_anchors":[],"result_type":"Prop","body":"The exact existential closure of P-059, preserving its witness order and all named conclusions for this fixed binder tuple."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-LATE-P020-EXISTS","kind":"DEFINITION","binders":[{"key":"epsilon_int","type":"Real"},{"key":"xi","type":"Real"},{"key":"sigma","type":"Real"},{"key":"theta","type":"Real"}],"uses_definitions":[],"source_anchors":[],"result_type":"Prop","body":"The exact existential closure of P-020, preserving its witness order and all named conclusions for this fixed binder tuple."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"A-LATE-P051F2-EXISTS","kind":"DERIVATION","binders":[{"key":"theta","type":"Real"},{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"}],"uses_definitions":["D-LATE-P051F2-EXISTS"],"source_anchors":[],"hypotheses":[{"key":"theta_ge_2","proposition":{"op":{"name":"ge","args":[{"var":"theta"},{"lit":{"type":"Real","value":"2"}}]}}},{"key":"y_pos","proposition":{"op":{"name":"gt","args":[{"var":"y"},{"lit":{"type":"Real","value":"0"}}]}}},{"key":"y_lt_1","proposition":{"op":{"name":"lt","args":[{"var":"y"},{"lit":{"type":"Real","value":"1"}}]}}},{"key":"k_ge_1","proposition":{"op":{"name":"ge","args":[{"var":"k"},{"lit":{"type":"Nat","value":"1"}}]}}},{"key":"sigma_ge_theta","proposition":{"op":{"name":"ge","args":[{"var":"sigma"},{"var":"theta"}]}}}],"witnesses":[],"conclusions":[{"key":"existentialized","proposition":{"def":{"id":"D-LATE-P051F2-EXISTS","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"}]}}}],"premises":[{"id":"use-p-051f2","producer":"P-051F2","closure_role":"REQUIRED","binder_map":{"theta":{"var":"theta"},"y":{"var":"y"},"k":{"var":"k"},"sigma":{"var":"sigma"}},"hypothesis_map":{"theta_ge_2":{"hypothesis":"theta_ge_2"},"y_pos":{"hypothesis":"y_pos"},"y_lt_1":{"hypothesis":"y_lt_1"},"k_ge_1":{"hypothesis":"k_ge_1"},"sigma_ge_theta":{"hypothesis":"sigma_ge_theta"}},"witness_map":{"c_2":"a_late_p051f2_exists_c_2","C_2":"a_late_p051f2_exists_C_2","Lambda_2":"a_late_p051f2_exists_Lambda_2"},"consume":["weight_type","dominates_w1","dominates_shift"]}],"witness_realizations":{},"proof_ref":"### P-051F2 — exact instantiation \\((w_1,v_k)\\to w_{2,k}\\)"}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"A-LATE-P051F3-EXISTS","kind":"DERIVATION","binders":[{"key":"theta","type":"Real"},{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"}],"uses_definitions":["D-LATE-P051F3-EXISTS"],"source_anchors":[],"hypotheses":[{"key":"theta_ge_2","proposition":{"op":{"name":"ge","args":[{"var":"theta"},{"lit":{"type":"Real","value":"2"}}]}}},{"key":"y_pos","proposition":{"op":{"name":"gt","args":[{"var":"y"},{"lit":{"type":"Real","value":"0"}}]}}},{"key":"y_lt_1","proposition":{"op":{"name":"lt","args":[{"var":"y"},{"lit":{"type":"Real","value":"1"}}]}}},{"key":"k_ge_1","proposition":{"op":{"name":"ge","args":[{"var":"k"},{"lit":{"type":"Nat","value":"1"}}]}}},{"key":"sigma_ge_theta","proposition":{"op":{"name":"ge","args":[{"var":"sigma"},{"var":"theta"}]}}}],"witnesses":[],"conclusions":[{"key":"existentialized","proposition":{"def":{"id":"D-LATE-P051F3-EXISTS","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"}]}}}],"premises":[{"id":"use-p-051f3","producer":"P-051F3","closure_role":"REQUIRED","binder_map":{"theta":{"var":"theta"},"y":{"var":"y"},"k":{"var":"k"},"sigma":{"var":"sigma"}},"hypothesis_map":{"theta_ge_2":{"hypothesis":"theta_ge_2"},"y_pos":{"hypothesis":"y_pos"},"y_lt_1":{"hypothesis":"y_lt_1"},"k_ge_1":{"hypothesis":"k_ge_1"},"sigma_ge_theta":{"hypothesis":"sigma_ge_theta"}},"witness_map":{"c_3":"a_late_p051f3_exists_c_3","C_3":"a_late_p051f3_exists_C_3","Lambda_3":"a_late_p051f3_exists_Lambda_3"},"consume":["weight_type","dominates_w1","dominates_w2"]}],"witness_realizations":{},"proof_ref":"### P-051F3 — exact instantiation \\((w_1,w_{2,k})\\to w_{3,k}\\)"}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"A-LATE-P051F4-EXISTS","kind":"DERIVATION","binders":[{"key":"theta","type":"Real"},{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"}],"uses_definitions":["D-LATE-P051F4-EXISTS"],"source_anchors":[],"hypotheses":[{"key":"theta_ge_2","proposition":{"op":{"name":"ge","args":[{"var":"theta"},{"lit":{"type":"Real","value":"2"}}]}}},{"key":"y_pos","proposition":{"op":{"name":"gt","args":[{"var":"y"},{"lit":{"type":"Real","value":"0"}}]}}},{"key":"y_lt_1","proposition":{"op":{"name":"lt","args":[{"var":"y"},{"lit":{"type":"Real","value":"1"}}]}}},{"key":"k_ge_1","proposition":{"op":{"name":"ge","args":[{"var":"k"},{"lit":{"type":"Nat","value":"1"}}]}}},{"key":"sigma_ge_theta","proposition":{"op":{"name":"ge","args":[{"var":"sigma"},{"var":"theta"}]}}}],"witnesses":[],"conclusions":[{"key":"existentialized","proposition":{"def":{"id":"D-LATE-P051F4-EXISTS","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"}]}}}],"premises":[{"id":"use-p-051f4","producer":"P-051F4","closure_role":"REQUIRED","binder_map":{"theta":{"var":"theta"},"y":{"var":"y"},"k":{"var":"k"},"sigma":{"var":"sigma"}},"hypothesis_map":{"theta_ge_2":{"hypothesis":"theta_ge_2"},"y_pos":{"hypothesis":"y_pos"},"y_lt_1":{"hypothesis":"y_lt_1"},"k_ge_1":{"hypothesis":"k_ge_1"},"sigma_ge_theta":{"hypothesis":"sigma_ge_theta"}},"witness_map":{"c_4":"a_late_p051f4_exists_c_4","C_4":"a_late_p051f4_exists_C_4","Lambda_4":"a_late_p051f4_exists_Lambda_4"},"consume":["weight_type","dominates_w3","dominates_shift"]}],"witness_realizations":{},"proof_ref":"### P-051F4 — exact instantiation \\((w_{3,k},v_k)\\to w_{4,k}\\)"}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"A-LATE-P051G-EXISTS","kind":"DERIVATION","binders":[{"key":"theta","type":"Real"},{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"}],"uses_definitions":["D-LATE-P051G-EXISTS"],"source_anchors":[],"hypotheses":[{"key":"theta_ge_2","proposition":{"op":{"name":"ge","args":[{"var":"theta"},{"lit":{"type":"Real","value":"2"}}]}}},{"key":"y_pos","proposition":{"op":{"name":"gt","args":[{"var":"y"},{"lit":{"type":"Real","value":"0"}}]}}},{"key":"y_lt_1","proposition":{"op":{"name":"lt","args":[{"var":"y"},{"lit":{"type":"Real","value":"1"}}]}}},{"key":"k_ge_1","proposition":{"op":{"name":"ge","args":[{"var":"k"},{"lit":{"type":"Nat","value":"1"}}]}}},{"key":"sigma_ge_theta","proposition":{"op":{"name":"ge","args":[{"var":"sigma"},{"var":"theta"}]}}}],"witnesses":[],"conclusions":[{"key":"existentialized","proposition":{"def":{"id":"D-LATE-P051G-EXISTS","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"}]}}}],"premises":[{"id":"use-p-051g","producer":"P-051G","closure_role":"REQUIRED","binder_map":{"theta":{"var":"theta"},"y":{"var":"y"},"k":{"var":"k"},"sigma":{"var":"sigma"}},"hypothesis_map":{"theta_ge_2":{"hypothesis":"theta_ge_2"},"y_pos":{"hypothesis":"y_pos"},"y_lt_1":{"hypothesis":"y_lt_1"},"k_ge_1":{"hypothesis":"k_ge_1"},"sigma_ge_theta":{"hypothesis":"sigma_ge_theta"}},"witness_map":{"c_star":"a_late_p051g_exists_c_star","C_star":"a_late_p051g_exists_C_star","Lambda_star":"a_late_p051g_exists_Lambda_star"},"consume":["base_type","w1_type","w2_type","w3_type","w4_type","common_lambda_floor","modifier_normalization","dominates_base","dominates_w1_by_w2","dominates_w1_by_w3","dominates_w2_by_w3","dominates_w3_by_w4"]}],"witness_realizations":{},"proof_ref":"### P-051G — common-witness family consolidation"}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"A-LATE-P051H-EXISTS","kind":"DERIVATION","binders":[{"key":"theta","type":"Real"},{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"},{"key":"w","type":{"fn":{"args":["Nat"],"return":"Real"}}},{"key":"b","type":{"fn":{"args":["Nat"],"return":"Real"}}},{"key":"p","type":"Nat"}],"uses_definitions":["D-LATE-P051H-EXISTS","D-S7A-MODIFIER","D-S7A-PRIME","D-S7A-SELECTED-WEIGHT"],"source_anchors":[],"hypotheses":[{"key":"theta_ge_2","proposition":{"op":{"name":"ge","args":[{"var":"theta"},{"lit":{"type":"Real","value":"2"}}]}}},{"key":"y_pos","proposition":{"op":{"name":"gt","args":[{"var":"y"},{"lit":{"type":"Real","value":"0"}}]}}},{"key":"y_lt_1","proposition":{"op":{"name":"lt","args":[{"var":"y"},{"lit":{"type":"Real","value":"1"}}]}}},{"key":"k_ge_1","proposition":{"op":{"name":"ge","args":[{"var":"k"},{"lit":{"type":"Nat","value":"1"}}]}}},{"key":"sigma_ge_theta","proposition":{"op":{"name":"ge","args":[{"var":"sigma"},{"var":"theta"}]}}},{"key":"selected_weight","proposition":{"def":{"id":"D-S7A-SELECTED-WEIGHT","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"},{"var":"w"}]}}},{"key":"modifier_b","proposition":{"def":{"id":"D-S7A-MODIFIER","args":[{"var":"b"}]}}},{"key":"prime_p","proposition":{"def":{"id":"D-S7A-PRIME","args":[{"var":"p"}]}}}],"witnesses":[],"conclusions":[{"key":"existentialized","proposition":{"def":{"id":"D-LATE-P051H-EXISTS","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"},{"var":"w"},{"var":"b"},{"var":"p"}]}}}],"premises":[{"id":"use-p-051h","producer":"P-051H","closure_role":"REQUIRED","binder_map":{"theta":{"var":"theta"},"y":{"var":"y"},"k":{"var":"k"},"sigma":{"var":"sigma"},"w":{"var":"w"},"b":{"var":"b"},"p":{"var":"p"}},"hypothesis_map":{"theta_ge_2":{"hypothesis":"theta_ge_2"},"y_pos":{"hypothesis":"y_pos"},"y_lt_1":{"hypothesis":"y_lt_1"},"k_ge_1":{"hypothesis":"k_ge_1"},"sigma_ge_theta":{"hypothesis":"sigma_ge_theta"},"selected_weight":{"hypothesis":"selected_weight"},"modifier_b":{"hypothesis":"modifier_b"},"prime_p":{"hypothesis":"prime_p"}},"witness_map":{"c_star":"a_late_p051h_exists_c_star","C_star":"a_late_p051h_exists_C_star","Lambda_star":"a_late_p051h_exists_Lambda_star"},"consume":["eta_positive","euler_constant_positive","tail_bound","tail_exponent_bound","replaced_main_bound"]}],"witness_realizations":{},"proof_ref":"### P-051H — reusable Euler-tail and replaced-main-term bound"}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"A-LATE-P052-EXISTS","kind":"DERIVATION","binders":[{"key":"theta","type":"Real"},{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"},{"key":"K_sh","type":"Nat"},{"key":"z","type":"Real"}],"uses_definitions":["D-LATE-P052-EXISTS","D-S7-P051V-DOMAIN","D-S7B-P052-DOMAIN"],"source_anchors":[],"hypotheses":[{"key":"domain","proposition":{"def":{"id":"D-S7B-P052-DOMAIN","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"},{"var":"K_sh"},{"var":"z"}]}}},{"key":"family_domain","proposition":{"def":{"id":"D-S7-P051V-DOMAIN","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"}]}}}],"witnesses":[],"conclusions":[{"key":"existentialized","proposition":{"def":{"id":"D-LATE-P052-EXISTS","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"},{"var":"K_sh"},{"var":"z"}]}}}],"premises":[{"id":"use-p-052","producer":"P-052","closure_role":"REQUIRED","binder_map":{"theta":{"var":"theta"},"y":{"var":"y"},"k":{"var":"k"},"sigma":{"var":"sigma"},"K_sh":{"var":"K_sh"},"z":{"var":"z"}},"hypothesis_map":{"domain":{"hypothesis":"domain"},"family_domain":{"hypothesis":"family_domain"}},"witness_map":{"C_sm":"a_late_p052_exists_C_sm"},"consume":["smoothing_bound"]}],"witness_realizations":{},"proof_ref":"### P-052 — exact reciprocal-divisor smoothing"}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"A-LATE-P053-EXISTS","kind":"DERIVATION","binders":[{"key":"M","type":"Real"}],"uses_definitions":["D-LATE-P053-EXISTS","D-S7B-P053-DOMAIN"],"source_anchors":[],"hypotheses":[{"key":"domain","proposition":{"def":{"id":"D-S7B-P053-DOMAIN","args":[{"var":"M"}]}}}],"witnesses":[],"conclusions":[{"key":"existentialized","proposition":{"def":{"id":"D-LATE-P053-EXISTS","args":[{"var":"M"}]}}}],"premises":[{"id":"use-p-053","producer":"P-053","closure_role":"REQUIRED","binder_map":{"M":{"var":"M"}},"hypothesis_map":{"domain":{"hypothesis":"domain"}},"witness_map":{"C_ps":"a_late_p053_exists_C_ps"},"consume":["partial_summation"]}],"witness_realizations":{},"proof_ref":"### P-053 — endpoint-safe partial sum"}
```

```mathminer-s3-legacy
{"schema":"mathminer.s3/1","id":"A-LATE-P055-EXISTS","kind":"DERIVATION","binders":[{"key":"theta","type":"Real"},{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"},{"key":"K_sh","type":"Nat"},{"key":"z","type":"Real"}],"uses_definitions":["D-LATE-P055-EXISTS","D-S7-P051V-DOMAIN","D-S7B-P055-DOMAIN"],"source_anchors":[],"hypotheses":[{"key":"domain","proposition":{"def":{"id":"D-S7B-P055-DOMAIN","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"},{"var":"K_sh"},{"var":"z"}]}}},{"key":"family_domain","proposition":{"def":{"id":"D-S7-P051V-DOMAIN","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"}]}}}],"witnesses":[],"conclusions":[{"key":"existentialized","proposition":{"def":{"id":"D-LATE-P055-EXISTS","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"},{"var":"K_sh"},{"var":"z"}]}}}],"premises":[{"id":"use-p-055","producer":"P-055","closure_role":"REQUIRED","binder_map":{"theta":{"var":"theta"},"y":{"var":"y"},"k":{"var":"k"},"sigma":{"var":"sigma"},"K_sh":{"var":"K_sh"},"z":{"var":"z"}},"hypothesis_map":{"domain":{"hypothesis":"domain"},"family_domain":{"hypothesis":"family_domain"}},"witness_map":{"C_up":"a_late_p055_exists_C_up"},"consume":["shifted_t_bound"]}],"witness_realizations":{},"proof_ref":"### P-055 — regular upper shifted \\(t\\)-mean"}
```

```mathminer-s3-legacy
{"schema":"mathminer.s3/1","id":"A-LATE-P056-EXISTS","kind":"DERIVATION","binders":[{"key":"theta","type":"Real"},{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"},{"key":"K_sh","type":"Nat"},{"key":"z","type":"Real"}],"uses_definitions":["D-LATE-P056-EXISTS","D-S7-P051V-DOMAIN","D-S7B-P056-DOMAIN"],"source_anchors":[],"hypotheses":[{"key":"domain","proposition":{"def":{"id":"D-S7B-P056-DOMAIN","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"},{"var":"K_sh"},{"var":"z"}]}}},{"key":"family_domain","proposition":{"def":{"id":"D-S7-P051V-DOMAIN","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"}]}}}],"witnesses":[],"conclusions":[{"key":"existentialized","proposition":{"def":{"id":"D-LATE-P056-EXISTS","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"},{"var":"K_sh"},{"var":"z"}]}}}],"premises":[{"id":"use-p-056","producer":"P-056","closure_role":"REQUIRED","binder_map":{"theta":{"var":"theta"},"y":{"var":"y"},"k":{"var":"k"},"sigma":{"var":"sigma"},"K_sh":{"var":"K_sh"},"z":{"var":"z"}},"hypothesis_map":{"domain":{"hypothesis":"domain"},"family_domain":{"hypothesis":"family_domain"}},"witness_map":{"C_mid":"a_late_p056_exists_C_mid"},"consume":["shifted_t_bound"]}],"witness_realizations":{},"proof_ref":"### P-056 — regular middle shifted \\(t\\)-mean"}
```

```mathminer-s3-legacy
{"schema":"mathminer.s3/1","id":"A-LATE-P058-EXISTS","kind":"DERIVATION","binders":[{"key":"theta","type":"Real"},{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"},{"key":"x","type":"Real"}],"uses_definitions":["D-LATE-P058-EXISTS","D-S7-P051V-DOMAIN","D-S7B-P058-DOMAIN"],"source_anchors":[],"hypotheses":[{"key":"domain","proposition":{"def":{"id":"D-S7B-P058-DOMAIN","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"},{"var":"x"}]}}},{"key":"family_domain","proposition":{"def":{"id":"D-S7-P051V-DOMAIN","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"}]}}}],"witnesses":[],"conclusions":[{"key":"existentialized","proposition":{"def":{"id":"D-LATE-P058-EXISTS","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"},{"var":"x"}]}}}],"premises":[{"id":"use-p-058","producer":"P-058","closure_role":"REQUIRED","binder_map":{"theta":{"var":"theta"},"y":{"var":"y"},"k":{"var":"k"},"sigma":{"var":"sigma"},"x":{"var":"x"}},"hypothesis_map":{"domain":{"hypothesis":"domain"},"family_domain":{"hypothesis":"family_domain"}},"witness_map":{"C_out":"a_late_p058_exists_C_out"},"consume":["outer_bound"]}],"witness_realizations":{},"proof_ref":"### P-058 — regular outer shifted mean"}
```

```mathminer-s3-legacy
{"schema":"mathminer.s3/1","id":"A-LATE-P059-EXISTS","kind":"DERIVATION","binders":[{"key":"Q","type":"Type"},{"key":"w_family","type":{"fn":{"args":[{"var":"Q"}],"return":{"fn":{"args":["Nat"],"return":"Real"}}}}},{"key":"c_w","type":"Real"},{"key":"C_w_err","type":"Real"},{"key":"Lambda_w","type":"Real"},{"key":"q","type":{"var":"Q"}},{"key":"Z","type":"Real"}],"uses_definitions":["D-LATE-P059-EXISTS","D-S7B-P059-DOMAIN"],"source_anchors":[],"hypotheses":[{"key":"domain","proposition":{"def":{"id":"D-S7B-P059-DOMAIN","args":[{"var":"Q"},{"var":"w_family"},{"var":"c_w"},{"var":"C_w_err"},{"var":"Lambda_w"},{"var":"q"},{"var":"Z"}]}}}],"witnesses":[],"conclusions":[{"key":"existentialized","proposition":{"def":{"id":"D-LATE-P059-EXISTS","args":[{"var":"Q"},{"var":"w_family"},{"var":"c_w"},{"var":"C_w_err"},{"var":"Lambda_w"},{"var":"q"},{"var":"Z"}]}}}],"premises":[{"id":"use-p-059","producer":"P-059","closure_role":"REQUIRED","binder_map":{"Q":{"var":"Q"},"w_family":{"var":"w_family"},"c_w":{"var":"c_w"},"C_w_err":{"var":"C_w_err"},"Lambda_w":{"var":"Lambda_w"},"q":{"var":"q"},"Z":{"var":"Z"}},"hypothesis_map":{"domain":{"hypothesis":"domain"}},"witness_map":{"C_mean":"a_late_p059_exists_C_mean"},"consume":["family_mean"]}],"witness_realizations":{},"proof_ref":"### P-059 — family-uniform mean with exposed common witnesses"}
```

```mathminer-s3-legacy
{"schema":"mathminer.s3/1","id":"A-LATE-P020-EXISTS","kind":"DERIVATION","binders":[{"key":"epsilon_int","type":"Real"},{"key":"xi","type":"Real"},{"key":"sigma","type":"Real"},{"key":"theta","type":"Real"}],"uses_definitions":["D-LATE-P020-EXISTS","D-S45-EPS-DOMAIN","D-S45-P020-DOMAIN"],"source_anchors":[],"hypotheses":[{"key":"domain","proposition":{"def":{"id":"D-S45-P020-DOMAIN","args":[{"var":"epsilon_int"},{"var":"xi"},{"var":"sigma"},{"var":"theta"}]}}},{"key":"epsilon_domain","proposition":{"def":{"id":"D-S45-EPS-DOMAIN","args":[{"var":"epsilon_int"}]}}}],"witnesses":[],"conclusions":[{"key":"existentialized","proposition":{"def":{"id":"D-LATE-P020-EXISTS","args":[{"var":"epsilon_int"},{"var":"xi"},{"var":"sigma"},{"var":"theta"}]}}}],"premises":[{"id":"use-p-020","producer":"P-020","closure_role":"REQUIRED","binder_map":{"epsilon_int":{"var":"epsilon_int"},"xi":{"var":"xi"},"sigma":{"var":"sigma"},"theta":{"var":"theta"}},"hypothesis_map":{"domain":{"hypothesis":"domain"},"epsilon_domain":{"hypothesis":"epsilon_domain"}},"witness_map":{"C_grid":"a_late_p020_exists_C_grid","Xi_0":"a_late_p020_exists_Xi_0","A":"a_late_p020_exists_A"},"consume":["lemma4_witness"]}],"witness_realizations":{},"proof_ref":"### P-020 — combined Lemma-4 witness theorem"}
```

### P-052 — exact reciprocal-divisor smoothing

```mathminer-s3
{"schema":"mathminer.s3/1","id":"P-052","kind":"PROPOSITION","binders":[{"key":"theta","type":"Real"},{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"},{"key":"K_sh","type":"Nat"},{"key":"z","type":"Real"}],"uses_definitions":["D-001","D-006","D-015","D-S45-P001C-DOMAIN","D-S45-SHIFT-FAMILY-DOMAIN","D-S7-P051V-DOMAIN","D-S7B-P052-DOMAIN","D-S7B-P052-RESULT","D-S7B-P052-W"],"source_anchors":[],"hypotheses":[{"key":"domain","proposition":{"def":{"id":"D-S7B-P052-DOMAIN","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"},{"var":"K_sh"},{"var":"z"}]}}},{"key":"family_domain","proposition":{"def":{"id":"D-S7-P051V-DOMAIN","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"}]}}}],"witnesses":[{"key":"C_sm","type":"Real","depends_on":["theta"]}],"conclusions":[{"key":"smoothing_bound","proposition":{"def":{"id":"D-S7B-P052-RESULT","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"},{"var":"K_sh"},{"var":"z"},{"var":"C_sm"}]}}}],"premises":[{"id":"MAP-P052-P005","producer":"A-S7-P005-EXISTS","closure_role":"REQUIRED","binder_map":{"lambda_seq":{"lambda":{"binders":[{"key":"i_seq","type":"Nat"}],"body":{"lit":{"type":"Real","value":"1"}}}},"lambda":{"lit":{"type":"Real","value":"1"}},"u":{"proj":{"value":{"def":{"id":"D-015","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"}]}},"index":0}},"v":{"lambda":{"binders":[{"key":"n_const","type":"Nat"}],"body":{"lit":{"type":"Real","value":"1"}}}},"K_sh":{"var":"K_sh"},"X":{"var":"z"}},"hypothesis_map":{"domain":{"guard":"MAP-P052-P005_domain"}},"witness_map":{},"consume":["shifted_mean_exists"],"guards":[{"key":"MAP-P052-P005_domain","proposition":{"def":{"id":"D-S45-SHIFT-FAMILY-DOMAIN","args":[{"lambda":{"binders":[{"key":"i_seq","type":"Nat"}],"body":{"lit":{"type":"Real","value":"1"}}}},{"lit":{"type":"Real","value":"1"}},{"proj":{"value":{"def":{"id":"D-015","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"}]}},"index":0}},{"lambda":{"binders":[{"key":"n_const","type":"Nat"}],"body":{"lit":{"type":"Real","value":"1"}}}},{"var":"K_sh"},{"var":"z"}]}}}]},{"id":"MAP-P052-P001C","producer":"P-001C","closure_role":"REQUIRED","binder_map":{"K_sh":{"var":"K_sh"},"z":{"var":"z"}},"hypothesis_map":{"domain":{"guard":"p001c_domain"}},"witness_map":{},"consume":["bounded_reciprocal_smoothing"],"guards":[{"key":"p001c_domain","proposition":{"def":{"id":"D-S45-P001C-DOMAIN","args":[{"var":"K_sh"},{"var":"z"}]}}}]},{"id":"MAP-P052-P051A","producer":"P-051A","closure_role":"REQUIRED","binder_map":{},"hypothesis_map":{},"witness_map":{"c_0":"p052_c0","C_0":"p052_C0","Lambda_0":"p052_L0"},"consume":["base_type"]},{"id":"MAP-P052-F1","producer":"P-051F1","closure_role":"REQUIRED","binder_map":{},"hypothesis_map":{},"witness_map":{"c_1":"MAP-P052_c1","C_1":"MAP-P052_C1","Lambda_1":"MAP-P052_L1"},"consume":["weight_type","dominates_base","dominates_shift"]}],"witness_realizations":{"C_sm":{"def":{"id":"D-S7B-P052-W","args":[{"var":"theta"}]}}},"proof_ref":"### P-052 — exact reciprocal-divisor smoothing"}
```

- Prenex statement:
  \[
  \forall\theta\ge2\;\exists C_{\rm sm}(\theta)>0\;
  \forall y\in(0,1)\;\forall k\ge1\;\forall\sigma\ge\theta\;
  \forall K_{\rm sh}\ge1\;\forall z>0,
  \]
  \[
  \sum_{m<z}\tau(mK_{\rm sh})^{-1}
  \le C_{\rm sm}(\theta)w_1(K_{\rm sh})
  \sum_{m<z}\ell(m)^{-1/2}.
  \]
- Local equalities: \(w_1\) is exactly D-015.
- Domain/range: constant chosen after its only allowed dependency \(\theta\)
  and before \(y,k,\sigma,K_{\rm sh},z,m\); hence uniform in all of them.
- Input subject: exact reciprocal-divisor shifted mean.
  Output subject: exact smoothed finite sum.
- Premise maps:
  - `MAP-P052-P005`, branch \(z\ge2\):

    | producer | producer slot | producer domain | consumer term | domain evidence |
    |---|---|---|---|---|
    | P-005 | `u` | nonnegative multiplicative | \(a_0:r\mapsto1/\tau(r)\) | D-015/P-051A |
    | P-005 | `v` | nonnegative multiplicative | constant \(1\) | elementary |
    | P-005 | `K_sh` | \(\mathbb N_{>0}\) | \(K_{\rm sh}\) | binder |
    | P-005 | `X` | \(\mathbb R_{\ge2}\) | \(z\) | branch hypothesis |
    | P-005 | `(lambda_i)` | nonnegative sequence | \(\lambda_i:=1\) for every \(i\in\mathbb N\) | \(a_0(p^{i+j})\le1\) |
    | P-005 | `lambda` | \([0,2)\) | \(1\) | \(1<2\) |

    Producer hypothesis: \(0\le a_0(p^{i+j})\le1\).
    Consumed conclusion is P-005's exact shifted-mean upper bound.
    Subject `SUB-P052-RAW` is literally the left sum; its Euler output is
    `SUB-P052-EULER`. The P-005 constant depends only on the fixed local
    majorants \((1,1)\) and is uniform in \((K_{\rm sh},z)\).
  - `MAP-P052-P007`, branch \(z\ge2\):

    | producer | producer slot | producer domain | consumer term | domain evidence |
    |---|---|---|---|---|
    | P-007 | `c` | \(\mathbb R\) | \(1/2\) | local expansion |
    | P-007 | `eta` | \(\mathbb R_{>0}\) | \(1\) | positive |
    | P-007 | `C_err` | \(\mathbb R_{>0}\) | \(C_{a_0}:=2\) | direct series tail bound |
    | P-007 | `(L_p)` | positive prime family | \(L_p:=\sum_{j\ge0}a_0(p^j)p^{-j}\) | first term is 1, all terms nonnegative |
    | P-007 | `A` | \(\mathbb R_{\ge2}\) | \(2\) | literal |
    | P-007 | `B` | \(\mathbb R_{\ge2}\) | \(z\) | branch hypothesis |

    Hypothesis: \(|L_p-(1+1/(2p))|\le2p^{-2}\), since
    \(a_0(p)=1/2\) and
    \(\sum_{j\ge2}a_0(p^j)p^{-j}\le\sum_{j\ge2}p^{-j}\le2p^{-2}\).
    Consumed conclusion is P-007's exact product comparison. Subject
    `SUB-P052-EULER` is exactly the P-005 Euler product; no adapter is needed.
    Constants map as absolute data \((1/2,1,2)\to C\to z\), uniformly in
    \(K_{\rm sh}\).
  - `MAP-P052-P001C`, branch \(0<z<2\): slots
    \(K_{\rm sh}:=K_{\rm sh},z:=z\); its conclusion is exactly the
    P-052 inequality with constant \(1\).
  - `MAP-P052-P051A`: consume the exact nonnegative multiplicative base
    \(a_0=1/\tau\) and its bound \(0\le a_0(p^i)\le1\), used to discharge
    the P-005 local hypotheses. No other shifted-weight conclusion is used.
  - `MAP-P052-P051F1`: the exact D-015 instantiation
    \(w_1=\widehat{\mathcal S}[a_0,1]\) maps identically; consume its type and
    integer domination \(w_1(K_{\rm sh})\ge a_0(K_{\rm sh})\).  Its absolute
    witnesses are absorbed into \(C_{\rm sm}(\theta)\).  No family
    consolidation or Euler-tail result is consumed.
- Derivation certificate: on \(z\ge2\), P-005 and P-007 give
  \(w_1(K_{\rm sh})z\ell(z)^{-1/2}\); endpoint-safe partial summation
  gives the displayed smoothed sum. On \(0<z<2\), invoke P-001C. These
  branches assemble the all-\(z>0\) statement; no illegal cutoff is sent to
  P-005 or EXT-001.
- Source/S2 anchor: ET p. 30; S2 R1 (5.2), R2.4.
- Definitions used: D-001, D-006, D-015.

### P-053 — endpoint-safe partial sum

```mathminer-s3
{"schema":"mathminer.s3/1","id":"P-053","kind":"PROPOSITION","binders":[{"key":"M","type":"Real"}],"uses_definitions":["D-S7B-P053-DOMAIN","D-S7B-P053-RESULT","D-S7B-P053-W"],"source_anchors":[],"hypotheses":[{"key":"domain","proposition":{"def":{"id":"D-S7B-P053-DOMAIN","args":[{"var":"M"}]}}}],"witnesses":[{"key":"C_ps","type":"Real","depends_on":[]}],"conclusions":[{"key":"partial_summation","proposition":{"def":{"id":"D-S7B-P053-RESULT","args":[{"var":"M"},{"var":"C_ps"}]}}}],"premises":[],"witness_realizations":{"C_ps":{"def":{"id":"D-S7B-P053-W","args":[]}}},"proof_ref":"### P-053 — endpoint-safe partial sum"}
```

- Prenex statement: there exists an absolute \(C_{\rm ps}>0\) such that
  for every \(M>0\),
  \[
  \sum_{1\le m<M}\ell(m)^{-1/2}
  \le C_{\rm ps}M\ell(2M)^{-1/2}.
  \]
- Local equalities: none.
- Domain/range: \(C_{\rm ps}\) precedes the uniform variable \(M\).
- Input subject: exact safe-log partial sum. Output: endpoint-safe bound.
- Premise maps: none (root).
- Derivation certificate: bounded \(M\) directly; for \(M\ge4\), split at
  \(\sqrt M\) and use \(\log m\ge\frac12\log M\) on the upper part.
- Source/S2 anchor: ET p. 31 convention; S2 R2.6.
- Definitions used: D-006.

### P-054 — half-open close-pair product window

```mathminer-s3
{"schema":"mathminer.s3/1","id":"P-054","kind":"PROPOSITION","binders":[{"key":"d","type":"Nat"},{"key":"d_prime","type":"Nat"},{"key":"k","type":"Nat"},{"key":"theta","type":"Real"}],"uses_definitions":["D-005","D-S7B-P054-DOMAIN","D-S7B-P054-RESULT"],"source_anchors":[],"hypotheses":[{"key":"domain","proposition":{"def":{"id":"D-S7B-P054-DOMAIN","args":[{"var":"d"},{"var":"d_prime"},{"var":"k"},{"var":"theta"}]}}}],"witnesses":[],"conclusions":[{"key":"close_window","proposition":{"def":{"id":"D-S7B-P054-RESULT","args":[{"var":"d"},{"var":"d_prime"},{"var":"k"},{"var":"theta"}]}}}],"premises":[],"witness_realizations":{},"proof_ref":"### P-054 — half-open close-pair product window"}
```

- Prenex statement: for every \(k\ge1,\theta>1,d,d'>0\), if
  \(\theta^k\le d<\theta^{k+1}\) and
  \({\rm Close}_\theta(d,d')\), then
  \[
  \theta^{2k-1}<dd'<\theta^{2k+3},\qquad
  \theta^{k-1}<d'<\theta^{k+2}.
  \]
- Local equalities: none.
- Domain/range: lower \(d\)-endpoint is weak; all product/pair endpoints are
  strict because closeness is strict.
- Input subject: one half-open close pair. Output: exact two windows.
- Premise maps: none (root).
- Derivation certificate: combine
  \(d/\theta<d'<\theta d\) with the bin endpoints.
- Source/S2 anchor: ET pp. 30–31; S2 R2.3.
- Definitions used: D-005.

### P-054A — nonnegative interval-to-initial-segment adapters

```mathminer-s3
{"schema":"mathminer.s3/1","id":"P-054A","kind":"PROPOSITION","binders":[{"key":"k","type":"Nat"},{"key":"theta","type":"Real"},{"key":"sigma","type":"Real"},{"key":"g","type":{"fn":{"args":["Nat"],"return":"Real"}}}],"uses_definitions":["D-S7B-P054A-DOMAIN","D-S7B-P054A-RESULT"],"source_anchors":[],"hypotheses":[{"key":"domain","proposition":{"def":{"id":"D-S7B-P054A-DOMAIN","args":[{"var":"k"},{"var":"theta"},{"var":"sigma"},{"var":"g"}]}}}],"witnesses":[],"conclusions":[{"key":"initial_enlargements","proposition":{"def":{"id":"D-S7B-P054A-RESULT","args":[{"var":"k"},{"var":"theta"},{"var":"sigma"},{"var":"g"}]}}}],"premises":[],"witness_realizations":{},"proof_ref":"### P-054A — nonnegative interval-to-initial-segment adapters"}
```

- Prenex statement: for every \(g:\mathbb N_{>0}\to\mathbb R_{\ge0}\),
  \(k\in\mathbb N_{\ge1}\), \(\theta\ge2\), and \(\sigma>0\),
  \[
  \sum_{\theta^k\le d<\theta^{k+1}}g(d)
  \le\sum_{d<\theta^{k+1}}g(d),\qquad
  \sum_{\substack{\sigma\le d<\theta^{k+1}}}g(d)
  \le\sum_{d<\theta^{k+1}}g(d).
  \]
- Dependency order: fixed \(g\) -> no witnesses -> uniform
  \(k,\theta,\sigma\).
- Subject IDs: `SUB-REG-INTERVAL`, `SUB-TR-INTERVAL`, and
  `SUB-OUTER-INITIAL`. The adapters are respectively `AD-REG-INIT` and
  `AD-TR-INIT`; they use only restriction and nonnegativity.
- Premise maps: none.

### P-055 — regular upper shifted \(t\)-mean

Current construction binding: the exact `P055Statement` in the GroupA--GroupD source contracts, W0--W8, and the retained S7 provider. Any `mathminer-s3-legacy` block here is historical, not a proof.

```mathminer-s3-legacy
{"schema":"mathminer.s3/1","id":"P-055","kind":"PROPOSITION","binders":[{"key":"theta","type":"Real"},{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"},{"key":"K_sh","type":"Nat"},{"key":"z","type":"Real"}],"uses_definitions":["D-006","D-015","D-016","D-S45-P007-DOMAIN","D-S45-P008-DOMAIN","D-S45-SHIFT-FAMILY-DOMAIN","D-S7-P051V-DOMAIN","D-S7A-MODIFIER","D-S7A-PRIME","D-S7A-SELECTED-WEIGHT","D-S7B-P055-DOMAIN","D-S7B-P055-RESULT","D-S7B-P055-W","D-S811-CERR","D-S811-ETA","D-S811-LAMBDA-SEQ","D-S811-P055-C-0","D-S811-P055-C-HI","D-S811-P055-C-MID","D-S811-P055-L-0","D-S811-P055-L-HI","D-S811-P055-L-MID","D-S811-P055-POINT-0","D-S811-P055-POINT-HI","D-S811-P055-POINT-MID","D-S811-P055-Q"],"source_anchors":[],"hypotheses":[{"key":"domain","proposition":{"def":{"id":"D-S7B-P055-DOMAIN","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"},{"var":"K_sh"},{"var":"z"}]}}},{"key":"family_domain","proposition":{"def":{"id":"D-S7-P051V-DOMAIN","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"}]}}}],"witnesses":[{"key":"C_up","type":"Real","depends_on":["theta"]}],"conclusions":[{"key":"shifted_t_bound","proposition":{"def":{"id":"D-S7B-P055-RESULT","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"},{"var":"K_sh"},{"var":"z"},{"var":"C_up"}]}}}],"premises":[{"id":"MAP-P055-P005","producer":"A-S7-P005-EXISTS","closure_role":"REQUIRED","binder_map":{"lambda_seq":{"def":{"id":"D-S811-LAMBDA-SEQ","args":[]}},"lambda":{"lit":{"type":"Real","value":"1"}},"u":{"proj":{"value":{"def":{"id":"D-015","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"}]}},"index":2}},"v":{"proj":{"value":{"def":{"id":"D-015","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"}]}},"index":1}},"K_sh":{"var":"K_sh"},"X":{"var":"z"}},"hypothesis_map":{"domain":{"guard":"MAP-P055-P005_domain"}},"witness_map":{},"consume":["shifted_mean_exists"],"guards":[{"key":"MAP-P055-P005_domain","proposition":{"def":{"id":"D-S45-SHIFT-FAMILY-DOMAIN","args":[{"def":{"id":"D-S811-LAMBDA-SEQ","args":[]}},{"lit":{"type":"Real","value":"1"}},{"proj":{"value":{"def":{"id":"D-015","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"}]}},"index":2}},{"proj":{"value":{"def":{"id":"D-015","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"}]}},"index":1}},{"var":"K_sh"},{"var":"z"}]}}}]},{"id":"MAP-P055-F1","producer":"P-051F1","closure_role":"REQUIRED","binder_map":{},"hypothesis_map":{},"witness_map":{"c_1":"MAP-P055_c1","C_1":"MAP-P055_C1","Lambda_1":"MAP-P055_L1"},"consume":["weight_type","dominates_base","dominates_shift"]},{"id":"MAP-P055-F2","producer":"A-LATE-P051F2-EXISTS","closure_role":"REQUIRED","binder_map":{"theta":{"var":"theta"},"y":{"var":"y"},"k":{"var":"k"},"sigma":{"var":"sigma"}},"hypothesis_map":{"theta_ge_2":{"guard":"MAP-P055-F2_theta_ge_2"},"y_pos":{"guard":"MAP-P055-F2_y_pos"},"y_lt_1":{"guard":"MAP-P055-F2_y_lt_1"},"k_ge_1":{"guard":"MAP-P055-F2_k_ge_1"},"sigma_ge_theta":{"guard":"MAP-P055-F2_sigma_ge_theta"}},"witness_map":{},"consume":["existentialized"],"guards":[{"key":"MAP-P055-F2_theta_ge_2","proposition":{"op":{"name":"ge","args":[{"var":"theta"},{"lit":{"type":"Real","value":"2"}}]}}},{"key":"MAP-P055-F2_y_pos","proposition":{"op":{"name":"gt","args":[{"var":"y"},{"lit":{"type":"Real","value":"0"}}]}}},{"key":"MAP-P055-F2_y_lt_1","proposition":{"op":{"name":"lt","args":[{"var":"y"},{"lit":{"type":"Real","value":"1"}}]}}},{"key":"MAP-P055-F2_k_ge_1","proposition":{"op":{"name":"ge","args":[{"var":"k"},{"lit":{"type":"Nat","value":"1"}}]}}},{"key":"MAP-P055-F2_sigma_ge_theta","proposition":{"op":{"name":"ge","args":[{"var":"sigma"},{"var":"theta"}]}}}]},{"id":"MAP-P055-V","producer":"P-051V","closure_role":"REQUIRED","binder_map":{"theta":{"var":"theta"},"y":{"var":"y"},"k":{"var":"k"},"sigma":{"var":"sigma"}},"hypothesis_map":{"theta_ge_2":{"guard":"MAP-P055-V_theta_ge_2"},"y_pos":{"guard":"MAP-P055-V_y_pos"},"y_lt_1":{"guard":"MAP-P055-V_y_lt_1"},"k_ge_1":{"guard":"MAP-P055-V_k_ge_1"},"sigma_ge_theta":{"guard":"MAP-P055-V_sigma_ge_theta"}},"witness_map":{},"consume":["modifier_normalization"],"guards":[{"key":"MAP-P055-V_theta_ge_2","proposition":{"op":{"name":"ge","args":[{"var":"theta"},{"lit":{"type":"Real","value":"2"}}]}}},{"key":"MAP-P055-V_y_pos","proposition":{"op":{"name":"gt","args":[{"var":"y"},{"lit":{"type":"Real","value":"0"}}]}}},{"key":"MAP-P055-V_y_lt_1","proposition":{"op":{"name":"lt","args":[{"var":"y"},{"lit":{"type":"Real","value":"1"}}]}}},{"key":"MAP-P055-V_k_ge_1","proposition":{"op":{"name":"ge","args":[{"var":"k"},{"lit":{"type":"Nat","value":"1"}}]}}},{"key":"MAP-P055-V_sigma_ge_theta","proposition":{"op":{"name":"ge","args":[{"var":"sigma"},{"var":"theta"}]}}}]},{"id":"MAP-P055-G","producer":"A-LATE-P051G-EXISTS","closure_role":"REQUIRED","binder_map":{"theta":{"var":"theta"},"y":{"var":"y"},"k":{"var":"k"},"sigma":{"var":"sigma"}},"hypothesis_map":{"theta_ge_2":{"guard":"MAP-P055-G_theta_ge_2"},"y_pos":{"guard":"MAP-P055-G_y_pos"},"y_lt_1":{"guard":"MAP-P055-G_y_lt_1"},"k_ge_1":{"guard":"MAP-P055-G_k_ge_1"},"sigma_ge_theta":{"guard":"MAP-P055-G_sigma_ge_theta"}},"witness_map":{},"consume":["existentialized"],"guards":[{"key":"MAP-P055-G_theta_ge_2","proposition":{"op":{"name":"ge","args":[{"var":"theta"},{"lit":{"type":"Real","value":"2"}}]}}},{"key":"MAP-P055-G_y_pos","proposition":{"op":{"name":"gt","args":[{"var":"y"},{"lit":{"type":"Real","value":"0"}}]}}},{"key":"MAP-P055-G_y_lt_1","proposition":{"op":{"name":"lt","args":[{"var":"y"},{"lit":{"type":"Real","value":"1"}}]}}},{"key":"MAP-P055-G_k_ge_1","proposition":{"op":{"name":"ge","args":[{"var":"k"},{"lit":{"type":"Nat","value":"1"}}]}}},{"key":"MAP-P055-G_sigma_ge_theta","proposition":{"op":{"name":"ge","args":[{"var":"sigma"},{"var":"theta"}]}}}]},{"id":"MAP-P055-H","producer":"A-LATE-P051H-EXISTS","closure_role":"REQUIRED","scope_binders":[{"key":"p","type":"Nat"}],"binder_map":{"theta":{"var":"theta"},"y":{"var":"y"},"k":{"var":"k"},"sigma":{"var":"sigma"},"w":{"proj":{"value":{"def":{"id":"D-015","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"}]}},"index":2}},"b":{"proj":{"value":{"def":{"id":"D-015","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"}]}},"index":1}},"p":{"var":"p"}},"hypothesis_map":{"theta_ge_2":{"guard":"MAP-P055-H_theta_ge_2"},"y_pos":{"guard":"MAP-P055-H_y_pos"},"y_lt_1":{"guard":"MAP-P055-H_y_lt_1"},"k_ge_1":{"guard":"MAP-P055-H_k_ge_1"},"sigma_ge_theta":{"guard":"MAP-P055-H_sigma_ge_theta"},"selected_weight":{"guard":"MAP-P055-H_selected_weight"},"modifier_b":{"guard":"MAP-P055-H_modifier_b"},"prime_p":{"guard":"MAP-P055-H_prime_p"}},"witness_map":{},"consume":["existentialized"],"guards":[{"key":"MAP-P055-H_theta_ge_2","proposition":{"op":{"name":"ge","args":[{"var":"theta"},{"lit":{"type":"Real","value":"2"}}]}}},{"key":"MAP-P055-H_y_pos","proposition":{"op":{"name":"gt","args":[{"var":"y"},{"lit":{"type":"Real","value":"0"}}]}}},{"key":"MAP-P055-H_y_lt_1","proposition":{"op":{"name":"lt","args":[{"var":"y"},{"lit":{"type":"Real","value":"1"}}]}}},{"key":"MAP-P055-H_k_ge_1","proposition":{"op":{"name":"ge","args":[{"var":"k"},{"lit":{"type":"Nat","value":"1"}}]}}},{"key":"MAP-P055-H_sigma_ge_theta","proposition":{"op":{"name":"ge","args":[{"var":"sigma"},{"var":"theta"}]}}},{"key":"MAP-P055-H_selected_weight","proposition":{"def":{"id":"D-S7A-SELECTED-WEIGHT","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"},{"proj":{"value":{"def":{"id":"D-015","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"}]}},"index":2}}]}}},{"key":"MAP-P055-H_modifier_b","proposition":{"def":{"id":"D-S7A-MODIFIER","args":[{"proj":{"value":{"def":{"id":"D-015","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"}]}},"index":1}}]}}},{"key":"MAP-P055-H_prime_p","proposition":{"def":{"id":"D-S7A-PRIME","args":[{"var":"p"}]}}}]},{"id":"MAP-P055-P007-0","producer":"A-S45-P007-EXISTS","closure_role":"REQUIRED","binder_map":{"c":{"lit":{"type":"Real","value":"0"}},"eta":{"def":{"id":"D-S811-ETA","args":[]}},"C_err":{"def":{"id":"D-S811-CERR","args":[]}},"L":{"def":{"id":"D-S811-P055-POINT-0","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"},{"var":"z"}]}}},"hypothesis_map":{"domain":{"guard":"MAP-P055-P007-0_domain"}},"witness_map":{},"consume":["existentialized"],"guards":[{"key":"MAP-P055-P007-0_domain","proposition":{"def":{"id":"D-S45-P007-DOMAIN","args":[{"lit":{"type":"Real","value":"0"}},{"def":{"id":"D-S811-ETA","args":[]}},{"def":{"id":"D-S811-CERR","args":[]}},{"def":{"id":"D-S811-P055-POINT-0","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"},{"var":"z"}]}}]}}}]},{"id":"MAP-P055-P008-0","producer":"A-S45-P008-EXISTS","closure_role":"REQUIRED","binder_map":{"Q":{"type":{"named":{"id":"D-S811-P055-Q","args":[{"var":"theta"}]}}},"c_minus":{"lit":{"type":"Real","value":"0"}},"c_plus":{"lit":{"type":"Real","value":"1/2"}},"eta_star":{"def":{"id":"D-S811-ETA","args":[]}},"C_err_star":{"def":{"id":"D-S811-CERR","args":[]}},"P_0":{"lit":{"type":"Real","value":"2"}},"m_fin":{"lit":{"type":"Real","value":"1"}},"M_fin":{"lit":{"type":"Real","value":"1"}},"coeff":{"def":{"id":"D-S811-P055-C-0","args":[{"var":"theta"}]}},"local_factor":{"def":{"id":"D-S811-P055-L-0","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"}]}}},"hypothesis_map":{"domain":{"guard":"MAP-P055-P008-0_domain"}},"witness_map":{},"consume":["existentialized"],"guards":[{"key":"MAP-P055-P008-0_domain","proposition":{"def":{"id":"D-S45-P008-DOMAIN","args":[{"type":{"named":{"id":"D-S811-P055-Q","args":[{"var":"theta"}]}}},{"lit":{"type":"Real","value":"0"}},{"lit":{"type":"Real","value":"1/2"}},{"def":{"id":"D-S811-ETA","args":[]}},{"def":{"id":"D-S811-CERR","args":[]}},{"lit":{"type":"Real","value":"2"}},{"lit":{"type":"Real","value":"1"}},{"lit":{"type":"Real","value":"1"}},{"def":{"id":"D-S811-P055-C-0","args":[{"var":"theta"}]}},{"def":{"id":"D-S811-P055-L-0","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"}]}}]}}}]},{"id":"MAP-P055-P007-MID","producer":"A-S45-P007-EXISTS","closure_role":"REQUIRED","binder_map":{"c":{"op":{"name":"div","args":[{"var":"y"},{"lit":{"type":"Real","value":"2"}}]}},"eta":{"def":{"id":"D-S811-ETA","args":[]}},"C_err":{"def":{"id":"D-S811-CERR","args":[]}},"L":{"def":{"id":"D-S811-P055-POINT-MID","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"},{"var":"z"}]}}},"hypothesis_map":{"domain":{"guard":"MAP-P055-P007-MID_domain"}},"witness_map":{},"consume":["existentialized"],"guards":[{"key":"MAP-P055-P007-MID_domain","proposition":{"def":{"id":"D-S45-P007-DOMAIN","args":[{"op":{"name":"div","args":[{"var":"y"},{"lit":{"type":"Real","value":"2"}}]}},{"def":{"id":"D-S811-ETA","args":[]}},{"def":{"id":"D-S811-CERR","args":[]}},{"def":{"id":"D-S811-P055-POINT-MID","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"},{"var":"z"}]}}]}}}]},{"id":"MAP-P055-P008-MID","producer":"A-S45-P008-EXISTS","closure_role":"REQUIRED","binder_map":{"Q":{"type":{"named":{"id":"D-S811-P055-Q","args":[{"var":"theta"}]}}},"c_minus":{"lit":{"type":"Real","value":"0"}},"c_plus":{"lit":{"type":"Real","value":"1/2"}},"eta_star":{"def":{"id":"D-S811-ETA","args":[]}},"C_err_star":{"def":{"id":"D-S811-CERR","args":[]}},"P_0":{"lit":{"type":"Real","value":"2"}},"m_fin":{"lit":{"type":"Real","value":"1"}},"M_fin":{"lit":{"type":"Real","value":"1"}},"coeff":{"def":{"id":"D-S811-P055-C-MID","args":[{"var":"theta"},{"var":"y"}]}},"local_factor":{"def":{"id":"D-S811-P055-L-MID","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"}]}}},"hypothesis_map":{"domain":{"guard":"MAP-P055-P008-MID_domain"}},"witness_map":{},"consume":["existentialized"],"guards":[{"key":"MAP-P055-P008-MID_domain","proposition":{"def":{"id":"D-S45-P008-DOMAIN","args":[{"type":{"named":{"id":"D-S811-P055-Q","args":[{"var":"theta"}]}}},{"lit":{"type":"Real","value":"0"}},{"lit":{"type":"Real","value":"1/2"}},{"def":{"id":"D-S811-ETA","args":[]}},{"def":{"id":"D-S811-CERR","args":[]}},{"lit":{"type":"Real","value":"2"}},{"lit":{"type":"Real","value":"1"}},{"lit":{"type":"Real","value":"1"}},{"def":{"id":"D-S811-P055-C-MID","args":[{"var":"theta"},{"var":"y"}]}},{"def":{"id":"D-S811-P055-L-MID","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"}]}}]}}}]},{"id":"MAP-P055-P007-HI","producer":"A-S45-P007-EXISTS","closure_role":"REQUIRED","binder_map":{"c":{"lit":{"type":"Real","value":"1/2"}},"eta":{"def":{"id":"D-S811-ETA","args":[]}},"C_err":{"def":{"id":"D-S811-CERR","args":[]}},"L":{"def":{"id":"D-S811-P055-POINT-HI","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"},{"var":"z"}]}}},"hypothesis_map":{"domain":{"guard":"MAP-P055-P007-HI_domain"}},"witness_map":{},"consume":["existentialized"],"guards":[{"key":"MAP-P055-P007-HI_domain","proposition":{"def":{"id":"D-S45-P007-DOMAIN","args":[{"lit":{"type":"Real","value":"1/2"}},{"def":{"id":"D-S811-ETA","args":[]}},{"def":{"id":"D-S811-CERR","args":[]}},{"def":{"id":"D-S811-P055-POINT-HI","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"},{"var":"z"}]}}]}}}]},{"id":"MAP-P055-P008-HI","producer":"A-S45-P008-EXISTS","closure_role":"REQUIRED","binder_map":{"Q":{"type":{"named":{"id":"D-S811-P055-Q","args":[{"var":"theta"}]}}},"c_minus":{"lit":{"type":"Real","value":"0"}},"c_plus":{"lit":{"type":"Real","value":"1/2"}},"eta_star":{"def":{"id":"D-S811-ETA","args":[]}},"C_err_star":{"def":{"id":"D-S811-CERR","args":[]}},"P_0":{"lit":{"type":"Real","value":"2"}},"m_fin":{"lit":{"type":"Real","value":"1"}},"M_fin":{"lit":{"type":"Real","value":"1"}},"coeff":{"def":{"id":"D-S811-P055-C-HI","args":[{"var":"theta"}]}},"local_factor":{"def":{"id":"D-S811-P055-L-HI","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"},{"var":"z"}]}}},"hypothesis_map":{"domain":{"guard":"MAP-P055-P008-HI_domain"}},"witness_map":{},"consume":["existentialized"],"guards":[{"key":"MAP-P055-P008-HI_domain","proposition":{"def":{"id":"D-S45-P008-DOMAIN","args":[{"type":{"named":{"id":"D-S811-P055-Q","args":[{"var":"theta"}]}}},{"lit":{"type":"Real","value":"0"}},{"lit":{"type":"Real","value":"1/2"}},{"def":{"id":"D-S811-ETA","args":[]}},{"def":{"id":"D-S811-CERR","args":[]}},{"lit":{"type":"Real","value":"2"}},{"lit":{"type":"Real","value":"1"}},{"lit":{"type":"Real","value":"1"}},{"def":{"id":"D-S811-P055-C-HI","args":[{"var":"theta"}]}},{"def":{"id":"D-S811-P055-L-HI","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"},{"var":"z"}]}}]}}}]}],"witness_realizations":{"C_up":{"def":{"id":"D-S7B-P055-W","args":[{"var":"theta"}]}}},"proof_ref":"### P-055 — regular upper shifted \\(t\\)-mean"}
```

- Prenex statement:
  \[
  \forall\theta\ge2\;\exists C_{\rm up}(\theta)>0\;
  \forall y\in(0,1)\;\forall k\ge1\;\forall\sigma\ge\theta\;
  \forall K_{\rm sh}\ge1\;\forall z\ge\theta^k,
  \]
  if \(\sigma\le\theta^k\), then
  \[
  T_k(z,K_{\rm sh})\le C_{\rm up}(\theta)
  zw_{2,k}(K_{\rm sh})(\log\sigma)^{-y/2}
  k^{(y-1)/2}\ell(z)^{-1/2}.
  \]
- Local equalities: \(T_k,w_{2,k}\) are D-016/D-015.
- Domain/range: constant is uniform in \(y,k,\sigma,K_{\rm sh},z\).
- Input subject: exact \(T_k(z,K_{\rm sh})\). Output: exact upper factor.
- Premise maps:
  - `MAP-P055-P005`:

    | producer | slot | domain | consumer term | evidence |
    |---|---|---|---|---|
    | P-005 | `u` | nonnegative multiplicative | \(w_1\) | P-051F1 |
    | P-005 | `v` | nonnegative multiplicative, normalized by `v(1)=1` | \(v_k\) | P-051V full-domain multiplicativity and normalization |
    | P-005 | `K_sh` | \(\mathbb N_{>0}\) | \(K_{\rm sh}\) | binder |
    | P-005 | `X` | \(\mathbb R_{\ge2}\) | \(z\) | \(z\ge\theta^k\ge2\) |
    | P-005 | `(lambda_i)` | nonnegative sequence | \(\lambda_i:=\Lambda_*\) for every \(i\) | P-051G common local bound |
    | P-005 | `lambda` | \([0,2)\) | \(1\) | P-051V full prime-power bound |

    Producer hypothesis is P-051G's common local bound. Consumed conclusion is
    P-005's exact shifted-mean estimate. Subject is literally
    `SUB-T` from D-016; its shift factor is dominated by
    \(w_{2,k}(K_{\rm sh})\). The producer constant uses only
    \((\Lambda_*,1)\) and precedes \((y,k,\sigma,K_{\rm sh},z)\).
  - `MAP-P055-P007` is the following three-application row table (tuple
    entries are ordered by the three literal prime ranges):

    | producer | slot | domain | consumer term tuple | evidence |
    |---|---|---|---|---|
    | P-007 | `c` | \(\mathbb R\) | \((0,y/2,1/2)\) | exact first coefficients |
    | P-007 | `eta` | \(\mathbb R_{>0}\) | \((\eta_*,\eta_*,\eta_*)\), \(\eta_*:=\min(c_*,1)\) | P-051H |
    | P-007 | `C_err` | \(\mathbb R_{>0}\) | \((C_E,C_E,C_E)\), \(C_E:=C_{E,*}=C_*+2\Lambda_*\) | common error bound |
    | P-007 | `(L_p)` | positive prime family | in each range \(L_p:=\sum_{j\ge0}w_1(p^j)v_k(p^j)p^{-j}\) | constant term 1 |
    | P-007 | `A` | \(\mathbb R_{\ge2}\) | \((2,\sigma,\theta^k)\) | \(2\le\sigma\le\theta^k\le z\) |
    | P-007 | `B` | \(\mathbb R_{\ge2}\) | \((\sigma,\theta^k,z)\) | same chain |

    In each tuple application the P-007 prime family is global: it equals the
    displayed Euler factor on that application's consumed interval and equals
    the exact model \(1+c/p\) outside it. Thus its error hypothesis holds for
    every prime, while its product on \([A,B)\) is unchanged. On the ranges
    the exact identities are respectively \(L_p=1\),
    \(L_p=1+(y/2)p^{-1}+O(C_Ep^{-1-\eta_*})\), and
    \(L_p=1+(1/2)p^{-1}+O(C_Ep^{-1-\eta_*})\).

    P-007's empty-range branch is used whenever endpoints coincide. Adapter
    `AD-P055-EULER-SPLIT` says the product of these literal prime ranges is
    exactly the P-005 Euler subject. Constant order is
    \((c_*,C_*,\Lambda_*)\to C_{\rm up}(\theta)\to y,k,\sigma,K_{\rm sh},z\).
  - `MAP-P055-P008`: define the endpoint-indexed set
    \[
    Q_{\rm up}:=\{q=(\theta,y,k,\sigma,z):\theta\ge2,\ 0<y<1,
    k\ge1,\ \theta\le\sigma\le\theta^k,\ z\ge\theta^k\}.
    \]
    For \(q=(\theta,y,k,\sigma,z)\in Q_{\rm up}\), define first the literal
    Euler factor, using the D-015 functions determined by
    \((\theta,y,k,\sigma)\),
    \[
    E_{q,p}:=\sum_{j\ge0}w_1(p^j)v_k(p^j)p^{-j},
    \]
    and define three global positive prime families, as literal functions of
    \((q,p)\) alone, by
    \[
    L^{\rm up,0}_{q,p}:=
    \begin{cases}E_{q,p},&2\le p<\sigma,\\1,&\text{otherwise},\end{cases}
    \quad
    L^{\rm up,mid}_{q,p}:=
    \begin{cases}E_{q,p},&\sigma\le p<\theta^k,\\1+y/(2p),&\text{otherwise},\end{cases}
    \]
    \[
    L^{\rm up,hi}_{q,p}:=
    \begin{cases}E_{q,p},&\theta^k\le p<z,\\1+1/(2p),&\text{otherwise}.
    \end{cases}
    \tag{L055-family}
    \]
    Thus the moving endpoint \(z\), and all data defining the third active
    factor, belong to the fixed family index before P-008 chooses its
    comparison constants. Apply P-008 to these three families with coefficient
    maps \(q\mapsto0,q\mapsto y/2,q\mapsto1/2\) and common data
    \(c_-:=0,c_+:=1/2,\eta_*:=\min(c_*,1),
    C_{\rm err,*}:=C_{E,*},P_0:=2,m_{\rm fin}:=M_{\rm fin}:=1\).
    On each active interval P051H-main supplies the displayed common error;
    outside it the error is zero by (L055-family). Hence the error, prefix,
    coefficient, and positivity data are independent of \(z\), and the finite
    prefix below \(P_0=2\) is vacuous. The consumed conclusions are the three
    family-uniform product comparisons and assemble by
    `AD-P055-EULER-SPLIT`. Their constants are selected after the complete
    \(Q_{\rm up}\)-indexed families and before \((q,A,B)\), so they remain
    uniform in \(z\) and license \(C_{\rm up}(\theta)\).

    | producer | slot | domain | consumer term tuple | evidence |
    |---|---|---|---|---|
    | P-008 | `Q` | nonempty index set | \(Q_{\rm up}\) | e.g. \((2,1/2,1,2,2)\) |
    | P-008 | `c_-` | \(\mathbb R\) | \(0\) | common lower endpoint |
    | P-008 | `c_+` | \(\mathbb R\), \(c_-\le c_+\), \(1+c_-/2>0\) | \(1/2\) | admissible compact interval |
    | P-008 | `eta_*` | \(\mathbb R_{>0}\) | \(\min(c_*,1)\) | P-051H |
    | P-008 | `C_err,*` | \(\mathbb R_{>0}\) | \(C_{E,*}\) | P051H-main |
    | P-008 | `P_0` | \(\mathbb R_{\ge2}\) | \(2\) | literal |
    | P-008 | `m_fin` | \(\mathbb R_{>0}\) | \(1\) | empty prefix |
    | P-008 | `M_fin` | \(\mathbb R_{\ge m_{\rm fin}}\) | \(1\) | empty prefix |
    | P-008 | `c` | maps into \([0,1/2]\) | \((q\mapsto0,q\mapsto y/2,q\mapsto1/2)\) | \(0<y<1\) from \(q\in Q_{\rm up}\) |
    | P-008 | `L` | positive factor families | \((L^{\rm up,0}_{q,p},L^{\rm up,mid}_{q,p},L^{\rm up,hi}_{q,p})\) from (L055-family) | literal functions of \((q,p)\); P051H-main |
    | P-008 | `q` | \(Q_{\rm up}\) | \((\theta,y,k,\sigma,z)\) | complete upper-domain tuple, including the active endpoint |
    | P-008 | `A` | \(\mathbb R_{\ge2}\) | \((2,\sigma,\theta^k)\) | regular endpoint chain |
    | P-008 | `B` | \(\mathbb R_{\ge2}\) | \((\sigma,\theta^k,z)\) | P-055 domain |
  - `MAP-P055-P051F2`: bind \((\theta,y,k,\sigma)\) identically and consume
    the exact construction \(w_{2,k}=\widehat{\mathcal S}[w_1,v_k]\) and
    its domination of the P-005 shift factor.
  - `MAP-P055-P051F1`: consume only the exact nonnegative multiplicative
    identity of \(w_1\) used as P-005's first weight.
  - `MAP-P055-P051V`: bind \((\theta,y,k,\sigma)\) identically and consume
    exactly nonnegative multiplicativity of \(v_k\), \(v_k(1)=1\), and
    \(0\le v_k(p^j)\le1\) for every prime \(p\) and \(j\in\mathbb N\),
    discharging every P-005 modifier slot.
  - `MAP-P055-P051G`: consume only the common local bounds for \(w_1\);
    specialize \((c_*,C_*,\Lambda_*)\).
  - `MAP-P055-P051H`: consume only (P051H-main) for the three exact local
    Euler families above, with \(b:=v_k\); P-051V supplies the literal
    modifier hypotheses for that specialization.
- Derivation certificate: local first-order coefficients are
  \(0,y/2,1/2\); apply the mapped shifted theorem and Euler comparison.
- Source/S2 anchor: ET pp. 30–31; S2 R2.14 upper line.
- Definitions used: D-006, D-015, D-016.

### P-056 — regular middle shifted \(t\)-mean

Current construction binding: the exact `P056Statement` in the GroupA--GroupD source contracts, W0--W8, and the retained S7 provider. Any `mathminer-s3-legacy` block here is historical, not a proof.

```mathminer-s3-legacy
{"schema":"mathminer.s3/1","id":"P-056","kind":"PROPOSITION","binders":[{"key":"theta","type":"Real"},{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"},{"key":"K_sh","type":"Nat"},{"key":"z","type":"Real"}],"uses_definitions":["D-006","D-015","D-016","D-S45-P007-DOMAIN","D-S45-P008-DOMAIN","D-S45-SHIFT-FAMILY-DOMAIN","D-S7-P051V-DOMAIN","D-S7A-MODIFIER","D-S7A-PRIME","D-S7A-SELECTED-WEIGHT","D-S7B-P056-DOMAIN","D-S7B-P056-RESULT","D-S7B-P056-W","D-S811-CERR","D-S811-ETA","D-S811-LAMBDA-SEQ","D-S811-P056-C-0","D-S811-P056-C-ACT","D-S811-P056-L-0","D-S811-P056-L-ACT","D-S811-P056-POINT-0","D-S811-P056-POINT-ACT","D-S811-P056-Q"],"source_anchors":[],"hypotheses":[{"key":"domain","proposition":{"def":{"id":"D-S7B-P056-DOMAIN","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"},{"var":"K_sh"},{"var":"z"}]}}},{"key":"family_domain","proposition":{"def":{"id":"D-S7-P051V-DOMAIN","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"}]}}}],"witnesses":[{"key":"C_mid","type":"Real","depends_on":["theta"]}],"conclusions":[{"key":"shifted_t_bound","proposition":{"def":{"id":"D-S7B-P056-RESULT","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"},{"var":"K_sh"},{"var":"z"},{"var":"C_mid"}]}}}],"premises":[{"id":"MAP-P056-P005","producer":"A-S7-P005-EXISTS","closure_role":"REQUIRED","binder_map":{"lambda_seq":{"def":{"id":"D-S811-LAMBDA-SEQ","args":[]}},"lambda":{"lit":{"type":"Real","value":"1"}},"u":{"proj":{"value":{"def":{"id":"D-015","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"}]}},"index":2}},"v":{"proj":{"value":{"def":{"id":"D-015","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"}]}},"index":1}},"K_sh":{"var":"K_sh"},"X":{"var":"z"}},"hypothesis_map":{"domain":{"guard":"MAP-P056-P005_domain"}},"witness_map":{},"consume":["shifted_mean_exists"],"guards":[{"key":"MAP-P056-P005_domain","proposition":{"def":{"id":"D-S45-SHIFT-FAMILY-DOMAIN","args":[{"def":{"id":"D-S811-LAMBDA-SEQ","args":[]}},{"lit":{"type":"Real","value":"1"}},{"proj":{"value":{"def":{"id":"D-015","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"}]}},"index":2}},{"proj":{"value":{"def":{"id":"D-015","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"}]}},"index":1}},{"var":"K_sh"},{"var":"z"}]}}}]},{"id":"MAP-P056-F1","producer":"P-051F1","closure_role":"REQUIRED","binder_map":{},"hypothesis_map":{},"witness_map":{"c_1":"MAP-P056_c1","C_1":"MAP-P056_C1","Lambda_1":"MAP-P056_L1"},"consume":["weight_type","dominates_base","dominates_shift"]},{"id":"MAP-P056-F2","producer":"A-LATE-P051F2-EXISTS","closure_role":"REQUIRED","binder_map":{"theta":{"var":"theta"},"y":{"var":"y"},"k":{"var":"k"},"sigma":{"var":"sigma"}},"hypothesis_map":{"theta_ge_2":{"guard":"MAP-P056-F2_theta_ge_2"},"y_pos":{"guard":"MAP-P056-F2_y_pos"},"y_lt_1":{"guard":"MAP-P056-F2_y_lt_1"},"k_ge_1":{"guard":"MAP-P056-F2_k_ge_1"},"sigma_ge_theta":{"guard":"MAP-P056-F2_sigma_ge_theta"}},"witness_map":{},"consume":["existentialized"],"guards":[{"key":"MAP-P056-F2_theta_ge_2","proposition":{"op":{"name":"ge","args":[{"var":"theta"},{"lit":{"type":"Real","value":"2"}}]}}},{"key":"MAP-P056-F2_y_pos","proposition":{"op":{"name":"gt","args":[{"var":"y"},{"lit":{"type":"Real","value":"0"}}]}}},{"key":"MAP-P056-F2_y_lt_1","proposition":{"op":{"name":"lt","args":[{"var":"y"},{"lit":{"type":"Real","value":"1"}}]}}},{"key":"MAP-P056-F2_k_ge_1","proposition":{"op":{"name":"ge","args":[{"var":"k"},{"lit":{"type":"Nat","value":"1"}}]}}},{"key":"MAP-P056-F2_sigma_ge_theta","proposition":{"op":{"name":"ge","args":[{"var":"sigma"},{"var":"theta"}]}}}]},{"id":"MAP-P056-V","producer":"P-051V","closure_role":"REQUIRED","binder_map":{"theta":{"var":"theta"},"y":{"var":"y"},"k":{"var":"k"},"sigma":{"var":"sigma"}},"hypothesis_map":{"theta_ge_2":{"guard":"MAP-P056-V_theta_ge_2"},"y_pos":{"guard":"MAP-P056-V_y_pos"},"y_lt_1":{"guard":"MAP-P056-V_y_lt_1"},"k_ge_1":{"guard":"MAP-P056-V_k_ge_1"},"sigma_ge_theta":{"guard":"MAP-P056-V_sigma_ge_theta"}},"witness_map":{},"consume":["modifier_normalization"],"guards":[{"key":"MAP-P056-V_theta_ge_2","proposition":{"op":{"name":"ge","args":[{"var":"theta"},{"lit":{"type":"Real","value":"2"}}]}}},{"key":"MAP-P056-V_y_pos","proposition":{"op":{"name":"gt","args":[{"var":"y"},{"lit":{"type":"Real","value":"0"}}]}}},{"key":"MAP-P056-V_y_lt_1","proposition":{"op":{"name":"lt","args":[{"var":"y"},{"lit":{"type":"Real","value":"1"}}]}}},{"key":"MAP-P056-V_k_ge_1","proposition":{"op":{"name":"ge","args":[{"var":"k"},{"lit":{"type":"Nat","value":"1"}}]}}},{"key":"MAP-P056-V_sigma_ge_theta","proposition":{"op":{"name":"ge","args":[{"var":"sigma"},{"var":"theta"}]}}}]},{"id":"MAP-P056-G","producer":"A-LATE-P051G-EXISTS","closure_role":"REQUIRED","binder_map":{"theta":{"var":"theta"},"y":{"var":"y"},"k":{"var":"k"},"sigma":{"var":"sigma"}},"hypothesis_map":{"theta_ge_2":{"guard":"MAP-P056-G_theta_ge_2"},"y_pos":{"guard":"MAP-P056-G_y_pos"},"y_lt_1":{"guard":"MAP-P056-G_y_lt_1"},"k_ge_1":{"guard":"MAP-P056-G_k_ge_1"},"sigma_ge_theta":{"guard":"MAP-P056-G_sigma_ge_theta"}},"witness_map":{},"consume":["existentialized"],"guards":[{"key":"MAP-P056-G_theta_ge_2","proposition":{"op":{"name":"ge","args":[{"var":"theta"},{"lit":{"type":"Real","value":"2"}}]}}},{"key":"MAP-P056-G_y_pos","proposition":{"op":{"name":"gt","args":[{"var":"y"},{"lit":{"type":"Real","value":"0"}}]}}},{"key":"MAP-P056-G_y_lt_1","proposition":{"op":{"name":"lt","args":[{"var":"y"},{"lit":{"type":"Real","value":"1"}}]}}},{"key":"MAP-P056-G_k_ge_1","proposition":{"op":{"name":"ge","args":[{"var":"k"},{"lit":{"type":"Nat","value":"1"}}]}}},{"key":"MAP-P056-G_sigma_ge_theta","proposition":{"op":{"name":"ge","args":[{"var":"sigma"},{"var":"theta"}]}}}]},{"id":"MAP-P056-H","producer":"A-LATE-P051H-EXISTS","closure_role":"REQUIRED","scope_binders":[{"key":"p","type":"Nat"}],"binder_map":{"theta":{"var":"theta"},"y":{"var":"y"},"k":{"var":"k"},"sigma":{"var":"sigma"},"w":{"proj":{"value":{"def":{"id":"D-015","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"}]}},"index":2}},"b":{"proj":{"value":{"def":{"id":"D-015","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"}]}},"index":1}},"p":{"var":"p"}},"hypothesis_map":{"theta_ge_2":{"guard":"MAP-P056-H_theta_ge_2"},"y_pos":{"guard":"MAP-P056-H_y_pos"},"y_lt_1":{"guard":"MAP-P056-H_y_lt_1"},"k_ge_1":{"guard":"MAP-P056-H_k_ge_1"},"sigma_ge_theta":{"guard":"MAP-P056-H_sigma_ge_theta"},"selected_weight":{"guard":"MAP-P056-H_selected_weight"},"modifier_b":{"guard":"MAP-P056-H_modifier_b"},"prime_p":{"guard":"MAP-P056-H_prime_p"}},"witness_map":{},"consume":["existentialized"],"guards":[{"key":"MAP-P056-H_theta_ge_2","proposition":{"op":{"name":"ge","args":[{"var":"theta"},{"lit":{"type":"Real","value":"2"}}]}}},{"key":"MAP-P056-H_y_pos","proposition":{"op":{"name":"gt","args":[{"var":"y"},{"lit":{"type":"Real","value":"0"}}]}}},{"key":"MAP-P056-H_y_lt_1","proposition":{"op":{"name":"lt","args":[{"var":"y"},{"lit":{"type":"Real","value":"1"}}]}}},{"key":"MAP-P056-H_k_ge_1","proposition":{"op":{"name":"ge","args":[{"var":"k"},{"lit":{"type":"Nat","value":"1"}}]}}},{"key":"MAP-P056-H_sigma_ge_theta","proposition":{"op":{"name":"ge","args":[{"var":"sigma"},{"var":"theta"}]}}},{"key":"MAP-P056-H_selected_weight","proposition":{"def":{"id":"D-S7A-SELECTED-WEIGHT","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"},{"proj":{"value":{"def":{"id":"D-015","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"}]}},"index":2}}]}}},{"key":"MAP-P056-H_modifier_b","proposition":{"def":{"id":"D-S7A-MODIFIER","args":[{"proj":{"value":{"def":{"id":"D-015","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"}]}},"index":1}}]}}},{"key":"MAP-P056-H_prime_p","proposition":{"def":{"id":"D-S7A-PRIME","args":[{"var":"p"}]}}}]},{"id":"MAP-P056-P007-0","producer":"A-S45-P007-EXISTS","closure_role":"REQUIRED","binder_map":{"c":{"lit":{"type":"Real","value":"0"}},"eta":{"def":{"id":"D-S811-ETA","args":[]}},"C_err":{"def":{"id":"D-S811-CERR","args":[]}},"L":{"def":{"id":"D-S811-P056-POINT-0","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"},{"var":"z"}]}}},"hypothesis_map":{"domain":{"guard":"MAP-P056-P007-0_domain"}},"witness_map":{},"consume":["existentialized"],"guards":[{"key":"MAP-P056-P007-0_domain","proposition":{"def":{"id":"D-S45-P007-DOMAIN","args":[{"lit":{"type":"Real","value":"0"}},{"def":{"id":"D-S811-ETA","args":[]}},{"def":{"id":"D-S811-CERR","args":[]}},{"def":{"id":"D-S811-P056-POINT-0","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"},{"var":"z"}]}}]}}}]},{"id":"MAP-P056-P008-0","producer":"A-S45-P008-EXISTS","closure_role":"REQUIRED","binder_map":{"Q":{"type":{"named":{"id":"D-S811-P056-Q","args":[{"var":"theta"}]}}},"c_minus":{"lit":{"type":"Real","value":"0"}},"c_plus":{"lit":{"type":"Real","value":"1/2"}},"eta_star":{"def":{"id":"D-S811-ETA","args":[]}},"C_err_star":{"def":{"id":"D-S811-CERR","args":[]}},"P_0":{"lit":{"type":"Real","value":"2"}},"m_fin":{"lit":{"type":"Real","value":"1"}},"M_fin":{"lit":{"type":"Real","value":"1"}},"coeff":{"def":{"id":"D-S811-P056-C-0","args":[{"var":"theta"}]}},"local_factor":{"def":{"id":"D-S811-P056-L-0","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"}]}}},"hypothesis_map":{"domain":{"guard":"MAP-P056-P008-0_domain"}},"witness_map":{},"consume":["existentialized"],"guards":[{"key":"MAP-P056-P008-0_domain","proposition":{"def":{"id":"D-S45-P008-DOMAIN","args":[{"type":{"named":{"id":"D-S811-P056-Q","args":[{"var":"theta"}]}}},{"lit":{"type":"Real","value":"0"}},{"lit":{"type":"Real","value":"1/2"}},{"def":{"id":"D-S811-ETA","args":[]}},{"def":{"id":"D-S811-CERR","args":[]}},{"lit":{"type":"Real","value":"2"}},{"lit":{"type":"Real","value":"1"}},{"lit":{"type":"Real","value":"1"}},{"def":{"id":"D-S811-P056-C-0","args":[{"var":"theta"}]}},{"def":{"id":"D-S811-P056-L-0","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"}]}}]}}}]},{"id":"MAP-P056-P007-ACT","producer":"A-S45-P007-EXISTS","closure_role":"REQUIRED","binder_map":{"c":{"op":{"name":"div","args":[{"var":"y"},{"lit":{"type":"Real","value":"2"}}]}},"eta":{"def":{"id":"D-S811-ETA","args":[]}},"C_err":{"def":{"id":"D-S811-CERR","args":[]}},"L":{"def":{"id":"D-S811-P056-POINT-ACT","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"},{"var":"z"}]}}},"hypothesis_map":{"domain":{"guard":"MAP-P056-P007-ACT_domain"}},"witness_map":{},"consume":["existentialized"],"guards":[{"key":"MAP-P056-P007-ACT_domain","proposition":{"def":{"id":"D-S45-P007-DOMAIN","args":[{"op":{"name":"div","args":[{"var":"y"},{"lit":{"type":"Real","value":"2"}}]}},{"def":{"id":"D-S811-ETA","args":[]}},{"def":{"id":"D-S811-CERR","args":[]}},{"def":{"id":"D-S811-P056-POINT-ACT","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"},{"var":"z"}]}}]}}}]},{"id":"MAP-P056-P008-ACT","producer":"A-S45-P008-EXISTS","closure_role":"REQUIRED","binder_map":{"Q":{"type":{"named":{"id":"D-S811-P056-Q","args":[{"var":"theta"}]}}},"c_minus":{"lit":{"type":"Real","value":"0"}},"c_plus":{"lit":{"type":"Real","value":"1/2"}},"eta_star":{"def":{"id":"D-S811-ETA","args":[]}},"C_err_star":{"def":{"id":"D-S811-CERR","args":[]}},"P_0":{"lit":{"type":"Real","value":"2"}},"m_fin":{"lit":{"type":"Real","value":"1"}},"M_fin":{"lit":{"type":"Real","value":"1"}},"coeff":{"def":{"id":"D-S811-P056-C-ACT","args":[{"var":"theta"},{"var":"y"}]}},"local_factor":{"def":{"id":"D-S811-P056-L-ACT","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"},{"var":"z"}]}}},"hypothesis_map":{"domain":{"guard":"MAP-P056-P008-ACT_domain"}},"witness_map":{},"consume":["existentialized"],"guards":[{"key":"MAP-P056-P008-ACT_domain","proposition":{"def":{"id":"D-S45-P008-DOMAIN","args":[{"type":{"named":{"id":"D-S811-P056-Q","args":[{"var":"theta"}]}}},{"lit":{"type":"Real","value":"0"}},{"lit":{"type":"Real","value":"1/2"}},{"def":{"id":"D-S811-ETA","args":[]}},{"def":{"id":"D-S811-CERR","args":[]}},{"lit":{"type":"Real","value":"2"}},{"lit":{"type":"Real","value":"1"}},{"lit":{"type":"Real","value":"1"}},{"def":{"id":"D-S811-P056-C-ACT","args":[{"var":"theta"},{"var":"y"}]}},{"def":{"id":"D-S811-P056-L-ACT","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"},{"var":"z"}]}}]}}}]}],"witness_realizations":{"C_mid":{"def":{"id":"D-S7B-P056-W","args":[{"var":"theta"}]}}},"proof_ref":"### P-056 — regular middle shifted \\(t\\)-mean"}
```

- Prenex statement:
  \[
  \forall\theta\ge2\;\exists C_{\rm mid}(\theta)>0\;
  \forall y\in(0,1)\;\forall k\ge1\;\forall\sigma\ge\theta\;
  \forall K_{\rm sh}\ge1\;\forall z>0,
  \]
  if \(\sigma\le z<\theta^k\), then
  \[
  T_k(z,K_{\rm sh})\le C_{\rm mid}(\theta)
  zw_{2,k}(K_{\rm sh})(\log\sigma)^{-y/2}\ell(z)^{y/2-1}.
  \]
- Local equalities: D-015/D-016.
- Domain/range: constant uniform in all post-constant variables.
- Input subject: exact T-sum. Output: exact middle factor.
- Premise maps:
  - `MAP-P056-P005`:

    | producer | slot | domain | consumer term | evidence |
    |---|---|---|---|---|
    | P-005 | `u` | nonnegative multiplicative | \(w_1\) | P-051F1 |
    | P-005 | `v` | nonnegative multiplicative, normalized by `v(1)=1` | \(v_k\) | P-051V full-domain multiplicativity and normalization |
    | P-005 | `K_sh` | \(\mathbb N_{>0}\) | \(K_{\rm sh}\) | binder |
    | P-005 | `X` | \(\mathbb R_{\ge2}\) | \(z\) | \(z\ge\sigma\ge2\) |
    | P-005 | `(lambda_i)` | nonnegative sequence | \(\lambda_i:=\Lambda_*\) for all \(i\) | P-051G |
    | P-005 | `lambda` | \([0,2)\) | \(1\) | P-051V full prime-power bound |

    Producer hypothesis is P-051G's common local bound. Consumed conclusion is
    P-005's exact shifted-mean estimate; subject is literally
    `SUB-T`. Its constant uses \((\Lambda_*,1)\) and precedes all
    displayed family variables.
  - `MAP-P056-P007` (two applications):

    | producer | slot | domain | consumer term tuple | evidence |
    |---|---|---|---|---|
    | P-007 | `c` | \(\mathbb R\) | \((0,y/2)\) | exact first coefficients |
    | P-007 | `eta` | \(>0\) | \((\eta_*,\eta_*)\), \(\eta_*:=\min(c_*,1)\) | P-051H |
    | P-007 | `C_err` | \(>0\) | \((C_E,C_E)\), \(C_E:=C_{E,*}=C_*+2\Lambda_*\) | common error |
    | P-007 | `(L_p)` | positive prime family | \(L_p:=\sum_{j\ge0}w_1(p^j)v_k(p^j)p^{-j}\) in each range | constant term 1 |
    | P-007 | `A` | \(\ge2\) | \((2,\sigma)\) | \(2\le\sigma\le z\) |
    | P-007 | `B` | \(\ge2\) | \((\sigma,z)\) | same chain |

    For each tuple application extend the displayed Euler factor by the exact
    model \(1+c/p\) outside its consumed interval. This gives a global
    P-007 error hypothesis without changing either consumed product. The
    coefficient-zero factor is exactly \(1\); the second expansion uses
    \(v_k(p)=y\). `AD-P056-EULER-SPLIT` is literal range partition.
  - `MAP-P056-P008`: define
    \[
    Q_{\rm mid}:=\{q=(\theta,y,k,\sigma,z):\theta\ge2,\ 0<y<1,
    k\ge1,\ \theta\le\sigma\le z<\theta^k\}.
    \]
    For \(q=(\theta,y,k,\sigma,z)\in Q_{\rm mid}\), let
    \(E_{q,p}:=\sum_{j\ge0}w_1(p^j)v_k(p^j)p^{-j}\), with the D-015 data
    determined by \((\theta,y,k,\sigma)\), and define the two global positive
    families
    \[
    L^{\rm mid,0}_{q,p}:=
    \begin{cases}E_{q,p},&2\le p<\sigma,\\1,&\text{otherwise},\end{cases}
    \quad
    L^{\rm mid,act}_{q,p}:=
    \begin{cases}E_{q,p},&\sigma\le p<z,\\1+y/(2p),&\text{otherwise}.
    \end{cases}
    \tag{L056-family}
    \]
    Apply P-008 to these literal \((q,p)\)-families with coefficient maps
    \(q\mapsto0,q\mapsto y/2\) and the common data
    \(c_-:=0,c_+:=1/2,\eta_*:=\min(c_*,1),
    C_{\rm err,*}:=C_{E,*},P_0:=2,m_{\rm fin}:=M_{\rm fin}:=1\).
    The endpoint \(z\) is therefore fixed as part of \(q\) before the P-008
    comparison constants are chosen. P051H-main supplies both active-interval
    error bounds, the exact-model branches have zero error, and the prefix is
    vacuous; all these data are uniform in \(z\). The two consumed conclusions
    assemble by `AD-P056-EULER-SPLIT`. Constants and uniform variables map as
    common family data -> \(C_{\rm mid}(\theta)\) ->
    \((y,k,\sigma,K_{\rm sh},z)\).

    | producer | slot | domain | consumer term tuple | evidence |
    |---|---|---|---|---|
    | P-008 | `Q` | nonempty index set | \(Q_{\rm mid}\) | e.g. \((2,1/2,2,2,3)\) |
    | P-008 | `c_-` | \(\mathbb R\) | \(0\) | common lower endpoint |
    | P-008 | `c_+` | \(\mathbb R\), \(c_-\le c_+\), \(1+c_-/2>0\) | \(1/2\) | admissible compact interval |
    | P-008 | `eta_*` | \(\mathbb R_{>0}\) | \(\min(c_*,1)\) | P-051H |
    | P-008 | `C_err,*` | \(\mathbb R_{>0}\) | \(C_{E,*}\) | P051H-main |
    | P-008 | `P_0` | \(\mathbb R_{\ge2}\) | \(2\) | literal |
    | P-008 | `m_fin` | \(\mathbb R_{>0}\) | \(1\) | empty prefix |
    | P-008 | `M_fin` | \(\mathbb R_{\ge m_{\rm fin}}\) | \(1\) | empty prefix |
    | P-008 | `c` | maps into \([0,1/2]\) | \((q\mapsto0,q\mapsto y/2)\) | \(0<y<1\) from \(q\in Q_{\rm mid}\) |
    | P-008 | `L` | positive factor families | \((L^{\rm mid,0}_{q,p},L^{\rm mid,act}_{q,p})\) from (L056-family) | literal functions of \((q,p)\); P051H-main |
    | P-008 | `q` | \(Q_{\rm mid}\) | \((\theta,y,k,\sigma,z)\) | complete middle-domain tuple, including the active endpoint |
    | P-008 | `A` | \(\mathbb R_{\ge2}\) | \((2,\sigma)\) | endpoint chain |
    | P-008 | `B` | \(\mathbb R_{\ge2}\) | \((\sigma,z)\) | P-056 branch |
  - `MAP-P056-P051F2`: consume the exact D-015 construction of \(w_{2,k}\)
    and its domination of the shift factor, with identical family binders.
  - `MAP-P056-P051F1`: consume only the exact nonnegative multiplicative
    identity of \(w_1\) used as P-005's first weight.
  - `MAP-P056-P051V`: bind \((\theta,y,k,\sigma)\) identically and consume
    exactly nonnegative multiplicativity of \(v_k\), \(v_k(1)=1\), and the
    full prime-power bound, discharging every P-005 modifier slot.
  - `MAP-P056-P051G`: consume only the common local bounds for \(w_1\).
  - `MAP-P056-P051H`: consume only (P051H-main) for the two exact local Euler
    families above, with \(b:=v_k\); P-051V supplies the literal modifier
    hypotheses for that specialization.
- Derivation certificate: evaluate only the two active coefficient ranges.
- Source/S2 anchor: ET p. 30; S2 R2.14 middle line.
- Definitions used: D-006, D-015, D-016.

### P-057 — regular terminal shifted \(t\)-mean

```mathminer-s3
{"schema":"mathminer.s3/1","id":"P-057","kind":"PROPOSITION","binders":[{"key":"theta","type":"Real"},{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"},{"key":"K_sh","type":"Nat"},{"key":"z","type":"Real"}],"uses_definitions":["D-015","D-016","D-S7-P051V-DOMAIN","D-S7B-P057-DOMAIN","D-S7B-P057-RESULT"],"source_anchors":[],"hypotheses":[{"key":"domain","proposition":{"def":{"id":"D-S7B-P057-DOMAIN","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"},{"var":"K_sh"},{"var":"z"}]}}},{"key":"family_domain","proposition":{"def":{"id":"D-S7-P051V-DOMAIN","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"}]}}}],"witnesses":[],"conclusions":[{"key":"terminal_bound","proposition":{"def":{"id":"D-S7B-P057-RESULT","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"},{"var":"K_sh"},{"var":"z"}]}}}],"premises":[{"id":"MAP-P057-P051F1","producer":"P-051F1","closure_role":"REQUIRED","binder_map":{},"hypothesis_map":{},"witness_map":{"c_1":"p057_c1","C_1":"p057_C1","Lambda_1":"p057_L1"},"consume":["weight_type","dominates_base","dominates_shift"]},{"id":"MAP-P057-P051V","producer":"P-051V","closure_role":"REQUIRED","binder_map":{"theta":{"var":"theta"},"y":{"var":"y"},"k":{"var":"k"},"sigma":{"var":"sigma"}},"hypothesis_map":{"theta_ge_2":{"guard":"MAP-P057-P051V_theta_ge_2"},"y_pos":{"guard":"MAP-P057-P051V_y_pos"},"y_lt_1":{"guard":"MAP-P057-P051V_y_lt_1"},"k_ge_1":{"guard":"MAP-P057-P051V_k_ge_1"},"sigma_ge_theta":{"guard":"MAP-P057-P051V_sigma_ge_theta"}},"witness_map":{},"consume":["modifier_normalization"],"guards":[{"key":"MAP-P057-P051V_theta_ge_2","proposition":{"op":{"name":"ge","args":[{"var":"theta"},{"lit":{"type":"Real","value":"2"}}]}}},{"key":"MAP-P057-P051V_y_pos","proposition":{"op":{"name":"gt","args":[{"var":"y"},{"lit":{"type":"Real","value":"0"}}]}}},{"key":"MAP-P057-P051V_y_lt_1","proposition":{"op":{"name":"lt","args":[{"var":"y"},{"lit":{"type":"Real","value":"1"}}]}}},{"key":"MAP-P057-P051V_k_ge_1","proposition":{"op":{"name":"ge","args":[{"var":"k"},{"lit":{"type":"Nat","value":"1"}}]}}},{"key":"MAP-P057-P051V_sigma_ge_theta","proposition":{"op":{"name":"ge","args":[{"var":"sigma"},{"var":"theta"}]}}}]}],"witness_realizations":{},"proof_ref":"### P-057 — regular terminal shifted \\(t\\)-mean"}
```

- Prenex statement: for every \(y\in(0,1),k\ge1,\sigma\ge\theta\ge2\),
  \(K_{\rm sh}\ge1,z>0\), if \(z<\sigma\), then
  \[
  T_k(z,K_{\rm sh})\le w_1(K_{\rm sh}).
  \]
- Local equalities: when \(z>1\) the sole possible contributing \(t\) is
  \(1\), with \(v_k(1)=1\); when \(z\le1\) the sum is empty.
- Domain/range: exact endpoint-safe upper bound.
- Input subject: exact T-sum. Output: terminal weight.
- Premise maps:
  - `MAP-P057-P051F1`: consume only the exact identity and nonnegativity of
    D-015's \(w_1\).
  - `MAP-P057-P051V`: bind \((\theta,y,k,\sigma)\) identically and consume
    exactly \(v_k(1)=1\) and nonnegativity; no type, domination,
    consolidation, or Euler-tail conclusion is used.
- Derivation certificate: the only positive \(\sigma\)-rough integer below
  \(\sigma\) is \(t=1\), and it occurs only when \(z>1\).
- Source/S2 anchor: ET p. 30; S2 R2.14 terminal line.
- Definitions used: D-002, D-015, D-016.

### P-058 — regular outer shifted mean

Current construction binding: the exact `P058Statement` in the GroupA--GroupD source contracts, W0--W8, and the retained S7 provider. Any `mathminer-s3-legacy` block here is historical, not a proof.

```mathminer-s3-legacy
{"schema":"mathminer.s3/1","id":"P-058","kind":"PROPOSITION","binders":[{"key":"theta","type":"Real"},{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"},{"key":"x","type":"Real"}],"uses_definitions":["D-005","D-015","D-018","D-S45-P007-DOMAIN","D-S45-P008-DOMAIN","D-S45-SHIFT-FAMILY-DOMAIN","D-S7-P051V-DOMAIN","D-S7A-MODIFIER","D-S7A-PRIME","D-S7A-SELECTED-WEIGHT","D-S7B-P054-DOMAIN","D-S7B-P054A-DOMAIN","D-S7B-P058-DOMAIN","D-S7B-P058-RESULT","D-S7B-P058-W","D-S811-CERR","D-S811-ETA","D-S811-LAMBDA-SEQ","D-S811-P058-C-0","D-S811-P058-C-HI","D-S811-P058-C-MID","D-S811-P058-G","D-S811-P058-L-0","D-S811-P058-L-HI","D-S811-P058-L-MID","D-S811-P058-POINT-0","D-S811-P058-POINT-HI","D-S811-P058-POINT-MID","D-S811-P058-Q","D-S811-THETA-SUCC"],"source_anchors":[],"hypotheses":[{"key":"domain","proposition":{"def":{"id":"D-S7B-P058-DOMAIN","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"},{"var":"x"}]}}},{"key":"family_domain","proposition":{"def":{"id":"D-S7-P051V-DOMAIN","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"}]}}}],"witnesses":[{"key":"C_out","type":"Real","depends_on":["theta"]}],"conclusions":[{"key":"outer_bound","proposition":{"def":{"id":"D-S7B-P058-RESULT","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"},{"var":"x"},{"var":"C_out"}]}}}],"premises":[{"id":"MAP-P058-P054A","producer":"P-054A","closure_role":"REQUIRED","scope_binders":[{"key":"d_prime","type":"Nat"}],"binder_map":{"k":{"var":"k"},"theta":{"var":"theta"},"sigma":{"var":"sigma"},"g":{"def":{"id":"D-S811-P058-G","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"},{"var":"d_prime"}]}}},"hypothesis_map":{"domain":{"guard":"MAP-P058-P054A_domain"}},"witness_map":{},"consume":["initial_enlargements"],"guards":[{"key":"MAP-P058-P054A_domain","proposition":{"def":{"id":"D-S7B-P054A-DOMAIN","args":[{"var":"k"},{"var":"theta"},{"var":"sigma"},{"def":{"id":"D-S811-P058-G","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"},{"var":"d_prime"}]}}]}}}]},{"id":"MAP-P058-P005","producer":"A-S7-P005-EXISTS","closure_role":"REQUIRED","scope_binders":[{"key":"d_prime","type":"Nat"}],"binder_map":{"lambda_seq":{"def":{"id":"D-S811-LAMBDA-SEQ","args":[]}},"lambda":{"lit":{"type":"Real","value":"1"}},"u":{"proj":{"value":{"def":{"id":"D-015","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"}]}},"index":4}},"v":{"proj":{"value":{"def":{"id":"D-015","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"}]}},"index":1}},"K_sh":{"var":"d_prime"},"X":{"def":{"id":"D-S811-THETA-SUCC","args":[{"var":"theta"},{"var":"k"}]}}},"hypothesis_map":{"domain":{"guard":"MAP-P058-P005_domain"}},"witness_map":{},"consume":["shifted_mean_exists"],"guards":[{"key":"MAP-P058-P005_domain","proposition":{"def":{"id":"D-S45-SHIFT-FAMILY-DOMAIN","args":[{"def":{"id":"D-S811-LAMBDA-SEQ","args":[]}},{"lit":{"type":"Real","value":"1"}},{"proj":{"value":{"def":{"id":"D-015","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"}]}},"index":4}},{"proj":{"value":{"def":{"id":"D-015","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"}]}},"index":1}},{"var":"d_prime"},{"def":{"id":"D-S811-THETA-SUCC","args":[{"var":"theta"},{"var":"k"}]}}]}}}]},{"id":"MAP-P058-F1","producer":"P-051F1","closure_role":"REQUIRED","binder_map":{},"hypothesis_map":{},"witness_map":{"c_1":"MAP-P058_c1","C_1":"MAP-P058_C1","Lambda_1":"MAP-P058_L1"},"consume":["weight_type","dominates_base","dominates_shift"]},{"id":"MAP-P058-F3","producer":"A-LATE-P051F3-EXISTS","closure_role":"REQUIRED","binder_map":{"theta":{"var":"theta"},"y":{"var":"y"},"k":{"var":"k"},"sigma":{"var":"sigma"}},"hypothesis_map":{"theta_ge_2":{"guard":"MAP-P058-F3_theta_ge_2"},"y_pos":{"guard":"MAP-P058-F3_y_pos"},"y_lt_1":{"guard":"MAP-P058-F3_y_lt_1"},"k_ge_1":{"guard":"MAP-P058-F3_k_ge_1"},"sigma_ge_theta":{"guard":"MAP-P058-F3_sigma_ge_theta"}},"witness_map":{},"consume":["existentialized"],"guards":[{"key":"MAP-P058-F3_theta_ge_2","proposition":{"op":{"name":"ge","args":[{"var":"theta"},{"lit":{"type":"Real","value":"2"}}]}}},{"key":"MAP-P058-F3_y_pos","proposition":{"op":{"name":"gt","args":[{"var":"y"},{"lit":{"type":"Real","value":"0"}}]}}},{"key":"MAP-P058-F3_y_lt_1","proposition":{"op":{"name":"lt","args":[{"var":"y"},{"lit":{"type":"Real","value":"1"}}]}}},{"key":"MAP-P058-F3_k_ge_1","proposition":{"op":{"name":"ge","args":[{"var":"k"},{"lit":{"type":"Nat","value":"1"}}]}}},{"key":"MAP-P058-F3_sigma_ge_theta","proposition":{"op":{"name":"ge","args":[{"var":"sigma"},{"var":"theta"}]}}}]},{"id":"MAP-P058-F4","producer":"A-LATE-P051F4-EXISTS","closure_role":"REQUIRED","binder_map":{"theta":{"var":"theta"},"y":{"var":"y"},"k":{"var":"k"},"sigma":{"var":"sigma"}},"hypothesis_map":{"theta_ge_2":{"guard":"MAP-P058-F4_theta_ge_2"},"y_pos":{"guard":"MAP-P058-F4_y_pos"},"y_lt_1":{"guard":"MAP-P058-F4_y_lt_1"},"k_ge_1":{"guard":"MAP-P058-F4_k_ge_1"},"sigma_ge_theta":{"guard":"MAP-P058-F4_sigma_ge_theta"}},"witness_map":{},"consume":["existentialized"],"guards":[{"key":"MAP-P058-F4_theta_ge_2","proposition":{"op":{"name":"ge","args":[{"var":"theta"},{"lit":{"type":"Real","value":"2"}}]}}},{"key":"MAP-P058-F4_y_pos","proposition":{"op":{"name":"gt","args":[{"var":"y"},{"lit":{"type":"Real","value":"0"}}]}}},{"key":"MAP-P058-F4_y_lt_1","proposition":{"op":{"name":"lt","args":[{"var":"y"},{"lit":{"type":"Real","value":"1"}}]}}},{"key":"MAP-P058-F4_k_ge_1","proposition":{"op":{"name":"ge","args":[{"var":"k"},{"lit":{"type":"Nat","value":"1"}}]}}},{"key":"MAP-P058-F4_sigma_ge_theta","proposition":{"op":{"name":"ge","args":[{"var":"sigma"},{"var":"theta"}]}}}]},{"id":"MAP-P058-V","producer":"P-051V","closure_role":"REQUIRED","binder_map":{"theta":{"var":"theta"},"y":{"var":"y"},"k":{"var":"k"},"sigma":{"var":"sigma"}},"hypothesis_map":{"theta_ge_2":{"guard":"MAP-P058-V_theta_ge_2"},"y_pos":{"guard":"MAP-P058-V_y_pos"},"y_lt_1":{"guard":"MAP-P058-V_y_lt_1"},"k_ge_1":{"guard":"MAP-P058-V_k_ge_1"},"sigma_ge_theta":{"guard":"MAP-P058-V_sigma_ge_theta"}},"witness_map":{},"consume":["modifier_normalization"],"guards":[{"key":"MAP-P058-V_theta_ge_2","proposition":{"op":{"name":"ge","args":[{"var":"theta"},{"lit":{"type":"Real","value":"2"}}]}}},{"key":"MAP-P058-V_y_pos","proposition":{"op":{"name":"gt","args":[{"var":"y"},{"lit":{"type":"Real","value":"0"}}]}}},{"key":"MAP-P058-V_y_lt_1","proposition":{"op":{"name":"lt","args":[{"var":"y"},{"lit":{"type":"Real","value":"1"}}]}}},{"key":"MAP-P058-V_k_ge_1","proposition":{"op":{"name":"ge","args":[{"var":"k"},{"lit":{"type":"Nat","value":"1"}}]}}},{"key":"MAP-P058-V_sigma_ge_theta","proposition":{"op":{"name":"ge","args":[{"var":"sigma"},{"var":"theta"}]}}}]},{"id":"MAP-P058-G","producer":"A-LATE-P051G-EXISTS","closure_role":"REQUIRED","binder_map":{"theta":{"var":"theta"},"y":{"var":"y"},"k":{"var":"k"},"sigma":{"var":"sigma"}},"hypothesis_map":{"theta_ge_2":{"guard":"MAP-P058-G_theta_ge_2"},"y_pos":{"guard":"MAP-P058-G_y_pos"},"y_lt_1":{"guard":"MAP-P058-G_y_lt_1"},"k_ge_1":{"guard":"MAP-P058-G_k_ge_1"},"sigma_ge_theta":{"guard":"MAP-P058-G_sigma_ge_theta"}},"witness_map":{},"consume":["existentialized"],"guards":[{"key":"MAP-P058-G_theta_ge_2","proposition":{"op":{"name":"ge","args":[{"var":"theta"},{"lit":{"type":"Real","value":"2"}}]}}},{"key":"MAP-P058-G_y_pos","proposition":{"op":{"name":"gt","args":[{"var":"y"},{"lit":{"type":"Real","value":"0"}}]}}},{"key":"MAP-P058-G_y_lt_1","proposition":{"op":{"name":"lt","args":[{"var":"y"},{"lit":{"type":"Real","value":"1"}}]}}},{"key":"MAP-P058-G_k_ge_1","proposition":{"op":{"name":"ge","args":[{"var":"k"},{"lit":{"type":"Nat","value":"1"}}]}}},{"key":"MAP-P058-G_sigma_ge_theta","proposition":{"op":{"name":"ge","args":[{"var":"sigma"},{"var":"theta"}]}}}]},{"id":"MAP-P058-H","producer":"A-LATE-P051H-EXISTS","closure_role":"REQUIRED","scope_binders":[{"key":"p","type":"Nat"}],"binder_map":{"theta":{"var":"theta"},"y":{"var":"y"},"k":{"var":"k"},"sigma":{"var":"sigma"},"w":{"proj":{"value":{"def":{"id":"D-015","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"}]}},"index":4}},"b":{"proj":{"value":{"def":{"id":"D-015","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"}]}},"index":1}},"p":{"var":"p"}},"hypothesis_map":{"theta_ge_2":{"guard":"MAP-P058-H_theta_ge_2"},"y_pos":{"guard":"MAP-P058-H_y_pos"},"y_lt_1":{"guard":"MAP-P058-H_y_lt_1"},"k_ge_1":{"guard":"MAP-P058-H_k_ge_1"},"sigma_ge_theta":{"guard":"MAP-P058-H_sigma_ge_theta"},"selected_weight":{"guard":"MAP-P058-H_selected_weight"},"modifier_b":{"guard":"MAP-P058-H_modifier_b"},"prime_p":{"guard":"MAP-P058-H_prime_p"}},"witness_map":{},"consume":["existentialized"],"guards":[{"key":"MAP-P058-H_theta_ge_2","proposition":{"op":{"name":"ge","args":[{"var":"theta"},{"lit":{"type":"Real","value":"2"}}]}}},{"key":"MAP-P058-H_y_pos","proposition":{"op":{"name":"gt","args":[{"var":"y"},{"lit":{"type":"Real","value":"0"}}]}}},{"key":"MAP-P058-H_y_lt_1","proposition":{"op":{"name":"lt","args":[{"var":"y"},{"lit":{"type":"Real","value":"1"}}]}}},{"key":"MAP-P058-H_k_ge_1","proposition":{"op":{"name":"ge","args":[{"var":"k"},{"lit":{"type":"Nat","value":"1"}}]}}},{"key":"MAP-P058-H_sigma_ge_theta","proposition":{"op":{"name":"ge","args":[{"var":"sigma"},{"var":"theta"}]}}},{"key":"MAP-P058-H_selected_weight","proposition":{"def":{"id":"D-S7A-SELECTED-WEIGHT","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"},{"proj":{"value":{"def":{"id":"D-015","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"}]}},"index":4}}]}}},{"key":"MAP-P058-H_modifier_b","proposition":{"def":{"id":"D-S7A-MODIFIER","args":[{"proj":{"value":{"def":{"id":"D-015","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"}]}},"index":1}}]}}},{"key":"MAP-P058-H_prime_p","proposition":{"def":{"id":"D-S7A-PRIME","args":[{"var":"p"}]}}}]},{"id":"MAP-P058-P054","producer":"P-054","closure_role":"REQUIRED","scope_binders":[{"key":"d","type":"Nat"},{"key":"d_prime","type":"Nat"}],"binder_map":{"d":{"var":"d"},"d_prime":{"var":"d_prime"},"k":{"var":"k"},"theta":{"var":"theta"}},"hypothesis_map":{"domain":{"guard":"MAP-P058-P054_domain"}},"witness_map":{},"consume":["close_window"],"guards":[{"key":"MAP-P058-P054_domain","proposition":{"def":{"id":"D-S7B-P054-DOMAIN","args":[{"var":"d"},{"var":"d_prime"},{"var":"k"},{"var":"theta"}]}}}]},{"id":"MAP-P058-P007-0","producer":"A-S45-P007-EXISTS","closure_role":"REQUIRED","binder_map":{"c":{"lit":{"type":"Real","value":"0"}},"eta":{"def":{"id":"D-S811-ETA","args":[]}},"C_err":{"def":{"id":"D-S811-CERR","args":[]}},"L":{"def":{"id":"D-S811-P058-POINT-0","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"}]}}},"hypothesis_map":{"domain":{"guard":"MAP-P058-P007-0_domain"}},"witness_map":{},"consume":["existentialized"],"guards":[{"key":"MAP-P058-P007-0_domain","proposition":{"def":{"id":"D-S45-P007-DOMAIN","args":[{"lit":{"type":"Real","value":"0"}},{"def":{"id":"D-S811-ETA","args":[]}},{"def":{"id":"D-S811-CERR","args":[]}},{"def":{"id":"D-S811-P058-POINT-0","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"}]}}]}}}]},{"id":"MAP-P058-P008-0","producer":"A-S45-P008-EXISTS","closure_role":"REQUIRED","binder_map":{"Q":{"type":{"named":{"id":"D-S811-P058-Q","args":[{"var":"theta"}]}}},"c_minus":{"lit":{"type":"Real","value":"0"}},"c_plus":{"lit":{"type":"Real","value":"1/2"}},"eta_star":{"def":{"id":"D-S811-ETA","args":[]}},"C_err_star":{"def":{"id":"D-S811-CERR","args":[]}},"P_0":{"lit":{"type":"Real","value":"2"}},"m_fin":{"lit":{"type":"Real","value":"1"}},"M_fin":{"lit":{"type":"Real","value":"1"}},"coeff":{"def":{"id":"D-S811-P058-C-0","args":[{"var":"theta"}]}},"local_factor":{"def":{"id":"D-S811-P058-L-0","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"}]}}},"hypothesis_map":{"domain":{"guard":"MAP-P058-P008-0_domain"}},"witness_map":{},"consume":["existentialized"],"guards":[{"key":"MAP-P058-P008-0_domain","proposition":{"def":{"id":"D-S45-P008-DOMAIN","args":[{"type":{"named":{"id":"D-S811-P058-Q","args":[{"var":"theta"}]}}},{"lit":{"type":"Real","value":"0"}},{"lit":{"type":"Real","value":"1/2"}},{"def":{"id":"D-S811-ETA","args":[]}},{"def":{"id":"D-S811-CERR","args":[]}},{"lit":{"type":"Real","value":"2"}},{"lit":{"type":"Real","value":"1"}},{"lit":{"type":"Real","value":"1"}},{"def":{"id":"D-S811-P058-C-0","args":[{"var":"theta"}]}},{"def":{"id":"D-S811-P058-L-0","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"}]}}]}}}]},{"id":"MAP-P058-P007-MID","producer":"A-S45-P007-EXISTS","closure_role":"REQUIRED","binder_map":{"c":{"op":{"name":"div","args":[{"var":"y"},{"lit":{"type":"Real","value":"2"}}]}},"eta":{"def":{"id":"D-S811-ETA","args":[]}},"C_err":{"def":{"id":"D-S811-CERR","args":[]}},"L":{"def":{"id":"D-S811-P058-POINT-MID","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"}]}}},"hypothesis_map":{"domain":{"guard":"MAP-P058-P007-MID_domain"}},"witness_map":{},"consume":["existentialized"],"guards":[{"key":"MAP-P058-P007-MID_domain","proposition":{"def":{"id":"D-S45-P007-DOMAIN","args":[{"op":{"name":"div","args":[{"var":"y"},{"lit":{"type":"Real","value":"2"}}]}},{"def":{"id":"D-S811-ETA","args":[]}},{"def":{"id":"D-S811-CERR","args":[]}},{"def":{"id":"D-S811-P058-POINT-MID","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"}]}}]}}}]},{"id":"MAP-P058-P008-MID","producer":"A-S45-P008-EXISTS","closure_role":"REQUIRED","binder_map":{"Q":{"type":{"named":{"id":"D-S811-P058-Q","args":[{"var":"theta"}]}}},"c_minus":{"lit":{"type":"Real","value":"0"}},"c_plus":{"lit":{"type":"Real","value":"1/2"}},"eta_star":{"def":{"id":"D-S811-ETA","args":[]}},"C_err_star":{"def":{"id":"D-S811-CERR","args":[]}},"P_0":{"lit":{"type":"Real","value":"2"}},"m_fin":{"lit":{"type":"Real","value":"1"}},"M_fin":{"lit":{"type":"Real","value":"1"}},"coeff":{"def":{"id":"D-S811-P058-C-MID","args":[{"var":"theta"},{"var":"y"}]}},"local_factor":{"def":{"id":"D-S811-P058-L-MID","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"}]}}},"hypothesis_map":{"domain":{"guard":"MAP-P058-P008-MID_domain"}},"witness_map":{},"consume":["existentialized"],"guards":[{"key":"MAP-P058-P008-MID_domain","proposition":{"def":{"id":"D-S45-P008-DOMAIN","args":[{"type":{"named":{"id":"D-S811-P058-Q","args":[{"var":"theta"}]}}},{"lit":{"type":"Real","value":"0"}},{"lit":{"type":"Real","value":"1/2"}},{"def":{"id":"D-S811-ETA","args":[]}},{"def":{"id":"D-S811-CERR","args":[]}},{"lit":{"type":"Real","value":"2"}},{"lit":{"type":"Real","value":"1"}},{"lit":{"type":"Real","value":"1"}},{"def":{"id":"D-S811-P058-C-MID","args":[{"var":"theta"},{"var":"y"}]}},{"def":{"id":"D-S811-P058-L-MID","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"}]}}]}}}]},{"id":"MAP-P058-P007-HI","producer":"A-S45-P007-EXISTS","closure_role":"REQUIRED","binder_map":{"c":{"lit":{"type":"Real","value":"1/2"}},"eta":{"def":{"id":"D-S811-ETA","args":[]}},"C_err":{"def":{"id":"D-S811-CERR","args":[]}},"L":{"def":{"id":"D-S811-P058-POINT-HI","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"}]}}},"hypothesis_map":{"domain":{"guard":"MAP-P058-P007-HI_domain"}},"witness_map":{},"consume":["existentialized"],"guards":[{"key":"MAP-P058-P007-HI_domain","proposition":{"def":{"id":"D-S45-P007-DOMAIN","args":[{"lit":{"type":"Real","value":"1/2"}},{"def":{"id":"D-S811-ETA","args":[]}},{"def":{"id":"D-S811-CERR","args":[]}},{"def":{"id":"D-S811-P058-POINT-HI","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"}]}}]}}}]},{"id":"MAP-P058-P008-HI","producer":"A-S45-P008-EXISTS","closure_role":"REQUIRED","binder_map":{"Q":{"type":{"named":{"id":"D-S811-P058-Q","args":[{"var":"theta"}]}}},"c_minus":{"lit":{"type":"Real","value":"0"}},"c_plus":{"lit":{"type":"Real","value":"1/2"}},"eta_star":{"def":{"id":"D-S811-ETA","args":[]}},"C_err_star":{"def":{"id":"D-S811-CERR","args":[]}},"P_0":{"lit":{"type":"Real","value":"2"}},"m_fin":{"lit":{"type":"Real","value":"1"}},"M_fin":{"lit":{"type":"Real","value":"1"}},"coeff":{"def":{"id":"D-S811-P058-C-HI","args":[{"var":"theta"}]}},"local_factor":{"def":{"id":"D-S811-P058-L-HI","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"}]}}},"hypothesis_map":{"domain":{"guard":"MAP-P058-P008-HI_domain"}},"witness_map":{},"consume":["existentialized"],"guards":[{"key":"MAP-P058-P008-HI_domain","proposition":{"def":{"id":"D-S45-P008-DOMAIN","args":[{"type":{"named":{"id":"D-S811-P058-Q","args":[{"var":"theta"}]}}},{"lit":{"type":"Real","value":"0"}},{"lit":{"type":"Real","value":"1/2"}},{"def":{"id":"D-S811-ETA","args":[]}},{"def":{"id":"D-S811-CERR","args":[]}},{"lit":{"type":"Real","value":"2"}},{"lit":{"type":"Real","value":"1"}},{"lit":{"type":"Real","value":"1"}},{"def":{"id":"D-S811-P058-C-HI","args":[{"var":"theta"}]}},{"def":{"id":"D-S811-P058-L-HI","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"}]}}]}}}]}],"witness_realizations":{"C_out":{"def":{"id":"D-S7B-P058-W","args":[{"var":"theta"}]}}},"proof_ref":"### P-058 — regular outer shifted mean"}
```

- Prenex statement:
  \[
  \forall\theta\ge2\;\exists C_{\rm out}(\theta)>0\;
  \forall y\in(0,1)\;\forall k\ge1\;\forall\sigma\ge\theta,
  \]
  if \(\sigma\le\theta^k\), then
  \[
  O_k\le C_{\rm out}(\theta)\theta^k(\log\sigma)^{-y/2}
  k^{y/2-1}
  \sum_{\theta^{k-1}<d'<\theta^{k+2}}w_{4,k}(d').
  \]
- Local equalities: \(O_k\) is exactly D-018.
- Domain/range: constant uniform in \(y,k,\sigma,d,d'\).
- Input subject: exact close-pair D-018 outer sum. Output: exact \(d'\)-sum.
- Premise maps:
  - `MAP-P058-P054A`: for each fixed \(d'\), set
    \(g(d):=w_{3,k}(dd')v_k(d)\), nonnegative by P-051F3 and the
    P-051V nonnegativity conclusion, and use
    `AD-REG-INIT` to pass from \(\theta^k\le d<\theta^{k+1}\) to
    \(d<\theta^{k+1}\).
  - `MAP-P058-P005`:

    | producer | slot | domain | consumer term | evidence |
    |---|---|---|---|---|
    | P-005 | `u` | nonnegative multiplicative | \(w_{3,k}\) | P-051F3 |
    | P-005 | `v` | nonnegative multiplicative, normalized by `v(1)=1` | \(v_k\) | P-051V full-domain multiplicativity and normalization |
    | P-005 | `K_sh` | \(\mathbb N_{>0}\) | \(d'\) | outer index |
    | P-005 | `X` | \(\mathbb R_{\ge2}\) | \(\theta^{k+1}\) | \(\theta\ge2,k\ge1\) |
    | P-005 | `(lambda_i)` | nonnegative sequence | \(\lambda_i:=\Lambda_*\) for every \(i\) | P-051G |
    | P-005 | `lambda` | \([0,2)\) | \(1\) | P-051V full prime-power bound |

    Producer hypothesis is P-051G's common local bound. Consumed conclusion is
    P-005's exact shifted estimate. Subject is `SUB-OUTER-INITIAL` after
    `AD-REG-INIT`; the shift factor is dominated by \(w_{4,k}(d')\).
    Its constant uses only \((\Lambda_*,1)\) and precedes all uniform family
    variables and \(d'\).
  - `MAP-P058-P007` (three applications):

    | producer | slot | domain | consumer term tuple | evidence |
    |---|---|---|---|---|
    | P-007 | `c` | \(\mathbb R\) | \((0,y/2,1/2)\) | exact first coefficients |
    | P-007 | `eta` | \(>0\) | \((\eta_*,\eta_*,\eta_*)\), \(\eta_*:=\min(c_*,1)\) | P-051H |
    | P-007 | `C_err` | \(>0\) | \((C_E,C_E,C_E)\), \(C_E:=C_{E,*}=C_*+2\Lambda_*\) | common error |
    | P-007 | `(L_p)` | positive prime family | \(L_p:=\sum_{j\ge0}w_{3,k}(p^j)v_k(p^j)p^{-j}\) in each range | constant term 1 |
    | P-007 | `A` | \(\ge2\) | \((2,\sigma,\theta^k)\) | \(2\le\sigma\le\theta^k\) |
    | P-007 | `B` | \(\ge2\) | \((\sigma,\theta^k,\theta^{k+1})\) | \(k\ge1,\theta\ge2\) |

    For each tuple application the global P-007 family equals the displayed
    Euler factor on its consumed interval and the exact model \(1+c/p\)
    outside. Hence P051H-main proves the global error hypothesis and leaves the
    consumed product literal. Empty endpoint ranges use P-007's empty
    branch. `AD-P058-EULER-SPLIT` identifies their product with the P-005
    Euler subject.
  - `MAP-P058-P008`: define the fixed-endpoint family
    \(Q_{\rm reg,out}:=\{(\theta,y,k,\sigma):\theta\ge2,0<y<1,
    k\ge1,\theta\le\sigma\le\theta^k\}\), and apply P-008 to the three
    coefficient maps \(0,y/2,1/2\) with
    \(c_-:=0,c_+:=1/2,\eta_*:=\min(c_*,1),
    C_{\rm err,*}:=C_{E,*},P_0:=2,m_{\rm fin}:=M_{\rm fin}:=1\).
    P051H-main supplies the common error and positivity. The three consumed
    product conclusions assemble by `AD-P058-EULER-SPLIT`; their constants
    precede \(y,k,\sigma,d'\), licensing the theta-only outer constant.
    P-007's hypotheses are P051H-main and the exact coefficient identities;
    its consumed conclusions and subject adapter are the displayed ones.

    | producer | slot | domain | consumer term tuple | evidence |
    |---|---|---|---|---|
    | P-008 | `Q` | nonempty index set | \(Q_{\rm reg,out}\) | e.g. \((2,1/2,1,2)\) |
    | P-008 | `c_-` | \(\mathbb R\) | \(0\) | common lower endpoint |
    | P-008 | `c_+` | \(\mathbb R\), \(c_-\le c_+\), \(1+c_-/2>0\) | \(1/2\) | admissible compact interval |
    | P-008 | `eta_*` | \(\mathbb R_{>0}\) | \(\min(c_*,1)\) | P-051H |
    | P-008 | `C_err,*` | \(\mathbb R_{>0}\) | \(C_{E,*}\) | P051H-main |
    | P-008 | `P_0` | \(\mathbb R_{\ge2}\) | \(2\) | literal |
    | P-008 | `m_fin` | \(\mathbb R_{>0}\) | \(1\) | empty prefix |
    | P-008 | `M_fin` | \(\mathbb R_{\ge m_{\rm fin}}\) | \(1\) | empty prefix |
    | P-008 | `c` | maps into \([0,1/2]\) | \((0,y/2,1/2)\) | \(0<y<1\) |
    | P-008 | `L` | positive factor families | three global exact-model extensions above | P051H-main |
    | P-008 | `q` | \(Q_{\rm reg,out}\) | \((\theta,y,k,\sigma)\) | complete fixed-endpoint regular tuple |
    | P-008 | `A` | \(\mathbb R_{\ge2}\) | \((2,\sigma,\theta^k)\) | endpoint chain |
    | P-008 | `B` | \(\mathbb R_{\ge2}\) | \((\sigma,\theta^k,\theta^{k+1})\) | P-058 endpoints |
  - `MAP-P058-P051F4`: consume the exact construction
    \(w_{4,k}=\widehat{\mathcal S}[w_{3,k},v_k]\) and its domination of the
    P-005 shift factor.
  - `MAP-P058-P051F3`: consume only the exact nonnegative multiplicative
    identity of \(w_{3,k}\) used as P-005's first weight.
  - `MAP-P058-P051V`: bind \((\theta,y,k,\sigma)\) identically and consume
    exactly nonnegative multiplicativity of \(v_k\), \(v_k(1)=1\), and the
    full prime-power bound, discharging every P-005 modifier slot and the
    nonnegativity used by `MAP-P058-P054A`.
  - `MAP-P058-P051G`: consume only the common local bounds for \(w_{3,k}\),
    with identical family binders.
  - `MAP-P058-P051H`: consume only (P051H-main) for the three exact local
    Euler factors above, with \((w,b):=(w_{3,k},v_k)\); P-051V supplies the
    literal modifier hypotheses for that specialization.
  - P-054 — Binders:
    \(d:=d,d':=d',k:=k,\theta:=\theta\) for each close pair.
    Hypotheses: D-018 index. Consumed: \(d'\)-window.
    Subject: exact enlargement to the displayed \(d'\)-sum.
    Constants: none.
- Derivation certificate: apply the shifted mean for each fixed \(d'\);
  use the exact close-pair window and sum.
- Source/S2 anchor: ET p. 31; S2 R1 (5.9), R2.4.
- Definitions used: D-002, D-003, D-005, D-015, D-018.

### P-059 — family-uniform mean with exposed common witnesses

Current construction binding: the exact `P059Statement` in the GroupA--GroupD source contracts, W0--W8, and the retained S7 provider. Any `mathminer-s3-legacy` block here is historical, not a proof.

```mathminer-s3-legacy
{"schema":"mathminer.s3/1","id":"P-059","kind":"PROPOSITION","binders":[{"key":"Q","type":"Type"},{"key":"w_family","type":{"fn":{"args":[{"var":"Q"}],"return":{"fn":{"args":["Nat"],"return":"Real"}}}}},{"key":"c_w","type":"Real"},{"key":"C_w_err","type":"Real"},{"key":"Lambda_w","type":"Real"},{"key":"q","type":{"var":"Q"}},{"key":"Z","type":"Real"}],"uses_definitions":["D-S45-P007-DOMAIN","D-S45-P008-DOMAIN","D-S7B-P059-CERR","D-S7B-P059-COEFF","D-S7B-P059-DOMAIN","D-S7B-P059-ETA","D-S7B-P059-L","D-S7B-P059-LAMBDA","D-S7B-P059-LOCAL","D-S7B-P059-RESULT","D-S7B-P059-W","DP-MEAN::DP-MEAN-DEF-006","DP-MEAN::DP-MEAN-DEF-007","DP-MEAN::DP-MEAN-DEF-008"],"source_anchors":[],"hypotheses":[{"key":"domain","proposition":{"def":{"id":"D-S7B-P059-DOMAIN","args":[{"var":"Q"},{"var":"w_family"},{"var":"c_w"},{"var":"C_w_err"},{"var":"Lambda_w"},{"var":"q"},{"var":"Z"}]}}}],"witnesses":[{"key":"C_mean","type":"Real","depends_on":["Q","w_family","c_w","C_w_err","Lambda_w"]}],"conclusions":[{"key":"family_mean","proposition":{"def":{"id":"D-S7B-P059-RESULT","args":[{"var":"Q"},{"var":"w_family"},{"var":"c_w"},{"var":"C_w_err"},{"var":"Lambda_w"},{"var":"q"},{"var":"Z"},{"var":"C_mean"}]}}}],"premises":[{"id":"MAP-P059-EXT001","producer":"A-S45-EXT001-EXISTS","closure_role":"REQUIRED","binder_map":{"h":{"app":{"fn":{"var":"w_family"},"args":[{"var":"q"}]}},"lambda_1":{"def":{"id":"D-S7B-P059-LAMBDA","args":[{"var":"Lambda_w"}]}},"lambda_2":{"lit":{"type":"Real","value":"1"}},"X":{"var":"Z"}},"hypothesis_map":{"h_nonnegative_multiplicative":{"guard":"ext_h_nonnegative_multiplicative"},"prime_power_geometric_bound":{"guard":"ext_prime_power_geometric_bound"},"lambda_1_nonnegative":{"guard":"ext_lambda_1_nonnegative"},"lambda_2_range":{"guard":"ext_lambda_2_range"},"X_at_least_2":{"guard":"ext_X_at_least_2"}},"witness_map":{},"consume":["mean_bound_exists"],"guards":[{"key":"ext_h_nonnegative_multiplicative","proposition":{"op":{"name":"and","args":[{"def":{"id":"DP-MEAN::DP-MEAN-DEF-006","args":[{"app":{"fn":{"var":"w_family"},"args":[{"var":"q"}]}}]}},{"def":{"id":"DP-MEAN::DP-MEAN-DEF-007","args":[{"app":{"fn":{"var":"w_family"},"args":[{"var":"q"}]}}]}}]}}},{"key":"ext_prime_power_geometric_bound","proposition":{"def":{"id":"DP-MEAN::DP-MEAN-DEF-008","args":[{"app":{"fn":{"var":"w_family"},"args":[{"var":"q"}]}},{"def":{"id":"D-S7B-P059-LAMBDA","args":[{"var":"Lambda_w"}]}},{"lit":{"type":"Real","value":"1"}}]}}},{"key":"ext_lambda_1_nonnegative","proposition":{"op":{"name":"ge","args":[{"def":{"id":"D-S7B-P059-LAMBDA","args":[{"var":"Lambda_w"}]}},{"lit":{"type":"Real","value":"0"}}]}}},{"key":"ext_lambda_2_range","proposition":{"op":{"name":"and","args":[{"op":{"name":"ge","args":[{"lit":{"type":"Real","value":"1"}},{"lit":{"type":"Real","value":"0"}}]}},{"op":{"name":"lt","args":[{"lit":{"type":"Real","value":"1"}},{"lit":{"type":"Real","value":"2"}}]}}]}}},{"key":"ext_X_at_least_2","proposition":{"op":{"name":"ge","args":[{"var":"Z"},{"lit":{"type":"Real","value":"2"}}]}}}]},{"id":"MAP-P059-P007","producer":"A-S45-P007-EXISTS","closure_role":"REQUIRED","binder_map":{"c":{"lit":{"type":"Real","value":"1/2"}},"eta":{"def":{"id":"D-S7B-P059-ETA","args":[{"var":"c_w"}]}},"C_err":{"def":{"id":"D-S7B-P059-CERR","args":[{"var":"C_w_err"},{"var":"Lambda_w"}]}},"L":{"def":{"id":"D-S7B-P059-L","args":[{"var":"Q"},{"var":"w_family"},{"var":"q"}]}}},"hypothesis_map":{"domain":{"guard":"p7_domain"}},"witness_map":{},"consume":["existentialized"],"guards":[{"key":"p7_domain","proposition":{"def":{"id":"D-S45-P007-DOMAIN","args":[{"lit":{"type":"Real","value":"1/2"}},{"def":{"id":"D-S7B-P059-ETA","args":[{"var":"c_w"}]}},{"def":{"id":"D-S7B-P059-CERR","args":[{"var":"C_w_err"},{"var":"Lambda_w"}]}},{"def":{"id":"D-S7B-P059-L","args":[{"var":"Q"},{"var":"w_family"},{"var":"q"}]}}]}}}]},{"id":"MAP-P059-P008","producer":"A-S45-P008-EXISTS","closure_role":"REQUIRED","binder_map":{"Q":{"type":{"var":"Q"}},"c_minus":{"lit":{"type":"Real","value":"1/2"}},"c_plus":{"lit":{"type":"Real","value":"1/2"}},"eta_star":{"def":{"id":"D-S7B-P059-ETA","args":[{"var":"c_w"}]}},"C_err_star":{"def":{"id":"D-S7B-P059-CERR","args":[{"var":"C_w_err"},{"var":"Lambda_w"}]}},"P_0":{"lit":{"type":"Real","value":"2"}},"m_fin":{"lit":{"type":"Real","value":"1"}},"M_fin":{"lit":{"type":"Real","value":"1"}},"coeff":{"def":{"id":"D-S7B-P059-COEFF","args":[{"var":"Q"}]}},"local_factor":{"def":{"id":"D-S7B-P059-LOCAL","args":[{"var":"Q"},{"var":"w_family"}]}}},"hypothesis_map":{"domain":{"guard":"p8_domain"}},"witness_map":{},"consume":["existentialized"],"guards":[{"key":"p8_domain","proposition":{"def":{"id":"D-S45-P008-DOMAIN","args":[{"type":{"var":"Q"}},{"lit":{"type":"Real","value":"1/2"}},{"lit":{"type":"Real","value":"1/2"}},{"def":{"id":"D-S7B-P059-ETA","args":[{"var":"c_w"}]}},{"def":{"id":"D-S7B-P059-CERR","args":[{"var":"C_w_err"},{"var":"Lambda_w"}]}},{"lit":{"type":"Real","value":"2"}},{"lit":{"type":"Real","value":"1"}},{"lit":{"type":"Real","value":"1"}},{"def":{"id":"D-S7B-P059-COEFF","args":[{"var":"Q"}]}},{"def":{"id":"D-S7B-P059-LOCAL","args":[{"var":"Q"},{"var":"w_family"}]}}]}}}]}],"witness_realizations":{"C_mean":{"def":{"id":"D-S7B-P059-W","args":[{"var":"Q"},{"var":"w_family"},{"var":"c_w"},{"var":"C_w_err"},{"var":"Lambda_w"}]}}},"proof_ref":"### P-059 — family-uniform mean with exposed common witnesses"}
```

- Prenex statement: let \(Q\) be a nonempty index set and
  \((w_q)_{q\in Q}\) a fixed family of nonnegative multiplicative functions.
  Fix common \(c_w,C_w^{\rm err},\Lambda_w>0\) such that, for every
  \(q\in Q\), prime \(p\), and \(i\ge1\),
  \[
  |w_q(p^i)-1/(i+1)|\le C_w^{\rm err}p^{-c_w},\qquad
  0\le w_q(p^i)\le\Lambda_w.
  \]
  Then there exists one \(C^{\rm mean}(c_w,C_w^{\rm err},\Lambda_w)>0\)
  such that for every \(q\in Q\) and every \(Z\ge2\),
  \[
  \sum_{r<Z}w_q(r)\le C^{\rm mean}Z(\log Z)^{-1/2}.
  \]
- Local equalities: none.
- Domain/range: the family and common witnesses are fixed before the single
  mean constant; \(q,Z\) are uniform variables after it.
- Input subject: exact partial sums of the family. Output: uniform log-decay.
- Premise maps:
  - `MAP-P059-EXT001`:

    | producer | slot | domain | consumer term | evidence |
    |---|---|---|---|---|
    | EXT-001 | `h` | nonnegative multiplicative | \(w_q\) | P-059 hypothesis |
    | EXT-001 | `lambda_1` | \(\mathbb R_{\ge0}\) | \(\Lambda_1:=\max(1,\Lambda_w)\) | common local bound |
    | EXT-001 | `lambda_2` | \([0,2)\) | \(1\) | local values are uniformly bounded by `lambda_1` |
    | EXT-001 | `X` | \(\mathbb R_{\ge2}\) | \(Z\) | P-059 binder |

    Producer hypothesis is the common \(w_q(p^i)\le\Lambda_1\). Consumed
    conclusion is EXT-001's exact mean bound for `SUB-P059-MEAN`;
    producer Euler subject is `SUB-P059-EULER`. Constants/uniformity:
    \((Q,(w_q),c_w,C_w^{\rm err},\Lambda_w)\to C^{\rm mean}\to(q,Z)\).
  - `MAP-P059-P007`:

    | producer | slot | domain | consumer term | evidence |
    |---|---|---|---|---|
    | P-007 | `c` | \(\mathbb R\) | \(1/2\) | first prime coefficient |
    | P-007 | `eta` | \(\mathbb R_{>0}\) | \(\min(c_w,1)\) | positive |
    | P-007 | `C_err` | \(\mathbb R_{>0}\) | \(C_{E,w}:=C_w^{\rm err}+2\Lambda_w\) | first-term error plus higher-power tail |
    | P-007 | `(L_p)` | positive prime family | \(L_{q,p}:=\sum_{j\ge0}w_q(p^j)p^{-j}\) | nonnegative, constant term 1 |
    | P-007 | `A` | \(\mathbb R_{\ge2}\) | \(2\) | literal |
    | P-007 | `B` | \(\mathbb R_{\ge2}\) | \(Z\) | P-059 binder |

    Hypothesis:
    \[
    |L_{q,p}-(1+1/(2p))|
    \le C_{E,w}p^{-1-\min(c_w,1)},
    \]
    because the \(j=1\) error contributes
    \(C_w^{\rm err}p^{-1-c_w}\) and
    \(\sum_{j\ge2}\Lambda_wp^{-j}\le2\Lambda_wp^{-2}\).
    Consumed conclusion is P-007's pointwise comparison; subject is
    `SUB-P059-EULER`. The pointwise constant is not promoted.
  - `MAP-P059-P008`: take the P-008 index set \(Q\),
    \(c_-:=c_+:=1/2\), \(\eta_*:=\min(c_w,1)\),
    \(C_{\rm err,*}:=C_{E,w}\), \(P_0:=2\),
    \(m_{\rm fin}:=M_{\rm fin}:=1\), \(c(q):=1/2\), and
    \(L_{q,p}\) as above. Its finite-prefix condition is vacuous. Consumed
    conclusion is the family-uniform product bound for
    `SUB-P059-EULER`; its single constant precedes \(q,Z\).

    | producer | slot | domain | consumer term | evidence |
    |---|---|---|---|---|
    | P-008 | `Q` | nonempty index set | \(Q\) | P-059 fixed domain |
    | P-008 | `c_-` | \(\mathbb R\) | \(1/2\) | fixed coefficient |
    | P-008 | `c_+` | \(\mathbb R\), \(c_-\le c_+\), \(1+c_-/2>0\) | \(1/2\) | admissible singleton interval |
    | P-008 | `eta_*` | \(\mathbb R_{>0}\) | \(\min(c_w,1)\) | \(c_w>0\) |
    | P-008 | `C_err,*` | \(\mathbb R_{>0}\) | \(C_{E,w}\) | displayed full tail bound |
    | P-008 | `P_0` | \(\mathbb R_{\ge2}\) | \(2\) | literal |
    | P-008 | `m_fin` | \(\mathbb R_{>0}\) | \(1\) | empty prefix |
    | P-008 | `M_fin` | \(\mathbb R_{\ge m_{\rm fin}}\) | \(1\) | empty prefix |
    | P-008 | `c` | map into \([1/2,1/2]\) | \(q\mapsto1/2\) | literal |
    | P-008 | `L` | positive local-factor family | \((q,p)\mapsto L_{q,p}\) | constant term \(1\) and nonnegativity |
    | P-008 | `q` | \(Q\) | \(q\) | P-059 uniform index |
    | P-008 | `A` | \(\mathbb R_{\ge2}\) | \(2\) | literal |
    | P-008 | `B` | \(\mathbb R_{\ge2}\) | \(Z\) | P-059 binder |
- Derivation certificate: combine the EXT-001 mean with P-008's uniform
  Euler bound; both use only the common witnesses, so the resulting mean
  constant is one witness for the whole family.
- Source/S2 anchor: ET p. 31; S2 R1 (5.10).
- Definitions used: D-014.

### Sections 8-11 typed support and witness definitions

These parameterized definitions are the exact analytic subjects and explicit witness selections used by the final proof cone. Their derivation text is retained here in the sole authority.

```mathminer-s3
{"schema":"mathminer.s3/1","id":"S-P-060","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"},{"key":"C_reg_sm","type":"Real"}],"uses_definitions":["D-002","D-003","D-015","D-016","D-017","D-019"],"source_anchors":[{"path":"stage3/canonical/CURRENT.md","git":"4279cd5e01f75401a9f5fa12d42961fe46b9ac8b","anchor":"### P-060 — exact regular smoothing"}],"result_type":"Prop","body":"- Prenex statement:\n  \\[\n  \\forall\\theta\\ge2\\;\\exists C_{\\rm reg,sm}(\\theta)>0\\;\n  \\forall y\\in(0,1)\\;\\forall k\\ge1\\;\\forall\\sigma\\in[\\theta,\\theta^k]\\;\n  \\forall x>\\theta^{2k-1},\n  \\]\n  \\[\n  S_k(x,y;\\sigma,\\theta)\\le C_{\\rm reg,sm}(\\theta)U_k.\n  \\]\n- Local equalities: \\(z_m=x/(mdd')\\); \\(S_k\\) is P-050/D-017 and \\(U_k\\)\n  is D-019.\n- Domain/range: \\(C_{\\rm reg,sm}\\) is chosen after \\(\\theta\\) and before\n  \\(y,k,\\sigma,x,d,d',t,m\\); it is uniform in all of them.\n- Input subject: exact P-050 four-variable regular sum.\n  Output subject: exact D-019 smoothed subject."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"W-P-060-C_reg_sm","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"},{"key":"p_060_p_052_2_C_sm","type":"Real"},{"key":"p_060_p_051f1_3_c_1","type":"Real"},{"key":"p_060_p_051f1_3_C_1","type":"Real"},{"key":"p_060_p_051f1_3_Lambda_1","type":"Real"}],"uses_definitions":["D-002","D-003","D-015","D-016","D-017","D-019"],"source_anchors":[],"result_type":"Real","body":"The product of (1+C) over the supplied positive premise constants, enlarged as in the adjacent finite inequality assembly."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"S-P-061","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"},{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"},{"key":"x","type":"Real"}],"uses_definitions":["D-019"],"source_anchors":[{"path":"stage3/canonical/CURRENT.md","git":"4279cd5e01f75401a9f5fa12d42961fe46b9ac8b","anchor":"### P-061 — exact three-way regular partition"}],"result_type":"Prop","body":"- Prenex statement: for every \\(y\\in(0,1)\\), \\(k\\ge1\\),\n  \\(\\theta\\ge2\\), \\(\\sigma\\in[\\theta,\\theta^k]\\), and\n  \\(x>\\theta^{2k-1}\\),\n  \\[\n  U_k=U_k^{\\rm up}+U_k^{\\rm mid}+U_k^{\\rm term}.\n  \\]\n- Local equalities: \\(z_m=x/(mdd')\\).\n- Domain/range: because \\(\\sigma\\le\\theta^k\\), the predicates\n  \\(z_m\\ge\\theta^k\\), \\(\\sigma\\le z_m<\\theta^k\\), \\(z_m<\\sigma\\)\n  are pairwise disjoint and exhaustive.\n- Input subject: exact U-sum. Output: exact equality of three restrictions."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"S-P-062","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"},{"key":"C_up","type":"Real"}],"uses_definitions":["D-019","D-020"],"source_anchors":[{"path":"stage3/canonical/CURRENT.md","git":"4279cd5e01f75401a9f5fa12d42961fe46b9ac8b","anchor":"### P-062 — upper-regime substitution"}],"result_type":"Prop","body":"- Prenex statement:\n  \\[\n  \\forall\\theta\\ge2\\;\\exists C_{\\rm up}(\\theta)>0\\;\n  \\forall y\\in(0,1)\\;\\forall k\\ge1\\;\\forall\\sigma\\in[\\theta,\\theta^k]\\;\n  \\forall x>\\theta^{2k-1},\\quad\n  U_k^{\\rm up}\\le C_{\\rm up}(\\theta)M_k^{\\rm up}.\n  \\]\n- Local equalities: at each term,\n  \\(K_{\\rm sh}=dd'\\) and \\(z=x/(mdd')=z_m\\).\n- Domain/range: exact upper predicate \\(z_m\\ge\\theta^k\\).\n- Input subject: \\(U_k^{\\rm up}\\). Output: \\(M_k^{\\rm up}\\)."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"S-P-063","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"},{"key":"C_A","type":"Real"}],"uses_definitions":["D-006","D-018","D-020"],"source_anchors":[{"path":"stage3/canonical/CURRENT.md","git":"4279cd5e01f75401a9f5fa12d42961fe46b9ac8b","anchor":"### P-063 — upper window/weight transport to \\(A_k\\)"}],"result_type":"Prop","body":"- Prenex statement:\n  \\[\n  \\forall\\theta\\ge2\\;\\exists C_A(\\theta)>0\\;\n  \\forall y\\in(0,1)\\;\\forall k\\ge1\\;\\forall\\sigma\\in[\\theta,\\theta^k]\\;\n  \\forall x>\\theta^{2k-1},\\quad\n  M_k^{\\rm up}\\le C_A(\\theta)R_k^A.\n  \\]\n- Local equalities: \\(z_m=x/(mdd')\\); \\(R_k^A\\) is D-018.\n- Domain/range: all summands nonnegative; exponent \\(-1/2\\) is negative.\n- Input subject: exact upper mixed sum. Output: exact D-018 A-subject."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"W-P-063-C_A","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"},{"key":"p_063_p_051f3_1_c_3","type":"Real"},{"key":"p_063_p_051f3_1_C_3","type":"Real"},{"key":"p_063_p_051f3_1_Lambda_3","type":"Real"}],"uses_definitions":["D-006","D-018","D-020"],"source_anchors":[],"result_type":"Real","body":"theta * sqrt(1 + 4 log(theta)/log(2)), proved by the strict four-power window and reversed exponent comparison."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"S-P-064","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"},{"key":"C_mid","type":"Real"}],"uses_definitions":["D-019","D-020"],"source_anchors":[{"path":"stage3/canonical/CURRENT.md","git":"4279cd5e01f75401a9f5fa12d42961fe46b9ac8b","anchor":"### P-064 — middle-regime substitution"}],"result_type":"Prop","body":"- Prenex statement:\n  \\[\n  \\forall\\theta\\ge2\\;\\exists C_{\\rm mid}(\\theta)>0\\;\n  \\forall y\\in(0,1)\\;\\forall k\\ge1\\;\\forall\\sigma\\in[\\theta,\\theta^k]\\;\n  \\forall x>\\theta^{2k-1},\\quad\n  U_k^{\\rm mid}\\le C_{\\rm mid}(\\theta)M_k^{\\rm mid}.\n  \\]\n- Local equalities: \\(K_{\\rm sh}=dd'\\), \\(z=z_m=x/(mdd')\\).\n- Domain/range: exact predicate \\(\\sigma\\le z_m<\\theta^k\\).\n- Input subject: exact middle U-subject. Output: exact middle mixed sum."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"S-P-065","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"},{"key":"C_B","type":"Real"}],"uses_definitions":["D-006","D-018","D-020"],"source_anchors":[{"path":"stage3/canonical/CURRENT.md","git":"4279cd5e01f75401a9f5fa12d42961fe46b9ac8b","anchor":"### P-065 — middle window/weight transport to \\(B_k\\)"}],"result_type":"Prop","body":"- Prenex statement:\n  \\[\n  \\forall\\theta\\ge2\\;\\exists C_B(\\theta)>0\\;\n  \\forall y\\in(0,1)\\;\\forall k\\ge1\\;\\forall\\sigma\\in[\\theta,\\theta^k]\\;\n  \\forall x>\\theta^{2k-1},\\quad\n  M_k^{\\rm mid}\\le C_B(\\theta)R_k^B.\n  \\]\n- Local equalities: \\(z_m=x/(mdd')\\); exponent \\(y/2-1\\in(-1,-1/2)\\).\n- Domain/range: exact middle range.\n- Input subject: middle mixed sum. Output: exact D-018\n  \\(B_k^{\\rm enl}\\)-subject; it is not identified with \\(B_k^{\\#}\\)."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"W-P-065-C_B","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"},{"key":"p_065_p_051f3_1_c_3","type":"Real"},{"key":"p_065_p_051f3_1_C_3","type":"Real"},{"key":"p_065_p_051f3_1_Lambda_3","type":"Real"}],"uses_definitions":["D-006","D-018","D-020"],"source_anchors":[],"result_type":"Real","body":"theta^5 * (1 + 4 log(theta)/log(2)), the explicit middle-window, negative-power, and restriction-enlargement loss."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"S-P-066","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"},{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"},{"key":"x","type":"Real"}],"uses_definitions":["D-019","D-020"],"source_anchors":[{"path":"stage3/canonical/CURRENT.md","git":"4279cd5e01f75401a9f5fa12d42961fe46b9ac8b","anchor":"### P-066 — terminal-regime substitution"}],"result_type":"Prop","body":"- Prenex statement: for every \\(y\\in(0,1)\\), \\(k\\ge1\\),\n  \\(\\theta\\ge2\\), \\(\\sigma\\in[\\theta,\\theta^k]\\), and\n  \\(x>\\theta^{2k-1}\\),\n  \\[\n  U_k^{\\rm term}\\le M_k^{\\rm term}.\n  \\]\n- Local equalities: \\(K_{\\rm sh}=dd'\\), \\(z=z_m=x/(mdd')\\).\n- Domain/range: exact predicate \\(z_m<\\sigma\\).\n- Input subject: terminal U-subject. Output: exact terminal mixed sum."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"S-P-067","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"},{"key":"C_C","type":"Real"}],"uses_definitions":["D-006","D-018","D-020"],"source_anchors":[{"path":"stage3/canonical/CURRENT.md","git":"4279cd5e01f75401a9f5fa12d42961fe46b9ac8b","anchor":"### P-067 — terminal window/weight transport to \\(C_k\\)"}],"result_type":"Prop","body":"- Prenex statement:\n  \\[\n  \\forall\\theta\\ge2\\;\\exists C_C(\\theta)>0\\;\n  \\forall y\\in(0,1)\\;\\forall k\\ge1\\;\\forall\\sigma\\in[\\theta,\\theta^k]\\;\n  \\forall x>\\theta^{2k-1},\\quad\n  M_k^{\\rm term}\\le C_C(\\theta)R_k^C.\n  \\]\n- Local equalities: \\(R_k^C=(\\log\\sigma)^{-y/2}O_kC_k\\), so the two\n  log-\\(\\sigma\\) factors cancel exactly.\n- Domain/range: exact terminal predicate; exponent \\(-1/2\\).\n- Input subject: terminal mixed sum. Output: exact D-018 C-subject."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"W-P-067-C_C","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"},{"key":"p_067_p_051f3_1_c_3","type":"Real"},{"key":"p_067_p_051f3_1_C_3","type":"Real"},{"key":"p_067_p_051f3_1_Lambda_3","type":"Real"},{"key":"p_067_p_053_3_C_ps","type":"Real"}],"uses_definitions":["D-006","D-018","D-020"],"source_anchors":[],"result_type":"Real","body":"C_ps * sqrt(1 + 4 log(theta)/log(2)), using the mapped P-053 witness and strict four-power window."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"S-P-068","kind":"DEFINITION","binders":[{"key":"C_A_abs","type":"Real"}],"uses_definitions":["D-006","D-018"],"source_anchors":[{"path":"stage3/canonical/CURRENT.md","git":"4279cd5e01f75401a9f5fa12d42961fe46b9ac8b","anchor":"### P-068 — \\(A_k\\) convolution bound"}],"result_type":"Prop","body":"- Prenex statement: there exists an absolute \\(C_A'>0\\) such that for all\n  \\(y\\in(0,1),k\\ge1,\\sigma\\ge\\theta\\ge2,x>\\theta^{2k-1}\\),\n  \\[\n  A_k\\le C_A'x\\theta^{-2k}k^{(y-1)/2}.\n  \\]\n- Local equalities: A is D-018 exactly.\n- Domain/range: constant uniform in every displayed variable.\n- Input subject: exact A-sum. Output: beta-convolution bound."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"S-P-069","kind":"DEFINITION","binders":[{"key":"C_mc","type":"Real"}],"uses_definitions":["D-006","D-018"],"source_anchors":[{"path":"stage3/canonical/CURRENT.md","git":"4279cd5e01f75401a9f5fa12d42961fe46b9ac8b","anchor":"### P-069 — exact R3 middle-convolution bounds"}],"result_type":"Prop","body":"- Prenex statement:\n  \\[\n  \\exists C_{\\rm mc}>0\\;\\forall\\theta\\ge2\\;\n  \\forall y\\in(0,1)\\;\\forall k\\ge1\\;\\forall\\sigma\\ge\\theta\\;\n  \\forall x>\\theta^{2k-1},\n  \\]\n  \\[\n  B_k^{\\#}(x;y)\\le {C_{\\rm mc}\\over y}x\\theta^{-2k}\n  \\ell(2x\\theta^{1-2k})^{(y-1)/2},\n  \\]\n  and the same bound holds with \\(B_k^{\\#}\\) replaced by\n  \\(B_k^{\\rm enl}\\).\n- Local equalities: \\(B_k^{\\#}\\) is the exact R3 subject, and\n  \\(B_k^{\\rm enl}\\) is the separately named restriction/enlargement subject.\n- Domain/range: exponent \\(y/2-1>-1\\).\n- Input subject: exact B-sum. Output: beta-convolution bound."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"S-P-070","kind":"DEFINITION","binders":[{"key":"c_star","type":"Real"},{"key":"C_star","type":"Real"},{"key":"Lambda_star","type":"Real"},{"key":"C_fam","type":"Real"}],"uses_definitions":["D-014","D-015"],"source_anchors":[{"path":"stage3/canonical/CURRENT.md","git":"4279cd5e01f75401a9f5fa12d42961fe46b9ac8b","anchor":"### P-070 — family-uniform final \\(w_{4,k}\\) mean"}],"result_type":"Prop","body":"- Prenex statement:\n  \\[\n  \\exists c_*>0\\;\\exists C_*>0\\;\\exists\\Lambda_*>0\\;\n  \\exists C_{\\rm fam}>0\\;\\forall\\theta\\ge2,\n  \\]\n  define, inside the scope of the selected \\(C_{\\rm fam}\\),\n  \\[\n  C_4(C_{\\rm fam},\\theta):=\n  {C_{\\rm fam}\\theta^2\\over\\sqrt{\\log\\theta}}>0.\n  \\tag{P070-C4}\n  \\]\n  Then for every \\(y\\in(0,1)\\), every\n  \\(k\\in\\mathbb N_{\\ge1}\\), and every \\(\\sigma\\ge\\theta\\), both\n  \\[\n  \\forall Z\\ge2,\\qquad\n  \\sum_{r<Z}w_{4,k}(r)\\le C_{\\rm fam}Z(\\log Z)^{-1/2},\n  \\tag{P070-family-mean}\n  \\]\n  and\n  \\[\n  \\sum_{\\theta^{k-1}<r<\\theta^{k+2}}w_{4,k}(r)\n  \\le C_4(C_{\\rm fam},\\theta)\\theta^k k^{-1/2}.\n  \\tag{P070-window}\n  \\]\n- Local equalities: \\(w_{4,k}\\) is D-015.\n- Domain/range: \\(C_{\\rm fam}\\) is selected before\n  \\(\\theta,y,k,\\sigma,Z\\). The positive term\n  \\(C_4(C_{\\rm fam},\\theta)\\) is an active definition after \\(\\theta\\) and\n  before \\(y,k,\\sigma,Z\\); it has no free witness or hidden binder.\n- Input subject: exact finite \\(d'\\)-window sum. Output: exact mean bound."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"W-P-070-C_fam","kind":"DEFINITION","binders":[{"key":"p_070_p_051f4_1_c_4","type":"Real"},{"key":"p_070_p_051f4_1_C_4w","type":"Real"},{"key":"p_070_p_051f4_1_Lambda_4","type":"Real"},{"key":"p_070_p_051g_2_c_star","type":"Real"},{"key":"p_070_p_051g_2_C_star","type":"Real"},{"key":"p_070_p_051g_2_Lambda_star","type":"Real"},{"key":"p_070_p_059_3_C_mean","type":"Real"}],"uses_definitions":["D-014","D-015"],"source_anchors":[],"result_type":"Real","body":"The product of (1+C) over the supplied positive premise constants, enlarged as in the adjacent finite inequality assembly."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"S-P-071","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"},{"key":"C_A_asm","type":"Real"}],"uses_definitions":["D-018"],"source_anchors":[{"path":"stage3/canonical/CURRENT.md","git":"4279cd5e01f75401a9f5fa12d42961fe46b9ac8b","anchor":"### P-071 — regular upper branch assembly"}],"result_type":"Prop","body":"- Prenex statement:\n  \\[\n  \\forall\\theta\\ge2\\;\\exists C_{A,\\rm asm}(\\theta)>0\\;\n  \\forall y\\in(0,1)\\;\\forall k\\ge1\\;\\forall\\sigma\\in[\\theta,\\theta^k]\\;\n  \\forall x>\\theta^{2k-1},\n  \\]\n  \\[\n  R_k^A\\le C_{A,\\rm asm}(\\theta)\n  x(\\log\\sigma)^{-y}k^{(y-3)/2}k^{(y-1)/2}.\n  \\]\n- Local equalities: \\(R_k^A=(\\log\\sigma)^{-y/2}O_kA_k\\).\n- Domain/range: uniform in \\(y,k,\\sigma,x\\).\n- Input subject: exact transported A-subject. Output: upper brace term."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"W-P-071-C_A_asm","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"},{"key":"p_071_p_058_1_C_out","type":"Real"},{"key":"p_071_p_068_2_C_A_abs","type":"Real"},{"key":"p_071_p_070_3_c_star","type":"Real"},{"key":"p_071_p_070_3_C_star","type":"Real"},{"key":"p_071_p_070_3_Lambda_star","type":"Real"},{"key":"p_071_p_070_3_C_fam","type":"Real"}],"uses_definitions":["D-018"],"source_anchors":[],"result_type":"Real","body":"The product of (1+C) over the supplied positive premise constants, enlarged as in the adjacent finite inequality assembly."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"S-P-072","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"},{"key":"C_B_asm","type":"Real"}],"uses_definitions":["D-018"],"source_anchors":[{"path":"stage3/canonical/CURRENT.md","git":"4279cd5e01f75401a9f5fa12d42961fe46b9ac8b","anchor":"### P-072 — regular middle branch assembly"}],"result_type":"Prop","body":"- Prenex statement:\n  \\[\n  \\forall\\theta\\ge2\\;\\exists C_{B,\\rm asm}(\\theta)>0\\;\n  \\forall y\\in(0,1)\\;\\forall k\\ge1\\;\\forall\\sigma\\in[\\theta,\\theta^k]\\;\n  \\forall x>\\theta^{2k-1},\n  \\]\n  \\[\n  R_k^B\\le {C_{B,\\rm asm}(\\theta)\\over y}\n  x(\\log\\sigma)^{-y}k^{(y-3)/2}\n  \\ell(2x\\theta^{1-2k})^{(y-1)/2}.\n  \\]\n- Local equalities: exact D-018 \\(R_k^B\\).\n- Domain/range: uniform after \\(\\theta\\).\n- Input subject: exact transported B-subject. Output: middle brace term."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"W-P-072-C_B_asm","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"},{"key":"p_072_p_058_1_C_out","type":"Real"},{"key":"p_072_p_069_2_C_mc","type":"Real"},{"key":"p_072_p_070_3_c_star","type":"Real"},{"key":"p_072_p_070_3_C_star","type":"Real"},{"key":"p_072_p_070_3_Lambda_star","type":"Real"},{"key":"p_072_p_070_3_C_fam","type":"Real"}],"uses_definitions":["D-018"],"source_anchors":[],"result_type":"Real","body":"The product of (1+C) over the supplied positive premise constants, enlarged as in the adjacent finite inequality assembly."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"S-P-073","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"},{"key":"C_C_asm","type":"Real"}],"uses_definitions":["D-018"],"source_anchors":[{"path":"stage3/canonical/CURRENT.md","git":"4279cd5e01f75401a9f5fa12d42961fe46b9ac8b","anchor":"### P-073 — regular terminal branch assembly"}],"result_type":"Prop","body":"- Prenex statement:\n  \\[\n  \\forall\\theta\\ge2\\;\\exists C_{C,\\rm asm}(\\theta)>0\\;\n  \\forall y\\in(0,1)\\;\\forall k\\ge1\\;\\forall\\sigma\\in[\\theta,\\theta^k]\\;\n  \\forall x>\\theta^{2k-1},\n  \\]\n  \\[\n  R_k^C\\le C_{C,\\rm asm}(\\theta)\n  x(\\log\\sigma)^{-y}k^{(y-3)/2}\n  {(\\log\\sigma)^{y/2}\\over\n  \\ell(2x\\theta^{1-2k})^{1/2}}.\n  \\]\n- Local equalities: exact D-018 \\(R_k^C\\).\n- Domain/range: uniform after \\(\\theta\\).\n- Input subject: exact transported C-subject. Output: terminal brace term."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"W-P-073-C_C_asm","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"},{"key":"p_073_p_058_1_C_out","type":"Real"},{"key":"p_073_p_070_2_c_star","type":"Real"},{"key":"p_073_p_070_2_C_star","type":"Real"},{"key":"p_073_p_070_2_Lambda_star","type":"Real"},{"key":"p_073_p_070_2_C_fam","type":"Real"}],"uses_definitions":["D-018"],"source_anchors":[],"result_type":"Real","body":"The product of (1+C) over the supplied positive premise constants, enlarged as in the adjacent finite inequality assembly."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"S-P-074","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"},{"key":"C_reg","type":"Real"}],"uses_definitions":["D-006","D-017","D-018","D-019","D-020"],"source_anchors":[{"path":"stage3/canonical/CURRENT.md","git":"4279cd5e01f75401a9f5fa12d42961fe46b9ac8b","anchor":"### P-074 — regular envelope addition"}],"result_type":"Prop","body":"- Prenex statement:\n  \\[\n  \\forall\\theta\\ge2\\;\\exists C_{\\rm reg}(\\theta)>0\\;\n  \\forall y\\in(0,1)\\;\\forall k\\ge1\\;\\forall\\sigma\\in[\\theta,\\theta^k]\\;\n  \\forall x>\\theta^{2k-1},\n  \\]\n  \\[\n  S_k(x,y;\\sigma,\\theta)\\le {C_{\\rm reg}(\\theta)\\over y}\n  x(\\log\\sigma)^{-y}k^{(y-3)/2}\n  \\left\\{k^{(y-1)/2}\n  +\\ell(2x\\theta^{1-2k})^{(y-1)/2}\n  +{(\\log\\sigma)^{y/2}\\over\\ell(2x\\theta^{1-2k})^{1/2}}\\right\\}.\n  \\]\n- Local equalities: the three branches are D-019/D-020/D-018.\n- Domain/range: the theta-only constant precedes \\(y,k,\\sigma,x\\); the sharp\n  dependence on the subsequently fixed \\(y\\) is the displayed \\(1/y\\).\n  The numerator constant is selected after \\(\\theta\\) from the three assembly\n  constants, each of which already contains the literal\n  \\(C_4(C_{\\rm fam},\\theta)\\) where used; it introduces no new \\(y\\)-dependence.\n- Input subject: exact regular S-subject. Output: regular P3 envelope."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"W-P-074-C_reg","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"},{"key":"p_074_p_060_1_C_reg_sm","type":"Real"},{"key":"p_074_p_062_3_C_up","type":"Real"},{"key":"p_074_p_063_4_C_A","type":"Real"},{"key":"p_074_p_064_5_C_mid","type":"Real"},{"key":"p_074_p_065_6_C_B","type":"Real"},{"key":"p_074_p_067_8_C_C","type":"Real"},{"key":"p_074_p_071_9_C_A_asm","type":"Real"},{"key":"p_074_p_072_10_C_B_asm","type":"Real"},{"key":"p_074_p_073_11_C_C_asm","type":"Real"}],"uses_definitions":["D-006","D-017","D-018","D-019","D-020"],"source_anchors":[],"result_type":"Real","body":"The product of (1+C) over the supplied positive premise constants, enlarged as in the adjacent finite inequality assembly."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"S-P-075","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"},{"key":"C_tr_sm","type":"Real"}],"uses_definitions":["D-002","D-003","D-015","D-016","D-017","D-021a","D-021b","D-021c","D-021d","D-021e"],"source_anchors":[{"path":"stage3/canonical/CURRENT.md","git":"4279cd5e01f75401a9f5fa12d42961fe46b9ac8b","anchor":"### P-075 — exact transition smoothing"}],"result_type":"Prop","body":"- Prenex statement:\n  \\[\n  \\forall\\theta\\ge2\\;\\exists C_{\\rm tr,sm}(\\theta)>0\\;\n  \\forall y\\in(0,1)\\;\\forall k\\ge1\\;\\forall\\sigma\\in(\\theta^k,\\theta^{k+1})\\;\n  \\forall x>\\theta^{2k-1},\\quad\n  S_k(x,y;\\sigma,\\theta)\\le C_{\\rm tr,sm}(\\theta)V_k.\n  \\]\n- Local equalities: \\(z_m=x/(mdd')\\); V is D-021a/D-021b/D-021c/D-021d/D-021e.\n- Domain/range: constant precedes every uniform variable and summation index.\n- Input subject: exact P-050 transition inversion. Output: exact V."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"W-P-075-C_tr_sm","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"},{"key":"p_075_p_052_2_C_sm","type":"Real"},{"key":"p_075_p_051f1_3_c_1","type":"Real"},{"key":"p_075_p_051f1_3_C_1","type":"Real"},{"key":"p_075_p_051f1_3_Lambda_1","type":"Real"}],"uses_definitions":["D-002","D-003","D-015","D-016","D-017","D-021a","D-021b","D-021c","D-021d","D-021e"],"source_anchors":[],"result_type":"Real","body":"The product of (1+C) over the supplied positive premise constants, enlarged as in the adjacent finite inequality assembly."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"S-P-076","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"},{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"},{"key":"x","type":"Real"}],"uses_definitions":["D-021a","D-021b"],"source_anchors":[{"path":"stage3/canonical/CURRENT.md","git":"4279cd5e01f75401a9f5fa12d42961fe46b9ac8b","anchor":"### P-076 — exact transition partition"}],"result_type":"Prop","body":"- Prenex statement: for every \\(y\\in(0,1)\\), \\(k\\ge1\\), \\(\\theta\\ge2\\),\n  \\(\\sigma\\in(\\theta^k,\\theta^{k+1})\\), and \\(x>\\theta^{2k-1}\\),\n  \\(V_k=V_k^\\ge+V_k^<\\).\n- Local equalities: \\(z_m=x/(mdd')\\).\n- Domain/range: \\(z_m\\ge\\sigma\\) and \\(z_m<\\sigma\\) are disjoint/exhaustive.\n- Input subject: exact V. Output: exact equality."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"S-P-077","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"},{"key":"C_tr_ge","type":"Real"}],"uses_definitions":["D-021b","D-021c"],"source_anchors":[{"path":"stage3/canonical/CURRENT.md","git":"4279cd5e01f75401a9f5fa12d42961fe46b9ac8b","anchor":"### P-077 — transition high-regime substitution"}],"result_type":"Prop","body":"- Prenex statement:\n  \\[\n  \\forall\\theta\\ge2\\;\\exists C_{\\rm tr,\\ge}(\\theta)>0\\;\n  \\forall y\\in(0,1)\\;\\forall k\\ge1\\;\n  \\forall\\sigma\\in(\\theta^k,\\theta^{k+1})\\;\n  \\forall x>\\theta^{2k-1},\\quad\n  V_k^\\ge\\le C_{\\rm tr,\\ge}(\\theta)\\widetilde H_k.\n  \\]\n- Local equalities: \\(K_{\\rm sh}=dd'\\), \\(z=z_m=x/(mdd')\\).\n- Domain/range: exact \\(z_m\\ge\\sigma\\) branch.\n- Input subject: \\(V^\\ge\\). Output: exact \\(\\widetilde H\\)."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"W-P-077-C_tr_ge","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"},{"key":"p_077_p_005_1_C_shift","type":"Real"},{"key":"p_077_p_007_2_P_err","type":"Real"},{"key":"p_077_p_007_2_C_minus","type":"Real"},{"key":"p_077_p_007_2_C_plus","type":"Real"},{"key":"p_077_p_008_3_C_minus","type":"Real"},{"key":"p_077_p_008_3_C_plus","type":"Real"},{"key":"p_077_p_051f2_4_c_2","type":"Real"},{"key":"p_077_p_051f2_4_C_2","type":"Real"},{"key":"p_077_p_051f2_4_Lambda_2","type":"Real"},{"key":"p_077_p_051f1_5_c_1","type":"Real"},{"key":"p_077_p_051f1_5_C_1","type":"Real"},{"key":"p_077_p_051f1_5_Lambda_1","type":"Real"},{"key":"p_077_p_051g_7_c_star","type":"Real"},{"key":"p_077_p_051g_7_C_star","type":"Real"},{"key":"p_077_p_051g_7_Lambda_star","type":"Real"}],"uses_definitions":["D-021b","D-021c"],"source_anchors":[],"result_type":"Real","body":"The product of (1+C) over the supplied positive premise constants, enlarged as in the adjacent finite inequality assembly."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"S-P-078","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"},{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"},{"key":"x","type":"Real"}],"uses_definitions":["D-021c","D-021d"],"source_anchors":[{"path":"stage3/canonical/CURRENT.md","git":"4279cd5e01f75401a9f5fa12d42961fe46b9ac8b","anchor":"### P-078 — transition high weight transport"}],"result_type":"Prop","body":"- Prenex statement: for every \\(y\\in(0,1)\\), \\(k\\ge1\\), \\(\\theta\\ge2\\),\n  \\(\\sigma\\in(\\theta^k,\\theta^{k+1})\\), and \\(x>\\theta^{2k-1}\\),\n  \\(\\widetilde H_k\\le H_k\\).\n- Local equalities: the subjects differ only by \\(w_{2,k}\\) versus\n  \\(w_{3,k}\\).\n- Domain/range: termwise nonnegative comparison.\n- Input subject: exact \\(\\widetilde H\\). Output: exact H."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"S-P-079","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"},{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"},{"key":"x","type":"Real"}],"uses_definitions":["D-021b","D-021c"],"source_anchors":[{"path":"stage3/canonical/CURRENT.md","git":"4279cd5e01f75401a9f5fa12d42961fe46b9ac8b","anchor":"### P-079 — transition low-regime substitution"}],"result_type":"Prop","body":"- Prenex statement: for every \\(y\\in(0,1)\\), \\(k\\ge1\\), \\(\\theta\\ge2\\),\n  \\(\\sigma\\in(\\theta^k,\\theta^{k+1})\\), and \\(x>\\theta^{2k-1}\\),\n  \\(V_k^<\\le\\widetilde L_k\\).\n- Local equalities: \\(K_{\\rm sh}=dd'\\), \\(z=z_m\\).\n- Domain/range: exact \\(z_m<\\sigma\\) branch.\n- Input subject: \\(V^<\\). Output: exact \\(\\widetilde L\\)."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"S-P-080","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"},{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"},{"key":"x","type":"Real"}],"uses_definitions":["D-021c","D-021d"],"source_anchors":[{"path":"stage3/canonical/CURRENT.md","git":"4279cd5e01f75401a9f5fa12d42961fe46b9ac8b","anchor":"### P-080 — transition low weight transport"}],"result_type":"Prop","body":"- Prenex statement: for every \\(y\\in(0,1)\\), \\(k\\ge1\\), \\(\\theta\\ge2\\),\n  \\(\\sigma\\in(\\theta^k,\\theta^{k+1})\\), and \\(x>\\theta^{2k-1}\\),\n  \\(\\widetilde L_k\\le L_k\\).\n- Local equalities: subjects differ only by \\(w_1\\) versus \\(w_{3,k}\\).\n- Domain/range: nonnegative termwise comparison.\n- Input subject: exact \\(\\widetilde L\\). Output: exact L."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"S-P-081","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"}],"uses_definitions":[],"source_anchors":[{"path":"stage3/canonical/CURRENT.md","git":"4279cd5e01f75401a9f5fa12d42961fe46b9ac8b","anchor":"### P-081 — transition scale comparison"}],"result_type":"Prop","body":"- Prenex statement: for every \\(k\\ge1,\\theta\\ge2\\), and\n  \\(\\theta^k<\\sigma<\\theta^{k+1}\\),\n  \\[\n  k\\log\\theta<\\log\\sigma<(k+1)\\log\\theta,\\qquad\n  k\\asymp_\\theta\\log\\sigma.\n  \\]\n- Local equalities: none.\n- Domain/range: positive logarithms.\n- Input subject: transition inequalities. Output: exact scale comparison."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"S-P-082","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"},{"key":"C_tr_H","type":"Real"}],"uses_definitions":["D-006","D-021d","D-021e"],"source_anchors":[{"path":"stage3/canonical/CURRENT.md","git":"4279cd5e01f75401a9f5fa12d42961fe46b9ac8b","anchor":"### P-082 — transition high convolution transport"}],"result_type":"Prop","body":"- Prenex statement:\n  \\[\n  \\forall\\theta\\ge2\\;\\exists C_{\\rm tr,H}(\\theta)>0\\;\n  \\forall y\\in(0,1)\\;\\forall k\\ge1\\;\n  \\forall\\sigma\\in(\\theta^k,\\theta^{k+1})\\;\n  \\forall x>\\theta^{2k-1},\\quad\n  H_k\\le C_{\\rm tr,H}(\\theta)(\\log\\sigma)^{-1/2}\n  x\\theta^{-2k}O_k^{\\rm tr}.\n  \\]\n- Local equalities: \\(z_m=x/(mdd')\\).\n- Domain/range: strict product window; safe exponent \\(-1/2\\).\n- Input subject: exact H. Output: O-tr times high envelope."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"W-P-082-C_tr_H","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"}],"uses_definitions":["D-006","D-021d","D-021e"],"source_anchors":[],"result_type":"Real","body":"theta * sqrt(1 + 4 log(theta)/log(2)), the transition high-window transport loss."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"S-P-083","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"},{"key":"C_tr_L","type":"Real"}],"uses_definitions":["D-006","D-021d","D-021e"],"source_anchors":[{"path":"stage3/canonical/CURRENT.md","git":"4279cd5e01f75401a9f5fa12d42961fe46b9ac8b","anchor":"### P-083 — transition low convolution transport"}],"result_type":"Prop","body":"- Prenex statement:\n  \\[\n  \\forall\\theta\\ge2\\;\\exists C_{\\rm tr,L}(\\theta)>0\\;\n  \\forall y\\in(0,1)\\;\\forall k\\ge1\\;\n  \\forall\\sigma\\in(\\theta^k,\\theta^{k+1})\\;\n  \\forall x>\\theta^{2k-1},\\quad\n  L_k\\le C_{\\rm tr,L}(\\theta)x\\theta^{-2k}\n  \\ell(2x\\theta^{1-2k})^{-1/2}O_k^{\\rm tr}.\n  \\]\n- Local equalities: \\(z_m=x/(mdd')\\).\n- Domain/range: exact low restriction may be dropped by nonnegativity.\n- Input subject: exact L. Output: O-tr times terminal endpoint."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"W-P-083-C_tr_L","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"},{"key":"p_083_p_053_1_C_ps","type":"Real"}],"uses_definitions":["D-006","D-021d","D-021e"],"source_anchors":[],"result_type":"Real","body":"C_ps * sqrt(1 + 4 log(theta)/log(2)), using the mapped P-053 witness and strict four-power window."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"S-P-084","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"},{"key":"C_tr_out","type":"Real"}],"uses_definitions":["D-002","D-003","D-005","D-015","D-021e"],"source_anchors":[{"path":"stage3/canonical/CURRENT.md","git":"4279cd5e01f75401a9f5fa12d42961fe46b9ac8b","anchor":"### P-084 — transition outer shifted mean"}],"result_type":"Prop","body":"- Prenex statement:\n  \\[\n  \\forall\\theta\\in\\mathbb R_{\\ge2}\\;\\exists C_{\\rm tr,out}(\\theta)>0\\;\n  \\forall y\\in(0,1)\\;\\forall k\\in\\mathbb N_{\\ge1}\\;\n  \\forall\\sigma\\in\\mathbb R,\\quad\n  \\theta^k<\\sigma<\\theta^{k+1}\\Longrightarrow\n  O_k^{\\rm tr}\\le C_{\\rm tr,out}(\\theta)\n  \\theta^k(\\log\\sigma)^{-1}\n  \\sum_{\\theta^{k-1}<d'<\\theta^{k+2}}w_{4,k}(d').\n  \\]\n- Local equalities: roughness restricts \\(d\\) to\n  \\([\\sigma,\\theta^{k+1})\\).\n- Domain/range: constant uniform in \\(y,k,\\sigma,d,d'\\).\n- Input subject: exact transition O-sum. Output: exact \\(d'\\)-sum."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"W-P-084-C_tr_out","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"},{"key":"p_084_p_005_2_C_shift","type":"Real"},{"key":"p_084_p_007_3_P_err","type":"Real"},{"key":"p_084_p_007_3_C_minus","type":"Real"},{"key":"p_084_p_007_3_C_plus","type":"Real"},{"key":"p_084_p_008_4_C_minus","type":"Real"},{"key":"p_084_p_008_4_C_plus","type":"Real"},{"key":"p_084_p_051f4_5_c_4","type":"Real"},{"key":"p_084_p_051f4_5_C_4w","type":"Real"},{"key":"p_084_p_051f4_5_Lambda_4","type":"Real"},{"key":"p_084_p_051f3_6_c_3","type":"Real"},{"key":"p_084_p_051f3_6_C_3","type":"Real"},{"key":"p_084_p_051f3_6_Lambda_3","type":"Real"},{"key":"p_084_p_051g_8_c_star","type":"Real"},{"key":"p_084_p_051g_8_C_star","type":"Real"},{"key":"p_084_p_051g_8_Lambda_star","type":"Real"}],"uses_definitions":["D-002","D-003","D-005","D-015","D-021e"],"source_anchors":[],"result_type":"Real","body":"The product of (1+C) over the supplied positive premise constants, enlarged as in the adjacent finite inequality assembly."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"S-P-085","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"},{"key":"C_tr_A","type":"Real"}],"uses_definitions":["D-006","D-021d"],"source_anchors":[{"path":"stage3/canonical/CURRENT.md","git":"4279cd5e01f75401a9f5fa12d42961fe46b9ac8b","anchor":"### P-085 — transition high assembly"}],"result_type":"Prop","body":"- Prenex statement:\n  \\[\n  \\forall\\theta\\ge2\\;\\exists C_{\\rm tr,A}(\\theta)>0\\;\n  \\forall y\\in(0,1)\\;\\forall k\\ge1\\;\n  \\forall\\sigma\\in(\\theta^k,\\theta^{k+1})\\;\n  \\forall x>\\theta^{2k-1},\n  \\]\n  \\[\n  H_k\\le C_{\\rm tr,A}(\\theta)\n  x(\\log\\sigma)^{-y}k^{(y-3)/2}k^{(y-1)/2}.\n  \\]\n- Local equalities: none.\n- Domain/range: uniform after \\(\\theta\\).\n- Input subject: exact H. Output: first P3 brace term."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"W-P-085-C_tr_A","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"},{"key":"p_085_p_082_1_C_tr_H","type":"Real"},{"key":"p_085_p_084_2_C_tr_out","type":"Real"},{"key":"p_085_p_070_3_c_star","type":"Real"},{"key":"p_085_p_070_3_C_star","type":"Real"},{"key":"p_085_p_070_3_Lambda_star","type":"Real"},{"key":"p_085_p_070_3_C_fam","type":"Real"}],"uses_definitions":["D-006","D-021d"],"source_anchors":[],"result_type":"Real","body":"The product of (1+C) over the supplied positive premise constants, enlarged as in the adjacent finite inequality assembly."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"S-P-086","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"},{"key":"C_tr_C","type":"Real"}],"uses_definitions":["D-006","D-021d"],"source_anchors":[{"path":"stage3/canonical/CURRENT.md","git":"4279cd5e01f75401a9f5fa12d42961fe46b9ac8b","anchor":"### P-086 — transition low assembly"}],"result_type":"Prop","body":"- Prenex statement:\n  \\[\n  \\forall\\theta\\ge2\\;\\exists C_{\\rm tr,C}(\\theta)>0\\;\n  \\forall y\\in(0,1)\\;\\forall k\\ge1\\;\n  \\forall\\sigma\\in(\\theta^k,\\theta^{k+1})\\;\n  \\forall x>\\theta^{2k-1},\n  \\]\n  \\[\n  L_k\\le C_{\\rm tr,C}(\\theta)\n  x(\\log\\sigma)^{-y}k^{(y-3)/2}\n  {(\\log\\sigma)^{y/2}\\over\\ell(2x\\theta^{1-2k})^{1/2}}.\n  \\]\n- Local equalities: none.\n- Domain/range: uniform after \\(\\theta\\).\n- Input subject: exact L. Output: terminal P3 brace term."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"W-P-086-C_tr_C","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"},{"key":"p_086_p_083_1_C_tr_L","type":"Real"},{"key":"p_086_p_084_2_C_tr_out","type":"Real"},{"key":"p_086_p_070_3_c_star","type":"Real"},{"key":"p_086_p_070_3_C_star","type":"Real"},{"key":"p_086_p_070_3_Lambda_star","type":"Real"},{"key":"p_086_p_070_3_C_fam","type":"Real"}],"uses_definitions":["D-006","D-021d"],"source_anchors":[],"result_type":"Real","body":"The product of (1+C) over the supplied positive premise constants, enlarged as in the adjacent finite inequality assembly."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"S-P-087","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"},{"key":"C_tr","type":"Real"}],"uses_definitions":["D-006","D-017","D-021a","D-021b","D-021c","D-021d","D-021e"],"source_anchors":[{"path":"stage3/canonical/CURRENT.md","git":"4279cd5e01f75401a9f5fa12d42961fe46b9ac8b","anchor":"### P-087 — transition envelope addition"}],"result_type":"Prop","body":"- Prenex statement:\n  \\[\n  \\forall\\theta\\ge2\\;\\exists C_{\\rm tr}(\\theta)>0\\;\n  \\forall y\\in(0,1)\\;\\forall k\\ge1\\;\n  \\forall\\sigma\\in(\\theta^k,\\theta^{k+1})\\;\n  \\forall x>\\theta^{2k-1},\n  \\]\n  \\[\n  S_k(x,y;\\sigma,\\theta)\\le C_{\\rm tr}(\\theta)\n  x(\\log\\sigma)^{-y}k^{(y-3)/2}\n  \\left\\{k^{(y-1)/2}\n  +\\ell(2x\\theta^{1-2k})^{(y-1)/2}\n  +{(\\log\\sigma)^{y/2}\\over\\ell(2x\\theta^{1-2k})^{1/2}}\\right\\}.\n  \\]\n- Local equalities: exact D-021a/D-021b/D-021c/D-021d/D-021e branch subjects.\n- Domain/range: one \\(\\theta\\)-constant, uniform in all other variables.\n  It is selected after \\(\\theta\\) from the high/low assembly constants, whose\n  P-070 input is exactly \\(C_4(C_{\\rm fam},\\theta)\\).\n- Input subject: exact transition S. Output: common P3 envelope."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"W-P-087-C_tr","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"},{"key":"p_087_p_075_1_C_tr_sm","type":"Real"},{"key":"p_087_p_077_3_C_tr_ge","type":"Real"},{"key":"p_087_p_085_7_C_tr_A","type":"Real"},{"key":"p_087_p_086_8_C_tr_C","type":"Real"}],"uses_definitions":["D-006","D-017","D-021a","D-021b","D-021c","D-021d","D-021e"],"source_anchors":[],"result_type":"Real","body":"The product of (1+C) over the supplied positive premise constants, enlarged as in the adjacent finite inequality assembly."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"S-P-088","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"},{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"},{"key":"x","type":"Real"}],"uses_definitions":["D-013","D-017"],"source_anchors":[{"path":"stage3/canonical/CURRENT.md","git":"4279cd5e01f75401a9f5fa12d42961fe46b9ac8b","anchor":"### P-088 — empty-bin result"}],"result_type":"Prop","body":"- Prenex statement: for every \\(y\\in(0,1),k\\ge1,\\sigma\\ge\\theta\\ge2,x>0\\),\n  if \\(\\theta^{k+1}\\le\\sigma\\), then \\(S_k(x,y;\\sigma,\\theta)=0\\).\n- Local equalities: none.\n- Domain/range: exact equality.\n- Input subject: D-013 outer d-bin. Output: zero mean."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"S-P-089","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"},{"key":"C_3","type":"Real"}],"uses_definitions":["D-006","D-017"],"source_anchors":[{"path":"stage3/canonical/CURRENT.md","git":"4279cd5e01f75401a9f5fa12d42961fe46b9ac8b","anchor":"### P-089 — Proposition 3"}],"result_type":"Prop","body":"- Prenex statement:\n  \\[\n  \\forall\\theta\\ge2\\;\\exists C_3(\\theta)>0\\;\n  \\forall y\\in(0,1)\\;\\forall k\\ge1\\;\\forall\\sigma\\ge\\theta\\;\n  \\forall x>\\theta^{2k-1},\n  \\]\n  \\[\n  \\sum_{n<x}f_k^\\#(y,n)\\le {C_3(\\theta)\\over y}\n  x(\\log\\sigma)^{-y}k^{(y-3)/2}\n  \\left\\{k^{(y-1)/2}\n  +\\ell(2x\\theta^{1-2k})^{(y-1)/2}\n  +{(\\log\\sigma)^{y/2}\\over\\ell(2x\\theta^{1-2k})^{1/2}}\\right\\}.\n  \\]\n- Local equalities: S is D-017.\n- Domain/range: the three cases below are disjoint/exhaustive. The numerator\n  \\(C_3(\\theta)\\) is selected after \\(\\theta\\) from \\(C_{\\rm reg}(\\theta)\\)\n  and \\(C_{\\rm tr}(\\theta)\\), and therefore carries the already scoped\n  \\(C_4(C_{\\rm fam},\\theta)\\) lineage but no dependence on \\(y,k,\\sigma,x\\).\n- Input subject: exact \\(S_k\\). Output: source Proposition-3 envelope."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"W-P-089-C_3","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"},{"key":"p_089_p_074_1_C_reg","type":"Real"},{"key":"p_089_p_087_2_C_tr","type":"Real"}],"uses_definitions":["D-006","D-017"],"source_anchors":[],"result_type":"Real","body":"The product of (1+C) over the supplied positive premise constants, enlarged as in the adjacent finite inequality assembly."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"S-P-090","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"},{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"},{"key":"n","type":"Nat"},{"key":"d","type":"Nat"},{"key":"d_prime","type":"Nat"},{"key":"t","type":"Nat"}],"uses_definitions":["D-002","D-003","D-005","D-013"],"source_anchors":[{"path":"stage3/canonical/CURRENT.md","git":"4279cd5e01f75401a9f5fa12d42961fe46b9ac8b","anchor":"### P-090 — finite-support witness from \\(f_k^\\#\\)"}],"result_type":"Prop","body":"- Prenex statement: for every \\(y\\in(0,1)\\), \\(k\\ge1\\),\n  \\(\\sigma\\ge\\theta\\ge2\\), and \\(n>0\\), if \\(f_k^\\#(y,n)>0\\), then there\n  exist \\(d,d',t>0\\) such that\n  \\[\n  dd't\\mid n,\\quad \\theta^k\\le d<\\theta^{k+1},\\quad\n  {\\rm Close}_\\theta(d,d'),\\quad\n  \\chi(d,\\sigma)y^{\\Omega(dt,\\theta^k)}\\chi(t,\\sigma)>0,\n  \\]\n  and\n  \\[\n  \\theta^{2k-1}<dd'\\le dd't\\le n.\n  \\]\n  Consequently, if \\(n<x\\), then \\(\\theta^{2k-1}<x\\).\n- Local equalities: the witnesses are an actual positive D-013 summand.\n- Domain/range: all integer products are positive and typed.\n- Input subject: exact D-013 \\(f_k^\\#\\). Output: support witness and chain."}
```

```mathminer-s3-legacy
{"schema":"mathminer.s3/1","id":"W-P-090-d","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"},{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"},{"key":"n","type":"Nat"}],"uses_definitions":["D-002","D-003","D-005","D-013"],"source_anchors":[],"result_type":"Nat","body":"The requested projection of the lexicographically least positive (d,d_prime,t) summand in the finite nonnegative D-013 sum."}
```

```mathminer-s3-legacy
{"schema":"mathminer.s3/1","id":"W-P-090-d_prime","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"},{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"},{"key":"n","type":"Nat"}],"uses_definitions":["D-002","D-003","D-005","D-013"],"source_anchors":[],"result_type":"Nat","body":"The requested projection of the lexicographically least positive (d,d_prime,t) summand in the finite nonnegative D-013 sum."}
```

```mathminer-s3-legacy
{"schema":"mathminer.s3/1","id":"W-P-090-t","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"},{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"},{"key":"n","type":"Nat"}],"uses_definitions":["D-002","D-003","D-005","D-013"],"source_anchors":[],"result_type":"Nat","body":"The requested projection of the lexicographically least positive (d,d_prime,t) summand in the finite nonnegative D-013 sum."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"S-P-091","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"},{"key":"x","type":"Real"},{"key":"k","type":"Int"}],"uses_definitions":["D-022"],"source_anchors":[{"path":"stage3/canonical/CURRENT.md","git":"4279cd5e01f75401a9f5fa12d42961fe46b9ac8b","anchor":"### P-091 — exact moving cutoff"}],"result_type":"Prop","body":"- Prenex statement: for every \\(\\theta\\ge2,x>0\\), put\n  \\(X=X_\\theta(x)\\), \\(N=N_\\theta(x)\\). For every integer \\(k\\),\n  \\[\n  \\theta^{2k-1}<x\\quad\\Longleftrightarrow\\quad k<X,\n  \\]\n  and\n  \\[\n  N<X\\le N+1,\\qquad k<X\\Longrightarrow k\\le N.\n  \\]\n- Local equalities:\n  \\(X=\\frac12(1+\\log x/\\log\\theta)\\), \\(N=\\lceil X\\rceil-1\\).\n- Domain/range: \\(N,k\\in\\mathbb Z\\).\n- Input subject: strict P3 support inequality. Output: exact integer cutoff."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"S-P-092","kind":"DEFINITION","binders":[{"key":"epsilon_int","type":"Real"},{"key":"xi","type":"Real"},{"key":"sigma","type":"Real"},{"key":"theta","type":"Real"},{"key":"y","type":"Real"},{"key":"x","type":"Real"}],"uses_definitions":["D-006","D-007","D-012","D-017","D-022"],"source_anchors":[{"path":"stage3/canonical/CURRENT.md","git":"4279cd5e01f75401a9f5fa12d42961fe46b9ac8b","anchor":"### P-092 — finite restriction of Proposition-2's infinite majorant"}],"result_type":"Prop","body":"- Prenex statement: for every\n  \\(\\varepsilon_{\\rm int}\\in(0,1/10]\\), \\(\\xi>1\\),\n  \\(\\sigma\\ge\\theta\\ge2\\), \\(y\\in(0,1)\\), \\(x>U_0\\), put\n  \\[\n  q=1/2+\\varepsilon_{\\rm int},\\quad\n  a_{\\rm pow}=-q\\log y,\\quad N=N_\\theta(x).\n  \\]\n  Then\n  \\[\n  \\sum_{U_0<n<x}f(n)\\le\n  (2\\log\\xi\\log\\theta/\\log\\sigma)^{a_{\\rm pow}}\n  \\sum_{K_0\\le k\\le N}k^{a_{\\rm pow}}S_k(x,y;\\sigma,\\theta).\n  \\]\n  If \\(N<K_0\\), the right sum is empty and the left side is \\(0\\).\n- Local equalities: exact \\(U_0,q,a_{\\rm pow},N,K_0,S_k\\).\n- Domain/range: finite k-sum; each retained k satisfies\n  \\(x>\\theta^{2k-1}\\).\n- Input subject: P-044 infinite pointwise majorant summed over \\(n\\).\n  Output subject: exact moving finite k-majorant."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"S-P-093","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"},{"key":"c_minus","type":"Real"},{"key":"c_plus","type":"Real"}],"uses_definitions":["D-006","D-022"],"source_anchors":[{"path":"stage3/canonical/CURRENT.md","git":"4279cd5e01f75401a9f5fa12d42961fe46b9ac8b","anchor":"### P-093 — exact logarithmic endpoint comparison"}],"result_type":"Prop","body":"- Prenex statement:\n  \\[\n  \\forall\\theta\\ge2\\;\\exists c_-(\\theta),c_+(\\theta)>0\\;\n  \\forall x>0\\;\\forall k\\in\\mathbb Z,\n  \\]\n  if \\(k\\le N_\\theta(x)\\), then, with \\(N=N_\\theta(x)\\),\n  \\[\n  \\log(2x\\theta^{1-2k})\n  =\\log2+2(X_\\theta(x)-k)\\log\\theta,\n  \\]\n  \\[\n  N-k<X_\\theta(x)-k\\le N-k+1,\n  \\]\n  and\n  \\[\n  c_-(\\theta)(N-k+1)\\le\n  \\ell(2x\\theta^{1-2k})\\le\n  c_+(\\theta)(N-k+1).\n  \\]\n- Local equalities: exact D-022 \\(X,N\\).\n- Domain/range: last cell \\(k=N\\) has \\(N-k+1=1\\); \\(\\ell\\ge1\\) prevents\n  endpoint degeneration.\n- Input subject: actual P3 logarithmic endpoint. Output: exact moving cell."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"W-P-093-c_plus","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"}],"uses_definitions":["D-006","D-022"],"source_anchors":[],"result_type":"Real","body":"log(2) + 2 log(theta), the explicit upper endpoint comparison coefficient."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"S-P-094","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"},{"key":"y","type":"Real"},{"key":"x","type":"Real"},{"key":"k","type":"Int"}],"uses_definitions":["D-006","D-022"],"source_anchors":[{"path":"stage3/canonical/CURRENT.md","git":"4279cd5e01f75401a9f5fa12d42961fe46b9ac8b","anchor":"### P-094 — negative-power adapter for \\(s=(y-1)/2\\)"}],"result_type":"Prop","body":"- Prenex statement: for every \\(\\theta\\ge2\\), choose the\n  \\(c_-(\\theta),c_+(\\theta)\\) of P-093. For every \\(y\\in(0,1)\\),\n  \\(x>0\\), and integer \\(k\\le N=N_\\theta(x)\\), put\n  \\(s=(y-1)/2<0\\). Then\n  \\[\n  c_+(\\theta)^s(N-k+1)^s\n  \\le\\ell(2x\\theta^{1-2k})^s\n  \\le c_-(\\theta)^s(N-k+1)^s.\n  \\]\n- Local equalities: \\(s=(y-1)/2\\).\n- Domain/range: both bases positive.\n- Input subject: P-093 comparison. Output: first exact power adapter."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"S-P-095","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"},{"key":"x","type":"Real"},{"key":"k","type":"Int"}],"uses_definitions":["D-006","D-022"],"source_anchors":[{"path":"stage3/canonical/CURRENT.md","git":"4279cd5e01f75401a9f5fa12d42961fe46b9ac8b","anchor":"### P-095 — negative-power adapter for \\(s=-1/2\\)"}],"result_type":"Prop","body":"- Prenex statement: for every \\(\\theta\\ge2\\), choose the P-093 constants.\n  For every \\(x>0\\) and integer \\(k\\le N=N_\\theta(x)\\),\n  \\[\n  c_+(\\theta)^{-1/2}(N-k+1)^{-1/2}\n  \\le\\ell(2x\\theta^{1-2k})^{-1/2}\n  \\le c_-(\\theta)^{-1/2}(N-k+1)^{-1/2}.\n  \\]\n- Local equalities: exponent exactly \\(-1/2\\).\n- Domain/range: positive bases; last cell safe.\n- Input subject: P-093 comparison. Output: second exact power adapter."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"S-P-096","kind":"DEFINITION","binders":[{"key":"y","type":"Real"},{"key":"epsilon_int","type":"Real"}],"uses_definitions":[],"source_anchors":[{"path":"stage3/canonical/CURRENT.md","git":"4279cd5e01f75401a9f5fa12d42961fe46b9ac8b","anchor":"### P-096 — convergence-condition normalization"}],"result_type":"Prop","body":"- Prenex statement: for every \\(y\\in(0,1)\\) and\n  \\(\\varepsilon_{\\rm int}>0\\), put\n  \\(a_{\\rm pow}=-(1/2+\\varepsilon_{\\rm int})\\log y\\). If\n  \\[\n  \\varepsilon_{\\rm int}<\n  -{1-y+\\tfrac12\\log y\\over\\log y},\n  \\]\n  then \\(0<a_{\\rm pow}<1-y\\).\n- Local equalities: exact \\(a_{\\rm pow}\\).\n- Domain/range: \\(\\log y<0\\).\n- Input subject: Proposition-4 condition. Output: exact power interval."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"S-P-097","kind":"DEFINITION","binders":[{"key":"y","type":"Real"},{"key":"a_pow","type":"Real"},{"key":"K_0","type":"Nat"}],"uses_definitions":["D-017"],"source_anchors":[{"path":"stage3/canonical/CURRENT.md","git":"4279cd5e01f75401a9f5fa12d42961fe46b9ac8b","anchor":"### P-097 — exact main power tail"}],"result_type":"Prop","body":"- Prenex statement: for every \\(y\\in(0,1)\\), every\n  \\(a_{\\rm pow}\\in(0,1-y)\\), every integer \\(K_0\\ge1\\),\n  \\[\n  \\sum_{k\\ge K_0}k^{y-2+a_{\\rm pow}}\n  \\le\\left(1+{1\\over1-y-a_{\\rm pow}}\\right)\n  K_0^{y-1+a_{\\rm pow}}.\n  \\]\n  If \\(K_0=K_0(\\sigma,\\theta)\\), \\(r_0=\\log\\sigma/\\log\\theta\\), then\n  \\(\\frac12r_0\\le K_0\\le\\frac32r_0\\).\n- Local equalities: exact D-017 K0 in the second clause.\n- Domain/range: exponent \\(y-2+a_{\\rm pow}<-1\\).\n- Input subject: main k-series. Output: exact lower-end tail."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"S-P-098","kind":"DEFINITION","binders":[{"key":"K_0","type":"Nat"},{"key":"y","type":"Real"},{"key":"a_pow","type":"Real"},{"key":"N","type":"Nat"}],"uses_definitions":[],"source_anchors":[{"path":"stage3/canonical/CURRENT.md","git":"4279cd5e01f75401a9f5fa12d42961fe46b9ac8b","anchor":"### P-098 — generic moving sum at \\(s=(y-1)/2\\)"}],"result_type":"Prop","body":"- Prenex statement: for every fixed integer \\(K_0\\ge1\\), every\n  \\(y\\in(0,1)\\), every \\(a_{\\rm pow}\\in(0,1-y)\\), put\n  \\(r=(y-3)/2+a_{\\rm pow}\\), \\(s=(y-1)/2\\). Then, as integer\n  \\(N\\to\\infty\\),\n  \\[\n  \\sum_{K_0\\le k\\le N}k^r(N-k+1)^s=o(1).\n  \\]\n- Local equalities: exact \\(r,s\\).\n- Domain/range: \\(s\\in(-1/2,0)\\).\n- Input subject: abstract moving power sum. Output: exact \\(o(1)\\)."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"S-P-099","kind":"DEFINITION","binders":[{"key":"K_0","type":"Nat"},{"key":"y","type":"Real"},{"key":"a_pow","type":"Real"},{"key":"N","type":"Nat"}],"uses_definitions":[],"source_anchors":[{"path":"stage3/canonical/CURRENT.md","git":"4279cd5e01f75401a9f5fa12d42961fe46b9ac8b","anchor":"### P-099 — generic moving sum at exponent \\(-1/2\\)"}],"result_type":"Prop","body":"- Prenex statement: for every fixed integer \\(K_0\\ge1\\), every\n  \\(y\\in(0,1)\\), every \\(a_{\\rm pow}\\in(0,1-y)\\), put\n  \\(r=(y-3)/2+a_{\\rm pow}\\). Then, as \\(N\\to\\infty\\),\n  \\[\n  \\sum_{K_0\\le k\\le N}k^r(N-k+1)^{-1/2}=o(1).\n  \\]\n- Local equalities: exact r.\n- Domain/range: \\(r+1/2=(y-2)/2+a_{\\rm pow}<0\\).\n- Input subject: abstract moving power sum. Output: exact \\(o(1)\\)."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"S-P-100","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"},{"key":"sigma","type":"Real"},{"key":"K_0","type":"Nat"},{"key":"y","type":"Real"},{"key":"a_pow","type":"Real"},{"key":"x","type":"Real"}],"uses_definitions":["D-006","D-017","D-022"],"source_anchors":[{"path":"stage3/canonical/CURRENT.md","git":"4279cd5e01f75401a9f5fa12d42961fe46b9ac8b","anchor":"### P-100 — exact weighted logarithmic sum, exponent \\((y-1)/2\\)"}],"result_type":"Prop","body":"- Prenex statement: for every fixed \\(\\theta\\ge2,\\sigma\\ge\\theta\\),\n  fixed \\(K_0=K_0(\\sigma,\\theta)\\), every \\(y\\in(0,1)\\), and\n  \\(a_{\\rm pow}\\in(0,1-y)\\), put\n  \\(r=(y-3)/2+a_{\\rm pow}\\), \\(N=N_\\theta(x)\\). As \\(x\\to\\infty\\),\n  \\[\n  \\sum_{K_0\\le k\\le N}k^r\n  \\ell(2x\\theta^{1-2k})^{(y-1)/2}=o(1).\n  \\]\n- Local equalities: exact \\(r,N,K_0\\).\n- Domain/range: \\(N\\to\\infty\\) as \\(x\\to\\infty\\).\n- Input subject: actual P3 second logarithmic sum. Output: exact \\(o(1)\\)."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"S-P-101","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"},{"key":"sigma","type":"Real"},{"key":"K_0","type":"Nat"},{"key":"y","type":"Real"},{"key":"a_pow","type":"Real"},{"key":"x","type":"Real"}],"uses_definitions":["D-006","D-017","D-022"],"source_anchors":[{"path":"stage3/canonical/CURRENT.md","git":"4279cd5e01f75401a9f5fa12d42961fe46b9ac8b","anchor":"### P-101 — exact weighted logarithmic sum, exponent \\(-1/2\\)"}],"result_type":"Prop","body":"- Prenex statement: for every fixed \\(\\theta\\ge2,\\sigma\\ge\\theta\\),\n  fixed \\(K_0=K_0(\\sigma,\\theta)\\), every \\(y\\in(0,1)\\), and every\n  \\(a_{\\rm pow}\\in(0,1-y)\\), with \\(r=(y-3)/2+a_{\\rm pow}\\) and\n  \\(N=N_\\theta(x)\\), as \\(x\\to\\infty\\),\n  \\[\n  \\sum_{K_0\\le k\\le N}k^r\n  \\ell(2x\\theta^{1-2k})^{-1/2}=o(1).\n  \\]\n- Local equalities: exact \\(r,N,K_0\\).\n- Domain/range: \\(N\\to\\infty\\).\n- Input subject: actual P3 terminal logarithmic sum. Output: exact \\(o(1)\\)."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"S-P-102","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"},{"key":"y","type":"Real"},{"key":"epsilon_int","type":"Real"},{"key":"C_P4","type":"Real"}],"uses_definitions":["D-006","D-007","D-012","D-017","D-022"],"source_anchors":[{"path":"stage3/canonical/CURRENT.md","git":"4279cd5e01f75401a9f5fa12d42961fe46b9ac8b","anchor":"### P-102 — Proposition 4"}],"result_type":"Prop","body":"- Prenex statement:\n  \\[\n  \\forall\\theta\\ge2\\;\\forall y\\in(0,1)\\;\n  \\forall\\varepsilon_{\\rm int}\\in(0,1/10],\n  \\]\n  if\n  \\[\n  \\varepsilon_{\\rm int}<\n  -{1-y+\\tfrac12\\log y\\over\\log y},\n  \\]\n  then there exists \\(C_{\\rm P4}(\\theta,y,\\varepsilon_{\\rm int})>0\\) such\n  that for every \\(\\sigma\\ge\\theta\\) and every \\(\\xi>1\\), there exists a\n  remainder witness\n  \\(r_{\\theta,y,\\varepsilon_{\\rm int},\\sigma,\\xi}(x)\\) satisfying\n  \\(r_{\\theta,y,\\varepsilon_{\\rm int},\\sigma,\\xi}(x)=o(x)\\), and, as\n  \\(x\\to\\infty\\),\n  \\[\n  \\sum_{n<x}f(n)\\le\n  C_{\\rm P4}(\\theta,y,\\varepsilon_{\\rm int})\n  x(\\log\\xi)^{-((1/2)+\\varepsilon_{\\rm int})\\log y}\n  (\\log\\sigma)^{-1}\n  +r_{\\theta,y,\\varepsilon_{\\rm int},\\sigma,\\xi}(x).\n  \\]\n- Local equalities:\n  \\(a_{\\rm pow}=-((1/2)+\\varepsilon_{\\rm int})\\log y\\),\n  \\(N=N_\\theta(x)\\), \\(K_0=K_0(\\sigma,\\theta)\\).\n- Domain/range and exact dependency order:\n  \\[\n  (\\theta,y,\\varepsilon_{\\rm int}\\text{ admissible})\n  \\longmapsto C_{\\rm P4}>0\n  \\longmapsto(\\sigma\\ge\\theta,\\xi>1)\n  \\longmapsto r_{\\theta,y,\\varepsilon_{\\rm int},\\sigma,\\xi}\n  \\longmapsto x\\to\\infty.\n  \\tag{P102-order}\n  \\]\n  Thus the main coefficient is common to all \\(\\sigma,\\xi\\), whereas the\n  little-o witness is only pointwise for each fixed \\((\\sigma,\\xi)\\).  The\n  \\(n\\le U_0\\) sum is finite after that pair is fixed.\n- Input subject: exact P-092 finite k-majorant.\n  Output subject: exact Proposition-4 mean."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"W-P-102-C_P4","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"},{"key":"y","type":"Real"},{"key":"epsilon_int","type":"Real"},{"key":"p_102_p_089_2_C_3","type":"Real"}],"uses_definitions":["D-006","D-007","D-012","D-017","D-022"],"source_anchors":[],"result_type":"Real","body":"The product of (1+C) over the supplied positive premise constants, enlarged as in the adjacent finite inequality assembly."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"S-P-110","kind":"DEFINITION","binders":[{"key":"n","type":"Nat"}],"uses_definitions":["D-001","D-002","D-004","D-006"],"source_anchors":[{"path":"stage3/canonical/CURRENT.md","git":"4279cd5e01f75401a9f5fa12d42961fe46b9ac8b","anchor":"### P-110 — specialization at \\(\\sigma=\\theta=2\\)"}],"result_type":"Prop","body":"- Prenex statement: for every \\(n>0\\),\n  \\[\n  \\chi(n,2)=1,\\qquad\\tau(n,2)=\\tau(n),\\qquad\n  \\tau^+(n,2)=\\tau^+(n),\\qquad\\rho_2=1.\n  \\]\n- Local equalities: the product defining \\(\\rho_2\\) is empty.\n- Domain/range: positive integers.\n- Input subject: D-001/D-002/D-004/D-006 at 2. Output: exact equalities."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"S-P-111","kind":"DEFINITION","binders":[{"key":"epsilon_int","type":"Real"},{"key":"xi","type":"Real"},{"key":"n","type":"Nat"},{"key":"alpha","type":"Real"}],"uses_definitions":["D-001","D-004","D-006","D-010","D-012"],"source_anchors":[{"path":"stage3/canonical/CURRENT.md","git":"4279cd5e01f75401a9f5fa12d42961fe46b9ac8b","anchor":"### P-111 — small ratio forces large \\(f\\)"}],"result_type":"Prop","body":"- Prenex statement: for every\n  \\(\\varepsilon_{\\rm int}\\in(0,1/10]\\), \\(\\xi>1\\),\n  every \\(\\mathcal A\\) with\n  L4Spec\\((\\varepsilon_{\\rm int},\\xi,2,2,\\mathcal A)\\), every\n  \\(n\\in\\mathcal A\\), and every \\(\\alpha\\in(0,2/5]\\), if\n  \\(\\tau^+(n)\\le\\alpha\\tau(n)\\), then\n  \\[\n  f(n)\\ge {4\\over5\\alpha}-1\\ge {2\\over5\\alpha}.\n  \\]\n- Local equalities: \\(\\sigma=\\theta=2\\).\n- Domain/range: \\(\\tau,\\tau^+>0\\).\n- Input subject: exact event \\(n\\in E_\\alpha\\cap\\mathcal A\\).\n  Output subject: pointwise lower bound on f."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"S-P-112","kind":"DEFINITION","binders":[{"key":"epsilon_int","type":"Real"},{"key":"y","type":"Real"},{"key":"C_grid","type":"Real"},{"key":"Xi_0","type":"Real"},{"key":"C_P4","type":"Real"},{"key":"C_den","type":"Real"}],"uses_definitions":["D-006","D-022"],"source_anchors":[{"path":"stage3/canonical/CURRENT.md","git":"4279cd5e01f75401a9f5fa12d42961fe46b9ac8b","anchor":"### P-112 — threshold-parametric density bound"}],"result_type":"Prop","body":"- Prenex statement: for every\n  \\(\\varepsilon_{\\rm int}\\in(0,1/10]\\) and every \\(y\\in(0,1)\\) satisfying\n  \\[\n  \\varepsilon_{\\rm int}<\n  -{1-y+\\tfrac12\\log y\\over\\log y},\n  \\]\n  there exist \\(C_{\\rm grid}>0,\\Xi_0>1\\), the single specialized coefficient\n  \\(C_{\\rm P4}(2,y,\\varepsilon_{\\rm int})>0\\), and \\(C_{\\rm den}>0\\), all\n  selected before every\n  \\(\\xi\\ge\\Xi_0\\) and every \\(\\alpha\\in(0,2/5]\\), putting\n  \\[\n  a_{\\rm bal}=-((1/2)+\\varepsilon_{\\rm int})\\log y,\\qquad\n  b_{\\rm bal}=(9/10)\\varepsilon_{\\rm int}^2,\n  \\]\n  \\[\n  \\bar d(E_\\alpha)\\le C_{\\rm den}\n  \\{\\alpha(\\log\\xi)^{a_{\\rm bal}}+(\\log\\xi)^{-b_{\\rm bal}}\\}.\n  \\]\n- Local equalities: exact \\(a_{\\rm bal},b_{\\rm bal}\\).\n- Domain/range: after fixed \\((\\varepsilon_{\\rm int},y)\\), first select\n  \\(C_{\\rm grid},\\Xi_0\\) from P-020 and the one P-102 main coefficient at\n  \\(\\theta=\\sigma=2\\), then absorb these into \\(C_{\\rm den}\\); all four\n  witnesses precede uniform \\((\\xi,\\alpha)\\).  The P-102 remainder remains\n  pointwise in each fixed \\(\\xi\\), exactly as required before taking the\n  density limsup.\n- Input subject: exact event \\(E_\\alpha\\). Output: two-term density bound."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"W-P-112-C_den","kind":"DEFINITION","binders":[{"key":"epsilon_int","type":"Real"},{"key":"y","type":"Real"},{"key":"p_112_p_020_1_C_grid","type":"Real"},{"key":"p_112_p_020_1_Xi_0","type":"Real"},{"key":"p_112_p_102_2_C_P4","type":"Real"}],"uses_definitions":["D-006","D-022"],"source_anchors":[],"result_type":"Real","body":"The product of (1+C) over the supplied positive premise constants, enlarged as in the adjacent finite inequality assembly."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"S-P-113","kind":"DEFINITION","binders":[{"key":"delta","type":"Real"},{"key":"y_delta","type":"Real"}],"uses_definitions":[],"source_anchors":[{"path":"stage3/canonical/CURRENT.md","git":"4279cd5e01f75401a9f5fa12d42961fe46b9ac8b","anchor":"### P-113 — admissible parameter selection"}],"result_type":"Prop","body":"- Prenex statement:\n  \\[\n  \\forall\\delta\\in(0,1)\\;\\exists y\\in(0,1):\n  \\]\n  \\[\n  {1\\over10}<\n  -{1-y+\\tfrac12\\log y\\over\\log y}\n  \\quad\\land\\quad\n  {0.009\\over0.009-0.6\\log y}\\ge1-\\delta.\n  \\]\n- Local equalities:\n  \\(a_{\\rm bal}=-0.6\\log y\\), \\(b_{\\rm bal}=0.009\\).\n- Domain/range: y is selected after delta and before every alpha.\n- Input subject: desired exponent loss. Output: exact admissible y."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"W-P-113-y_delta","kind":"DEFINITION","binders":[{"key":"delta","type":"Real"}],"uses_definitions":[],"source_anchors":[],"result_type":"Real","body":"exp(-3 delta/400), which satisfies both displayed P-113 inequalities by 1-exp(-L)>=L-L^2/2."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"S-P-114","kind":"DEFINITION","binders":[{"key":"y","type":"Real"},{"key":"alpha","type":"Real"}],"uses_definitions":[],"source_anchors":[{"path":"stage3/canonical/CURRENT.md","git":"4279cd5e01f75401a9f5fa12d42961fe46b9ac8b","anchor":"### P-114 — balance identity with all defining equations"}],"result_type":"Prop","body":"- Prenex statement: for every \\(y\\in(0,1)\\), every \\(\\alpha\\in(0,1)\\), put\n  \\[\n  a_{\\rm bal}=-0.6\\log y,\\qquad b_{\\rm bal}=0.009,\\qquad\n  L=\\alpha^{-1/(a_{\\rm bal}+b_{\\rm bal})},\\qquad\n  \\log\\xi=L.\n  \\]\n  Then\n  \\[\n  \\alpha L^{a_{\\rm bal}}=L^{-b_{\\rm bal}}\n  =\\alpha^{b_{\\rm bal}/(a_{\\rm bal}+b_{\\rm bal})},\n  \\quad\n  {b_{\\rm bal}\\over a_{\\rm bal}+b_{\\rm bal}}\n  ={0.009\\over0.009-0.6\\log y}.\n  \\]\n- Local equalities: all four equations appear in the prefix.\n- Domain/range: \\(a_{\\rm bal},b_{\\rm bal},L>0\\).\n- Input subject: two terms in P-112. Output: exact common balanced power."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"S-P-115","kind":"DEFINITION","binders":[{"key":"delta","type":"Real"},{"key":"y","type":"Real"},{"key":"C_grid","type":"Real"},{"key":"Xi_0","type":"Real"},{"key":"C_P4","type":"Real"},{"key":"C_den","type":"Real"},{"key":"alpha_0","type":"Real"},{"key":"C_small","type":"Real"}],"uses_definitions":["D-006","D-022"],"source_anchors":[{"path":"stage3/canonical/CURRENT.md","git":"4279cd5e01f75401a9f5fa12d42961fe46b9ac8b","anchor":"### P-115 — optimized small-\\(\\alpha\\) density"}],"result_type":"Prop","body":"- Prenex statement: for every \\(\\delta\\in(0,1)\\), every \\(y\\in(0,1)\\)\n  satisfying both conclusions of P-113, put\n  \\(a_{\\rm bal}=-0.6\\log y\\), \\(b_{\\rm bal}=0.009\\). Then there exist\n  \\[\n  C_{\\rm grid}>0,\\quad\\Xi_0>1,\\quad\n  C_{\\rm P4}(2,y,1/10)>0,\\quad C_{\\rm den}>0,\\quad\n  \\alpha_0\\in(0,2/5],\\quad C_{\\rm small}>0\n  \\]\n  such that for every \\(\\alpha\\in(0,\\alpha_0)\\), putting\n  \\[\n  L=\\alpha^{-1/(a_{\\rm bal}+b_{\\rm bal})},\\qquad\n  \\log\\xi=L,\n  \\]\n  one has \\(\\xi\\ge\\Xi_0\\) and\n  \\[\n  \\bar d(E_\\alpha)\\le C_{\\rm small}\\alpha^{1-\\delta}.\n  \\]\n- Local equalities: exact \\(a_{\\rm bal},b_{\\rm bal},L,\\xi\\).\n- Domain/range: after fixed \\((\\delta,y)\\), the P-112 witnesses occur in the\n  exact order\n  \\((C_{\\rm grid},\\Xi_0,C_{\\rm P4},C_{\\rm den})\\), then\n  \\((\\alpha_0,C_{\\rm small})\\); all are selected before uniform alpha.\n- Input subject: P-112 two-term bound. Output: small-alpha power bound."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"W-P-115-alpha_0","kind":"DEFINITION","binders":[{"key":"delta","type":"Real"},{"key":"y","type":"Real"},{"key":"p_115_p_112_1_C_grid","type":"Real"},{"key":"p_115_p_112_1_Xi_0","type":"Real"},{"key":"p_115_p_112_1_C_P4","type":"Real"},{"key":"p_115_p_112_1_C_den","type":"Real"}],"uses_definitions":["D-006","D-022"],"source_anchors":[],"result_type":"Real","body":"One half of min(2/5,1/2,(log Xi_0)^(-(a_bal+b_bal))), with Xi_0 the mapped P-112 threshold."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"W-P-115-C_small","kind":"DEFINITION","binders":[{"key":"delta","type":"Real"},{"key":"y","type":"Real"},{"key":"p_115_p_112_1_C_grid","type":"Real"},{"key":"p_115_p_112_1_Xi_0","type":"Real"},{"key":"p_115_p_112_1_C_P4","type":"Real"},{"key":"p_115_p_112_1_C_den","type":"Real"}],"uses_definitions":["D-006","D-022"],"source_anchors":[],"result_type":"Real","body":"2*C_den, because P-114 balances the two P-112 terms and P-113 gives the exponent monotonicity."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"S-P-116","kind":"DEFINITION","binders":[{"key":"delta","type":"Real"},{"key":"alpha_0","type":"Real"},{"key":"alpha","type":"Real"}],"uses_definitions":["D-006","D-022"],"source_anchors":[{"path":"stage3/canonical/CURRENT.md","git":"4279cd5e01f75401a9f5fa12d42961fe46b9ac8b","anchor":"### P-116 — compact alpha completion"}],"result_type":"Prop","body":"- Prenex statement: for every \\(\\delta\\in(0,1)\\), every\n  \\(\\alpha_0\\in(0,1]\\), and every \\(\\alpha\\in[\\alpha_0,1]\\),\n  \\[\n  \\bar d(E_\\alpha)\\le1\n  \\le\\alpha_0^{-(1-\\delta)}\\alpha^{1-\\delta}.\n  \\]\n- Local equalities: none.\n- Domain/range: exact closed alpha interval.\n- Input subject: E-event. Output: uniform compact-range bound."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"S-P-117","kind":"DEFINITION","binders":[{"key":"delta","type":"Real"},{"key":"C_delta","type":"Real"}],"uses_definitions":["D-006","D-022"],"source_anchors":[{"path":"stage3/canonical/CURRENT.md","git":"4279cd5e01f75401a9f5fa12d42961fe46b9ac8b","anchor":"### P-117 — Theorem 1, interior, with uniform constant order"}],"result_type":"Prop","body":"- Prenex statement:\n  \\[\n  \\forall\\delta\\in(0,1)\\;\\exists C_\\delta>0\\;\n  \\forall\\alpha\\in(0,1],\\quad\n  \\bar d(E_\\alpha)\\le C_\\delta\\alpha^{1-\\delta}.\n  \\]\n- Local equalities:\n  choose \\(y\\) from P-113; choose the P-115\n  \\(C_{\\rm grid},\\Xi_0,C_{\\rm P4},C_{\\rm den},\\alpha_0,C_{\\rm small}\\) in\n  that order; set\n  \\(C_\\delta=\\max(C_{\\rm small},\\alpha_0^{-(1-\\delta)})\\).\n- Domain/range: \\(C_\\delta\\) is chosen before every alpha and is uniform in it.\n- Input subject: exact E-event. Output: source-faithful interior theorem."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"W-P-117-C_delta","kind":"DEFINITION","binders":[{"key":"delta","type":"Real"},{"key":"p_117_p_113_1_y_delta","type":"Real"},{"key":"p_117_p_115_2_C_grid","type":"Real"},{"key":"p_117_p_115_2_Xi_0","type":"Real"},{"key":"p_117_p_115_2_C_P4","type":"Real"},{"key":"p_117_p_115_2_C_den","type":"Real"},{"key":"p_117_p_115_2_alpha_0","type":"Real"},{"key":"p_117_p_115_2_C_small","type":"Real"}],"uses_definitions":["D-006","D-022"],"source_anchors":[],"result_type":"Real","body":"C_small + alpha_0^(-(1-delta)), dominating both exhaustive alpha-range coefficients."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"S-P-118","kind":"DEFINITION","binders":[{"key":"n","type":"Nat"}],"uses_definitions":["D-001","D-004","D-006","D-022"],"source_anchors":[{"path":"stage3/canonical/CURRENT.md","git":"4279cd5e01f75401a9f5fa12d42961fe46b9ac8b","anchor":"### P-118 — zero-alpha endpoint"}],"result_type":"Prop","body":"- Prenex statement: for every \\(n>0\\), \\(\\tau^+(n)\\ge1\\), hence\n  \\(E_0=\\varnothing\\) and \\(\\bar d(E_0)=0\\).\n- Local equalities: \\(1\\mid n\\) lies in \\([1,2)\\).\n- Domain/range: exact endpoint.\n- Input subject: E0. Output: empty set and density zero."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"S-P-119","kind":"DEFINITION","binders":[{"key":"delta","type":"Real"},{"key":"alpha","type":"Real"}],"uses_definitions":["D-006","D-022"],"source_anchors":[{"path":"stage3/canonical/CURRENT.md","git":"4279cd5e01f75401a9f5fa12d42961fe46b9ac8b","anchor":"### P-119 — large-loss endpoint"}],"result_type":"Prop","body":"- Prenex statement: for every \\(\\delta\\ge1\\) and\n  \\(\\alpha\\in(0,1]\\),\n  \\[\n  \\bar d(E_\\alpha)\\le1\\le\\alpha^{1-\\delta}.\n  \\]\n- Local equalities: none.\n- Domain/range: no expression \\(0^{1-\\delta}\\) is formed.\n- Input subject: E-event. Output: endpoint theorem with constant 1."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"S-P-120","kind":"DEFINITION","binders":[{"key":"delta","type":"Real"},{"key":"C_delta","type":"Real"},{"key":"alpha","type":"Real"}],"uses_definitions":["D-001","D-004","D-006","D-022"],"source_anchors":[{"path":"stage3/canonical/CURRENT.md","git":"4279cd5e01f75401a9f5fa12d42961fe46b9ac8b","anchor":"### P-120 — strict event is not density one"}],"result_type":"Prop","body":"- Prenex statement: there exist\n  \\[\n  \\delta\\in(0,1),\\quad C_\\delta>0,\\quad\n  \\alpha\\in\\bigl(0,\\min(1,C_\\delta^{-1/(1-\\delta)})\\bigr)\n  \\]\n  such that\n  \\[\n  \\bar d\\{n>0:\\tau^+(n)<\\alpha\\tau(n)\\}<1.\n  \\]\n- Local equalities: first choose, for example, \\(\\delta=1/2\\); next eliminate\n  P-113's \\(y\\), P-115's pre-alpha coefficient/threshold witnesses, and then\n  \\(C_\\delta\\) from P-117; only afterward choose alpha from the displayed\n  open interval.\n- Domain/range: the interval is nonempty because \\(C_\\delta>0\\).\n- Input subject: strict event. Output: strict upper-density bound."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"W-P-120-alpha","kind":"DEFINITION","binders":[{"key":"p_120_p_117_1_C_delta","type":"Real"}],"uses_definitions":["D-001","D-004","D-006","D-022"],"source_anchors":[],"result_type":"Real","body":"1/(2*(1+C_delta)^2), positive and strictly below min(1,C_delta^-2) at delta=1/2."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"S-FT-448-NEG-017","kind":"DEFINITION","binders":[{"key":"alpha","type":"Real"}],"uses_definitions":["D-001","D-004","D-006"],"source_anchors":[{"path":"stage3/canonical/CURRENT.md","git":"4279cd5e01f75401a9f5fa12d42961fe46b9ac8b","anchor":"### FT-448-NEG-017 — literal negative answer"}],"result_type":"Prop","body":"- Prenex statement: no binders; the assertion\n  \\[\n  \\forall\\varepsilon>0,\\quad\n  \\tau^+(n)<\\varepsilon\\tau(n)\\ {\\rm for\\ almost\\ all}\\ n\n  \\]\n  is false.\n- Local equalities: instantiate its \\(\\varepsilon\\) by the positive alpha\n  selected in P-120.\n- Domain/range: “almost all” means natural density one.\n- Input subject: exact universal question in PROBLEM.md.\n  Output subject: its logical negation."}
```

```mathminer-s3-legacy
{"schema":"mathminer.s3/1","id":"D-S811-CSTAR","kind":"DEFINITION","binders":[],"uses_definitions":[],"source_anchors":[],"result_type":"Real","body":"The canonical positive family-uniform c_* selected by P-051G from the five fixed weight constructions."}
```

```mathminer-s3-legacy
{"schema":"mathminer.s3/1","id":"D-S811-CERR","kind":"DEFINITION","binders":[],"uses_definitions":["D-S811-CSTAR","D-S811-LAMBDASTAR"],"source_anchors":[],"result_type":"Real","body":"The canonical positive common Euler-error constant C_*+2 Lambda_* supplied by P-051G and P-051H."}
```

```mathminer-s3-legacy
{"schema":"mathminer.s3/1","id":"D-S811-LAMBDASTAR","kind":"DEFINITION","binders":[],"uses_definitions":[],"source_anchors":[],"result_type":"Real","body":"The canonical positive common prime-power bound Lambda_* selected by P-051G."}
```

```mathminer-s3-legacy
{"schema":"mathminer.s3/1","id":"D-S811-ETA","kind":"DEFINITION","binders":[],"uses_definitions":["D-S811-CSTAR"],"source_anchors":[],"result_type":"Real","body":"min(D-S811-CSTAR,1), positive and uniform over every late family."}
```

```mathminer-s3-legacy
{"schema":"mathminer.s3/1","id":"D-S811-LAMBDA-SEQ","kind":"DEFINITION","binders":[],"uses_definitions":["D-S811-LAMBDASTAR"],"source_anchors":[],"result_type":{"fn":{"args":["Nat"],"return":"Real"}},"body":"The constant sequence i maps to D-S811-LAMBDASTAR."}
```

```mathminer-s3-legacy
{"schema":"mathminer.s3/1","id":"D-S811-THETA-SUCC","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"},{"key":"k","type":"Nat"}],"uses_definitions":[],"source_anchors":[],"result_type":"Real","body":"The exact real power theta^(k+1)."}
```

```mathminer-s3-legacy
{"schema":"mathminer.s3/1","id":"D-S811-P058-G","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"},{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"},{"key":"d_prime","type":"Nat"}],"uses_definitions":["D-015"],"source_anchors":[],"result_type":{"fn":{"args":["Nat"],"return":"Real"}},"body":"d maps to w_{3,k}(d d') v_k(d), the exact nonnegative initial-segment summand."}
```

```mathminer-s3-legacy
{"schema":"mathminer.s3/1","id":"D-S811-P020-FIXED-W","kind":"DEFINITION","binders":[{"key":"epsilon_int","type":"Real"}],"uses_definitions":["D-LATE-P020-W"],"source_anchors":[],"result_type":{"tuple":["Real","Real"]},"body":"The first two components C_grid and Xi_0 of D-LATE-P020-W at xi=sigma=theta=2; their P-020 witness dependencies are only epsilon_int, so this pair is selected before every live xi."}
```

```mathminer-s3-legacy
{"schema":"mathminer.s3/1","id":"D-S811-P068-ADM","kind":"DEFINITION","binders":[],"uses_definitions":["S-P-068"],"source_anchors":[],"result_type":{"set":"Real"},"body":"The nonempty set of positive absolute constants for which the full S-P-068 inequality holds; nonemptiness is proved by the P-068 beta-integral derivation."}
```

```mathminer-s3-legacy
{"schema":"mathminer.s3/1","id":"D-S811-P068-CHOOSE","kind":"DEFINITION","binders":[],"uses_definitions":["D-S811-P068-ADM"],"source_anchors":[],"result_type":"Real","body":"The canonical classical choice from D-S811-P068-ADM."}
```

```mathminer-s3-legacy
{"schema":"mathminer.s3/1","id":"D-S811-P069-ADM","kind":"DEFINITION","binders":[],"uses_definitions":["S-P-069"],"source_anchors":[],"result_type":{"set":"Real"},"body":"The nonempty set of positive absolute constants for which both S-P-069 inequalities hold; nonemptiness is proved by the R3.2--R3.5 derivation."}
```

```mathminer-s3-legacy
{"schema":"mathminer.s3/1","id":"D-S811-P069-CHOOSE","kind":"DEFINITION","binders":[],"uses_definitions":["D-S811-P069-ADM"],"source_anchors":[],"result_type":"Real","body":"The canonical classical choice from D-S811-P069-ADM."}
```

```mathminer-s3-legacy
{"schema":"mathminer.s3/1","id":"D-S811-P077-W","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"}],"uses_definitions":[],"source_anchors":[],"result_type":"Real","body":"The positive theta-uniform transition-high constant assembled from the exact P-005, P-007 and P-008 family applications."}
```

```mathminer-s3-legacy
{"schema":"mathminer.s3/1","id":"D-S811-P084-W","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"}],"uses_definitions":[],"source_anchors":[],"result_type":"Real","body":"The positive theta-uniform transition-outer constant assembled from the exact P-005, P-007 and P-008 family applications."}
```

```mathminer-s3
{"schema":"mathminer.s3/1","id":"D-LATE-P090-EXISTS","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"},{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"},{"key":"n","type":"Nat"}],"uses_definitions":["S-P-090"],"source_anchors":[],"result_type":"Prop","body":"There exist the selected d,d',t of P-090 satisfying its exact finite-support conclusion."}
```

```mathminer-s3-legacy
{"schema":"mathminer.s3/1","id":"D-S811-P055-Q","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"}],"uses_definitions":[],"source_anchors":[],"result_type":"Type","body":"The nonempty exact endpoint-index type for the P055 family."}
```

```mathminer-s3-legacy
{"schema":"mathminer.s3/1","id":"D-S811-P055-C-0","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"}],"uses_definitions":["D-S811-P055-Q"],"source_anchors":[],"result_type":{"fn":{"args":[{"named":{"id":"D-S811-P055-Q","args":[{"var":"theta"}]}}],"return":"Real"}},"body":"The exact P055 coefficient map q maps to 0."}
```

```mathminer-s3-legacy
{"schema":"mathminer.s3/1","id":"D-S811-P055-L-0","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"},{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"}],"uses_definitions":["D-S811-P055-Q","D-S811-P055-C-0","D-015"],"source_anchors":[],"result_type":{"fn":{"args":[{"named":{"id":"D-S811-P055-Q","args":[{"var":"theta"}]}},"Nat"],"return":"Real"}},"body":"The exact global positive Euler family: D-015 factor on [2,sigma) and 1+c(q)/p outside."}
```

```mathminer-s3-legacy
{"schema":"mathminer.s3/1","id":"D-S811-P055-POINT-0","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"},{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"},{"key":"z","type":"Real"}],"uses_definitions":["D-015"],"source_anchors":[],"result_type":{"fn":{"args":["Nat"],"return":"Real"}},"body":"The pointwise global positive Euler family: exact on [2,sigma) and exact model outside."}
```

```mathminer-s3-legacy
{"schema":"mathminer.s3/1","id":"D-S811-P055-C-MID","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"},{"key":"y","type":"Real"}],"uses_definitions":["D-S811-P055-Q"],"source_anchors":[],"result_type":{"fn":{"args":[{"named":{"id":"D-S811-P055-Q","args":[{"var":"theta"}]}}],"return":"Real"}},"body":"The exact P055 coefficient map q maps to y/2."}
```

```mathminer-s3-legacy
{"schema":"mathminer.s3/1","id":"D-S811-P055-L-MID","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"},{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"}],"uses_definitions":["D-S811-P055-Q","D-S811-P055-C-MID","D-015"],"source_anchors":[],"result_type":{"fn":{"args":[{"named":{"id":"D-S811-P055-Q","args":[{"var":"theta"}]}},"Nat"],"return":"Real"}},"body":"The exact global positive Euler family: D-015 factor on [sigma,theta^k) and 1+c(q)/p outside."}
```

```mathminer-s3-legacy
{"schema":"mathminer.s3/1","id":"D-S811-P055-POINT-MID","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"},{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"},{"key":"z","type":"Real"}],"uses_definitions":["D-015"],"source_anchors":[],"result_type":{"fn":{"args":["Nat"],"return":"Real"}},"body":"The pointwise global positive Euler family: exact on [sigma,theta^k) and exact model outside."}
```

```mathminer-s3-legacy
{"schema":"mathminer.s3/1","id":"D-S811-P055-C-HI","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"}],"uses_definitions":["D-S811-P055-Q"],"source_anchors":[],"result_type":{"fn":{"args":[{"named":{"id":"D-S811-P055-Q","args":[{"var":"theta"}]}}],"return":"Real"}},"body":"The exact P055 coefficient map q maps to 1/2."}
```

```mathminer-s3-legacy
{"schema":"mathminer.s3/1","id":"D-S811-P055-L-HI","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"},{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"},{"key":"z","type":"Real"}],"uses_definitions":["D-S811-P055-Q","D-S811-P055-C-HI","D-015"],"source_anchors":[],"result_type":{"fn":{"args":[{"named":{"id":"D-S811-P055-Q","args":[{"var":"theta"}]}},"Nat"],"return":"Real"}},"body":"The exact global positive Euler family: D-015 factor on [theta^k,z) and 1+c(q)/p outside."}
```

```mathminer-s3-legacy
{"schema":"mathminer.s3/1","id":"D-S811-P055-POINT-HI","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"},{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"},{"key":"z","type":"Real"}],"uses_definitions":["D-015"],"source_anchors":[],"result_type":{"fn":{"args":["Nat"],"return":"Real"}},"body":"The pointwise global positive Euler family: exact on [theta^k,z) and exact model outside."}
```

```mathminer-s3-legacy
{"schema":"mathminer.s3/1","id":"D-S811-P056-Q","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"}],"uses_definitions":[],"source_anchors":[],"result_type":"Type","body":"The nonempty exact endpoint-index type for the P056 family."}
```

```mathminer-s3-legacy
{"schema":"mathminer.s3/1","id":"D-S811-P056-C-0","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"}],"uses_definitions":["D-S811-P056-Q"],"source_anchors":[],"result_type":{"fn":{"args":[{"named":{"id":"D-S811-P056-Q","args":[{"var":"theta"}]}}],"return":"Real"}},"body":"The exact P056 coefficient map q maps to 0."}
```

```mathminer-s3-legacy
{"schema":"mathminer.s3/1","id":"D-S811-P056-L-0","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"},{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"}],"uses_definitions":["D-S811-P056-Q","D-S811-P056-C-0","D-015"],"source_anchors":[],"result_type":{"fn":{"args":[{"named":{"id":"D-S811-P056-Q","args":[{"var":"theta"}]}},"Nat"],"return":"Real"}},"body":"The exact global positive Euler family: D-015 factor on [2,sigma) and 1+c(q)/p outside."}
```

```mathminer-s3-legacy
{"schema":"mathminer.s3/1","id":"D-S811-P056-POINT-0","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"},{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"},{"key":"z","type":"Real"}],"uses_definitions":["D-015"],"source_anchors":[],"result_type":{"fn":{"args":["Nat"],"return":"Real"}},"body":"The pointwise global positive Euler family: exact on [2,sigma) and exact model outside."}
```

```mathminer-s3-legacy
{"schema":"mathminer.s3/1","id":"D-S811-P056-C-ACT","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"},{"key":"y","type":"Real"}],"uses_definitions":["D-S811-P056-Q"],"source_anchors":[],"result_type":{"fn":{"args":[{"named":{"id":"D-S811-P056-Q","args":[{"var":"theta"}]}}],"return":"Real"}},"body":"The exact P056 coefficient map q maps to y/2."}
```

```mathminer-s3-legacy
{"schema":"mathminer.s3/1","id":"D-S811-P056-L-ACT","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"},{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"},{"key":"z","type":"Real"}],"uses_definitions":["D-S811-P056-Q","D-S811-P056-C-ACT","D-015"],"source_anchors":[],"result_type":{"fn":{"args":[{"named":{"id":"D-S811-P056-Q","args":[{"var":"theta"}]}},"Nat"],"return":"Real"}},"body":"The exact global positive Euler family: D-015 factor on [sigma,z) and 1+c(q)/p outside."}
```

```mathminer-s3-legacy
{"schema":"mathminer.s3/1","id":"D-S811-P056-POINT-ACT","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"},{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"},{"key":"z","type":"Real"}],"uses_definitions":["D-015"],"source_anchors":[],"result_type":{"fn":{"args":["Nat"],"return":"Real"}},"body":"The pointwise global positive Euler family: exact on [sigma,z) and exact model outside."}
```

```mathminer-s3-legacy
{"schema":"mathminer.s3/1","id":"D-S811-P058-Q","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"}],"uses_definitions":[],"source_anchors":[],"result_type":"Type","body":"The nonempty exact endpoint-index type for the P058 family."}
```

```mathminer-s3-legacy
{"schema":"mathminer.s3/1","id":"D-S811-P058-C-0","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"}],"uses_definitions":["D-S811-P058-Q"],"source_anchors":[],"result_type":{"fn":{"args":[{"named":{"id":"D-S811-P058-Q","args":[{"var":"theta"}]}}],"return":"Real"}},"body":"The exact P058 coefficient map q maps to 0."}
```

```mathminer-s3-legacy
{"schema":"mathminer.s3/1","id":"D-S811-P058-L-0","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"},{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"}],"uses_definitions":["D-S811-P058-Q","D-S811-P058-C-0","D-015"],"source_anchors":[],"result_type":{"fn":{"args":[{"named":{"id":"D-S811-P058-Q","args":[{"var":"theta"}]}},"Nat"],"return":"Real"}},"body":"The exact global positive Euler family: D-015 factor on [2,sigma) and 1+c(q)/p outside."}
```

```mathminer-s3-legacy
{"schema":"mathminer.s3/1","id":"D-S811-P058-POINT-0","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"},{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"}],"uses_definitions":["D-015"],"source_anchors":[],"result_type":{"fn":{"args":["Nat"],"return":"Real"}},"body":"The pointwise global positive Euler family: exact on [2,sigma) and exact model outside."}
```

```mathminer-s3-legacy
{"schema":"mathminer.s3/1","id":"D-S811-P058-C-MID","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"},{"key":"y","type":"Real"}],"uses_definitions":["D-S811-P058-Q"],"source_anchors":[],"result_type":{"fn":{"args":[{"named":{"id":"D-S811-P058-Q","args":[{"var":"theta"}]}}],"return":"Real"}},"body":"The exact P058 coefficient map q maps to y/2."}
```

```mathminer-s3-legacy
{"schema":"mathminer.s3/1","id":"D-S811-P058-L-MID","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"},{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"}],"uses_definitions":["D-S811-P058-Q","D-S811-P058-C-MID","D-015"],"source_anchors":[],"result_type":{"fn":{"args":[{"named":{"id":"D-S811-P058-Q","args":[{"var":"theta"}]}},"Nat"],"return":"Real"}},"body":"The exact global positive Euler family: D-015 factor on [sigma,theta^k) and 1+c(q)/p outside."}
```

```mathminer-s3-legacy
{"schema":"mathminer.s3/1","id":"D-S811-P058-POINT-MID","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"},{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"}],"uses_definitions":["D-015"],"source_anchors":[],"result_type":{"fn":{"args":["Nat"],"return":"Real"}},"body":"The pointwise global positive Euler family: exact on [sigma,theta^k) and exact model outside."}
```

```mathminer-s3-legacy
{"schema":"mathminer.s3/1","id":"D-S811-P058-C-HI","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"}],"uses_definitions":["D-S811-P058-Q"],"source_anchors":[],"result_type":{"fn":{"args":[{"named":{"id":"D-S811-P058-Q","args":[{"var":"theta"}]}}],"return":"Real"}},"body":"The exact P058 coefficient map q maps to 1/2."}
```

```mathminer-s3-legacy
{"schema":"mathminer.s3/1","id":"D-S811-P058-L-HI","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"},{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"}],"uses_definitions":["D-S811-P058-Q","D-S811-P058-C-HI","D-015"],"source_anchors":[],"result_type":{"fn":{"args":[{"named":{"id":"D-S811-P058-Q","args":[{"var":"theta"}]}},"Nat"],"return":"Real"}},"body":"The exact global positive Euler family: D-015 factor on [theta^k,theta^(k+1)) and 1+c(q)/p outside."}
```

```mathminer-s3-legacy
{"schema":"mathminer.s3/1","id":"D-S811-P058-POINT-HI","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"},{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"}],"uses_definitions":["D-015"],"source_anchors":[],"result_type":{"fn":{"args":["Nat"],"return":"Real"}},"body":"The pointwise global positive Euler family: exact on [theta^k,theta^(k+1)) and exact model outside."}
```

```mathminer-s3-legacy
{"schema":"mathminer.s3/1","id":"D-S811-P077-Q","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"}],"uses_definitions":[],"source_anchors":[],"result_type":"Type","body":"The nonempty exact endpoint-index type for the P077 family."}
```

```mathminer-s3-legacy
{"schema":"mathminer.s3/1","id":"D-S811-P077-C-0","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"}],"uses_definitions":["D-S811-P077-Q"],"source_anchors":[],"result_type":{"fn":{"args":[{"named":{"id":"D-S811-P077-Q","args":[{"var":"theta"}]}}],"return":"Real"}},"body":"The exact P077 coefficient map q maps to 0."}
```

```mathminer-s3-legacy
{"schema":"mathminer.s3/1","id":"D-S811-P077-L-0","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"},{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"}],"uses_definitions":["D-S811-P077-Q","D-S811-P077-C-0","D-015"],"source_anchors":[],"result_type":{"fn":{"args":[{"named":{"id":"D-S811-P077-Q","args":[{"var":"theta"}]}},"Nat"],"return":"Real"}},"body":"The exact global positive Euler family: D-015 factor on [2,sigma) and 1+c(q)/p outside."}
```

```mathminer-s3-legacy
{"schema":"mathminer.s3/1","id":"D-S811-P077-POINT-0","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"},{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"},{"key":"z","type":"Real"}],"uses_definitions":["D-015"],"source_anchors":[],"result_type":{"fn":{"args":["Nat"],"return":"Real"}},"body":"The pointwise global positive Euler family: exact on [2,sigma) and exact model outside."}
```

```mathminer-s3-legacy
{"schema":"mathminer.s3/1","id":"D-S811-P077-C-HI","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"}],"uses_definitions":["D-S811-P077-Q"],"source_anchors":[],"result_type":{"fn":{"args":[{"named":{"id":"D-S811-P077-Q","args":[{"var":"theta"}]}}],"return":"Real"}},"body":"The exact P077 coefficient map q maps to 1/2."}
```

```mathminer-s3-legacy
{"schema":"mathminer.s3/1","id":"D-S811-P077-L-HI","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"},{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"},{"key":"z","type":"Real"}],"uses_definitions":["D-S811-P077-Q","D-S811-P077-C-HI","D-015"],"source_anchors":[],"result_type":{"fn":{"args":[{"named":{"id":"D-S811-P077-Q","args":[{"var":"theta"}]}},"Nat"],"return":"Real"}},"body":"The exact global positive Euler family: D-015 factor on [sigma,z) and 1+c(q)/p outside."}
```

```mathminer-s3-legacy
{"schema":"mathminer.s3/1","id":"D-S811-P077-POINT-HI","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"},{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"},{"key":"z","type":"Real"}],"uses_definitions":["D-015"],"source_anchors":[],"result_type":{"fn":{"args":["Nat"],"return":"Real"}},"body":"The pointwise global positive Euler family: exact on [sigma,z) and exact model outside."}
```

```mathminer-s3-legacy
{"schema":"mathminer.s3/1","id":"D-S811-P084-Q","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"}],"uses_definitions":[],"source_anchors":[],"result_type":"Type","body":"The nonempty exact endpoint-index type for the P084 family."}
```

```mathminer-s3-legacy
{"schema":"mathminer.s3/1","id":"D-S811-P084-C-0","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"}],"uses_definitions":["D-S811-P084-Q"],"source_anchors":[],"result_type":{"fn":{"args":[{"named":{"id":"D-S811-P084-Q","args":[{"var":"theta"}]}}],"return":"Real"}},"body":"The exact P084 coefficient map q maps to 0."}
```

```mathminer-s3-legacy
{"schema":"mathminer.s3/1","id":"D-S811-P084-L-0","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"},{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"}],"uses_definitions":["D-S811-P084-Q","D-S811-P084-C-0","D-015"],"source_anchors":[],"result_type":{"fn":{"args":[{"named":{"id":"D-S811-P084-Q","args":[{"var":"theta"}]}},"Nat"],"return":"Real"}},"body":"The exact global positive Euler family: D-015 factor on [2,sigma) and 1+c(q)/p outside."}
```

```mathminer-s3-legacy
{"schema":"mathminer.s3/1","id":"D-S811-P084-POINT-0","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"},{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"}],"uses_definitions":["D-015"],"source_anchors":[],"result_type":{"fn":{"args":["Nat"],"return":"Real"}},"body":"The pointwise global positive Euler family: exact on [2,sigma) and exact model outside."}
```

```mathminer-s3-legacy
{"schema":"mathminer.s3/1","id":"D-S811-P084-C-HI","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"}],"uses_definitions":["D-S811-P084-Q"],"source_anchors":[],"result_type":{"fn":{"args":[{"named":{"id":"D-S811-P084-Q","args":[{"var":"theta"}]}}],"return":"Real"}},"body":"The exact P084 coefficient map q maps to 1/2."}
```

```mathminer-s3-legacy
{"schema":"mathminer.s3/1","id":"D-S811-P084-L-HI","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"},{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"}],"uses_definitions":["D-S811-P084-Q","D-S811-P084-C-HI","D-015"],"source_anchors":[],"result_type":{"fn":{"args":[{"named":{"id":"D-S811-P084-Q","args":[{"var":"theta"}]}},"Nat"],"return":"Real"}},"body":"The exact global positive Euler family: D-015 factor on [sigma,theta^(k+1)) and 1+c(q)/p outside."}
```

```mathminer-s3-legacy
{"schema":"mathminer.s3/1","id":"D-S811-P084-POINT-HI","kind":"DEFINITION","binders":[{"key":"theta","type":"Real"},{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"}],"uses_definitions":["D-015"],"source_anchors":[],"result_type":{"fn":{"args":["Nat"],"return":"Real"}},"body":"The pointwise global positive Euler family: exact on [sigma,theta^(k+1)) and exact model outside."}
```

```mathminer-s3-legacy
{"schema":"mathminer.s3/1","id":"D-S811-Q","kind":"DEFINITION","binders":[],"uses_definitions":[],"source_anchors":[],"result_type":"Type","body":"The nonempty type of all tuples (theta,y,k,sigma) with theta>=2, 0<y<1, k>=1 and sigma>=theta."}
```

```mathminer-s3-legacy
{"schema":"mathminer.s3/1","id":"D-S811-Q0","kind":"DEFINITION","binders":[],"uses_definitions":["D-S811-Q"],"source_anchors":[],"result_type":{"named":{"id":"D-S811-Q","args":[]}},"body":"The distinguished valid tuple (2,1/2,1,2) in D-S811-Q."}
```

```mathminer-s3-legacy
{"schema":"mathminer.s3/1","id":"D-S811-WF","kind":"DEFINITION","binders":[],"uses_definitions":["D-015","D-S811-Q"],"source_anchors":[],"result_type":{"fn":{"args":[{"named":{"id":"D-S811-Q","args":[]}}],"return":{"fn":{"args":["Nat"],"return":"Real"}}}},"body":"At q=(theta,y,k,sigma), the exact D-015 final weight w_{4,k}; the whole family is fixed before P-059 selects C_fam."}
```

## 8. Regular-bin branch-explicit chain

### P-060 — exact regular smoothing

```mathminer-s3
{"schema":"mathminer.s3/1","id":"P-060","kind":"PROPOSITION","binders":[{"key":"theta","type":"Real"}],"uses_definitions":["D-002","D-003","D-015","D-016","D-017","D-019","D-S7-P051V-DOMAIN","D-S7A-TWO-K-MINUS-ONE","D-S7B-P052-DOMAIN","D-S7B-P052-W","S-P-060","W-P-060-C_reg_sm"],"source_anchors":[{"path":"stage3/canonical/CURRENT.md","git":"4279cd5e01f75401a9f5fa12d42961fe46b9ac8b","anchor":"### P-060 — exact regular smoothing"}],"hypotheses":[],"witnesses":[{"key":"C_reg_sm","type":"Real","depends_on":["theta"]}],"conclusions":[{"key":"result","proposition":{"def":{"id":"S-P-060","args":[{"var":"theta"},{"var":"C_reg_sm"}]}}}],"premises":[{"id":"MAP-P060-P050-1","producer":"P-050","closure_role":"REQUIRED","scope_binders":[{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"},{"key":"x","type":"Real"}],"binder_map":{"theta":{"var":"theta"},"y":{"var":"y"},"k":{"var":"k"},"sigma":{"var":"sigma"},"x":{"var":"x"}},"hypothesis_map":{"theta_ge_2":{"guard":"MAP-P060-P050-1_theta_ge_2"},"y_pos":{"guard":"MAP-P060-P050-1_y_pos"},"y_lt_1":{"guard":"MAP-P060-P050-1_y_lt_1"},"k_ge_1":{"guard":"MAP-P060-P050-1_k_ge_1"},"sigma_ge_theta":{"guard":"MAP-P060-P050-1_sigma_ge_theta"},"x_range":{"guard":"MAP-P060-P050-1_x_range"}},"witness_map":{},"consume":["four_variable_inversion"],"guards":[{"key":"MAP-P060-P050-1_theta_ge_2","proposition":{"op":{"name":"ge","args":[{"var":"theta"},{"lit":{"type":"Real","value":"2"}}]}}},{"key":"MAP-P060-P050-1_y_pos","proposition":{"op":{"name":"gt","args":[{"var":"y"},{"lit":{"type":"Real","value":"0"}}]}}},{"key":"MAP-P060-P050-1_y_lt_1","proposition":{"op":{"name":"lt","args":[{"var":"y"},{"lit":{"type":"Real","value":"1"}}]}}},{"key":"MAP-P060-P050-1_k_ge_1","proposition":{"op":{"name":"ge","args":[{"var":"k"},{"lit":{"type":"Nat","value":"1"}}]}}},{"key":"MAP-P060-P050-1_sigma_ge_theta","proposition":{"op":{"name":"ge","args":[{"var":"sigma"},{"var":"theta"}]}}},{"key":"MAP-P060-P050-1_x_range","proposition":{"op":{"name":"gt","args":[{"var":"x"},{"op":{"name":"pow_nat","args":[{"var":"theta"},{"def":{"id":"D-S7A-TWO-K-MINUS-ONE","args":[{"var":"k"}]}}]}}]}}}]},{"id":"MAP-P060-P052-2","producer":"A-LATE-P052-EXISTS","closure_role":"REQUIRED","scope_binders":[{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"},{"key":"x","type":"Real"},{"key":"t","type":"Nat"},{"key":"d","type":"Nat"},{"key":"d_prime","type":"Nat"}],"binder_map":{"theta":{"var":"theta"},"y":{"var":"y"},"k":{"var":"k"},"sigma":{"var":"sigma"},"K_sh":{"op":{"name":"mul","args":[{"var":"t"},{"op":{"name":"mul","args":[{"var":"d"},{"var":"d_prime"}]}}]}},"z":{"op":{"name":"div","args":[{"var":"x"},{"cast":{"value":{"op":{"name":"mul","args":[{"var":"t"},{"op":{"name":"mul","args":[{"var":"d"},{"var":"d_prime"}]}}]}},"to":"Real"}}]}}},"hypothesis_map":{"domain":{"guard":"MAP-P060-P052-2_domain"},"family_domain":{"guard":"MAP-P060-P052-2_family_domain"}},"witness_map":{},"consume":["existentialized"],"guards":[{"key":"MAP-P060-P052-2_domain","proposition":{"def":{"id":"D-S7B-P052-DOMAIN","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"},{"op":{"name":"mul","args":[{"var":"t"},{"op":{"name":"mul","args":[{"var":"d"},{"var":"d_prime"}]}}]}},{"op":{"name":"div","args":[{"var":"x"},{"cast":{"value":{"op":{"name":"mul","args":[{"var":"t"},{"op":{"name":"mul","args":[{"var":"d"},{"var":"d_prime"}]}}]}},"to":"Real"}}]}}]}}},{"key":"MAP-P060-P052-2_family_domain","proposition":{"def":{"id":"D-S7-P051V-DOMAIN","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"}]}}}]},{"id":"MAP-P060-P051F1-3","producer":"P-051F1","closure_role":"REQUIRED","binder_map":{},"hypothesis_map":{},"witness_map":{"c_1":"p_060_p_051f1_3_c_1","C_1":"p_060_p_051f1_3_C_1","Lambda_1":"p_060_p_051f1_3_Lambda_1"},"consume":["weight_type","dominates_base","dominates_shift"]},{"id":"MAP-P060-P051V-4","producer":"P-051V","closure_role":"REQUIRED","scope_binders":[{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"}],"binder_map":{"theta":{"var":"theta"},"y":{"var":"y"},"k":{"var":"k"},"sigma":{"var":"sigma"}},"hypothesis_map":{"theta_ge_2":{"guard":"MAP-P060-P051V-4_theta_ge_2"},"y_pos":{"guard":"MAP-P060-P051V-4_y_pos"},"y_lt_1":{"guard":"MAP-P060-P051V-4_y_lt_1"},"k_ge_1":{"guard":"MAP-P060-P051V-4_k_ge_1"},"sigma_ge_theta":{"guard":"MAP-P060-P051V-4_sigma_ge_theta"}},"witness_map":{},"consume":["modifier_normalization"],"guards":[{"key":"MAP-P060-P051V-4_theta_ge_2","proposition":{"op":{"name":"ge","args":[{"var":"theta"},{"lit":{"type":"Real","value":"2"}}]}}},{"key":"MAP-P060-P051V-4_y_pos","proposition":{"op":{"name":"gt","args":[{"var":"y"},{"lit":{"type":"Real","value":"0"}}]}}},{"key":"MAP-P060-P051V-4_y_lt_1","proposition":{"op":{"name":"lt","args":[{"var":"y"},{"lit":{"type":"Real","value":"1"}}]}}},{"key":"MAP-P060-P051V-4_k_ge_1","proposition":{"op":{"name":"ge","args":[{"var":"k"},{"lit":{"type":"Nat","value":"1"}}]}}},{"key":"MAP-P060-P051V-4_sigma_ge_theta","proposition":{"op":{"name":"ge","args":[{"var":"sigma"},{"var":"theta"}]}}}]}],"witness_realizations":{"C_reg_sm":{"def":{"id":"W-P-060-C_reg_sm","args":[{"var":"theta"},{"def":{"id":"D-S7B-P052-W","args":[{"var":"theta"}]}},{"var":"p_060_p_051f1_3_c_1"},{"var":"p_060_p_051f1_3_C_1"},{"var":"p_060_p_051f1_3_Lambda_1"}]}}},"proof_ref":"### P-060 — exact regular smoothing"}
```

- Prenex statement:
  \[
  \forall\theta\ge2\;\exists C_{\rm reg,sm}(\theta)>0\;
  \forall y\in(0,1)\;\forall k\ge1\;\forall\sigma\in[\theta,\theta^k]\;
  \forall x>\theta^{2k-1},
  \]
  \[
  S_k(x,y;\sigma,\theta)\le C_{\rm reg,sm}(\theta)U_k.
  \]
- Local equalities: \(z_m=x/(mdd')\); \(S_k\) is P-050/D-017 and \(U_k\)
  is D-019.
- Domain/range: \(C_{\rm reg,sm}\) is chosen after \(\theta\) and before
  \(y,k,\sigma,x,d,d',t,m\); it is uniform in all of them.
- Input subject: exact P-050 four-variable regular sum.
  Output subject: exact D-019 smoothed subject.
- Premise maps:
  - P-050 — Binders:
    \(y:=y,k:=k,\sigma:=\sigma,\theta:=\theta,x:=x\). Hypotheses:
    \(x>\theta^{2k-1}\) and regular domain. Consumed: exact inversion.
    Subject: literal input \(S_k\). Constants: none.
  - P-052 — Binders:
    \(K_{\rm sh}:=tdd'\), \(z:=x/(tdd')\);
    \(y:=y,k:=k,\sigma:=\sigma,\theta:=\theta\).
    Hypotheses: \(tdd'>0,z>0\). Consumed: reciprocal-divisor smoothing.
    Subject: the innermost P-050 \(m\)-sum. Constants:
    \(C_{\rm sm}(\theta)\mapsto C_{\rm reg,sm}(\theta)\), uniform in
    \(t,d,d'\).
  - `MAP-P060-P051F1`: consume only the exact D-015 identity and
    nonnegativity of \(w_1\).
  - `MAP-P060-P051V-MODIFIER`: bind \((\theta,y,k,\sigma)\) identically;
    the producer domains are discharged literally by
    \(\theta\ge2\), \(y\in(0,1)\), \(k\in\mathbb N_{\ge1}\), and
    \(\sigma\in[\theta,\theta^k]\). Consume from P-051V only the exact
    D-015 identity, nonnegativity, and multiplicativity of \(v_k\).
    Together these identify the post-factorization inner sum with D-016;
    neither normalization, the prime-power bound, a weight type, common
    witnesses, nor Euler tails are consumed.
- Derivation certificate: apply P-052, factor the displayed \(d,t\) weight,
  using multiplicativity of the indicator D-002 and complete additivity of
  D-003, then interchange the finite nonnegative \(m,t\) sums. The inner
  \(t\)-sum is literally \(T_k(x/(mdd'),dd')\).
- Source/S2 anchor: ET pp. 29–30; S2 R1 (5.1)–(5.3), R2.4.
- Definitions used: D-002, D-003, D-015, D-016, D-017, D-019.

### P-061 — exact three-way regular partition

```mathminer-s3
{"schema":"mathminer.s3/1","id":"P-061","kind":"PROPOSITION","binders":[{"key":"theta","type":"Real"},{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"},{"key":"x","type":"Real"}],"uses_definitions":["D-019","S-P-061"],"source_anchors":[{"path":"stage3/canonical/CURRENT.md","git":"4279cd5e01f75401a9f5fa12d42961fe46b9ac8b","anchor":"### P-061 — exact three-way regular partition"}],"hypotheses":[],"witnesses":[],"conclusions":[{"key":"result","proposition":{"def":{"id":"S-P-061","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"},{"var":"x"}]}}}],"premises":[],"witness_realizations":{},"proof_ref":"### P-061 — exact three-way regular partition"}
```

- Prenex statement: for every \(y\in(0,1)\), \(k\ge1\),
  \(\theta\ge2\), \(\sigma\in[\theta,\theta^k]\), and
  \[
  U_k=U_k^{\rm up}+U_k^{\rm mid}+U_k^{\rm term}.
  \]
- Local equalities: \(z_m=x/(mdd')\).
- Domain/range: because \(\sigma\le\theta^k\), the predicates
  \(z_m\ge\theta^k\), \(\sigma\le z_m<\theta^k\), \(z_m<\sigma\)
  are pairwise disjoint and exhaustive.
- Input subject: exact U-sum. Output: exact equality of three restrictions.
- Premise maps: none (root partition proposition).
- Derivation certificate: trichotomy on the real number \(z_m\); no estimate.
- Source/S2 anchor: ET p. 30; S2 R2.5a.
- Definitions used: D-019.

### P-062 — upper-regime substitution

Current construction binding: the exact `P062Statement` in the GroupA--GroupD source contracts, W0--W8, and the retained S7 provider. Any `mathminer-s3-legacy` block here is historical, not a proof.

```mathminer-s3-legacy
{"schema":"mathminer.s3/1","id":"P-062","kind":"PROPOSITION","binders":[{"key":"theta","type":"Real"}],"uses_definitions":["D-019","D-020","D-S7-P051V-DOMAIN","D-S7B-P055-DOMAIN","D-S7B-P055-W","S-P-062"],"source_anchors":[{"path":"stage3/canonical/CURRENT.md","git":"4279cd5e01f75401a9f5fa12d42961fe46b9ac8b","anchor":"### P-062 — upper-regime substitution"}],"hypotheses":[],"witnesses":[{"key":"C_up","type":"Real","depends_on":["theta"]}],"conclusions":[{"key":"result","proposition":{"def":{"id":"S-P-062","args":[{"var":"theta"},{"var":"C_up"}]}}}],"premises":[{"id":"MAP-P062-P055-1","producer":"A-LATE-P055-EXISTS","closure_role":"REQUIRED","scope_binders":[{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"},{"key":"x","type":"Real"},{"key":"d","type":"Nat"},{"key":"d_prime","type":"Nat"},{"key":"m","type":"Nat"}],"binder_map":{"theta":{"var":"theta"},"y":{"var":"y"},"k":{"var":"k"},"sigma":{"var":"sigma"},"K_sh":{"op":{"name":"mul","args":[{"var":"d"},{"var":"d_prime"}]}},"z":{"op":{"name":"div","args":[{"var":"x"},{"cast":{"value":{"op":{"name":"mul","args":[{"var":"m"},{"op":{"name":"mul","args":[{"var":"d"},{"var":"d_prime"}]}}]}},"to":"Real"}}]}}},"hypothesis_map":{"domain":{"guard":"MAP-P062-P055-1_domain"},"family_domain":{"guard":"MAP-P062-P055-1_family_domain"}},"witness_map":{},"consume":["existentialized"],"guards":[{"key":"MAP-P062-P055-1_domain","proposition":{"def":{"id":"D-S7B-P055-DOMAIN","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"},{"op":{"name":"mul","args":[{"var":"d"},{"var":"d_prime"}]}},{"op":{"name":"div","args":[{"var":"x"},{"cast":{"value":{"op":{"name":"mul","args":[{"var":"m"},{"op":{"name":"mul","args":[{"var":"d"},{"var":"d_prime"}]}}]}},"to":"Real"}}]}}]}}},{"key":"MAP-P062-P055-1_family_domain","proposition":{"def":{"id":"D-S7-P051V-DOMAIN","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"}]}}}]}],"witness_realizations":{"C_up":{"def":{"id":"D-S7B-P055-W","args":[{"var":"theta"}]}}},"proof_ref":"### P-062 — upper-regime substitution"}
```

  \[
  \forall\theta\ge2\;\exists C_{\rm up}(\theta)>0\;
  \forall y\in(0,1)\;\forall k\ge1\;\forall\sigma\in[\theta,\theta^k]\;
  \forall x>\theta^{2k-1},\quad
  U_k^{\rm up}\le C_{\rm up}(\theta)M_k^{\rm up}.
  \]
- Local equalities: at each term,
  \(K_{\rm sh}=dd'\) and \(z=x/(mdd')=z_m\).
- Domain/range: exact upper predicate \(z_m\ge\theta^k\).
- Input subject: \(U_k^{\rm up}\). Output: \(M_k^{\rm up}\).
- Premise maps:
  - P-055 — Binders:
    \(K_{\rm sh}:=dd'\), \(z:=x/(mdd')\), and
    \(y:=y,k:=k,\sigma:=\sigma,\theta:=\theta\).
    Hypotheses: upper predicate supplies \(z\ge\theta^k\);
    D-019 supplies \(\sigma\le\theta^k\).
    Consumed: exact upper T-bound.
    Subject: the T-factor in each U-term is replaced termwise, producing
    D-020 \(M_k^{\rm up}\) literally.
    Constants: \(C_{\rm up}(\theta)\) stays outside all
    \(d,d',m\)-sums and is uniform in \(x\).
- Derivation certificate: substitute the mapped T-bound term by term and sum.
- Source/S2 anchor: ET p. 30; S2 R2.14 upper line.
- Definitions used: D-019, D-020.

### P-063 — upper window/weight transport to \(A_k\)

Current construction binding: the exact `P063Statement` in the GroupA--GroupD source contracts, W0--W8, and the retained S7 provider. Any `mathminer-s3-legacy` block here is historical, not a proof.

```mathminer-s3-legacy
{"schema":"mathminer.s3/1","id":"P-063","kind":"PROPOSITION","binders":[{"key":"theta","type":"Real"}],"uses_definitions":["D-006","D-018","D-020","D-LATE-P051F3-W","D-S7B-P054-DOMAIN","D-S811-CERR","D-S811-CSTAR","D-S811-LAMBDASTAR","S-P-063","W-P-063-C_A"],"source_anchors":[{"path":"stage3/canonical/CURRENT.md","git":"4279cd5e01f75401a9f5fa12d42961fe46b9ac8b","anchor":"### P-063 \u2014 upper window/weight transport to \\(A_k\\)"}],"hypotheses":[],"witnesses":[{"key":"C_A","type":"Real","depends_on":["theta"]}],"conclusions":[{"key":"result","proposition":{"def":{"id":"S-P-063","args":[{"var":"theta"},{"var":"C_A"}]}}}],"premises":[{"id":"MAP-P063-P051F3-1","producer":"A-LATE-P051F3-EXISTS","closure_role":"REQUIRED","scope_binders":[{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"}],"binder_map":{"theta":{"var":"theta"},"y":{"var":"y"},"k":{"var":"k"},"sigma":{"var":"sigma"}},"hypothesis_map":{"theta_ge_2":{"guard":"MAP-P063-P051F3-1_theta_ge_2"},"y_pos":{"guard":"MAP-P063-P051F3-1_y_pos"},"y_lt_1":{"guard":"MAP-P063-P051F3-1_y_lt_1"},"k_ge_1":{"guard":"MAP-P063-P051F3-1_k_ge_1"},"sigma_ge_theta":{"guard":"MAP-P063-P051F3-1_sigma_ge_theta"}},"witness_map":{},"consume":["existentialized"],"guards":[{"key":"MAP-P063-P051F3-1_theta_ge_2","proposition":{"op":{"name":"ge","args":[{"var":"theta"},{"lit":{"type":"Real","value":"2"}}]}}},{"key":"MAP-P063-P051F3-1_y_pos","proposition":{"op":{"name":"gt","args":[{"var":"y"},{"lit":{"type":"Real","value":"0"}}]}}},{"key":"MAP-P063-P051F3-1_y_lt_1","proposition":{"op":{"name":"lt","args":[{"var":"y"},{"lit":{"type":"Real","value":"1"}}]}}},{"key":"MAP-P063-P051F3-1_k_ge_1","proposition":{"op":{"name":"ge","args":[{"var":"k"},{"lit":{"type":"Nat","value":"1"}}]}}},{"key":"MAP-P063-P051F3-1_sigma_ge_theta","proposition":{"op":{"name":"ge","args":[{"var":"sigma"},{"var":"theta"}]}}}]},{"id":"MAP-P063-P054-2","producer":"P-054","closure_role":"REQUIRED","scope_binders":[{"key":"d","type":"Nat"},{"key":"d_prime","type":"Nat"},{"key":"k","type":"Nat"}],"binder_map":{"d":{"var":"d"},"d_prime":{"var":"d_prime"},"k":{"var":"k"},"theta":{"var":"theta"}},"hypothesis_map":{"domain":{"guard":"MAP-P063-P054-2_domain"}},"witness_map":{},"consume":["close_window"],"guards":[{"key":"MAP-P063-P054-2_domain","proposition":{"def":{"id":"D-S7B-P054-DOMAIN","args":[{"var":"d"},{"var":"d_prime"},{"var":"k"},{"var":"theta"}]}}}]}],"witness_realizations":{"C_A":{"def":{"id":"W-P-063-C_A","args":[{"var":"theta"},{"def":{"id":"D-S811-CSTAR","args":[]}},{"def":{"id":"D-S811-CERR","args":[]}},{"def":{"id":"D-S811-LAMBDASTAR","args":[]}}]}}},"proof_ref":"### P-063 \u2014 upper window/weight transport to \\(A_k\\)"}
```

- Prenex statement:
  \[
  \forall\theta\ge2\;\exists C_A(\theta)>0\;
  \forall y\in(0,1)\;\forall k\ge1\;\forall\sigma\in[\theta,\theta^k]\;
  \forall x>\theta^{2k-1},\quad
  M_k^{\rm up}\le C_A(\theta)R_k^A.
  \]
- Local equalities: \(z_m=x/(mdd')\); \(R_k^A\) is D-018.
- Domain/range: all summands nonnegative; exponent \(-1/2\) is negative.
- Input subject: exact upper mixed sum. Output: exact D-018 A-subject.
- Premise maps:
  - `MAP-P063-P051F3`: bind \((\theta,y,k,\sigma)\) identically and consume
    only \(w_{2,k}(dd')\le w_{3,k}(dd')\); the subject is the literal
    differing D-020 weight and no constants are introduced.
  - P-054 — Binders:
    \(d:=d,d':=d',k:=k,\theta:=\theta\) termwise.
    Hypotheses: D-020 outer index. Consumed:
    \(\theta^{2k-1}<dd'<\theta^{2k+3}\).
    Subject: with \(z_m=x/(mdd')\), the condition
    \(z_m\ge\theta^k\) implies, up to a \(\theta\)-factor,
    \(m<x\theta^{1-3k}\); also
    \(z_m\asymp_\theta x\theta^{1-2k}/m\).
    Constants: all four-power window losses are absorbed only in
    \(C_A(\theta)\).
- Derivation certificate: use the upper bound on \(1/(dd')\); for
  \(\ell(z_m)^{-1/2}\), use the lower comparison for \(z_m\), reversing the
  comparison because the exponent is negative. Endpoint safety of \(\ell\)
  makes the comparison uniform in the last cell. The resulting \(m\)-sum is
  exactly A in D-018.
- Source/S2 anchor: ET pp. 30–31; S2 R1 (5.4)–(5.6), R2.6.
- Definitions used: D-006, D-018, D-020.

### P-064 — middle-regime substitution

Current construction binding: the exact `P064Statement` in the GroupA--GroupD source contracts, W0--W8, and the retained S7 provider. Any `mathminer-s3-legacy` block here is historical, not a proof.

```mathminer-s3-legacy
{"schema":"mathminer.s3/1","id":"P-064","kind":"PROPOSITION","binders":[{"key":"theta","type":"Real"}],"uses_definitions":["D-019","D-020","D-S7-P051V-DOMAIN","D-S7B-P056-DOMAIN","D-S7B-P056-W","S-P-064"],"source_anchors":[{"path":"stage3/canonical/CURRENT.md","git":"4279cd5e01f75401a9f5fa12d42961fe46b9ac8b","anchor":"### P-064 — middle-regime substitution"}],"hypotheses":[],"witnesses":[{"key":"C_mid","type":"Real","depends_on":["theta"]}],"conclusions":[{"key":"result","proposition":{"def":{"id":"S-P-064","args":[{"var":"theta"},{"var":"C_mid"}]}}}],"premises":[{"id":"MAP-P064-P056-1","producer":"A-LATE-P056-EXISTS","closure_role":"REQUIRED","scope_binders":[{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"},{"key":"x","type":"Real"},{"key":"d","type":"Nat"},{"key":"d_prime","type":"Nat"},{"key":"m","type":"Nat"}],"binder_map":{"theta":{"var":"theta"},"y":{"var":"y"},"k":{"var":"k"},"sigma":{"var":"sigma"},"K_sh":{"op":{"name":"mul","args":[{"var":"d"},{"var":"d_prime"}]}},"z":{"op":{"name":"div","args":[{"var":"x"},{"cast":{"value":{"op":{"name":"mul","args":[{"var":"m"},{"op":{"name":"mul","args":[{"var":"d"},{"var":"d_prime"}]}}]}},"to":"Real"}}]}}},"hypothesis_map":{"domain":{"guard":"MAP-P064-P056-1_domain"},"family_domain":{"guard":"MAP-P064-P056-1_family_domain"}},"witness_map":{},"consume":["existentialized"],"guards":[{"key":"MAP-P064-P056-1_domain","proposition":{"def":{"id":"D-S7B-P056-DOMAIN","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"},{"op":{"name":"mul","args":[{"var":"d"},{"var":"d_prime"}]}},{"op":{"name":"div","args":[{"var":"x"},{"cast":{"value":{"op":{"name":"mul","args":[{"var":"m"},{"op":{"name":"mul","args":[{"var":"d"},{"var":"d_prime"}]}}]}},"to":"Real"}}]}}]}}},{"key":"MAP-P064-P056-1_family_domain","proposition":{"def":{"id":"D-S7-P051V-DOMAIN","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"}]}}}]}],"witness_realizations":{"C_mid":{"def":{"id":"D-S7B-P056-W","args":[{"var":"theta"}]}}},"proof_ref":"### P-064 — middle-regime substitution"}
```

- Prenex statement:
  \[
  \forall\theta\ge2\;\exists C_{\rm mid}(\theta)>0\;
  \forall y\in(0,1)\;\forall k\ge1\;\forall\sigma\in[\theta,\theta^k]\;
  \forall x>\theta^{2k-1},\quad
  U_k^{\rm mid}\le C_{\rm mid}(\theta)M_k^{\rm mid}.
  \]
- Local equalities: \(K_{\rm sh}=dd'\), \(z=z_m=x/(mdd')\).
- Domain/range: exact predicate \(\sigma\le z_m<\theta^k\).
- Input subject: exact middle U-subject. Output: exact middle mixed sum.
- Premise maps:
  - P-056 — Binders:
    \(y:=y,k:=k,\sigma:=\sigma,\theta:=\theta,
    K_{\rm sh}:=dd',z:=z_m\).
    Hypotheses: exact middle predicate. Consumed: middle T-bound.
    Subject: termwise substitution yields D-020 \(M_k^{\rm mid}\).
    Constants: \(C_{\rm mid}(\theta)\) stays outside all sums, uniform in
    \(x,d,d',m\).
- Derivation certificate: substitute and sum.
- Source/S2 anchor: ET p. 30; S2 R2.14 middle line.
- Definitions used: D-019, D-020.

### P-065 — middle window/weight transport to \(B_k\)

Current construction binding: the exact `P065Statement` in the GroupA--GroupD source contracts, W0--W8, and the retained S7 provider. Any `mathminer-s3-legacy` block here is historical, not a proof.

```mathminer-s3-legacy
{"schema":"mathminer.s3/1","id":"P-065","kind":"PROPOSITION","binders":[{"key":"theta","type":"Real"}],"uses_definitions":["D-006","D-018","D-020","D-LATE-P051F3-W","D-S7B-P054-DOMAIN","D-S811-CERR","D-S811-CSTAR","D-S811-LAMBDASTAR","S-P-065","W-P-065-C_B"],"source_anchors":[{"path":"stage3/canonical/CURRENT.md","git":"4279cd5e01f75401a9f5fa12d42961fe46b9ac8b","anchor":"### P-065 \u2014 middle window/weight transport to \\(B_k\\)"}],"hypotheses":[],"witnesses":[{"key":"C_B","type":"Real","depends_on":["theta"]}],"conclusions":[{"key":"result","proposition":{"def":{"id":"S-P-065","args":[{"var":"theta"},{"var":"C_B"}]}}}],"premises":[{"id":"MAP-P065-P051F3-1","producer":"A-LATE-P051F3-EXISTS","closure_role":"REQUIRED","scope_binders":[{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"}],"binder_map":{"theta":{"var":"theta"},"y":{"var":"y"},"k":{"var":"k"},"sigma":{"var":"sigma"}},"hypothesis_map":{"theta_ge_2":{"guard":"MAP-P065-P051F3-1_theta_ge_2"},"y_pos":{"guard":"MAP-P065-P051F3-1_y_pos"},"y_lt_1":{"guard":"MAP-P065-P051F3-1_y_lt_1"},"k_ge_1":{"guard":"MAP-P065-P051F3-1_k_ge_1"},"sigma_ge_theta":{"guard":"MAP-P065-P051F3-1_sigma_ge_theta"}},"witness_map":{},"consume":["existentialized"],"guards":[{"key":"MAP-P065-P051F3-1_theta_ge_2","proposition":{"op":{"name":"ge","args":[{"var":"theta"},{"lit":{"type":"Real","value":"2"}}]}}},{"key":"MAP-P065-P051F3-1_y_pos","proposition":{"op":{"name":"gt","args":[{"var":"y"},{"lit":{"type":"Real","value":"0"}}]}}},{"key":"MAP-P065-P051F3-1_y_lt_1","proposition":{"op":{"name":"lt","args":[{"var":"y"},{"lit":{"type":"Real","value":"1"}}]}}},{"key":"MAP-P065-P051F3-1_k_ge_1","proposition":{"op":{"name":"ge","args":[{"var":"k"},{"lit":{"type":"Nat","value":"1"}}]}}},{"key":"MAP-P065-P051F3-1_sigma_ge_theta","proposition":{"op":{"name":"ge","args":[{"var":"sigma"},{"var":"theta"}]}}}]},{"id":"MAP-P065-P054-2","producer":"P-054","closure_role":"REQUIRED","scope_binders":[{"key":"d","type":"Nat"},{"key":"d_prime","type":"Nat"},{"key":"k","type":"Nat"}],"binder_map":{"d":{"var":"d"},"d_prime":{"var":"d_prime"},"k":{"var":"k"},"theta":{"var":"theta"}},"hypothesis_map":{"domain":{"guard":"MAP-P065-P054-2_domain"}},"witness_map":{},"consume":["close_window"],"guards":[{"key":"MAP-P065-P054-2_domain","proposition":{"def":{"id":"D-S7B-P054-DOMAIN","args":[{"var":"d"},{"var":"d_prime"},{"var":"k"},{"var":"theta"}]}}}]}],"witness_realizations":{"C_B":{"def":{"id":"W-P-065-C_B","args":[{"var":"theta"},{"def":{"id":"D-S811-CSTAR","args":[]}},{"def":{"id":"D-S811-CERR","args":[]}},{"def":{"id":"D-S811-LAMBDASTAR","args":[]}}]}}},"proof_ref":"### P-065 \u2014 middle window/weight transport to \\(B_k\\)"}
```

- Prenex statement:
  \[
  \forall\theta\ge2\;\exists C_B(\theta)>0\;
  \forall y\in(0,1)\;\forall k\ge1\;\forall\sigma\in[\theta,\theta^k]\;
  \forall x>\theta^{2k-1},\quad
  M_k^{\rm mid}\le C_B(\theta)R_k^B.
  \]
- Local equalities: \(z_m=x/(mdd')\); exponent \(y/2-1\in(-1,-1/2)\).
- Domain/range: exact middle range.
- Input subject: middle mixed sum. Output: exact D-018
  \(B_k^{\rm enl}\)-subject; it is not identified with \(B_k^{\#}\).
- Premise maps:
  - `MAP-P065-P051F3`: bind \((\theta,y,k,\sigma)\) identically and consume
    only \(w_{2,k}(dd')\le w_{3,k}(dd')\); the subject is the literal
    differing D-020 weight and no constants are introduced.
  - P-054 — Binders:
    \(d:=d,d':=d',k:=k,\theta:=\theta\) termwise.
    Hypotheses: D-020 outer index.
    Consumed: strict product window.
    Subject: the predicates \(\sigma\le z_m<\theta^k\) and the two strict
    product-window endpoints transport to
    \(x\theta^{-3k-3}<m<x\theta^{1-2k}\);
    \(z_m\asymp_\theta x\theta^{1-2k}/m\).
    Constants: only \(C_B(\theta)\).
- Adapter: `AD-P065-MIDDLE-ENLARGE` is the termwise map from the exact
  variable-\(dd'\) middle range to the separately named fixed interval of
  \(B_k^{\rm enl}\); it preserves the summand up to the displayed
  \(\theta\)-comparison and uses nonnegativity for restriction enlargement.
- Derivation certificate: upper-bound \(z_m\) using the lower product
  endpoint; since \(y/2-1<0\), upper-bound
  \(\ell(z_m)^{y/2-1}\) using the lower logarithmic comparison—the direction
  reverses. Enlarge finite endpoints by fixed \(\theta\)-factors; the exact
  resulting subject is \(B_k^{\rm enl}\) in D-018.
- Source/S2 anchor: ET p. 31; S2 R1 (5.7), R2.6.
- Definitions used: D-006, D-018, D-020.

### P-066 — terminal-regime substitution

```mathminer-s3
{"schema":"mathminer.s3/1","id":"P-066","kind":"PROPOSITION","binders":[{"key":"theta","type":"Real"},{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"},{"key":"x","type":"Real"}],"uses_definitions":["D-019","D-020","D-S7-P051V-DOMAIN","D-S7B-P057-DOMAIN","S-P-066"],"source_anchors":[{"path":"stage3/canonical/CURRENT.md","git":"4279cd5e01f75401a9f5fa12d42961fe46b9ac8b","anchor":"### P-066 — terminal-regime substitution"}],"hypotheses":[],"witnesses":[],"conclusions":[{"key":"result","proposition":{"def":{"id":"S-P-066","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"},{"var":"x"}]}}}],"premises":[{"id":"MAP-P066-P057-1","producer":"P-057","closure_role":"REQUIRED","scope_binders":[{"key":"d","type":"Nat"},{"key":"d_prime","type":"Nat"},{"key":"m","type":"Nat"}],"binder_map":{"theta":{"var":"theta"},"y":{"var":"y"},"k":{"var":"k"},"sigma":{"var":"sigma"},"K_sh":{"op":{"name":"mul","args":[{"var":"d"},{"var":"d_prime"}]}},"z":{"op":{"name":"div","args":[{"var":"x"},{"cast":{"value":{"op":{"name":"mul","args":[{"var":"m"},{"op":{"name":"mul","args":[{"var":"d"},{"var":"d_prime"}]}}]}},"to":"Real"}}]}}},"hypothesis_map":{"domain":{"guard":"MAP-P066-P057-1_domain"},"family_domain":{"guard":"MAP-P066-P057-1_family_domain"}},"witness_map":{},"consume":["terminal_bound"],"guards":[{"key":"MAP-P066-P057-1_domain","proposition":{"def":{"id":"D-S7B-P057-DOMAIN","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"},{"op":{"name":"mul","args":[{"var":"d"},{"var":"d_prime"}]}},{"op":{"name":"div","args":[{"var":"x"},{"cast":{"value":{"op":{"name":"mul","args":[{"var":"m"},{"op":{"name":"mul","args":[{"var":"d"},{"var":"d_prime"}]}}]}},"to":"Real"}}]}}]}}},{"key":"MAP-P066-P057-1_family_domain","proposition":{"def":{"id":"D-S7-P051V-DOMAIN","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"}]}}}]}],"witness_realizations":{},"proof_ref":"### P-066 — terminal-regime substitution"}
```

- Prenex statement: for every \(y\in(0,1)\), \(k\ge1\),
  \(\theta\ge2\), \(\sigma\in[\theta,\theta^k]\), and
  \(x>\theta^{2k-1}\),
  \[
  U_k^{\rm term}\le M_k^{\rm term}.
  \]
- Local equalities: \(K_{\rm sh}=dd'\), \(z=z_m=x/(mdd')\).
- Domain/range: exact predicate \(z_m<\sigma\).
- Input subject: terminal U-subject. Output: exact terminal mixed sum.
- Premise maps:
  - P-057 — Binders:
    \(y:=y,k:=k,\sigma:=\sigma,\theta:=\theta,
    K_{\rm sh}:=dd',z:=z_m\).
    Hypotheses: terminal predicate and regular domain.
    Consumed: endpoint-safe bound \(T_k\le w_1\).
    Subject: termwise comparison gives D-020 \(M_k^{\rm term}\) literally.
    Constants: none.
- Derivation certificate: apply the exact T-bound and retain every index.
- Source/S2 anchor: ET p. 30; S2 R2.14 terminal line.
- Definitions used: D-019, D-020.

### P-067 — terminal window/weight transport to \(C_k\)

Current construction binding: the exact `P067Statement` in the GroupA--GroupD source contracts, W0--W8, and the retained S7 provider. Any `mathminer-s3-legacy` block here is historical, not a proof.

```mathminer-s3-legacy
{"schema":"mathminer.s3/1","id":"P-067","kind":"PROPOSITION","binders":[{"key":"theta","type":"Real"}],"uses_definitions":["D-006","D-018","D-020","D-LATE-P051F3-W","D-S7B-P053-DOMAIN","D-S7B-P053-W","D-S7B-P054-DOMAIN","D-S811-CERR","D-S811-CSTAR","D-S811-LAMBDASTAR","S-P-067","W-P-067-C_C"],"source_anchors":[{"path":"stage3/canonical/CURRENT.md","git":"4279cd5e01f75401a9f5fa12d42961fe46b9ac8b","anchor":"### P-067 \u2014 terminal window/weight transport to \\(C_k\\)"}],"hypotheses":[],"witnesses":[{"key":"C_C","type":"Real","depends_on":["theta"]}],"conclusions":[{"key":"result","proposition":{"def":{"id":"S-P-067","args":[{"var":"theta"},{"var":"C_C"}]}}}],"premises":[{"id":"MAP-P067-P051F3-1","producer":"A-LATE-P051F3-EXISTS","closure_role":"REQUIRED","scope_binders":[{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"}],"binder_map":{"theta":{"var":"theta"},"y":{"var":"y"},"k":{"var":"k"},"sigma":{"var":"sigma"}},"hypothesis_map":{"theta_ge_2":{"guard":"MAP-P067-P051F3-1_theta_ge_2"},"y_pos":{"guard":"MAP-P067-P051F3-1_y_pos"},"y_lt_1":{"guard":"MAP-P067-P051F3-1_y_lt_1"},"k_ge_1":{"guard":"MAP-P067-P051F3-1_k_ge_1"},"sigma_ge_theta":{"guard":"MAP-P067-P051F3-1_sigma_ge_theta"}},"witness_map":{},"consume":["existentialized"],"guards":[{"key":"MAP-P067-P051F3-1_theta_ge_2","proposition":{"op":{"name":"ge","args":[{"var":"theta"},{"lit":{"type":"Real","value":"2"}}]}}},{"key":"MAP-P067-P051F3-1_y_pos","proposition":{"op":{"name":"gt","args":[{"var":"y"},{"lit":{"type":"Real","value":"0"}}]}}},{"key":"MAP-P067-P051F3-1_y_lt_1","proposition":{"op":{"name":"lt","args":[{"var":"y"},{"lit":{"type":"Real","value":"1"}}]}}},{"key":"MAP-P067-P051F3-1_k_ge_1","proposition":{"op":{"name":"ge","args":[{"var":"k"},{"lit":{"type":"Nat","value":"1"}}]}}},{"key":"MAP-P067-P051F3-1_sigma_ge_theta","proposition":{"op":{"name":"ge","args":[{"var":"sigma"},{"var":"theta"}]}}}]},{"id":"MAP-P067-P054-2","producer":"P-054","closure_role":"REQUIRED","scope_binders":[{"key":"d","type":"Nat"},{"key":"d_prime","type":"Nat"},{"key":"k","type":"Nat"}],"binder_map":{"d":{"var":"d"},"d_prime":{"var":"d_prime"},"k":{"var":"k"},"theta":{"var":"theta"}},"hypothesis_map":{"domain":{"guard":"MAP-P067-P054-2_domain"}},"witness_map":{},"consume":["close_window"],"guards":[{"key":"MAP-P067-P054-2_domain","proposition":{"def":{"id":"D-S7B-P054-DOMAIN","args":[{"var":"d"},{"var":"d_prime"},{"var":"k"},{"var":"theta"}]}}}]},{"id":"MAP-P067-P053-3","producer":"A-LATE-P053-EXISTS","closure_role":"REQUIRED","scope_binders":[{"key":"M","type":"Real"}],"binder_map":{"M":{"var":"M"}},"hypothesis_map":{"domain":{"guard":"MAP-P067-P053-3_domain"}},"witness_map":{},"consume":["existentialized"],"guards":[{"key":"MAP-P067-P053-3_domain","proposition":{"def":{"id":"D-S7B-P053-DOMAIN","args":[{"var":"M"}]}}}]}],"witness_realizations":{"C_C":{"def":{"id":"W-P-067-C_C","args":[{"var":"theta"},{"def":{"id":"D-S811-CSTAR","args":[]}},{"def":{"id":"D-S811-CERR","args":[]}},{"def":{"id":"D-S811-LAMBDASTAR","args":[]}},{"def":{"id":"D-S7B-P053-W","args":[]}}]}}},"proof_ref":"### P-067 \u2014 terminal window/weight transport to \\(C_k\\)"}
```

- Prenex statement:
  \[
  \forall\theta\ge2\;\exists C_C(\theta)>0\;
  \forall y\in(0,1)\;\forall k\ge1\;\forall\sigma\in[\theta,\theta^k]\;
  \forall x>\theta^{2k-1},\quad
  M_k^{\rm term}\le C_C(\theta)R_k^C.
  \]
- Local equalities: \(R_k^C=(\log\sigma)^{-y/2}O_kC_k\), so the two
  log-\(\sigma\) factors cancel exactly.
- Domain/range: exact terminal predicate; exponent \(-1/2\).
- Input subject: terminal mixed sum. Output: exact D-018 C-subject.
- Premise maps:
  - `MAP-P067-P051F3`: bind \((\theta,y,k,\sigma)\) identically and consume
    only \(w_1(dd')\le w_{3,k}(dd')\); the subject is the literal terminal
    weight and no constants are introduced.
  - P-054 — Binders:
    \(d:=d,d':=d',k:=k,\theta:=\theta\) termwise.
    Hypotheses: D-020 outer index.
    Consumed: product window.
    Subject: \(M=x/(dd')\asymp_\theta x\theta^{1-2k}\).
    Constants: only \(\theta\)-dependence.
  - P-053 — Binders: \(M:=x/(dd')\).
    Hypotheses: positivity. Consumed: endpoint-safe partial sum.
    Subject: terminal inner sum after dropping \(z_m<\sigma\);
    the negative \(-1/2\) power uses the lower endpoint comparison, with
    direction reversed, to yield
    \(\ell(2x\theta^{1-2k})^{-1/2}\).
    Constants: \(C_{\rm ps}\) absorbed into \(C_C(\theta)\).
- Derivation certificate: dominate the weight, enlarge the terminal
  \(m\)-range, apply P-053, and use the strict product window. The output is
  exactly \(R_k^C\), not an unnamed contribution.
- Source/S2 anchor: ET pp. 30–31; S2 R1 (5.8), R2.6.
- Definitions used: D-006, D-018, D-020.

### P-068 — \(A_k\) convolution bound

Current construction binding: the exact `P068Statement` in the GroupA--GroupD source contracts, W0--W8, and the retained S7 provider. Any `mathminer-s3-legacy` block here is historical, not a proof.

```mathminer-s3-legacy
{"schema":"mathminer.s3/1","id":"P-068","kind":"PROPOSITION","binders":[],"uses_definitions":["D-006","D-018","D-S811-P068-ADM","D-S811-P068-CHOOSE","S-P-068"],"source_anchors":[{"path":"stage3/canonical/CURRENT.md","git":"4279cd5e01f75401a9f5fa12d42961fe46b9ac8b","anchor":"### P-068 \u2014 \\(A_k\\) convolution bound"}],"hypotheses":[],"witnesses":[{"key":"C_A_abs","type":"Real","depends_on":[]}],"conclusions":[{"key":"result","proposition":{"def":{"id":"S-P-068","args":[{"var":"C_A_abs"}]}}}],"premises":[],"witness_realizations":{"C_A_abs":{"def":{"id":"D-S811-P068-CHOOSE","args":[]}}},"proof_ref":"### P-068 \u2014 \\(A_k\\) convolution bound"}
```

- Prenex statement: there exists an absolute \(C_A'>0\) such that for all
  \(y\in(0,1),k\ge1,\sigma\ge\theta\ge2,x>\theta^{2k-1}\),
  \[
  A_k\le C_A'x\theta^{-2k}k^{(y-1)/2}.
  \]
- Local equalities: A is D-018 exactly.
- Domain/range: constant uniform in every displayed variable.
- Input subject: exact A-sum. Output: beta-convolution bound.
- Premise maps: none (root).
- Derivation certificate: log-coordinate comparison with
  \(\int_0^L s^{-1/2}(L-s)^{-1/2}ds=\pi\), using \(\ell\) for endpoints.
- Source/S2 anchor: ET p. 31; S2 R1 (5.6), R2.6.
- Definitions used: D-006, D-018.

### P-069 — exact R3 middle-convolution bounds

Current construction binding: the exact `P069Statement` in the GroupA--GroupD source contracts, W0--W8, and the retained S7 provider. Any `mathminer-s3-legacy` block here is historical, not a proof.

```mathminer-s3-legacy
{"schema":"mathminer.s3/1","id":"P-069","kind":"PROPOSITION","binders":[],"uses_definitions":["D-006","D-018","D-S811-P069-ADM","D-S811-P069-CHOOSE","S-P-069"],"source_anchors":[{"path":"stage3/canonical/CURRENT.md","git":"4279cd5e01f75401a9f5fa12d42961fe46b9ac8b","anchor":"### P-069 \u2014 exact R3 middle-convolution bounds"}],"hypotheses":[],"witnesses":[{"key":"C_mc","type":"Real","depends_on":[]}],"conclusions":[{"key":"result","proposition":{"def":{"id":"S-P-069","args":[{"var":"C_mc"}]}}}],"premises":[],"witness_realizations":{"C_mc":{"def":{"id":"D-S811-P069-CHOOSE","args":[]}}},"proof_ref":"### P-069 \u2014 exact R3 middle-convolution bounds"}
```

- Prenex statement:
  \[
  \exists C_{\rm mc}>0\;\forall\theta\ge2\;
  \forall y\in(0,1)\;\forall k\ge1\;\forall\sigma\ge\theta\;
  \forall x>\theta^{2k-1},
  \]
  \[
  B_k^{\#}(x;y)\le {C_{\rm mc}\over y}x\theta^{-2k}
  \ell(2x\theta^{1-2k})^{(y-1)/2},
  \]
  and the same bound holds with \(B_k^{\#}\) replaced by
  \(B_k^{\rm enl}\).
- Local equalities: \(B_k^{\#}\) is the exact R3 subject, and
  \(B_k^{\rm enl}\) is the separately named restriction/enlargement subject.
- Domain/range: exponent \(y/2-1>-1\).
- Input subject: exact B-sum. Output: beta-convolution bound.
- Premise maps: none (root).
- Derivation certificate: apply the discrete R3-MC split at \(\sqrt M\),
  with \(M=x\theta^{1-2k}>1\) and \(\beta=y/2\). Its common absolute
  witness precedes \(\theta,y,k,\sigma,x\), and the shell sum contributes
  the explicit sharp factor \(1/y\). Both displayed sums are restrictions of
  \(1\le m<M\), so nonnegativity gives the second bound without identifying
  the subjects.
- Source/S2 anchor: S2 R3.2--R3.5 and S2B R3.
- Definitions used: D-006, D-018.

### P-070 — family-uniform final \(w_{4,k}\) mean

Current construction binding: the exact `P070Statement` in the GroupA--GroupD source contracts, W0--W8, and the retained S7 provider. Any `mathminer-s3-legacy` block here is historical, not a proof.

```mathminer-s3-legacy
{"schema":"mathminer.s3/1","id":"P-070","kind":"PROPOSITION","binders":[],"uses_definitions":["D-014","D-015","D-LATE-P051G-W","D-S7A-F4-W","D-S7B-P059-DOMAIN","D-S7B-P059-W","D-S811-CERR","D-S811-CSTAR","D-S811-LAMBDASTAR","D-S811-Q","D-S811-Q0","D-S811-WF","S-P-070","W-P-070-C_fam"],"source_anchors":[{"path":"stage3/canonical/CURRENT.md","git":"4279cd5e01f75401a9f5fa12d42961fe46b9ac8b","anchor":"### P-070 \u2014 family-uniform final \\(w_{4,k}\\) mean"}],"hypotheses":[],"witnesses":[{"key":"c_star","type":"Real","depends_on":[]},{"key":"C_star","type":"Real","depends_on":[]},{"key":"Lambda_star","type":"Real","depends_on":[]},{"key":"C_fam","type":"Real","depends_on":[]}],"conclusions":[{"key":"result","proposition":{"def":{"id":"S-P-070","args":[{"var":"c_star"},{"var":"C_star"},{"var":"Lambda_star"},{"var":"C_fam"}]}}}],"premises":[{"id":"MAP-P070-P051F4-1","producer":"A-LATE-P051F4-EXISTS","closure_role":"REQUIRED","scope_binders":[{"key":"theta","type":"Real"},{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"}],"binder_map":{"theta":{"var":"theta"},"y":{"var":"y"},"k":{"var":"k"},"sigma":{"var":"sigma"}},"hypothesis_map":{"theta_ge_2":{"guard":"MAP-P070-P051F4-1_theta_ge_2"},"y_pos":{"guard":"MAP-P070-P051F4-1_y_pos"},"y_lt_1":{"guard":"MAP-P070-P051F4-1_y_lt_1"},"k_ge_1":{"guard":"MAP-P070-P051F4-1_k_ge_1"},"sigma_ge_theta":{"guard":"MAP-P070-P051F4-1_sigma_ge_theta"}},"witness_map":{},"consume":["existentialized"],"guards":[{"key":"MAP-P070-P051F4-1_theta_ge_2","proposition":{"op":{"name":"ge","args":[{"var":"theta"},{"lit":{"type":"Real","value":"2"}}]}}},{"key":"MAP-P070-P051F4-1_y_pos","proposition":{"op":{"name":"gt","args":[{"var":"y"},{"lit":{"type":"Real","value":"0"}}]}}},{"key":"MAP-P070-P051F4-1_y_lt_1","proposition":{"op":{"name":"lt","args":[{"var":"y"},{"lit":{"type":"Real","value":"1"}}]}}},{"key":"MAP-P070-P051F4-1_k_ge_1","proposition":{"op":{"name":"ge","args":[{"var":"k"},{"lit":{"type":"Nat","value":"1"}}]}}},{"key":"MAP-P070-P051F4-1_sigma_ge_theta","proposition":{"op":{"name":"ge","args":[{"var":"sigma"},{"var":"theta"}]}}}]},{"id":"MAP-P070-P051G-2","producer":"A-LATE-P051G-EXISTS","closure_role":"REQUIRED","scope_binders":[{"key":"theta","type":"Real"},{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"}],"binder_map":{"theta":{"var":"theta"},"y":{"var":"y"},"k":{"var":"k"},"sigma":{"var":"sigma"}},"hypothesis_map":{"theta_ge_2":{"guard":"MAP-P070-P051G-2_theta_ge_2"},"y_pos":{"guard":"MAP-P070-P051G-2_y_pos"},"y_lt_1":{"guard":"MAP-P070-P051G-2_y_lt_1"},"k_ge_1":{"guard":"MAP-P070-P051G-2_k_ge_1"},"sigma_ge_theta":{"guard":"MAP-P070-P051G-2_sigma_ge_theta"}},"witness_map":{},"consume":["existentialized"],"guards":[{"key":"MAP-P070-P051G-2_theta_ge_2","proposition":{"op":{"name":"ge","args":[{"var":"theta"},{"lit":{"type":"Real","value":"2"}}]}}},{"key":"MAP-P070-P051G-2_y_pos","proposition":{"op":{"name":"gt","args":[{"var":"y"},{"lit":{"type":"Real","value":"0"}}]}}},{"key":"MAP-P070-P051G-2_y_lt_1","proposition":{"op":{"name":"lt","args":[{"var":"y"},{"lit":{"type":"Real","value":"1"}}]}}},{"key":"MAP-P070-P051G-2_k_ge_1","proposition":{"op":{"name":"ge","args":[{"var":"k"},{"lit":{"type":"Nat","value":"1"}}]}}},{"key":"MAP-P070-P051G-2_sigma_ge_theta","proposition":{"op":{"name":"ge","args":[{"var":"sigma"},{"var":"theta"}]}}}]},{"id":"MAP-P070-P059-3","producer":"A-LATE-P059-EXISTS","closure_role":"REQUIRED","scope_binders":[{"key":"q","type":{"named":{"id":"D-S811-Q","args":[]}}},{"key":"Z","type":"Real"}],"binder_map":{"Q":{"type":{"named":{"id":"D-S811-Q","args":[]}}},"w_family":{"def":{"id":"D-S811-WF","args":[]}},"c_w":{"def":{"id":"D-S811-CSTAR","args":[]}},"C_w_err":{"def":{"id":"D-S811-CERR","args":[]}},"Lambda_w":{"def":{"id":"D-S811-LAMBDASTAR","args":[]}},"q":{"var":"q"},"Z":{"var":"Z"}},"hypothesis_map":{"domain":{"guard":"MAP-P070-P059-3_domain"}},"witness_map":{},"consume":["existentialized"],"guards":[{"key":"MAP-P070-P059-3_domain","proposition":{"def":{"id":"D-S7B-P059-DOMAIN","args":[{"type":{"named":{"id":"D-S811-Q","args":[]}}},{"def":{"id":"D-S811-WF","args":[]}},{"def":{"id":"D-S811-CSTAR","args":[]}},{"def":{"id":"D-S811-CERR","args":[]}},{"def":{"id":"D-S811-LAMBDASTAR","args":[]}},{"var":"q"},{"var":"Z"}]}}}]}],"witness_realizations":{"c_star":{"def":{"id":"D-S811-CSTAR","args":[]}},"C_star":{"def":{"id":"D-S811-CERR","args":[]}},"Lambda_star":{"def":{"id":"D-S811-LAMBDASTAR","args":[]}},"C_fam":{"def":{"id":"D-S7B-P059-W","args":[{"type":{"named":{"id":"D-S811-Q","args":[]}}},{"def":{"id":"D-S811-WF","args":[]}},{"def":{"id":"D-S811-CSTAR","args":[]}},{"def":{"id":"D-S811-CERR","args":[]}},{"def":{"id":"D-S811-LAMBDASTAR","args":[]}}]}}},"proof_ref":"### P-070 \u2014 family-uniform final \\(w_{4,k}\\) mean"}
```

- Prenex statement:
  \[
  \exists c_*>0\;\exists C_*>0\;\exists\Lambda_*>0\;
  \exists C_{\rm fam}>0\;\forall\theta\ge2,
  \]
  define, inside the scope of the selected \(C_{\rm fam}\),
  \[
  C_4(C_{\rm fam},\theta):=
  {C_{\rm fam}\theta^2\over\sqrt{\log\theta}}>0.
  \tag{P070-C4}
  \]
  Then for every \(y\in(0,1)\), every
  \(k\in\mathbb N_{\ge1}\), and every \(\sigma\ge\theta\), both
  \[
  \forall Z\ge2,\qquad
  \sum_{r<Z}w_{4,k}(r)\le C_{\rm fam}Z(\log Z)^{-1/2},
  \tag{P070-family-mean}
  \]
  and
  \[
  \sum_{\theta^{k-1}<r<\theta^{k+2}}w_{4,k}(r)
  \le C_4(C_{\rm fam},\theta)\theta^k k^{-1/2}.
  \tag{P070-window}
  \]
- Local equalities: \(w_{4,k}\) is D-015.
- Domain/range: \(C_{\rm fam}\) is selected before
  \(\theta,y,k,\sigma,Z\). The positive term
  \(C_4(C_{\rm fam},\theta)\) is an active definition after \(\theta\) and
  before \(y,k,\sigma,Z\); it has no free witness or hidden binder.
- Input subject: exact finite \(d'\)-window sum. Output: exact mean bound.
- Premise maps:
  - `MAP-P070-P051F4`: consume the exact D-015 construction and
    nonnegative multiplicativity of the \(w_{4,k}\)-family.
  - `MAP-P070-P051G`: consume the single common witnesses
    \(c_*,C_*,\Lambda_*\) before assigning
    \(\theta:=\theta,y:=y,k:=k,\sigma:=\sigma\); the conclusion gives the
    exact \(w_{4,k}\) error and local bounds.
  - `MAP-P070-P059`:

    | producer | slot | domain | consumer term | evidence |
    |---|---|---|---|---|
    | P-059 | `Q` | nonempty index set | \(Q_4:=\{(\theta,y,k,\sigma):\theta\ge2,0<y<1,k\in\mathbb N_{\ge1},\sigma\ge\theta\}\) | nonempty, e.g. \((2,1/2,1,2)\) |
    | P-059 | `(w_q)` | family | \(w_{(\theta,y,k,\sigma)}:=w_{4,k}\) from D-015 | P-051F4 exact construction |
    | P-059 | `c_w` | \(\mathbb R_{>0}\) | \(c_*\) | P-051G common witness |
    | P-059 | `C_w_err` | \(\mathbb R_{>0}\) | \(C_*\) | P-051G common witness |
    | P-059 | `Lambda_w` | \(\mathbb R_{>0}\) | \(\Lambda_*\) | P-051G common witness |
    | P-059 | `q` | \(Q_4\) | \((\theta,y,k,\sigma)\) | P-070 uniform tuple |
    | P-059 | `Z` | \(\mathbb R_{\ge2}\) | \(Z\) | P-070 binder |

    Producer hypotheses are exactly the P-051G common error, bound,
    nonnegativity, and multiplicativity conclusions. Consumed conclusion is
    P-059's family mean for `SUB-P070-FAMILY-MEAN`; this subject is literally
    the P-070 partial sum after the \(q\)-substitution. The producer constant
    is mapped identically to \(C_{\rm fam}\), and its uniform variables
    \((q,Z)\) map to \((\theta,y,k,\sigma,Z)\). The window corollary uses
    \(Z:=\theta^{k+2}\) and nonnegative restriction.
- Derivation certificate: apply (P070-family-mean) at
  \(Z:=\theta^{k+2}\) and restrict its nonnegative sum. Since
  \(\log(\theta^{k+2})=(k+2)\log\theta\) and \(k+2\ge k\),
  \[
  {C_{\rm fam}\theta^{k+2}\over\sqrt{(k+2)\log\theta}}
  \le {C_{\rm fam}\theta^2\over\sqrt{\log\theta}}
       \theta^k k^{-1/2}
  =C_4(C_{\rm fam},\theta)\theta^k k^{-1/2}.
  \]
  This is exactly (P070-window); no asymptotic comparison constant is added.
- Source/S2 anchor: ET p. 31; S2 R1 (5.10), R2.4.
- Definitions used: D-014, D-015.

### P-071 — regular upper branch assembly

Current construction binding: the exact `P071Statement` in the GroupA--GroupD source contracts, W0--W8, and the retained S7 provider. Any `mathminer-s3-legacy` block here is historical, not a proof.

```mathminer-s3-legacy
{"schema":"mathminer.s3/1","id":"P-071","kind":"PROPOSITION","binders":[{"key":"theta","type":"Real"}],"uses_definitions":["D-018","D-S7-P051V-DOMAIN","D-S7B-P058-DOMAIN","D-S7B-P058-W","S-P-071","W-P-071-C_A_asm"],"source_anchors":[{"path":"stage3/canonical/CURRENT.md","git":"4279cd5e01f75401a9f5fa12d42961fe46b9ac8b","anchor":"### P-071 \u2014 regular upper branch assembly"}],"hypotheses":[],"witnesses":[{"key":"C_A_asm","type":"Real","depends_on":["theta"]}],"conclusions":[{"key":"result","proposition":{"def":{"id":"S-P-071","args":[{"var":"theta"},{"var":"C_A_asm"}]}}}],"premises":[{"id":"MAP-P071-P058-1","producer":"A-LATE-P058-EXISTS","closure_role":"REQUIRED","scope_binders":[{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"},{"key":"x","type":"Real"}],"binder_map":{"theta":{"var":"theta"},"y":{"var":"y"},"k":{"var":"k"},"sigma":{"var":"sigma"},"x":{"var":"x"}},"hypothesis_map":{"domain":{"guard":"MAP-P071-P058-1_domain"},"family_domain":{"guard":"MAP-P071-P058-1_family_domain"}},"witness_map":{},"consume":["existentialized"],"guards":[{"key":"MAP-P071-P058-1_domain","proposition":{"def":{"id":"D-S7B-P058-DOMAIN","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"},{"var":"x"}]}}},{"key":"MAP-P071-P058-1_family_domain","proposition":{"def":{"id":"D-S7-P051V-DOMAIN","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"}]}}}]},{"id":"MAP-P071-P068-2","producer":"P-068","closure_role":"REQUIRED","binder_map":{},"hypothesis_map":{},"witness_map":{"C_A_abs":"p_071_p_068_2_C_A_abs"},"consume":["result"]},{"id":"MAP-P071-P070-3","producer":"P-070","closure_role":"REQUIRED","binder_map":{},"hypothesis_map":{},"witness_map":{"c_star":"p_071_p_070_3_c_star","C_star":"p_071_p_070_3_C_star","Lambda_star":"p_071_p_070_3_Lambda_star","C_fam":"p_071_p_070_3_C_fam"},"consume":["result"]}],"witness_realizations":{"C_A_asm":{"def":{"id":"W-P-071-C_A_asm","args":[{"var":"theta"},{"def":{"id":"D-S7B-P058-W","args":[{"var":"theta"}]}},{"var":"p_071_p_068_2_C_A_abs"},{"var":"p_071_p_070_3_c_star"},{"var":"p_071_p_070_3_C_star"},{"var":"p_071_p_070_3_Lambda_star"},{"var":"p_071_p_070_3_C_fam"}]}}},"proof_ref":"### P-071 \u2014 regular upper branch assembly"}
```

- Prenex statement:
  \[
  \forall\theta\ge2\;\exists C_{A,\rm asm}(\theta)>0\;
  \forall y\in(0,1)\;\forall k\ge1\;\forall\sigma\in[\theta,\theta^k]\;
  \forall x>\theta^{2k-1},
  \]
  \[
  R_k^A\le C_{A,\rm asm}(\theta)
  x(\log\sigma)^{-y}k^{(y-3)/2}k^{(y-1)/2}.
  \]
- Local equalities: \(R_k^A=(\log\sigma)^{-y/2}O_kA_k\).
- Domain/range: uniform in \(y,k,\sigma,x\).
- Input subject: exact transported A-subject. Output: upper brace term.
- Premise maps:
  - P-058 — Binders:
    \(\theta:=\theta,y:=y,k:=k,\sigma:=\sigma\).
    Hypotheses: \(\theta\ge2,\sigma\in[\theta,\theta^k]\).
    Consumed: outer mean. Subject: exact O-factor. Constants:
    \(C_{\rm out}(\theta)\).
  - P-068 — Binders:
    \(y:=y,k:=k,\sigma:=\sigma,\theta:=\theta,x:=x\).
    Hypotheses: the displayed domains.
    Consumed: A-bound. Subject: exact A-factor. Constants: absolute.
  - P-070 — Witness/order map: first select
    \(c_*,C_*,\Lambda_*,C_{\rm fam}\), then set \(\theta:=\theta\) and
    define \(C_4:=C_4(C_{\rm fam},\theta)\) by (P070-C4), and only then set
    \(y:=y,k:=k,\sigma:=\sigma\).
    Hypotheses: the displayed domains.
    Consumed: (P070-window). Subject: `SUB-P070-WINDOW`, literally the exact
    \(d'\)-sum produced by P-058. Constants: map the P-070 window coefficient as
    \(C_4:=C_4(C_{\rm fam},\theta)\) from (P070-C4); it is absorbed into
    \(C_{A,\rm asm}(\theta)\) only after \(\theta\) is fixed.
- Derivation certificate: multiply the three exact inequalities and simplify
  \((\log\sigma)^{-y/2}\cdot(\log\sigma)^{-y/2}\) and the k-powers.
- Source/S2 anchor: ET pp. 30–31; S2 R1 (5.5)–(5.10).
- Definitions used: D-018.

### P-072 — regular middle branch assembly

Current construction binding: the exact `P072Statement` in the GroupA--GroupD source contracts, W0--W8, and the retained S7 provider. Any `mathminer-s3-legacy` block here is historical, not a proof.

```mathminer-s3-legacy
{"schema":"mathminer.s3/1","id":"P-072","kind":"PROPOSITION","binders":[{"key":"theta","type":"Real"}],"uses_definitions":["D-018","D-S7-P051V-DOMAIN","D-S7B-P058-DOMAIN","D-S7B-P058-W","S-P-072","W-P-072-C_B_asm"],"source_anchors":[{"path":"stage3/canonical/CURRENT.md","git":"4279cd5e01f75401a9f5fa12d42961fe46b9ac8b","anchor":"### P-072 \u2014 regular middle branch assembly"}],"hypotheses":[],"witnesses":[{"key":"C_B_asm","type":"Real","depends_on":["theta"]}],"conclusions":[{"key":"result","proposition":{"def":{"id":"S-P-072","args":[{"var":"theta"},{"var":"C_B_asm"}]}}}],"premises":[{"id":"MAP-P072-P058-1","producer":"A-LATE-P058-EXISTS","closure_role":"REQUIRED","scope_binders":[{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"},{"key":"x","type":"Real"}],"binder_map":{"theta":{"var":"theta"},"y":{"var":"y"},"k":{"var":"k"},"sigma":{"var":"sigma"},"x":{"var":"x"}},"hypothesis_map":{"domain":{"guard":"MAP-P072-P058-1_domain"},"family_domain":{"guard":"MAP-P072-P058-1_family_domain"}},"witness_map":{},"consume":["existentialized"],"guards":[{"key":"MAP-P072-P058-1_domain","proposition":{"def":{"id":"D-S7B-P058-DOMAIN","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"},{"var":"x"}]}}},{"key":"MAP-P072-P058-1_family_domain","proposition":{"def":{"id":"D-S7-P051V-DOMAIN","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"}]}}}]},{"id":"MAP-P072-P069-2","producer":"P-069","closure_role":"REQUIRED","binder_map":{},"hypothesis_map":{},"witness_map":{"C_mc":"p_072_p_069_2_C_mc"},"consume":["result"]},{"id":"MAP-P072-P070-3","producer":"P-070","closure_role":"REQUIRED","binder_map":{},"hypothesis_map":{},"witness_map":{"c_star":"p_072_p_070_3_c_star","C_star":"p_072_p_070_3_C_star","Lambda_star":"p_072_p_070_3_Lambda_star","C_fam":"p_072_p_070_3_C_fam"},"consume":["result"]}],"witness_realizations":{"C_B_asm":{"def":{"id":"W-P-072-C_B_asm","args":[{"var":"theta"},{"def":{"id":"D-S7B-P058-W","args":[{"var":"theta"}]}},{"var":"p_072_p_069_2_C_mc"},{"var":"p_072_p_070_3_c_star"},{"var":"p_072_p_070_3_C_star"},{"var":"p_072_p_070_3_Lambda_star"},{"var":"p_072_p_070_3_C_fam"}]}}},"proof_ref":"### P-072 \u2014 regular middle branch assembly"}
```

- Prenex statement:
  \[
  \forall\theta\ge2\;\exists C_{B,\rm asm}(\theta)>0\;
  \forall y\in(0,1)\;\forall k\ge1\;\forall\sigma\in[\theta,\theta^k]\;
  \forall x>\theta^{2k-1},
  \]
  \[
  R_k^B\le {C_{B,\rm asm}(\theta)\over y}
  x(\log\sigma)^{-y}k^{(y-3)/2}
  \ell(2x\theta^{1-2k})^{(y-1)/2}.
  \]
- Local equalities: exact D-018 \(R_k^B\).
- Domain/range: uniform after \(\theta\).
- Input subject: exact transported B-subject. Output: middle brace term.
- Premise maps:
  - P-058 — Binders:
    \(\theta:=\theta,y:=y,k:=k,\sigma:=\sigma\).
    Hypotheses: \(\sigma\in[\theta,\theta^k]\). Consumed: O-bound.
    Subject: exact O. Constants: \(C_{\rm out}(\theta)\).
  - P-069 — Binders:
    \(\theta:=\theta,y:=y,k:=k,\sigma:=\sigma,x:=x\).
    Hypotheses: \(y\in(0,1),k\ge1,\theta\ge2,
    \sigma\in[\theta,\theta^k],x>\theta^{2k-1}\). Consumed: B-bound.
    Subject: exact \(B_k^{\rm enl}\), not \(B_k^{\#}\). Constants:
    \(C_{\rm mc}/y\), with \(y\) kept explicit.
  - P-070 — Witness/order map: first select
    \(c_*,C_*,\Lambda_*,C_{\rm fam}\), then set \(\theta:=\theta\) and
    define \(C_4:=C_4(C_{\rm fam},\theta)\) by (P070-C4), and only then set
    \(y:=y,k:=k,\sigma:=\sigma\).
    Hypotheses: \(y\in(0,1),k\ge1,\sigma\ge\theta\ge2\).
    Consumed: (P070-window).
    Subject: `SUB-P070-WINDOW`, literally P-058's \(d'\)-sum. Constants: map
    \(C_4:=C_4(C_{\rm fam},\theta)\) literally, then absorb it into
    \(C_{B,\rm asm}(\theta)\) after \(\theta\) is fixed.
- Derivation certificate: multiply and simplify exact factors.
- Source/S2 anchor: ET p. 31; S2 R1 (5.5)–(5.10).
- Definitions used: D-018.

### P-073 — regular terminal branch assembly

Current construction binding: the exact `P073Statement` in the GroupA--GroupD source contracts, W0--W8, and the retained S7 provider. Any `mathminer-s3-legacy` block here is historical, not a proof.

```mathminer-s3-legacy
{"schema":"mathminer.s3/1","id":"P-073","kind":"PROPOSITION","binders":[{"key":"theta","type":"Real"}],"uses_definitions":["D-018","D-S7-P051V-DOMAIN","D-S7B-P058-DOMAIN","D-S7B-P058-W","S-P-073","W-P-073-C_C_asm"],"source_anchors":[{"path":"stage3/canonical/CURRENT.md","git":"4279cd5e01f75401a9f5fa12d42961fe46b9ac8b","anchor":"### P-073 \u2014 regular terminal branch assembly"}],"hypotheses":[],"witnesses":[{"key":"C_C_asm","type":"Real","depends_on":["theta"]}],"conclusions":[{"key":"result","proposition":{"def":{"id":"S-P-073","args":[{"var":"theta"},{"var":"C_C_asm"}]}}}],"premises":[{"id":"MAP-P073-P058-1","producer":"A-LATE-P058-EXISTS","closure_role":"REQUIRED","scope_binders":[{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"},{"key":"x","type":"Real"}],"binder_map":{"theta":{"var":"theta"},"y":{"var":"y"},"k":{"var":"k"},"sigma":{"var":"sigma"},"x":{"var":"x"}},"hypothesis_map":{"domain":{"guard":"MAP-P073-P058-1_domain"},"family_domain":{"guard":"MAP-P073-P058-1_family_domain"}},"witness_map":{},"consume":["existentialized"],"guards":[{"key":"MAP-P073-P058-1_domain","proposition":{"def":{"id":"D-S7B-P058-DOMAIN","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"},{"var":"x"}]}}},{"key":"MAP-P073-P058-1_family_domain","proposition":{"def":{"id":"D-S7-P051V-DOMAIN","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"}]}}}]},{"id":"MAP-P073-P070-2","producer":"P-070","closure_role":"REQUIRED","binder_map":{},"hypothesis_map":{},"witness_map":{"c_star":"p_073_p_070_2_c_star","C_star":"p_073_p_070_2_C_star","Lambda_star":"p_073_p_070_2_Lambda_star","C_fam":"p_073_p_070_2_C_fam"},"consume":["result"]}],"witness_realizations":{"C_C_asm":{"def":{"id":"W-P-073-C_C_asm","args":[{"var":"theta"},{"def":{"id":"D-S7B-P058-W","args":[{"var":"theta"}]}},{"var":"p_073_p_070_2_c_star"},{"var":"p_073_p_070_2_C_star"},{"var":"p_073_p_070_2_Lambda_star"},{"var":"p_073_p_070_2_C_fam"}]}}},"proof_ref":"### P-073 \u2014 regular terminal branch assembly"}
```

- Prenex statement:
  \[
  \forall\theta\ge2\;\exists C_{C,\rm asm}(\theta)>0\;
  \forall y\in(0,1)\;\forall k\ge1\;\forall\sigma\in[\theta,\theta^k]\;
  \forall x>\theta^{2k-1},
  \]
  \[
  R_k^C\le C_{C,\rm asm}(\theta)
  x(\log\sigma)^{-y}k^{(y-3)/2}
  {(\log\sigma)^{y/2}\over
  \ell(2x\theta^{1-2k})^{1/2}}.
  \]
- Local equalities: exact D-018 \(R_k^C\).
- Domain/range: uniform after \(\theta\).
- Input subject: exact transported C-subject. Output: terminal brace term.
- Premise maps:
  - P-058 — Binders:
    \(\theta:=\theta,y:=y,k:=k,\sigma:=\sigma\).
    Hypotheses: \(\sigma\in[\theta,\theta^k]\). Consumed: O-bound.
    Subject: exact O. Constants: \(C_{\rm out}(\theta)\).
  - P-070 — Witness/order map: first select
    \(c_*,C_*,\Lambda_*,C_{\rm fam}\), then set \(\theta:=\theta\) and
    define \(C_4:=C_4(C_{\rm fam},\theta)\) by (P070-C4), and only then set
    \(y:=y,k:=k,\sigma:=\sigma\).
    Hypotheses: \(y\in(0,1),k\ge1,\sigma\ge\theta\ge2\).
    Consumed: (P070-window).
    Subject: `SUB-P070-WINDOW`, literally P-058's \(d'\)-sum. Constants: map
    \(C_4:=C_4(C_{\rm fam},\theta)\) literally, then absorb it into
    \(C_{C,\rm asm}(\theta)\) after \(\theta\) is fixed.
  - D-018 equality — no theorem edge: C is already the exact scalar
    \(x\theta^{-2k}(\log\sigma)^{y/2}\ell(\cdot)^{-1/2}\).
- Derivation certificate: substitute C's defining equality and multiply the
  two mean estimates.
- Source/S2 anchor: ET p. 31; S2 R1 (5.5)–(5.10).
- Definitions used: D-018.

### P-074 — regular envelope addition

Current construction binding: the exact `P074Statement` in the GroupA--GroupD source contracts, W0--W8, and the retained S7 provider. Any `mathminer-s3-legacy` block here is historical, not a proof.

```mathminer-s3-legacy
{"schema":"mathminer.s3/1","id":"P-074","kind":"PROPOSITION","binders":[{"key":"theta","type":"Real"}],"uses_definitions":["D-006","D-017","D-018","D-019","D-020","S-P-074","W-P-074-C_reg"],"source_anchors":[{"path":"stage3/canonical/CURRENT.md","git":"4279cd5e01f75401a9f5fa12d42961fe46b9ac8b","anchor":"### P-074 \u2014 regular envelope addition"}],"hypotheses":[],"witnesses":[{"key":"C_reg","type":"Real","depends_on":["theta"]}],"conclusions":[{"key":"result","proposition":{"def":{"id":"S-P-074","args":[{"var":"theta"},{"var":"C_reg"}]}}}],"premises":[{"id":"MAP-P074-P060-1","producer":"P-060","closure_role":"REQUIRED","binder_map":{"theta":{"var":"theta"}},"hypothesis_map":{},"witness_map":{"C_reg_sm":"p_074_p_060_1_C_reg_sm"},"consume":["result"]},{"id":"MAP-P074-P061-2","producer":"P-061","closure_role":"REQUIRED","scope_binders":[{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"},{"key":"x","type":"Real"}],"binder_map":{"theta":{"var":"theta"},"y":{"var":"y"},"k":{"var":"k"},"sigma":{"var":"sigma"},"x":{"var":"x"}},"hypothesis_map":{},"witness_map":{},"consume":["result"]},{"id":"MAP-P074-P062-3","producer":"P-062","closure_role":"REQUIRED","binder_map":{"theta":{"var":"theta"}},"hypothesis_map":{},"witness_map":{"C_up":"p_074_p_062_3_C_up"},"consume":["result"]},{"id":"MAP-P074-P063-4","producer":"P-063","closure_role":"REQUIRED","binder_map":{"theta":{"var":"theta"}},"hypothesis_map":{},"witness_map":{"C_A":"p_074_p_063_4_C_A"},"consume":["result"]},{"id":"MAP-P074-P064-5","producer":"P-064","closure_role":"REQUIRED","binder_map":{"theta":{"var":"theta"}},"hypothesis_map":{},"witness_map":{"C_mid":"p_074_p_064_5_C_mid"},"consume":["result"]},{"id":"MAP-P074-P065-6","producer":"P-065","closure_role":"REQUIRED","binder_map":{"theta":{"var":"theta"}},"hypothesis_map":{},"witness_map":{"C_B":"p_074_p_065_6_C_B"},"consume":["result"]},{"id":"MAP-P074-P066-7","producer":"P-066","closure_role":"REQUIRED","scope_binders":[{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"},{"key":"x","type":"Real"}],"binder_map":{"theta":{"var":"theta"},"y":{"var":"y"},"k":{"var":"k"},"sigma":{"var":"sigma"},"x":{"var":"x"}},"hypothesis_map":{},"witness_map":{},"consume":["result"]},{"id":"MAP-P074-P067-8","producer":"P-067","closure_role":"REQUIRED","binder_map":{"theta":{"var":"theta"}},"hypothesis_map":{},"witness_map":{"C_C":"p_074_p_067_8_C_C"},"consume":["result"]},{"id":"MAP-P074-P071-9","producer":"P-071","closure_role":"REQUIRED","binder_map":{"theta":{"var":"theta"}},"hypothesis_map":{},"witness_map":{"C_A_asm":"p_074_p_071_9_C_A_asm"},"consume":["result"]},{"id":"MAP-P074-P072-10","producer":"P-072","closure_role":"REQUIRED","binder_map":{"theta":{"var":"theta"}},"hypothesis_map":{},"witness_map":{"C_B_asm":"p_074_p_072_10_C_B_asm"},"consume":["result"]},{"id":"MAP-P074-P073-11","producer":"P-073","closure_role":"REQUIRED","binder_map":{"theta":{"var":"theta"}},"hypothesis_map":{},"witness_map":{"C_C_asm":"p_074_p_073_11_C_C_asm"},"consume":["result"]}],"witness_realizations":{"C_reg":{"def":{"id":"W-P-074-C_reg","args":[{"var":"theta"},{"var":"p_074_p_060_1_C_reg_sm"},{"var":"p_074_p_062_3_C_up"},{"var":"p_074_p_063_4_C_A"},{"var":"p_074_p_064_5_C_mid"},{"var":"p_074_p_065_6_C_B"},{"var":"p_074_p_067_8_C_C"},{"var":"p_074_p_071_9_C_A_asm"},{"var":"p_074_p_072_10_C_B_asm"},{"var":"p_074_p_073_11_C_C_asm"}]}}},"proof_ref":"### P-074 \u2014 regular envelope addition"}
```

- Prenex statement:
  \[
  \forall\theta\ge2\;\exists C_{\rm reg}(\theta)>0\;
  \forall y\in(0,1)\;\forall k\ge1\;\forall\sigma\in[\theta,\theta^k]\;
  \forall x>\theta^{2k-1},
  \]
  \[
  S_k(x,y;\sigma,\theta)\le {C_{\rm reg}(\theta)\over y}
  x(\log\sigma)^{-y}k^{(y-3)/2}
  \left\{k^{(y-1)/2}
  +\ell(2x\theta^{1-2k})^{(y-1)/2}
  +{(\log\sigma)^{y/2}\over\ell(2x\theta^{1-2k})^{1/2}}\right\}.
  \]
- Local equalities: the three branches are D-019/D-020/D-018.
- Domain/range: the theta-only constant precedes \(y,k,\sigma,x\); the sharp
  dependence on the subsequently fixed \(y\) is the displayed \(1/y\).
  The numerator constant is selected after \(\theta\) from the three assembly
  constants, each of which already contains the literal
  \(C_4(C_{\rm fam},\theta)\) where used; it introduces no new \(y\)-dependence.
- Input subject: exact regular S-subject. Output: regular P3 envelope.
- Premise maps:
  - P-060 — Binders:
    \(\theta:=\theta,y:=y,k:=k,\sigma:=\sigma,x:=x\).
    Hypotheses: \(\theta\ge2,\sigma\in[\theta,\theta^k],
    x>\theta^{2k-1}\).
    Consumed: \(S_k\le C_{\rm reg,sm}U_k\).
    Subject: literal S and U. Constants: preserve \(C_{\rm reg,sm}(\theta)\).
  - P-061 — Binders:
    \(y:=y,k:=k,\theta:=\theta,\sigma:=\sigma,x:=x\).
    Hypotheses: \(y\in(0,1),k\ge1,\theta\ge2,
    \sigma\in[\theta,\theta^k],x>\theta^{2k-1}\).
    Consumed: exact partition equality. Subject: literal U.
    Constants: none.
  - P-062 — Binders:
    \(\theta:=\theta,y:=y,k:=k,\sigma:=\sigma,x:=x\).
    Hypotheses: the explicit regular parameter inequalities in the P-074
    prefix. Consumed: upper substitution.
    Subject: \(U^{\rm up}\to M^{\rm up}\). Constants: \(C_{\rm up}(\theta)\).
  - P-063 — Binders:
    \(\theta:=\theta,y:=y,k:=k,\sigma:=\sigma,x:=x\).
    Hypotheses: the explicit regular parameter inequalities in the P-074
    prefix. Consumed: upper transport.
    Subject: \(M^{\rm up}\to R^A\). Constants: \(C_A(\theta)\).
  - P-064 — Binders:
    \(\theta:=\theta,y:=y,k:=k,\sigma:=\sigma,x:=x\).
    Hypotheses: the explicit regular parameter inequalities in the P-074
    prefix. Consumed: middle substitution.
    Subject: \(U^{\rm mid}\to M^{\rm mid}\). Constants: \(C_{\rm mid}(\theta)\).
  - P-065 — Binders:
    \(\theta:=\theta,y:=y,k:=k,\sigma:=\sigma,x:=x\).
    Hypotheses: the explicit regular parameter inequalities in the P-074
    prefix. Consumed: middle transport.
    Subject: \(M^{\rm mid}\to R^B\). Constants: \(C_B(\theta)\).
  - P-066 — Binders:
    \(y:=y,k:=k,\theta:=\theta,\sigma:=\sigma,x:=x\).
    Hypotheses: the explicit regular parameter inequalities in the P-074
    prefix. Consumed: terminal substitution bound.
    Subject: \(U^{\rm term}\to M^{\rm term}\). Constants: none.
  - P-067 — Binders:
    \(\theta:=\theta,y:=y,k:=k,\sigma:=\sigma,x:=x\).
    Hypotheses: the explicit regular parameter inequalities in the P-074
    prefix. Consumed: terminal transport.
    Subject: \(M^{\rm term}\to R^C\). Constants: \(C_C(\theta)\).
  - P-071 — Binders:
    \(\theta:=\theta,y:=y,k:=k,\sigma:=\sigma,x:=x\).
    Hypotheses: the explicit regular parameter inequalities in the P-074
    prefix. Consumed: A assembly.
    Subject: exact \(R^A\). Constants: \(C_{A,\rm asm}(\theta)\).
  - P-072 — Binders:
    \(\theta:=\theta,y:=y,k:=k,\sigma:=\sigma,x:=x\).
    Hypotheses: the explicit regular parameter inequalities in the P-074
    prefix. Consumed: B assembly.
    Subject: exact \(R^B\). Constants: \(C_{B,\rm asm}(\theta)\).
  - P-073 — Binders:
    \(\theta:=\theta,y:=y,k:=k,\sigma:=\sigma,x:=x\).
    Hypotheses: the explicit regular parameter inequalities in the P-074
    prefix. Consumed: C assembly.
    Subject: exact \(R^C\). Constants: \(C_{C,\rm asm}(\theta)\).
- Derivation certificate: follow the exact branch chain and add the three
  nonnegative bounds. No mixed subject is introduced here.
- Source/S2 anchor: ET Proposition 3 regular calculation, pp. 29–31;
  S2 R1 (5.1)–(5.10), R2.4–R2.6.
- Definitions used: D-017, D-018, D-019, D-020.

## 9. Transition-bin parity chain and Proposition 3

### P-075 — exact transition smoothing

```mathminer-s3
{"schema":"mathminer.s3/1","id":"P-075","kind":"PROPOSITION","binders":[{"key":"theta","type":"Real"}],"uses_definitions":["D-002","D-003","D-015","D-016","D-017","D-021a","D-021b","D-021c","D-021d","D-021e","D-S7-P051V-DOMAIN","D-S7A-TWO-K-MINUS-ONE","D-S7B-P052-DOMAIN","D-S7B-P052-W","S-P-075","W-P-075-C_tr_sm"],"source_anchors":[{"path":"stage3/canonical/CURRENT.md","git":"4279cd5e01f75401a9f5fa12d42961fe46b9ac8b","anchor":"### P-075 — exact transition smoothing"}],"hypotheses":[],"witnesses":[{"key":"C_tr_sm","type":"Real","depends_on":["theta"]}],"conclusions":[{"key":"result","proposition":{"def":{"id":"S-P-075","args":[{"var":"theta"},{"var":"C_tr_sm"}]}}}],"premises":[{"id":"MAP-P075-P050-1","producer":"P-050","closure_role":"REQUIRED","scope_binders":[{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"},{"key":"x","type":"Real"}],"binder_map":{"theta":{"var":"theta"},"y":{"var":"y"},"k":{"var":"k"},"sigma":{"var":"sigma"},"x":{"var":"x"}},"hypothesis_map":{"theta_ge_2":{"guard":"MAP-P075-P050-1_theta_ge_2"},"y_pos":{"guard":"MAP-P075-P050-1_y_pos"},"y_lt_1":{"guard":"MAP-P075-P050-1_y_lt_1"},"k_ge_1":{"guard":"MAP-P075-P050-1_k_ge_1"},"sigma_ge_theta":{"guard":"MAP-P075-P050-1_sigma_ge_theta"},"x_range":{"guard":"MAP-P075-P050-1_x_range"}},"witness_map":{},"consume":["four_variable_inversion"],"guards":[{"key":"MAP-P075-P050-1_theta_ge_2","proposition":{"op":{"name":"ge","args":[{"var":"theta"},{"lit":{"type":"Real","value":"2"}}]}}},{"key":"MAP-P075-P050-1_y_pos","proposition":{"op":{"name":"gt","args":[{"var":"y"},{"lit":{"type":"Real","value":"0"}}]}}},{"key":"MAP-P075-P050-1_y_lt_1","proposition":{"op":{"name":"lt","args":[{"var":"y"},{"lit":{"type":"Real","value":"1"}}]}}},{"key":"MAP-P075-P050-1_k_ge_1","proposition":{"op":{"name":"ge","args":[{"var":"k"},{"lit":{"type":"Nat","value":"1"}}]}}},{"key":"MAP-P075-P050-1_sigma_ge_theta","proposition":{"op":{"name":"ge","args":[{"var":"sigma"},{"var":"theta"}]}}},{"key":"MAP-P075-P050-1_x_range","proposition":{"op":{"name":"gt","args":[{"var":"x"},{"op":{"name":"pow_nat","args":[{"var":"theta"},{"def":{"id":"D-S7A-TWO-K-MINUS-ONE","args":[{"var":"k"}]}}]}}]}}}]},{"id":"MAP-P075-P052-2","producer":"A-LATE-P052-EXISTS","closure_role":"REQUIRED","scope_binders":[{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"},{"key":"x","type":"Real"},{"key":"t","type":"Nat"},{"key":"d","type":"Nat"},{"key":"d_prime","type":"Nat"}],"binder_map":{"theta":{"var":"theta"},"y":{"var":"y"},"k":{"var":"k"},"sigma":{"var":"sigma"},"K_sh":{"op":{"name":"mul","args":[{"var":"t"},{"op":{"name":"mul","args":[{"var":"d"},{"var":"d_prime"}]}}]}},"z":{"op":{"name":"div","args":[{"var":"x"},{"cast":{"value":{"op":{"name":"mul","args":[{"var":"t"},{"op":{"name":"mul","args":[{"var":"d"},{"var":"d_prime"}]}}]}},"to":"Real"}}]}}},"hypothesis_map":{"domain":{"guard":"MAP-P075-P052-2_domain"},"family_domain":{"guard":"MAP-P075-P052-2_family_domain"}},"witness_map":{},"consume":["existentialized"],"guards":[{"key":"MAP-P075-P052-2_domain","proposition":{"def":{"id":"D-S7B-P052-DOMAIN","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"},{"op":{"name":"mul","args":[{"var":"t"},{"op":{"name":"mul","args":[{"var":"d"},{"var":"d_prime"}]}}]}},{"op":{"name":"div","args":[{"var":"x"},{"cast":{"value":{"op":{"name":"mul","args":[{"var":"t"},{"op":{"name":"mul","args":[{"var":"d"},{"var":"d_prime"}]}}]}},"to":"Real"}}]}}]}}},{"key":"MAP-P075-P052-2_family_domain","proposition":{"def":{"id":"D-S7-P051V-DOMAIN","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"}]}}}]},{"id":"MAP-P075-P051F1-3","producer":"P-051F1","closure_role":"REQUIRED","binder_map":{},"hypothesis_map":{},"witness_map":{"c_1":"p_075_p_051f1_3_c_1","C_1":"p_075_p_051f1_3_C_1","Lambda_1":"p_075_p_051f1_3_Lambda_1"},"consume":["weight_type","dominates_base","dominates_shift"]},{"id":"MAP-P075-P051V-4","producer":"P-051V","closure_role":"REQUIRED","scope_binders":[{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"}],"binder_map":{"theta":{"var":"theta"},"y":{"var":"y"},"k":{"var":"k"},"sigma":{"var":"sigma"}},"hypothesis_map":{"theta_ge_2":{"guard":"MAP-P075-P051V-4_theta_ge_2"},"y_pos":{"guard":"MAP-P075-P051V-4_y_pos"},"y_lt_1":{"guard":"MAP-P075-P051V-4_y_lt_1"},"k_ge_1":{"guard":"MAP-P075-P051V-4_k_ge_1"},"sigma_ge_theta":{"guard":"MAP-P075-P051V-4_sigma_ge_theta"}},"witness_map":{},"consume":["modifier_normalization"],"guards":[{"key":"MAP-P075-P051V-4_theta_ge_2","proposition":{"op":{"name":"ge","args":[{"var":"theta"},{"lit":{"type":"Real","value":"2"}}]}}},{"key":"MAP-P075-P051V-4_y_pos","proposition":{"op":{"name":"gt","args":[{"var":"y"},{"lit":{"type":"Real","value":"0"}}]}}},{"key":"MAP-P075-P051V-4_y_lt_1","proposition":{"op":{"name":"lt","args":[{"var":"y"},{"lit":{"type":"Real","value":"1"}}]}}},{"key":"MAP-P075-P051V-4_k_ge_1","proposition":{"op":{"name":"ge","args":[{"var":"k"},{"lit":{"type":"Nat","value":"1"}}]}}},{"key":"MAP-P075-P051V-4_sigma_ge_theta","proposition":{"op":{"name":"ge","args":[{"var":"sigma"},{"var":"theta"}]}}}]}],"witness_realizations":{"C_tr_sm":{"def":{"id":"W-P-075-C_tr_sm","args":[{"var":"theta"},{"def":{"id":"D-S7B-P052-W","args":[{"var":"theta"}]}},{"var":"p_075_p_051f1_3_c_1"},{"var":"p_075_p_051f1_3_C_1"},{"var":"p_075_p_051f1_3_Lambda_1"}]}}},"proof_ref":"### P-075 — exact transition smoothing"}
```

- Prenex statement:
  \[
  \forall\theta\ge2\;\exists C_{\rm tr,sm}(\theta)>0\;
  \forall y\in(0,1)\;\forall k\ge1\;\forall\sigma\in(\theta^k,\theta^{k+1})\;
  \forall x>\theta^{2k-1},\quad
  S_k(x,y;\sigma,\theta)\le C_{\rm tr,sm}(\theta)V_k.
  \]
- Local equalities: \(z_m=x/(mdd')\); V is D-021a/D-021b/D-021c/D-021d/D-021e.
- Domain/range: constant precedes every uniform variable and summation index.
- Input subject: exact P-050 transition inversion. Output: exact V.
- Premise maps:
  - P-050 — Binders:
    \(y:=y,k:=k,\sigma:=\sigma,\theta:=\theta,x:=x\).
    Hypotheses: transition domain. Consumed: exact inversion.
    Subject: literal S. Constants: none.
  - P-052 — Binders:
    \(\theta:=\theta,y:=y,k:=k,\sigma:=\sigma,
    K_{\rm sh}:=tdd',z:=x/(tdd')\).
    Hypotheses: positivity. Consumed: reciprocal smoothing.
    Subject: innermost reciprocal sum. Constants:
    \(C_{\rm sm}(\theta)\mapsto C_{\rm tr,sm}(\theta)\), uniform in all indices.
  - `MAP-P075-P051F1`: consume only the exact D-015 identity and
    nonnegativity of \(w_1\).
  - `MAP-P075-P051V-MODIFIER`: bind \((\theta,y,k,\sigma)\) identically;
    the transition domains are mapped literally as
    \(\theta\ge2\), \(y\in(0,1)\), \(k\in\mathbb N_{\ge1}\), and
    \(\sigma\in(\theta^k,\theta^{k+1})\), which discharges
    \(\sigma\ge\theta\). Consume from P-051V only the exact D-015 identity,
    nonnegativity, and multiplicativity of \(v_k\).
    Together these identify the post-factorization inner sum with D-016;
    neither normalization, the prime-power bound, a weight type, common
    witnesses, nor Euler tails are consumed.
- Derivation certificate: apply smoothing, factor the weight using
  multiplicativity of D-002 and complete additivity of D-003, and interchange
  the finite nonnegative \(m,t\)-sums.
- Source/S2 anchor: ET pp. 29–30; S2 R2.5c.
- Definitions used: D-015, D-016, D-017, D-021a/D-021b/D-021c/D-021d/D-021e.

### P-076 — exact transition partition

```mathminer-s3
{"schema":"mathminer.s3/1","id":"P-076","kind":"PROPOSITION","binders":[{"key":"theta","type":"Real"},{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"},{"key":"x","type":"Real"}],"uses_definitions":["D-021a","D-021b","S-P-076"],"source_anchors":[{"path":"stage3/canonical/CURRENT.md","git":"4279cd5e01f75401a9f5fa12d42961fe46b9ac8b","anchor":"### P-076 — exact transition partition"}],"hypotheses":[],"witnesses":[],"conclusions":[{"key":"result","proposition":{"def":{"id":"S-P-076","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"},{"var":"x"}]}}}],"premises":[],"witness_realizations":{},"proof_ref":"### P-076 — exact transition partition"}
```

- Prenex statement: for every \(y\in(0,1)\), \(k\ge1\), \(\theta\ge2\),
  \(\sigma\in(\theta^k,\theta^{k+1})\), and \(x>\theta^{2k-1}\),
  \(V_k=V_k^\ge+V_k^<\).
- Local equalities: \(z_m=x/(mdd')\).
- Domain/range: \(z_m\ge\sigma\) and \(z_m<\sigma\) are disjoint/exhaustive.
- Input subject: exact V. Output: exact equality.
- Premise maps: none (root partition proposition).
- Derivation certificate: dichotomy on \(z_m\).
- Source/S2 anchor: S2 R2.5c.
- Definitions used: D-021a/D-021b/D-021c/D-021d/D-021e.

### P-077 — transition high-regime substitution

Current construction binding: the exact `P077Statement` in the GroupA--GroupD source contracts, W0--W8, and the retained S7 provider. Any `mathminer-s3-legacy` block here is historical, not a proof.

```mathminer-s3-legacy
{"schema":"mathminer.s3/1","id":"P-077","kind":"PROPOSITION","binders":[{"key":"theta","type":"Real"}],"uses_definitions":["D-015","D-021b","D-021c","D-LATE-P051F2-W","D-LATE-P051G-W","D-S45-P005-C","D-S45-P007-CMINUS","D-S45-P007-CPLUS","D-S45-P007-DOMAIN","D-S45-P007-PERR","D-S45-P008-CMINUS","D-S45-P008-CPLUS","D-S45-P008-DOMAIN","D-S45-SHIFT-FAMILY-DOMAIN","D-S7A-MODIFIER","D-S7A-PRIME","D-S7A-SELECTED-WEIGHT","D-S811-CERR","D-S811-ETA","D-S811-LAMBDA-SEQ","D-S811-P077-C-0","D-S811-P077-C-HI","D-S811-P077-L-0","D-S811-P077-L-HI","D-S811-P077-POINT-0","D-S811-P077-POINT-HI","D-S811-P077-Q","D-S811-P077-W","D-S811-Q","S-P-077","W-P-077-C_tr_ge"],"source_anchors":[{"path":"stage3/canonical/CURRENT.md","git":"4279cd5e01f75401a9f5fa12d42961fe46b9ac8b","anchor":"### P-077 — transition high-regime substitution"}],"hypotheses":[],"witnesses":[{"key":"C_tr_ge","type":"Real","depends_on":["theta"]}],"conclusions":[{"key":"result","proposition":{"def":{"id":"S-P-077","args":[{"var":"theta"},{"var":"C_tr_ge"}]}}}],"premises":[{"id":"MAP-P077-P005-1","producer":"A-S7-P005-EXISTS","closure_role":"REQUIRED","scope_binders":[{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"},{"key":"x","type":"Real"},{"key":"d","type":"Nat"},{"key":"d_prime","type":"Nat"},{"key":"m","type":"Nat"}],"binder_map":{"lambda_seq":{"def":{"id":"D-S811-LAMBDA-SEQ","args":[]}},"lambda":{"lit":{"type":"Real","value":"1"}},"u":{"proj":{"value":{"def":{"id":"D-015","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"}]}},"index":2}},"v":{"proj":{"value":{"def":{"id":"D-015","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"}]}},"index":1}},"K_sh":{"op":{"name":"mul","args":[{"var":"d"},{"var":"d_prime"}]}},"X":{"op":{"name":"div","args":[{"var":"x"},{"cast":{"value":{"op":{"name":"mul","args":[{"var":"m"},{"op":{"name":"mul","args":[{"var":"d"},{"var":"d_prime"}]}}]}},"to":"Real"}}]}}},"hypothesis_map":{"domain":{"guard":"MAP-P077-P005-1_domain"}},"witness_map":{},"consume":["shifted_mean_exists"],"guards":[{"key":"MAP-P077-P005-1_domain","proposition":{"def":{"id":"D-S45-SHIFT-FAMILY-DOMAIN","args":[{"def":{"id":"D-S811-LAMBDA-SEQ","args":[]}},{"lit":{"type":"Real","value":"1"}},{"proj":{"value":{"def":{"id":"D-015","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"}]}},"index":2}},{"proj":{"value":{"def":{"id":"D-015","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"}]}},"index":1}},{"op":{"name":"mul","args":[{"var":"d"},{"var":"d_prime"}]}},{"op":{"name":"div","args":[{"var":"x"},{"cast":{"value":{"op":{"name":"mul","args":[{"var":"m"},{"op":{"name":"mul","args":[{"var":"d"},{"var":"d_prime"}]}}]}},"to":"Real"}}]}}]}}}]},{"id":"MAP-P077-P007-0","producer":"A-S45-P007-EXISTS","closure_role":"REQUIRED","scope_binders":[{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"},{"key":"z","type":"Real"}],"binder_map":{"c":{"lit":{"type":"Real","value":"0"}},"eta":{"def":{"id":"D-S811-ETA","args":[]}},"C_err":{"def":{"id":"D-S811-CERR","args":[]}},"L":{"def":{"id":"D-S811-P077-POINT-0","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"},{"var":"z"}]}}},"hypothesis_map":{"domain":{"guard":"MAP-P077-P007-0_domain"}},"witness_map":{},"consume":["existentialized"],"guards":[{"key":"MAP-P077-P007-0_domain","proposition":{"def":{"id":"D-S45-P007-DOMAIN","args":[{"lit":{"type":"Real","value":"0"}},{"def":{"id":"D-S811-ETA","args":[]}},{"def":{"id":"D-S811-CERR","args":[]}},{"def":{"id":"D-S811-P077-POINT-0","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"},{"var":"z"}]}}]}}}]},{"id":"MAP-P077-P008-0","producer":"A-S45-P008-EXISTS","closure_role":"REQUIRED","scope_binders":[{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"},{"key":"z","type":"Real"}],"binder_map":{"Q":{"type":{"named":{"id":"D-S811-P077-Q","args":[{"var":"theta"}]}}},"c_minus":{"lit":{"type":"Real","value":"0"}},"c_plus":{"lit":{"type":"Real","value":"1/2"}},"eta_star":{"def":{"id":"D-S811-ETA","args":[]}},"C_err_star":{"def":{"id":"D-S811-CERR","args":[]}},"P_0":{"lit":{"type":"Real","value":"2"}},"m_fin":{"lit":{"type":"Real","value":"1"}},"M_fin":{"lit":{"type":"Real","value":"1"}},"coeff":{"def":{"id":"D-S811-P077-C-0","args":[{"var":"theta"}]}},"local_factor":{"def":{"id":"D-S811-P077-L-0","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"}]}}},"hypothesis_map":{"domain":{"guard":"MAP-P077-P008-0_domain"}},"witness_map":{},"consume":["existentialized"],"guards":[{"key":"MAP-P077-P008-0_domain","proposition":{"def":{"id":"D-S45-P008-DOMAIN","args":[{"type":{"named":{"id":"D-S811-P077-Q","args":[{"var":"theta"}]}}},{"lit":{"type":"Real","value":"0"}},{"lit":{"type":"Real","value":"1/2"}},{"def":{"id":"D-S811-ETA","args":[]}},{"def":{"id":"D-S811-CERR","args":[]}},{"lit":{"type":"Real","value":"2"}},{"lit":{"type":"Real","value":"1"}},{"lit":{"type":"Real","value":"1"}},{"def":{"id":"D-S811-P077-C-0","args":[{"var":"theta"}]}},{"def":{"id":"D-S811-P077-L-0","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"}]}}]}}}]},{"id":"MAP-P077-P007-HI","producer":"A-S45-P007-EXISTS","closure_role":"REQUIRED","scope_binders":[{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"},{"key":"z","type":"Real"}],"binder_map":{"c":{"lit":{"type":"Real","value":"1/2"}},"eta":{"def":{"id":"D-S811-ETA","args":[]}},"C_err":{"def":{"id":"D-S811-CERR","args":[]}},"L":{"def":{"id":"D-S811-P077-POINT-HI","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"},{"var":"z"}]}}},"hypothesis_map":{"domain":{"guard":"MAP-P077-P007-HI_domain"}},"witness_map":{},"consume":["existentialized"],"guards":[{"key":"MAP-P077-P007-HI_domain","proposition":{"def":{"id":"D-S45-P007-DOMAIN","args":[{"lit":{"type":"Real","value":"1/2"}},{"def":{"id":"D-S811-ETA","args":[]}},{"def":{"id":"D-S811-CERR","args":[]}},{"def":{"id":"D-S811-P077-POINT-HI","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"},{"var":"z"}]}}]}}}]},{"id":"MAP-P077-P008-HI","producer":"A-S45-P008-EXISTS","closure_role":"REQUIRED","scope_binders":[{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"},{"key":"z","type":"Real"}],"binder_map":{"Q":{"type":{"named":{"id":"D-S811-P077-Q","args":[{"var":"theta"}]}}},"c_minus":{"lit":{"type":"Real","value":"0"}},"c_plus":{"lit":{"type":"Real","value":"1/2"}},"eta_star":{"def":{"id":"D-S811-ETA","args":[]}},"C_err_star":{"def":{"id":"D-S811-CERR","args":[]}},"P_0":{"lit":{"type":"Real","value":"2"}},"m_fin":{"lit":{"type":"Real","value":"1"}},"M_fin":{"lit":{"type":"Real","value":"1"}},"coeff":{"def":{"id":"D-S811-P077-C-HI","args":[{"var":"theta"}]}},"local_factor":{"def":{"id":"D-S811-P077-L-HI","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"},{"var":"z"}]}}},"hypothesis_map":{"domain":{"guard":"MAP-P077-P008-HI_domain"}},"witness_map":{},"consume":["existentialized"],"guards":[{"key":"MAP-P077-P008-HI_domain","proposition":{"def":{"id":"D-S45-P008-DOMAIN","args":[{"type":{"named":{"id":"D-S811-P077-Q","args":[{"var":"theta"}]}}},{"lit":{"type":"Real","value":"0"}},{"lit":{"type":"Real","value":"1/2"}},{"def":{"id":"D-S811-ETA","args":[]}},{"def":{"id":"D-S811-CERR","args":[]}},{"lit":{"type":"Real","value":"2"}},{"lit":{"type":"Real","value":"1"}},{"lit":{"type":"Real","value":"1"}},{"def":{"id":"D-S811-P077-C-HI","args":[{"var":"theta"}]}},{"def":{"id":"D-S811-P077-L-HI","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"},{"var":"z"}]}}]}}}]},{"id":"MAP-P077-P051F2-4","producer":"A-LATE-P051F2-EXISTS","closure_role":"REQUIRED","scope_binders":[{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"}],"binder_map":{"theta":{"var":"theta"},"y":{"var":"y"},"k":{"var":"k"},"sigma":{"var":"sigma"}},"hypothesis_map":{"theta_ge_2":{"guard":"MAP-P077-P051F2-4_theta_ge_2"},"y_pos":{"guard":"MAP-P077-P051F2-4_y_pos"},"y_lt_1":{"guard":"MAP-P077-P051F2-4_y_lt_1"},"k_ge_1":{"guard":"MAP-P077-P051F2-4_k_ge_1"},"sigma_ge_theta":{"guard":"MAP-P077-P051F2-4_sigma_ge_theta"}},"witness_map":{},"consume":["existentialized"],"guards":[{"key":"MAP-P077-P051F2-4_theta_ge_2","proposition":{"op":{"name":"ge","args":[{"var":"theta"},{"lit":{"type":"Real","value":"2"}}]}}},{"key":"MAP-P077-P051F2-4_y_pos","proposition":{"op":{"name":"gt","args":[{"var":"y"},{"lit":{"type":"Real","value":"0"}}]}}},{"key":"MAP-P077-P051F2-4_y_lt_1","proposition":{"op":{"name":"lt","args":[{"var":"y"},{"lit":{"type":"Real","value":"1"}}]}}},{"key":"MAP-P077-P051F2-4_k_ge_1","proposition":{"op":{"name":"ge","args":[{"var":"k"},{"lit":{"type":"Nat","value":"1"}}]}}},{"key":"MAP-P077-P051F2-4_sigma_ge_theta","proposition":{"op":{"name":"ge","args":[{"var":"sigma"},{"var":"theta"}]}}}]},{"id":"MAP-P077-P051F1-5","producer":"P-051F1","closure_role":"REQUIRED","binder_map":{},"hypothesis_map":{},"witness_map":{"c_1":"p_077_p_051f1_5_c_1","C_1":"p_077_p_051f1_5_C_1","Lambda_1":"p_077_p_051f1_5_Lambda_1"},"consume":["weight_type","dominates_base","dominates_shift"]},{"id":"MAP-P077-P051V-6","producer":"P-051V","closure_role":"REQUIRED","scope_binders":[{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"}],"binder_map":{"theta":{"var":"theta"},"y":{"var":"y"},"k":{"var":"k"},"sigma":{"var":"sigma"}},"hypothesis_map":{"theta_ge_2":{"guard":"MAP-P077-P051V-6_theta_ge_2"},"y_pos":{"guard":"MAP-P077-P051V-6_y_pos"},"y_lt_1":{"guard":"MAP-P077-P051V-6_y_lt_1"},"k_ge_1":{"guard":"MAP-P077-P051V-6_k_ge_1"},"sigma_ge_theta":{"guard":"MAP-P077-P051V-6_sigma_ge_theta"}},"witness_map":{},"consume":["modifier_normalization"],"guards":[{"key":"MAP-P077-P051V-6_theta_ge_2","proposition":{"op":{"name":"ge","args":[{"var":"theta"},{"lit":{"type":"Real","value":"2"}}]}}},{"key":"MAP-P077-P051V-6_y_pos","proposition":{"op":{"name":"gt","args":[{"var":"y"},{"lit":{"type":"Real","value":"0"}}]}}},{"key":"MAP-P077-P051V-6_y_lt_1","proposition":{"op":{"name":"lt","args":[{"var":"y"},{"lit":{"type":"Real","value":"1"}}]}}},{"key":"MAP-P077-P051V-6_k_ge_1","proposition":{"op":{"name":"ge","args":[{"var":"k"},{"lit":{"type":"Nat","value":"1"}}]}}},{"key":"MAP-P077-P051V-6_sigma_ge_theta","proposition":{"op":{"name":"ge","args":[{"var":"sigma"},{"var":"theta"}]}}}]},{"id":"MAP-P077-P051G-7","producer":"A-LATE-P051G-EXISTS","closure_role":"REQUIRED","scope_binders":[{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"}],"binder_map":{"theta":{"var":"theta"},"y":{"var":"y"},"k":{"var":"k"},"sigma":{"var":"sigma"}},"hypothesis_map":{"theta_ge_2":{"guard":"MAP-P077-P051G-7_theta_ge_2"},"y_pos":{"guard":"MAP-P077-P051G-7_y_pos"},"y_lt_1":{"guard":"MAP-P077-P051G-7_y_lt_1"},"k_ge_1":{"guard":"MAP-P077-P051G-7_k_ge_1"},"sigma_ge_theta":{"guard":"MAP-P077-P051G-7_sigma_ge_theta"}},"witness_map":{},"consume":["existentialized"],"guards":[{"key":"MAP-P077-P051G-7_theta_ge_2","proposition":{"op":{"name":"ge","args":[{"var":"theta"},{"lit":{"type":"Real","value":"2"}}]}}},{"key":"MAP-P077-P051G-7_y_pos","proposition":{"op":{"name":"gt","args":[{"var":"y"},{"lit":{"type":"Real","value":"0"}}]}}},{"key":"MAP-P077-P051G-7_y_lt_1","proposition":{"op":{"name":"lt","args":[{"var":"y"},{"lit":{"type":"Real","value":"1"}}]}}},{"key":"MAP-P077-P051G-7_k_ge_1","proposition":{"op":{"name":"ge","args":[{"var":"k"},{"lit":{"type":"Nat","value":"1"}}]}}},{"key":"MAP-P077-P051G-7_sigma_ge_theta","proposition":{"op":{"name":"ge","args":[{"var":"sigma"},{"var":"theta"}]}}}]},{"id":"MAP-P077-P051H-8","producer":"A-LATE-P051H-EXISTS","closure_role":"REQUIRED","scope_binders":[{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"},{"key":"p","type":"Nat"}],"binder_map":{"theta":{"var":"theta"},"y":{"var":"y"},"k":{"var":"k"},"sigma":{"var":"sigma"},"w":{"proj":{"value":{"def":{"id":"D-015","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"}]}},"index":2}},"b":{"proj":{"value":{"def":{"id":"D-015","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"}]}},"index":1}},"p":{"var":"p"}},"hypothesis_map":{"theta_ge_2":{"guard":"MAP-P077-P051H-8_theta_ge_2"},"y_pos":{"guard":"MAP-P077-P051H-8_y_pos"},"y_lt_1":{"guard":"MAP-P077-P051H-8_y_lt_1"},"k_ge_1":{"guard":"MAP-P077-P051H-8_k_ge_1"},"sigma_ge_theta":{"guard":"MAP-P077-P051H-8_sigma_ge_theta"},"selected_weight":{"guard":"MAP-P077-P051H-8_selected_weight"},"modifier_b":{"guard":"MAP-P077-P051H-8_modifier_b"},"prime_p":{"guard":"MAP-P077-P051H-8_prime_p"}},"witness_map":{},"consume":["existentialized"],"guards":[{"key":"MAP-P077-P051H-8_theta_ge_2","proposition":{"op":{"name":"ge","args":[{"var":"theta"},{"lit":{"type":"Real","value":"2"}}]}}},{"key":"MAP-P077-P051H-8_y_pos","proposition":{"op":{"name":"gt","args":[{"var":"y"},{"lit":{"type":"Real","value":"0"}}]}}},{"key":"MAP-P077-P051H-8_y_lt_1","proposition":{"op":{"name":"lt","args":[{"var":"y"},{"lit":{"type":"Real","value":"1"}}]}}},{"key":"MAP-P077-P051H-8_k_ge_1","proposition":{"op":{"name":"ge","args":[{"var":"k"},{"lit":{"type":"Nat","value":"1"}}]}}},{"key":"MAP-P077-P051H-8_sigma_ge_theta","proposition":{"op":{"name":"ge","args":[{"var":"sigma"},{"var":"theta"}]}}},{"key":"MAP-P077-P051H-8_selected_weight","proposition":{"def":{"id":"D-S7A-SELECTED-WEIGHT","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"},{"proj":{"value":{"def":{"id":"D-015","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"}]}},"index":2}}]}}},{"key":"MAP-P077-P051H-8_modifier_b","proposition":{"def":{"id":"D-S7A-MODIFIER","args":[{"proj":{"value":{"def":{"id":"D-015","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"}]}},"index":1}}]}}},{"key":"MAP-P077-P051H-8_prime_p","proposition":{"def":{"id":"D-S7A-PRIME","args":[{"var":"p"}]}}}]}],"witness_realizations":{"C_tr_ge":{"def":{"id":"D-S811-P077-W","args":[{"var":"theta"}]}}},"proof_ref":"### P-077 — transition high-regime substitution"}
```

- Prenex statement:
  \[
  \forall\theta\ge2\;\exists C_{\rm tr,\ge}(\theta)>0\;
  \forall y\in(0,1)\;\forall k\ge1\;
  \forall\sigma\in(\theta^k,\theta^{k+1})\;
  \forall x>\theta^{2k-1},\quad
  V_k^\ge\le C_{\rm tr,\ge}(\theta)\widetilde H_k.
  \]
- Local equalities: \(K_{\rm sh}=dd'\), \(z=z_m=x/(mdd')\).
- Domain/range: exact \(z_m\ge\sigma\) branch.
- Input subject: \(V^\ge\). Output: exact \(\widetilde H\).
- Premise maps:
  - `MAP-P077-P005`:

    | producer | slot | domain | consumer term | evidence |
    |---|---|---|---|---|
    | P-005 | `u` | nonnegative multiplicative | \(w_1\) | P-051F1 |
    | P-005 | `v` | nonnegative multiplicative, normalized by `v(1)=1` | \(v_k\) | P-051V full-domain multiplicativity and normalization |
    | P-005 | `K_sh` | \(\mathbb N_{>0}\) | \(dd'\) | positive outer indices |
    | P-005 | `X` | \(\mathbb R_{\ge2}\) | \(z_m\) | branch gives \(z_m\ge\sigma>\theta^k\ge2\) |
    | P-005 | `(lambda_i)` | nonnegative sequence | \(\lambda_i:=\Lambda_*\) for all \(i\) | P-051G |
    | P-005 | `lambda` | \([0,2)\) | \(1\) | P-051V full prime-power bound |

    Producer hypothesis is P-051G's common local bound. Consumed conclusion is
    P-005's exact shifted estimate. Subject is the literal
    `SUB-T`; the constant uses only \((\Lambda_*,1)\) and is
    uniform in \((\theta,y,k,\sigma,x,d,d',m)\).
  - `MAP-P077-P007` (two applications):

    | producer | slot | domain | consumer term tuple | evidence |
    |---|---|---|---|---|
    | P-007 | `c` | \(\mathbb R\) | \((0,1/2)\) | transition coefficients |
    | P-007 | `eta` | \(>0\) | \((\eta_*,\eta_*)\), \(\eta_*:=\min(c_*,1)\) | P-051H |
    | P-007 | `C_err` | \(>0\) | \((C_E,C_E)\), \(C_E:=C_{E,*}=C_*+2\Lambda_*\) | common error |
    | P-007 | `(L_p)` | positive prime family | \(L_p:=\sum_{j\ge0}w_1(p^j)v_k(p^j)p^{-j}\) | constant term 1 |
    | P-007 | `A` | \(\ge2\) | \((2,\sigma)\) | \(2\le\sigma\le z_m\) |
    | P-007 | `B` | \(\ge2\) | \((\sigma,z_m)\) | same chain |

    In each application extend the displayed Euler factor by the exact model
    \(1+c/p\) outside its consumed interval; P051H-main then discharges the
    global P-007 hypothesis without altering the interval product. Transition roughness gives
    \(\Omega(t,\theta^k)=0\) on nonzero terms and hence these coefficients.
    `AD-P077-EULER-SPLIT` is the literal two-range product identity.
  - `MAP-P077-P008`: before making the termwise substitution
    \(z=z_m=x/(mdd')\), define the abstract endpoint-indexed family
    \[
    Q_{\rm tr,hi}:=\{q=(\theta,y,k,\sigma,z):\theta\ge2,\ 0<y<1,
    k\ge1,\ \theta^k<\sigma<\theta^{k+1},\ z\ge\sigma\}.
    \]
    For \(q=(\theta,y,k,\sigma,z)\in Q_{\rm tr,hi}\), let
    \(E_{q,p}:=\sum_{j\ge0}w_1(p^j)v_k(p^j)p^{-j}\), where D-015 is
    determined by \((\theta,y,k,\sigma)\), and define
    \[
    L^{\rm tr,0}_{q,p}:=
    \begin{cases}E_{q,p},&2\le p<\sigma,\\1,&\text{otherwise},\end{cases}
    \quad
    L^{\rm tr,hi}_{q,p}:=
    \begin{cases}E_{q,p},&\sigma\le p<z,\\1+1/(2p),&\text{otherwise}.
    \end{cases}
    \tag{L077-family}
    \]
    These are global positive families and literal functions of \((q,p)\)
    alone. Apply P-008 with coefficient maps \(q\mapsto0,q\mapsto1/2\),
    \(c_-:=0,c_+:=1/2\), \(\eta_*:=\min(c_*,1)\),
    \(C_{\rm err,*}:=C_{E,*},P_0:=2\), and
    \(m_{\rm fin}:=M_{\rm fin}:=1\). P051H-main supplies the common error on
    each active interval, the exact-model branches have zero error, and the
    finite prefix is vacuous. Thus the error, prefix, coefficient, and
    positivity data are independent of \(z\). The consumed conclusions
    assemble by `AD-P077-EULER-SPLIT`, with their constants chosen after the
    whole \(Q_{\rm tr,hi}\)-indexed family and before \((q,A,B)\).

    Only now, for a term of \(V_k^{\ge}\), instantiate
    \(z:=z_m=x/(mdd')\). Positivity of \(x,m,d,d'\) defines \(z_m>0\), and
    the high-branch predicate supplies \(z_m\ge\sigma\); hence
    \((\theta,y,k,\sigma,z_m)\in Q_{\rm tr,hi}\). This substitution introduces
    no new constant dependence on \(x,m,d,d'\), and licenses one
    \(C_{\rm tr,\ge}(\theta)\) before \(y,k,\sigma,x\).

    | producer | slot | domain | consumer term tuple | evidence |
    |---|---|---|---|---|
    | P-008 | `Q` | nonempty index set | \(Q_{\rm tr,hi}\) | e.g. \((2,1/2,1,3,3)\) |
    | P-008 | `c_-` | \(\mathbb R\) | \(0\) | common lower endpoint |
    | P-008 | `c_+` | \(\mathbb R\), \(c_-\le c_+\), \(1+c_-/2>0\) | \(1/2\) | admissible compact interval |
    | P-008 | `eta_*` | \(\mathbb R_{>0}\) | \(\min(c_*,1)\) | P-051H |
    | P-008 | `C_err,*` | \(\mathbb R_{>0}\) | \(C_{E,*}\) | P051H-main |
    | P-008 | `P_0` | \(\mathbb R_{\ge2}\) | \(2\) | literal |
    | P-008 | `m_fin` | \(\mathbb R_{>0}\) | \(1\) | empty prefix |
    | P-008 | `M_fin` | \(\mathbb R_{\ge m_{\rm fin}}\) | \(1\) | empty prefix |
    | P-008 | `c` | maps into \([0,1/2]\) | \((q\mapsto0,q\mapsto1/2)\) | literal transition coefficients |
    | P-008 | `L` | positive factor families | \((L^{\rm tr,0}_{q,p},L^{\rm tr,hi}_{q,p})\) from (L077-family) | literal functions of \((q,p)\); P051H-main |
    | P-008 | `q` | \(Q_{\rm tr,hi}\) | first \((\theta,y,k,\sigma,z)\), then \(z:=z_m=x/(mdd')\) | complete transition-high tuple, including the active endpoint |
    | P-008 | `A` | \(\mathbb R_{\ge2}\) | \((2,\sigma)\) | transition endpoints |
    | P-008 | `B` | \(\mathbb R_{\ge2}\) | \((\sigma,z)\), then \(z:=z_m\) | high branch |
  - `MAP-P077-P051F2`: bind the transition tuple identically and consume the
    exact construction \(w_{2,k}=\widehat{\mathcal S}[w_1,v_k]\) and its
    domination of the P-005 shift factor.
  - `MAP-P077-P051F1`: consume only the exact nonnegative multiplicative
    identity of \(w_1\) used as P-005's first weight.
  - `MAP-P077-P051V`: bind \((\theta,y,k,\sigma)\) identically and consume
    exactly nonnegative multiplicativity of \(v_k\), \(v_k(1)=1\), and the
    full prime-power bound, discharging every P-005 modifier slot.
  - `MAP-P077-P051G`: consume only the common local bounds for \(w_1\).
  - `MAP-P077-P051H`: consume only (P051H-main) for the two transition Euler
    families above with \(b:=v_k\); P-051V supplies the literal modifier
    hypotheses for that specialization.
- Derivation certificate: apply the mapped high transition T-estimate termwise.
- Source/S2 anchor: S2 R2.15 high line and S2B R2(4).
- Definitions used: D-015, D-016, D-021a/D-021b/D-021c/D-021d/D-021e.

### P-078 — transition high weight transport

```mathminer-s3
{"schema":"mathminer.s3/1","id":"P-078","kind":"PROPOSITION","binders":[{"key":"theta","type":"Real"},{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"},{"key":"x","type":"Real"}],"uses_definitions":["D-021c","D-021d","S-P-078"],"source_anchors":[{"path":"stage3/canonical/CURRENT.md","git":"4279cd5e01f75401a9f5fa12d42961fe46b9ac8b","anchor":"### P-078 — transition high weight transport"}],"hypotheses":[],"witnesses":[],"conclusions":[{"key":"result","proposition":{"def":{"id":"S-P-078","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"},{"var":"x"}]}}}],"premises":[{"id":"MAP-P078-P051F3-1","producer":"A-LATE-P051F3-EXISTS","closure_role":"REQUIRED","binder_map":{"theta":{"var":"theta"},"y":{"var":"y"},"k":{"var":"k"},"sigma":{"var":"sigma"}},"hypothesis_map":{"theta_ge_2":{"guard":"MAP-P078-P051F3-1_theta_ge_2"},"y_pos":{"guard":"MAP-P078-P051F3-1_y_pos"},"y_lt_1":{"guard":"MAP-P078-P051F3-1_y_lt_1"},"k_ge_1":{"guard":"MAP-P078-P051F3-1_k_ge_1"},"sigma_ge_theta":{"guard":"MAP-P078-P051F3-1_sigma_ge_theta"}},"witness_map":{},"consume":["existentialized"],"guards":[{"key":"MAP-P078-P051F3-1_theta_ge_2","proposition":{"op":{"name":"ge","args":[{"var":"theta"},{"lit":{"type":"Real","value":"2"}}]}}},{"key":"MAP-P078-P051F3-1_y_pos","proposition":{"op":{"name":"gt","args":[{"var":"y"},{"lit":{"type":"Real","value":"0"}}]}}},{"key":"MAP-P078-P051F3-1_y_lt_1","proposition":{"op":{"name":"lt","args":[{"var":"y"},{"lit":{"type":"Real","value":"1"}}]}}},{"key":"MAP-P078-P051F3-1_k_ge_1","proposition":{"op":{"name":"ge","args":[{"var":"k"},{"lit":{"type":"Nat","value":"1"}}]}}},{"key":"MAP-P078-P051F3-1_sigma_ge_theta","proposition":{"op":{"name":"ge","args":[{"var":"sigma"},{"var":"theta"}]}}}]}],"witness_realizations":{},"proof_ref":"### P-078 — transition high weight transport"}
```

- Prenex statement: for every \(y\in(0,1)\), \(k\ge1\), \(\theta\ge2\),
  \(\sigma\in(\theta^k,\theta^{k+1})\), and \(x>\theta^{2k-1}\),
  \(\widetilde H_k\le H_k\).
- Local equalities: the subjects differ only by \(w_{2,k}\) versus
  \(w_{3,k}\).
- Domain/range: termwise nonnegative comparison.
- Input subject: exact \(\widetilde H\). Output: exact H.
- Premise maps:
  - `MAP-P078-P051F3`: bind the transition tuple identically and consume only
    \(w_{2,k}(dd')\le w_{3,k}(dd')\); the subject is the literal differing
    factor and no constants are introduced.
- Derivation certificate: termwise domination.
- Source/S2 anchor: S2 R2.12 and R2.5c.
- Definitions used: D-021a/D-021b/D-021c/D-021d/D-021e.

### P-079 — transition low-regime substitution

```mathminer-s3
{"schema":"mathminer.s3/1","id":"P-079","kind":"PROPOSITION","binders":[{"key":"theta","type":"Real"},{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"},{"key":"x","type":"Real"}],"uses_definitions":["D-021b","D-021c","D-S7-P051V-DOMAIN","D-S7B-P057-DOMAIN","S-P-079"],"source_anchors":[{"path":"stage3/canonical/CURRENT.md","git":"4279cd5e01f75401a9f5fa12d42961fe46b9ac8b","anchor":"### P-079 — transition low-regime substitution"}],"hypotheses":[],"witnesses":[],"conclusions":[{"key":"result","proposition":{"def":{"id":"S-P-079","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"},{"var":"x"}]}}}],"premises":[{"id":"MAP-P079-P057-1","producer":"P-057","closure_role":"REQUIRED","scope_binders":[{"key":"d","type":"Nat"},{"key":"d_prime","type":"Nat"},{"key":"m","type":"Nat"}],"binder_map":{"theta":{"var":"theta"},"y":{"var":"y"},"k":{"var":"k"},"sigma":{"var":"sigma"},"K_sh":{"op":{"name":"mul","args":[{"var":"d"},{"var":"d_prime"}]}},"z":{"op":{"name":"div","args":[{"var":"x"},{"cast":{"value":{"op":{"name":"mul","args":[{"var":"m"},{"op":{"name":"mul","args":[{"var":"d"},{"var":"d_prime"}]}}]}},"to":"Real"}}]}}},"hypothesis_map":{"domain":{"guard":"MAP-P079-P057-1_domain"},"family_domain":{"guard":"MAP-P079-P057-1_family_domain"}},"witness_map":{},"consume":["terminal_bound"],"guards":[{"key":"MAP-P079-P057-1_domain","proposition":{"def":{"id":"D-S7B-P057-DOMAIN","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"},{"op":{"name":"mul","args":[{"var":"d"},{"var":"d_prime"}]}},{"op":{"name":"div","args":[{"var":"x"},{"cast":{"value":{"op":{"name":"mul","args":[{"var":"m"},{"op":{"name":"mul","args":[{"var":"d"},{"var":"d_prime"}]}}]}},"to":"Real"}}]}}]}}},{"key":"MAP-P079-P057-1_family_domain","proposition":{"def":{"id":"D-S7-P051V-DOMAIN","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"}]}}}]}],"witness_realizations":{},"proof_ref":"### P-079 — transition low-regime substitution"}
```

- Prenex statement: for every \(y\in(0,1)\), \(k\ge1\), \(\theta\ge2\),
  \(\sigma\in(\theta^k,\theta^{k+1})\), and \(x>\theta^{2k-1}\),
  \(V_k^<\le\widetilde L_k\).
- Local equalities: \(K_{\rm sh}=dd'\), \(z=z_m\).
- Domain/range: exact \(z_m<\sigma\) branch.
- Input subject: \(V^<\). Output: exact \(\widetilde L\).
- Premise maps:
  - P-057 — Binders:
    \(y:=y,k:=k,\sigma:=\sigma,\theta:=\theta,
    K_{\rm sh}:=dd',z:=z_m\).
    Hypotheses: \(z_m<\sigma\); the equality uses only roughness.
    Consumed: \(T_k\le w_1\).
    Subject: literal T-factor is bounded by D-021a/D-021b/D-021c/D-021d/D-021e \(\widetilde L\).
    Constants: none.
- Derivation certificate: substitute the endpoint-safe terminal T bound.
- Source/S2 anchor: S2 R2.15 low line.
- Definitions used: D-021a/D-021b/D-021c/D-021d/D-021e.

### P-080 — transition low weight transport

```mathminer-s3
{"schema":"mathminer.s3/1","id":"P-080","kind":"PROPOSITION","binders":[{"key":"theta","type":"Real"},{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"},{"key":"x","type":"Real"}],"uses_definitions":["D-021c","D-021d","S-P-080"],"source_anchors":[{"path":"stage3/canonical/CURRENT.md","git":"4279cd5e01f75401a9f5fa12d42961fe46b9ac8b","anchor":"### P-080 — transition low weight transport"}],"hypotheses":[],"witnesses":[],"conclusions":[{"key":"result","proposition":{"def":{"id":"S-P-080","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"},{"var":"x"}]}}}],"premises":[{"id":"MAP-P080-P051F3-1","producer":"A-LATE-P051F3-EXISTS","closure_role":"REQUIRED","binder_map":{"theta":{"var":"theta"},"y":{"var":"y"},"k":{"var":"k"},"sigma":{"var":"sigma"}},"hypothesis_map":{"theta_ge_2":{"guard":"MAP-P080-P051F3-1_theta_ge_2"},"y_pos":{"guard":"MAP-P080-P051F3-1_y_pos"},"y_lt_1":{"guard":"MAP-P080-P051F3-1_y_lt_1"},"k_ge_1":{"guard":"MAP-P080-P051F3-1_k_ge_1"},"sigma_ge_theta":{"guard":"MAP-P080-P051F3-1_sigma_ge_theta"}},"witness_map":{},"consume":["existentialized"],"guards":[{"key":"MAP-P080-P051F3-1_theta_ge_2","proposition":{"op":{"name":"ge","args":[{"var":"theta"},{"lit":{"type":"Real","value":"2"}}]}}},{"key":"MAP-P080-P051F3-1_y_pos","proposition":{"op":{"name":"gt","args":[{"var":"y"},{"lit":{"type":"Real","value":"0"}}]}}},{"key":"MAP-P080-P051F3-1_y_lt_1","proposition":{"op":{"name":"lt","args":[{"var":"y"},{"lit":{"type":"Real","value":"1"}}]}}},{"key":"MAP-P080-P051F3-1_k_ge_1","proposition":{"op":{"name":"ge","args":[{"var":"k"},{"lit":{"type":"Nat","value":"1"}}]}}},{"key":"MAP-P080-P051F3-1_sigma_ge_theta","proposition":{"op":{"name":"ge","args":[{"var":"sigma"},{"var":"theta"}]}}}]}],"witness_realizations":{},"proof_ref":"### P-080 — transition low weight transport"}
```

- Prenex statement: for every \(y\in(0,1)\), \(k\ge1\), \(\theta\ge2\),
  \(\sigma\in(\theta^k,\theta^{k+1})\), and \(x>\theta^{2k-1}\),
  \(\widetilde L_k\le L_k\).
- Local equalities: subjects differ only by \(w_1\) versus \(w_{3,k}\).
- Domain/range: nonnegative termwise comparison.
- Input subject: exact \(\widetilde L\). Output: exact L.
- Premise maps:
  - `MAP-P080-P051F3`: bind the transition tuple identically and consume only
    \(w_1(dd')\le w_{3,k}(dd')\); the subject is the literal differing
    factor and no constants are introduced.
- Derivation certificate: termwise domination.
- Source/S2 anchor: S2 R2.12 and R2.5c.
- Definitions used: D-021a/D-021b/D-021c/D-021d/D-021e.

### P-081 — transition scale comparison

```mathminer-s3
{"schema":"mathminer.s3/1","id":"P-081","kind":"PROPOSITION","binders":[{"key":"theta","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"}],"uses_definitions":["S-P-081"],"source_anchors":[{"path":"stage3/canonical/CURRENT.md","git":"4279cd5e01f75401a9f5fa12d42961fe46b9ac8b","anchor":"### P-081 — transition scale comparison"}],"hypotheses":[],"witnesses":[],"conclusions":[{"key":"result","proposition":{"def":{"id":"S-P-081","args":[{"var":"theta"},{"var":"k"},{"var":"sigma"}]}}}],"premises":[],"witness_realizations":{},"proof_ref":"### P-081 — transition scale comparison"}
```

- Prenex statement: for every \(k\ge1,\theta\ge2\), and
  \(\theta^k<\sigma<\theta^{k+1}\),
  \[
  k\log\theta<\log\sigma<(k+1)\log\theta,\qquad
  k\asymp_\theta\log\sigma.
  \]
- Local equalities: none.
- Domain/range: positive logarithms.
- Input subject: transition inequalities. Output: exact scale comparison.
- Premise maps: none (root).
- Derivation certificate: take logs and divide by \(\log\theta>0\).
- Source/S2 anchor: S2 R2.5c.
- Definitions used: none.

### P-082 — transition high convolution transport

```mathminer-s3
{"schema":"mathminer.s3/1","id":"P-082","kind":"PROPOSITION","binders":[{"key":"theta","type":"Real"}],"uses_definitions":["D-006","D-021d","D-021e","D-S7B-P054-DOMAIN","S-P-082","W-P-082-C_tr_H"],"source_anchors":[{"path":"stage3/canonical/CURRENT.md","git":"4279cd5e01f75401a9f5fa12d42961fe46b9ac8b","anchor":"### P-082 \u2014 transition high convolution transport"}],"hypotheses":[],"witnesses":[{"key":"C_tr_H","type":"Real","depends_on":["theta"]}],"conclusions":[{"key":"result","proposition":{"def":{"id":"S-P-082","args":[{"var":"theta"},{"var":"C_tr_H"}]}}}],"premises":[{"id":"MAP-P082-P054-1","producer":"P-054","closure_role":"REQUIRED","scope_binders":[{"key":"d","type":"Nat"},{"key":"d_prime","type":"Nat"},{"key":"k","type":"Nat"}],"binder_map":{"d":{"var":"d"},"d_prime":{"var":"d_prime"},"k":{"var":"k"},"theta":{"var":"theta"}},"hypothesis_map":{"domain":{"guard":"MAP-P082-P054-1_domain"}},"witness_map":{},"consume":["close_window"],"guards":[{"key":"MAP-P082-P054-1_domain","proposition":{"def":{"id":"D-S7B-P054-DOMAIN","args":[{"var":"d"},{"var":"d_prime"},{"var":"k"},{"var":"theta"}]}}}]}],"witness_realizations":{"C_tr_H":{"def":{"id":"W-P-082-C_tr_H","args":[{"var":"theta"}]}}},"proof_ref":"### P-082 \u2014 transition high convolution transport"}
```

- Prenex statement:
  \[
  \forall\theta\ge2\;\exists C_{\rm tr,H}(\theta)>0\;
  \forall y\in(0,1)\;\forall k\ge1\;
  \forall\sigma\in(\theta^k,\theta^{k+1})\;
  \forall x>\theta^{2k-1},\quad
  H_k\le C_{\rm tr,H}(\theta)(\log\sigma)^{-1/2}
  x\theta^{-2k}O_k^{\rm tr}.
  \]
- Local equalities: \(z_m=x/(mdd')\).
- Domain/range: strict product window; safe exponent \(-1/2\).
- Input subject: exact H. Output: O-tr times high envelope.
- Premise maps:
  - P-054 — Binders:
    \(d:=d,d':=d',k:=k,\theta:=\theta\) termwise.
    Hypotheses: D-021a/D-021b/D-021c/D-021d/D-021e outer index. Consumed: product window.
    Subject: \(dd'\asymp_\theta\theta^{2k}\); the high restriction only
    shortens the beta convolution. Constants: \(\theta\)-only.
- Derivation certificate: substitute \(z_m=x/(mdd')\); bound the exact inner
  sum by \(C(\theta)x\theta^{-2k}\) using the safe
  \((-1/2,-1/2)\) beta convolution; factor exact \(O_k^{\rm tr}\).
- Source/S2 anchor: ET p. 31; S2 R2.5c.
- Definitions used: D-006, D-021a/D-021b/D-021c/D-021d/D-021e.

### P-083 — transition low convolution transport

```mathminer-s3
{"schema":"mathminer.s3/1","id":"P-083","kind":"PROPOSITION","binders":[{"key":"theta","type":"Real"}],"uses_definitions":["D-006","D-021d","D-021e","D-S7B-P053-DOMAIN","D-S7B-P053-W","D-S7B-P054-DOMAIN","S-P-083","W-P-083-C_tr_L"],"source_anchors":[{"path":"stage3/canonical/CURRENT.md","git":"4279cd5e01f75401a9f5fa12d42961fe46b9ac8b","anchor":"### P-083 \u2014 transition low convolution transport"}],"hypotheses":[],"witnesses":[{"key":"C_tr_L","type":"Real","depends_on":["theta"]}],"conclusions":[{"key":"result","proposition":{"def":{"id":"S-P-083","args":[{"var":"theta"},{"var":"C_tr_L"}]}}}],"premises":[{"id":"MAP-P083-P053-1","producer":"A-LATE-P053-EXISTS","closure_role":"REQUIRED","scope_binders":[{"key":"M","type":"Real"}],"binder_map":{"M":{"var":"M"}},"hypothesis_map":{"domain":{"guard":"MAP-P083-P053-1_domain"}},"witness_map":{},"consume":["existentialized"],"guards":[{"key":"MAP-P083-P053-1_domain","proposition":{"def":{"id":"D-S7B-P053-DOMAIN","args":[{"var":"M"}]}}}]},{"id":"MAP-P083-P054-2","producer":"P-054","closure_role":"REQUIRED","scope_binders":[{"key":"d","type":"Nat"},{"key":"d_prime","type":"Nat"},{"key":"k","type":"Nat"}],"binder_map":{"d":{"var":"d"},"d_prime":{"var":"d_prime"},"k":{"var":"k"},"theta":{"var":"theta"}},"hypothesis_map":{"domain":{"guard":"MAP-P083-P054-2_domain"}},"witness_map":{},"consume":["close_window"],"guards":[{"key":"MAP-P083-P054-2_domain","proposition":{"def":{"id":"D-S7B-P054-DOMAIN","args":[{"var":"d"},{"var":"d_prime"},{"var":"k"},{"var":"theta"}]}}}]}],"witness_realizations":{"C_tr_L":{"def":{"id":"W-P-083-C_tr_L","args":[{"var":"theta"},{"def":{"id":"D-S7B-P053-W","args":[]}}]}}},"proof_ref":"### P-083 \u2014 transition low convolution transport"}
```

- Prenex statement:
  \[
  \forall\theta\ge2\;\exists C_{\rm tr,L}(\theta)>0\;
  \forall y\in(0,1)\;\forall k\ge1\;
  \forall\sigma\in(\theta^k,\theta^{k+1})\;
  \forall x>\theta^{2k-1},\quad
  L_k\le C_{\rm tr,L}(\theta)x\theta^{-2k}
  \ell(2x\theta^{1-2k})^{-1/2}O_k^{\rm tr}.
  \]
- Local equalities: \(z_m=x/(mdd')\).
- Domain/range: exact low restriction may be dropped by nonnegativity.
- Input subject: exact L. Output: O-tr times terminal endpoint.
- Premise maps:
  - P-053 — Binders: \(M:=x/(dd')\). Hypotheses: positivity.
    Consumed: safe partial sum. Subject: exact inner L-sum after dropping
    \(z_m<\sigma\). Constants: absolute.
  - P-054 — Binders:
    \(d:=d,d':=d',k:=k,\theta:=\theta\) termwise.
    Hypotheses: D-021a/D-021b/D-021c/D-021d/D-021e outer index.
    Consumed: product window. Subject:
    \(x/(dd')\asymp_\theta x\theta^{1-2k}\); because the power is
    \(-1/2\), the lower logarithmic comparison gives the upper bound.
    Constants: absorbed into \(C_{\rm tr,L}(\theta)\).
- Derivation certificate: apply P-053, transport the negative-power endpoint,
  and factor \(O_k^{\rm tr}\).
- Source/S2 anchor: ET p. 31; S2 R2.5c.
- Definitions used: D-006, D-021a/D-021b/D-021c/D-021d/D-021e.

### P-084 — transition outer shifted mean

Current construction binding: the exact `P084Statement` in the GroupA--GroupD source contracts, W0--W8, and the retained S7 provider. Any `mathminer-s3-legacy` block here is historical, not a proof.

```mathminer-s3-legacy
{"schema":"mathminer.s3/1","id":"P-084","kind":"PROPOSITION","binders":[{"key":"theta","type":"Real"}],"uses_definitions":["D-002","D-003","D-005","D-015","D-021e","D-LATE-P051F3-W","D-LATE-P051G-W","D-S45-P005-C","D-S45-P007-CMINUS","D-S45-P007-CPLUS","D-S45-P007-DOMAIN","D-S45-P007-PERR","D-S45-P008-CMINUS","D-S45-P008-CPLUS","D-S45-P008-DOMAIN","D-S45-SHIFT-FAMILY-DOMAIN","D-S7A-F4-W","D-S7A-MODIFIER","D-S7A-PRIME","D-S7A-SELECTED-WEIGHT","D-S7B-P054-DOMAIN","D-S7B-P054A-DOMAIN","D-S811-CERR","D-S811-ETA","D-S811-LAMBDA-SEQ","D-S811-P058-G","D-S811-P084-C-0","D-S811-P084-C-HI","D-S811-P084-L-0","D-S811-P084-L-HI","D-S811-P084-POINT-0","D-S811-P084-POINT-HI","D-S811-P084-Q","D-S811-P084-W","D-S811-Q","D-S811-THETA-SUCC","S-P-084","W-P-084-C_tr_out"],"source_anchors":[{"path":"stage3/canonical/CURRENT.md","git":"4279cd5e01f75401a9f5fa12d42961fe46b9ac8b","anchor":"### P-084 — transition outer shifted mean"}],"hypotheses":[],"witnesses":[{"key":"C_tr_out","type":"Real","depends_on":["theta"]}],"conclusions":[{"key":"result","proposition":{"def":{"id":"S-P-084","args":[{"var":"theta"},{"var":"C_tr_out"}]}}}],"premises":[{"id":"MAP-P084-P054A-1","producer":"P-054A","closure_role":"REQUIRED","scope_binders":[{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"},{"key":"d_prime","type":"Nat"}],"binder_map":{"k":{"var":"k"},"theta":{"var":"theta"},"sigma":{"var":"sigma"},"g":{"def":{"id":"D-S811-P058-G","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"},{"var":"d_prime"}]}}},"hypothesis_map":{"domain":{"guard":"MAP-P084-P054A-1_domain"}},"witness_map":{},"consume":["initial_enlargements"],"guards":[{"key":"MAP-P084-P054A-1_domain","proposition":{"def":{"id":"D-S7B-P054A-DOMAIN","args":[{"var":"k"},{"var":"theta"},{"var":"sigma"},{"def":{"id":"D-S811-P058-G","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"},{"var":"d_prime"}]}}]}}}]},{"id":"MAP-P084-P005-2","producer":"A-S7-P005-EXISTS","closure_role":"REQUIRED","scope_binders":[{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"},{"key":"d_prime","type":"Nat"}],"binder_map":{"lambda_seq":{"def":{"id":"D-S811-LAMBDA-SEQ","args":[]}},"lambda":{"lit":{"type":"Real","value":"1"}},"u":{"proj":{"value":{"def":{"id":"D-015","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"}]}},"index":4}},"v":{"proj":{"value":{"def":{"id":"D-015","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"}]}},"index":1}},"K_sh":{"var":"d_prime"},"X":{"def":{"id":"D-S811-THETA-SUCC","args":[{"var":"theta"},{"var":"k"}]}}},"hypothesis_map":{"domain":{"guard":"MAP-P084-P005-2_domain"}},"witness_map":{},"consume":["shifted_mean_exists"],"guards":[{"key":"MAP-P084-P005-2_domain","proposition":{"def":{"id":"D-S45-SHIFT-FAMILY-DOMAIN","args":[{"def":{"id":"D-S811-LAMBDA-SEQ","args":[]}},{"lit":{"type":"Real","value":"1"}},{"proj":{"value":{"def":{"id":"D-015","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"}]}},"index":4}},{"proj":{"value":{"def":{"id":"D-015","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"}]}},"index":1}},{"var":"d_prime"},{"def":{"id":"D-S811-THETA-SUCC","args":[{"var":"theta"},{"var":"k"}]}}]}}}]},{"id":"MAP-P084-P007-0","producer":"A-S45-P007-EXISTS","closure_role":"REQUIRED","scope_binders":[{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"}],"binder_map":{"c":{"lit":{"type":"Real","value":"0"}},"eta":{"def":{"id":"D-S811-ETA","args":[]}},"C_err":{"def":{"id":"D-S811-CERR","args":[]}},"L":{"def":{"id":"D-S811-P084-POINT-0","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"}]}}},"hypothesis_map":{"domain":{"guard":"MAP-P084-P007-0_domain"}},"witness_map":{},"consume":["existentialized"],"guards":[{"key":"MAP-P084-P007-0_domain","proposition":{"def":{"id":"D-S45-P007-DOMAIN","args":[{"lit":{"type":"Real","value":"0"}},{"def":{"id":"D-S811-ETA","args":[]}},{"def":{"id":"D-S811-CERR","args":[]}},{"def":{"id":"D-S811-P084-POINT-0","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"}]}}]}}}]},{"id":"MAP-P084-P008-0","producer":"A-S45-P008-EXISTS","closure_role":"REQUIRED","scope_binders":[{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"}],"binder_map":{"Q":{"type":{"named":{"id":"D-S811-P084-Q","args":[{"var":"theta"}]}}},"c_minus":{"lit":{"type":"Real","value":"0"}},"c_plus":{"lit":{"type":"Real","value":"1/2"}},"eta_star":{"def":{"id":"D-S811-ETA","args":[]}},"C_err_star":{"def":{"id":"D-S811-CERR","args":[]}},"P_0":{"lit":{"type":"Real","value":"2"}},"m_fin":{"lit":{"type":"Real","value":"1"}},"M_fin":{"lit":{"type":"Real","value":"1"}},"coeff":{"def":{"id":"D-S811-P084-C-0","args":[{"var":"theta"}]}},"local_factor":{"def":{"id":"D-S811-P084-L-0","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"}]}}},"hypothesis_map":{"domain":{"guard":"MAP-P084-P008-0_domain"}},"witness_map":{},"consume":["existentialized"],"guards":[{"key":"MAP-P084-P008-0_domain","proposition":{"def":{"id":"D-S45-P008-DOMAIN","args":[{"type":{"named":{"id":"D-S811-P084-Q","args":[{"var":"theta"}]}}},{"lit":{"type":"Real","value":"0"}},{"lit":{"type":"Real","value":"1/2"}},{"def":{"id":"D-S811-ETA","args":[]}},{"def":{"id":"D-S811-CERR","args":[]}},{"lit":{"type":"Real","value":"2"}},{"lit":{"type":"Real","value":"1"}},{"lit":{"type":"Real","value":"1"}},{"def":{"id":"D-S811-P084-C-0","args":[{"var":"theta"}]}},{"def":{"id":"D-S811-P084-L-0","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"}]}}]}}}]},{"id":"MAP-P084-P007-HI","producer":"A-S45-P007-EXISTS","closure_role":"REQUIRED","scope_binders":[{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"}],"binder_map":{"c":{"lit":{"type":"Real","value":"1/2"}},"eta":{"def":{"id":"D-S811-ETA","args":[]}},"C_err":{"def":{"id":"D-S811-CERR","args":[]}},"L":{"def":{"id":"D-S811-P084-POINT-HI","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"}]}}},"hypothesis_map":{"domain":{"guard":"MAP-P084-P007-HI_domain"}},"witness_map":{},"consume":["existentialized"],"guards":[{"key":"MAP-P084-P007-HI_domain","proposition":{"def":{"id":"D-S45-P007-DOMAIN","args":[{"lit":{"type":"Real","value":"1/2"}},{"def":{"id":"D-S811-ETA","args":[]}},{"def":{"id":"D-S811-CERR","args":[]}},{"def":{"id":"D-S811-P084-POINT-HI","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"}]}}]}}}]},{"id":"MAP-P084-P008-HI","producer":"A-S45-P008-EXISTS","closure_role":"REQUIRED","scope_binders":[{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"}],"binder_map":{"Q":{"type":{"named":{"id":"D-S811-P084-Q","args":[{"var":"theta"}]}}},"c_minus":{"lit":{"type":"Real","value":"0"}},"c_plus":{"lit":{"type":"Real","value":"1/2"}},"eta_star":{"def":{"id":"D-S811-ETA","args":[]}},"C_err_star":{"def":{"id":"D-S811-CERR","args":[]}},"P_0":{"lit":{"type":"Real","value":"2"}},"m_fin":{"lit":{"type":"Real","value":"1"}},"M_fin":{"lit":{"type":"Real","value":"1"}},"coeff":{"def":{"id":"D-S811-P084-C-HI","args":[{"var":"theta"}]}},"local_factor":{"def":{"id":"D-S811-P084-L-HI","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"}]}}},"hypothesis_map":{"domain":{"guard":"MAP-P084-P008-HI_domain"}},"witness_map":{},"consume":["existentialized"],"guards":[{"key":"MAP-P084-P008-HI_domain","proposition":{"def":{"id":"D-S45-P008-DOMAIN","args":[{"type":{"named":{"id":"D-S811-P084-Q","args":[{"var":"theta"}]}}},{"lit":{"type":"Real","value":"0"}},{"lit":{"type":"Real","value":"1/2"}},{"def":{"id":"D-S811-ETA","args":[]}},{"def":{"id":"D-S811-CERR","args":[]}},{"lit":{"type":"Real","value":"2"}},{"lit":{"type":"Real","value":"1"}},{"lit":{"type":"Real","value":"1"}},{"def":{"id":"D-S811-P084-C-HI","args":[{"var":"theta"}]}},{"def":{"id":"D-S811-P084-L-HI","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"}]}}]}}}]},{"id":"MAP-P084-P051F4-5","producer":"A-LATE-P051F4-EXISTS","closure_role":"REQUIRED","scope_binders":[{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"}],"binder_map":{"theta":{"var":"theta"},"y":{"var":"y"},"k":{"var":"k"},"sigma":{"var":"sigma"}},"hypothesis_map":{"theta_ge_2":{"guard":"MAP-P084-P051F4-5_theta_ge_2"},"y_pos":{"guard":"MAP-P084-P051F4-5_y_pos"},"y_lt_1":{"guard":"MAP-P084-P051F4-5_y_lt_1"},"k_ge_1":{"guard":"MAP-P084-P051F4-5_k_ge_1"},"sigma_ge_theta":{"guard":"MAP-P084-P051F4-5_sigma_ge_theta"}},"witness_map":{},"consume":["existentialized"],"guards":[{"key":"MAP-P084-P051F4-5_theta_ge_2","proposition":{"op":{"name":"ge","args":[{"var":"theta"},{"lit":{"type":"Real","value":"2"}}]}}},{"key":"MAP-P084-P051F4-5_y_pos","proposition":{"op":{"name":"gt","args":[{"var":"y"},{"lit":{"type":"Real","value":"0"}}]}}},{"key":"MAP-P084-P051F4-5_y_lt_1","proposition":{"op":{"name":"lt","args":[{"var":"y"},{"lit":{"type":"Real","value":"1"}}]}}},{"key":"MAP-P084-P051F4-5_k_ge_1","proposition":{"op":{"name":"ge","args":[{"var":"k"},{"lit":{"type":"Nat","value":"1"}}]}}},{"key":"MAP-P084-P051F4-5_sigma_ge_theta","proposition":{"op":{"name":"ge","args":[{"var":"sigma"},{"var":"theta"}]}}}]},{"id":"MAP-P084-P051F3-6","producer":"A-LATE-P051F3-EXISTS","closure_role":"REQUIRED","scope_binders":[{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"}],"binder_map":{"theta":{"var":"theta"},"y":{"var":"y"},"k":{"var":"k"},"sigma":{"var":"sigma"}},"hypothesis_map":{"theta_ge_2":{"guard":"MAP-P084-P051F3-6_theta_ge_2"},"y_pos":{"guard":"MAP-P084-P051F3-6_y_pos"},"y_lt_1":{"guard":"MAP-P084-P051F3-6_y_lt_1"},"k_ge_1":{"guard":"MAP-P084-P051F3-6_k_ge_1"},"sigma_ge_theta":{"guard":"MAP-P084-P051F3-6_sigma_ge_theta"}},"witness_map":{},"consume":["existentialized"],"guards":[{"key":"MAP-P084-P051F3-6_theta_ge_2","proposition":{"op":{"name":"ge","args":[{"var":"theta"},{"lit":{"type":"Real","value":"2"}}]}}},{"key":"MAP-P084-P051F3-6_y_pos","proposition":{"op":{"name":"gt","args":[{"var":"y"},{"lit":{"type":"Real","value":"0"}}]}}},{"key":"MAP-P084-P051F3-6_y_lt_1","proposition":{"op":{"name":"lt","args":[{"var":"y"},{"lit":{"type":"Real","value":"1"}}]}}},{"key":"MAP-P084-P051F3-6_k_ge_1","proposition":{"op":{"name":"ge","args":[{"var":"k"},{"lit":{"type":"Nat","value":"1"}}]}}},{"key":"MAP-P084-P051F3-6_sigma_ge_theta","proposition":{"op":{"name":"ge","args":[{"var":"sigma"},{"var":"theta"}]}}}]},{"id":"MAP-P084-P051V-7","producer":"P-051V","closure_role":"REQUIRED","scope_binders":[{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"}],"binder_map":{"theta":{"var":"theta"},"y":{"var":"y"},"k":{"var":"k"},"sigma":{"var":"sigma"}},"hypothesis_map":{"theta_ge_2":{"guard":"MAP-P084-P051V-7_theta_ge_2"},"y_pos":{"guard":"MAP-P084-P051V-7_y_pos"},"y_lt_1":{"guard":"MAP-P084-P051V-7_y_lt_1"},"k_ge_1":{"guard":"MAP-P084-P051V-7_k_ge_1"},"sigma_ge_theta":{"guard":"MAP-P084-P051V-7_sigma_ge_theta"}},"witness_map":{},"consume":["modifier_normalization"],"guards":[{"key":"MAP-P084-P051V-7_theta_ge_2","proposition":{"op":{"name":"ge","args":[{"var":"theta"},{"lit":{"type":"Real","value":"2"}}]}}},{"key":"MAP-P084-P051V-7_y_pos","proposition":{"op":{"name":"gt","args":[{"var":"y"},{"lit":{"type":"Real","value":"0"}}]}}},{"key":"MAP-P084-P051V-7_y_lt_1","proposition":{"op":{"name":"lt","args":[{"var":"y"},{"lit":{"type":"Real","value":"1"}}]}}},{"key":"MAP-P084-P051V-7_k_ge_1","proposition":{"op":{"name":"ge","args":[{"var":"k"},{"lit":{"type":"Nat","value":"1"}}]}}},{"key":"MAP-P084-P051V-7_sigma_ge_theta","proposition":{"op":{"name":"ge","args":[{"var":"sigma"},{"var":"theta"}]}}}]},{"id":"MAP-P084-P051G-8","producer":"A-LATE-P051G-EXISTS","closure_role":"REQUIRED","scope_binders":[{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"}],"binder_map":{"theta":{"var":"theta"},"y":{"var":"y"},"k":{"var":"k"},"sigma":{"var":"sigma"}},"hypothesis_map":{"theta_ge_2":{"guard":"MAP-P084-P051G-8_theta_ge_2"},"y_pos":{"guard":"MAP-P084-P051G-8_y_pos"},"y_lt_1":{"guard":"MAP-P084-P051G-8_y_lt_1"},"k_ge_1":{"guard":"MAP-P084-P051G-8_k_ge_1"},"sigma_ge_theta":{"guard":"MAP-P084-P051G-8_sigma_ge_theta"}},"witness_map":{},"consume":["existentialized"],"guards":[{"key":"MAP-P084-P051G-8_theta_ge_2","proposition":{"op":{"name":"ge","args":[{"var":"theta"},{"lit":{"type":"Real","value":"2"}}]}}},{"key":"MAP-P084-P051G-8_y_pos","proposition":{"op":{"name":"gt","args":[{"var":"y"},{"lit":{"type":"Real","value":"0"}}]}}},{"key":"MAP-P084-P051G-8_y_lt_1","proposition":{"op":{"name":"lt","args":[{"var":"y"},{"lit":{"type":"Real","value":"1"}}]}}},{"key":"MAP-P084-P051G-8_k_ge_1","proposition":{"op":{"name":"ge","args":[{"var":"k"},{"lit":{"type":"Nat","value":"1"}}]}}},{"key":"MAP-P084-P051G-8_sigma_ge_theta","proposition":{"op":{"name":"ge","args":[{"var":"sigma"},{"var":"theta"}]}}}]},{"id":"MAP-P084-P051H-9","producer":"A-LATE-P051H-EXISTS","closure_role":"REQUIRED","scope_binders":[{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"},{"key":"p","type":"Nat"}],"binder_map":{"theta":{"var":"theta"},"y":{"var":"y"},"k":{"var":"k"},"sigma":{"var":"sigma"},"w":{"proj":{"value":{"def":{"id":"D-015","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"}]}},"index":4}},"b":{"proj":{"value":{"def":{"id":"D-015","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"}]}},"index":1}},"p":{"var":"p"}},"hypothesis_map":{"theta_ge_2":{"guard":"MAP-P084-P051H-9_theta_ge_2"},"y_pos":{"guard":"MAP-P084-P051H-9_y_pos"},"y_lt_1":{"guard":"MAP-P084-P051H-9_y_lt_1"},"k_ge_1":{"guard":"MAP-P084-P051H-9_k_ge_1"},"sigma_ge_theta":{"guard":"MAP-P084-P051H-9_sigma_ge_theta"},"selected_weight":{"guard":"MAP-P084-P051H-9_selected_weight"},"modifier_b":{"guard":"MAP-P084-P051H-9_modifier_b"},"prime_p":{"guard":"MAP-P084-P051H-9_prime_p"}},"witness_map":{},"consume":["existentialized"],"guards":[{"key":"MAP-P084-P051H-9_theta_ge_2","proposition":{"op":{"name":"ge","args":[{"var":"theta"},{"lit":{"type":"Real","value":"2"}}]}}},{"key":"MAP-P084-P051H-9_y_pos","proposition":{"op":{"name":"gt","args":[{"var":"y"},{"lit":{"type":"Real","value":"0"}}]}}},{"key":"MAP-P084-P051H-9_y_lt_1","proposition":{"op":{"name":"lt","args":[{"var":"y"},{"lit":{"type":"Real","value":"1"}}]}}},{"key":"MAP-P084-P051H-9_k_ge_1","proposition":{"op":{"name":"ge","args":[{"var":"k"},{"lit":{"type":"Nat","value":"1"}}]}}},{"key":"MAP-P084-P051H-9_sigma_ge_theta","proposition":{"op":{"name":"ge","args":[{"var":"sigma"},{"var":"theta"}]}}},{"key":"MAP-P084-P051H-9_selected_weight","proposition":{"def":{"id":"D-S7A-SELECTED-WEIGHT","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"},{"proj":{"value":{"def":{"id":"D-015","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"}]}},"index":4}}]}}},{"key":"MAP-P084-P051H-9_modifier_b","proposition":{"def":{"id":"D-S7A-MODIFIER","args":[{"proj":{"value":{"def":{"id":"D-015","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"}]}},"index":1}}]}}},{"key":"MAP-P084-P051H-9_prime_p","proposition":{"def":{"id":"D-S7A-PRIME","args":[{"var":"p"}]}}}]},{"id":"MAP-P084-P054-10","producer":"P-054","closure_role":"REQUIRED","scope_binders":[{"key":"d","type":"Nat"},{"key":"d_prime","type":"Nat"},{"key":"k","type":"Nat"}],"binder_map":{"d":{"var":"d"},"d_prime":{"var":"d_prime"},"k":{"var":"k"},"theta":{"var":"theta"}},"hypothesis_map":{"domain":{"guard":"MAP-P084-P054-10_domain"}},"witness_map":{},"consume":["close_window"],"guards":[{"key":"MAP-P084-P054-10_domain","proposition":{"def":{"id":"D-S7B-P054-DOMAIN","args":[{"var":"d"},{"var":"d_prime"},{"var":"k"},{"var":"theta"}]}}}]}],"witness_realizations":{"C_tr_out":{"def":{"id":"D-S811-P084-W","args":[{"var":"theta"}]}}},"proof_ref":"### P-084 — transition outer shifted mean"}
```

- Prenex statement:
  \[
  \forall\theta\in\mathbb R_{\ge2}\;\exists C_{\rm tr,out}(\theta)>0\;
  \forall y\in(0,1)\;\forall k\in\mathbb N_{\ge1}\;
  \forall\sigma\in\mathbb R,\quad
  \theta^k<\sigma<\theta^{k+1}\Longrightarrow
  O_k^{\rm tr}\le C_{\rm tr,out}(\theta)
  \theta^k(\log\sigma)^{-1}
  \sum_{\theta^{k-1}<d'<\theta^{k+2}}w_{4,k}(d').
  \]
- Local equalities: roughness restricts \(d\) to
  \([\sigma,\theta^{k+1})\).
- Domain/range: constant uniform in \(y,k,\sigma,d,d'\).
- Input subject: exact transition O-sum. Output: exact \(d'\)-sum.
- Premise maps:
  - `MAP-P084-P054A`: for fixed \(d'\), take
    \(g(d):=w_{3,k}(dd')v_k(d)\) and use `AD-TR-INIT` from
    \([\sigma,\theta^{k+1})\) to \(d<\theta^{k+1}\); P-051V supplies
    nonnegativity of the modifier in this product.
  - `MAP-P084-P005`:

    | producer | slot | domain | consumer term | evidence |
    |---|---|---|---|---|
    | P-005 | `u` | nonnegative multiplicative | \(w_{3,k}\) | P-051F3 |
    | P-005 | `v` | nonnegative multiplicative, normalized by `v(1)=1` | \(v_k\) | P-051V full-domain multiplicativity and normalization |
    | P-005 | `K_sh` | \(\mathbb N_{>0}\) | \(d'\) | outer index |
    | P-005 | `X` | \(\mathbb R_{\ge2}\) | \(\theta^{k+1}\) | \(\theta\ge2,k\ge1\) |
    | P-005 | `(lambda_i)` | nonnegative sequence | \(\lambda_i:=\Lambda_*\) for all \(i\) | P-051G |
    | P-005 | `lambda` | \([0,2)\) | \(1\) | P-051V full prime-power bound |

    Producer hypothesis is P-051G's common local bound. Consumed conclusion is
    P-005's exact shifted estimate. Subject is `SUB-OUTER-INITIAL` after
    `AD-TR-INIT`; its constant uses only \((\Lambda_*,1)\) and is uniform in
    \((\theta,y,k,\sigma,d')\).
  - `MAP-P084-P007` (two applications):

    | producer | slot | domain | consumer term tuple | evidence |
    |---|---|---|---|---|
    | P-007 | `c` | \(\mathbb R\) | \((0,1/2)\) | transition coefficients |
    | P-007 | `eta` | \(>0\) | \((\eta_*,\eta_*)\), \(\eta_*:=\min(c_*,1)\) | P-051H |
    | P-007 | `C_err` | \(>0\) | \((C_E,C_E)\), \(C_E:=C_{E,*}=C_*+2\Lambda_*\) | common error |
    | P-007 | `(L_p)` | positive prime family | \(L_p:=\sum_{j\ge0}w_{3,k}(p^j)v_k(p^j)p^{-j}\) | constant term 1 |
    | P-007 | `A` | \(\ge2\) | \((2,\sigma)\) | \(2\le\sigma<\theta^{k+1}\) |
    | P-007 | `B` | \(\ge2\) | \((\sigma,\theta^{k+1})\) | transition domain |

    In each application extend the displayed Euler factor by the exact model
    \(1+c/p\) outside its consumed interval; P051H-main then discharges the
    global P-007 hypothesis without altering the interval product. In a transition bin
    \(v_k(p)=0\) below \(\sigma\) and \(v_k(p)=1\) above it.
    `AD-P084-EULER-SPLIT` is the literal two-range factorization; empty
    ranges use P-007's empty branch.
  - `MAP-P084-P008`: define the fixed-endpoint family
    \(Q_{\rm tr,out}:=\{(\theta,y,k,\sigma):\theta\ge2,0<y<1,k\ge1,
    \theta^k<\sigma<\theta^{k+1}\}\), use its coefficient maps \(0,1/2\), and
    the exact common data
    \(\eta_*:=\min(c_*,1),C_{\rm err,*}:=C_{E,*},P_0:=2,
    m_{\rm fin}:=M_{\rm fin}:=1\). P051H-main discharges the error
    hypotheses. The consumed P-008 conclusions assemble by
    `AD-P084-EULER-SPLIT`; their common constants precede
    \(y,k,\sigma,d'\), licensing \(C_{\rm tr,out}(\theta)\).
    The P-007 hypotheses are P051H-main and the exact transition coefficients;
    its consumed conclusions and literal subject adapter are the displayed
    ones.

    | producer | slot | domain | consumer term tuple | evidence |
    |---|---|---|---|---|
    | P-008 | `Q` | nonempty index set | \(Q_{\rm tr,out}\) | e.g. \((2,1/2,1,3)\) |
    | P-008 | `c_-` | \(\mathbb R\) | \(0\) | common lower endpoint |
    | P-008 | `c_+` | \(\mathbb R\), \(c_-\le c_+\), \(1+c_-/2>0\) | \(1/2\) | admissible compact interval |
    | P-008 | `eta_*` | \(\mathbb R_{>0}\) | \(\min(c_*,1)\) | P-051H |
    | P-008 | `C_err,*` | \(\mathbb R_{>0}\) | \(C_{E,*}\) | P051H-main |
    | P-008 | `P_0` | \(\mathbb R_{\ge2}\) | \(2\) | literal |
    | P-008 | `m_fin` | \(\mathbb R_{>0}\) | \(1\) | empty prefix |
    | P-008 | `M_fin` | \(\mathbb R_{\ge m_{\rm fin}}\) | \(1\) | empty prefix |
    | P-008 | `c` | maps into \([0,1/2]\) | \((0,1/2)\) | transition coefficients |
    | P-008 | `L` | positive factor families | two global exact-model extensions above | P051H-main |
    | P-008 | `q` | \(Q_{\rm tr,out}\) | \((\theta,y,k,\sigma)\) | complete fixed-endpoint transition tuple |
    | P-008 | `A` | \(\mathbb R_{\ge2}\) | \((2,\sigma)\) | transition endpoints |
    | P-008 | `B` | \(\mathbb R_{\ge2}\) | \((\sigma,\theta^{k+1})\) | P-084 endpoint |
  - `MAP-P084-P051F4`: consume the exact construction of \(w_{4,k}\) and
    its domination of the P-005 shift factor.
  - `MAP-P084-P051F3`: consume only the exact nonnegative multiplicative
    identity of \(w_{3,k}\) used as P-005's first weight.
  - `MAP-P084-P051V`: bind \((\theta,y,k,\sigma)\) identically and consume
    exactly nonnegative multiplicativity of \(v_k\), \(v_k(1)=1\), and the
    full prime-power bound, discharging every P-005 modifier slot and the
    nonnegativity used by `MAP-P084-P054A`.
  - `MAP-P084-P051G`: consume only the common local bounds for \(w_{3,k}\),
    with the transition tuple mapped identically.
  - `MAP-P084-P051H`: consume only (P051H-main) for the two exact transition
    Euler factors above with \(b:=v_k\); P-051V supplies the literal modifier
    hypotheses for that specialization.
  - P-054 — Binders:
    \(d:=d,d':=d',k:=k,\theta:=\theta\) termwise.
    Hypotheses: the D-021e outer index. Consumed: \(d'\)-window.
    Subject: exact enlargement. Constants: none.
- Derivation certificate: apply shifted mean for each \(d'\), then sum.
- Source/S2 anchor: S2 R2.16 and S2B R2(4).
- Definitions used: D-002, D-015, D-021a/D-021b/D-021c/D-021d/D-021e.

### P-085 — transition high assembly

Current construction binding: the exact `P085Statement` in the GroupA--GroupD source contracts, W0--W8, and the retained S7 provider. Any `mathminer-s3-legacy` block here is historical, not a proof.

```mathminer-s3-legacy
{"schema":"mathminer.s3/1","id":"P-085","kind":"PROPOSITION","binders":[{"key":"theta","type":"Real"}],"uses_definitions":["D-006","D-021d","S-P-085","W-P-085-C_tr_A"],"source_anchors":[{"path":"stage3/canonical/CURRENT.md","git":"4279cd5e01f75401a9f5fa12d42961fe46b9ac8b","anchor":"### P-085 \u2014 transition high assembly"}],"hypotheses":[],"witnesses":[{"key":"C_tr_A","type":"Real","depends_on":["theta"]}],"conclusions":[{"key":"result","proposition":{"def":{"id":"S-P-085","args":[{"var":"theta"},{"var":"C_tr_A"}]}}}],"premises":[{"id":"MAP-P085-P082-1","producer":"P-082","closure_role":"REQUIRED","binder_map":{"theta":{"var":"theta"}},"hypothesis_map":{},"witness_map":{"C_tr_H":"p_085_p_082_1_C_tr_H"},"consume":["result"]},{"id":"MAP-P085-P084-2","producer":"P-084","closure_role":"REQUIRED","binder_map":{"theta":{"var":"theta"}},"hypothesis_map":{},"witness_map":{"C_tr_out":"p_085_p_084_2_C_tr_out"},"consume":["result"]},{"id":"MAP-P085-P070-3","producer":"P-070","closure_role":"REQUIRED","binder_map":{},"hypothesis_map":{},"witness_map":{"c_star":"p_085_p_070_3_c_star","C_star":"p_085_p_070_3_C_star","Lambda_star":"p_085_p_070_3_Lambda_star","C_fam":"p_085_p_070_3_C_fam"},"consume":["result"]},{"id":"MAP-P085-P081-4","producer":"P-081","closure_role":"REQUIRED","scope_binders":[{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"}],"binder_map":{"theta":{"var":"theta"},"k":{"var":"k"},"sigma":{"var":"sigma"}},"hypothesis_map":{},"witness_map":{},"consume":["result"]}],"witness_realizations":{"C_tr_A":{"def":{"id":"W-P-085-C_tr_A","args":[{"var":"theta"},{"var":"p_085_p_082_1_C_tr_H"},{"var":"p_085_p_084_2_C_tr_out"},{"var":"p_085_p_070_3_c_star"},{"var":"p_085_p_070_3_C_star"},{"var":"p_085_p_070_3_Lambda_star"},{"var":"p_085_p_070_3_C_fam"}]}}},"proof_ref":"### P-085 \u2014 transition high assembly"}
```

- Prenex statement:
  \[
  \forall\theta\ge2\;\exists C_{\rm tr,A}(\theta)>0\;
  \forall y\in(0,1)\;\forall k\ge1\;
  \forall\sigma\in(\theta^k,\theta^{k+1})\;
  \forall x>\theta^{2k-1},
  \]
  \[
  H_k\le C_{\rm tr,A}(\theta)
  x(\log\sigma)^{-y}k^{(y-3)/2}k^{(y-1)/2}.
  \]
- Local equalities: none.
- Domain/range: uniform after \(\theta\).
- Input subject: exact H. Output: first P3 brace term.
- Premise maps:
  - P-082 — Binders:
    \(\theta:=\theta,y:=y,k:=k,\sigma:=\sigma,x:=x\).
    Hypotheses: the explicit transition domain. Consumed: H transport.
    Subject: exact H. Constants: \(C_{\rm tr,H}(\theta)\).
  - P-084 — Binders:
    \(\theta:=\theta,y:=y,k:=k,\sigma:=\sigma\).
    Hypotheses: the explicit transition domain. Consumed: outer mean.
    Subject: exact O-tr. Constants: \(C_{\rm tr,out}(\theta)\).
  - P-070 — Witness/order map: first select
    \(c_*,C_*,\Lambda_*,C_{\rm fam}\), then set \(\theta:=\theta\) and
    define \(C_4:=C_4(C_{\rm fam},\theta)\) by (P070-C4), and only then set
    \(y:=y,k:=k,\sigma:=\sigma\).
    Hypotheses: the displayed domains. Consumed: (P070-window).
    Subject: `SUB-P070-WINDOW`, literally P-084's \(d'\)-sum. Constants: map
    \(C_4:=C_4(C_{\rm fam},\theta)\) literally, then absorb it into
    \(C_{\rm tr,A}(\theta)\) after \(\theta\) is fixed.
  - P-081 — Binders:
    \(k:=k,\theta:=\theta,\sigma:=\sigma\).
    Hypotheses: \(\theta^k<\sigma<\theta^{k+1}\).
    Consumed: scale comparison. Subject: exact scalar conversion
    \((\log\sigma)^{-3/2}k^{-1/2}
    \asymp_\theta(\log\sigma)^{-y}
    k^{(y-3)/2}k^{(y-1)/2}\). Constants: \(\theta\)-only.
- Derivation certificate: multiply exact estimates and apply scale identity.
- Source/S2 anchor: S2 R2.5c.
- Definitions used: D-021a/D-021b/D-021c/D-021d/D-021e.

### P-086 — transition low assembly

Current construction binding: the exact `P086Statement` in the GroupA--GroupD source contracts, W0--W8, and the retained S7 provider. Any `mathminer-s3-legacy` block here is historical, not a proof.

```mathminer-s3-legacy
{"schema":"mathminer.s3/1","id":"P-086","kind":"PROPOSITION","binders":[{"key":"theta","type":"Real"}],"uses_definitions":["D-006","D-021d","S-P-086","W-P-086-C_tr_C"],"source_anchors":[{"path":"stage3/canonical/CURRENT.md","git":"4279cd5e01f75401a9f5fa12d42961fe46b9ac8b","anchor":"### P-086 \u2014 transition low assembly"}],"hypotheses":[],"witnesses":[{"key":"C_tr_C","type":"Real","depends_on":["theta"]}],"conclusions":[{"key":"result","proposition":{"def":{"id":"S-P-086","args":[{"var":"theta"},{"var":"C_tr_C"}]}}}],"premises":[{"id":"MAP-P086-P083-1","producer":"P-083","closure_role":"REQUIRED","binder_map":{"theta":{"var":"theta"}},"hypothesis_map":{},"witness_map":{"C_tr_L":"p_086_p_083_1_C_tr_L"},"consume":["result"]},{"id":"MAP-P086-P084-2","producer":"P-084","closure_role":"REQUIRED","binder_map":{"theta":{"var":"theta"}},"hypothesis_map":{},"witness_map":{"C_tr_out":"p_086_p_084_2_C_tr_out"},"consume":["result"]},{"id":"MAP-P086-P070-3","producer":"P-070","closure_role":"REQUIRED","binder_map":{},"hypothesis_map":{},"witness_map":{"c_star":"p_086_p_070_3_c_star","C_star":"p_086_p_070_3_C_star","Lambda_star":"p_086_p_070_3_Lambda_star","C_fam":"p_086_p_070_3_C_fam"},"consume":["result"]},{"id":"MAP-P086-P081-4","producer":"P-081","closure_role":"REQUIRED","scope_binders":[{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"}],"binder_map":{"theta":{"var":"theta"},"k":{"var":"k"},"sigma":{"var":"sigma"}},"hypothesis_map":{},"witness_map":{},"consume":["result"]}],"witness_realizations":{"C_tr_C":{"def":{"id":"W-P-086-C_tr_C","args":[{"var":"theta"},{"var":"p_086_p_083_1_C_tr_L"},{"var":"p_086_p_084_2_C_tr_out"},{"var":"p_086_p_070_3_c_star"},{"var":"p_086_p_070_3_C_star"},{"var":"p_086_p_070_3_Lambda_star"},{"var":"p_086_p_070_3_C_fam"}]}}},"proof_ref":"### P-086 \u2014 transition low assembly"}
```

- Prenex statement:
  \[
  \forall\theta\ge2\;\exists C_{\rm tr,C}(\theta)>0\;
  \forall y\in(0,1)\;\forall k\ge1\;
  \forall\sigma\in(\theta^k,\theta^{k+1})\;
  \forall x>\theta^{2k-1},
  \]
  \[
  L_k\le C_{\rm tr,C}(\theta)
  x(\log\sigma)^{-y}k^{(y-3)/2}
  {(\log\sigma)^{y/2}\over\ell(2x\theta^{1-2k})^{1/2}}.
  \]
- Local equalities: none.
- Domain/range: uniform after \(\theta\).
- Input subject: exact L. Output: terminal P3 brace term.
- Premise maps:
  - P-083 — Binders:
    \(\theta:=\theta,y:=y,k:=k,\sigma:=\sigma,x:=x\).
    Hypotheses: the explicit transition domain. Consumed: low transport.
    Subject: exact L. Constants: \(C_{\rm tr,L}(\theta)\).
  - P-084 — Binders:
    \(\theta:=\theta,y:=y,k:=k,\sigma:=\sigma\).
    Hypotheses: the explicit transition domain. Consumed: outer mean.
    Subject: exact O-tr. Constants: \(C_{\rm tr,out}(\theta)\).
  - P-070 — Witness/order map: first select
    \(c_*,C_*,\Lambda_*,C_{\rm fam}\), then set \(\theta:=\theta\) and
    define \(C_4:=C_4(C_{\rm fam},\theta)\) by (P070-C4), and only then set
    \(y:=y,k:=k,\sigma:=\sigma\).
    Hypotheses: the displayed domains. Consumed: (P070-window).
    Subject: `SUB-P070-WINDOW`, literally P-084's \(d'\)-sum. Constants: map
    \(C_4:=C_4(C_{\rm fam},\theta)\) literally, then absorb it into
    \(C_{\rm tr,C}(\theta)\) after \(\theta\) is fixed.
  - P-081 — Binders:
    \(k:=k,\theta:=\theta,\sigma:=\sigma\).
    Hypotheses: \(\theta^k<\sigma<\theta^{k+1}\).
    Consumed: scale comparison. Subject: converts
    \((\log\sigma)^{-1}k^{-1/2}\) to
    \((\log\sigma)^{-y/2}k^{(y-3)/2}\).
    Constants: \(\theta\)-only.
- Derivation certificate: multiply and simplify exact factors.
- Source/S2 anchor: S2 R2.5c.
- Definitions used: D-006, D-021a/D-021b/D-021c/D-021d/D-021e.

### P-087 — transition envelope addition

Current construction binding: the exact `P087Statement` in the GroupA--GroupD source contracts, W0--W8, and the retained S7 provider. Any `mathminer-s3-legacy` block here is historical, not a proof.

```mathminer-s3-legacy
{"schema":"mathminer.s3/1","id":"P-087","kind":"PROPOSITION","binders":[{"key":"theta","type":"Real"}],"uses_definitions":["D-006","D-017","D-021a","D-021b","D-021c","D-021d","D-021e","S-P-087","W-P-087-C_tr"],"source_anchors":[{"path":"stage3/canonical/CURRENT.md","git":"4279cd5e01f75401a9f5fa12d42961fe46b9ac8b","anchor":"### P-087 \u2014 transition envelope addition"}],"hypotheses":[],"witnesses":[{"key":"C_tr","type":"Real","depends_on":["theta"]}],"conclusions":[{"key":"result","proposition":{"def":{"id":"S-P-087","args":[{"var":"theta"},{"var":"C_tr"}]}}}],"premises":[{"id":"MAP-P087-P075-1","producer":"P-075","closure_role":"REQUIRED","binder_map":{"theta":{"var":"theta"}},"hypothesis_map":{},"witness_map":{"C_tr_sm":"p_087_p_075_1_C_tr_sm"},"consume":["result"]},{"id":"MAP-P087-P076-2","producer":"P-076","closure_role":"REQUIRED","scope_binders":[{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"},{"key":"x","type":"Real"}],"binder_map":{"theta":{"var":"theta"},"y":{"var":"y"},"k":{"var":"k"},"sigma":{"var":"sigma"},"x":{"var":"x"}},"hypothesis_map":{},"witness_map":{},"consume":["result"]},{"id":"MAP-P087-P077-3","producer":"P-077","closure_role":"REQUIRED","binder_map":{"theta":{"var":"theta"}},"hypothesis_map":{},"witness_map":{"C_tr_ge":"p_087_p_077_3_C_tr_ge"},"consume":["result"]},{"id":"MAP-P087-P078-4","producer":"P-078","closure_role":"REQUIRED","scope_binders":[{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"},{"key":"x","type":"Real"}],"binder_map":{"theta":{"var":"theta"},"y":{"var":"y"},"k":{"var":"k"},"sigma":{"var":"sigma"},"x":{"var":"x"}},"hypothesis_map":{},"witness_map":{},"consume":["result"]},{"id":"MAP-P087-P079-5","producer":"P-079","closure_role":"REQUIRED","scope_binders":[{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"},{"key":"x","type":"Real"}],"binder_map":{"theta":{"var":"theta"},"y":{"var":"y"},"k":{"var":"k"},"sigma":{"var":"sigma"},"x":{"var":"x"}},"hypothesis_map":{},"witness_map":{},"consume":["result"]},{"id":"MAP-P087-P080-6","producer":"P-080","closure_role":"REQUIRED","scope_binders":[{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"},{"key":"x","type":"Real"}],"binder_map":{"theta":{"var":"theta"},"y":{"var":"y"},"k":{"var":"k"},"sigma":{"var":"sigma"},"x":{"var":"x"}},"hypothesis_map":{},"witness_map":{},"consume":["result"]},{"id":"MAP-P087-P085-7","producer":"P-085","closure_role":"REQUIRED","binder_map":{"theta":{"var":"theta"}},"hypothesis_map":{},"witness_map":{"C_tr_A":"p_087_p_085_7_C_tr_A"},"consume":["result"]},{"id":"MAP-P087-P086-8","producer":"P-086","closure_role":"REQUIRED","binder_map":{"theta":{"var":"theta"}},"hypothesis_map":{},"witness_map":{"C_tr_C":"p_087_p_086_8_C_tr_C"},"consume":["result"]}],"witness_realizations":{"C_tr":{"def":{"id":"W-P-087-C_tr","args":[{"var":"theta"},{"var":"p_087_p_075_1_C_tr_sm"},{"var":"p_087_p_077_3_C_tr_ge"},{"var":"p_087_p_085_7_C_tr_A"},{"var":"p_087_p_086_8_C_tr_C"}]}}},"proof_ref":"### P-087 \u2014 transition envelope addition"}
```

- Prenex statement:
  \[
  \forall\theta\ge2\;\exists C_{\rm tr}(\theta)>0\;
  \forall y\in(0,1)\;\forall k\ge1\;
  \forall\sigma\in(\theta^k,\theta^{k+1})\;
  \forall x>\theta^{2k-1},
  \]
  \[
  S_k(x,y;\sigma,\theta)\le C_{\rm tr}(\theta)
  x(\log\sigma)^{-y}k^{(y-3)/2}
  \left\{k^{(y-1)/2}
  +\ell(2x\theta^{1-2k})^{(y-1)/2}
  +{(\log\sigma)^{y/2}\over\ell(2x\theta^{1-2k})^{1/2}}\right\}.
  \]
- Local equalities: exact D-021a/D-021b/D-021c/D-021d/D-021e branch subjects.
- Domain/range: one \(\theta\)-constant, uniform in all other variables.
  It is selected after \(\theta\) from the high/low assembly constants, whose
  P-070 input is exactly \(C_4(C_{\rm fam},\theta)\).
- Input subject: exact transition S. Output: common P3 envelope.
- Premise maps:
  - P-075 — Binders:
    \(\theta:=\theta,y:=y,k:=k,\sigma:=\sigma,x:=x\).
    Hypotheses: \(\theta^k<\sigma<\theta^{k+1}\) and
    \(x>\theta^{2k-1}\).
    Consumed: S-to-V smoothing. Subject: exact S,V.
    Constants: \(C_{\rm tr,sm}(\theta)\).
  - P-076 — Binders:
    \(y:=y,k:=k,\theta:=\theta,\sigma:=\sigma,x:=x\).
    Hypotheses: the explicit transition domain. Consumed: V partition.
    Subject: exact equality. Constants: none.
  - P-077 — Binders:
    \(\theta:=\theta,y:=y,k:=k,\sigma:=\sigma,x:=x\).
    Hypotheses: \(y\in(0,1),k\ge1,\theta\ge2,
    \theta^k<\sigma<\theta^{k+1},x>\theta^{2k-1}\).
    Consumed: high substitution.
    Subject: \(V^\ge\to\widetilde H\). Constants: \(C_{\rm tr,\ge}(\theta)\).
  - P-078 — Binders:
    \(y:=y,k:=k,\theta:=\theta,\sigma:=\sigma,x:=x\).
    Hypotheses: \(y\in(0,1),k\ge1,\theta\ge2,
    \theta^k<\sigma<\theta^{k+1},x>\theta^{2k-1}\).
    Consumed: high weight transport.
    Subject: \(\widetilde H\to H\). Constants: none.
  - P-079 — Binders:
    \(y:=y,k:=k,\theta:=\theta,\sigma:=\sigma,x:=x\).
    Hypotheses: \(y\in(0,1),k\ge1,\theta\ge2,
    \theta^k<\sigma<\theta^{k+1},x>\theta^{2k-1}\).
    Consumed: low substitution bound.
    Subject: \(V^<\to\widetilde L\). Constants: none.
  - P-080 — Binders:
    \(y:=y,k:=k,\theta:=\theta,\sigma:=\sigma,x:=x\).
    Hypotheses: \(y\in(0,1),k\ge1,\theta\ge2,
    \theta^k<\sigma<\theta^{k+1},x>\theta^{2k-1}\).
    Consumed: low weight transport.
    Subject: \(\widetilde L\to L\). Constants: none.
  - P-085 — Binders:
    \(\theta:=\theta,y:=y,k:=k,\sigma:=\sigma,x:=x\).
    Hypotheses: \(y\in(0,1),k\ge1,\theta\ge2,
    \theta^k<\sigma<\theta^{k+1},x>\theta^{2k-1}\).
    Consumed: high assembly.
    Subject: exact H. Constants: \(C_{\rm tr,A}(\theta)\).
  - P-086 — Binders:
    \(\theta:=\theta,y:=y,k:=k,\sigma:=\sigma,x:=x\).
    Hypotheses: \(y\in(0,1),k\ge1,\theta\ge2,
    \theta^k<\sigma<\theta^{k+1},x>\theta^{2k-1}\).
    Consumed: low assembly.
    Subject: exact L. Constants: \(C_{\rm tr,C}(\theta)\).
- Derivation certificate: follow both exact branches, add their bounds, and
  add the nonnegative middle brace term.
- Source/S2 anchor: ET Proposition 3; S2 R2.5c.
- Definitions used: D-017, D-021a/D-021b/D-021c/D-021d/D-021e.

### P-088 — empty-bin result

```mathminer-s3
{"schema":"mathminer.s3/1","id":"P-088","kind":"PROPOSITION","binders":[{"key":"theta","type":"Real"},{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"},{"key":"x","type":"Real"}],"uses_definitions":["D-013","D-017","S-P-088"],"source_anchors":[{"path":"stage3/canonical/CURRENT.md","git":"4279cd5e01f75401a9f5fa12d42961fe46b9ac8b","anchor":"### P-088 — empty-bin result"}],"hypotheses":[],"witnesses":[],"conclusions":[{"key":"result","proposition":{"def":{"id":"S-P-088","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"},{"var":"x"}]}}}],"premises":[],"witness_realizations":{},"proof_ref":"### P-088 — empty-bin result"}
```

- Prenex statement: for every \(y\in(0,1),k\ge1,\sigma\ge\theta\ge2,x>0\),
  if \(\theta^{k+1}\le\sigma\), then \(S_k(x,y;\sigma,\theta)=0\).
- Local equalities: none.
- Domain/range: exact equality.
- Input subject: D-013 outer d-bin. Output: zero mean.
- Premise maps: none (root).
- Derivation certificate: a nontrivial \(\sigma\)-rough \(d\) is at least
  \(\sigma\); \(d=1\) cannot occur in a \(k\ge1\) bin.
- Source/S2 anchor: S2 R2.5b.
- Definitions used: D-002, D-013, D-017.

### P-089 — Proposition 3

Current construction binding: the exact `P089Statement` in the GroupA--GroupD source contracts, W0--W8, and the retained S7 provider. Any `mathminer-s3-legacy` block here is historical, not a proof.

```mathminer-s3-legacy
{"schema":"mathminer.s3/1","id":"P-089","kind":"PROPOSITION","binders":[{"key":"theta","type":"Real"}],"uses_definitions":["D-006","D-017","S-P-089","W-P-089-C_3"],"source_anchors":[{"path":"stage3/canonical/CURRENT.md","git":"4279cd5e01f75401a9f5fa12d42961fe46b9ac8b","anchor":"### P-089 \u2014 Proposition 3"}],"hypotheses":[],"witnesses":[{"key":"C_3","type":"Real","depends_on":["theta"]}],"conclusions":[{"key":"result","proposition":{"def":{"id":"S-P-089","args":[{"var":"theta"},{"var":"C_3"}]}}}],"premises":[{"id":"MAP-P089-P074-1","producer":"P-074","closure_role":"REQUIRED","binder_map":{"theta":{"var":"theta"}},"hypothesis_map":{},"witness_map":{"C_reg":"p_089_p_074_1_C_reg"},"consume":["result"]},{"id":"MAP-P089-P087-2","producer":"P-087","closure_role":"REQUIRED","binder_map":{"theta":{"var":"theta"}},"hypothesis_map":{},"witness_map":{"C_tr":"p_089_p_087_2_C_tr"},"consume":["result"]},{"id":"MAP-P089-P088-3","producer":"P-088","closure_role":"REQUIRED","scope_binders":[{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"},{"key":"x","type":"Real"}],"binder_map":{"theta":{"var":"theta"},"y":{"var":"y"},"k":{"var":"k"},"sigma":{"var":"sigma"},"x":{"var":"x"}},"hypothesis_map":{},"witness_map":{},"consume":["result"]}],"witness_realizations":{"C_3":{"def":{"id":"W-P-089-C_3","args":[{"var":"theta"},{"var":"p_089_p_074_1_C_reg"},{"var":"p_089_p_087_2_C_tr"}]}}},"proof_ref":"### P-089 \u2014 Proposition 3"}
```

- Prenex statement:
  \[
  \forall\theta\ge2\;\exists C_3(\theta)>0\;
  \forall y\in(0,1)\;\forall k\ge1\;\forall\sigma\ge\theta\;
  \forall x>\theta^{2k-1},
  \]
  \[
  \sum_{n<x}f_k^\#(y,n)\le {C_3(\theta)\over y}
  x(\log\sigma)^{-y}k^{(y-3)/2}
  \left\{k^{(y-1)/2}
  +\ell(2x\theta^{1-2k})^{(y-1)/2}
  +{(\log\sigma)^{y/2}\over\ell(2x\theta^{1-2k})^{1/2}}\right\}.
  \]
- Local equalities: S is D-017.
- Domain/range: the three cases below are disjoint/exhaustive. The numerator
  \(C_3(\theta)\) is selected after \(\theta\) from \(C_{\rm reg}(\theta)\)
  and \(C_{\rm tr}(\theta)\), and therefore carries the already scoped
  \(C_4(C_{\rm fam},\theta)\) lineage but no dependence on \(y,k,\sigma,x\).
- Input subject: exact \(S_k\). Output: source Proposition-3 envelope.
- Premise maps:
  - P-074 — Binders:
    \(\theta:=\theta,y:=y,k:=k,\sigma:=\sigma,x:=x\).
    Hypotheses: \(\sigma\le\theta^k\).
    Consumed: regular envelope. Subject: exact S.
    Constants: the explicit \(C_{\rm reg}(\theta)/y\) maps into
    \(C_3(\theta)/y\); \(y\) is not absorbed into a pre-\(y\) constant.
  - P-087 — Binders:
    \(\theta:=\theta,y:=y,k:=k,\sigma:=\sigma,x:=x\).
    Hypotheses:
    \(\theta^k<\sigma<\theta^{k+1}\).
    Consumed: transition envelope. Subject: exact S.
    Constants: \(C_{\rm tr}(\theta)\le C_3(\theta)/y\) because
    \(0<y<1\).
  - P-088 — Binders:
    \(y:=y,k:=k,\sigma:=\sigma,\theta:=\theta,x:=x\).
    Hypotheses:
    \(\theta^{k+1}\le\sigma\). Consumed: empty equality.
    Subject: exact S. Constants: none.
- Derivation certificate: trichotomy on \(\sigma\); select the corresponding
  completed envelope.
- Source/S2 anchor: ET Proposition 3, pp. 29–31; accepted S2 R1+R2+R3,
  especially R3.P3 and S2B R3.
- Definitions used: D-006, D-013, D-017.

## 10. Proposition 4 support, endpoint, and weighted-sum chain

### P-090 — finite-support witness from \(f_k^\#\)

Current construction binding: the exact `P090Statement` in the GroupA--GroupD source contracts, W0--W8, and the retained S7 provider. Any `mathminer-s3-legacy` block here is historical, not a proof.

```mathminer-s3-legacy
{"schema":"mathminer.s3/1","id":"P-090","kind":"PROPOSITION","binders":[{"key":"theta","type":"Real"},{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"},{"key":"n","type":"Nat"}],"uses_definitions":["D-002","D-003","D-005","D-013","D-S7B-P054-DOMAIN","S-P-090","W-P-090-d","W-P-090-d_prime","W-P-090-t"],"source_anchors":[{"path":"stage3/canonical/CURRENT.md","git":"4279cd5e01f75401a9f5fa12d42961fe46b9ac8b","anchor":"### P-090 \u2014 finite-support witness from \\(f_k^\\#\\)"}],"hypotheses":[],"witnesses":[{"key":"d","type":"Nat","depends_on":["theta","y","k","sigma","n"]},{"key":"d_prime","type":"Nat","depends_on":["theta","y","k","sigma","n"]},{"key":"t","type":"Nat","depends_on":["theta","y","k","sigma","n"]}],"conclusions":[{"key":"result","proposition":{"def":{"id":"S-P-090","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"},{"var":"n"},{"var":"d"},{"var":"d_prime"},{"var":"t"}]}}}],"premises":[{"id":"MAP-P090-P054-1","producer":"P-054","closure_role":"REQUIRED","binder_map":{"d":{"var":"d_selected"},"d_prime":{"var":"d_prime_selected"},"k":{"var":"k"},"theta":{"var":"theta"}},"hypothesis_map":{"domain":{"guard":"MAP-P090-P054-1_domain"}},"witness_map":{},"consume":["close_window"],"guards":[{"key":"MAP-P090-P054-1_domain","proposition":{"def":{"id":"D-S7B-P054-DOMAIN","args":[{"var":"d_selected"},{"var":"d_prime_selected"},{"var":"k"},{"var":"theta"}]}}}]}],"witness_realizations":{"d":{"var":"d_selected"},"d_prime":{"var":"d_prime_selected"},"t":{"var":"t_selected"}},"proof_ref":"### P-090 \u2014 finite-support witness from \\(f_k^\\#\\)","locals":[{"key":"d_selected","type":"Nat","value":{"def":{"id":"W-P-090-d","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"},{"var":"n"}]}}},{"key":"d_prime_selected","type":"Nat","value":{"def":{"id":"W-P-090-d_prime","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"},{"var":"n"}]}}},{"key":"t_selected","type":"Nat","value":{"def":{"id":"W-P-090-t","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"},{"var":"n"}]}}}]}
```

- Prenex statement: for every \(y\in(0,1)\), \(k\ge1\),
  \(\sigma\ge\theta\ge2\), and \(n>0\), if \(f_k^\#(y,n)>0\), then there
  exist \(d,d',t>0\) such that
  \[
  dd't\mid n,\quad \theta^k\le d<\theta^{k+1},\quad
  {\rm Close}_\theta(d,d'),\quad
  \chi(d,\sigma)y^{\Omega(dt,\theta^k)}\chi(t,\sigma)>0,
  \]
  and
  \[
  \theta^{2k-1}<dd'\le dd't\le n.
  \]
  Consequently, if \(n<x\), then \(\theta^{2k-1}<x\).
- Local equalities: the witnesses are an actual positive D-013 summand.
- Domain/range: all integer products are positive and typed.
- Input subject: exact D-013 \(f_k^\#\). Output: support witness and chain.
- Premise maps:
  - P-054 — Binders:
    \(d:=d,d':=d',k:=k,\theta:=\theta\), the selected summand data.
    Hypotheses: its half-open bin and Close predicate come from D-013.
    Consumed: strict lower product window.
    Subject: the selected \(dd'\). Constants: none.
- Derivation certificate: a positive finite nonnegative sum has a positive
  term; divisibility gives \(dd't\le n\), and \(t\ge1\) gives \(dd'\le dd't\).
- Source/S2 anchor: S2 R1 §6 and R2.7, with D-013 typed subject.
- Definitions used: D-005, D-013.

### A-LATE-P090-EXISTS — existentialized finite-support adapter

```mathminer-s3-legacy
{"schema":"mathminer.s3/1","id":"A-LATE-P090-EXISTS","kind":"PROPOSITION","binders":[{"key":"theta","type":"Real"},{"key":"y","type":"Real"},{"key":"k","type":"Nat"},{"key":"sigma","type":"Real"},{"key":"n","type":"Nat"}],"uses_definitions":["D-LATE-P090-EXISTS"],"source_anchors":[],"hypotheses":[],"witnesses":[],"conclusions":[{"key":"existentialized","proposition":{"def":{"id":"D-LATE-P090-EXISTS","args":[{"var":"theta"},{"var":"y"},{"var":"k"},{"var":"sigma"},{"var":"n"}]}}}],"premises":[{"id":"use-p-090","producer":"P-090","closure_role":"REQUIRED","binder_map":{"theta":{"var":"theta"},"y":{"var":"y"},"k":{"var":"k"},"sigma":{"var":"sigma"},"n":{"var":"n"}},"hypothesis_map":{},"witness_map":{"d":"adapter_p090_d","d_prime":"adapter_p090_d_prime","t":"adapter_p090_t"},"consume":["result"]}],"witness_realizations":{},"proof_ref":"### A-LATE-P090-EXISTS \u2014 existentialized finite-support adapter"}
```

- Prenex statement: for every live (theta,y,k,sigma,n) tuple, existentially
  package the three P-090 support witnesses without exporting a scoped witness.
- Premise map: bind P-090 identically and consume its exact finite-support
  conclusion; expose only the existential proposition.

### P-091 — exact moving cutoff

```mathminer-s3
{"schema":"mathminer.s3/1","id":"P-091","kind":"PROPOSITION","binders":[{"key":"theta","type":"Real"},{"key":"x","type":"Real"},{"key":"k","type":"Int"}],"uses_definitions":["D-022","S-P-091"],"source_anchors":[{"path":"stage3/canonical/CURRENT.md","git":"4279cd5e01f75401a9f5fa12d42961fe46b9ac8b","anchor":"### P-091 — exact moving cutoff"}],"hypotheses":[],"witnesses":[],"conclusions":[{"key":"result","proposition":{"def":{"id":"S-P-091","args":[{"var":"theta"},{"var":"x"},{"var":"k"}]}}}],"premises":[],"witness_realizations":{},"proof_ref":"### P-091 — exact moving cutoff"}
```

- Prenex statement: for every \(\theta\ge2,x>0\), put
  \(X=X_\theta(x)\), \(N=N_\theta(x)\). For every integer \(k\),
  \[
  \theta^{2k-1}<x\quad\Longleftrightarrow\quad k<X,
  \]
  and
  \[
  N<X\le N+1,\qquad k<X\Longrightarrow k\le N.
  \]
- Local equalities:
  \(X=\frac12(1+\log x/\log\theta)\), \(N=\lceil X\rceil-1\).
- Input subject: strict P3 support inequality. Output: exact integer cutoff.
- Premise maps: none (root).
- Derivation certificate: take logarithms using \(\log\theta>0\);
  the ceiling definition gives \(N<X\le N+1\) whether or not \(X\) is integer.
- Source/S2 anchor: ET Proposition 4 summation range, pp. 31–32; S2 R1 §6.
- Definitions used: D-022.

### P-092 — finite restriction of Proposition-2's infinite majorant

Current construction binding: the exact `P092Statement` in the GroupA--GroupD source contracts, W0--W8, and the retained S7 provider. Any `mathminer-s3-legacy` block here is historical, not a proof.

```mathminer-s3-legacy
{"schema":"mathminer.s3/1","id":"P-092","kind":"PROPOSITION","binders":[{"key":"epsilon_int","type":"Real"},{"key":"xi","type":"Real"},{"key":"sigma","type":"Real"},{"key":"theta","type":"Real"},{"key":"y","type":"Real"},{"key":"x","type":"Real"}],"uses_definitions":["D-006","D-007","D-012","D-017","D-022","S-P-044","S-P-092"],"source_anchors":[{"path":"stage3/canonical/CURRENT.md","git":"4279cd5e01f75401a9f5fa12d42961fe46b9ac8b","anchor":"### P-092 \u2014 finite restriction of Proposition-2's infinite majorant"}],"hypotheses":[],"witnesses":[],"conclusions":[{"key":"result","proposition":{"def":{"id":"S-P-092","args":[{"var":"epsilon_int"},{"var":"xi"},{"var":"sigma"},{"var":"theta"},{"var":"y"},{"var":"x"}]}}}],"premises":[{"id":"MAP-P092-P044-1","producer":"P-044","closure_role":"REQUIRED","scope_binders":[{"key":"n","type":"Nat"}],"binder_map":{"epsilon_int":{"var":"epsilon_int"},"xi":{"var":"xi"},"sigma":{"var":"sigma"},"theta":{"var":"theta"},"y":{"var":"y"},"n":{"var":"n"}},"hypothesis_map":{"proposition_2_domain":{"guard":"MAP-P092-P044-1_proposition_2_domain"}},"witness_map":{},"consume":["proposition_2"],"guards":[{"key":"MAP-P092-P044-1_proposition_2_domain","proposition":{"proj":{"value":{"def":{"id":"S-P-044","args":[{"var":"epsilon_int"},{"var":"xi"},{"var":"sigma"},{"var":"theta"},{"var":"y"},{"var":"n"}]}},"index":0}}}]},{"id":"MAP-P092-P090-2","producer":"A-LATE-P090-EXISTS","closure_role":"REQUIRED","scope_binders":[{"key":"k","type":"Nat"},{"key":"n","type":"Nat"}],"binder_map":{"theta":{"var":"theta"},"y":{"var":"y"},"k":{"var":"k"},"sigma":{"var":"sigma"},"n":{"var":"n"}},"hypothesis_map":{},"witness_map":{},"consume":["existentialized"]},{"id":"MAP-P092-P091-3","producer":"P-091","closure_role":"REQUIRED","scope_binders":[{"key":"k_int","type":"Int"}],"binder_map":{"theta":{"var":"theta"},"x":{"var":"x"},"k":{"var":"k_int"}},"hypothesis_map":{},"witness_map":{},"consume":["result"]}],"witness_realizations":{},"proof_ref":"### P-092 \u2014 finite restriction of Proposition-2's infinite majorant"}
```

- Prenex statement: for every
  \(\varepsilon_{\rm int}\in(0,1/10]\), \(\xi>1\),
  \(\sigma\ge\theta\ge2\), \(y\in(0,1)\), \(x>U_0\), put
  \[
  q=1/2+\varepsilon_{\rm int},\quad
  a_{\rm pow}=-q\log y,\quad N=N_\theta(x).
  \]
  Then
  \[
  \sum_{U_0<n<x}f(n)\le
  (2\log\xi\log\theta/\log\sigma)^{a_{\rm pow}}
  \sum_{K_0\le k\le N}k^{a_{\rm pow}}S_k(x,y;\sigma,\theta).
  \]
  If \(N<K_0\), the right sum is empty and the left side is \(0\).
- Local equalities: exact \(U_0,q,a_{\rm pow},N,K_0,S_k\).
- Domain/range: finite k-sum; each retained k satisfies
  \(x>\theta^{2k-1}\).
- Input subject: P-044 infinite pointwise majorant summed over \(n\).
  Output subject: exact moving finite k-majorant.
- Premise maps:
  - P-044 — Binders:
    \(\varepsilon_{\rm int}:=\varepsilon_{\rm int},\xi:=\xi,
    \sigma:=\sigma,\theta:=\theta,y:=y,n:=n,
    q:=1/2+\varepsilon_{\rm int}\).
    Hypotheses: \(U_0<n<x\). Consumed: pointwise infinite majorant.
    Subject: sum it over the exact interval \(U_0<n<x\); interchange
    nonnegative \(n,k\)-sums. Constants: exact.
  - P-090 — Binders:
    \(y:=y,k:=k,\sigma:=\sigma,\theta:=\theta,n:=n\) for each term.
    Hypotheses: a nonzero \(f_k^\#(y,n)\) term.
    Consumed: \(\theta^{2k-1}<x\).
    Subject: exact D-013 support. Constants: none.
  - P-091 — Binders:
    \(\theta:=\theta,x:=x,k:=k\).
    Hypotheses: support inequality from P-090.
    Subject: exact cutoff. Constants: none.
- Derivation certificate: sum P-044, interchange by nonnegativity, and delete
  all \(k>N\) because their S-subject is identically zero. If \(N<K_0\),
  every term vanishes by the same implication.
- Source/S2 anchor: ET pp. 31–32; S2 R1 §6, R2.7.
- Definitions used: D-007, D-012, D-013, D-017, D-022.

### P-093 — exact logarithmic endpoint comparison

```mathminer-s3
{"schema":"mathminer.s3/1","id":"P-093","kind":"PROPOSITION","binders":[{"key":"theta","type":"Real"}],"uses_definitions":["D-006","D-022","S-P-093","W-P-093-c_plus"],"source_anchors":[{"path":"stage3/canonical/CURRENT.md","git":"4279cd5e01f75401a9f5fa12d42961fe46b9ac8b","anchor":"### P-093 \u2014 exact logarithmic endpoint comparison"}],"hypotheses":[],"witnesses":[{"key":"c_minus","type":"Real","depends_on":["theta"]},{"key":"c_plus","type":"Real","depends_on":["theta"]}],"conclusions":[{"key":"result","proposition":{"def":{"id":"S-P-093","args":[{"var":"theta"},{"var":"c_minus"},{"var":"c_plus"}]}}}],"premises":[{"id":"MAP-P093-P091-1","producer":"P-091","closure_role":"REQUIRED","scope_binders":[{"key":"x","type":"Real"},{"key":"k","type":"Int"}],"binder_map":{"theta":{"var":"theta"},"x":{"var":"x"},"k":{"var":"k"}},"hypothesis_map":{},"witness_map":{},"consume":["result"]}],"witness_realizations":{"c_minus":{"lit":{"type":"Real","value":"1"}},"c_plus":{"def":{"id":"W-P-093-c_plus","args":[{"var":"theta"}]}}},"proof_ref":"### P-093 \u2014 exact logarithmic endpoint comparison"}
```

- Prenex statement:
  \[
  \forall\theta\ge2\;\exists c_-(\theta),c_+(\theta)>0\;
  \forall x>0\;\forall k\in\mathbb Z,
  \]
  if \(k\le N_\theta(x)\), then, with \(N=N_\theta(x)\),
  \[
  \log(2x\theta^{1-2k})
  =\log2+2(X_\theta(x)-k)\log\theta,
  \]
  \[
  N-k<X_\theta(x)-k\le N-k+1,
  \]
  and
  \[
  c_-(\theta)(N-k+1)\le
  \ell(2x\theta^{1-2k})\le
  c_+(\theta)(N-k+1).
  \]
- Local equalities: exact D-022 \(X,N\).
- Domain/range: last cell \(k=N\) has \(N-k+1=1\); \(\ell\ge1\) prevents
  endpoint degeneration.
- Input subject: actual P3 logarithmic endpoint. Output: exact moving cell.
- Premise maps:
  - P-091 — Binders: \(\theta:=\theta,x:=x,k:=k\).
    Hypotheses: D-022 definitions. Consumed: \(N<X\le N+1\).
    Subject: subtract \(k\) to obtain the exact two inequalities.
    Constants: none.
- Derivation certificate: substitute the definition of \(X_\theta(x)\);
  use the displayed cell bounds. For \(N-k\ge1\), compare linearly; for the
  last cell, use \(1\le\ell\le\max(1,\log2+2\log\theta)\).
- Source/S2 anchor: ET p. 32 endpoint; S2 R1 §6.
- Definitions used: D-006, D-022.

### P-094 — negative-power adapter for \(s=(y-1)/2\)

```mathminer-s3
{"schema":"mathminer.s3/1","id":"P-094","kind":"PROPOSITION","binders":[{"key":"theta","type":"Real"},{"key":"y","type":"Real"},{"key":"x","type":"Real"},{"key":"k","type":"Int"}],"uses_definitions":["D-006","D-022","S-P-094"],"source_anchors":[{"path":"stage3/canonical/CURRENT.md","git":"4279cd5e01f75401a9f5fa12d42961fe46b9ac8b","anchor":"### P-094 — negative-power adapter for \\(s=(y-1)/2\\)"}],"hypotheses":[],"witnesses":[],"conclusions":[{"key":"result","proposition":{"def":{"id":"S-P-094","args":[{"var":"theta"},{"var":"y"},{"var":"x"},{"var":"k"}]}}}],"premises":[{"id":"MAP-P094-P093-1","producer":"P-093","closure_role":"REQUIRED","binder_map":{"theta":{"var":"theta"}},"hypothesis_map":{},"witness_map":{"c_minus":"p_094_p_093_1_c_minus","c_plus":"p_094_p_093_1_c_plus"},"consume":["result"]}],"witness_realizations":{},"proof_ref":"### P-094 — negative-power adapter for \\(s=(y-1)/2\\)"}
```

- Prenex statement: for every \(\theta\ge2\), choose the
  \(c_-(\theta),c_+(\theta)\) of P-093. For every \(y\in(0,1)\),
  \(x>0\), and integer \(k\le N=N_\theta(x)\), put
  \(s=(y-1)/2<0\). Then
  \[
  c_+(\theta)^s(N-k+1)^s
  \le\ell(2x\theta^{1-2k})^s
  \le c_-(\theta)^s(N-k+1)^s.
  \]
- Local equalities: \(s=(y-1)/2\).
- Domain/range: both bases positive.
- Input subject: P-093 comparison. Output: first exact power adapter.
- Premise maps:
  - P-093 — Binders:
    \(\theta:=\theta,x:=x,k:=k\); select its \(c_-,c_+\).
    Hypotheses: \(k\le N\). Consumed: two-sided endpoint comparison.
    Subject: raise both positive sides to \(s\).
    Constants: lower and upper constants reverse because \(s<0\);
    both remain functions only of \(\theta,y\).
- Derivation certificate: \(t\mapsto t^s\) is decreasing for \(s<0\).
- Source/S2 anchor: S2 R1 §6; mandated endpoint adapter.
- Definitions used: D-006, D-022.

### P-095 — negative-power adapter for \(s=-1/2\)

```mathminer-s3
{"schema":"mathminer.s3/1","id":"P-095","kind":"PROPOSITION","binders":[{"key":"theta","type":"Real"},{"key":"x","type":"Real"},{"key":"k","type":"Int"}],"uses_definitions":["D-006","D-022","S-P-095"],"source_anchors":[{"path":"stage3/canonical/CURRENT.md","git":"4279cd5e01f75401a9f5fa12d42961fe46b9ac8b","anchor":"### P-095 — negative-power adapter for \\(s=-1/2\\)"}],"hypotheses":[],"witnesses":[],"conclusions":[{"key":"result","proposition":{"def":{"id":"S-P-095","args":[{"var":"theta"},{"var":"x"},{"var":"k"}]}}}],"premises":[{"id":"MAP-P095-P093-1","producer":"P-093","closure_role":"REQUIRED","binder_map":{"theta":{"var":"theta"}},"hypothesis_map":{},"witness_map":{"c_minus":"p_095_p_093_1_c_minus","c_plus":"p_095_p_093_1_c_plus"},"consume":["result"]}],"witness_realizations":{},"proof_ref":"### P-095 — negative-power adapter for \\(s=-1/2\\)"}
```

- Prenex statement: for every \(\theta\ge2\), choose the P-093 constants.
  For every \(x>0\) and integer \(k\le N=N_\theta(x)\),
  \[
  c_+(\theta)^{-1/2}(N-k+1)^{-1/2}
  \le\ell(2x\theta^{1-2k})^{-1/2}
  \le c_-(\theta)^{-1/2}(N-k+1)^{-1/2}.
  \]
- Local equalities: exponent exactly \(-1/2\).
- Domain/range: positive bases; last cell safe.
- Input subject: P-093 comparison. Output: second exact power adapter.
- Premise maps:
  - P-093 — Binders:
    \(\theta:=\theta,x:=x,k:=k,N:=N_\theta(x)\).
    Hypotheses: \(k\le N\). Consumed: endpoint comparison.
    Subject: raise to \(-1/2\). Constants: directions reverse explicitly.
- Derivation certificate: decreasing negative power.
- Source/S2 anchor: S2 R1 §6; mandated endpoint adapter.
- Definitions used: D-006, D-022.

### P-096 — convergence-condition normalization

```mathminer-s3
{"schema":"mathminer.s3/1","id":"P-096","kind":"PROPOSITION","binders":[{"key":"y","type":"Real"},{"key":"epsilon_int","type":"Real"}],"uses_definitions":["S-P-096"],"source_anchors":[{"path":"stage3/canonical/CURRENT.md","git":"4279cd5e01f75401a9f5fa12d42961fe46b9ac8b","anchor":"### P-096 — convergence-condition normalization"}],"hypotheses":[],"witnesses":[],"conclusions":[{"key":"result","proposition":{"def":{"id":"S-P-096","args":[{"var":"y"},{"var":"epsilon_int"}]}}}],"premises":[],"witness_realizations":{},"proof_ref":"### P-096 — convergence-condition normalization"}
```

- Prenex statement: for every \(y\in(0,1)\) and
  \(\varepsilon_{\rm int}>0\), put
  \(a_{\rm pow}=-(1/2+\varepsilon_{\rm int})\log y\). If
  \[
  \varepsilon_{\rm int}<
  -{1-y+\tfrac12\log y\over\log y},
  \]
  then \(0<a_{\rm pow}<1-y\).
- Local equalities: exact \(a_{\rm pow}\).
- Domain/range: \(\log y<0\).
- Input subject: Proposition-4 condition. Output: exact power interval.
- Premise maps: none (root).
- Derivation certificate: multiply by the negative \(\log y\), reverse the
  inequality, and rearrange.
- Source/S2 anchor: ET pp. 31–32; S2 R1 (6.1)–(6.2).
- Definitions used: none.

### P-097 — exact main power tail

```mathminer-s3
{"schema":"mathminer.s3/1","id":"P-097","kind":"PROPOSITION","binders":[{"key":"y","type":"Real"},{"key":"a_pow","type":"Real"},{"key":"K_0","type":"Nat"}],"uses_definitions":["D-017","S-P-097"],"source_anchors":[{"path":"stage3/canonical/CURRENT.md","git":"4279cd5e01f75401a9f5fa12d42961fe46b9ac8b","anchor":"### P-097 — exact main power tail"}],"hypotheses":[],"witnesses":[],"conclusions":[{"key":"result","proposition":{"def":{"id":"S-P-097","args":[{"var":"y"},{"var":"a_pow"},{"var":"K_0"}]}}}],"premises":[],"witness_realizations":{},"proof_ref":"### P-097 — exact main power tail"}
```

- Prenex statement: for every \(y\in(0,1)\), every
  \(a_{\rm pow}\in(0,1-y)\), every integer \(K_0\ge1\),
  \[
  \sum_{k\ge K_0}k^{y-2+a_{\rm pow}}
  \le\left(1+{1\over1-y-a_{\rm pow}}\right)
  K_0^{y-1+a_{\rm pow}}.
  \]
  If \(K_0=K_0(\sigma,\theta)\), \(r_0=\log\sigma/\log\theta\), then
  \(\frac12r_0\le K_0\le\frac32r_0\).
- Local equalities: exact D-017 K0 in the second clause.
- Domain/range: exponent \(y-2+a_{\rm pow}<-1\).
- Input subject: main k-series. Output: exact lower-end tail.
- Premise maps: none (generic root; it does not cite P-096).
- Derivation certificate: integral comparison and ceiling inequalities.
- Source/S2 anchor: ET pp. 31–32; S2 R2.18–R2.19.
- Definitions used: D-017.

### P-098 — generic moving sum at \(s=(y-1)/2\)

```mathminer-s3
{"schema":"mathminer.s3/1","id":"P-098","kind":"PROPOSITION","binders":[{"key":"K_0","type":"Nat"},{"key":"y","type":"Real"},{"key":"a_pow","type":"Real"},{"key":"N","type":"Nat"}],"uses_definitions":["S-P-098"],"source_anchors":[{"path":"stage3/canonical/CURRENT.md","git":"4279cd5e01f75401a9f5fa12d42961fe46b9ac8b","anchor":"### P-098 — generic moving sum at \\(s=(y-1)/2\\)"}],"hypotheses":[],"witnesses":[],"conclusions":[{"key":"result","proposition":{"def":{"id":"S-P-098","args":[{"var":"K_0"},{"var":"y"},{"var":"a_pow"},{"var":"N"}]}}}],"premises":[],"witness_realizations":{},"proof_ref":"### P-098 — generic moving sum at \\(s=(y-1)/2\\)"}
```

- Prenex statement: for every fixed integer \(K_0\ge1\), every
  \(y\in(0,1)\), every \(a_{\rm pow}\in(0,1-y)\), put
  \(r=(y-3)/2+a_{\rm pow}\), \(s=(y-1)/2\). Then, as integer
  \(N\to\infty\),
  \[
  \sum_{K_0\le k\le N}k^r(N-k+1)^s=o(1).
  \]
- Local equalities: exact \(r,s\).
- Domain/range: \(s\in(-1/2,0)\).
- Input subject: abstract moving power sum. Output: exact \(o(1)\).
- Premise maps: none (generic root).
- Derivation certificate: split at \(N/2\); on the first half isolate fixed
  k and dominate the tail by \(k^{r+s}\); on the second obtain
  \(O(N^{r+s+1})\), with \(r+s+1=y-1+a_{\rm pow}<0\).
- Source/S2 anchor: ET p. 32; S2 R1 §6.
- Definitions used: none.

### P-099 — generic moving sum at exponent \(-1/2\)

```mathminer-s3
{"schema":"mathminer.s3/1","id":"P-099","kind":"PROPOSITION","binders":[{"key":"K_0","type":"Nat"},{"key":"y","type":"Real"},{"key":"a_pow","type":"Real"},{"key":"N","type":"Nat"}],"uses_definitions":["S-P-099"],"source_anchors":[{"path":"stage3/canonical/CURRENT.md","git":"4279cd5e01f75401a9f5fa12d42961fe46b9ac8b","anchor":"### P-099 — generic moving sum at exponent \\(-1/2\\)"}],"hypotheses":[],"witnesses":[],"conclusions":[{"key":"result","proposition":{"def":{"id":"S-P-099","args":[{"var":"K_0"},{"var":"y"},{"var":"a_pow"},{"var":"N"}]}}}],"premises":[],"witness_realizations":{},"proof_ref":"### P-099 — generic moving sum at exponent \\(-1/2\\)"}
```

- Prenex statement: for every fixed integer \(K_0\ge1\), every
  \(y\in(0,1)\), every \(a_{\rm pow}\in(0,1-y)\), put
  \(r=(y-3)/2+a_{\rm pow}\). Then, as \(N\to\infty\),
  \[
  \sum_{K_0\le k\le N}k^r(N-k+1)^{-1/2}=o(1).
  \]
- Local equalities: exact r.
- Input subject: abstract moving power sum. Output: exact \(o(1)\).
- Premise maps: none (generic root).
- Derivation certificate: split at \(N/2\); both endpoint portions decay by
  the displayed exponent inequality.
- Source/S2 anchor: ET p. 32; S2 R1 §6.
- Definitions used: none.

### P-100 — exact weighted logarithmic sum, exponent \((y-1)/2\)

```mathminer-s3
{"schema":"mathminer.s3/1","id":"P-100","kind":"PROPOSITION","binders":[{"key":"theta","type":"Real"},{"key":"sigma","type":"Real"},{"key":"K_0","type":"Nat"},{"key":"y","type":"Real"},{"key":"a_pow","type":"Real"},{"key":"x","type":"Real"}],"uses_definitions":["D-006","D-017","D-022","S-P-100"],"source_anchors":[{"path":"stage3/canonical/CURRENT.md","git":"4279cd5e01f75401a9f5fa12d42961fe46b9ac8b","anchor":"### P-100 \u2014 exact weighted logarithmic sum, exponent \\((y-1)/2\\)"}],"hypotheses":[],"witnesses":[],"conclusions":[{"key":"result","proposition":{"def":{"id":"S-P-100","args":[{"var":"theta"},{"var":"sigma"},{"var":"K_0"},{"var":"y"},{"var":"a_pow"},{"var":"x"}]}}}],"premises":[{"id":"MAP-P100-P094-1","producer":"P-094","closure_role":"REQUIRED","scope_binders":[{"key":"k","type":"Int"}],"binder_map":{"theta":{"var":"theta"},"y":{"var":"y"},"x":{"var":"x"},"k":{"var":"k"}},"hypothesis_map":{},"witness_map":{},"consume":["result"]},{"id":"MAP-P100-P098-2","producer":"P-098","closure_role":"REQUIRED","scope_binders":[{"key":"N","type":"Nat"}],"binder_map":{"K_0":{"var":"K_0"},"y":{"var":"y"},"a_pow":{"var":"a_pow"},"N":{"var":"N"}},"hypothesis_map":{},"witness_map":{},"consume":["result"]}],"witness_realizations":{},"proof_ref":"### P-100 \u2014 exact weighted logarithmic sum, exponent \\((y-1)/2\\)"}
```

- Prenex statement: for every fixed \(\theta\ge2,\sigma\ge\theta\),
  fixed \(K_0=K_0(\sigma,\theta)\), every \(y\in(0,1)\), and
  \(a_{\rm pow}\in(0,1-y)\), put
  \(r=(y-3)/2+a_{\rm pow}\), \(N=N_\theta(x)\). As \(x\to\infty\),
  \[
  \sum_{K_0\le k\le N}k^r
  \ell(2x\theta^{1-2k})^{(y-1)/2}=o(1).
  \]
- Local equalities: exact \(r,N,K_0\).
- Domain/range: \(N\to\infty\) as \(x\to\infty\).
- Input subject: actual P3 second logarithmic sum. Output: exact \(o(1)\).
- Premise maps:
  - P-094 — Binders:
    \(\theta:=\theta,y:=y,x:=x,k:=k,N:=N_\theta(x),
    s:=(y-1)/2\).
    Hypotheses: \(k\le N\). Consumed: upper negative-power comparison.
    Subject: each actual logarithmic factor maps to
    \(c_-(\theta)^s(N-k+1)^s\).
    Constants: \(c_-(\theta)^s\) is fixed in x,k.
  - P-098 — Binders:
    \(K_0:=K_0,y:=y,a_{\rm pow}:=a_{\rm pow},
    r:=(y-3)/2+a_{\rm pow},s:=(y-1)/2,N:=N_\theta(x)\).
    Consumed: generic moving-sum \(o(1)\).
    Subject: exact comparison target from P-094.
    Constants: multiplication by the fixed adapter preserves \(o(1)\).
- Derivation certificate: termwise adapter followed by the exact generic sum.
- Source/S2 anchor: ET p. 32; S2 R1 §6.
- Definitions used: D-006, D-017, D-022.

### P-101 — exact weighted logarithmic sum, exponent \(-1/2\)

```mathminer-s3
{"schema":"mathminer.s3/1","id":"P-101","kind":"PROPOSITION","binders":[{"key":"theta","type":"Real"},{"key":"sigma","type":"Real"},{"key":"K_0","type":"Nat"},{"key":"y","type":"Real"},{"key":"a_pow","type":"Real"},{"key":"x","type":"Real"}],"uses_definitions":["D-006","D-017","D-022","S-P-101"],"source_anchors":[{"path":"stage3/canonical/CURRENT.md","git":"4279cd5e01f75401a9f5fa12d42961fe46b9ac8b","anchor":"### P-101 \u2014 exact weighted logarithmic sum, exponent \\(-1/2\\)"}],"hypotheses":[],"witnesses":[],"conclusions":[{"key":"result","proposition":{"def":{"id":"S-P-101","args":[{"var":"theta"},{"var":"sigma"},{"var":"K_0"},{"var":"y"},{"var":"a_pow"},{"var":"x"}]}}}],"premises":[{"id":"MAP-P101-P095-1","producer":"P-095","closure_role":"REQUIRED","scope_binders":[{"key":"k","type":"Int"}],"binder_map":{"theta":{"var":"theta"},"x":{"var":"x"},"k":{"var":"k"}},"hypothesis_map":{},"witness_map":{},"consume":["result"]},{"id":"MAP-P101-P099-2","producer":"P-099","closure_role":"REQUIRED","scope_binders":[{"key":"N","type":"Nat"}],"binder_map":{"K_0":{"var":"K_0"},"y":{"var":"y"},"a_pow":{"var":"a_pow"},"N":{"var":"N"}},"hypothesis_map":{},"witness_map":{},"consume":["result"]}],"witness_realizations":{},"proof_ref":"### P-101 \u2014 exact weighted logarithmic sum, exponent \\(-1/2\\)"}
```

- Prenex statement: for every fixed \(\theta\ge2,\sigma\ge\theta\),
  fixed \(K_0=K_0(\sigma,\theta)\), every \(y\in(0,1)\), and every
  \(a_{\rm pow}\in(0,1-y)\), with \(r=(y-3)/2+a_{\rm pow}\) and
  \(N=N_\theta(x)\), as \(x\to\infty\),
  \[
  \sum_{K_0\le k\le N}k^r
  \ell(2x\theta^{1-2k})^{-1/2}=o(1).
  \]
- Local equalities: exact \(r,N,K_0\).
- Domain/range: \(N\to\infty\).
- Input subject: actual P3 terminal logarithmic sum. Output: exact \(o(1)\).
- Premise maps:
  - P-095 — Binders:
    \(\theta:=\theta,x:=x,k:=k,N:=N_\theta(x)\).
    Hypotheses: \(k\le N\). Consumed: upper \(-1/2\) comparison.
    Subject: actual log factor maps to
    \(c_-(\theta)^{-1/2}(N-k+1)^{-1/2}\).
    Constants: fixed in x,k.
  - P-099 — Binders:
    \(K_0:=K_0,y:=y,a_{\rm pow}:=a_{\rm pow},
    r:=(y-3)/2+a_{\rm pow},N:=N_\theta(x)\).
    Consumed: generic moving-sum \(o(1)\).
    Subject: exact P-095 comparison target.
    Constants: fixed adapter preserves \(o(1)\).
- Derivation certificate: termwise adapter then generic moving sum.
- Source/S2 anchor: ET p. 32; S2 R1 §6.
- Definitions used: D-006, D-017, D-022.

### P-102 — Proposition 4

Current construction binding: the exact `P102Statement` in the GroupA--GroupD source contracts, W0--W8, and the retained S7 provider. Any `mathminer-s3-legacy` block here is historical, not a proof.

```mathminer-s3-legacy
{"schema":"mathminer.s3/1","id":"P-102","kind":"PROPOSITION","binders":[{"key":"theta","type":"Real"},{"key":"y","type":"Real"},{"key":"epsilon_int","type":"Real"}],"uses_definitions":["D-006","D-007","D-012","D-017","D-022","S-P-102","W-P-102-C_P4"],"source_anchors":[{"path":"stage3/canonical/CURRENT.md","git":"4279cd5e01f75401a9f5fa12d42961fe46b9ac8b","anchor":"### P-102 \u2014 Proposition 4"}],"hypotheses":[],"witnesses":[{"key":"C_P4","type":"Real","depends_on":["theta","y","epsilon_int"]}],"conclusions":[{"key":"result","proposition":{"def":{"id":"S-P-102","args":[{"var":"theta"},{"var":"y"},{"var":"epsilon_int"},{"var":"C_P4"}]}}}],"premises":[{"id":"MAP-P102-P092-1","producer":"P-092","closure_role":"REQUIRED","scope_binders":[{"key":"xi","type":"Real"},{"key":"sigma","type":"Real"},{"key":"x","type":"Real"}],"binder_map":{"epsilon_int":{"var":"epsilon_int"},"xi":{"var":"xi"},"sigma":{"var":"sigma"},"theta":{"var":"theta"},"y":{"var":"y"},"x":{"var":"x"}},"hypothesis_map":{},"witness_map":{},"consume":["result"]},{"id":"MAP-P102-P089-2","producer":"P-089","closure_role":"REQUIRED","binder_map":{"theta":{"var":"theta"}},"hypothesis_map":{},"witness_map":{"C_3":"p_102_p_089_2_C_3"},"consume":["result"]},{"id":"MAP-P102-P096-3","producer":"P-096","closure_role":"REQUIRED","binder_map":{"y":{"var":"y"},"epsilon_int":{"var":"epsilon_int"}},"hypothesis_map":{},"witness_map":{},"consume":["result"]},{"id":"MAP-P102-P097-4","producer":"P-097","closure_role":"REQUIRED","scope_binders":[{"key":"a_pow","type":"Real"},{"key":"K_0","type":"Nat"}],"binder_map":{"y":{"var":"y"},"a_pow":{"var":"a_pow"},"K_0":{"var":"K_0"}},"hypothesis_map":{},"witness_map":{},"consume":["result"]},{"id":"MAP-P102-P100-5","producer":"P-100","closure_role":"REQUIRED","scope_binders":[{"key":"sigma","type":"Real"},{"key":"K_0","type":"Nat"},{"key":"a_pow","type":"Real"},{"key":"x","type":"Real"}],"binder_map":{"theta":{"var":"theta"},"sigma":{"var":"sigma"},"K_0":{"var":"K_0"},"y":{"var":"y"},"a_pow":{"var":"a_pow"},"x":{"var":"x"}},"hypothesis_map":{},"witness_map":{},"consume":["result"]},{"id":"MAP-P102-P101-6","producer":"P-101","closure_role":"REQUIRED","scope_binders":[{"key":"sigma","type":"Real"},{"key":"K_0","type":"Nat"},{"key":"a_pow","type":"Real"},{"key":"x","type":"Real"}],"binder_map":{"theta":{"var":"theta"},"sigma":{"var":"sigma"},"K_0":{"var":"K_0"},"y":{"var":"y"},"a_pow":{"var":"a_pow"},"x":{"var":"x"}},"hypothesis_map":{},"witness_map":{},"consume":["result"]}],"witness_realizations":{"C_P4":{"def":{"id":"W-P-102-C_P4","args":[{"var":"theta"},{"var":"y"},{"var":"epsilon_int"},{"var":"p_102_p_089_2_C_3"}]}}},"proof_ref":"### P-102 \u2014 Proposition 4"}
```

- Prenex statement:
  \[
  \forall\theta\ge2\;\forall y\in(0,1)\;
  \forall\varepsilon_{\rm int}\in(0,1/10],
  \]
  if
  \[
  \varepsilon_{\rm int}<
  -{1-y+\tfrac12\log y\over\log y},
  \]
  then there exists \(C_{\rm P4}(\theta,y,\varepsilon_{\rm int})>0\) such
  that for every \(\sigma\ge\theta\) and every \(\xi>1\), there exists a
  remainder witness
  \(r_{\theta,y,\varepsilon_{\rm int},\sigma,\xi}(x)\) satisfying
  \(r_{\theta,y,\varepsilon_{\rm int},\sigma,\xi}(x)=o(x)\), and, as
  \(x\to\infty\),
  \[
  \sum_{n<x}f(n)\le
  C_{\rm P4}(\theta,y,\varepsilon_{\rm int})
  x(\log\xi)^{-((1/2)+\varepsilon_{\rm int})\log y}
  (\log\sigma)^{-1}
  +r_{\theta,y,\varepsilon_{\rm int},\sigma,\xi}(x).
  \]
- Local equalities:
  \(a_{\rm pow}=-((1/2)+\varepsilon_{\rm int})\log y\),
  \(N=N_\theta(x)\), \(K_0=K_0(\sigma,\theta)\).
- Domain/range and exact dependency order:
  \[
  (\theta,y,\varepsilon_{\rm int}\text{ admissible})
  \longmapsto C_{\rm P4}>0
  \longmapsto(\sigma\ge\theta,\xi>1)
  \longmapsto r_{\theta,y,\varepsilon_{\rm int},\sigma,\xi}
  \longmapsto x\to\infty.
  \tag{P102-order}
  \]
  Thus the main coefficient is common to all \(\sigma,\xi\), whereas the
  little-o witness is only pointwise for each fixed \((\sigma,\xi)\).  The
  \(n\le U_0\) sum is finite after that pair is fixed.
- Input subject: exact P-092 finite k-majorant.
  Output subject: exact Proposition-4 mean.
- Premise maps:
  - P-092 — Binders:
    \(\varepsilon_{\rm int}:=\varepsilon_{\rm int},\xi:=\xi,
    \sigma:=\sigma,\theta:=\theta,y:=y,x:=x,
    q:=1/2+\varepsilon_{\rm int},
    a_{\rm pow}:=-q\log y,N:=N_\theta(x)\).
    Hypotheses: \(x>U_0\). Consumed: finite-support majorant.
    Subject: exact mean over \(U_0<n<x\). Constants: exact prefactor.
  - P-089 — Binders:
    \(\theta:=\theta,y:=y,k:=k,\sigma:=\sigma,x:=x\)
    for every \(K_0\le k\le N\).
    Hypotheses: P-092 supplies \(x>\theta^{2k-1}\).
    Consumed: Proposition-3 bound. Subject: exact \(S_k\).
    Constants: the mapped factor is exactly \(C_3(\theta)/y\). The P-102
    prefix has already fixed \(y\) before choosing \(C_{\rm P4}\), so this
    finite factor is absorbed only at this point; no pre-\(y\) uniformity is
    claimed. Through P-089, its numerator contains the exact scoped descendant
    of \(C_4(C_{\rm fam},\theta)\), never a free \(C_4\) symbol.
  - P-096 — Binders:
    \(y:=y,\varepsilon_{\rm int}:=\varepsilon_{\rm int},
    a_{\rm pow}:=-((1/2)+\varepsilon_{\rm int})\log y\).
    Hypotheses: consumer admissibility condition.
    Consumed: \(0<a_{\rm pow}<1-y\).
    Subject: exact exponent in P-092. Constants: none.
  - P-097 — Binders:
    \(y:=y,a_{\rm pow}:=a_{\rm pow},K_0:=K_0(\sigma,\theta)\).
    Hypotheses: P-096. Consumed: main k-tail and K0 comparison.
    Subject: first P3 brace sum
    \(k^{y-2+a_{\rm pow}}\). Constants: its factor leaves exactly
    \((\log\sigma)^{-1}\) after the P-092/P3 powers combine.
  - P-100 — Binders:
    \(\theta:=\theta,\sigma:=\sigma,K_0:=K_0(\sigma,\theta),
    y:=y,a_{\rm pow}:=a_{\rm pow},x:=x,N:=N_\theta(x)\).
    Hypotheses: P-096, fixed \(\theta,\sigma,K_0\).
    Consumed: second actual moving-log \(o(1)\).
    Subject: second P3 brace sum exactly. Constants: fixed endpoint adapter.
  - P-101 — Binders:
    \(\theta:=\theta,\sigma:=\sigma,K_0:=K_0(\sigma,\theta),
    y:=y,a_{\rm pow}:=a_{\rm pow},x:=x,N:=N_\theta(x)\).
    Hypotheses: P-096. Consumed: terminal actual moving-log \(o(1)\).
    Subject: third P3 brace sum exactly; the fixed
    \((\log\sigma)^{y/2}\) remains outside. Constants: fixed.
- Derivation certificate: insert P-089 into P-092; evaluate the main tail;
  use both exact moving-log maps; restore the fixed finite
  \(\sum_{n\le U_0}f(n)=o(x)\).  The common main coefficient is selected
  from the P-089/P-097 bounds after \((\theta,y,\varepsilon_{\rm int})\) and
  before \((\sigma,\xi)\); after fixing the latter pair, sum the two
  P-100/P-101 moving-endpoint remainders and the finite-initial remainder to
  obtain the displayed pointwise witness.  No remainder witness is selected
  before \((\sigma,\xi)\).
- Source/S2 anchor: ET Proposition 4, pp. 31–32; S2 R1 §6, R2.7, R3.6,
  and S2B R3 fixed-\(y\) propagation.
- Definitions used: D-006, D-007, D-012, D-017, D-022.

## 11. Optimization, Theorem 1, and literal target

### P-110 — specialization at \(\sigma=\theta=2\)

```mathminer-s3
{"schema":"mathminer.s3/1","id":"P-110","kind":"PROPOSITION","binders":[{"key":"n","type":"Nat"}],"uses_definitions":["D-001","D-002","D-004","D-006","S-P-110"],"source_anchors":[{"path":"stage3/canonical/CURRENT.md","git":"4279cd5e01f75401a9f5fa12d42961fe46b9ac8b","anchor":"### P-110 — specialization at \\(\\sigma=\\theta=2\\)"}],"hypotheses":[],"witnesses":[],"conclusions":[{"key":"result","proposition":{"def":{"id":"S-P-110","args":[{"var":"n"}]}}}],"premises":[],"witness_realizations":{},"proof_ref":"### P-110 — specialization at \\(\\sigma=\\theta=2\\)"}
```

- Prenex statement: for every \(n>0\),
  \[
  \chi(n,2)=1,\qquad\tau(n,2)=\tau(n),\qquad
  \tau^+(n,2)=\tau^+(n),\qquad\rho_2=1.
  \]
- Local equalities: the product defining \(\rho_2\) is empty.
- Domain/range: positive integers.
- Input subject: D-001/D-002/D-004/D-006 at 2. Output: exact equalities.
- Premise maps: none (root).
- Derivation certificate: every prime is at least 2; the empty product is 1.
- Source/S2 anchor: ET p. 32; S2 R1 §7.
- Definitions used: D-001, D-002, D-004, D-006.

### P-111 — small ratio forces large \(f\)

```mathminer-s3
{"schema":"mathminer.s3/1","id":"P-111","kind":"PROPOSITION","binders":[{"key":"epsilon_int","type":"Real"},{"key":"xi","type":"Real"},{"key":"n","type":"Nat"},{"key":"alpha","type":"Real"}],"uses_definitions":["D-001","D-004","D-006","D-010","D-012","D-S45-P020-A","S-P-031","S-P-111"],"source_anchors":[{"path":"stage3/canonical/CURRENT.md","git":"4279cd5e01f75401a9f5fa12d42961fe46b9ac8b","anchor":"### P-111 — small ratio forces large \\(f\\)"}],"hypotheses":[],"witnesses":[],"conclusions":[{"key":"result","proposition":{"def":{"id":"S-P-111","args":[{"var":"epsilon_int"},{"var":"xi"},{"var":"n"},{"var":"alpha"}]}}}],"premises":[{"id":"MAP-P111-P034-1","producer":"P-034","closure_role":"REQUIRED","binder_map":{"epsilon_int":{"var":"epsilon_int"},"xi":{"var":"xi"},"sigma":{"lit":{"type":"Real","value":"2"}},"theta":{"lit":{"type":"Real","value":"2"}},"n":{"var":"n"},"A":{"def":{"id":"D-S45-P020-A","args":[{"var":"epsilon_int"},{"var":"xi"},{"lit":{"type":"Real","value":"2"}},{"lit":{"type":"Real","value":"2"}},{"lit":{"type":"Real","value":"1"}},{"lit":{"type":"Real","value":"2"}}]}}},"hypothesis_map":{"l4_member":{"guard":"MAP-P111-P034-1_l4_member"}},"witness_map":{},"consume":["proposition_1"],"guards":[{"key":"MAP-P111-P034-1_l4_member","proposition":{"proj":{"value":{"def":{"id":"S-P-031","args":[{"var":"epsilon_int"},{"var":"xi"},{"lit":{"type":"Real","value":"2"}},{"lit":{"type":"Real","value":"2"}},{"def":{"id":"D-S45-P020-A","args":[{"var":"epsilon_int"},{"var":"xi"},{"lit":{"type":"Real","value":"2"}},{"lit":{"type":"Real","value":"2"}},{"lit":{"type":"Real","value":"1"}},{"lit":{"type":"Real","value":"2"}}]}},{"var":"n"}]}},"index":0}}}]},{"id":"MAP-P111-P110-2","producer":"P-110","closure_role":"REQUIRED","binder_map":{"n":{"var":"n"}},"hypothesis_map":{},"witness_map":{},"consume":["result"]}],"witness_realizations":{},"proof_ref":"### P-111 — small ratio forces large \\(f\\)"}
```

- Prenex statement: for every
  \(\varepsilon_{\rm int}\in(0,1/10]\), \(\xi>1\),
  every \(\mathcal A\) with
  L4Spec\((\varepsilon_{\rm int},\xi,2,2,\mathcal A)\), every
  \(n\in\mathcal A\), and every \(\alpha\in(0,2/5]\), if
  \(\tau^+(n)\le\alpha\tau(n)\), then
  \[
  f(n)\ge {4\over5\alpha}-1\ge {2\over5\alpha}.
  \]
- Local equalities: \(\sigma=\theta=2\).
- Domain/range: \(\tau,\tau^+>0\).
- Input subject: exact event \(n\in E_\alpha\cap\mathcal A\).
  Output subject: pointwise lower bound on f.
- Premise maps:
  - P-034 — Binders:
    \(\varepsilon_{\rm int},\xi,\sigma:=2,\theta:=2,\mathcal A,n\).
    Hypotheses: L4Spec and \(n\in\mathcal A\).
    Consumed: Proposition-1 inequality.
    Subject: exact Q/f relation from D-012. Constants: none.
  - P-110 — Binders: \(n:=n\). Hypotheses: positivity.
    Subject: converts the P-034 ratio to \(\tau(n)/\tau^+(n)\).
    Constants: exact.
- Derivation certificate: rearrange P-034 using
  \(\tau^+\le\alpha\tau\); the final inequality uses \(\alpha\le2/5\).
- Source/S2 anchor: ET p. 32; S2 R1 (7.2)–(7.3).
- Definitions used: D-001, D-004, D-010, D-012, D-022.

### P-112 — threshold-parametric density bound

Current construction binding: the exact `P112Statement` in the GroupA--GroupD source contracts, W0--W8, and the retained S7 provider. Any `mathminer-s3-legacy` block here is historical, not a proof.

```mathminer-s3-legacy
{"schema":"mathminer.s3/1","id":"P-112","kind":"PROPOSITION","binders":[{"key":"epsilon_int","type":"Real"},{"key":"y","type":"Real"}],"uses_definitions":["D-006","D-022","D-LATE-P020-W","D-S45-EPS-DOMAIN","D-S45-P020-DOMAIN","D-S811-P020-FIXED-W","S-P-112","W-P-112-C_den"],"source_anchors":[{"path":"stage3/canonical/CURRENT.md","git":"4279cd5e01f75401a9f5fa12d42961fe46b9ac8b","anchor":"### P-112 — threshold-parametric density bound"}],"hypotheses":[],"witnesses":[{"key":"C_grid","type":"Real","depends_on":["epsilon_int"]},{"key":"Xi_0","type":"Real","depends_on":["epsilon_int"]},{"key":"C_P4","type":"Real","depends_on":["epsilon_int","y"]},{"key":"C_den","type":"Real","depends_on":["epsilon_int","y"]}],"conclusions":[{"key":"result","proposition":{"def":{"id":"S-P-112","args":[{"var":"epsilon_int"},{"var":"y"},{"var":"C_grid"},{"var":"Xi_0"},{"var":"C_P4"},{"var":"C_den"}]}}}],"premises":[{"id":"MAP-P112-P020-1","producer":"A-LATE-P020-EXISTS","closure_role":"REQUIRED","scope_binders":[{"key":"xi","type":"Real"}],"binder_map":{"epsilon_int":{"var":"epsilon_int"},"xi":{"var":"xi"},"sigma":{"lit":{"type":"Real","value":"2"}},"theta":{"lit":{"type":"Real","value":"2"}}},"hypothesis_map":{"domain":{"guard":"MAP-P112-P020-1_domain"},"epsilon_domain":{"guard":"MAP-P112-P020-1_epsilon_domain"}},"witness_map":{},"consume":["existentialized"],"guards":[{"key":"MAP-P112-P020-1_domain","proposition":{"def":{"id":"D-S45-P020-DOMAIN","args":[{"var":"epsilon_int"},{"var":"xi"},{"lit":{"type":"Real","value":"2"}},{"lit":{"type":"Real","value":"2"}}]}}},{"key":"MAP-P112-P020-1_epsilon_domain","proposition":{"def":{"id":"D-S45-EPS-DOMAIN","args":[{"var":"epsilon_int"}]}}}]},{"id":"MAP-P112-P102-2","producer":"P-102","closure_role":"REQUIRED","binder_map":{"theta":{"lit":{"type":"Real","value":"2"}},"y":{"var":"y"},"epsilon_int":{"var":"epsilon_int"}},"hypothesis_map":{},"witness_map":{"C_P4":"p_112_p_102_2_C_P4"},"consume":["result"]},{"id":"MAP-P112-P111-3","producer":"P-111","closure_role":"REQUIRED","scope_binders":[{"key":"xi","type":"Real"},{"key":"n","type":"Nat"},{"key":"alpha","type":"Real"}],"binder_map":{"epsilon_int":{"var":"epsilon_int"},"xi":{"var":"xi"},"n":{"var":"n"},"alpha":{"var":"alpha"}},"hypothesis_map":{},"witness_map":{},"consume":["result"]},{"id":"MAP-P112-P110-4","producer":"P-110","closure_role":"REQUIRED","scope_binders":[{"key":"n","type":"Nat"}],"binder_map":{"n":{"var":"n"}},"hypothesis_map":{},"witness_map":{},"consume":["result"]}],"witness_realizations":{"C_grid":{"proj":{"value":{"def":{"id":"D-S811-P020-FIXED-W","args":[{"var":"epsilon_int"}]}},"index":0}},"Xi_0":{"proj":{"value":{"def":{"id":"D-S811-P020-FIXED-W","args":[{"var":"epsilon_int"}]}},"index":1}},"C_P4":{"var":"p_112_p_102_2_C_P4"},"C_den":{"def":{"id":"W-P-112-C_den","args":[{"var":"epsilon_int"},{"var":"y"},{"proj":{"value":{"def":{"id":"D-S811-P020-FIXED-W","args":[{"var":"epsilon_int"}]}},"index":0}},{"proj":{"value":{"def":{"id":"D-S811-P020-FIXED-W","args":[{"var":"epsilon_int"}]}},"index":1}},{"var":"p_112_p_102_2_C_P4"}]}}},"proof_ref":"### P-112 — threshold-parametric density bound"}
```

- Prenex statement: for every
  \(\varepsilon_{\rm int}\in(0,1/10]\) and every \(y\in(0,1)\) satisfying
  \[
  \varepsilon_{\rm int}<
  -{1-y+\tfrac12\log y\over\log y},
  \]
  there exist \(C_{\rm grid}>0,\Xi_0>1\), the single specialized coefficient
  \(C_{\rm P4}(2,y,\varepsilon_{\rm int})>0\), and \(C_{\rm den}>0\), all
  selected before every
  \(\xi\ge\Xi_0\) and every \(\alpha\in(0,2/5]\), putting
  \[
  a_{\rm bal}=-((1/2)+\varepsilon_{\rm int})\log y,\qquad
  b_{\rm bal}=(9/10)\varepsilon_{\rm int}^2,
  \]
  \[
  \bar d(E_\alpha)\le C_{\rm den}
  \{\alpha(\log\xi)^{a_{\rm bal}}+(\log\xi)^{-b_{\rm bal}}\}.
  \]
- Local equalities: exact \(a_{\rm bal},b_{\rm bal}\).
- Domain/range: after fixed \((\varepsilon_{\rm int},y)\), first select
  \(C_{\rm grid},\Xi_0\) from P-020 and the one P-102 main coefficient at
  \(\theta=\sigma=2\), then absorb these into \(C_{\rm den}\); all four
  witnesses precede uniform \((\xi,\alpha)\).  The P-102 remainder remains
  pointwise in each fixed \(\xi\), exactly as required before taking the
  density limsup.
- Input subject: exact event \(E_\alpha\). Output: two-term density bound.
- Premise maps:
  - P-020 — Binders:
    \(\varepsilon_{\rm int}:=\varepsilon_{\rm int}\); select its
    \(C_{\rm grid},\Xi_0\); then \(\xi:=\xi,\sigma:=2,\theta:=2\), and
    select the resulting \(\mathcal A\).
    Hypotheses: \(\xi\ge\Xi_0\).
    Consumed: L4Spec for one common \(\mathcal A\).
    Subject: the complement has upper density at most
    \((\log\xi)^{-b_{\rm bal}}\) because \(\rho_2=1\).
    Constants: witness order retained exactly.
  - P-102 — Binders:
    first \(\theta:=2,y:=y,
    \varepsilon_{\rm int}:=\varepsilon_{\rm int}\), then select the single
    \(C_{\rm P4}(2,y,\varepsilon_{\rm int})\); only afterward bind
    \(\sigma:=2,\xi:=\xi\), select the permitted
    \(r_{2,y,\varepsilon_{\rm int},2,\xi}\), and let \(x\to\infty\).
    Hypotheses: consumer admissibility condition.
    Consumed: mean bound for f.
    Subject: exact D-012 f. Constants:
    The already selected \(C_{\rm P4}(2,y,\varepsilon_{\rm int})\) is
    absorbed into \(C_{\rm den}\), uniform in \(\xi,\alpha\); the pointwise
    remainder disappears only after the \(x\)-limsup for that fixed \(\xi\).
  - P-111 — Binders:
    \(\varepsilon_{\rm int}:=\varepsilon_{\rm int},\xi:=\xi,
    \mathcal A:=\mathcal A,n:=n,\alpha:=\alpha\).
    Hypotheses: \(n\in E_\alpha\cap\mathcal A\), \(0<\alpha\le2/5\).
    Consumed: \(f(n)\ge2/(5\alpha)\).
    Subject: exact E-event. Constants: Markov adds only an absolute factor.
  - P-110 — Binders: \(n:=n\). Hypotheses: none.
    Consumed: \(\rho_2=1\) and all 2-specializations.
    Subject: exact complement-density and event identities. Constants: exact.
- Derivation certificate: split \(E_\alpha\) into its intersection with
  \(\mathcal A\) and its complement; bound the complement by L4Spec and the
  intersection by Markov using P-111/P-102.
- Source/S2 anchor: ET p. 32; S2 R1 (7.1)–(7.3).
- Definitions used: D-006, D-010, D-012, D-022.

### P-113 — admissible parameter selection

```mathminer-s3
{"schema":"mathminer.s3/1","id":"P-113","kind":"PROPOSITION","binders":[{"key":"delta","type":"Real"}],"uses_definitions":["S-P-113","W-P-113-y_delta"],"source_anchors":[{"path":"stage3/canonical/CURRENT.md","git":"4279cd5e01f75401a9f5fa12d42961fe46b9ac8b","anchor":"### P-113 — admissible parameter selection"}],"hypotheses":[],"witnesses":[{"key":"y_delta","type":"Real","depends_on":["delta"]}],"conclusions":[{"key":"result","proposition":{"def":{"id":"S-P-113","args":[{"var":"delta"},{"var":"y_delta"}]}}}],"premises":[],"witness_realizations":{"y_delta":{"def":{"id":"W-P-113-y_delta","args":[{"var":"delta"}]}}},"proof_ref":"### P-113 — admissible parameter selection"}
```

- Prenex statement:
  \[
  \forall\delta\in(0,1)\;\exists y\in(0,1):
  \]
  \[
  {1\over10}<
  -{1-y+\tfrac12\log y\over\log y}
  \quad\land\quad
  {0.009\over0.009-0.6\log y}\ge1-\delta.
  \]
- Local equalities:
  \(a_{\rm bal}=-0.6\log y\), \(b_{\rm bal}=0.009\).
- Domain/range: y is selected after delta and before every alpha.
- Input subject: desired exponent loss. Output: exact admissible y.
- Premise maps: none (root).
- Derivation certificate: as \(y\uparrow1\), the admissible upper bound tends
  to \(1/2\) and the displayed quotient tends continuously to 1.
- Source/S2 anchor: ET p. 32; S2 R1 (7.5), R2.8.
- Definitions used: none.

### P-114 — balance identity with all defining equations

```mathminer-s3
{"schema":"mathminer.s3/1","id":"P-114","kind":"PROPOSITION","binders":[{"key":"y","type":"Real"},{"key":"alpha","type":"Real"}],"uses_definitions":["S-P-114"],"source_anchors":[{"path":"stage3/canonical/CURRENT.md","git":"4279cd5e01f75401a9f5fa12d42961fe46b9ac8b","anchor":"### P-114 — balance identity with all defining equations"}],"hypotheses":[],"witnesses":[],"conclusions":[{"key":"result","proposition":{"def":{"id":"S-P-114","args":[{"var":"y"},{"var":"alpha"}]}}}],"premises":[],"witness_realizations":{},"proof_ref":"### P-114 — balance identity with all defining equations"}
```

- Prenex statement: for every \(y\in(0,1)\), every \(\alpha\in(0,1)\), put
  \[
  a_{\rm bal}=-0.6\log y,\qquad b_{\rm bal}=0.009,\qquad
  L=\alpha^{-1/(a_{\rm bal}+b_{\rm bal})},\qquad
  \log\xi=L.
  \]
  Then
  \[
  \alpha L^{a_{\rm bal}}=L^{-b_{\rm bal}}
  =\alpha^{b_{\rm bal}/(a_{\rm bal}+b_{\rm bal})},
  \quad
  {b_{\rm bal}\over a_{\rm bal}+b_{\rm bal}}
  ={0.009\over0.009-0.6\log y}.
  \]
- Local equalities: all four equations appear in the prefix.
- Input subject: two terms in P-112. Output: exact common balanced power.
- Premise maps: none (root transformation-result proposition).
- Derivation certificate: direct exponent arithmetic.
- Source/S2 anchor: ET p. 32 with S2 repaired
  \(\varepsilon_{\rm int}=1/10\); S2 R1 (7.4)–(7.5).
- Definitions used: none.

### P-115 — optimized small-\(\alpha\) density

Current construction binding: the exact `P115Statement` in the GroupA--GroupD source contracts, W0--W8, and the retained S7 provider. Any `mathminer-s3-legacy` block here is historical, not a proof.

```mathminer-s3-legacy
{"schema":"mathminer.s3/1","id":"P-115","kind":"PROPOSITION","binders":[{"key":"delta","type":"Real"},{"key":"y","type":"Real"}],"uses_definitions":["D-006","D-022","S-P-115","W-P-115-C_small","W-P-115-alpha_0"],"source_anchors":[{"path":"stage3/canonical/CURRENT.md","git":"4279cd5e01f75401a9f5fa12d42961fe46b9ac8b","anchor":"### P-115 \u2014 optimized small-\\(\\alpha\\) density"}],"hypotheses":[],"witnesses":[{"key":"C_grid","type":"Real","depends_on":["delta","y"]},{"key":"Xi_0","type":"Real","depends_on":["delta","y"]},{"key":"C_P4","type":"Real","depends_on":["delta","y"]},{"key":"C_den","type":"Real","depends_on":["delta","y"]},{"key":"alpha_0","type":"Real","depends_on":["delta","y"]},{"key":"C_small","type":"Real","depends_on":["delta","y"]}],"conclusions":[{"key":"result","proposition":{"def":{"id":"S-P-115","args":[{"var":"delta"},{"var":"y"},{"var":"C_grid"},{"var":"Xi_0"},{"var":"C_P4"},{"var":"C_den"},{"var":"alpha_0"},{"var":"C_small"}]}}}],"premises":[{"id":"MAP-P115-P112-1","producer":"P-112","closure_role":"REQUIRED","binder_map":{"epsilon_int":{"lit":{"type":"Real","value":"1/10"}},"y":{"var":"y"}},"hypothesis_map":{},"witness_map":{"C_grid":"p_115_p_112_1_C_grid","Xi_0":"p_115_p_112_1_Xi_0","C_P4":"p_115_p_112_1_C_P4","C_den":"p_115_p_112_1_C_den"},"consume":["result"]},{"id":"MAP-P115-P114-2","producer":"P-114","closure_role":"REQUIRED","scope_binders":[{"key":"alpha","type":"Real"}],"binder_map":{"y":{"var":"y"},"alpha":{"var":"alpha"}},"hypothesis_map":{},"witness_map":{},"consume":["result"]}],"witness_realizations":{"C_grid":{"var":"p_115_p_112_1_C_grid"},"Xi_0":{"var":"p_115_p_112_1_Xi_0"},"C_P4":{"var":"p_115_p_112_1_C_P4"},"C_den":{"var":"p_115_p_112_1_C_den"},"alpha_0":{"def":{"id":"W-P-115-alpha_0","args":[{"var":"delta"},{"var":"y"},{"var":"p_115_p_112_1_C_grid"},{"var":"p_115_p_112_1_Xi_0"},{"var":"p_115_p_112_1_C_P4"},{"var":"p_115_p_112_1_C_den"}]}},"C_small":{"def":{"id":"W-P-115-C_small","args":[{"var":"delta"},{"var":"y"},{"var":"p_115_p_112_1_C_grid"},{"var":"p_115_p_112_1_Xi_0"},{"var":"p_115_p_112_1_C_P4"},{"var":"p_115_p_112_1_C_den"}]}}},"proof_ref":"### P-115 \u2014 optimized small-\\(\\alpha\\) density"}
```

- Prenex statement: for every \(\delta\in(0,1)\), every \(y\in(0,1)\)
  satisfying both conclusions of P-113, put
  \(a_{\rm bal}=-0.6\log y\), \(b_{\rm bal}=0.009\). Then there exist
  \[
  C_{\rm grid}>0,\quad\Xi_0>1,\quad
  C_{\rm P4}(2,y,1/10)>0,\quad C_{\rm den}>0,\quad
  \alpha_0\in(0,2/5],\quad C_{\rm small}>0
  \]
  such that for every \(\alpha\in(0,\alpha_0)\), putting
  \[
  L=\alpha^{-1/(a_{\rm bal}+b_{\rm bal})},\qquad
  \log\xi=L,
  \]
  one has \(\xi\ge\Xi_0\) and
  \[
  \bar d(E_\alpha)\le C_{\rm small}\alpha^{1-\delta}.
  \]
- Local equalities: exact \(a_{\rm bal},b_{\rm bal},L,\xi\).
- Domain/range: after fixed \((\delta,y)\), the P-112 witnesses occur in the
  exact order
  \((C_{\rm grid},\Xi_0,C_{\rm P4},C_{\rm den})\), then
  \((\alpha_0,C_{\rm small})\); all are selected before uniform alpha.
- Input subject: P-112 two-term bound. Output: small-alpha power bound.
- Premise maps:
  - P-112 — Binders:
    \(\varepsilon_{\rm int}:=1/10,y:=y\);
    select \(C_{\rm grid},\Xi_0,C_{\rm P4}(2,y,1/10),C_{\rm den}\);
    \(\xi:=\exp(L)\), \(\alpha:=\alpha\).
    Hypotheses: first P-113 inequality is exactly P-112 admissibility;
    \(\alpha_0\) is chosen so \(\exp(L)\ge\Xi_0\).
    Consumed: two-term density bound.
    Subject: \(\log\xi=L\), so its two terms are the P-114 subjects.
    Constants: the already pre-\(\xi\) P-102 coefficient is contained in
    \(C_{\rm den}\), and \(C_{\rm den}\mapsto C_{\rm small}\), independent
    of alpha.  Substituting the alpha-dependent \(\xi=\exp(L)\) therefore
    changes no main coefficient.
  - P-114 — Binders:
    \(y:=y,\alpha:=\alpha,a_{\rm bal}:=-0.6\log y,
    b_{\rm bal}:=0.009,
    L:=\alpha^{-1/(a_{\rm bal}+b_{\rm bal})},
    \xi:=\exp(L)\).
    Hypotheses: \(0<\alpha<\alpha_0\le1\).
    Consumed: balance identity and exponent quotient.
    Subject: both P-112 terms become
    \(\alpha^{b_{\rm bal}/(a_{\rm bal}+b_{\rm bal})}\).
    Constants: exact.
- Derivation certificate: since the P-113 exponent quotient is at least
  \(1-\delta\), decreasing-power monotonicity on \((0,1]\) gives the desired
  alpha exponent; choose \(\alpha_0\) to meet the L4 threshold.
- Source/S2 anchor: ET p. 32; S2 R1 §7 and R2.8.
- Definitions used: D-006, D-022.

### P-116 — compact alpha completion

```mathminer-s3
{"schema":"mathminer.s3/1","id":"P-116","kind":"PROPOSITION","binders":[{"key":"delta","type":"Real"},{"key":"alpha_0","type":"Real"},{"key":"alpha","type":"Real"}],"uses_definitions":["D-006","D-022","S-P-116"],"source_anchors":[{"path":"stage3/canonical/CURRENT.md","git":"4279cd5e01f75401a9f5fa12d42961fe46b9ac8b","anchor":"### P-116 — compact alpha completion"}],"hypotheses":[],"witnesses":[],"conclusions":[{"key":"result","proposition":{"def":{"id":"S-P-116","args":[{"var":"delta"},{"var":"alpha_0"},{"var":"alpha"}]}}}],"premises":[],"witness_realizations":{},"proof_ref":"### P-116 — compact alpha completion"}
```

- Prenex statement: for every \(\delta\in(0,1)\), every
  \(\alpha_0\in(0,1]\), and every \(\alpha\in[\alpha_0,1]\),
  \[
  \bar d(E_\alpha)\le1
  \le\alpha_0^{-(1-\delta)}\alpha^{1-\delta}.
  \]
- Local equalities: none.
- Input subject: E-event. Output: uniform compact-range bound.
- Premise maps: none (root).
- Derivation certificate: upper density is at most 1 and
  \(\alpha^{1-\delta}\ge\alpha_0^{1-\delta}\).
- Source/S2 anchor: ET p. 32 endpoint completion; S2 R1 §7.
- Definitions used: D-006, D-022.

### P-117 — Theorem 1, interior, with uniform constant order

Current construction binding: the exact `P117Statement` in the GroupA--GroupD source contracts, W0--W8, and the retained S7 provider. Any `mathminer-s3-legacy` block here is historical, not a proof.

```mathminer-s3-legacy
{"schema":"mathminer.s3/1","id":"P-117","kind":"PROPOSITION","binders":[{"key":"delta","type":"Real"}],"uses_definitions":["D-006","D-022","S-P-117","W-P-117-C_delta"],"source_anchors":[{"path":"stage3/canonical/CURRENT.md","git":"4279cd5e01f75401a9f5fa12d42961fe46b9ac8b","anchor":"### P-117 \u2014 Theorem 1, interior, with uniform constant order"}],"hypotheses":[],"witnesses":[{"key":"C_delta","type":"Real","depends_on":["delta"]}],"conclusions":[{"key":"result","proposition":{"def":{"id":"S-P-117","args":[{"var":"delta"},{"var":"C_delta"}]}}}],"premises":[{"id":"MAP-P117-P113-1","producer":"P-113","closure_role":"REQUIRED","binder_map":{"delta":{"var":"delta"}},"hypothesis_map":{},"witness_map":{"y_delta":"p_117_p_113_1_y_delta"},"consume":["result"]},{"id":"MAP-P117-P115-2","producer":"P-115","closure_role":"REQUIRED","binder_map":{"delta":{"var":"delta"},"y":{"var":"p_117_p_113_1_y_delta"}},"hypothesis_map":{},"witness_map":{"C_grid":"p_117_p_115_2_C_grid","Xi_0":"p_117_p_115_2_Xi_0","C_P4":"p_117_p_115_2_C_P4","C_den":"p_117_p_115_2_C_den","alpha_0":"p_117_p_115_2_alpha_0","C_small":"p_117_p_115_2_C_small"},"consume":["result"]},{"id":"MAP-P117-P116-3","producer":"P-116","closure_role":"REQUIRED","scope_binders":[{"key":"alpha","type":"Real"}],"binder_map":{"delta":{"var":"delta"},"alpha_0":{"var":"p_117_p_115_2_alpha_0"},"alpha":{"var":"alpha"}},"hypothesis_map":{},"witness_map":{},"consume":["result"]}],"witness_realizations":{"C_delta":{"def":{"id":"W-P-117-C_delta","args":[{"var":"delta"},{"var":"p_117_p_113_1_y_delta"},{"var":"p_117_p_115_2_C_grid"},{"var":"p_117_p_115_2_Xi_0"},{"var":"p_117_p_115_2_C_P4"},{"var":"p_117_p_115_2_C_den"},{"var":"p_117_p_115_2_alpha_0"},{"var":"p_117_p_115_2_C_small"}]}}},"proof_ref":"### P-117 \u2014 Theorem 1, interior, with uniform constant order"}
```

- Prenex statement:
  \[
  \forall\delta\in(0,1)\;\exists C_\delta>0\;
  \forall\alpha\in(0,1],\quad
  \bar d(E_\alpha)\le C_\delta\alpha^{1-\delta}.
  \]
- Local equalities:
  choose \(y\) from P-113; choose the P-115
  \(C_{\rm grid},\Xi_0,C_{\rm P4},C_{\rm den},\alpha_0,C_{\rm small}\) in
  that order; set
  \(C_\delta=\max(C_{\rm small},\alpha_0^{-(1-\delta)})\).
- Domain/range: \(C_\delta\) is chosen before every alpha and is uniform in it.
- Input subject: exact E-event. Output: source-faithful interior theorem.
- Premise maps:
  - P-113 — Binders: \(\delta:=\delta\). Hypotheses: \(0<\delta<1\).
    Consumed: select y with both exact inequalities.
    Subject: exact admissibility/exponent data. Constants: y may depend on delta.
  - P-115 — Binders:
    \(\delta:=\delta,y:=\) selected P-113 witness,
    \(a_{\rm bal}:=-0.6\log y,b_{\rm bal}:=0.009\).
    Hypotheses: both P-113 inequalities.
    Consumed: select the pre-alpha P4/denominator coefficient, threshold, and
    small-alpha constants; obtain small-range
    event bound. Subject: exact \(E_\alpha\). Constants:
    \(C_{\rm small}\) depends on delta through y and the earlier fixed
    \(C_{\rm P4}(2,y,1/10)\), never on alpha or its chosen xi.
  - P-116 — Binders:
    \(\delta:=\delta,\alpha_0:=\) selected P-115 witness,
    \(\alpha:=\alpha\).
    Hypotheses: complementary \(\alpha_0\le\alpha\le1\).
    Consumed: compact-range bound. Subject: exact \(E_\alpha\).
    Constants: \(\alpha_0^{-(1-\delta)}\) enters the single \(C_\delta\).
- Derivation certificate: use P-115 for \(\alpha<\alpha_0\) and P-116 for
  \(\alpha\ge\alpha_0\); the displayed maximum works uniformly.
- Source/S2 anchor: ET Theorem 1, statement p. 19 and proof p. 32; S2 R1 T1.
- Definitions used: D-006, D-022.

### P-118 — zero-alpha endpoint

```mathminer-s3
{"schema":"mathminer.s3/1","id":"P-118","kind":"PROPOSITION","binders":[{"key":"n","type":"Nat"}],"uses_definitions":["D-001","D-004","D-006","D-022","S-P-118"],"source_anchors":[{"path":"stage3/canonical/CURRENT.md","git":"4279cd5e01f75401a9f5fa12d42961fe46b9ac8b","anchor":"### P-118 — zero-alpha endpoint"}],"hypotheses":[],"witnesses":[],"conclusions":[{"key":"result","proposition":{"def":{"id":"S-P-118","args":[{"var":"n"}]}}}],"premises":[],"witness_realizations":{},"proof_ref":"### P-118 — zero-alpha endpoint","root_role":"CROSS_CHECK"}
```

- Prenex statement: for every \(n>0\), \(\tau^+(n)\ge1\), hence
  \(E_0=\varnothing\) and \(\bar d(E_0)=0\).
- Local equalities: \(1\mid n\) lies in \([1,2)\).
- Domain/range: exact endpoint.
- Input subject: E0. Output: empty set and density zero.
- Premise maps: none (root).
- Derivation certificate: the divisor 1 occupies the \(k=0\) bin.
- Source/S2 anchor: ET Theorem 1 endpoint; S2 R1 §7.
- Definitions used: D-001, D-004, D-006, D-022.

### P-119 — large-loss endpoint

```mathminer-s3
{"schema":"mathminer.s3/1","id":"P-119","kind":"PROPOSITION","binders":[{"key":"delta","type":"Real"},{"key":"alpha","type":"Real"}],"uses_definitions":["D-006","D-022","S-P-119"],"source_anchors":[{"path":"stage3/canonical/CURRENT.md","git":"4279cd5e01f75401a9f5fa12d42961fe46b9ac8b","anchor":"### P-119 — large-loss endpoint"}],"hypotheses":[],"witnesses":[],"conclusions":[{"key":"result","proposition":{"def":{"id":"S-P-119","args":[{"var":"delta"},{"var":"alpha"}]}}}],"premises":[],"witness_realizations":{},"proof_ref":"### P-119 — large-loss endpoint","root_role":"CROSS_CHECK"}
```

- Prenex statement: for every \(\delta\ge1\) and
  \(\alpha\in(0,1]\),
  \[
  \bar d(E_\alpha)\le1\le\alpha^{1-\delta}.
  \]
- Local equalities: none.
- Domain/range: no expression \(0^{1-\delta}\) is formed.
- Input subject: E-event. Output: endpoint theorem with constant 1.
- Premise maps: none (root).
- Source/S2 anchor: ET Theorem 1 endpoint; S2 R1 §7.
- Definitions used: D-006, D-022.

P-117, P-118, and P-119 together state ET Theorem 1 on every
\(\delta>0,\alpha\in[0,1]\), with the source-faithful uniform constant order
on the nontrivial interior.

### P-120 — strict event is not density one

Current construction binding: the exact `P120Statement` in the GroupA--GroupD source contracts, W0--W8, and the retained S7 provider. Any `mathminer-s3-legacy` block here is historical, not a proof.

```mathminer-s3-legacy
{"schema":"mathminer.s3/1","id":"P-120","kind":"PROPOSITION","binders":[],"uses_definitions":["D-001","D-004","D-006","D-022","S-P-120","W-P-120-alpha"],"source_anchors":[{"path":"stage3/canonical/CURRENT.md","git":"4279cd5e01f75401a9f5fa12d42961fe46b9ac8b","anchor":"### P-120 \u2014 strict event is not density one"}],"hypotheses":[],"witnesses":[{"key":"delta","type":"Real","depends_on":[]},{"key":"C_delta","type":"Real","depends_on":[]},{"key":"alpha","type":"Real","depends_on":[]}],"conclusions":[{"key":"result","proposition":{"def":{"id":"S-P-120","args":[{"var":"delta"},{"var":"C_delta"},{"var":"alpha"}]}}}],"premises":[{"id":"MAP-P120-P117-1","producer":"P-117","closure_role":"REQUIRED","binder_map":{"delta":{"lit":{"type":"Real","value":"1/2"}}},"hypothesis_map":{},"witness_map":{"C_delta":"p_120_p_117_1_C_delta"},"consume":["result"]}],"witness_realizations":{"delta":{"lit":{"type":"Real","value":"1/2"}},"C_delta":{"var":"p_120_p_117_1_C_delta"},"alpha":{"def":{"id":"W-P-120-alpha","args":[{"var":"p_120_p_117_1_C_delta"}]}}},"proof_ref":"### P-120 \u2014 strict event is not density one"}
```

- Prenex statement: there exist
  \[
  \delta\in(0,1),\quad C_\delta>0,\quad
  \alpha\in\bigl(0,\min(1,C_\delta^{-1/(1-\delta)})\bigr)
  \]
  such that
  \[
  \bar d\{n>0:\tau^+(n)<\alpha\tau(n)\}<1.
  \]
- Local equalities: first choose, for example, \(\delta=1/2\); next eliminate
  P-113's \(y\), P-115's pre-alpha coefficient/threshold witnesses, and then
  \(C_\delta\) from P-117; only afterward choose alpha from the displayed
  open interval.
- Domain/range: the interval is nonempty because \(C_\delta>0\).
- Input subject: strict event. Output: strict upper-density bound.
- Premise maps:
  - P-117 — Binders:
    \(\delta:=1/2\); select its \(C_\delta\); after that set
    \(\alpha:=\) any point of the displayed interval.
    Hypotheses: \(0<\delta<1\), \(0<\alpha\le1\).
    Consumed:
    \(\bar d(E_\alpha)\le C_\delta\alpha^{1-\delta}\).
    Subject:
    \(\{n:\tau^+(n)<\alpha\tau(n)\}\subseteq E_\alpha\).
    Constants: the lineage
    \(C_{\rm P4}(2,y,1/10)\to C_{\rm den}\to C_{\rm small}\to C_\delta\)
    is fully selected before alpha; \(C_\delta\) cannot depend on alpha or on
    the alpha-dependent xi used inside P-115.
- Derivation certificate: subset monotonicity of upper density and
  \(C_\delta\alpha^{1-\delta}<1\).
- Source/S2 anchor: PROBLEM.md; ET Theorem 1; S2 R2.9.
- Definitions used: D-001, D-004, D-006, D-022.

### FT-448-NEG-017 — literal negative answer

```mathminer-s3-legacy
{"schema":"mathminer.s3/1","id":"FT-448-NEG-017","kind":"FINAL_TARGET","binders":[],"uses_definitions":["D-001","D-004","D-006","S-FT-448-NEG-017"],"source_anchors":[{"path":"stage3/canonical/CURRENT.md","git":"4279cd5e01f75401a9f5fa12d42961fe46b9ac8b","anchor":"### FT-448-NEG-017 — literal negative answer"}],"hypotheses":[],"witnesses":[{"key":"alpha","type":"Real","depends_on":[]}],"conclusions":[{"key":"result","proposition":{"def":{"id":"S-FT-448-NEG-017","args":[{"var":"alpha"}]}}}],"premises":[{"id":"MAP-FT448NEG017-P120-1","producer":"P-120","closure_role":"REQUIRED","binder_map":{},"hypothesis_map":{},"witness_map":{"delta":"ft_448_neg_017_p_120_1_delta","C_delta":"ft_448_neg_017_p_120_1_C_delta","alpha":"ft_448_neg_017_p_120_1_alpha"},"consume":["result"]}],"witness_realizations":{"alpha":{"var":"ft_448_neg_017_p_120_1_alpha"}},"proof_ref":"### FT-448-NEG-017 — literal negative answer"}
```

- Prenex statement: no binders; the assertion
  \[
  \forall\varepsilon>0,\quad
  \tau^+(n)<\varepsilon\tau(n)\ {\rm for\ almost\ all}\ n
  \]
  is false.
- Local equalities: instantiate its \(\varepsilon\) by the positive alpha
  selected in P-120.
- Domain/range: “almost all” means natural density one.
- Input subject: exact universal question in PROBLEM.md.
  Output subject: its logical negation.
- Premise maps:
  - P-120 — Binders: its selected
    \(\delta,C_\delta,\alpha\) are existentially eliminated.
    Hypotheses: all are in their displayed domains.
    Consumed: strict event has upper density below 1.
    Subject: the universal claim at \(\varepsilon:=\alpha\) would require
    this exact strict event to have density one. Constants: none.
- Derivation certificate: one positive counter-parameter refutes the universal
  almost-all assertion.
- Source/S2 anchor: PROBLEM.md; ET pp. 18–19,32; S2 R2.9.
- Definitions used: D-001, D-004, D-006.

## 12. Normalized typed-slot and dependency-order registry

This registry is a derived mechanical view of the active contracts. It removes
residual typographic compression without becoming a second semantic authority.
The authored records above control on any discrepancy. `fixed -> exists ->
uniform` displays their literal quantifier order. An empty middle column means
that the record has no existential constant or witness.

### 12.1 Definitions and external leaves

| records | fixed typed slots | existential slots | uniform typed slots |
|---|---|---|---|
| D-001 | none | none | \(n\in\mathbb N_{>0}\) |
| D-002 | none | none | \(n\in\mathbb N_{>0},s\in\mathbb R_{\ge2}\) |
| D-003 | none | none | \(n\in\mathbb N_{>0},u\in\mathbb R_{>0}\) |
| D-004 | none | none | \(n\in\mathbb N_{>0},\theta\in\mathbb R_{>1}\) |
| D-005 | none | none | \(d,d'\in\mathbb N_{>0},\theta\in\mathbb R_{>1}\) |
| D-006 | none | none | \(A\subseteq\mathbb N_{>0},t\in\mathbb R_{>0},\theta\in\mathbb R_{\ge2}\) |
| D-007 | \(\varepsilon_{\rm int}\in(0,1/10],\xi>1,\sigma\ge2\) | none | \(n,d\in\mathbb N_{>0},d\mid n,u\in[U_0,n)\) |
| D-008 | \(y\in(0,2),\sigma\ge\theta\ge2,u>\sigma\) | none | \(n\in\mathbb N_{>0}\) |
| D-009 | \(\varepsilon_{\rm int}\in(0,1/10],C_{\rm grid}>0,\Xi_0>1\) | none | \(\xi>\mathrm e,\sigma\ge\theta\ge2,x>U_0,j\in\mathbb N,n,d\in\mathbb N_{>0}\) |
| D-010 | \(\varepsilon_{\rm int}\in(0,1/10],\xi>1,\sigma\ge\theta\ge2\) | none | \(\mathcal A\subseteq\mathbb N_{>0}\) |
| D-011 | \(\varepsilon_{\rm int},\xi,\sigma,\theta,\mathcal A\) as D-010 | none | \(n\in\mathcal A,k\in\mathbb N\) |
| D-012 | \(\varepsilon_{\rm int},\xi,\sigma,\theta\) as D-010 | none | \(n\in\mathbb N_{>0}\) |
| D-013 | \(y\in(0,1),k\in\mathbb N,\sigma\ge\theta\ge2\) | none | \(n\in\mathbb N_{>0}\) |
| D-014 | \(w,a,b:\mathbb N_{>0}\to\mathbb R_{\ge0}\) with stated local conditions | \(c,C>0\) only inside `TauInvType` | \(p\text{ prime},i\in\mathbb N_{\ge1},j\in\mathbb N\) |
| D-015 | none | none | \(\theta\ge2,y\in(0,1),k\in\mathbb N_{\ge1},\sigma\ge\theta\) |
| D-016 | \(\theta,y,k,\sigma\) as D-015 | none | \(z>0,K_{\rm sh}\in\mathbb N_{>0}\) |
| D-017 | \(\sigma\ge\theta\ge2\) | none | \(y\in(0,1),k\in\mathbb N_{\ge1},x>0\) |
| D-018 | \(\theta\ge2,y\in(0,1),k\in\mathbb N_{\ge1},\sigma\ge\theta\) | none | \(x>0\) and displayed integer indices |
| D-019/D-020 | \(\theta\ge2,y\in(0,1),k\in\mathbb N_{\ge1},\sigma\in[\theta,\theta^k]\) | none | \(x>\theta^{2k-1}\) and displayed integer indices |
| D-021a, D-021b, D-021c, D-021d | \(\theta\ge2,y\in(0,1),k\in\mathbb N_{\ge1},\sigma\in(\theta^k,\theta^{k+1})\) | none | \(x>\theta^{2k-1}\) and displayed integer indices |
| D-021e | \(\theta\ge2,y\in(0,1),k\in\mathbb N_{\ge1},\sigma\in(\theta^k,\theta^{k+1})\) | none | displayed \(d,d'\in\mathbb N_{>0}\); no \(x\) slot |
| D-022 | \(\theta\ge2\) | none | \(x>0,\alpha\in[0,1]\) |
| P070-C4 (scoped definition) | selected \(C_{\rm fam}>0\), then \(\theta\ge2\) | none | no free slot; value is \(C_{\rm fam}\theta^2/\sqrt{\log\theta}>0\) |
| EXT-001 | \(h,\lambda_1,\lambda_2\) | \(C_{\rm EXT001}>0\), depending only on \(\lambda_1,\lambda_2\) | \(X\ge2\) |
| EXT-002 | none | \(X_{\rm M}\ge2,c_{{\rm M},-},c_{{\rm M},+}>0\) | \(x\ge2\) in the asymptotic regime; \(B>A\ge X_{\rm M}\) for the interval comparison |

### 12.2 Propositions through Proposition 3

| records | fixed typed slots | existential slots | uniform typed slots |
|---|---|---|---|
| P-001, P-002, P-003, P-004 | displayed nonnegative multiplicative functions/local majorants | only displayed comparison constants | \(K_{\rm sh},d,m,n\in\mathbb N_{>0},X\ge2\) |
| P-001A, P-001B, P-001C, P-001D | displayed \(g,u,v\) or none | none | their displayed \(X,z,x,K_{\rm sh},d\) domains |
| P-005A | \((\lambda_i),\lambda\) | none | \(u,v,p,K_{\rm sh},X\) in the displayed domains |
| P-005 | \((\lambda_i),\lambda\) | shifted-mean comparison constant (depending only on \(\lambda_0,\lambda\)) | \(u,v,K_{\rm sh},X\) in the displayed domains |
| P-006 | \(C,\eta,(r_p)\) | \(P_0\) and product bounds | \(B>P_0\) |
| P-007 | \(c,\eta,C_{\rm err},(L_p)\), with the global displayed error hypothesis | \(P_{\rm err}\ge2,C_-,C_+>0\) | \(A,B\ge2\) |
| P-006A | \(c,P_0,(L_p)\) | none | \(A,B,t\ge2\) in the displayed identities |
| P-008 | \((Q,c_-,c_+,\eta_*,C_{\rm err,*},P_0,m_{\rm fin},M_{\rm fin},c,L)\), with \(1+c_-/2>0\) | \(C_-,C_+>0\) | \(q\in Q,A,B\ge2\) |
| P-010 | none | none | \(\theta\ge2,\sigma\ge\theta,y\in(0,2),u>\sigma,p\text{ prime},\nu\in\mathbb N_{\ge1}\) |
| P-011 | compact \(Y\Subset(0,2)\) | \(C_Y>0\) | \(y\in Y,\theta\ge2,\sigma\ge\theta,\sigma<u\le x,x\ge2\) |
| P-012/P-013 | fixed \(y\in(1,2)\) / \(y\in(0,1)\) | tail constant depending on \(y\) | \(\theta\ge2,\sigma\ge\theta,\sigma<u\le x,n,d\in\mathbb N_{>0}\) |
| P-014/P-015 | none | none | \(\varepsilon_{\rm int}\in(0,1/10]\) |
| P-016 | \(\varepsilon_{\rm int}\in(0,1/10]\) | \(C_{\rm grid}>0\) | \(\xi,\theta,\sigma,x,j,n,d\) exactly as D-009 |
| P-017 | \((\varepsilon_{\rm int},C_{\rm grid})\) | \(\Xi_0>1\) | \(\xi\ge\Xi_0\) |
| P-018 | \(\varepsilon_{\rm int}\) | \(C_{\rm grid},\Xi_0\) | \(\xi\ge\Xi_0,\sigma\ge\theta\ge2,x>U_0\) |
| P-019 | \(\theta\ge2\) | none | \(n\in\mathbb N_{>0}\) |
| P-020 | \(\varepsilon_{\rm int}\) | \(C_{\rm grid},\Xi_0\), then \(\mathcal A\) after \(\xi,\sigma,\theta\) are fixed | \(\xi\ge\Xi_0,\sigma\ge\theta\ge2\) |
| P-030, P-031, P-032 | exact Lemma-4/bin data | none | displayed positive integer divisors and bin indices |
| P-033 | none | none | \(r\in\mathbb N_{\ge1},\nu:\{1,\ldots,r\}\to\mathbb R_{\ge0}\) |
| P-034 | \(\varepsilon_{\rm int},\xi,\sigma,\theta,\mathcal A\) | none | \(n\in\mathcal A\) |
| P-040/P-041 | none | none | all displayed \(n,D,D',t,d,d'\in\mathbb N_{>0}\), \(\sigma\ge\theta\ge2\), \(k\in\mathbb N\) |
| P-042/P-043 | \(\varepsilon_{\rm int},\xi,\sigma,\theta,y\) | none | \(n,m\in\mathbb N_{>0},k\in\mathbb N_{\ge1}\) in the displayed branch |
| P-044 | \(\varepsilon_{\rm int},\xi,\sigma,\theta,y\) | none | \(n>U_0\) |
| P-050 | \(\theta\ge2,y\in(0,1),k\in\mathbb N_{\ge1},\sigma\ge\theta\) | none | \(x>\theta^{2k-1}\) and positive integer indices |
| P-051A | none | absolute base witnesses \((c_0,C_0,\Lambda_0)\) | \(p\text{ prime},i\in\mathbb N_{\ge1},n\in\mathbb N_{>0}\) |
| P-051B | \((a,c_a,C_a,\Lambda_a)\) with displayed type/bound hypotheses | none | admissible \(b,p,j\); denominator bound uniform in the whole \(b\)-family |
| P-051C | \((a,c_a,C_a,\Lambda_a)\) as P-051B | \(c_{\rm sh},C_{\rm sh},\Lambda_{\rm sh}>0\) | admissible \(b,p,i\), all after the witnesses |
| P-051D | typed \(a\) and P-051C output \(s\) | hat-type witnesses depending only on the two typed inputs | admissible \(b,p,i,K\) |
| P-051E | typed \(a_1,a_2\) with common \((c,C,\Lambda)\) | none beyond those common witnesses | \(p,i,K\) |
| P-051V | none | none | \(\theta\in\mathbb R_{\ge2},y\in(0,1),k\in\mathbb N_{\ge1},\sigma\in\mathbb R_{\ge\theta},n\in\mathbb N_{>0},p\text{ prime},j\in\mathbb N\) |
| P-051F1 | none | absolute \(w_1\) witnesses | \(p,i,K\) |
| P-051F2 | P-051F1 witnesses | uniform \(w_{2,k}\) witnesses | \(\theta\ge2,y\in(0,1),k\ge1,\sigma\ge\theta,p,i,K\) |
| P-051F3 | commonized P-051F1/P-051F2 witnesses | uniform \(w_{3,k}\) witnesses | \(\theta,y,k,\sigma,p,i,K\) in the D-015 domain |
| P-051F4 | P-051F3 witnesses | uniform \(w_{4,k}\) witnesses | \(\theta,y,k,\sigma,p,i,K\) in the D-015 domain |
| P-051G | none | \(c_*,C_*,\Lambda_*>0\), finite min/max of P-051A/F1/F2/F3/F4 outputs | \(\theta\in\mathbb R_{\ge2},y\in(0,1),k\in\mathbb N_{\ge1},\sigma\in\mathbb R_{\ge\theta},p\text{ prime},i\in\mathbb N_{\ge1},j\in\mathbb N,K\in\mathbb N_{>0}\) |
| P-051H | fixed P-051G witnesses, then \(\eta_*=\min(c_*,1),C_{E,*}=C_*+2\Lambda_*\) | none | exact five-weight member \(w\) with \(w(1)=1\); \(b:\mathbb N_{>0}\to\mathbb R_{\ge0}\), multiplicative, \(b(1)=1\), \(0\le b(p^j)\le1\) for every prime \(p\), \(j\in\mathbb N\) |
| P-052 | \(\theta\ge2\) | \(C_{\rm sm}(\theta)>0\) | \(y\in(0,1),k\in\mathbb N_{\ge1},\sigma\ge\theta,K_{\rm sh}\in\mathbb N_{>0},z>0\) |
| P-053 | none | absolute \(C_{\rm ps}>0\) | \(M>0\) |
| P-054/P-054A | none | none | typed \(k\in\mathbb N_{\ge1},\theta\ge2,d,d'\in\mathbb N_{>0},\sigma>0,g\ge0\) |
| P-055/P-056/P-058 | \(\theta\ge2\) | their \(\theta\)-constants | \(y\in(0,1),k\in\mathbb N_{\ge1},\sigma\ge\theta,K_{\rm sh}\in\mathbb N_{>0},z\) in the displayed branch |
| P-057 | none | none | \(\theta\ge2,y\in(0,1),k\in\mathbb N_{\ge1},\sigma\ge\theta,K_{\rm sh}\in\mathbb N_{>0},0<z<\sigma\) |
| P-059 | \((Q,(w_q),c_w,C_w^{\rm err},\Lambda_w)\) | one \(C^{\rm mean}>0\) | \(q\in Q,Z\ge2\) |
| P-060, P-061, P-062, P-063, P-064, P-065, P-066, P-067, P-068 | \(\theta\ge2\) where a constant is present | displayed constants | \(y\in(0,1),k\in\mathbb N_{\ge1},\sigma\in[\theta,\theta^k],x>\theta^{2k-1}\) |
| P-069 | none | absolute \(C_{\rm mc}>0\) | \(\theta\ge2,y\in(0,1),k\in\mathbb N_{\ge1},\sigma\ge\theta,x>\theta^{2k-1}\) |
| P-070 | none | \(c_*,C_*,\Lambda_*,C_{\rm fam}>0\), in that order | first \(\theta\ge2\), then define P070-C4, then \(y\in(0,1),k\in\mathbb N_{\ge1},\sigma\ge\theta\), and \(Z\ge2\) only in the family-mean conjunct |
| P-071/P-073 | \(\theta\ge2\) | theta-only constants | regular-domain \(y,k,\sigma,x\) |
| P-072/P-074 | \(\theta\ge2\) | theta-only numerator constants | regular-domain \(y,k,\sigma,x\), with explicit factor \(1/y\) |
| P-075, P-076, P-077, P-078, P-079, P-080, P-081, P-082, P-083 | \(\theta\ge2\) where a constant is present | displayed theta-only constants | \(y\in(0,1),k\in\mathbb N_{\ge1},\sigma\in(\theta^k,\theta^{k+1}),x>\theta^{2k-1}\) |
| P-084 | \(\theta\ge2\) | \(C_{\rm tr,out}(\theta)>0\) | \(y\in(0,1),k\in\mathbb N_{\ge1},\sigma\in\mathbb R\) subject to \(\theta^k<\sigma<\theta^{k+1}\); no \(x\) |
| P-085, P-086, P-087 | \(\theta\ge2\) | displayed theta-only constants | typed transition-domain \(y,k,\sigma,x\) |
| P-088 | none | none | \(\theta\ge2,y\in(0,1),k\in\mathbb N_{\ge1},\sigma\ge\theta,x>0\) |
| P-089 | \(\theta\ge2\) | numerator \(C_3(\theta)>0\) | \(y\in(0,1),k\in\mathbb N_{\ge1},\sigma\ge\theta,x>\theta^{2k-1}\), with explicit factor \(1/y\) |

### 12.3 Proposition 4 and final target

| records | fixed typed slots | existential slots | uniform typed slots |
|---|---|---|---|
| P-090/P-091 | \(\theta\ge2\) where relevant | positive summand witnesses only after the positive-sum hypothesis | typed \(y,k,\sigma,n,x\) from the statements |
| P-092 | \(\varepsilon_{\rm int},\xi,\sigma,\theta,y\) | none | \(x>U_0\), finite \(k\le N_\theta(x)\) |
| P-093, P-094, P-095 | \(\theta\ge2\) | positive comparison constants | \(x>0,k\le N_\theta(x),s\in\{(y-1)/2,-1/2\}\) |
| P-096 | none | none | \(y\in(0,1),\varepsilon_{\rm int}\) in the displayed admissible range |
| P-097 | \(y\in(0,1),a_{\rm pow}\in(0,1-y),K_0\in\mathbb N_{\ge1}\) | none | none; the infinite \(k\)-sum is part of the conclusion |
| P-098, P-099, P-100, P-101 | fixed \((y,a_{\rm pow},K_0,\theta,\sigma)\) as displayed | domination constants | \(N\to\infty\) or \(x\to\infty\) |
| P-102 | \(\theta\ge2,y\in(0,1),\varepsilon_{\rm int}\in(0,1/10]\), admissible | \(C_{\rm P4}(\theta,y,\varepsilon_{\rm int})>0\) before \((\sigma,\xi)\) | \(\sigma\ge\theta,\xi>1\), then \(\exists r_{\theta,y,\varepsilon_{\rm int},\sigma,\xi}=o(x)\), then \(x\to\infty\) |
| P-110/P-111 | fixed Lemma-4 data where displayed | none | \(n\in\mathbb N_{>0},\alpha\in(0,2/5]\) |
| P-112 | \((\varepsilon_{\rm int},y)\) admissible | \(C_{\rm grid},\Xi_0,C_{\rm P4}(2,y,\varepsilon_{\rm int}),C_{\rm den}\), in that order | \(\xi\ge\Xi_0,\alpha\in(0,2/5]\); P4 remainder only pointwise in fixed \(\xi\) before density limsup |
| P-113 | \(\delta\in(0,1)\) | \(y=y_\delta\in(0,1)\) | none |
| P-114 | \((y,a_{\rm bal},b_{\rm bal})\) | none | \(\alpha\in(0,1),\log\xi=\alpha^{-1/(a_{\rm bal}+b_{\rm bal})}\) |
| P-115 | \(\delta\in(0,1),y\in(0,1)\) satisfying P-113 | \(C_{\rm grid},\Xi_0,C_{\rm P4},C_{\rm den},\alpha_0,C_{\rm small}\), all before alpha | \(\alpha\in(0,\alpha_0)\), with \(\xi=\exp(\alpha^{-1/(a_{\rm bal}+b_{\rm bal})})\) only afterward |
| P-116 | \(\delta\in(0,1),\alpha_0\in(0,1]\) | none | \(\alpha\in[\alpha_0,1]\) |
| P-117 | \(\delta\in(0,1)\) | \(C_\delta>0\) | \(\alpha\in(0,1]\) |
| P-118/P-119 | none | none | endpoint domains displayed in each statement |
| P-120 | choose \(\delta\in(0,1)\) | then \(C_\delta>0\), then \(\alpha\in(0,\min(1,C_\delta^{-1/(1-\delta)}))\) | none |
| FT-448-NEG-017 | none | the witnesses supplied by P-120 | no free variables |

## 13. Exact external-consumer equality and active registries

### 13.1 Exact subject IDs

The following IDs name literal formulas, not descriptive equivalence classes.
Every premise consumes the same ID or cites the adapter shown in its map.

| subject ID | literal active subject |
|---|---|
| `SUB-P001-SHIFTED-LOG` | \(\sum_{n<x}u(K_{\rm sh}n)v(n)\log x\) |
| `SUB-IS` | \({\sf IS}(g;X)=\sum_{n<X}g(n)\) |
| `SUB-IS-EMPTY` | `SUB-IS` on \(0<X\le1\), equal to \(0\) |
| `SUB-IS-ONE` | `SUB-IS` on \(1<X<2\), equal to \(g(1)\) |
| `SUB-P002-FIRST-LOG` | \(\sum_{m<x/d,(m,K_{\rm sh})=1}u(m)v(m)\log(x/d)\) |
| `SUB-P002-MEAN` | \(\sum_{m<x/d,(m,K_{\rm sh})=1}u(m)v(m)\) |
| `SUB-P002-EULER-X` | \(\prod_{p<x/d,p\nmid K_{\rm sh}}\sum_{j\ge0}u(p^j)v(p^j)p^{-j}\) |
| `SUB-P002-EULER-x` | \(\prod_{p<x,p\nmid K_{\rm sh}}\sum_{j\ge0}u(p^j)v(p^j)p^{-j}\) |
| `SUB-P003-SECOND-LOG` | \(\sum_{m<x/d,(m,K_{\rm sh})=1}u(m)v(m)\log d\) |
| `SUB-P005-SHIFTED` | \(\sum_{n<X}u(K_{\rm sh}n)v(n)\) |
| `SUB-P005-EULER` | \(\prod_{p<X}\sum_{j\ge0}u(p^j)v(p^j)p^{-j}\) |
| `SUB-P052-RAW` | \(\sum_{m<z}\tau(mK_{\rm sh})^{-1}\) |
| `SUB-P052-EULER` | \(\prod_{p<z}\sum_{j\ge0}a_0(p^j)p^{-j}\) on \(z\ge2\) |
| `SUB-P011-MEAN` | \(\sum_{n<x}F_{y,u}(n)\) |
| `SUB-P011-EULER` | \(\prod_{p<x}\sum_{j\ge0}F_{y,u}(p^j)p^{-j}\) |
| `SUB-P011-AMBIENT` | \(\prod_{2\le p<x}(1-1/p)^{-1}\) |
| `SUB-P011-ROUGH` | \(\prod_{2\le p<\theta}(1-1/p)=\rho_\theta\) |
| `SUB-P011-MOM` | \(\prod_{\sigma\le p<u}(1-1/p)\sum_{j\ge0}F_{y,u}(p^j)p^{-j}\) |
| `SUB-P011-ZERO` | \(\prod_{\theta\le p<\sigma}1\prod_{u\le p<x}1\) |
| `SUB-P051A-BASE` | exact D-015 base weight \(a_0=1/\tau\) |
| `SUB-P051B-DEN` | \(\sum_{j\ge0}a(p^j)b(p^j)p^{-j}\) |
| `SUB-P051C-NUM` | \(\sum_{j\ge0}a(p^{i+j})b(p^j)(1+j\log p)p^{-j}\) |
| `SUB-P051C-SHIFT` | exact quotient \(\mathcal S[a,b]\) and multiplicative extension |
| `SUB-P051D-HAT` | exact \(\widehat{\mathcal S}[a,b]\) prime-power maximum and extension |
| `SUB-P051E-MAX` | exact two-weight prime-power maximum and multiplicative extension |
| `SUB-P051V-MODIFIER` | exact full-domain D-015 modifier \(v_k(n)=y^{\Omega(n,\theta^k)}\chi(n,\sigma)\) |
| `SUB-P051F1-W1` | exact D-015 \(w_1\) |
| `SUB-P051F2-W2` | exact D-015 family \(w_{2,k}\) |
| `SUB-P051F3-W3` | exact D-015 family \(w_{3,k}\) |
| `SUB-P051F4-W4` | exact D-015 family \(w_{4,k}\) |
| `SUB-P051G-FAMILY` | exact five weights \(a_0,w_1,w_{2,k},w_{3,k},w_{4,k}\) with common type witnesses |
| `SUB-P051G-DOM` | the four exact integer dominations in (P051G-dom) |
| `SUB-P051H-EULER` | \(\sum_{j\ge0}w(p^j)b(p^j)p^{-j}\) for an exact consolidated weight |
| `SUB-P059-MEAN` | \(\sum_{r<Z}w_q(r)\) |
| `SUB-P059-EULER` | \(\prod_{p<Z}\sum_{j\ge0}w_q(p^j)p^{-j}\) |
| `SUB-P070-FAMILY-MEAN` | \(\sum_{r<Z}w_{4,k}(r)\) for \(q=(\theta,y,k,\sigma)\) |
| `SUB-P070-WINDOW` | \(\sum_{\theta^{k-1}<r<\theta^{k+2}}w_{4,k}(r)\) with coefficient exactly \(C_4(C_{\rm fam},\theta)\theta^k k^{-1/2}\) |
| `SUB-E-TERM` | D-009's strict two-sided grid samples plus upper-only terminal sample |
| `SUB-L4-BAD-ALL-U` | D-007 all-\(u\) bad-divisor mass |
| `SUB-Q` | D-012's exact close-pair sum \(Q(n)\) |
| `SUB-F` | D-012's normalized mean summand \(f(n)=\chi(n,\theta)Q(n)/\tau(n)\) |
| `SUB-FK` | D-013's exact half-open \(f_k^\#\) |
| `SUB-SK` | D-017's \(S_k(x,y;\sigma,\theta)\) |
| `SUB-T` | \(T_k(z,K_{\rm sh})=\sum_{t<z}v_k(t)w_1(tK_{\rm sh})\) |
| `SUB-REG-INTERVAL` | \(\sum_{\theta^k\le d<\theta^{k+1}}g(d)\) |
| `SUB-TR-INTERVAL` | \(\sum_{\sigma\le d<\theta^{k+1}}g(d)\) |
| `SUB-OUTER-INITIAL` | \(\sum_{d<\theta^{k+1}}g(d)\) |
| `SUB-REG-U` | D-019's exact \(U_k\) |
| `SUB-REG-U-UP` | D-019's restriction \(U_k^{\rm up}\) |
| `SUB-REG-U-MID` | D-019's restriction \(U_k^{\rm mid}\) |
| `SUB-REG-U-TERM` | D-019's restriction \(U_k^{\rm term}\) |
| `SUB-REG-M-UP` | D-020's exact \(M_k^{\rm up}\) |
| `SUB-REG-M-MID` | D-020's exact \(M_k^{\rm mid}\) |
| `SUB-REG-M-TERM` | D-020's exact \(M_k^{\rm term}\) |
| `SUB-A` | D-018's exact \(A_k\) |
| `SUB-B-SHARP` | D-018's exact R3 \(B_k^{\#}\) |
| `SUB-B-ENL` | D-018's distinct enlarged \(B_k^{\rm enl}\) |
| `SUB-C` | D-018's exact \(C_k\) |
| `SUB-RA` | D-018's \(R_k^A\) |
| `SUB-RB` | D-018's \(R_k^B\) |
| `SUB-RC` | D-018's \(R_k^C\) |
| `SUB-TR-V` | D-021a's exact \(V_k\) |
| `SUB-TR-V-HI` | D-021b's restriction \(V_k^{\ge}\) |
| `SUB-TR-V-LO` | D-021b's restriction \(V_k^{<}\) |
| `SUB-TR-HT` | D-021c's \(\widetilde H_k\) |
| `SUB-TR-LT` | D-021c's \(\widetilde L_k\) |
| `SUB-TR-H` | D-021d's \(H_k\) |
| `SUB-TR-L` | D-021d's \(L_k\) |
| `SUB-TR-O` | D-021e outer transition subject, independent of \(x\) |
| `SUB-P2-INFINITE` | P-044's infinite nonnegative majorant |
| `SUB-P2-FINITE` | P-092's support-restricted majorant |
| `SUB-P4-MAIN` | P-097's main power tail |
| `SUB-P4-MOVE-Y` | P-100's weighted moving sum |
| `SUB-P4-MOVE-HALF` | P-101's exponent \(-1/2\) moving sum |
| `SUB-E-ALPHA` | D-022's weak event \(\tau^+\le\alpha\tau\) |
| `SUB-E-STRICT` | P-120's strict event \(\tau^+<\alpha\tau\) |

The regenerated active transformation/adapter registry is `AD-BFIRST`,
`AD-EULER-ENLARGE`, `AD-PRIME-INDEX`,
`AD-FINITE-PREFIX`, `AD-P011-EULER-SPLIT`,
`AD-P055-EULER-SPLIT`, `AD-P056-EULER-SPLIT`, `AD-REG-INIT`,
`AD-P058-EULER-SPLIT`, `AD-P065-MIDDLE-ENLARGE`,
`AD-P077-EULER-SPLIT`, `AD-TR-INIT`, and `AD-P084-EULER-SPLIT`.
Their directions, domains, endpoints, and nonnegativity hypotheses are stated
at the consuming records; none asserts equality between `SUB-B-SHARP` and
`SUB-B-ENL`.

### 13.2 Normalized direct-map semantic fields

This table is the normalized post-slot portion of the direct maps. It does not
replace their row tables; it completes their four required semantic fields.

| map | producer hypotheses discharged by | consumed conclusion | exact subject / adapter | producer constants -> consumer uniform variables |
|---|---|---|---|---|
| P-002 -> EXT-001 | P-002 multiplicativity and local majorant | EXT-001 mean bound | `SUB-P002-MEAN`; P-001D sends `SUB-P002-EULER-X` to `SUB-P002-EULER-x` | \((\lambda_0,\lambda)\to C\to(x,d,K_{\rm sh})\) |
| P-007 -> EXT-002 | large-range branch \(B>A'\ge P_{\rm err}\ge X_{\rm M}\) | `EXT002-interval` | the literal \(\prod_{A'\le p<B}(1-1/p)\); P-006A supplies only the finite/large-range partition | absolute \((X_{\rm M},c_{{\rm M},-},c_{{\rm M},+})\to P_{\rm err}\to(A,B)\) |
| P-011 -> EXT-001 | P-010 and \(\Lambda_Y<2\) | EXT-001 mean bound | `SUB-P011-MEAN`, output `SUB-P011-EULER` | \(Y\to C_{\rm EXT}\to(y,\theta,\sigma,u,x)\) |
| P-011 -> P-007 ambient | \(L_p^{\rm amb}>0\) and \(|L_p^{\rm amb}-(1+1/p)|=1/(p(p-1))\le2p^{-2}\) globally | pointwise product comparison | `SUB-P011-AMBIENT`, ambient component of `AD-P011-EULER-SPLIT` | fixed \((1,1,2,L^{\rm amb})\to C_{\rm amb}\to(A,B)=(2,x)\); absolute result absorbed before \(Y\to(\Lambda_Y,C_Y^{\rm loc})\to C_Y\to(y,\theta,\sigma,u,x)\) |
| P-011 -> P-007 rough | exact \(L_p^{\rm rough}=1-1/p\) | pointwise product comparison | rough component of `AD-P011-EULER-SPLIT` | fixed \((-1,1,1)\to C\to(2,\theta)\) |
| P-011 -> P-007/P-008 moment | displayed \(C_Y^{\rm loc}\) tail estimate | pointwise P-007 and family-uniform P-008 comparisons | moment component of `AD-P011-EULER-SPLIT` | \(Y\to(C_-,C_+)\to(y,\sigma,u)\) |
| P-051C -> P-051B | typed \(a\), admissible \(b\) | positive uniform shift denominator | `SUB-P051B-DEN` in the quotient `SUB-P051C-SHIFT` | \((a,c_a,C_a,\Lambda_a)\to(c_{\rm sh},C_{\rm sh},\Lambda_{\rm sh})\to(b,p,i)\) |
| P-051D -> P-051C | P-051C type/bound plus input type of \(a\) | hat type and two integer dominations | `SUB-P051D-HAT` literally | fixed typed inputs -> hat witnesses -> \((b,p,i,K)\) |
| P-051F1 -> P-051A/P-051C/P-051D | \(b=1\) and base witnesses | exact \(a_0\to w_1\) construction/type/domination | `SUB-P051F1-W1` | absolute witnesses before \((p,i,K)\) |
| P-051F2 -> P-051F1/P-051V/P-051C/P-051D | exact \(v_k\), nonnegative multiplicativity, \(v_k(1)=1\), and the full \(j\in\mathbb N\) prime-power bound | exact \((w_1,v_k)\to w_{2,k}\) construction/type/domination | `SUB-P051F2-W2`, with `SUB-P051V-MODIFIER` supplying every modifier slot | input witnesses -> output witnesses -> whole \((\theta,y,k,\sigma,p,i,j,K)\)-family |
| P-051F3 -> P-051F1/P-051F2/P-051E | commonized typed inputs | exact two-weight maximum/type/two dominations | `SUB-P051F3-W3` | common input witnesses -> output witnesses -> whole family |
| P-051F4 -> P-051F3/P-051V/P-051C/P-051D | exact \(v_k\), nonnegative multiplicativity, \(v_k(1)=1\), and the full \(j\in\mathbb N\) prime-power bound | exact \((w_{3,k},v_k)\to w_{4,k}\) construction/type/domination | `SUB-P051F4-W4`, with `SUB-P051V-MODIFIER` supplying every modifier slot | input witnesses -> output witnesses -> whole family |
| P-051G -> P-051A/P-051V/P-051F1/P-051F2/P-051F3/P-051F4 | five exposed typed weights plus the full-domain modifier producer | common type/local witnesses, normalization, integer dominations, and all three modifier facts | `SUB-P051G-FAMILY`, `SUB-P051G-DOM`, `SUB-P051V-MODIFIER` | finite min/max \((c_*,C_*,\Lambda_*)\) before \((\theta,y,k,\sigma,p,i,j,K)\) |
| P-051H -> P-051G/P-051V | common local type/bounds and \(w(1)=1\); on \(b:=v_k\), all literal modifier hypotheses from P-051V | separate tail and replaced-main-term estimates | `SUB-P051H-EULER` | \((c_*,C_*,\Lambda_*)\to(\eta_*,C_{E,*})\to(w,b,p)\) |
| P-052 -> P-005 | \(0\le a_0\le1\) | shifted-mean bound | `SUB-P052-RAW`, output `SUB-P052-EULER` | \((1,1)\to C\to(K_{\rm sh},z)\) |
| P-052 -> P-007 | \(C_{a_0}=2\) tail estimate | exact local-product comparison | `SUB-P052-EULER` literally | absolute data -> \(C\to z\) |
| P-055 -> P-005/P-051V | P-051F2 exact shift domination, P-051G local bounds, and P-051V multiplicativity/normalization/full prime-power bound | shifted-mean bound | `SUB-T` -> P-005 Euler subject | \((\Lambda_*,1)\to C\to(y,k,\sigma,K_{\rm sh},z)\) |
| P-055 -> P-007/P-008 | P051H-main and three coefficient identities, uniformly for \(q\in Q_{\rm up}\) | three pointwise and three endpoint-indexed family comparisons | `AD-P055-EULER-SPLIT`; \(L\) is exactly (L055-family) | fixed \(Q_{\rm up},L\) (including \(z\)) -> comparison constants -> \(q,A,B\) -> \(C_{\rm up}(\theta)\to(y,k,\sigma,K_{\rm sh},z)\) |
| P-056 -> P-005/P-051V | P-051F2 exact shift domination, P-051G local bounds, and P-051V multiplicativity/normalization/full prime-power bound | shifted-mean bound | `SUB-T` -> P-005 Euler subject | \((\Lambda_*,1)\to C\to(y,k,\sigma,K_{\rm sh},z)\) |
| P-056 -> P-007/P-008 | P051H-main and two coefficient identities, uniformly for \(q\in Q_{\rm mid}\) | two pointwise and endpoint-indexed family comparisons | `AD-P056-EULER-SPLIT`; \(L\) is exactly (L056-family) | fixed \(Q_{\rm mid},L\) (including \(z\)) -> comparison constants -> \(q,A,B\) -> \(C_{\rm mid}(\theta)\to(y,k,\sigma,K_{\rm sh},z)\) |
| P-057 -> P-051V | P-051V normalization and nonnegativity | exact terminal \(t=1\) contribution | `SUB-T` | no constants |
| P-058 -> P-005/P-051V | P-051F4 exact shift domination, P-051G bounds, P-051V multiplicativity/normalization/full prime-power bound, and `AD-REG-INIT` | shifted-mean bound | `SUB-REG-INTERVAL` -> `SUB-OUTER-INITIAL` | \((\Lambda_*,1)\to C\to(y,k,\sigma,d')\) |
| P-058 -> P-007/P-008 | P051H-main and three coefficient identities | three pointwise and family comparisons | `AD-P058-EULER-SPLIT` | common witnesses -> \(C_{\rm out}(\theta)\to(y,k,\sigma,d')\) |
| P-059 -> EXT-001 | common family local bound | mean bound for every \(q\) | `SUB-P059-MEAN`, output `SUB-P059-EULER` | common family witnesses -> \(C^{\rm mean}\to(q,Z)\) |
| P-059 -> P-007/P-008 | \(C_{E,w}=C_w^{\rm err}+2\Lambda_w\) estimate | pointwise and family product comparisons | `SUB-P059-EULER` literally | common family witnesses -> uniform product constant -> \((q,Z)\) |
| P-060 -> P-051V | regular domains \(\theta\ge2\), \(y\in(0,1)\), \(k\in\mathbb N_{\ge1}\), \(\sigma\in[\theta,\theta^k]\) | exact D-015 \(v_k\) identity, nonnegativity, and multiplicativity | `SUB-P051V-MODIFIER` literally in the D-016 factorization | no constants |
| P-075 -> P-051V | transition domains \(\theta\ge2\), \(y\in(0,1)\), \(k\in\mathbb N_{\ge1}\), \(\sigma\in(\theta^k,\theta^{k+1})\), hence \(\sigma\ge\theta\) | exact D-015 \(v_k\) identity, nonnegativity, and multiplicativity | `SUB-P051V-MODIFIER` literally in the D-016 factorization | no constants |
| P-077 -> P-005/P-051V | P-051F2 exact shift domination, P-051G bounds, P-051V multiplicativity/normalization/full prime-power bound, and \(z_m\ge\sigma\ge2\) | shifted-mean bound | `SUB-T` on the high restriction | \((\Lambda_*,1)\to C\to(\theta,y,k,\sigma,x,d,d',m)\) |
| P-077 -> P-007/P-008 | P051H-main and transition coefficients, uniformly for abstract \(q\in Q_{\rm tr,hi}\) | two pointwise and endpoint-indexed family comparisons, followed by \(z:=z_m=x/(mdd')\) | `AD-P077-EULER-SPLIT`; \(L\) is exactly (L077-family) | fixed \(Q_{\rm tr,hi},L\) (including \(z\)) -> comparison constants -> \(q,A,B\) -> substitute \(z_m\) -> \(C_{\rm tr,\ge}(\theta)\to(y,k,\sigma,x)\) |
| P-084 -> P-005/P-051V | P-051F4 exact shift domination, P-051G bounds, P-051V multiplicativity/normalization/full prime-power bound, and `AD-TR-INIT` | shifted-mean bound | `SUB-TR-INTERVAL` -> `SUB-OUTER-INITIAL` | \((\Lambda_*,1)\to C\to(\theta,y,k,\sigma,d')\) |
| P-084 -> P-007/P-008 | P051H-main and transition coefficients | two pointwise and family comparisons | `AD-P084-EULER-SPLIT` | common witnesses -> \(C_{\rm tr,out}(\theta)\to(y,k,\sigma,d')\) |
| P-070 -> P-059 | P-051F4 exact family and P-051G common witnesses | (P070-family-mean) | `SUB-P070-FAMILY-MEAN` literally | \((c_*,C_*,\Lambda_*)\to C_{\rm fam}\to\theta\to C_4(C_{\rm fam},\theta)\to(y,k,\sigma,Z)\) |
| P-071 -> P-070 | P-070 witness selection and regular domain | (P070-window) | `SUB-P070-WINDOW`, identical to P-058's \(d'\)-sum | \(C_4:=C_4(C_{\rm fam},\theta)\to C_{A,\rm asm}(\theta)\to(y,k,\sigma,x)\) |
| P-072 -> P-070 | P-070 witness selection and regular domain | (P070-window) | `SUB-P070-WINDOW`, identical to P-058's \(d'\)-sum | \(C_4:=C_4(C_{\rm fam},\theta)\to C_{B,\rm asm}(\theta)\to(y,k,\sigma,x)\), with \(1/y\) still explicit |
| P-073 -> P-070 | P-070 witness selection and regular domain | (P070-window) | `SUB-P070-WINDOW`, identical to P-058's \(d'\)-sum | \(C_4:=C_4(C_{\rm fam},\theta)\to C_{C,\rm asm}(\theta)\to(y,k,\sigma,x)\) |
| P-085 -> P-070 | P-070 witness selection and transition domain | (P070-window) | `SUB-P070-WINDOW`, identical to P-084's \(d'\)-sum | \(C_4:=C_4(C_{\rm fam},\theta)\to C_{\rm tr,A}(\theta)\to(y,k,\sigma,x)\) |
| P-086 -> P-070 | P-070 witness selection and transition domain | (P070-window) | `SUB-P070-WINDOW`, identical to P-084's \(d'\)-sum | \(C_4:=C_4(C_{\rm fam},\theta)\to C_{\rm tr,C}(\theta)\to(y,k,\sigma,x)\) |
| P-102 -> P-089/P-097/P-100/P-101 | admissibility and exact finite-support decomposition | Proposition-4 main bound plus three remainder components | `SUB-P4-MAIN`, `SUB-P4-MOVE-Y`, `SUB-P4-MOVE-HALF`, and finite initial term | \((\theta,y,\varepsilon_{\rm int})\to C_{\rm P4}\to(\sigma,\xi)\to r_{\theta,y,\varepsilon_{\rm int},\sigma,\xi}\to x\) |
| P-112 -> P-102 | specialize \(\theta=\sigma=2\) after selecting the P4 main coefficient | mean-to-density Markov input | `SUB-F` and `SUB-E-ALPHA` | \((\varepsilon_{\rm int},y)\to C_{\rm P4}(2,y,\varepsilon_{\rm int})\to C_{\rm den}\to(\xi,\alpha)\); the remainder is pointwise in fixed \(\xi\) |
| P-115 -> P-112 | P-113 admissibility and \(\xi=\exp(\alpha^{-1/(a_{\rm bal}+b_{\rm bal})})\ge\Xi_0\) | two-term density bound | `SUB-E-ALPHA` | \((\delta,y)\to(C_{\rm grid},\Xi_0,C_{\rm P4},C_{\rm den},\alpha_0,C_{\rm small})\to\alpha\) |
| P-117 -> P-115 | selected P-113 witness \(y\) | small-alpha bound | `SUB-E-ALPHA` | \(\delta\to y\to(C_{\rm P4},C_{\rm den},C_{\rm small},\alpha_0)\to C_\delta\to\alpha\) |
| P-120 -> P-117 | \(\delta=1/2\) and selected interior theorem constant | strict-event subset bound | `SUB-E-STRICT` -> `SUB-E-ALPHA` | \(\delta\to C_\delta\to\alpha\), with the entire P4 coefficient lineage already absorbed before alpha |

### 13.3 Regenerated constant and family-index lineage

- Endpoint-indexed P-008 families:
  \[
  Q_{\rm up}=(\theta,y,k,\sigma,z),\qquad
  Q_{\rm mid}=(\theta,y,k,\sigma,z),\qquad
  Q_{\rm tr,hi}=(\theta,y,k,\sigma,z).
  \]
  In each case the corresponding displayed \(L_{q,p}\), coefficient map,
  common error, prefix bounds, and endpoints are fixed before the P-008
  comparison constants. The direct constants descend respectively as
  \(C_{\rm up}\to C_{\rm reg}\),
  \(C_{\rm mid}\to C_{\rm reg}\), and
  \(C_{\rm tr,\ge}\to C_{\rm tr}\). The fixed-endpoint controls remain the
  distinct families \(Q_{\rm reg,out}\) at P-058 and
  \(Q_{\rm tr,out}\) at P-084.
- Final-weight constant lineage is exactly
  \[
  C_{\rm fam}
  \to C_4(C_{\rm fam},\theta)
  \to\{C_{A,\rm asm},C_{B,\rm asm},C_{C,\rm asm},
       C_{\rm tr,A},C_{\rm tr,C}\}
  \to\{C_{\rm reg},C_{\rm tr}\}
  \to C_3
  \to C_{\rm P4}
  \to C_{\rm den}
  \to C_{\rm small}
  \to C_\delta.
  \]
  Here \(C_4(C_{\rm fam},\theta)\) is absorbed only after \(\theta\),
  \(C_3(\theta)/y\) is absorbed only after P-102 has fixed \(y\).  More
  precisely the final segment has prenex order
  \[
  (\theta,y,\varepsilon_{\rm int})\to C_{\rm P4}
  \to(\sigma,\xi)\to r_{\theta,y,\varepsilon_{\rm int},\sigma,\xi}\to x,
  \]
  and, after \(\theta=\sigma=2\),
  \[
  (\varepsilon_{\rm int},y)\to C_{\rm P4}\to C_{\rm den}
  \to(\xi,\alpha),\qquad
  \delta\to y\to C_{\rm small}\to C_\delta\to\alpha.
  \]
  Thus the alpha-dependent xi in P-115 is chosen only after the exact P4
  main coefficient; no descendant infers uniformity from a constant's name.
  The independent R3 lineage
  \(B_k^{\#}\to P\text{-}069\to P\text{-}072\to P\text{-}074
   \to P\text{-}089\to P\text{-}102\)
  retains its explicit \(1/y\) throughout.

### 13.4 External consumer equality

- Direct premise-map scan for `EXT-001` gives exactly
  \(\{P\text{-}002,P\text{-}011,P\text{-}059\}\). This is equal as a set
  to `DP-MEAN-017.consumer_nodes`; P-054/P-054A are not consumers.
- Direct premise-map scan for `EXT-002` gives exactly \(\{P\text{-}007\}\).
  This is equal as a set to `DP-MERTENS-017.consumer_nodes`.
- Active definition registry:
  `D-001`--`D-020`, `D-021a`, `D-021b`, `D-021c`, `D-021d`, `D-021e`,
  `D-022`, and the scoped active definition `P070-C4`.
- Active family-index registry: `Q_up`, `Q_mid`, `Q_reg,out`, `Q_tr,hi`,
  `Q_tr,out`, `Q_4`, and the family set internal to P-059; each is defined at
  its consuming statement, and the three variable-endpoint indices contain
  their endpoint as a component.
- Active external/dependency registry: `EXT-001`, `EXT-002`, `DP-MEAN-017`,
  `DP-MERTENS-017`.
- Active proposition registry: `P-001`, `P-001A`, `P-001B`, `P-001C`,
  `P-001D`, `P-002`--`P-007`, `P-005A`, `P-006A`, `P-008`,
  `P-010`--`P-020`, `P-030`--`P-034`,
  `P-040`--`P-044`, `P-050`, `P-051A`--`P-051E`, `P-051V`,
  `P-051F1`--`P-051F4`, `P-051G`, `P-051H`, `P-052`--`P-059`,
  `P-054A`, `P-060`--`P-102`,
  `P-110`--`P-120`, and `FT-448-NEG-017`.

The external frames preserve exact target, parent obligation, required
eventual `KERNEL_CLOSED` closure, S0 entry, and continuation. Their live local
stage/status and current authority paths are recorded in the frames themselves.
They are abstraction boundaries, never construction tasks.

### 13.5 Regenerated proof-DAG edge projection

This is the complete active projection of the authored Premise maps; arrows
point from producer to consumer.  Root propositions have no incoming edges
and are omitted from the left-hand lists.

```text
P-001A -> P-001B, P-001C
P-051F1 -> P-001C
EXT-001 -> P-002, P-011, P-059
P-001B, P-001D -> P-002
P-005A, P-001, P-002, P-003, P-004 -> P-005
P-006, P-006A, EXT-002 -> P-007
P-007, P-006A -> P-008
P-010, P-007, P-008 -> P-011
P-011 -> P-012, P-013
P-012, P-013, P-014, P-015 -> P-016
P-016, P-017 -> P-018
P-018, P-019 -> P-020
P-030, P-031 -> P-032
P-032, P-033 -> P-034
P-040 -> P-041
P-040, P-041, P-042, P-043 -> P-044

P-051B -> P-051C
P-051C -> P-051D
P-051A, P-051C, P-051D -> P-051F1
P-051F1, P-051V, P-051C, P-051D -> P-051F2
P-051F1, P-051F2, P-051E -> P-051F3
P-051F3, P-051V, P-051C, P-051D -> P-051F4
P-051A, P-051V, P-051F1, P-051F2, P-051F3, P-051F4 -> P-051G
P-051G, P-051V -> P-051H

P-005, P-007, P-001C, P-051A, P-051F1 -> P-052
P-005, P-007, P-008, P-051F1, P-051F2, P-051V, P-051G, P-051H -> P-055, P-056
P-051F1, P-051V -> P-057
P-054A, P-005, P-007, P-008, P-051F3, P-051F4, P-051V, P-051G, P-051H, P-054 -> P-058
P-007, P-008 -> P-059
P-050, P-052, P-051F1, P-051V -> P-060
P-055 -> P-062
P-051F3, P-054 -> P-063
P-056 -> P-064
P-051F3, P-054 -> P-065
P-057 -> P-066
P-051F3, P-053, P-054 -> P-067
P-051F4, P-051G, P-059 -> P-070
P-058, P-068, P-070 -> P-071
P-058, P-069, P-070 -> P-072
P-058, P-070 -> P-073
P-060, P-061, P-062, P-063, P-064, P-065, P-066, P-067,
P-071, P-072, P-073 -> P-074

P-050, P-052, P-051F1, P-051V -> P-075
P-005, P-007, P-008, P-051F1, P-051F2, P-051V, P-051G, P-051H -> P-077
P-051F3 -> P-078, P-080
P-057 -> P-079
P-054 -> P-082
P-053, P-054 -> P-083
P-054A, P-005, P-007, P-008, P-051F3, P-051F4, P-051V, P-051G, P-051H, P-054 -> P-084
P-070, P-081, P-082, P-084 -> P-085
P-070, P-081, P-083, P-084 -> P-086
P-075, P-076, P-077, P-078, P-079, P-080, P-085, P-086 -> P-087
P-074, P-087, P-088 -> P-089

P-054 -> P-090
P-044, P-090, P-091 -> P-092
P-091 -> P-093
P-093 -> P-094, P-095
P-094, P-098 -> P-100
P-095, P-099 -> P-101
P-092, P-089, P-096, P-097, P-100, P-101 -> P-102
P-034, P-110 -> P-111
P-020, P-102, P-111, P-110 -> P-112
P-112, P-114 -> P-115
P-113, P-115, P-116 -> P-117
P-117 -> P-120
P-120 -> FT-448-NEG-017
```

Two independent finite-set checks were made against the complete authored
Premise-map relation after deduplication:

```text
set(authored premise-map producer/consumer pairs)
  = set(projected producer/consumer pairs),
set(projected producer/consumer pairs)
  = set(authored premise-map producer/consumer pairs).
```

Writing \(M\) for the authored-map pair set and \(E\) for the expanded
projection pair set, the checks returned
\(|M|=|E|=211\), \(M\setminus E=\varnothing\),
\(E\setminus M=\varnothing\), and no duplicate expanded pair. Thus every
authored pair occurs exactly once in the projection, and every projected pair
has an authored premise map. In
particular, the projection contains `P-051F1 -> P-001C`, contains every real
P-051V consumer edge including `P-051V -> P-060` and `P-051V -> P-075`,
contains neither `P-051F2 -> P-060` nor `P-051F2 -> P-075`, and retains
`P-063/P-065/P-067 -> P-074` and
`P-096/P-097 -> P-102`, and contains none of the false pairs
`P-063 -> P-071`, `P-065 -> P-072`, `P-067 -> P-073`, or
`P-096 -> P-097`.

The projection is acyclic.  In particular there is no node or edge named
`P-051`; its former consumers now point only to the exact construction,
common-witness, integer-domination, or Euler-tail record they use.

### 13.6 Current-SKILL closure roles and stable L1 keys

This subsection is the thin structural view of the already-authored records
and premise maps. It adds no proposition, hypothesis, premise relation,
substitution, constant dependence, or mathematical conclusion.

#### Closure-role declaration

Every active producer occurrence in every authored `Premise maps` field in
Sections 4--11 has

```yaml
closure_role: REQUIRED
```

There are no `CROSS_CHECK` or `DIAGNOSTIC` premise relations in the active
parent authority. Consequently every active definition, external interface,
derivation result, final-target record, and every proposition other than
`P-118` and `P-119` in Sections 2--11 has

```yaml
effective_closure_role: REQUIRED
```

because it is reverse-reachable from `FT-448-NEG-017` through the displayed
authored premise maps or is a definition used on that cone. `P-118` and
`P-119` complete the source theorem's unused endpoint cases, have no outgoing
premise relation, and explicitly have

```yaml
effective_closure_role: CROSS_CHECK
```

They do not block the parent final-target cone. The two Dependency Problem
interfaces separately declare
`closure_role: REQUIRED` in their frames. Thus the required-cone view is the
complete reverse-reachable parent cone represented by Sections 2--11 and the
exact edge projection in Section 13.5, excluding only the two endpoint
cross-check records just named.

#### Stable binder and hypothesis keys

For each theorem-like record with active ID `R`, the following fields are
explicitly defined:

```yaml
binder_keys(R):
  - R.b.<slot>
hypothesis_keys(R):
  - R.h.<ordinal>
witness_keys(R):
  - R.w.<slot>
derived_keys(R):
  - R.d.<slot>
```

For `binder_keys`, `<slot>` is the literal normalized universally quantified
input slot label in `R`'s prenex statement or exact prefix, as exposed in the
fixed and uniform typed-slot cells of Section 12, in quantifier order.  For
`witness_keys`, `<slot>` is the literal normalized existential output slot
label in the intervening existential cell.  This distinction prevents a
producer-selected constant from being mistaken for a consumer-supplied input.
Tuple-valued displayed slots retain their literal tuple label rather than
being silently split. `<ordinal>` is the two-digit, one-based left-to-right
ordinal of an atomic non-binder assumption introduced by `if`, `assuming`, or
`assume` in that same authored prefix; a domain restriction carried by a typed
binder remains part of its binder key. For `derived_keys`, `<slot>` is a
literal name introduced by `put`, `define`, or `Local equalities` and later
addressed by a premise map. Local defining equalities are not hypotheses. For
example, EXT-001 exposes

```yaml
binder_keys:
  - EXT-001.b.h
  - EXT-001.b.lambda_1
  - EXT-001.b.lambda_2
  - EXT-001.b.X
hypothesis_keys:
  - EXT-001.h.01
witness_keys:
  - EXT-001.w.C_EXT001
```

where `EXT-001.h.01` is its complete prime-power geometric-bound assumption.
EXT-002 exposes `EXT-002.b.x`, the witness keys
`EXT-002.w.X_M`, `EXT-002.w.c_M_minus`, `EXT-002.w.c_M_plus`, and the
uniform endpoint keys `EXT-002.b.A`, `EXT-002.b.B`, with no non-domain
hypothesis key. A
premise-map `producer slot` label resolves to the unique key
`<producer>.b.<slot>` when it is a universal input binder and to
`<producer>.d.<slot>` when it is a displayed local definition; its
`Hypotheses` paragraph resolves, in prefix order, to the producer's
`hypothesis_keys`, and its `Constants` paragraph resolves selected producer
outputs through `<producer>.w.<slot>`. The complete typed-slot registry in Section 12, each
record's `Local equalities`, and the literal producer-slot row tables are the
mechanical enumeration of these fields. A missing, duplicated, or
non-resolving key is an L1 failure. The authored prenex statement and
premise-map substitution remain the sole mathematical authority; these
qualified keys only stabilize their typed structural identity.

## 14. Current-authority recovery and integrity anchors

The mathematical content in Sections 1--13.5 is the R19 recovery payload. The
current-authority migration changed only status, live Dependency Problem
continuation metadata, and the classification of registries/projections as
derived views. The later current-SKILL preflight repair added only the
explicit role/key structural view in Section 13.6 and the two matching
Dependency Problem `closure_role` fields; it changed no authored mathematical
statement or premise relation. It does not seal a legacy revision or accept
its own semantics. A different fresh auditor must accept the repaired
structural surface, and a fresh exhaustive whole-cone audit remains mandatory
after transitive dependency closure.

The subsequent A2 cone audit found that the parent `EXT-002` relative-error
contract was stronger than the active DP-MERTENS provider.  Its discovering
auditor replaced that unused rate by the exact minimum sufficient
`FT-MERTENS` asymptotic plus `P-MERT-08` interval comparison, updated only the
single P-007 consumption wording, and completed the two parent Dependency
Problem frames.  The edge `EXT-002 -> P-007`, P-007's statement/constants,
all descendant premise maps, and the final target are unchanged.  This is a
semantic interface repair and remains uncertified pending a different fresh
cone auditor.

The 2026-09-17 P-005 repair preserves the accepted family-uniform P-005
statement and introduces the separately bounded geometric/common-prime
summability adapter under the fresh stable identity `P-005A`. Historical
`P-001E` continues to denote the shifted mean theorem in frozen revisions and
is not reinterpreted. The focused S2B review accepted the exact E4--E4a input;
this S3 repair remains uncertified pending a different fresh S3 auditor.

### Immutable upstream and recovery-evidence hashes

- `PROBLEM.md`:
  `2abd3765b19f85a92e67187fa6103a64dbc99fbf7186fdc5221f195e454634c8`
- `erdos448_required_paper_pages.md`:
  `09c7bfc2d25c118b52dbc25df2ecee2284b76f0cb7741784645936cbcc054805`
- `Erdos448/stage1/S1_UNDERSTANDING.md`:
  `dbd25e171f9c820820dec23e6d663fd29caee1705b50516bdfa6394a1ff9e493`
- `Erdos448/stage2/reconstruction/S2_RECONSTRUCTION_R1.md`:
  `f602a88b14bae3aacdbbcf85b0edd885e5aa3adbbbb68d6b390c5f30f9b9b976`
- `Erdos448/stage2/reconstruction/S2_RECONSTRUCTION_R2.md`:
  `74d3436cce747a7d9444ba540bec785ea53b727e109bb4039d3030ba0b0742f0`
- `Erdos448/stage2/reconstruction/S2_RECONSTRUCTION_R3.md`:
  `cc1a5666a439fd19acb798e7b37d6cd938eb336bb65b91d049bded422a1697d3`
- `Erdos448/stage2/breaker/S2B_P005_E4A_2026-09-17.md`:
  `ddd50b23b4921cb276892b26951f561b18d29e98628d5f8467375d36dbad1663`
- `Erdos448/stage2/breaker/S2B_REPORT_R1.md`:
  `0870d4ca172dab0181b455a604bdb6333fdccbd22591697ab7ea4c3b08c53d05`
- `Erdos448/stage2/breaker/S2B_REPORT_R2.md`:
  `4e42c1fe601122429b3674a75da1bc998b4576b6dd182dbbcf00f51082930545`
- `Erdos448/stage2/breaker/S2B_REPORT_R3.md`:
  `2b3d0b7d19127d1715f4692a265d09987f08898753d31752d865a5955f0bed96`
- Rejected predecessor and repair evidence: the real paths/hashes in Section
  0 and both Dependency Problem frames.
