# Sparse random-graph evolution: mathematical statement

## Scope and model

The principal result is the five-branch **sparse evolution atlas**. It is not a theorem simultaneous in every edge count, does
not cover every sequence with M/n tending to zero or infinity, and is not a
complete dense-regime classification of the original open-ended historical question.

For n vertices, let N=binom(n,2), and let G(n,M) be uniform on the labelled simple
graphs with exactly M edges. All finite-n assertions include 0<=M<=N. Asymptotic
assumptions need hold **eventually**, not at n=0 or n=1. L_i is the i-th largest
component order, counting multiplicity; it is zero when fewer than i components
exist. Indices i start at one. A tree component on one vertex counts as a tree.
A unicyclic component has equally many edges and vertices; positive excess r
means edges=vertices+r, r>=1.

Put

    lambda_n = 2 M_n / n,
    a(x) = x - 1 - log x       (x>0),
    b_n = [log n - (5/2) log log n] / a(lambda_n).

When lambda_n -> lambda in (0,infinity)\{1}, define

    nu_lambda(ell) = a(lambda)^(5/2) exp[-a(lambda) ell]
                    / [lambda sqrt(2 pi) (1-exp[-a(lambda)])].

When lambda_n=1 +/- epsilon_n, epsilon_n>0, epsilon_n->0 and
w_n=n epsilon_n^3->infinity, put

    z_n=w_n/8,
    H_n(r)=[log z_n-(5/2)log log z_n+r]/a(lambda_n),
    mu(r)=2 exp(-r)/sqrt(pi).

These expressions are used only on their eventual positive domains. A concrete
formal definition may totalize them arbitrarily outside those domains, provided
it proves the eventual-domain and tail-invariance lemmas.

## FINAL-01 — fixed subcritical

For lambda_n->lambda with 0<lambda<1, L_2-b_n=O_p(1). On every deterministic
subsequence n_j->infinity with integer thresholds h_j satisfying
h_j-b_(n_j)->ell,

    P(L_2(G(n_j,M_(n_j))) < h_j)
      -> exp[-nu_lambda(ell)] (1+nu_lambda(ell)).

The centre uses **lambda_(n_j)**, not just its limit. A subsequence is essential
for a lattice law, not an optional presentational convention.

## FINAL-02 — fixed supercritical

For lambda_n->lambda>1, L_2-b_n=O_p(1), and under the same integer-threshold
condition the limit is exp[-nu_lambda(ell)]. Let x(lambda_n) be the unique
solution in (0,1) of x exp(-x)=lambda_n exp(-lambda_n). Then

    L_1 = n [1-x(lambda_n)/lambda_n] + O_p(sqrt(n)).

With probability tending to one there is exactly one component of order at
least ceil(n^(2/3)); all the others are trees or unicyclic. In particular rank 1
is linear and separated from rank 2. This is a pointwise sequence theorem, not
a claim about the entire graph process at once.

## FINAL-03 — barely subcritical, exact rate

For lambda_n=1-epsilon_n with epsilon_n->0 and n epsilon_n^3->infinity,

    P(L_2 < H_n(r)) -> exp[-mu(r)] (1+mu(r))       for every fixed real r.

With high probability there is no positive-excess component. The real threshold
is legitimate because a(lambda_n)->0, so integer rounding has vanishing effect
on the normalized threshold.

## FINAL-04 — barely supercritical, exact rate and giant centre

For lambda_n=1+epsilon_n with the same two limiting assumptions,

    P(L_2 < H_n(r)) -> exp[-mu(r)].

Let s_n=n epsilon_n/2 and s'_n=n[1-x(lambda_n)]/2. Then 0<s'_n<n/2 eventually,

    (1-2s'_n/n) exp(2s'_n/n)=(1+2s_n/n) exp(-2s_n/n),
    L_1 = 2(s_n+s'_n)n/(n+2s_n) + O_p(n/sqrt(s_n)),
    L_1 = 4s_n + O(s_n^2/n) + O_p(n/sqrt(s_n)).

The deterministic O term means: one absolute constant bounds the centre error
for all sufficiently small positive epsilon. The O_p term implies the displayed
window with **every** positive divergent omega_n, without making omega a hidden
constant or exchanging its quantifier with n. With high probability there is
exactly one component of order at least ceil(n^(2/3)), and all others are trees
or unicyclic.

## FINAL-05 — critical fixed-edge law

For every fixed real lambda and admissible edge sequence satisfying

    (2M_n-n)/n^(2/3) -> lambda,

we have, jointly for each fixed number of ranks,

    n^(-2/3)(L_1,L_2,...,L_k) => (xi_1(lambda),...,xi_k(lambda)).

Here xi_i are the decreasing excursion lengths of the reflection above its past
minimum of B(t)+lambda t-t^2/2, where B is standard Brownian motion starting at
zero. The Brownian law is explicitly characterized and its existence is a
required foundation theorem, not an opaque probability model. For the public
rank-two CDF statement, convergence is claimed at continuity points of its CDF;
no Janson–Spencer no-atom or all-moment theorem is silently assumed.

In particular xi_2 is finite and strictly positive almost surely, so the rank-two
critical order is n^(2/3) in probability. This immediately rules out any assertion
that rank two remains sub-polynomial throughout the sparse evolution.

## FINAL-TARGET — conjunction

The conjunction of FINAL-01 through FINAL-05, with the exact-rate correction in
FINAL-03 and FINAL-04. This is a semantic correction of a false over-generalized
normalization, not an unchanged statement with a new proof. The original
quadratic normalization requires the additional condition
epsilon_n log(n epsilon_n^3)->0; see [NORMALIZATION.md](NORMALIZATION.md).
That restricted corollary is discussed there and is not a separate Palomar claim.


## Formal statement

The exact definitions and quantifiers are in the root `Challenge.lean`.
`Solution.lean` proves `Erdos745.Palomar.sparseEvolution` directly from
`Erdos745.WrapUp.atlas` in `Erdos745/WrapUp/Assembly.lean`.
The source relationships and scope differences are recorded in
`formalization.yaml` and `stage8/CLAIM_LEDGER.md`.
