# Near-critical quadratic normalization

**Statement.** Write L_n(r)=log(w_n/8)-(5/2)log log(w_n/8)+r and

    H_quad(r)=2 L_n(r)/epsilon_n^2.

The original quadratic-threshold law follows from the exact-rate law if

    epsilon_n log w_n -> 0.                                    (R03.1)

More generally, if epsilon_n log w_n->theta in [0,infinity), its limiting law
is the exact-rate law with r replaced by r+2theta/3 on the subcritical side,
and by r-2theta/3 on the supercritical side. Under the original hypotheses
alone, a universal unshifted quadratic law is false.

**Proof.** Its effective exact-rate parameter is

    r_eff=r+[a(1 +/- epsilon)/(epsilon^2/2)-1] L_n(r).

The Taylor expansion of the exact rate gives r_eff-r=+2epsilon log w/3+o(1) on the subcritical side and its negative
on the supercritical side when epsilon log w has a finite limit. Squeeze between
fixed r values in the exact-rate law; continuity of `exp[-mu(r)]` and `exp[-mu(r)](1+mu(r))` gives
the shifted law and (R03.1).

For a decisive counterexample choose admissible M_n by rounding
n(1 +/- (log n)^(-1/2))/2. Then epsilon_n~(log n)^(-1/2),
w_n~n/(log n)^(3/2)->infinity, but epsilon_n log w_n->infinity. The effective
parameter tends to +infinity below criticality and -infinity above it. For
any fixed R, compare H_quad(r) with H_n(R), respectively H_n(-R), and use R02.
Then let R->infinity. It follows that

    subcritical:   P(L_2<H_quad(r))->1,
    supercritical: P(L_2<H_quad(r))->0,

rather than the printed nondegenerate functions at the unshifted r.

**Independent local check of the counterexample.** This failure does not require
accepting the giant proof or the complete critical-limit reconstruction. For
these particular sequences h=H_quad(r)=O((log n)^2), so the finite component-count and factorial-moment estimates apply with
errors O((log n)^4/n), uniformly on a sufficiently large multiple of h. They give

    E T_h = exp[-(2/3)sqrt(log n)+O(log log n)]   below criticality,
    E T_h = exp[+(2/3)sqrt(log n)+O(log log n)]   above criticality.

The exact second tuple formula gives E(T_h)_2/(E T_h)^2 -> 1 above criticality;
tails outside that multiple of h are exponentially smaller by the tail estimates. Hence
T_h>=2 with probability tending to one above criticality, already implying
L_2>=h even without a unique-giant theorem. Below criticality, Markov gives no
tree above h, the unicyclic-component bound gives no unicyclic component above h, and the elementary
bicyclic embedding bound excludes all complex components. Thus L_2<h with
probability tending to one. This direct first/second-moment check establishes
the normalization defect independently of the more ambitious proof route.

**Source discrepancy.** The supplied image of Łuczak (1990), printed p.294,
Theorem 3 (2.8) and (2.10), displays the quadratic threshold under only
s n^(-2/3)->infinity and s=o(n). This is not merely an OCR loss in the supplied
text: the same formula and hypotheses are visible in the page image. The
current reconstruction does not promote that formula at full generality.
It retains the full parameter regime with the exact rate and preserves the
printed formula as the explicitly restricted corollary (R03.1). The derivation
above, rather than a claim of bibliographic authority, is the reason for the
semantic correction. No source file has been silently edited.
