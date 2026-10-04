module

import all Mathlib.Basic.Real.Basic
public import Mathlib

public section

set_option backward.isDefEq.respectTransparency false

/-!
Lean-facing representation design for `DP-MERTENS-017` and its closed child
`DP-MERTENS-SUM-CONSTANT`.

This file contains definitions, proposition-valued contracts, and witness-carrying
interfaces only.  Mathematical authority remains the frozen S3 authority identified
in `stage4/authority.md`.
-/

open Filter Finset Set
open scoped BigOperators Topology

namespace Erdos448.DPMertens

noncomputable section

/-! ## Exact finite-cutoff objects -/

/-- Rational primes `p` satisfying `p ≤ x`. -/
@[expose] def primesLE (x : ℝ) : Finset ℕ :=
  (Finset.range (Nat.floor x + 1)).filter Nat.Prime

/-- Rational primes `p` satisfying `p < x`. -/
@[expose] def primesLT (x : ℝ) : Finset ℕ :=
  (Finset.range (Nat.ceil x)).filter Nat.Prime

/-- Rational primes in the real half-open interval `[A,B)`. -/
@[expose] def primesIco (A B : ℝ) : Finset ℕ :=
  (Finset.range (Nat.ceil B)).filter (fun p ↦ p.Prime ∧ A ≤ (p : ℝ))

/-- The Mertens Euler factor at a natural index. -/
@[expose] def primeFactor (p : ℕ) : ℝ := 1 - ((p : ℝ)⁻¹)

/-- `Q_≤(x)` from D-MERT-01. -/
@[expose] def qLE (x : ℝ) : ℝ := ∏ p ∈ primesLE x, primeFactor p

/-- `Q_<(x)` from D-MERT-01. -/
@[expose] def qLT (x : ℝ) : ℝ := ∏ p ∈ primesLT x, primeFactor p

/-- The literal endpoint product `b(x) = ∏_{p=x} (1-1/p)`. -/
@[expose] def endpointFactor (x : ℝ) : ℝ :=
  ∏ p ∈ (primesLE x).filter (fun p : ℕ ↦ (p : ℝ) = x), primeFactor p

/-- The exact interval product consumed by the parent P-007. -/
@[expose] def intervalProduct (A B : ℝ) : ℝ :=
  ∏ p ∈ primesIco A B, primeFactor p

/-! ## Correction and child-provider objects -/

/-- `a_p` from D-MERT-02. -/
@[expose] def correction (p : ℕ) : ℝ :=
  -Real.log (1 - (p : ℝ)⁻¹) - (p : ℝ)⁻¹

/-- Prime-indexed correction sequence, zero off the rational primes. -/
@[expose] def correctionSeq (p : ℕ) : ℝ := if p.Prime then correction p else 0

/-- `H_≤(x)` from D-MERT-02. -/
@[expose] def correctionLE (x : ℝ) : ℝ := ∑ p ∈ primesLE x, correction p

/-- The nonnegative power-series tail used in P-MERT-01. -/
@[expose] def correctionPowerSeries (p : ℕ) : ℝ :=
  ∑' k : ℕ, if 2 ≤ k then 1 / ((k : ℝ) * (p : ℝ) ^ k) else 0

/-! ## Prime-zeta representation bridge

These declarations expose the construction-critical real form of the complex
Euler-product provider used in P-MSC-03A/B.  They assert no theorem: later
construction must supply every field of the witness packages below. -/

/-- The one-sided filter `ρ ↓ 0`, preserving the strict positivity domain. -/
@[expose] def rhoDownZero : Filter ℝ := nhdsWithin 0 (Set.Ioi 0)

/-- The guarded real Dirichlet-series representation of `ζ(1+ρ)`. -/
@[expose] def zetaOnePlus (rho : ℝ) : ℝ :=
  ∑' n : ℕ, if 1 ≤ n then Real.rpow n (-(1 + rho)) else 0

/-- The guarded real prime Dirichlet series in P-MSC-03B. -/
@[expose] def primeZetaOnePlus (rho : ℝ) : ℝ :=
  ∑' p : ℕ, if p.Prime then Real.rpow p (-(1 + rho)) else 0

/-- The rho-dependent correction term, zero off the rational primes. -/
@[expose] def primeZetaCorrection (rho : ℝ) (p : ℕ) : ℝ :=
  if p.Prime then
    -Real.log (1 - (p : ℝ).rpow (-(1 + rho))) -
      (p : ℝ).rpow (-(1 + rho))
  else 0

/-- Exact positive-rho Euler/log data.  Both absolute-convergence witnesses
are packaged with the rearranged identity, so downstream construction cannot
consume the identity while silently omitting its convergence obligations. -/
structure PrimeZetaEulerIdentityAt (rho : ℝ) where
  rho_pos : 0 < rho
  zeta_positive : 0 < zetaOnePlus rho
  prime_norm_summable : Summable (fun p : ℕ ↦
    ‖if p.Prime then Real.rpow p (-(1 + rho)) else 0‖)
  correction_norm_summable : Summable (fun p : ℕ ↦
    ‖primeZetaCorrection rho p‖)
  euler_log_identity :
    Real.log (zetaOnePlus rho) =
      primeZetaOnePlus rho + ∑' p : ℕ, primeZetaCorrection rho p

/-- P-MSC-03B's analytic bridge for the same correction limit `H` supplied by
P-MERT-02.  Pointwise convergence and domination are explicit; the final
`tsum` limit is retained as the exact dominated-convergence output. -/
structure PrimeZetaAnalyticBridge (H : ℝ) where
  at_positive : ∀ rho : ℝ, 0 < rho → PrimeZetaEulerIdentityAt rho
  correction_pointwise : ∀ p : ℕ,
    Tendsto (fun rho : ℝ ↦ primeZetaCorrection rho p)
      rhoDownZero (nhds (correctionSeq p))
  correction_dominated : ∀ rho : ℝ, 0 < rho → ∀ p : ℕ,
    ‖primeZetaCorrection rho p‖ ≤ ‖correctionSeq p‖
  correction_tsum_tendsto :
    Tendsto (fun rho : ℝ ↦ ∑' p : ℕ, primeZetaCorrection rho p)
      rhoDownZero (nhds H)

/-- `ϑ(t)` from D-MSC-01. -/
@[expose] def theta (t : ℝ) : ℝ := ∑ p ∈ primesLE t, Real.log p

/-- `A(t)` from D-MSC-01. -/
@[expose] def weightedPrimeSum (t : ℝ) : ℝ :=
  ∑ p ∈ primesLE t, Real.log p / p

/-- `f_ρ(t)` from D-MSC-01. -/
@[expose] def tailKernel (rho t : ℝ) : ℝ := t ^ (-rho) / Real.log t

/-- A finite encoding of `V(n)=∑_{p^k≤n,k≥1} log(p)/p^k` from D-MSC-01.
The bounds `p ≤ n` and `k ≤ n` contain every active pair when `n ≥ 2`. -/
@[expose] def primePowerSum (n : ℕ) : ℝ :=
  ∑ p ∈ Finset.range (n + 1),
    if p.Prime then
      ∑ k ∈ Finset.range (n + 1),
        if 1 ≤ k ∧ p ^ k ≤ n then Real.log p / (p : ℝ) ^ k else 0
    else 0

/-- Reciprocal-prime sum at a real cutoff. -/
@[expose] def reciprocalPrimeSum (x : ℝ) : ℝ := ∑ p ∈ primesLE x, (p : ℝ)⁻¹

/-- Reciprocal-prime sum at an integer cutoff. -/
@[expose] def reciprocalPrimeSumNat (G : ℕ) : ℝ :=
  ∑ p ∈ (Finset.range (G + 1)).filter Nat.Prime, (p : ℝ)⁻¹

/-- The positive-domain rate predicate used for every `O(1/log x)` output. -/
@[expose] def ReciprocalLogRate (R : ℝ → ℝ) (C X : ℝ) : Prop :=
  0 < C ∧ 2 ≤ X ∧ ∀ x : ℝ, X ≤ x → |R x| ≤ C / Real.log x

/-- Asymptotic equivalence at positive real infinity. -/
@[expose] def AtTopEquivalent (f g : ℝ → ℝ) : Prop :=
  Asymptotics.IsEquivalent atTop f g

/-- The target main term `exp(-γ)/log x`. -/
@[expose] def mertensMain (x : ℝ) : ℝ :=
  Real.exp (-Real.eulerMascheroniConstant) / Real.log x

/-! ## Exact proposition contracts for the parent-facing cone -/

/-- P-MERT-01. -/
@[expose] def LocalCorrectionContract : Prop :=
  ∀ p : ℕ, p.Prime →
    correction p = correctionPowerSeries p ∧
      0 ≤ correction p ∧ correction p ≤ 2 / (p : ℝ) ^ 2

/-- P-MERT-02, with convergence represented by an explicit sum witness. -/
@[expose] def CorrectionConvergenceContract (H : ℝ) : Prop :=
  Summable (fun p : ℕ ↦ ‖correctionSeq p‖) ∧
    HasSum correctionSeq H ∧ Tendsto correctionLE atTop (𝓝 H)

/-- P-MERT-03. -/
@[expose] def FiniteProductLogContract : Prop :=
  ∀ x : ℝ, 2 ≤ x →
    Real.log (qLE x) = -reciprocalPrimeSum x - correctionLE x

/-- P-MERT-06A, including positivity and the endpoint squeeze. -/
@[expose] def EndpointContract : Prop :=
  (∀ x : ℝ, 2 ≤ x →
    0 < endpointFactor x ∧
    qLE x = qLT x * endpointFactor x ∧
    1 ≤ (endpointFactor x)⁻¹ ∧
    (endpointFactor x)⁻¹ ≤ (1 - x⁻¹)⁻¹) ∧
  Tendsto (fun x : ℝ ↦ (endpointFactor x)⁻¹) atTop (𝓝 1)

/-- P-MERT-06B. -/
@[expose] def IntervalQuotientContract : Prop :=
  ∀ A B : ℝ, 2 ≤ A → A < B →
    intervalProduct A B = qLT B / qLT A ∧
    intervalProduct A B = qLE B * endpointFactor A / (qLE A * endpointFactor B)

/-- P-MERT-08, with witnesses selected before both moving endpoints. -/
@[expose] def IntervalComparisonContract : Prop :=
  ∃ X0 cMinus cPlus : ℝ,
    2 ≤ X0 ∧ 0 < cMinus ∧ 0 < cPlus ∧
    ∀ A B : ℝ, X0 ≤ A → A < B →
      cMinus * (Real.log A / Real.log B) ≤ intervalProduct A B ∧
      intervalProduct A B ≤ cPlus * (Real.log A / Real.log B)

/-- FT-MERTENS. -/
@[expose] def StrictMertensAsymptotic : Prop := AtTopEquivalent qLT mertensMain

/-- EXT-002 exactly: strict asymptotic together with the uniform interval output. -/
@[expose] def EXT002Contract : Prop := StrictMertensAsymptotic ∧ IntervalComparisonContract

/-! ## Witness-carrying interfaces -/

/-- The closed child output.  All witnesses are fixed before the cutoff variables.
`H` is not a totalized infinite sum: `correction_hasSum` is its defining witness. -/
structure SumConstantInterface where
  H : ℝ
  correction_norm_summable : Summable (fun p : ℕ ↦ ‖correctionSeq p‖)
  correction_hasSum : HasSum correctionSeq H
  correction_partial_tendsto : Tendsto correctionLE atTop (𝓝 H)
  B : ℝ
  B_identity : B = Real.eulerMascheroniConstant - H
  Delta : ℕ → ℝ
  C0 : ℝ
  C0_pos : 0 < C0
  integer_formula : ∀ G : ℕ, 2 ≤ G →
    reciprocalPrimeSumNat G = Real.log (Real.log G) + B + Delta G
  integer_rate : ∀ G : ℕ, 2 ≤ G → |Delta G| ≤ C0 / Real.log G
  R : ℝ → ℝ
  CR : ℝ
  XR : ℝ
  remainder_rate : ReciprocalLogRate R CR XR
  real_formula : ∀ x : ℝ, 2 ≤ x →
    reciprocalPrimeSum x = Real.log (Real.log x) + B + R x
  remainder_tendsto : Tendsto R atTop (𝓝 0)

/-- The complete main-module formal interface.  Proof construction may consume the
fixed child witnesses and every endpoint/rate/positivity invariant directly. -/
structure MertensInterface where
  sumConstant : SumConstantInterface
  localCorrection : LocalCorrectionContract
  correction_tail : ∀ x : ℝ, 2 ≤ x →
    0 ≤ sumConstant.H - correctionLE x ∧
      sumConstant.H - correctionLE x ≤ 2 / (x - 1)
  finiteProductLog : FiniteProductLogContract
  E : ℝ → ℝ
  CE : ℝ
  XE : ℝ
  E_definition : ∀ x : ℝ, 2 ≤ x →
    E x = (sumConstant.H - correctionLE x) - sumConstant.R x
  log_cancellation : ∀ x : ℝ, 2 ≤ x →
    Real.log (qLE x) =
      -Real.log (Real.log x) - Real.eulerMascheroniConstant + E x
  E_rate : ReciprocalLogRate E CE XE
  E_tendsto : Tendsto E atTop (𝓝 0)
  weakRelativeError : ℝ → ℝ
  CWeak : ℝ
  XWeak : ℝ
  weak_exact : ∀ x : ℝ, 2 ≤ x →
    qLE x = mertensMain x * (1 + weakRelativeError x)
  weak_exponential_exact : ∀ x : ℝ, 2 ≤ x →
    qLE x = mertensMain x * Real.exp (E x)
  weakRelativeError_definition : ∀ x : ℝ, 2 ≤ x →
    weakRelativeError x = Real.exp (E x) - 1
  weak_rate : ReciprocalLogRate weakRelativeError CWeak XWeak
  weak_asymptotic : AtTopEquivalent qLE mertensMain
  endpoint : EndpointContract
  intervalQuotient : IntervalQuotientContract
  strictRelativeError : ℝ → ℝ
  CStrict : ℝ
  XStrict : ℝ
  strict_exact : ∀ x : ℝ, 2 ≤ x →
    qLT x = mertensMain x * (1 + strictRelativeError x)
  strict_rate : ReciprocalLogRate strictRelativeError CStrict XStrict
  strict_asymptotic : StrictMertensAsymptotic
  intervalComparison : IntervalComparisonContract

/-- The exact parent-consumer surface, packaged without changing witness order. -/
structure ParentEXT002Interface where
  strict_asymptotic : StrictMertensAsymptotic
  X_M : ℝ
  c_M_minus : ℝ
  c_M_plus : ℝ
  X_M_ge_two : 2 ≤ X_M
  c_M_minus_pos : 0 < c_M_minus
  c_M_plus_pos : 0 < c_M_plus
  interval_comparison : ∀ A B : ℝ, X_M ≤ A → A < B →
    c_M_minus * (Real.log A / Real.log B) ≤ intervalProduct A B ∧
    intervalProduct A B ≤ c_M_plus * (Real.log A / Real.log B)

end

end Erdos448.DPMertens
