module

import all Mathlib.Basic.Real.Basic
public import Mathlib

public section

set_option backward.isDefEq.respectTransparency false

/-!
Lean-facing representation authority for `DP-MEAN-017`.

Mathematical authority: `../stage3/AUTHORITY.md`, SHA-256
`ed4eb39f1a3ad059e4a6623373ddd07bc6cb0959ac09ccee6b8e52a8646dbc75`.

Accepted `DP-MEAN-T001` contract hash:
`4b7a4e7df2cb622f6cca1920b2bb43dbb41c9c5aef18cd206b6fcc2a4ff1e2a2`.

This file contains definitions, proposition-valued interfaces, and provider
records only.  It intentionally contains no proof implementation.
-/

namespace Erdos448.DPMean

noncomputable section

@[expose] abbrev ArithmeticFunction := ℕ → ℝ

@[expose] def Nonnegative (h : ArithmeticFunction) : Prop :=
  ∀ n, 0 < n → 0 ≤ h n

@[expose] def Multiplicative (h : ArithmeticFunction) : Prop :=
  h 1 = 1 ∧ ∀ a b, 0 < a → 0 < b →
    Nat.Coprime a b → h (a * b) = h a * h b

structure NonnegativeMultiplicative (h : ArithmeticFunction) : Prop where
  nonnegative : Nonnegative h
  multiplicative : Multiplicative h

structure ParameterRange (lambda1 lambda2 : ℝ) : Prop where
  lambda1_nonnegative : 0 ≤ lambda1
  lambda2_nonnegative : 0 ≤ lambda2
  lambda2_lt_two : lambda2 < 2

@[expose] def PrimePowerGeometricBound
    (h : ArithmeticFunction) (lambda1 lambda2 : ℝ) : Prop :=
  ∀ p, Nat.Prime p → ∀ j : ℕ,
    0 ≤ h (p ^ j) ∧ h (p ^ j) ≤ lambda1 * lambda2 ^ j

structure MeanAssumptions
    (h : ArithmeticFunction) (lambda1 lambda2 : ℝ) : Prop where
  h_nonnegative_multiplicative : NonnegativeMultiplicative h
  parameter_range : ParameterRange lambda1 lambda2
  prime_power_geometric_bound : PrimePowerGeometricBound h lambda1 lambda2

@[expose] def inclusiveNatDomain (x : ℝ) : Finset ℕ :=
  (Finset.range (Nat.floor x + 1)).filter (fun n => 0 < n)

@[expose] def strictNatDomain (X : ℝ) : Finset ℕ :=
  (Finset.range (Nat.ceil X)).filter (fun n => 0 < n)

@[expose] def inclusivePrimeDomain (x : ℝ) : Finset ℕ :=
  (inclusiveNatDomain x).filter Nat.Prime

@[expose] def strictPrimeDomain (X : ℝ) : Finset ℕ :=
  (strictNatDomain X).filter Nat.Prime

@[expose] def theta (y : ℝ) : ℝ :=
  ∑ p ∈ inclusivePrimeDomain y, Real.log (p : ℝ)

@[expose] def inclusiveMean (h : ArithmeticFunction) (x : ℝ) : ℝ :=
  ∑ n ∈ inclusiveNatDomain x, h n

@[expose] def reciprocalMean (h : ArithmeticFunction) (x : ℝ) : ℝ :=
  ∑ n ∈ inclusiveNatDomain x, h n / (n : ℝ)

@[expose] def smoothingIntegral (h : ArithmeticFunction) (x : ℝ) : ℝ :=
  ∫ t in (1 : ℝ)..x, inclusiveMean h t / t

@[expose] def smoothingWeightedSum (h : ArithmeticFunction) (x : ℝ) : ℝ :=
  ∑ n ∈ inclusiveNatDomain x, h n * Real.log (x / (n : ℝ))

@[expose] def weightedLogMean (h : ArithmeticFunction) (x : ℝ) : ℝ :=
  ∑ n ∈ inclusiveNatDomain x, h n * Real.log (n : ℝ)

@[expose] def chebyshevConstant : ℝ := 4 * Real.log 2

@[expose] def firstPowerConstant (lambda1 lambda2 : ℝ) : ℝ :=
  chebyshevConstant * lambda1 * lambda2

@[expose] def higherPowerTerm (lambda2 : ℝ) (p r : ℕ) : ℝ :=
  if Nat.Prime p ∧ 2 ≤ r then
    (r : ℝ) * Real.log (p : ℝ) * (lambda2 / (p : ℝ)) ^ r
  else 0

@[expose] def higherPowerConstant (lambda1 lambda2 : ℝ) : ℝ :=
  lambda1 * ∑' p : ℕ, ∑' r : ℕ, higherPowerTerm lambda2 p r

@[expose] def primeLogSquareTerm (p : ℕ) : ℝ :=
  if Nat.Prime p then Real.log (p : ℝ) / (p : ℝ) ^ 2 else 0

@[expose] def geometricMajorant (lambda1 lambda2 : ℝ) : ℝ :=
  let rho := lambda2 / 2
  (2 * lambda1 * lambda2 ^ 2 / (1 - rho) ^ 2) *
    ∑' p : ℕ, primeLogSquareTerm p

@[expose] def strictCutoff (X : ℝ) : ℕ :=
  Nat.ceil X - 1

@[expose] def eulerTerm (h : ArithmeticFunction) (p j : ℕ) : ℝ :=
  h (p ^ j) / (p : ℝ) ^ j

@[expose] def inclusiveEulerProduct (h : ArithmeticFunction) (x : ℝ) : ℝ :=
  ∏ p ∈ inclusivePrimeDomain x, ∑' j : ℕ, eulerTerm h p j

@[expose] def strictEulerProduct (h : ArithmeticFunction) (X : ℝ) : ℝ :=
  ∏ p ∈ strictPrimeDomain X, ∑' j : ℕ, eulerTerm h p j

@[expose] def strictMean (h : ArithmeticFunction) (X : ℝ) : ℝ :=
  ∑ n ∈ strictNatDomain X, h n

@[expose] def primePowerCoprimeSum (h : ArithmeticFunction) (x : ℝ) : ℝ :=
  ∑ p ∈ inclusivePrimeDomain x,
    ∑ r ∈ inclusiveNatDomain x,
      ∑ m ∈ inclusiveNatDomain x,
        if Nat.Coprime p m ∧ (((p ^ r) * m : ℕ) : ℝ) ≤ x then
          h (p ^ r) * h m * Real.log (((p ^ r : ℕ) : ℝ))
        else 0

@[expose] def firstPowerContribution (h : ArithmeticFunction) (x : ℝ) : ℝ :=
  ∑ m ∈ inclusiveNatDomain (x / 2),
    h m * ∑ p ∈ inclusivePrimeDomain (x / (m : ℝ)),
      h p * Real.log (p : ℝ)

@[expose] def higherPowerContribution (h : ArithmeticFunction) (x : ℝ) : ℝ :=
  ∑ m ∈ inclusiveNatDomain (x / 4),
    h m * ∑ p ∈ inclusivePrimeDomain x,
      ∑ r ∈ inclusiveNatDomain x,
        if 2 ≤ r ∧ (((p ^ r : ℕ) : ℝ) ≤ x / (m : ℝ)) then
          h (p ^ r) * Real.log (((p ^ r : ℕ) : ℝ))
        else 0

/- DP-MEAN-DEF-003: total definitions above are accompanied by the exact
integral-to-finite-sum specification on the intended domain. -/
@[expose] def SmoothingDefinitionStatement : Prop :=
  ∀ h : ArithmeticFunction, ∀ x : ℝ, 1 ≤ x →
    smoothingIntegral h x = smoothingWeightedSum h x

end

end Erdos448.DPMean

open Erdos448.DPMean

noncomputable section

/- DP-MEAN-P001. -/
@[expose] def Erdos448.DPMean.P001Statement : Prop :=
  ∀ y : ℝ, 2 ≤ y → theta y ≤ chebyshevConstant * y

structure Erdos448.DPMean.HigherPowerConvergencePayload
    (lambda1 lambda2 : ℝ) : Prop where
  local_summable : ∀ p : ℕ, Nat.Prime p →
    Summable (fun r : ℕ => higherPowerTerm lambda2 p r)
  outer_summable : Summable
    (fun p : ℕ => ∑' r : ℕ, higherPowerTerm lambda2 p r)
  prime_log_square_summable : Summable primeLogSquareTerm
  bound : higherPowerConstant lambda1 lambda2 ≤
    geometricMajorant lambda1 lambda2

/- DP-MEAN-P002.  Finiteness is represented by explicit summability fields,
not hidden by the total value of `tsum`. -/
@[expose] def Erdos448.DPMean.P002Statement : Prop :=
  ∀ lambda1 lambda2 : ℝ, ParameterRange lambda1 lambda2 →
    HigherPowerConvergencePayload lambda1 lambda2

/- DP-MEAN-P003. -/
@[expose] def Erdos448.DPMean.P003Statement : Prop :=
  ∀ h : ArithmeticFunction, ∀ lambda1 lambda2 y : ℝ,
    Nonnegative h →
    PrimePowerGeometricBound h lambda1 lambda2 →
    ParameterRange lambda1 lambda2 →
    2 ≤ y →
    (∑ p ∈ inclusivePrimeDomain y, h p * Real.log (p : ℝ)) ≤
      firstPowerConstant lambda1 lambda2 * y

structure Erdos448.DPMean.SmoothingBoundPayload
    (h : ArithmeticFunction) (x : ℝ) : Prop where
  combined : inclusiveMean h x + smoothingIntegral h x ≤
    x * reciprocalMean h x
  integral_only : smoothingIntegral h x ≤ x * reciprocalMean h x

/- DP-MEAN-P004. -/
@[expose] def Erdos448.DPMean.P004Statement : Prop :=
  ∀ h : ArithmeticFunction, Nonnegative h → ∀ x : ℝ, 1 ≤ x →
    SmoothingBoundPayload h x

/- DP-MEAN-P005. -/
@[expose] def Erdos448.DPMean.P005Statement : Prop :=
  ∀ h : ArithmeticFunction, Nonnegative h → ∀ x : ℝ, 1 ≤ x →
    inclusiveMean h x * Real.log x =
      weightedLogMean h x + smoothingIntegral h x

structure Erdos448.DPMean.PrimePowerReindexPayload
    (h : ArithmeticFunction) (x : ℝ) : Prop where
  exact_identity : weightedLogMean h x = primePowerCoprimeSum h x
  /-- For a fixed prime divisor, the inverse data `(r,m)` is unique. -/
  multiplicity_one : ∀ n : ℕ, 0 < n → (n : ℝ) ≤ x →
    ∀ p : ℕ, Nat.Prime p → p ∣ n →
      ∃! rm : ℕ × ℕ,
        1 ≤ rm.1 ∧ n = p ^ rm.1 * rm.2 ∧ Nat.Coprime p rm.2

/- DP-MEAN-P006. -/
@[expose] def Erdos448.DPMean.P006Statement : Prop :=
  ∀ h : ArithmeticFunction, NonnegativeMultiplicative h →
    ∀ x : ℝ, 1 ≤ x → PrimePowerReindexPayload h x

/- DP-MEAN-P007. -/
@[expose] def Erdos448.DPMean.P007Statement : Prop :=
  ∀ h : ArithmeticFunction, ∀ lambda1 lambda2 x : ℝ,
    Nonnegative h →
    PrimePowerGeometricBound h lambda1 lambda2 →
    ParameterRange lambda1 lambda2 →
    2 ≤ x →
    firstPowerContribution h x ≤
      firstPowerConstant lambda1 lambda2 * x * reciprocalMean h x

/- DP-MEAN-P008. -/
@[expose] def Erdos448.DPMean.P008Statement : Prop :=
  ∀ h : ArithmeticFunction, ∀ lambda1 lambda2 x : ℝ,
    Nonnegative h →
    PrimePowerGeometricBound h lambda1 lambda2 →
    ParameterRange lambda1 lambda2 →
    1 ≤ x →
    higherPowerContribution h x ≤
      higherPowerConstant lambda1 lambda2 * x * reciprocalMean h x

/- DP-MEAN-P009. -/
@[expose] def Erdos448.DPMean.P009Statement : Prop :=
  ∀ h : ArithmeticFunction, ∀ lambda1 lambda2 x : ℝ,
    MeanAssumptions h lambda1 lambda2 →
    2 ≤ x →
    weightedLogMean h x ≤
      (firstPowerConstant lambda1 lambda2 +
        higherPowerConstant lambda1 lambda2) * x * reciprocalMean h x

/- DP-MEAN-P010. -/
@[expose] def Erdos448.DPMean.P010Statement : Prop :=
  ∀ h : ArithmeticFunction, ∀ lambda1 lambda2 x : ℝ,
    MeanAssumptions h lambda1 lambda2 →
    2 ≤ x →
    inclusiveMean h x ≤
      (firstPowerConstant lambda1 lambda2 +
          higherPowerConstant lambda1 lambda2 + 1) *
        (x / Real.log x) * reciprocalMean h x

structure Erdos448.DPMean.EulerDominationPayload
    (h : ArithmeticFunction) (x : ℝ) : Prop where
  local_summable : ∀ p : ℕ, Nat.Prime p → (p : ℝ) ≤ x →
    Summable (fun j : ℕ => eulerTerm h p j)
  domination : reciprocalMean h x ≤ inclusiveEulerProduct h x

/- DP-MEAN-P011. -/
@[expose] def Erdos448.DPMean.P011Statement : Prop :=
  ∀ h : ArithmeticFunction, ∀ lambda1 lambda2 x : ℝ,
    MeanAssumptions h lambda1 lambda2 →
    1 ≤ x → EulerDominationPayload h x

structure Erdos448.DPMean.StrictEndpointPayload (X : ℝ) : Prop where
  nat_iff : ∀ n : ℕ, 0 < n →
    ((n : ℝ) < X ↔ n ≤ strictCutoff X)
  prime_iff : ∀ p : ℕ, Nat.Prime p →
    ((p : ℝ) < X ↔ p ≤ strictCutoff X)
  cutoff_at_least_two : 2 < X → 2 ≤ strictCutoff X
  factor_bound : 2 < X →
    ((strictCutoff X : ℕ) : ℝ) /
        Real.log ((strictCutoff X : ℕ) : ℝ) ≤
      2 * (X / Real.log X)

/- DP-MEAN-P012. -/
@[expose] def Erdos448.DPMean.P012Statement : Prop :=
  ∀ X : ℝ, 2 ≤ X → StrictEndpointPayload X

end


namespace Erdos448.DPMean

noncomputable section

@[expose] def meanThreshold (lambda1 lambda2 : ℝ) : ℝ :=
  max 1 (2 * (firstPowerConstant lambda1 lambda2 +
    higherPowerConstant lambda1 lambda2 + 1))

@[expose] def MeanBoundAt
    (lambda1 lambda2 C : ℝ) (h : ArithmeticFunction) (X : ℝ) : Prop :=
  strictMean h X ≤
    C * (X / Real.log X) * strictEulerProduct h X

end

end Erdos448.DPMean

open Erdos448.DPMean

noncomputable section

/-! ## Complete object-indexed S3 interface surface

The declarations in this section give every required S3 object its own actual
Lean identity.  They are transparent wrappers around the canonical
representations above; no existing declaration or mathematical contract is
changed. -/

/- DP-MEAN-DEF-001--005: value-valued definitions. -/
@[expose] def Erdos448.DPMean.DEF001Interface (y : ℝ) : ℝ :=
  theta y

@[expose] def Erdos448.DPMean.DEF002Interface
    (h : ArithmeticFunction) (x : ℝ) : ℝ × ℝ :=
  (inclusiveMean h x, reciprocalMean h x)

@[expose] def Erdos448.DPMean.DEF003Interface
    (h : ArithmeticFunction) (x : ℝ) : ℝ × ℝ :=
  (smoothingIntegral h x, weightedLogMean h x)

@[expose] def Erdos448.DPMean.DEF004Interface
    (lambda1 lambda2 : ℝ) : ℝ × ℝ :=
  (firstPowerConstant lambda1 lambda2,
    higherPowerConstant lambda1 lambda2)

@[expose] def Erdos448.DPMean.DEF005Interface (X : ℝ) : ℝ :=
  (strictCutoff X : ℝ)

/- DP-MEAN-DEF-006--026: proposition/expression interfaces. -/
@[expose] def Erdos448.DPMean.DEF006Interface (h : ArithmeticFunction) : Prop :=
  Nonnegative h

@[expose] def Erdos448.DPMean.DEF007Interface (h : ArithmeticFunction) : Prop :=
  Multiplicative h

@[expose] def Erdos448.DPMean.DEF008Interface
    (h : ArithmeticFunction) (lambda1 lambda2 : ℝ) : Prop :=
  PrimePowerGeometricBound h lambda1 lambda2

@[expose] def Erdos448.DPMean.DEF009Interface (y : ℝ) : Prop :=
  theta y ≤ chebyshevConstant * y

@[expose] def Erdos448.DPMean.DEF010Interface (lambda1 lambda2 : ℝ) : Prop :=
  HigherPowerConvergencePayload lambda1 lambda2

@[expose] def Erdos448.DPMean.DEF011Interface
    (h : ArithmeticFunction) (lambda1 lambda2 y : ℝ) : Prop :=
  (∑ p ∈ inclusivePrimeDomain y, h p * Real.log (p : ℝ)) ≤
    firstPowerConstant lambda1 lambda2 * y

@[expose] def Erdos448.DPMean.DEF012Interface
    (h : ArithmeticFunction) (x : ℝ) : Prop :=
  inclusiveMean h x + smoothingIntegral h x ≤
    x * reciprocalMean h x

@[expose] def Erdos448.DPMean.DEF013Interface
    (h : ArithmeticFunction) (x : ℝ) : Prop :=
  smoothingIntegral h x ≤ x * reciprocalMean h x

@[expose] def Erdos448.DPMean.DEF014Interface
    (h : ArithmeticFunction) (x : ℝ) : Prop :=
  inclusiveMean h x * Real.log x =
    weightedLogMean h x + smoothingIntegral h x

@[expose] def Erdos448.DPMean.DEF015Interface
    (h : ArithmeticFunction) (x : ℝ) : Prop :=
  weightedLogMean h x = primePowerCoprimeSum h x

@[expose] def Erdos448.DPMean.DEF016Interface
    (h : ArithmeticFunction) (lambda1 lambda2 x : ℝ) : Prop :=
  firstPowerContribution h x ≤
    firstPowerConstant lambda1 lambda2 * x * reciprocalMean h x

@[expose] def Erdos448.DPMean.DEF017Interface
    (h : ArithmeticFunction) (lambda1 lambda2 x : ℝ) : Prop :=
  higherPowerContribution h x ≤
    higherPowerConstant lambda1 lambda2 * x * reciprocalMean h x

@[expose] def Erdos448.DPMean.DEF018Interface
    (h : ArithmeticFunction) (lambda1 lambda2 x : ℝ) : Prop :=
  weightedLogMean h x ≤
    (firstPowerConstant lambda1 lambda2 +
      higherPowerConstant lambda1 lambda2) * x * reciprocalMean h x

@[expose] def Erdos448.DPMean.DEF019Interface
    (h : ArithmeticFunction) (lambda1 lambda2 x : ℝ) : Prop :=
  inclusiveMean h x ≤
    (firstPowerConstant lambda1 lambda2 +
        higherPowerConstant lambda1 lambda2 + 1) *
      (x / Real.log x) * reciprocalMean h x

@[expose] def Erdos448.DPMean.DEF020Interface
    (h : ArithmeticFunction) (x : ℝ) : Prop :=
  reciprocalMean h x ≤ inclusiveEulerProduct h x

@[expose] def Erdos448.DPMean.DEF021Interface (X : ℝ) : Prop :=
  ∀ n : ℕ, 0 < n →
    ((n : ℝ) < X ↔ (n : ℝ) ≤ DEF005Interface X)

@[expose] def Erdos448.DPMean.DEF022Interface (X : ℝ) : Prop :=
  ∀ p : ℕ, Nat.Prime p →
    ((p : ℝ) < X ↔ (p : ℝ) ≤ DEF005Interface X)

@[expose] def Erdos448.DPMean.DEF023Interface (X : ℝ) : Prop :=
  1 ≤ DEF005Interface X

@[expose] def Erdos448.DPMean.DEF024Interface (X : ℝ) : Prop :=
  DEF005Interface X / Real.log (DEF005Interface X) ≤
    2 * (X / Real.log X)

@[expose] def Erdos448.DPMean.DEF025Interface
    (h : ArithmeticFunction) (lambda1 lambda2 X C : ℝ) : Prop :=
  MeanBoundAt lambda1 lambda2 C h X

@[expose] def Erdos448.DPMean.DEF026Interface (lambda1 lambda2 : ℝ) : ℝ :=
  meanThreshold lambda1 lambda2

structure Erdos448.DPMean.StrictEndpointFullPayload (X : ℝ) : Prop where
  integer_endpoint_transport : DEF021Interface X
  prime_endpoint_transport : DEF022Interface X
  cutoff_at_least_one : DEF023Interface X
  strict_cutoff_at_least_two : 2 < X → 2 ≤ DEF005Interface X
  strict_factor_comparison : 2 < X → DEF024Interface X

/- Exact five-conclusion surface for DP-MEAN-P012.  The pre-existing
`P012Statement` remains available unchanged for compatibility. -/
@[expose] def Erdos448.DPMean.P012FullStatement : Prop :=
  ∀ X : ℝ, 2 ≤ X → StrictEndpointFullPayload X

/- DP-MEAN-P013--P016: exact adapters used by the construction DAG. -/
@[expose] def Erdos448.DPMean.P013Statement : Prop :=
  ∀ h : ArithmeticFunction,
    NonnegativeMultiplicative h → Nonnegative h

@[expose] def Erdos448.DPMean.P014Statement : Prop :=
  ∀ x : ℝ, 2 ≤ x → 1 ≤ x

@[expose] def Erdos448.DPMean.P015Statement : Prop :=
  ∀ x : ℝ, 2 < x → 2 ≤ x

@[expose] def Erdos448.DPMean.P016Statement : Prop :=
  ∀ x m : ℝ, 2 ≤ x → 1 ≤ m → m ≤ x / 2 → 2 ≤ x / m

structure Erdos448.DPMean.StrictBranchFactsPayload (X : ℝ) : Prop where
  integer_endpoint_transport : DEF021Interface X
  prime_endpoint_transport : DEF022Interface X
  cutoff_at_least_one : 1 ≤ DEF005Interface X
  cutoff_at_least_two : 2 ≤ DEF005Interface X
  factor_comparison : DEF024Interface X

/- DP-MEAN-P017. -/
@[expose] def Erdos448.DPMean.P017Statement : Prop :=
  ∀ X : ℝ, 2 < X → StrictBranchFactsPayload X

/- DP-MEAN-P018, including every repaired ambient sign hypothesis. -/
@[expose] def Erdos448.DPMean.P018Statement : Prop :=
  ∀ h : ArithmeticFunction, ∀ lambda1 lambda2 X : ℝ,
    NonnegativeMultiplicative h →
    PrimePowerGeometricBound h lambda1 lambda2 →
    0 ≤ lambda1 →
    (0 ≤ lambda2 ∧ lambda2 < 2) →
    2 < X →
    DEF019Interface h lambda1 lambda2 (DEF005Interface X) →
    DEF020Interface h (DEF005Interface X) →
    DEF021Interface X →
    DEF022Interface X →
    DEF024Interface X →
    DEF025Interface h lambda1 lambda2 X
      (DEF026Interface lambda1 lambda2)

/- DP-MEAN-P019. -/
@[expose] def Erdos448.DPMean.P019Statement : Prop :=
  ∀ h : ArithmeticFunction, ∀ lambda1 lambda2 X : ℝ,
    NonnegativeMultiplicative h →
    PrimePowerGeometricBound h lambda1 lambda2 →
    0 ≤ lambda1 →
    (0 ≤ lambda2 ∧ lambda2 < 2) →
    X = 2 →
    DEF025Interface h lambda1 lambda2 X
      (DEF026Interface lambda1 lambda2)

/- DP-MEAN-P020. -/
@[expose] def Erdos448.DPMean.P020Statement : Prop :=
  ∀ h : ArithmeticFunction, ∀ lambda1 lambda2 X : ℝ,
    2 ≤ X →
    (2 < X → DEF025Interface h lambda1 lambda2 X
      (DEF026Interface lambda1 lambda2)) →
    (X = 2 → DEF025Interface h lambda1 lambda2 X
      (DEF026Interface lambda1 lambda2)) →
    DEF025Interface h lambda1 lambda2 X
      (DEF026Interface lambda1 lambda2)

/- Frozen construction targets for the repaired T09/T10 boundary. -/
@[expose] def Erdos448.DPMean.T09ConstructionTarget : Prop :=
  P012FullStatement

end

namespace Erdos448.DPMean

noncomputable section

/- The witness `C` is selected after `(lambda1, lambda2)` and before both
`h` and `X`.  This makes uniformity in the arithmetic function and endpoint
part of the type rather than a comment. -/
structure MeanProvider (lambda1 lambda2 : ℝ) where
  C : ℝ
  C_positive : 0 < C
  threshold_le_C : meanThreshold lambda1 lambda2 ≤ C
  local_series_summable : ∀ h : ArithmeticFunction,
    PrimePowerGeometricBound h lambda1 lambda2 →
    ∀ p : ℕ, Nat.Prime p →
      Summable (fun j : ℕ => eulerTerm h p j)
  bound : ∀ h : ArithmeticFunction,
    NonnegativeMultiplicative h →
    PrimePowerGeometricBound h lambda1 lambda2 →
    ∀ X : ℝ, 2 ≤ X → MeanBoundAt lambda1 lambda2 C h X

/- DP-MEAN-T001 / parent EXT-001, with the exact constant dependency order. -/
@[expose] abbrev T001ProviderFactory :=
  ∀ lambda1 lambda2 : ℝ, ParameterRange lambda1 lambda2 →
    MeanProvider lambda1 lambda2

end

end Erdos448.DPMean

open Erdos448.DPMean

@[expose] def Erdos448.DPMean.T001Statement : Prop :=
  ∀ lambda1 lambda2 : ℝ, ParameterRange lambda1 lambda2 →
    Nonempty (MeanProvider lambda1 lambda2)

@[expose] def Erdos448.DPMean.T10ConstructionTarget : Prop :=
  P010Statement → P011Statement → P012FullStatement → T001Statement

namespace Erdos448.DPMean

noncomputable section

/- A construction worker may receive this record as a local parameter.
Nothing here installs any field as a global theorem or axiom. -/
structure ConstructionPayload where
  smoothing_definition : SmoothingDefinitionStatement
  p001 : P001Statement
  p002 : P002Statement
  p003 : P003Statement
  p004 : P004Statement
  p005 : P005Statement
  p006 : P006Statement
  p007 : P007Statement
  p008 : P008Statement
  p009 : P009Statement
  p010 : P010Statement
  p011 : P011Statement
  p012 : P012Statement

structure CompleteProvider where
  construction_payload : ConstructionPayload
  final_provider : T001ProviderFactory

/- Representative consumer signatures.  These stress the witness order used
by parent consumers P-002, P-011, and P-059 without asserting their proofs. -/
@[expose] abbrev P002ConsumerInterface
    (lambda0 lambda : ℝ) (range : ParameterRange lambda0 lambda) :=
  MeanProvider lambda0 lambda

@[expose] abbrev P011ConsumerInterface
    (LambdaY : ℝ) (range : ParameterRange 1 LambdaY) :=
  MeanProvider 1 LambdaY

@[expose] abbrev P059ConsumerInterface
    (LambdaW : ℝ) (range : ParameterRange (max 1 LambdaW) 1) :=
  MeanProvider (max 1 LambdaW) 1

end

end Erdos448.DPMean
