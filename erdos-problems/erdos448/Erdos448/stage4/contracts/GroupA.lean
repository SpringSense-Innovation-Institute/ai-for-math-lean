module

import all Mathlib.Basic.Real.Basic
public import Erdos448.stage4.RootObjects

public section

set_option backward.isDefEq.respectTransparency false

/-!
Group A proposition contracts for the frozen S3 authority.

Mathematical authority: `Erdos448/stage3/canonical/CURRENT.md`, SHA-256
`07b55262f273e07042e14b2b054ed5cbf63ff71dcc6720161151c8a3b133c047`.

Only definitions, proposition aliases, and witness/specification structures
occur here.  In particular, no field is installed as a theorem or axiom.
-/

namespace Erdos448.Stage4.Contracts

open Filter Finset Set
open scoped BigOperators Topology

noncomputable section

/-! ## Shared exact subjects for EXT-001, P-001--P-008 -/

@[expose] def PrimePowerGeometricBound
    (h : ArithmeticWeight) (lambda1 lambda2 : ℝ) : Prop :=
  ∀ p : ℕ, p.Prime → ∀ j : ℕ,
    0 ≤ h (p ^ j) ∧ h (p ^ j) ≤ lambda1 * lambda2 ^ j

structure MeanParameterRange (lambda1 lambda2 : ℝ) : Prop where
  lambda1_nonnegative : 0 ≤ lambda1
  lambda2_nonnegative : 0 ≤ lambda2
  lambda2_lt_two : lambda2 < 2

@[expose] def localEulerSeries (u v : ArithmeticWeight) (p : ℕ) : ℝ :=
  ∑' j : ℕ, u (p ^ j) * v (p ^ j) / (p : ℝ) ^ j

@[expose] def meanEulerSeries (h : ArithmeticWeight) (p : ℕ) : ℝ :=
  ∑' j : ℕ, h (p ^ j) / (p : ℝ) ^ j

@[expose] def strictMean (h : ArithmeticWeight) (X : ℝ) : ℝ :=
  ∑ n ∈ positiveNatsBelow X, h n

@[expose] def strictEulerProduct (h : ArithmeticWeight) (X : ℝ) : ℝ :=
  ∏ p ∈ strictPrimeRange X, meanEulerSeries h p

@[expose] def primeIntervalProduct (L : ℕ → ℝ) (A B : ℝ) : ℝ :=
  ∏ p ∈ strictPrimeRange B, if A ≤ (p : ℝ) then L p else 1

@[expose] def localEulerProductAway
    (u v : ArithmeticWeight) (Ksh : PosNat) (X : ℝ) : ℝ :=
  ∏ p ∈ strictPrimeRange X,
    if p ∣ Ksh.1 then 1 else localEulerSeries u v p

@[expose] def HasPrimeSupportIn (d Ksh : PosNat) : Prop :=
  d.1.primeFactors ⊆ Ksh.1.primeFactors

@[expose] def coprimeInnerSum
    (u v : ArithmeticWeight) (Ksh : PosNat) (X : ℝ) : ℝ :=
  ∑ m ∈ positiveNatsBelow X,
    if Nat.Coprime m Ksh.1 then u m * v m else 0

@[expose] def commonPrimeTerm
    (u v : ArithmeticWeight) (Ksh : PosNat) (x : ℝ) (d : ℕ) : ℝ :=
  if hd : 0 < d then
    @ite ℝ (HasPrimeSupportIn ⟨d, hd⟩ Ksh) (Classical.propDecidable _)
      (
      u (Ksh.1 * d) * v d *
        ∑ m ∈ positiveNatsBelow (x / d),
          if Nat.Coprime m Ksh.1 then
            u m * v m * (Real.log (x / d) + Real.log d)
          else 0
      ) 0
  else 0

@[expose] def shiftedLogMean
    (u v : ArithmeticWeight) (Ksh : PosNat) (x : ℝ) : ℝ :=
  ∑ n ∈ positiveNatsBelow x,
    u (Ksh.1 * n) * v n * Real.log x

@[expose] def firstLogComponent
    (u v : ArithmeticWeight) (Ksh : PosNat) (d : PosNat) (x : ℝ) : ℝ :=
  coprimeInnerSum u v Ksh (x / d.1) * Real.log (x / d.1)

@[expose] def secondLogComponent
    (u v : ArithmeticWeight) (Ksh : PosNat) (d : PosNat) (x : ℝ) : ℝ :=
  coprimeInnerSum u v Ksh (x / d.1) * Real.log d.1

@[expose] def initialSegment (g : ArithmeticWeight) (X : ℝ) : ℝ :=
  strictMean g X

/-! ## EXT-001 and EXT-002 -/

/-- EXT-001.  The provider constant is fixed by `(lambda1,lambda2)` before
the arithmetic function and cutoff, exactly as required by `≪_{lambda1,lambda2}`. -/
structure EXT001Output (lambda1 lambda2 : ℝ) where
  constant : ℝ
  constant_pos : 0 < constant
  local_series_summable : ∀ h : ArithmeticWeight,
    PrimePowerGeometricBound h lambda1 lambda2 →
    ∀ p : ℕ, p.Prime →
      Summable (fun j : ℕ => h (p ^ j) / (p : ℝ) ^ j)
  bound : ∀ h : ArithmeticWeight,
    NonnegativeMultiplicativeWeight h →
    PrimePowerGeometricBound h lambda1 lambda2 →
    ∀ X : ℝ, 2 ≤ X →
      strictMean h X ≤ constant * (X / Real.log X) * strictEulerProduct h X

@[expose] def EXT001Statement : Prop :=
  ∀ lambda1 lambda2 : ℝ, MeanParameterRange lambda1 lambda2 →
    Nonempty (EXT001Output lambda1 lambda2)

@[expose] def mertensFactor (p : ℕ) : ℝ := 1 - 1 / (p : ℝ)

@[expose] def mertensStrictProduct (x : ℝ) : ℝ :=
  ∏ p ∈ strictPrimeRange x, mertensFactor p

@[expose] def mertensMainTerm (x : ℝ) : ℝ :=
  Real.exp (-Real.eulerMascheroniConstant) / Real.log x

@[expose] def StrictMertensAsymptotic : Prop :=
  Asymptotics.IsEquivalent atTop mertensStrictProduct mertensMainTerm

/-- EXT-002.  The same three witnesses serve every moving interval endpoint. -/
structure EXT002Output where
  strict_asymptotic : StrictMertensAsymptotic
  X_M : ℝ
  c_M_minus : ℝ
  c_M_plus : ℝ
  X_M_ge_two : 2 ≤ X_M
  c_M_minus_pos : 0 < c_M_minus
  c_M_plus_pos : 0 < c_M_plus
  interval_comparison : ∀ A B : ℝ, X_M ≤ A → A < B →
    c_M_minus * (Real.log A / Real.log B) ≤
        primeIntervalProduct mertensFactor A B ∧
      primeIntervalProduct mertensFactor A B ≤
        c_M_plus * (Real.log A / Real.log B)

@[expose] def EXT002Statement : Prop := Nonempty EXT002Output

/-! ## P-001--P-005: shifted means -/

@[expose] def P001Statement : Prop :=
  ∀ u v : ArithmeticWeight,
    NonnegativeMultiplicativeWeight u →
    NonnegativeMultiplicativeWeight v →
    ∀ Ksh : PosNat, ∀ x : ℝ, 2 ≤ x →
      Summable (commonPrimeTerm u v Ksh x) →
      shiftedLogMean u v Ksh x = ∑' d : ℕ, commonPrimeTerm u v Ksh x d

@[expose] def P001AStatement : Prop :=
  ∀ g : ArithmeticWeight, NonnegativeWeight g →
    ∀ X : ℝ, 0 < X →
      (X ≤ 1 → initialSegment g X = 0) ∧
      (1 < X → X < 2 → initialSegment g X = g 1)

@[expose] def P001BStatement : Prop :=
  ∀ u v : ArithmeticWeight,
    NonnegativeMultiplicativeWeight u →
    NonnegativeMultiplicativeWeight v →
    ∀ Ksh d : PosNat, ∀ x X : ℝ,
      2 ≤ x → X = x / d.1 → 0 < X → X < 2 →
      (∀ p : ℕ, p.Prime → (p : ℝ) < x →
        Summable (fun j : ℕ => u (p ^ j) * v (p ^ j) / (p : ℝ) ^ j)) →
      firstLogComponent u v Ksh d x ≤
        X * localEulerProductAway u v Ksh x

@[expose] def P001DStatement : Prop :=
  ∀ u v : ArithmeticWeight,
    NonnegativeMultiplicativeWeight u →
    NonnegativeMultiplicativeWeight v →
    (∀ p : ℕ, p.Prime →
      Summable (fun j : ℕ => u (p ^ j) * v (p ^ j) / (p : ℝ) ^ j)) →
    (∀ p : ℕ, p.Prime → 1 ≤ localEulerSeries u v p) →
    ∀ Ksh : PosNat, ∀ X x : ℝ, 2 ≤ X → X ≤ x →
      localEulerProductAway u v Ksh X ≤ localEulerProductAway u v Ksh x

@[expose] def ShiftedGeometricBounds
    (u v : ArithmeticWeight) (lambdaSeq : ℕ → ℝ) (lambda : ℝ) : Prop :=
  ∀ p : ℕ, p.Prime → ∀ i j : ℕ,
    0 ≤ u (p ^ (i + j)) * v (p ^ j) ∧
      u (p ^ (i + j)) * v (p ^ j) ≤ lambdaSeq i * lambda ^ j

/-- P-002 output.  The constant depends only on `(lambda0,lambda)` and is
fixed before the weights, majorant sequence, shifted integer, supported
divisor, and endpoint. -/
structure P002Output (lambda0 lambda : ℝ) where
  constant : ℝ
  constant_pos : 0 < constant
  local_series_summable : ∀ u v : ArithmeticWeight,
    ∀ lambdaSeq : ℕ → ℝ, lambdaSeq 0 = lambda0 →
    ShiftedGeometricBounds u v lambdaSeq lambda →
    ∀ p : ℕ, p.Prime →
      Summable (fun j : ℕ => u (p ^ j) * v (p ^ j) / (p : ℝ) ^ j)
  bound : ∀ u v : ArithmeticWeight,
    NonnegativeMultiplicativeWeight u →
    NonnegativeMultiplicativeWeight v →
    ∀ lambdaSeq : ℕ → ℝ, (∀ i : ℕ, 0 ≤ lambdaSeq i) →
    lambdaSeq 0 = lambda0 → ShiftedGeometricBounds u v lambdaSeq lambda →
    ∀ Ksh d : PosNat, ∀ x : ℝ,
    2 ≤ x → HasPrimeSupportIn d Ksh →
      firstLogComponent u v Ksh d x ≤
        constant * (x / d.1) * localEulerProductAway u v Ksh x

@[expose] def P002Statement : Prop :=
  ∀ lambda0 lambda : ℝ, 0 ≤ lambda0 → 0 ≤ lambda → lambda < 2 →
    Nonempty (P002Output lambda0 lambda)

@[expose] def P003Statement : Prop :=
  ∀ u v : ArithmeticWeight,
    NonnegativeMultiplicativeWeight u →
    NonnegativeMultiplicativeWeight v →
    (∀ p : ℕ, p.Prime →
      Summable (fun j : ℕ => u (p ^ j) * v (p ^ j) / (p : ℝ) ^ j)) →
    ∀ Ksh d : PosNat, ∀ x : ℝ,
      2 ≤ x → HasPrimeSupportIn d Ksh →
      secondLogComponent u v Ksh d x ≤
        (x / d.1) * Real.log d.1 * localEulerProductAway u v Ksh x

@[expose] def logarithmicPrimeFactorProduct (d : PosNat) : ℝ :=
  ∏ p ∈ d.1.primeFactors,
    (1 + (d.1.factorization p : ℝ) * Real.log p)

@[expose] def P004Statement : Prop :=
  ∀ d : PosNat,
    1 + Real.log d.1 ≤ logarithmicPrimeFactorProduct d

/-! ## P-005A: construction-critical convergence and factorization payload -/

/-- The nonnegative enlarged `d`-majorant in the accepted P-005A
factorization.  Its support restriction is literal: only positive integers
whose prime factors occur in `Ksh` contribute. -/
@[expose] def enlargedShiftMajorant
    (u v : ArithmeticWeight) (Ksh : PosNat) (d : ℕ) : ℝ :=
  by
    classical
    exact if hd : 0 < d then
      if HasPrimeSupportIn ⟨d, hd⟩ Ksh then
        u (Ksh.1 * d) * v d / (d : ℝ) *
          ∏ p ∈ d.primeFactors,
            (1 + (d.factorization p : ℝ) * Real.log p)
      else 0
    else 0

/-- P-005A payload.  The structure exposes every construction-critical fact:
both local convergence statements, the exact finite-support endpoint, the
enlarged majorant's summability and primewise factorization, and positivity of
the local denominators used by the shift quotients. -/
structure P005ASummabilityPayload
    (u v : ArithmeticWeight) (Ksh : PosNat) (X : ℝ) : Prop where
  unshifted_local_summable : ∀ p : ℕ, p.Prime →
    Summable (fun j : ℕ => u (p ^ j) * v (p ^ j) / (p : ℝ) ^ j)
  shifted_local_summable : ∀ p : ℕ, p.Prime → ∀ i : ℕ,
    Summable (fun j : ℕ =>
      u (p ^ (i + j)) * v (p ^ j) * (1 + j * Real.log p) / (p : ℝ) ^ j)
  exact_outer_support : ∀ d : ℕ,
    commonPrimeTerm u v Ksh X d ≠ 0 → 0 < d ∧ (d : ℝ) < X
  exact_outer_support_finite :
    (Function.support (commonPrimeTerm u v Ksh X)).Finite
  exact_outer_summable : Summable (commonPrimeTerm u v Ksh X)
  enlarged_majorant_nonnegative : ∀ d : ℕ,
    0 ≤ enlargedShiftMajorant u v Ksh d
  enlarged_majorant_summable : Summable (enlargedShiftMajorant u v Ksh)
  enlarged_majorant_factorization :
    ∑' d : ℕ, enlargedShiftMajorant u v Ksh d =
      ∏ p ∈ Ksh.1.primeFactors,
        shiftNumerator u v p (Ksh.1.factorization p)
  shift_denominator_positive : ∀ p : ℕ, p.Prime →
    0 < shiftDenominator u v p

/-- P-005A, with `(lambdaSeq, lambda)` fixed before the entire weight and
endpoint family.  There is no selected witness, so all payload fields are
uniform in `u`, `v`, `Ksh`, and `X`. -/
@[expose] def P005AStatement : Prop :=
  ∀ lambdaSeq : ℕ → ℝ, (∀ i : ℕ, 0 ≤ lambdaSeq i) →
  ∀ lambda : ℝ, 0 ≤ lambda → lambda < 2 →
    ∀ u v : ArithmeticWeight,
      NonnegativeMultiplicativeWeight u →
      NonnegativeMultiplicativeWeight v →
      ShiftedGeometricBounds u v lambdaSeq lambda →
      ∀ Ksh : PosNat, ∀ X : ℝ, 2 ≤ X →
        P005ASummabilityPayload u v Ksh X

@[expose] def shiftedMean (u v : ArithmeticWeight) (Ksh : PosNat) (X : ℝ) : ℝ :=
  ∑ n ∈ positiveNatsBelow X, u (Ksh.1 * n) * v n

@[expose] def exactShiftFactor (u v : ArithmeticWeight) (p i : ℕ) : ℝ :=
  localShift u v p i

@[expose] def shiftedPrimeProduct
    (u v : ArithmeticWeight) (Ksh : PosNat) (X : ℝ) : ℝ :=
  (∏ p ∈ Ksh.1.primeFactors,
      if (p : ℝ) < X then exactShiftFactor u v p (Ksh.1.factorization p)
      else 1) *
    (∏ p ∈ Ksh.1.primeFactors,
      if X ≤ (p : ℝ) then u (p ^ Ksh.1.factorization p) else 1)

structure P005Output (lambdaSeq : ℕ → ℝ) (lambda : ℝ) where
  constant : ℝ
  constant_pos : 0 < constant
  bound : ∀ u v : ArithmeticWeight,
    NonnegativeMultiplicativeWeight u →
    NonnegativeMultiplicativeWeight v →
    ShiftedGeometricBounds u v lambdaSeq lambda →
    ∀ Ksh : PosNat, ∀ X : ℝ, 2 ≤ X →
    shiftedMean u v Ksh X ≤
      constant * shiftedPrimeProduct u v Ksh X * (X / Real.log X) *
        (∏ p ∈ strictPrimeRange X, localEulerSeries u v p)

@[expose] def P005Statement : Prop :=
  ∀ lambdaSeq : ℕ → ℝ, (∀ i : ℕ, 0 ≤ lambdaSeq i) →
  ∀ lambda : ℝ, 0 ≤ lambda → lambda < 2 →
    Nonempty (P005Output lambdaSeq lambda)

/-! ## P-006--P-008: exact local-factor products -/

structure P006Output (r : ℕ → ℝ) where
  P0 : ℝ
  lower : ℝ
  upper : ℝ
  P0_ge_two : 2 ≤ P0
  lower_pos : 0 < lower
  upper_pos : 0 < upper
  uniform_bounds : ∀ B : ℝ, P0 < B →
    lower ≤ primeIntervalProduct (fun p => 1 + r p) P0 B ∧
      primeIntervalProduct (fun p => 1 + r p) P0 B ≤ upper

@[expose] def P006Statement : Prop :=
  ∀ C eta : ℝ, 0 < C → 0 < eta →
    ∀ r : ℕ → ℝ,
      (∀ p : ℕ, p.Prime → |r p| ≤ C * (p : ℝ).rpow (-1 - eta)) →
      (∀ p : ℕ, p.Prime → 0 < 1 + r p) →
      Nonempty (P006Output r)

@[expose] def mertensLE (t : ℝ) : ℝ :=
  ∏ p ∈ (positiveNatsBelow (t + 1)).filter fun (p : ℕ) =>
      (p : ℝ) ≤ t ∧ p.Prime,
    mertensFactor p

@[expose] def mertensEndpointFactor (t : ℝ) : ℝ :=
  ∏ p ∈ (strictPrimeRange (t + 1)).filter fun (p : ℕ) => (p : ℝ) = t,
    mertensFactor p

@[expose] def P006AStatement : Prop :=
  (∀ t : ℝ, 2 ≤ t →
    mertensStrictProduct t = mertensLE t / mertensEndpointFactor t) ∧
  (∀ A B c : ℝ, 2 ≤ A → A < B →
    (primeIntervalProduct mertensFactor A B).rpow (-c) =
        (mertensStrictProduct B / mertensStrictProduct A).rpow (-c) ∧
    (mertensStrictProduct B / mertensStrictProduct A).rpow (-c) =
        (mertensLE B * mertensEndpointFactor A /
          (mertensLE A * mertensEndpointFactor B)).rpow (-c)) ∧
  (∀ P0 A B : ℝ, 2 ≤ P0 → 2 ≤ A → 2 ≤ B → ∀ L : ℕ → ℝ,
    (∀ p : ℕ, p.Prime → 0 < L p) →
    primeIntervalProduct L A B =
      primeIntervalProduct L A (min B P0) *
        primeIntervalProduct L (max A P0) B) ∧
  (∀ A B : ℝ, B ≤ A → ∀ L : ℕ → ℝ,
    primeIntervalProduct L A B = 1)

structure P007Output (L : ℕ → ℝ) (c : ℝ) where
  P_err : ℝ
  comparison : PositiveComparison
  P_err_ge_two : 2 ≤ P_err
  interval_bounds : ∀ A B : ℝ, 2 ≤ A → A < B →
    comparison.lower * (Real.log B / Real.log A).rpow c ≤
        primeIntervalProduct L A B ∧
      primeIntervalProduct L A B ≤
        comparison.upper * (Real.log B / Real.log A).rpow c
  empty_branch : ∀ A B : ℝ, 2 ≤ A → 2 ≤ B → B ≤ A →
    primeIntervalProduct L A B = 1

@[expose] def P007Statement : Prop :=
  ∀ c eta C_err : ℝ, 0 < eta → 0 < C_err →
    ∀ L : ℕ → ℝ,
      (∀ p : ℕ, p.Prime → 0 < L p) →
      (∀ p : ℕ, p.Prime → 2 ≤ p →
        |L p - (1 + c / p)| ≤ C_err * (p : ℝ).rpow (-1 - eta)) →
      Nonempty (P007Output L c)

structure P008Output {Q : Type*} (c : Q → ℝ) (L : Q → ℕ → ℝ) where
  comparison : PositiveComparison
  family_bounds : ∀ q : Q, ∀ A B : ℝ, 2 ≤ A → A < B →
    comparison.lower * (Real.log B / Real.log A).rpow (c q) ≤
        primeIntervalProduct (L q) A B ∧
      primeIntervalProduct (L q) A B ≤
        comparison.upper * (Real.log B / Real.log A).rpow (c q)
  empty_branch : ∀ q : Q, ∀ A B : ℝ, 2 ≤ A → 2 ≤ B → B ≤ A →
    primeIntervalProduct (L q) A B = 1

/-- Uniform comparison requires a uniform floor, not pointwise positivity.
`mFin` bounds every prime uniformly over `q`; the finite-prefix upper bound
and the uniform tail error then control every prime. Merely changing the old
prefix endpoint from `< P0` to `≤ P0` is insufficient (see CURRENT.md W1).
This strengthens an auxiliary premise only; the final target is unchanged. -/
@[expose] def P008Statement : Prop :=
  ∀ Q : Type*, Nonempty Q →
    ∀ cMinus cPlus : ℝ, cMinus ≤ cPlus → 0 < 1 + cMinus / 2 →
    ∀ etaStar C_errStar : ℝ, 0 < etaStar → 0 < C_errStar →
    ∀ P0 mFin MFin : ℝ, 2 ≤ P0 → 0 < mFin → mFin ≤ MFin →
    ∀ c : Q → ℝ, (∀ q : Q, cMinus ≤ c q ∧ c q ≤ cPlus) →
    ∀ L : Q → ℕ → ℝ, (∀ q : Q, ∀ p : ℕ, p.Prime → mFin ≤ L q p) →
      (∀ q : Q, ∀ p : ℕ, p.Prime → P0 ≤ p →
        |L q p - (1 + c q / p)| ≤
          C_errStar * (p : ℝ).rpow (-1 - etaStar)) →
      (∀ q : Q, ∀ p : ℕ, p.Prime → 2 ≤ p → (p : ℝ) < P0 →
        mFin ≤ L q p ∧ L q p ≤ MFin) →
      Nonempty (P008Output c L)

/-! ## P-010--P-020: Lemma-4 witness chain -/

@[expose] def momentWeight (q : MomentParameters) : ArithmeticWeight := fun n =>
  if hn : 0 < n then moment q ⟨n, hn⟩ else 0

@[expose] def P010Statement : Prop :=
  ∀ q : MomentParameters,
    NonnegativeMultiplicativeWeight (momentWeight q) ∧
    ∀ p nu : ℕ, ∀ hp : p.Prime, 1 ≤ nu →
      let pp : PosNat := ⟨p ^ nu, Nat.pow_pos hp.pos⟩
      let value := moment q pp
      (value = if (p : ℝ) < q.theta then 0
        else if (p : ℝ) < q.sigma then 1
        else if (p : ℝ) < q.u then
          (1 / (nu + 1 : ℕ)) * ∑ j ∈ Finset.range (nu + 1), q.y ^ j
        else 1) ∧
      0 ≤ value ∧ value ≤ (max 1 q.y) ^ nu

@[expose] def CompactMomentDomain (Y : Set ℝ) : Prop :=
  Y.Nonempty ∧ IsCompact Y ∧ Y ⊆ Set.Ioo 0 2

@[expose] def lambdaOfFamily (Y : Set ℝ) : ℝ := max 1 (sSup Y)

@[expose] def localFamilyConstant (Y : Set ℝ) : ℝ :=
  4 + 2 * lambdaOfFamily Y ^ 2 / (2 - lambdaOfFamily Y)

structure P011Output (Y : Set ℝ) (hY : CompactMomentDomain Y) where
  C_Y : ℝ
  C_Y_pos : 0 < C_Y
  lambda_lt_two : lambdaOfFamily Y < 2
  local_constant_pos : 0 < localFamilyConstant Y
  bound : ∀ y : ℝ, ∀ hy : y ∈ Y,
    ∀ theta sigma u x : ℝ,
      ∀ htheta : 2 ≤ theta, ∀ hsigma : theta ≤ sigma,
      ∀ hu : sigma < u, u ≤ x → 2 ≤ x →
      let q : MomentParameters :=
        { y := y, y_pos := (hY.2.2 hy).1,
          y_lt_two := (hY.2.2 hy).2,
          theta := theta, theta_ge_two := htheta,
          sigma := sigma, sigma_ge_theta := hsigma,
          u := u, u_gt_sigma := hu }
      strictMean (momentWeight q) x ≤
        C_Y * x * roughDensity theta *
          (Real.log u / Real.log sigma).rpow ((y - 1) / 2)

@[expose] def P011Statement : Prop :=
  ∀ Y : Set ℝ, ∀ hY : CompactMomentDomain Y,
    Nonempty (P011Output Y hY)

@[expose] def upperTailCount (q : MomentParameters) (n : PosNat) : ℕ :=
  ((divisorSet n).filter fun d =>
    roughIndicator d q.sigma = 1 ∧
      (q.y / 2) * Real.log (Real.log q.u / Real.log q.sigma) <
        omegaBelowRaw d q.u).card

@[expose] def lowerTailCount (q : MomentParameters) (n : PosNat) : ℕ :=
  ((divisorSet n).filter fun d =>
    roughIndicator d q.sigma = 1 ∧
      (omegaBelowRaw d q.u : ℝ) <
        (q.y / 2) * Real.log (Real.log q.u / Real.log q.sigma)).card

@[expose] def tailPointSubject
    (upper : Bool) (q : MomentParameters) (n : PosNat) : ℝ :=
  (roughIndicator n.1 q.theta : ℝ) / roughTau n q.sigma *
    (if upper then upperTailCount q n else lowerTailCount q n)

@[expose] def tailMeanSubject
    (upper : Bool) (q : MomentParameters) (x : ℝ) : ℝ :=
  ∑ n ∈ positiveNatsBelow x,
    if hn : 0 < n then tailPointSubject upper q ⟨n, hn⟩ else 0

structure TailOutput
    (upper : Bool) (y : ℝ) (y_pos : 0 < y) (y_lt_two : y < 2) where
  C_y : ℝ
  C_y_pos : 0 < C_y
  bound : ∀ theta sigma u x : ℝ,
    ∀ htheta : 2 ≤ theta, ∀ hsigma : theta ≤ sigma,
    ∀ hu : sigma < u, u ≤ x → 2 ≤ x →
    let q : MomentParameters :=
      { y := y, y_pos := y_pos, y_lt_two := y_lt_two,
        theta := theta, theta_ge_two := htheta,
        sigma := sigma, sigma_ge_theta := hsigma,
        u := u, u_gt_sigma := hu }
    let R := Real.log u / Real.log sigma
    (∀ n : PosNat,
      tailPointSubject upper q n ≤
        moment q n * R.rpow (-(y / 2) * Real.log y)) ∧
    tailMeanSubject upper q x ≤
      C_y * x * roughDensity theta *
        R.rpow ((y - 1 - y * Real.log y) / 2)

@[expose] def P012Statement : Prop :=
  ∀ y : ℝ, ∀ hy : 1 < y, ∀ hy2 : y < 2,
    Nonempty (TailOutput true y (lt_trans zero_lt_one hy) hy2)

@[expose] def P013Statement : Prop :=
  ∀ y : ℝ, ∀ hy : 0 < y, ∀ hy1 : y < 1,
    Nonempty (TailOutput false y hy (lt_trans hy1 one_lt_two))

@[expose] def P014Statement : Prop :=
  ∀ epsilonInt : ℝ, 0 < epsilonInt → epsilonInt ≤ 1 / 10 →
    let t := 1.96 * epsilonInt
    t - (1 + t) * Real.log (1 + t) ≤ -1.802 * epsilonInt ^ 2

@[expose] def P015Statement : Prop :=
  ∀ epsilonInt : ℝ, 0 < epsilonInt → epsilonInt ≤ 1 / 10 →
    let t := 1.96 * epsilonInt
    (-t) - (1 - t) * Real.log (1 - t) ≤ -1.802 * epsilonInt ^ 2

@[expose] def makeGridParameters
    (epsilonInt : ℝ) (epsilonInt_pos : 0 < epsilonInt)
    (epsilonInt_le_tenth : epsilonInt ≤ 1 / 10)
    (Cgrid : ℝ) (Cgrid_pos : 0 < Cgrid) : GridParameters :=
  { epsilonInt := epsilonInt, epsilonInt_pos := epsilonInt_pos,
    epsilonInt_le_tenth := epsilonInt_le_tenth,
    Cgrid := Cgrid, Cgrid_pos := Cgrid_pos }

structure P016Output
    (epsilonInt : ℝ) (epsilonInt_pos : 0 < epsilonInt)
    (epsilonInt_le_tenth : epsilonInt ≤ 1 / 10) where
  Cgrid : ℝ
  Cgrid_pos : 0 < Cgrid
  grid_bound : GridBound
    (makeGridParameters epsilonInt epsilonInt_pos epsilonInt_le_tenth
      Cgrid Cgrid_pos)

@[expose] def P016Statement : Prop :=
  ∀ epsilonInt : ℝ, ∀ hpos : 0 < epsilonInt,
    ∀ hle : epsilonInt ≤ 1 / 10,
      Nonempty (P016Output epsilonInt hpos hle)

structure P017Output (q : GridParameters) where
  Xi0 : ℝ
  Xi0_gt_one : 1 < Xi0
  threshold_spec : ThresholdSpec q Xi0

@[expose] def P017Statement : Prop :=
  ∀ q : GridParameters, Nonempty (P017Output q)

@[expose] def badDivisorCount (goodQ : GoodParameters) (n : PosNat) : ℕ :=
  (@Finset.filter ℕ
      (fun d => roughIndicator d goodQ.sigma = 1 ∧
        if hd : 0 < d then ¬ Good goodQ n ⟨d, hd⟩ else False)
      (fun d => Classical.propDecidable _) (divisorSet n)).card

@[expose] def badDivisorMass
    (goodQ : GoodParameters) (theta x : ℝ) : ℝ :=
  ∑ n ∈ positiveNatsBelow x,
    if hn : 0 < n then
      (roughIndicator n theta : ℝ) / roughTau ⟨n, hn⟩ goodQ.sigma *
        badDivisorCount goodQ ⟨n, hn⟩
    else 0

@[expose] def makeGoodParameters
    (epsilonInt : ℝ) (epsilonInt_pos : 0 < epsilonInt)
    (epsilonInt_le_tenth : epsilonInt ≤ 1 / 10)
    (xi : ℝ) (xi_gt_one : 1 < xi)
    (sigma : ℝ) (sigma_ge_two : 2 ≤ sigma) : GoodParameters :=
  { epsilonInt := epsilonInt, epsilonInt_pos := epsilonInt_pos,
    epsilonInt_le_tenth := epsilonInt_le_tenth,
    xi := xi, xi_gt_one := xi_gt_one,
    sigma := sigma, sigma_ge_two := sigma_ge_two }

structure P018Output
    (epsilonInt : ℝ) (epsilonInt_pos : 0 < epsilonInt)
    (epsilonInt_le_tenth : epsilonInt ≤ 1 / 10) where
  Cgrid : ℝ
  Cgrid_pos : 0 < Cgrid
  grid_bound : GridBound
    (makeGridParameters epsilonInt epsilonInt_pos epsilonInt_le_tenth
      Cgrid Cgrid_pos)
  Xi0 : ℝ
  Xi0_gt_one : 1 < Xi0
  threshold_spec : ThresholdSpec
    (makeGridParameters epsilonInt epsilonInt_pos epsilonInt_le_tenth
      Cgrid Cgrid_pos) Xi0
  all_u_bound : ∀ xi sigma theta x : ℝ,
    ∀ hxi : Xi0 ≤ xi, ∀ htheta : 2 ≤ theta,
    ∀ hsigma : theta ≤ sigma, gridU0 xi sigma < x →
      badDivisorMass
          (makeGoodParameters epsilonInt epsilonInt_pos epsilonInt_le_tenth
            xi (lt_of_lt_of_le Xi0_gt_one hxi) sigma (le_trans htheta hsigma))
          theta x ≤
        (1 / 10 : ℝ) * x * roughDensity theta *
          (Real.log xi).rpow (-0.9 * epsilonInt ^ 2)

@[expose] def P018Statement : Prop :=
  ∀ epsilonInt : ℝ, ∀ hpos : 0 < epsilonInt,
    ∀ hle : epsilonInt ≤ 1 / 10,
      Nonempty (P018Output epsilonInt hpos hle)

@[expose] def roughNumberSet (theta : ℝ) : Set ℕ :=
  {n | 0 < n ∧ IsRough n theta}

@[expose] def P019Statement : Prop :=
  ∀ theta : ℝ, 2 ≤ theta →
    HasNaturalDensity (roughNumberSet theta) (roughDensity theta)

@[expose] def makeLemma4Parameters
    (epsilonInt : ℝ) (epsilonInt_pos : 0 < epsilonInt)
    (epsilonInt_le_tenth : epsilonInt ≤ 1 / 10)
    (xi : ℝ) (xi_gt_one : 1 < xi)
    (sigma theta : ℝ) (theta_ge_two : 2 ≤ theta)
    (sigma_ge_theta : theta ≤ sigma) : Lemma4Parameters :=
  { epsilonInt := epsilonInt, epsilonInt_pos := epsilonInt_pos,
    epsilonInt_le_tenth := epsilonInt_le_tenth,
    xi := xi, xi_gt_one := xi_gt_one,
    sigma := sigma, sigma_ge_two := le_trans theta_ge_two sigma_ge_theta,
    theta := theta, theta_ge_two := theta_ge_two,
    sigma_ge_theta := sigma_ge_theta }

structure P020Output
    (epsilonInt : ℝ) (epsilonInt_pos : 0 < epsilonInt)
    (epsilonInt_le_tenth : epsilonInt ≤ 1 / 10) where
  Cgrid : ℝ
  Cgrid_pos : 0 < Cgrid
  Xi0 : ℝ
  Xi0_gt_one : 1 < Xi0
  grid_bound : GridBound
    (makeGridParameters epsilonInt epsilonInt_pos epsilonInt_le_tenth
      Cgrid Cgrid_pos)
  threshold_spec : ThresholdSpec
    (makeGridParameters epsilonInt epsilonInt_pos epsilonInt_le_tenth
      Cgrid Cgrid_pos) Xi0
  witness : ∀ xi sigma theta : ℝ,
    ∀ hxi : Xi0 ≤ xi, ∀ htheta : 2 ≤ theta,
    ∀ hsigma : theta ≤ sigma,
    ∃ A : Set ℕ,
      L4Spec
        (makeLemma4Parameters epsilonInt epsilonInt_pos epsilonInt_le_tenth
          xi (lt_of_lt_of_le Xi0_gt_one hxi) sigma theta
          htheta hsigma) A

@[expose] def P020Statement : Prop :=
  ∀ epsilonInt : ℝ, ∀ hpos : 0 < epsilonInt,
    ∀ hle : epsilonInt ≤ 1 / 10,
      Nonempty (P020Output epsilonInt hpos hle)

end

end Erdos448.Stage4.Contracts

/-! ## Binder-faithful lowering interfaces: late P-020 closure

These declarations intentionally expose the fixed-binder existential closure
used by the late S3 derivation. It is not definitionally identified with the
closed `P020Statement`, whose `Cgrid` and `Xi0` witnesses are selected before
`xi`, `sigma`, and `theta`.
-/

@[expose] def Erdos448.Stage4.Typed.I_D_S45_EPS_DOMAIN
    (epsilonInt : ℝ) : Prop :=
  0 < epsilonInt ∧ epsilonInt ≤ 1 / 10

@[expose] def Erdos448.Stage4.Typed.I_D_S45_P020_DOMAIN
    (epsilonInt xi sigma theta : ℝ) : Prop :=
  0 < epsilonInt ∧ epsilonInt ≤ 1 / 10 ∧
    1 < xi ∧ 2 ≤ theta ∧ theta ≤ sigma

@[expose] def Erdos448.Stage4.Typed.I_D_S45_P020_L4SPEC
    (epsilonInt xi sigma theta Cgrid Xi0 : ℝ)
    (A : Set ℕ) : Prop :=
  ∃ (hepsilonPos : 0 < epsilonInt)
    (hepsilonLe : epsilonInt ≤ 1 / 10)
    (hCgrid : 0 < Cgrid) (hXi0 : 1 < Xi0)
    (hxi : Xi0 ≤ xi) (htheta : 2 ≤ theta) (hsigma : theta ≤ sigma),
      Erdos448.Stage4.GridBound
          (Erdos448.Stage4.Contracts.makeGridParameters
            epsilonInt hepsilonPos hepsilonLe Cgrid hCgrid) ∧
        Erdos448.Stage4.ThresholdSpec
          (Erdos448.Stage4.Contracts.makeGridParameters
            epsilonInt hepsilonPos hepsilonLe Cgrid hCgrid) Xi0 ∧
        Erdos448.Stage4.L4Spec
          (Erdos448.Stage4.Contracts.makeLemma4Parameters
            epsilonInt hepsilonPos hepsilonLe xi
            (lt_of_lt_of_le hXi0 hxi) sigma theta htheta hsigma) A

@[expose] abbrev Erdos448.Stage4.Typed.I_D_LATE_P020_W
    (_epsilonInt _xi _sigma _theta : ℝ) :=
  ℝ × ℝ × Set ℕ

@[expose] def Erdos448.Stage4.Typed.I_D_LATE_P020_EXISTS
    (epsilonInt xi sigma theta : ℝ) : Prop :=
  ∃ Cgrid Xi0 : ℝ, ∃ A : Set ℕ,
    Erdos448.Stage4.Typed.I_D_S45_P020_L4SPEC
      epsilonInt xi sigma theta Cgrid Xi0 A

@[expose] def Erdos448.Stage4.Typed.I_A_LATE_P020_EXISTS : Prop :=
  ∀ epsilonInt xi sigma theta : ℝ,
    Erdos448.Stage4.Typed.I_D_S45_P020_DOMAIN
        epsilonInt xi sigma theta →
      Erdos448.Stage4.Typed.I_D_S45_EPS_DOMAIN epsilonInt →
      Erdos448.Stage4.Typed.I_D_LATE_P020_EXISTS
        epsilonInt xi sigma theta

@[expose] def Erdos448.Stage4.Typed.I_D_S45_EXT001_DOMAIN
    (h : Erdos448.Stage4.ArithmeticWeight)
    (lambda1 lambda2 X : ℝ) : Prop :=
  Erdos448.Stage4.NonnegativeMultiplicativeWeight h ∧
    Erdos448.Stage4.Contracts.PrimePowerGeometricBound h lambda1 lambda2 ∧
    0 ≤ lambda1 ∧ 0 ≤ lambda2 ∧ lambda2 < 2 ∧ 2 ≤ X

@[expose] def Erdos448.Stage4.Typed.I_D_S45_EXT001_MEAN_BOUND
    (h : Erdos448.Stage4.ArithmeticWeight)
    (_lambda1 _lambda2 X Cext : ℝ) : Prop :=
  Erdos448.Stage4.Contracts.strictMean h X ≤
    Cext * (X / Real.log X) *
      Erdos448.Stage4.Contracts.strictEulerProduct h X

@[expose] def Erdos448.Stage4.Typed.I_D_S45_EXT001_EXISTS
    (h : Erdos448.Stage4.ArithmeticWeight)
    (lambda1 lambda2 X : ℝ) : Prop :=
  ∃ Cext : ℝ, 0 < Cext ∧
    Erdos448.Stage4.Typed.I_D_S45_EXT001_MEAN_BOUND
      h lambda1 lambda2 X Cext

@[expose] def Erdos448.Stage4.Typed.I_A_S45_EXT001_EXISTS : Prop :=
  ∀ (h : Erdos448.Stage4.ArithmeticWeight) (lambda1 lambda2 X : ℝ),
    Erdos448.Stage4.NonnegativeMultiplicativeWeight h →
    Erdos448.Stage4.Contracts.PrimePowerGeometricBound h lambda1 lambda2 →
    0 ≤ lambda1 → (0 ≤ lambda2 ∧ lambda2 < 2) → 2 ≤ X →
      Erdos448.Stage4.Typed.I_D_S45_EXT001_EXISTS h lambda1 lambda2 X

@[expose] def Erdos448.Stage4.Typed.I_D_S45_P006_DOMAIN
    (Cerr eta : ℝ) (r : ℕ → ℝ) : Prop :=
  0 < Cerr ∧ 0 < eta ∧
    (∀ p : ℕ, p.Prime →
      |r p| ≤ Cerr * (p : ℝ).rpow (-1 - eta)) ∧
    ∀ p : ℕ, p.Prime → 0 < 1 + r p

@[expose] def Erdos448.Stage4.Typed.I_D_S45_P006_PRODUCT_BOUNDS
    (_Cerr _eta : ℝ) (r : ℕ → ℝ)
    (P0 Cminus Cplus : ℝ) : Prop :=
  2 ≤ P0 ∧ 0 < Cminus ∧ 0 < Cplus ∧
    ∀ B : ℝ, P0 < B →
      Cminus ≤ Erdos448.Stage4.Contracts.primeIntervalProduct
          (fun p => 1 + r p) P0 B ∧
        Erdos448.Stage4.Contracts.primeIntervalProduct
            (fun p => 1 + r p) P0 B ≤ Cplus

@[expose] def Erdos448.Stage4.Typed.I_D_S45_P006_EXISTS
    (Cerr eta : ℝ) (r : ℕ → ℝ) : Prop :=
  ∃ P0 Cminus Cplus : ℝ,
    Erdos448.Stage4.Typed.I_D_S45_P006_PRODUCT_BOUNDS
      Cerr eta r P0 Cminus Cplus

@[expose] def Erdos448.Stage4.Typed.I_A_S45_P006_EXISTS : Prop :=
  ∀ Cerr eta : ℝ, ∀ r : ℕ → ℝ,
    Erdos448.Stage4.Typed.I_D_S45_P006_DOMAIN Cerr eta r →
      Erdos448.Stage4.Typed.I_D_S45_P006_EXISTS Cerr eta r

@[expose] def Erdos448.Stage4.Typed.I_D_S45_P007_DOMAIN
    (c eta Cerr : ℝ) (L : ℕ → ℝ) : Prop :=
  0 < eta ∧ 0 < Cerr ∧
    (∀ p : ℕ, p.Prime → 0 < L p) ∧
    ∀ p : ℕ, p.Prime → 2 ≤ p →
      |L p - (1 + c / p)| ≤ Cerr * (p : ℝ).rpow (-1 - eta)

@[expose] def Erdos448.Stage4.Typed.I_D_S45_P007_PRODUCT_COMPARISON
    (c _eta _Cerr : ℝ) (L : ℕ → ℝ)
    (Perr Cminus Cplus : ℝ) : Prop :=
  2 ≤ Perr ∧ 0 < Cminus ∧ 0 < Cplus ∧
    (∀ A B : ℝ, 2 ≤ A → A < B →
      Cminus * (Real.log B / Real.log A).rpow c ≤
          Erdos448.Stage4.Contracts.primeIntervalProduct L A B ∧
        Erdos448.Stage4.Contracts.primeIntervalProduct L A B ≤
          Cplus * (Real.log B / Real.log A).rpow c) ∧
    ∀ A B : ℝ, 2 ≤ A → 2 ≤ B → B ≤ A →
      Erdos448.Stage4.Contracts.primeIntervalProduct L A B = 1

@[expose] def Erdos448.Stage4.Typed.I_D_S45_P007_EXISTS
    (c eta Cerr : ℝ) (L : ℕ → ℝ) : Prop :=
  ∃ Perr Cminus Cplus : ℝ,
    Erdos448.Stage4.Typed.I_D_S45_P007_PRODUCT_COMPARISON
      c eta Cerr L Perr Cminus Cplus

@[expose] def Erdos448.Stage4.Typed.I_A_S45_P007_EXISTS : Prop :=
  ∀ c eta Cerr : ℝ, ∀ L : ℕ → ℝ,
    Erdos448.Stage4.Typed.I_D_S45_P007_DOMAIN c eta Cerr L →
      Erdos448.Stage4.Typed.I_D_S45_P007_EXISTS c eta Cerr L

@[expose] def Erdos448.Stage4.Typed.I_D_S45_P008_DOMAIN
    (Q : Type*) (cMinus cPlus etaStar CerrStar P0 mFin MFin : ℝ)
    (coeff : Q → ℝ) (localFactor : Q → ℕ → ℝ) : Prop :=
  Nonempty Q ∧ cMinus ≤ cPlus ∧ 0 < 1 + cMinus / 2 ∧
    0 < etaStar ∧ 0 < CerrStar ∧ 2 ≤ P0 ∧
    0 < mFin ∧ mFin ≤ MFin ∧
    (∀ q : Q, cMinus ≤ coeff q ∧ coeff q ≤ cPlus) ∧
    (∀ q : Q, ∀ p : ℕ, p.Prime → 0 < localFactor q p) ∧
    (∀ q : Q, ∀ p : ℕ, p.Prime → P0 ≤ p →
      |localFactor q p - (1 + coeff q / p)| ≤
        CerrStar * (p : ℝ).rpow (-1 - etaStar)) ∧
    ∀ q : Q, ∀ p : ℕ, p.Prime → 2 ≤ p → (p : ℝ) < P0 →
      mFin ≤ localFactor q p ∧ localFactor q p ≤ MFin

@[expose] def Erdos448.Stage4.Typed.I_D_S45_P008_FAMILY_COMPARISON
    (Q : Type*) (_cMinus _cPlus _etaStar _CerrStar _P0 _mFin _MFin : ℝ)
    (coeff : Q → ℝ) (localFactor : Q → ℕ → ℝ)
    (CfamilyMinus CfamilyPlus : ℝ) : Prop :=
  0 < CfamilyMinus ∧ 0 < CfamilyPlus ∧
    (∀ q : Q, ∀ A B : ℝ, 2 ≤ A → A < B →
      CfamilyMinus * (Real.log B / Real.log A).rpow (coeff q) ≤
          Erdos448.Stage4.Contracts.primeIntervalProduct
            (localFactor q) A B ∧
        Erdos448.Stage4.Contracts.primeIntervalProduct
            (localFactor q) A B ≤
          CfamilyPlus * (Real.log B / Real.log A).rpow (coeff q)) ∧
    ∀ q : Q, ∀ A B : ℝ, 2 ≤ A → 2 ≤ B → B ≤ A →
      Erdos448.Stage4.Contracts.primeIntervalProduct
        (localFactor q) A B = 1

@[expose] def Erdos448.Stage4.Typed.I_D_S45_P008_EXISTS
    (Q : Type*) (cMinus cPlus etaStar CerrStar P0 mFin MFin : ℝ)
    (coeff : Q → ℝ) (localFactor : Q → ℕ → ℝ) : Prop :=
  ∃ CfamilyMinus CfamilyPlus : ℝ,
    Erdos448.Stage4.Typed.I_D_S45_P008_FAMILY_COMPARISON
      Q cMinus cPlus etaStar CerrStar P0 mFin MFin coeff localFactor
      CfamilyMinus CfamilyPlus

@[expose] def Erdos448.Stage4.Typed.I_A_S45_P008_EXISTS : Prop :=
  ∀ (Q : Type*) (cMinus cPlus etaStar CerrStar P0 mFin MFin : ℝ),
    ∀ (coeff : Q → ℝ) (localFactor : Q → ℕ → ℝ),
      Erdos448.Stage4.Typed.I_D_S45_P008_DOMAIN
          Q cMinus cPlus etaStar CerrStar P0 mFin MFin coeff localFactor →
        Erdos448.Stage4.Typed.I_D_S45_P008_EXISTS
          Q cMinus cPlus etaStar CerrStar P0 mFin MFin coeff localFactor
