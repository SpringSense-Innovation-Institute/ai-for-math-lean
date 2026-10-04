module

import all Mathlib.Basic.Real.Basic
public import Erdos448.stage7.tasks.«ROOT-01».Components

public section

set_option backward.isDefEq.respectTransparency false

namespace Erdos448.Stage7.ROOT01

open Erdos448.Stage4
open Erdos448.Stage4.Contracts
open Finset Nat Set
open scoped BigOperators

noncomputable section

@[expose] def fullShiftCoefficient
    (u v : ArithmeticWeight) (Ksh : PosNat) (p j : ℕ) : ℝ :=
  u (p ^ (Ksh.1.factorization p + j)) * v (p ^ j) *
    (1 + (j : ℝ) * Real.log p) / (p : ℝ) ^ j

@[expose] def cutoffShiftCoefficient
    (u v : ArithmeticWeight) (Ksh : PosNat) (X : ℝ) (p j : ℕ) : ℝ :=
  if (p : ℝ) < X then fullShiftCoefficient u v Ksh p j
  else if j = 0 then u (p ^ Ksh.1.factorization p) else 0

lemma cutoffCoefficient_nonnegative
    (lambdaSeq : ℕ → ℝ) (lambda : ℝ)
    (u v : ArithmeticWeight) (hu : NonnegativeMultiplicativeWeight u)
    (hbounds : ShiftedGeometricBounds u v lambdaSeq lambda)
    (Ksh : PosNat) (X : ℝ) {p : ℕ} (hp : p.Prime) (j : ℕ) :
    0 ≤ cutoffShiftCoefficient u v Ksh X p j := by
  unfold cutoffShiftCoefficient fullShiftCoefficient
  split_ifs
  · exact div_nonneg
      (mul_nonneg (hbounds p hp (Ksh.1.factorization p) j).1
        (add_nonneg zero_le_one
          (mul_nonneg (Nat.cast_nonneg j) (Real.log_natCast_nonneg p))))
      (pow_nonneg (Nat.cast_nonneg p) j)
  · exact hu.nonnegative _ (pow_pos hp.pos _)
  · exact le_rfl

lemma cutoffCoefficient_summable
    (u v : ArithmeticWeight) (Ksh : PosNat) (X : ℝ)
    (hshifted : ∀ p : ℕ, p.Prime → ∀ i : ℕ,
      Summable (fun j : ℕ =>
        u (p ^ (i + j)) * v (p ^ j) * (1 + j * Real.log p) / (p : ℝ) ^ j))
    {p : ℕ} (hp : p.Prime) :
    Summable (cutoffShiftCoefficient u v Ksh X p) := by
  by_cases hpX : (p : ℝ) < X
  · apply (hshifted p hp (Ksh.1.factorization p)).congr
    intro j
    simp [cutoffShiftCoefficient, hpX, fullShiftCoefficient]
  · apply summable_of_ne_finset_zero (s := {0})
    intro j hj
    have hj0 : j ≠ 0 := by simpa using hj
    simp [cutoffShiftCoefficient, hpX, hj0]

lemma cutoffCoefficient_tsum
    (u v : ArithmeticWeight)
    (hu : NonnegativeMultiplicativeWeight u)
    (hv : NonnegativeMultiplicativeWeight v)
    (Ksh : PosNat) (X : ℝ) {p : ℕ} (hp : p.Prime) :
    (∑' j : ℕ, cutoffShiftCoefficient u v Ksh X p j) =
      if (p : ℝ) < X then shiftNumerator u v p (Ksh.1.factorization p)
      else u (p ^ Ksh.1.factorization p) := by
  by_cases hpX : (p : ℝ) < X
  · rw [if_pos hpX]
    simp only [cutoffShiftCoefficient, hpX, if_true, fullShiftCoefficient]
    rfl
  · rw [if_neg hpX]
    unfold cutoffShiftCoefficient
    simp only [hpX, if_false]
    rw [tsum_eq_single 0]
    · simp
    · intro j hj
      simp [hj]

lemma cutoff_eq_full_on_small_d
    (u v : ArithmeticWeight)
    (hu : NonnegativeMultiplicativeWeight u)
    (hv : NonnegativeMultiplicativeWeight v)
    (Ksh : PosNat) {X : ℝ} {d : ℕ} (hd : 0 < d) (hdX : (d : ℝ) < X)
    (hdSupport : d.primeFactors ⊆ Ksh.1.primeFactors) :
    localCoefficientProduct (cutoffShiftCoefficient u v Ksh X)
        Ksh.1.primeFactors d = enlargedShiftMajorant u v Ksh d := by
  have hdmem : d ∈ factoredNumbers Ksh.1.primeFactors :=
    mem_factoredNumbers_of_primeFactors_subset (Nat.ne_of_gt hd) hdSupport
  rw [← coefficient_eq_enlarged u v hu hv Ksh ⟨d, hdmem⟩]
  unfold localCoefficientProduct
  apply Finset.prod_congr rfl
  intro p hpK
  have hp := Nat.prime_of_mem_primeFactors hpK
  by_cases hpX : (p : ℝ) < X
  · simp [cutoffShiftCoefficient, hpX, fullShiftCoefficient]
  · have hpd : ¬p ∣ d := by
      intro hpd
      have hple : p ≤ d := Nat.le_of_dvd hd hpd
      exact hpX ((Nat.cast_le.mpr hple).trans_lt hdX)
    have hfac : d.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd hpd
    simp [cutoffShiftCoefficient, hpX, fullShiftCoefficient, hfac,
      hv.multiplicative.1]

lemma shiftedLogMean_eq
    (u v : ArithmeticWeight) (Ksh : PosNat) (X : ℝ) :
    shiftedLogMean u v Ksh X =
      Contracts.shiftedMean u v Ksh X * Real.log X := by
  unfold shiftedLogMean Contracts.shiftedMean
  rw [Finset.sum_mul]

lemma commonPrimeTerm_components
    (u v : ArithmeticWeight) (Ksh d : PosNat) (X : ℝ)
    (hdSupport : HasPrimeSupportIn d Ksh) :
    commonPrimeTerm u v Ksh X d.1 =
      u (Ksh.1 * d.1) * v d.1 *
        (firstLogComponent u v Ksh d X + secondLogComponent u v Ksh d X) := by
  unfold commonPrimeTerm firstLogComponent secondLogComponent coprimeInnerSum
  rw [dif_pos d.2, if_pos hdSupport]
  apply congrArg (fun z : ℝ => u (Ksh.1 * d.1) * v d.1 * z)
  rw [Finset.sum_mul, Finset.sum_mul]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m hm
  split_ifs <;> ring

lemma commonPrimeTerm_bound
    {lambda0 lambda : ℝ}
    (u v : ArithmeticWeight)
    (hu : NonnegativeMultiplicativeWeight u)
    (hv : NonnegativeMultiplicativeWeight v)
    (hsum : ∀ p : ℕ, p.Prime →
      Summable (fun j : ℕ => u (p ^ j) * v (p ^ j) / (p : ℝ) ^ j))
    (P2 : P002Output lambda0 lambda)
    (C : ℝ) (hP2C : P2.constant ≤ C) (hCOne : 1 ≤ C)
    (hfirst : ∀ Ksh d : PosNat, ∀ X : ℝ, 2 ≤ X → HasPrimeSupportIn d Ksh →
      firstLogComponent u v Ksh d X ≤
        P2.constant * (X / d.1) * localEulerProductAway u v Ksh X)
    (Ksh : PosNat) {X : ℝ} (hX : 2 ≤ X) {d : ℕ}
    (hdne : commonPrimeTerm u v Ksh X d ≠ 0) :
    commonPrimeTerm u v Ksh X d ≤
      C * X * localEulerProductAway u v Ksh X *
        localCoefficientProduct (cutoffShiftCoefficient u v Ksh X)
          Ksh.1.primeFactors d := by
  have hdData := exactOuterSupport u v Ksh X d hdne
  let dp : PosNat := ⟨d, hdData.1⟩
  have hdSupport : HasPrimeSupportIn dp Ksh := by
    unfold commonPrimeTerm at hdne
    split_ifs at hdne with hd hs
    · exact hs
    · contradiction
    · contradiction
  have hA : 0 ≤ u (Ksh.1 * d) * v d :=
    mul_nonneg (hu.nonnegative _ (Nat.mul_pos Ksh.2 hdData.1))
      (hv.nonnegative _ hdData.1)
  have hE : 0 ≤ localEulerProductAway u v Ksh X := by
    unfold localEulerProductAway
    exact Finset.prod_nonneg fun p hpS => by
      split_ifs
      · exact zero_le_one
      · unfold localEulerSeries
        exact tsum_nonneg fun j => div_nonneg
          (mul_nonneg (hu.nonnegative _ (pow_pos (mem_strictPrimeRange.mp hpS).1.pos j))
            (hv.nonnegative _ (pow_pos (mem_strictPrimeRange.mp hpS).1.pos j)))
          (pow_nonneg (Nat.cast_nonneg p) j)
  have hlogd : 0 ≤ Real.log d := Real.log_natCast_nonneg d
  have hsecond := p003 u v hu hv hsum Ksh dp X hX hdSupport
  have hfirst' := hfirst Ksh dp X hX hdSupport
  have hcomponents := commonPrimeTerm_components u v Ksh dp X hdSupport
  have hsumComp :
      firstLogComponent u v Ksh dp X + secondLogComponent u v Ksh dp X ≤
        (X / d) * localEulerProductAway u v Ksh X *
          (P2.constant + Real.log d) := by
    nlinarith
  have hlogFac := p004 dp
  have hCoeff := cutoff_eq_full_on_small_d u v hu hv Ksh hdData.1 hdData.2 hdSupport
  rw [hCoeff]
  rw [enlargedShiftMajorant, dif_pos hdData.1, if_pos hdSupport]
  rw [hcomponents]
  have hlogScale : Real.log d ≤ C * Real.log d :=
    le_mul_of_one_le_left hlogd hCOne
  have hClog : P2.constant + Real.log d ≤
      C * (1 + Real.log d) := by
    nlinarith
  calc
    u (Ksh.1 * d) * v d *
        (firstLogComponent u v Ksh dp X + secondLogComponent u v Ksh dp X) ≤
        u (Ksh.1 * d) * v d *
          ((X / d) * localEulerProductAway u v Ksh X *
            (P2.constant + Real.log d)) :=
      mul_le_mul_of_nonneg_left hsumComp hA
    _ ≤ u (Ksh.1 * d) * v d *
          ((X / d) * localEulerProductAway u v Ksh X *
            (C * (1 + Real.log d))) := by gcongr
    _ ≤ u (Ksh.1 * d) * v d *
          ((X / d) * localEulerProductAway u v Ksh X *
            (C * logarithmicPrimeFactorProduct dp)) := by gcongr
    _ = C * X * localEulerProductAway u v Ksh X *
          (u (Ksh.1 * d) * v d / (d : ℝ) *
            logarithmicPrimeFactorProduct dp) := by
      field_simp [Nat.ne_of_gt hdData.1]

lemma euler_shift_product_identity
    (u v : ArithmeticWeight)
    (hu : NonnegativeMultiplicativeWeight u)
    (hv : NonnegativeMultiplicativeWeight v)
    (hdenPos : ∀ p : ℕ, p.Prime → 0 < shiftDenominator u v p)
    (Ksh : PosNat) (X : ℝ) :
    localEulerProductAway u v Ksh X *
        (∏ p ∈ Ksh.1.primeFactors,
          if (p : ℝ) < X then shiftNumerator u v p (Ksh.1.factorization p)
          else u (p ^ Ksh.1.factorization p)) =
      shiftedPrimeProduct u v Ksh X *
        (∏ p ∈ strictPrimeRange X, localEulerSeries u v p) := by
  classical
  let S := strictPrimeRange X
  let KS : Finset ℕ := Ksh.1.primeFactors.filter fun p => (p : ℝ) < X
  have hKS : KS = S.filter fun p => p ∣ Ksh.1 := by
    ext p
    simp only [KS, S, Finset.mem_filter]
    constructor
    · rintro ⟨hpK, hpX⟩
      have hp := Nat.prime_of_mem_primeFactors hpK
      exact ⟨mem_strictPrimeRange.mpr ⟨hp, hpX⟩,
        Nat.dvd_of_mem_primeFactors hpK⟩
    · rintro ⟨hpS, hpK⟩
      exact ⟨Nat.mem_primeFactors.mpr
        ⟨(mem_strictPrimeRange.mp hpS).1, hpK, Nat.ne_of_gt Ksh.2⟩,
        (mem_strictPrimeRange.mp hpS).2⟩
  have hden :
      (∏ p ∈ Ksh.1.primeFactors,
        if (p : ℝ) < X then localEulerSeries u v p else 1) =
      ∏ p ∈ S.filter (fun p => p ∣ Ksh.1), localEulerSeries u v p := by
    rw [← hKS]
    simp [KS, Finset.prod_filter]
  have hfull :
      (∏ p ∈ S, localEulerSeries u v p) =
        localEulerProductAway u v Ksh X *
          ∏ p ∈ S.filter (fun p => p ∣ Ksh.1), localEulerSeries u v p := by
    unfold localEulerProductAway
    change (∏ p ∈ S, localEulerSeries u v p) =
      (∏ p ∈ S, if p ∣ Ksh.1 then 1 else localEulerSeries u v p) *
        ∏ p ∈ S.filter (fun p => p ∣ Ksh.1), localEulerSeries u v p
    rw [Finset.prod_ite]
    simp only [Finset.prod_const_one, one_mul]
    simpa only [not_not] using
      (Finset.prod_filter_mul_prod_filter_not S
        (fun p : ℕ => ¬p ∣ Ksh.1) (fun p => localEulerSeries u v p)).symm
  have hnumden :
      (∏ p ∈ Ksh.1.primeFactors,
          if (p : ℝ) < X then
            shiftNumerator u v p (Ksh.1.factorization p) /
              shiftDenominator u v p else 1) *
        (∏ p ∈ Ksh.1.primeFactors,
          if (p : ℝ) < X then localEulerSeries u v p else 1) =
        ∏ p ∈ Ksh.1.primeFactors,
          if (p : ℝ) < X then shiftNumerator u v p (Ksh.1.factorization p)
          else 1 := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro p hpK
    by_cases hpX : (p : ℝ) < X
    · simp only [hpX, if_true]
      rw [show localEulerSeries u v p = shiftDenominator u v p by rfl]
      exact div_mul_cancel₀ _
        (ne_of_gt (hdenPos p (Nat.prime_of_mem_primeFactors hpK)))
    · simp [hpX]
  have hsplitnum :
      (∏ p ∈ Ksh.1.primeFactors,
          if (p : ℝ) < X then shiftNumerator u v p (Ksh.1.factorization p)
          else u (p ^ Ksh.1.factorization p)) =
        (∏ p ∈ Ksh.1.primeFactors,
          if (p : ℝ) < X then shiftNumerator u v p (Ksh.1.factorization p)
          else 1) *
        (∏ p ∈ Ksh.1.primeFactors,
          if X ≤ (p : ℝ) then u (p ^ Ksh.1.factorization p) else 1) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro p hpK
    by_cases hpX : (p : ℝ) < X <;> simp [hpX, not_lt.mp]
  unfold shiftedPrimeProduct exactShiftFactor localShift
  rw [hfull, ← hden]
  rw [hsplitnum, ← hnumden]
  ring

theorem p005 (hEXT001 : EXT001Statement) : P005Statement := by
  intro lambdaSeq hlambdaSeq lambda hlambda hlt
  obtain ⟨P2⟩ := p002 hEXT001 (lambdaSeq 0) lambda (hlambdaSeq 0) hlambda hlt
  let C := max P2.constant 1
  refine ⟨{
    constant := C
    constant_pos := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
    bound := ?_
  }⟩
  intro u v hu hv hbounds Ksh X hX
  have hA := p005A hEXT001 lambdaSeq hlambdaSeq lambda hlambda hlt
    u v hu hv hbounds Ksh X hX
  have hP1 := p001 u v hu hv Ksh X hX hA.exact_outer_summable
  have hfirst := P2.bound u v hu hv lambdaSeq hlambdaSeq rfl hbounds
  have hP2C : P2.constant ≤ C := le_max_left _ _
  have hCOne : 1 ≤ C := le_max_right _ _
  let a := cutoffShiftCoefficient u v Ksh X
  have haNonneg : ∀ p ∈ Ksh.1.primeFactors, ∀ j : ℕ, 0 ≤ a p j := by
    intro p hpK j
    exact cutoffCoefficient_nonnegative lambdaSeq lambda u v hu hbounds Ksh X
      (Nat.prime_of_mem_primeFactors hpK) j
  have haSum : ∀ p ∈ Ksh.1.primeFactors, Summable (a p) := by
    intro p hpK
    exact cutoffCoefficient_summable u v Ksh X hA.shifted_local_summable
      (Nat.prime_of_mem_primeFactors hpK)
  have hexpand := finiteEulerExpansion a Ksh.1.primeFactors
    (fun p hp => Nat.prime_of_mem_primeFactors hp) haNonneg haSum
  let M : ℕ → ℝ :=
    (factoredNumbers Ksh.1.primeFactors).indicator
      (fun d => localCoefficientProduct a Ksh.1.primeFactors d)
  have hMsum : Summable M := by
    exact summable_subtype_iff_indicator.mp hexpand.1
  have hMtsum : (∑' d : ℕ, M d) =
      ∏ p ∈ Ksh.1.primeFactors,
        if (p : ℝ) < X then shiftNumerator u v p (Ksh.1.factorization p)
        else u (p ^ Ksh.1.factorization p) := by
    unfold M
    rw [← _root_.tsum_subtype, hexpand.2.tsum_eq]
    apply Finset.prod_congr rfl
    intro p hpK
    exact cutoffCoefficient_tsum u v hu hv Ksh X
      (Nat.prime_of_mem_primeFactors hpK)
  have hpoint : ∀ d : ℕ, commonPrimeTerm u v Ksh X d ≤
      C * X * localEulerProductAway u v Ksh X * M d := by
    intro d
    by_cases hd0 : commonPrimeTerm u v Ksh X d = 0
    · rw [hd0]
      exact mul_nonneg
        (mul_nonneg
          (mul_nonneg (lt_of_lt_of_le zero_lt_one hCOne).le
            (le_trans (by norm_num) hX))
          (by
            unfold localEulerProductAway
            exact Finset.prod_nonneg fun p hpS => by
              split_ifs
              · exact zero_le_one
              · unfold localEulerSeries
                exact tsum_nonneg fun j => div_nonneg
                  (mul_nonneg (hu.nonnegative _ (pow_pos (mem_strictPrimeRange.mp hpS).1.pos j))
                    (hv.nonnegative _ (pow_pos (mem_strictPrimeRange.mp hpS).1.pos j)))
                  (pow_nonneg (Nat.cast_nonneg p) j)))
        (by
          unfold M
          by_cases hdmem : d ∈ factoredNumbers Ksh.1.primeFactors
          · rw [Set.indicator_of_mem hdmem]
            exact Finset.prod_nonneg fun p hpK =>
              haNonneg p hpK (d.factorization p)
          · rw [Set.indicator_of_notMem hdmem])
    · have hb := commonPrimeTerm_bound u v hu hv hA.unshifted_local_summable
        P2 C hP2C hCOne hfirst Ksh hX hd0
      have hdData := exactOuterSupport u v Ksh X d hd0
      have hdSupport : d.primeFactors ⊆ Ksh.1.primeFactors := by
        unfold commonPrimeTerm at hd0
        split_ifs at hd0 with hd hs
        · exact hs
        · contradiction
        · contradiction
      have hdmem : d ∈ factoredNumbers Ksh.1.primeFactors :=
        mem_factoredNumbers_of_primeFactors_subset (Nat.ne_of_gt hdData.1) hdSupport
      unfold M
      rw [Set.indicator_of_mem hdmem]
      exact hb
  have hsumBound := Summable.tsum_le_tsum hpoint hA.exact_outer_summable
    (hMsum.mul_left (C * X * localEulerProductAway u v Ksh X))
  have hlogPos : 0 < Real.log X := Real.log_pos (lt_of_lt_of_le (by norm_num) hX)
  have hlogEq := shiftedLogMean_eq u v Ksh X
  rw [hlogEq] at hP1
  have hraw : shiftedMean u v Ksh X * Real.log X ≤
      C * X * localEulerProductAway u v Ksh X *
        (∏ p ∈ Ksh.1.primeFactors,
          if (p : ℝ) < X then shiftNumerator u v p (Ksh.1.factorization p)
          else u (p ^ Ksh.1.factorization p)) := by
    rw [hP1]
    calc
      (∑' d : ℕ, commonPrimeTerm u v Ksh X d) ≤
          ∑' d : ℕ, (C * X * localEulerProductAway u v Ksh X) * M d :=
        hsumBound
      _ = (C * X * localEulerProductAway u v Ksh X) * ∑' d, M d :=
        tsum_mul_left
      _ = _ := by rw [hMtsum]
  have hidentity := euler_shift_product_identity u v hu hv
    hA.shift_denominator_positive Ksh X
  have hraw' : Contracts.shiftedMean u v Ksh X * Real.log X ≤
      C * X * (shiftedPrimeProduct u v Ksh X *
        (∏ p ∈ strictPrimeRange X, localEulerSeries u v p)) := by
    calc
      Contracts.shiftedMean u v Ksh X * Real.log X ≤
          C * X * localEulerProductAway u v Ksh X *
            (∏ p ∈ Ksh.1.primeFactors,
              if (p : ℝ) < X then shiftNumerator u v p (Ksh.1.factorization p)
              else u (p ^ Ksh.1.factorization p)) := hraw
      _ = C * X * (localEulerProductAway u v Ksh X *
            (∏ p ∈ Ksh.1.primeFactors,
              if (p : ℝ) < X then shiftNumerator u v p (Ksh.1.factorization p)
              else u (p ^ Ksh.1.factorization p))) := by ring
      _ = _ := by rw [hidentity]
  have hquot :
      Contracts.shiftedMean u v Ksh X ≤
        (C * shiftedPrimeProduct u v Ksh X * X *
          (∏ p ∈ strictPrimeRange X, localEulerSeries u v p)) /
            Real.log X := by
    apply (le_div_iff₀ hlogPos).2
    convert hraw' using 1 <;> ring
  convert hquot using 1
  field_simp [ne_of_gt hlogPos]

end

end Erdos448.Stage7.ROOT01
