module

import all Mathlib.Basic.Real.Basic
public import Erdos448.stage7.tasks.«ROOT-06».MainNodes

public section

set_option backward.isDefEq.respectTransparency false

namespace Erdos448.Stage7.ROOT06.Smoothing

open Erdos448.Stage4
open Erdos448.Stage4.Contracts
open Erdos448.Stage7.ROOT06.EulerEngine
open Erdos448.Stage7.ROOT06.ShiftEngine
open Erdos448.Stage7.ROOT06.LogBounds
open Finset
open scoped BigOperators

noncomputable section

instance (p : Prop) : Decidable p := Classical.propDecidable p

theorem oneWeightSpec : ModifierSpec oneWeight := by
  refine ⟨?_, rfl, ?_⟩
  · constructor
    · intro n hn
      simp [oneWeight]
    · refine ⟨rfl, ?_⟩
      intro a b ha hb hab
      simp [oneWeight]
  · intro p hp j
    simp [oneWeight]

theorem a0GeometricBounds (W : CommonWeightWitnesses) :
    ShiftedGeometricBounds a0Weight oneWeight (fun _ => W.LambdaStar) 1 := by
  intro p hp i j
  have hw := W.weight_type regularBase.parameters .a0
  by_cases hij : i + j = 0
  · have hi : i = 0 := by omega
    have hj : j = 0 := by omega
    subst i
    subst j
    have hterm : 0 ≤ W.CStar * (2 : ℝ).rpow (-W.cStar) :=
      mul_nonneg W.CStar_pos.le (Real.rpow_nonneg (by norm_num) _)
    have hLam : 1 ≤ W.LambdaStar :=
      (by linarith : (1 : ℝ) ≤ 1 + W.CStar * (2 : ℝ).rpow (-W.cStar)) |>.trans
        W.LambdaStar_lower
    constructor
    · simpa [oneWeight, selectedWeight] using
        hw.nonnegative_multiplicative.nonnegative 1 (by omega)
    · have ha0one : a0Weight 1 = 1 := by
        simpa [selectedWeight] using hw.normalized
      simp [oneWeight, ha0one, hLam]
  · have hu := hw.prime_power_bounds p hp (i + j)
      (Nat.one_le_iff_ne_zero.mpr hij)
    constructor
    · simpa [oneWeight, selectedWeight] using hu.1
    · simpa [oneWeight, selectedWeight] using hu.2.trans (le_refl W.LambdaStar)

theorem a0EulerOutput (hP008 : P008Statement.{0}) (W : CommonWeightWitnesses)
    (h051H : P051HStatement) :
    Nonempty (P008Output (fun _ : Unit => (1 / 2 : ℝ))
      (fun _ p => localEulerFactor a0Weight oneWeight p)) := by
  have heta : 0 < min W.cStar 1 := lt_min W.cStar_pos zero_lt_one
  have hC : 0 < W.CStar + 2 * W.LambdaStar := by linarith [W.CStar_pos, W.LambdaStar_pos]
  apply hP008 Unit ⟨()⟩ (1 / 2) (1 / 2) le_rfl (by norm_num)
    (min W.cStar 1) (W.CStar + 2 * W.LambdaStar) heta hC
    2 1 1 le_rfl zero_lt_one le_rfl
    (fun _ : Unit => (1 / 2 : ℝ))
  · intro q
    exact ⟨le_rfl, le_rfl⟩
  · intro q p hp
    exact Erdos448.Stage7.Shared.localEulerFactor_ge_one hp
      (W.weight_type regularBase.parameters .a0).nonnegative_multiplicative
      (W.weight_type regularBase.parameters .a0).normalized oneWeightSpec
      (h051H W regularBase.parameters .a0 oneWeight oneWeightSpec p hp).domain.summable
  · intro q p hp _
    simpa [selectedWeight, oneWeight, div_eq_mul_inv, mul_assoc, mul_left_comm,
      mul_comm] using
      (h051H W regularBase.parameters .a0 oneWeight oneWeightSpec p hp).replaced_main_term
  · intro q p hp hp2 hplt
    exfalso
    exact (not_lt_of_ge (by exact_mod_cast hp2 : (2 : ℝ) ≤ p)) hplt

theorem positiveNatsBelow_eq_Ico {z : ℝ} :
    positiveNatsBelow z = Finset.Ico 1 (Nat.ceil z) := by
  ext n
  simp [positiveNatsBelow, Nat.lt_ceil, Nat.one_le_iff_ne_zero,
    Nat.pos_iff_ne_zero, and_left_comm, and_assoc]

theorem safeLog_monotone {m : ℕ} {z : ℝ}
    (hm : 0 < m) (hmz : (m : ℝ) < z) : safeLog m ≤ safeLog z := by
  unfold safeLog
  apply max_le_max_left
  exact Real.log_le_log (by exact_mod_cast hm) (le_of_lt hmz)

theorem safeLogHalfSum_lower {z : ℝ} (hz : 2 ≤ z) :
    z / 2 * (safeLog z).rpow (-1 / 2) ≤ safeLogHalfSum z := by
  have hsafe : 0 < safeLog z := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hpoint : ∀ m ∈ positiveNatsBelow z,
      (safeLog z).rpow (-1 / 2) ≤ (safeLog m).rpow (-1 / 2) := by
    intro m hm
    have hmdata := (Finset.mem_filter.mp hm).2
    have hmpos : 0 < safeLog m :=
      lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    exact (Real.rpow_le_rpow_iff_of_neg hsafe hmpos (by norm_num)).2
      (safeLog_monotone hmdata.1 hmdata.2)
  have hsum : (positiveNatsBelow z).card * (safeLog z).rpow (-1 / 2) ≤
      safeLogHalfSum z := by
    unfold safeLogHalfSum
    simpa [nsmul_eq_mul] using Finset.card_nsmul_le_sum
      (positiveNatsBelow z) (fun m : ℕ => (safeLog m).rpow (-1 / 2))
      ((safeLog z).rpow (-1 / 2)) hpoint
  have hcard : z / 2 ≤ ((positiveNatsBelow z).card : ℝ) := by
    rw [positiveNatsBelow_eq_Ico, Nat.card_Ico]
    have hceil : z ≤ (Nat.ceil z : ℝ) := Nat.le_ceil z
    have hceil2 : 2 ≤ Nat.ceil z := by exact_mod_cast hz.trans hceil
    have hcast : (((Nat.ceil z - 1 : ℕ) : ℕ) : ℝ) = (Nat.ceil z : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ Nat.ceil z)]
      norm_num
    rw [hcast]
    linarith
  exact (mul_le_mul_of_nonneg_right hcard (Real.rpow_nonneg hsafe.le _)).trans hsum

theorem reciprocal_eq_shifted (z : ℝ) (Ksh : PosNat) :
    reciprocalDivisorSum z Ksh = Contracts.shiftedMean a0Weight oneWeight Ksh z := by
  unfold reciprocalDivisorSum Contracts.shiftedMean oneWeight
  apply Finset.sum_congr rfl
  intro n hn
  simp [mul_comm]

theorem strict_product_eq_interval (z : ℝ) :
    (∏ p ∈ strictPrimeRange z, localEulerFactor a0Weight oneWeight p) =
      primeIntervalProduct (fun p => localEulerFactor a0Weight oneWeight p) 2 z := by
  unfold primeIntervalProduct
  apply Finset.prod_congr rfl
  intro p hp
  have hpprime := (Erdos448.Stage7.ROOT06.EulerEngine.mem_strictPrimeRange.mp hp).1
  simp [show (2 : ℝ) ≤ p by exact_mod_cast hpprime.two_le]

theorem p052 (hP001C : P001CStatement) (hP005 : P005Statement)
    (hP008 : P008Statement.{0}) (chain : WeightChainSpec)
    (W : CommonWeightWitnesses) (h051H : P051HStatement) : P052Statement := by
  obtain ⟨P⟩ := hP005 (fun _ => W.LambdaStar)
    (fun _ => W.LambdaStar_pos.le) 1 zero_le_one (by norm_num)
  obtain ⟨E⟩ := a0EulerOutput hP008 W h051H
  let EB : ℝ := max 1 E.comparison.upper
  have hEB : 1 ≤ EB := le_max_left _ _
  have hEupper : E.comparison.upper ≤ EB := le_max_right _ _
  intro theta htheta
  let Csm := max 1 (2 * P.constant * EB *
    (Real.log 2).rpow (-1 / 2) * logLoss)
  have hCsm : 0 < Csm := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨Csm, hCsm, ?_⟩
  intro q hq Ksh z hz
  by_cases hz2 : z < 2
  · have hrest : 0 ≤ w1Weight Ksh.1 * safeLogHalfSum z := by
      apply mul_nonneg
      · exact (W.weight_type q .w1).nonnegative_multiplicative.nonnegative Ksh.1 Ksh.2
      · unfold safeLogHalfSum
        exact Finset.sum_nonneg fun m hm => Real.rpow_nonneg
          (zero_le_one.trans (le_max_left _ _)) _
    calc
      reciprocalDivisorSum z Ksh ≤ w1Weight Ksh.1 * safeLogHalfSum z :=
        hP001C Ksh z hz hz2
      _ = 1 * (w1Weight Ksh.1 * safeLogHalfSum z) := by ring
      _ ≤ Csm * (w1Weight Ksh.1 * safeLogHalfSum z) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) hrest
      _ = Csm * w1Weight Ksh.1 * safeLogHalfSum z := by ring
  · have hz2' : 2 ≤ z := le_of_not_gt hz2
    have hraw := P.bound a0Weight oneWeight
      (W.weight_type regularBase.parameters .a0).nonnegative_multiplicative
      oneWeightSpec.nonnegative_multiplicative (a0GeometricBounds W) Ksh z hz2'
    have hshift := shiftedPrimeProduct_le_maxShift
      (W.weight_type regularBase.parameters .a0).nonnegative_multiplicative
      chain.w1_shift Ksh z
    have hlogz : 0 < Real.log z := Real.log_pos (one_lt_two.trans_le hz2')
    have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
    have hprod : primeIntervalProduct
        (fun p => localEulerFactor a0Weight oneWeight p) 2 z ≤
        EB * (Real.log z / Real.log 2).rpow (1 / 2) := by
      by_cases heq : z = 2
      · subst z
        rw [E.empty_branch () 2 2 le_rfl le_rfl le_rfl]
        have hratio : Real.log 2 / Real.log 2 = 1 := div_self hlog2.ne'
        rw [hratio]
        have hone : Real.rpow 1 (1 / 2 : ℝ) = 1 := Real.one_rpow _
        rw [hone, mul_one]
        exact hEB
      · exact ((E.family_bounds () 2 z le_rfl
          (lt_of_le_of_ne hz2' (Ne.symm heq))).2).trans
            (mul_le_mul_of_nonneg_right hEupper (Real.rpow_nonneg
              (div_nonneg hlogz.le hlog2.le) _))
    have hmean : reciprocalDivisorSum z Ksh ≤
        P.constant * w1Weight Ksh.1 * z *
          (Real.log z).rpow (-1 / 2) *
          EB * (Real.log 2).rpow (-1 / 2) := by
      rw [reciprocal_eq_shifted]
      have hw1 : 0 ≤ w1Weight Ksh.1 :=
        (W.weight_type regularBase.parameters .w1).nonnegative_multiplicative.nonnegative
          Ksh.1 Ksh.2
      have hdiv : 0 ≤ z / Real.log z := div_nonneg
        (zero_le_two.trans hz2') (Real.log_nonneg (one_le_two.trans hz2'))
      have heuler0 : 0 ≤ ∏ p ∈ strictPrimeRange z,
          localEulerSeries a0Weight oneWeight p := by
        apply Finset.prod_nonneg
        intro p hp
        have hprime := (Erdos448.Stage7.ROOT06.EulerEngine.mem_strictPrimeRange.mp hp).1
        exact (Erdos448.Stage7.Shared.localEulerFactor_ge_one hprime
          (W.weight_type regularBase.parameters .a0).nonnegative_multiplicative
          (W.weight_type regularBase.parameters .a0).normalized oneWeightSpec
          (h051H W regularBase.parameters .a0 oneWeight oneWeightSpec p hprime).domain.summable).trans'
            zero_le_one
      have hprod' : (∏ p ∈ strictPrimeRange z,
          localEulerSeries a0Weight oneWeight p) ≤
          EB * (Real.log z / Real.log 2).rpow (1 / 2) := by
        rw [show (∏ p ∈ strictPrimeRange z, localEulerSeries a0Weight oneWeight p) =
          ∏ p ∈ strictPrimeRange z, localEulerFactor a0Weight oneWeight p by
            rfl, strict_product_eq_interval]
        exact hprod
      have hratio : (Real.log z / Real.log 2).rpow (1 / 2 : ℝ) =
          (Real.log z).rpow (1 / 2 : ℝ) *
            (Real.log 2).rpow (-1 / 2 : ℝ) := by
        calc
          _ = (Real.log z).rpow (1 / 2 : ℝ) /
              (Real.log 2).rpow (1 / 2 : ℝ) := by
                simpa using Real.div_rpow hlogz.le hlog2.le (1 / 2 : ℝ)
          _ = _ := by
            rw [div_eq_mul_inv]
            congr 1
            symm
            simpa only [Real.rpow_eq_pow, show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by ring] using
              Real.rpow_neg hlog2.le (1 / 2 : ℝ)
      have hcombine : (Real.log z).rpow (-1 : ℝ) *
          (Real.log z).rpow (1 / 2 : ℝ) =
          (Real.log z).rpow (-1 / 2 : ℝ) := by
        calc
          _ = (Real.log z).rpow ((-1 : ℝ) + 1 / 2) := by
            simpa using (Real.rpow_add hlogz (-1 : ℝ) (1 / 2 : ℝ)).symm
          _ = _ := by norm_num
      calc
        Contracts.shiftedMean a0Weight oneWeight Ksh z ≤
            P.constant * shiftedPrimeProduct a0Weight oneWeight Ksh z *
              (z / Real.log z) *
              (∏ p ∈ strictPrimeRange z, localEulerSeries a0Weight oneWeight p) := hraw
        _ ≤ P.constant * w1Weight Ksh.1 * (z / Real.log z) *
              (∏ p ∈ strictPrimeRange z, localEulerSeries a0Weight oneWeight p) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (by simpa [selectedWeight, w1Weight] using hshift)
                P.constant_pos.le) hdiv) heuler0
        _ ≤ P.constant * w1Weight Ksh.1 * (z / Real.log z) *
              (EB *
                (Real.log z / Real.log 2).rpow (1 / 2)) := by
          exact mul_le_mul_of_nonneg_left hprod'
            (mul_nonneg (mul_nonneg P.constant_pos.le hw1) hdiv)
        _ = P.constant * w1Weight Ksh.1 * z *
              (Real.log z).rpow (-1 / 2) * EB *
              (Real.log 2).rpow (-1 / 2) := by
          rw [hratio, show z / Real.log z = z * (Real.log z)⁻¹ by ring,
            ← Real.rpow_neg_one (Real.log z)]
          calc
            P.constant * w1Weight Ksh.1 * (z * (Real.log z).rpow (-1)) *
                (EB * ((Real.log z).rpow (1 / 2) *
                  (Real.log 2).rpow (-1 / 2))) =
              P.constant * w1Weight Ksh.1 * z *
                ((Real.log z).rpow (-1) * (Real.log z).rpow (1 / 2)) *
                EB * (Real.log 2).rpow (-1 / 2) := by ring
            _ = _ := by rw [hcombine]
    have hlower := safeLogHalfSum_lower hz2'
    have hlogsafe := log_rpow_le_loss_safeLog hz2'
      (by norm_num : (-1 / 2 : ℝ) ≤ 0) (by norm_num : (-1 : ℝ) ≤ -1 / 2)
    have hcompare : z * (Real.log z).rpow (-1 / 2) ≤
        2 * logLoss * safeLogHalfSum z := by
      have hfirst := mul_le_mul_of_nonneg_left hlogsafe (zero_le_two.trans hz2')
      have hsafe0 : 0 ≤ (safeLog z).rpow (-1 / 2) :=
        Real.rpow_nonneg (zero_le_one.trans (le_max_left _ _)) _
      have hsum0 : 0 ≤ safeLogHalfSum z := by
        unfold safeLogHalfSum
        exact Finset.sum_nonneg fun m hm => Real.rpow_nonneg
          (zero_le_one.trans (le_max_left _ _)) _
      have hsecond : z * (safeLog z).rpow (-1 / 2) ≤ 2 * safeLogHalfSum z := by
        nlinarith [hlower]
      calc
        z * (Real.log z).rpow (-1 / 2) ≤
            z * (logLoss * (safeLog z).rpow (-1 / 2)) := hfirst
        _ = logLoss * (z * (safeLog z).rpow (-1 / 2)) := by ring
        _ ≤ logLoss * (2 * safeLogHalfSum z) :=
          mul_le_mul_of_nonneg_left hsecond logLoss_pos.le
        _ = 2 * logLoss * safeLogHalfSum z := by ring
    calc
      reciprocalDivisorSum z Ksh ≤ P.constant * w1Weight Ksh.1 * z *
          (Real.log z).rpow (-1 / 2) * EB *
          (Real.log 2).rpow (-1 / 2) := hmean
      _ ≤ (2 * P.constant * EB *
          (Real.log 2).rpow (-1 / 2) * logLoss) *
          w1Weight Ksh.1 * safeLogHalfSum z := by
            have hw1 := (W.weight_type q .w1).nonnegative_multiplicative.nonnegative Ksh.1 Ksh.2
            have hcoef : 0 ≤ P.constant * EB *
                (Real.log 2).rpow (-1 / 2) * w1Weight Ksh.1 :=
              mul_nonneg (mul_nonneg (mul_nonneg P.constant_pos.le
                (zero_le_one.trans hEB)) (Real.rpow_nonneg hlog2.le _)) hw1
            calc
              P.constant * w1Weight Ksh.1 * z *
                  (Real.log z).rpow (-1 / 2) * EB *
                  (Real.log 2).rpow (-1 / 2) =
                (P.constant * EB * (Real.log 2).rpow (-1 / 2) *
                  w1Weight Ksh.1) *
                  (z * (Real.log z).rpow (-1 / 2)) := by ring
              _ ≤ (P.constant * EB * (Real.log 2).rpow (-1 / 2) *
                  w1Weight Ksh.1) *
                  (2 * logLoss * safeLogHalfSum z) :=
                    mul_le_mul_of_nonneg_left hcompare hcoef
              _ = _ := by ring
      _ ≤ Csm * w1Weight Ksh.1 * safeLogHalfSum z := by
        have hw1 := (W.weight_type q .w1).nonnegative_multiplicative.nonnegative Ksh.1 Ksh.2
        have hsum : 0 ≤ safeLogHalfSum z := by
          unfold safeLogHalfSum
          exact Finset.sum_nonneg fun m hm => Real.rpow_nonneg
            (zero_le_one.trans (le_max_left _ _)) _
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_max_right _ _) hw1) hsum

end

end Erdos448.Stage7.ROOT06.Smoothing
