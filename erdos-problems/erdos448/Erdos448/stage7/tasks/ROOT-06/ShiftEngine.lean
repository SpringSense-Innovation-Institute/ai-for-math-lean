module

import all Mathlib.Basic.Real.Basic
public import Erdos448.stage6.TaskContracts
public import Erdos448.stage7.shared.LocalFactorFloor

public section

set_option backward.isDefEq.respectTransparency false

namespace Erdos448.Stage7.ROOT06.ShiftEngine

open Erdos448.Stage4
open Erdos448.Stage4.Contracts
open Finset
open scoped BigOperators

noncomputable section

instance (p : Prop) : Decidable p := Classical.propDecidable p

theorem geometricBounds
    (W : CommonWeightWitnesses) (q : WeightParameters) (member : WeightMember) :
    ShiftedGeometricBounds (selectedWeight q member) (modifierWeight q)
      (fun _ => W.LambdaStar) 1 := by
  intro p hp i j
  have hw := W.weight_type q member
  have hb := W.modifier q
  by_cases hij : i + j = 0
  · have hi : i = 0 := by omega
    have hj : j = 0 := by omega
    subst i
    subst j
    have hLam : 1 ≤ W.LambdaStar := by
      have hterm : 0 ≤ W.CStar * (2 : ℝ).rpow (-W.cStar) :=
        mul_nonneg W.CStar_pos.le (Real.rpow_nonneg (by norm_num) _)
      exact (by linarith : (1 : ℝ) ≤ 1 + W.CStar *
        (2 : ℝ).rpow (-W.cStar)) |>.trans W.LambdaStar_lower
    simpa [hw.normalized, hb.normalized] using hLam
  · have hijpos : 1 ≤ i + j := Nat.one_le_iff_ne_zero.mpr hij
    have hu := hw.prime_power_bounds p hp (i + j) hijpos
    have hv := hb.prime_power_bounds p hp j
    constructor
    · exact mul_nonneg hu.1 hv.1
    · calc
        selectedWeight q member (p ^ (i + j)) * modifierWeight q (p ^ j)
            ≤ W.LambdaStar * 1 := by
              exact mul_le_mul hu.2 hv.2 hv.1 W.LambdaStar_pos.le
        _ = (fun _ : ℕ => W.LambdaStar) i * 1 ^ j := by simp

theorem shiftedPrimeProduct_le_maxShift
    {u v : ArithmeticWeight} (hu : NonnegativeMultiplicativeWeight u)
    (hs : ShiftSpecification u v) (Ksh : PosNat) (X : ℝ) :
    shiftedPrimeProduct u v Ksh X ≤ maxShift u v Ksh.1 := by
  have hK0 : Ksh.1 ≠ 0 := Nat.ne_of_gt Ksh.2
  unfold shiftedPrimeProduct maxShift multiplicativeExtension
  rw [if_neg hK0, ← Finset.prod_mul_distrib]
  apply Finset.prod_le_prod₀
  · intro p hp
    have hprime := Nat.prime_of_mem_primeFactors hp
    have hdiv := Nat.dvd_of_mem_primeFactors hp
    have hexp : 1 ≤ Ksh.1.factorization p :=
      hprime.factorization_pos_of_dvd hK0 hdiv
    by_cases hpx : (p : ℝ) < X
    · have hnot : ¬X ≤ (p : ℝ) := not_le_of_gt hpx
      simp only [hpx, if_true, hnot, if_false, mul_one, exactShiftFactor]
      rw [← hs.shift_prime_power p hprime _ hexp]
      exact hs.shift_nonnegative_multiplicative.nonnegative _
        (Nat.pow_pos hprime.pos)
    · have hxp : X ≤ (p : ℝ) := le_of_not_gt hpx
      simp only [hpx, if_false, hxp, if_true, one_mul]
      exact hu.nonnegative _ (Nat.pow_pos hprime.pos)
  · intro p hp
    have hprime := Nat.prime_of_mem_primeFactors hp
    by_cases hpx : (p : ℝ) < X
    · have hnot : ¬X ≤ (p : ℝ) := not_le_of_gt hpx
      simp [hpx, hnot, exactShiftFactor, le_max_left]
    · have hxp : X ≤ (p : ℝ) := le_of_not_gt hpx
      simp [hpx, hxp, exactShiftFactor, le_max_right]

theorem p005Bound
    (hP005 : P005Statement) (W : CommonWeightWitnesses)
    (q : WeightParameters) (member : WeightMember)
    (hs : ShiftSpecification (selectedWeight q member) (modifierWeight q)) :
    ∃ D : ℝ, 0 < D ∧ ∀ Ksh : PosNat, ∀ X : ℝ, 2 ≤ X →
      Contracts.shiftedMean (selectedWeight q member) (modifierWeight q) Ksh X ≤
        D * maxShift (selectedWeight q member) (modifierWeight q) Ksh.1 *
          (X / Real.log X) *
          (∏ p ∈ strictPrimeRange X,
            localEulerFactor (selectedWeight q member) (modifierWeight q) p) := by
  obtain ⟨P⟩ := hP005 (fun _ => W.LambdaStar)
    (fun _ => W.LambdaStar_pos.le) 1 zero_le_one (by norm_num)
  refine ⟨P.constant, P.constant_pos, ?_⟩
  intro Ksh X hX
  have hb := P.bound (selectedWeight q member) (modifierWeight q)
    (W.weight_type q member).nonnegative_multiplicative
    (W.modifier q).nonnegative_multiplicative
    (geometricBounds W q member) Ksh X hX
  calc
    Contracts.shiftedMean (selectedWeight q member) (modifierWeight q) Ksh X
        ≤ P.constant * shiftedPrimeProduct (selectedWeight q member)
          (modifierWeight q) Ksh X * (X / Real.log X) *
          (∏ p ∈ strictPrimeRange X,
            localEulerFactor (selectedWeight q member) (modifierWeight q) p) := by
              simpa [localEulerFactor, localEulerSeries] using hb
    _ ≤ P.constant * maxShift (selectedWeight q member) (modifierWeight q) Ksh.1 *
          (X / Real.log X) *
          (∏ p ∈ strictPrimeRange X,
            localEulerFactor (selectedWeight q member) (modifierWeight q) p) := by
      have hp : 0 ≤ ∏ p ∈ strictPrimeRange X,
          localEulerFactor (selectedWeight q member) (modifierWeight q) p := by
        apply Finset.prod_nonneg
        intro p hp
        have hprime := (Finset.mem_filter.mp hp).2
        exact (Erdos448.Stage7.Shared.localEulerFactor_ge_one hprime
          (W.weight_type q member).nonnegative_multiplicative
          (W.weight_type q member).normalized (W.modifier q)
          ((hs.admissible.denominator_summable p hprime))).trans' zero_le_one
      have hdiv : 0 ≤ X / Real.log X := div_nonneg
        (zero_le_two.trans hX) (Real.log_nonneg (one_le_two.trans hX))
      have hshift := shiftedPrimeProduct_le_maxShift
        (W.weight_type q member).nonnegative_multiplicative hs Ksh X
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hshift P.constant_pos.le) hdiv) hp

end

end Erdos448.Stage7.ROOT06.ShiftEngine
