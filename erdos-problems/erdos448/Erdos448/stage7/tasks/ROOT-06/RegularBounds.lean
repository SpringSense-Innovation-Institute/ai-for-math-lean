module

import all Mathlib.Basic.Real.Basic
public import Erdos448.stage7.tasks.«ROOT-06».EulerEngine

public section

set_option backward.isDefEq.respectTransparency false

namespace Erdos448.Stage7.ROOT06.RegularBounds

open Erdos448.Stage4
open Erdos448.Stage4.Contracts
open Erdos448.Stage4.WrapupFamilies
open Erdos448.Stage7.ROOT06.EulerEngine
open Finset
open scoped BigOperators

noncomputable section

instance (p : Prop) : Decidable p := Classical.propDecidable p

theorem productBounds (hP008 : P008Statement.{0}) (W : CommonWeightWitnesses)
    (h051H : P051HStatement) :
    ∃ B : ℝ, 1 ≤ B ∧
      ∀ q : RegularIndex,
        (q.parameters.sigma ≤ q.z →
          q.z ≤ q.parameters.theta ^ q.parameters.k →
          (∏ p ∈ strictPrimeRange q.z, regularEuler q p) ≤
            B * (Real.log q.z / Real.log q.parameters.sigma).rpow
              (q.parameters.y / 2)) ∧
        (q.parameters.theta ^ q.parameters.k ≤ q.z →
          (∏ p ∈ strictPrimeRange q.z, regularEuler q p) ≤
            B ^ 2 *
              (Real.log (q.parameters.theta ^ q.parameters.k) /
                Real.log q.parameters.sigma).rpow (q.parameters.y / 2) *
              (Real.log q.z /
                Real.log (q.parameters.theta ^ q.parameters.k)).rpow (1 / 2)) := by
  obtain ⟨Pm⟩ := midOutput hP008 W h051H
  obtain ⟨Ph⟩ := highOutput hP008 W h051H
  let B : ℝ := max 1 (max Pm.comparison.upper Ph.comparison.upper)
  have hB : 1 ≤ B := le_max_left _ _
  have hBm : Pm.comparison.upper ≤ B :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hBh : Ph.comparison.upper ≤ B :=
    (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨B, hB, ?_⟩
  intro q
  constructor
  · intro hsz hzH
    rw [strictEuler_eq_mid W h051H q hzH hsz]
    by_cases heq : q.parameters.sigma = q.z
    · rw [← heq, Pm.empty_branch q q.parameters.sigma q.parameters.sigma
        (q.parameters.theta_ge_two.trans q.parameters.sigma_ge_theta)
        (q.parameters.theta_ge_two.trans q.parameters.sigma_ge_theta) le_rfl]
      have hlogs : 0 < Real.log q.parameters.sigma :=
        Real.log_pos (one_lt_two.trans_le
          (q.parameters.theta_ge_two.trans q.parameters.sigma_ge_theta))
      simp [hlogs.ne', hB]
    · have hlt : q.parameters.sigma < q.z := lt_of_le_of_ne hsz heq
      have hb := (Pm.family_bounds q q.parameters.sigma q.z
        (q.parameters.theta_ge_two.trans q.parameters.sigma_ge_theta) hlt).2
      have hz2 : 2 ≤ q.z :=
        q.parameters.theta_ge_two.trans (q.parameters.sigma_ge_theta.trans hsz)
      exact hb.trans (mul_le_mul_of_nonneg_right hBm
        (Real.rpow_nonneg (div_nonneg (Real.log_nonneg (one_le_two.trans hz2))
          (Real.log_nonneg (one_le_two.trans
            (q.parameters.theta_ge_two.trans q.parameters.sigma_ge_theta)))) _))
  · intro hHz
    rw [strictEuler_eq_mid_mul_high W h051H q hHz]
    have hsH : q.parameters.sigma ≤ q.parameters.theta ^ q.parameters.k := q.regular
    have hs2 : 2 ≤ q.parameters.sigma :=
      q.parameters.theta_ge_two.trans q.parameters.sigma_ge_theta
    have hH2 : 2 ≤ q.parameters.theta ^ q.parameters.k := hs2.trans hsH
    have hz2 : 2 ≤ q.z := hH2.trans hHz
    have hlogS : 0 < Real.log q.parameters.sigma :=
      Real.log_pos (one_lt_two.trans_le hs2)
    have hlogH : 0 < Real.log (q.parameters.theta ^ q.parameters.k) :=
      Real.log_pos (one_lt_two.trans_le hH2)
    have hlogZ : 0 < Real.log q.z := Real.log_pos (one_lt_two.trans_le hz2)
    have hmratio0 : 0 ≤ Real.log (q.parameters.theta ^ q.parameters.k) /
        Real.log q.parameters.sigma := div_nonneg hlogH.le hlogS.le
    have hhratio0 : 0 ≤ Real.log q.z /
        Real.log (q.parameters.theta ^ q.parameters.k) := div_nonneg hlogZ.le hlogH.le
    have hmid : primeIntervalProduct (regularMidFactor q) q.parameters.sigma
        (q.parameters.theta ^ q.parameters.k) ≤
        B *
          (Real.log (q.parameters.theta ^ q.parameters.k) /
            Real.log q.parameters.sigma).rpow (q.parameters.y / 2) := by
      by_cases heq : q.parameters.sigma = q.parameters.theta ^ q.parameters.k
      · rw [← heq, Pm.empty_branch q _ _ hs2 hs2 le_rfl]
        have hratio : Real.log q.parameters.sigma /
            Real.log q.parameters.sigma = 1 := div_self hlogS.ne'
        rw [hratio]
        have hone : Real.rpow 1 (q.parameters.y / 2) = 1 :=
          Real.one_rpow _
        rw [hone, mul_one]
        exact hB
      · exact ((Pm.family_bounds q _ _ hs2 (lt_of_le_of_ne hsH heq)).2).trans
          (mul_le_mul_of_nonneg_right hBm (Real.rpow_nonneg hmratio0 _))
    have hhigh : primeIntervalProduct (regularHighFactor q)
        (q.parameters.theta ^ q.parameters.k) q.z ≤
        B *
          (Real.log q.z / Real.log (q.parameters.theta ^ q.parameters.k)).rpow
            (1 / 2) := by
      by_cases heq : q.parameters.theta ^ q.parameters.k = q.z
      · rw [← heq, Ph.empty_branch q _ _ hH2 hH2 le_rfl]
        have hratio : Real.log (q.parameters.theta ^ q.parameters.k) /
            Real.log (q.parameters.theta ^ q.parameters.k) = 1 := div_self hlogH.ne'
        rw [hratio]
        have hone : Real.rpow 1 (1 / 2 : ℝ) = 1 := Real.one_rpow _
        rw [hone, mul_one]
        exact hB
      · exact ((Ph.family_bounds q _ _ hH2 (lt_of_le_of_ne hHz heq)).2).trans
          (mul_le_mul_of_nonneg_right hBh (Real.rpow_nonneg hhratio0 _))
    have hhigh0 : 0 ≤ primeIntervalProduct (regularHighFactor q)
        (q.parameters.theta ^ q.parameters.k) q.z := by
      unfold primeIntervalProduct
      apply Finset.prod_nonneg
      intro p hp
      by_cases hA : q.parameters.theta ^ q.parameters.k ≤ (p : ℝ)
      · simp only [hA, if_true]
        unfold regularHighFactor
        split_ifs
        · exact (actual_floor W h051H q (mem_strictPrimeRange.mp hp).1).trans' zero_le_one
        · exact (model_high_floor (mem_strictPrimeRange.mp hp).1).trans' zero_le_one
      · simp [hA]
    have hmidR0 : 0 ≤ B *
        (Real.log (q.parameters.theta ^ q.parameters.k) /
          Real.log q.parameters.sigma).rpow (q.parameters.y / 2) :=
      mul_nonneg (zero_le_one.trans hB) (Real.rpow_nonneg hmratio0 _)
    calc
      primeIntervalProduct (regularMidFactor q) q.parameters.sigma
            (q.parameters.theta ^ q.parameters.k) *
          primeIntervalProduct (regularHighFactor q)
            (q.parameters.theta ^ q.parameters.k) q.z
          ≤ (B *
              (Real.log (q.parameters.theta ^ q.parameters.k) /
                Real.log q.parameters.sigma).rpow (q.parameters.y / 2)) *
            (B *
              (Real.log q.z /
                Real.log (q.parameters.theta ^ q.parameters.k)).rpow
                  (1 / 2)) := mul_le_mul hmid hhigh hhigh0 hmidR0
      _ = B ^ 2 *
            (Real.log (q.parameters.theta ^ q.parameters.k) /
              Real.log q.parameters.sigma).rpow (q.parameters.y / 2) *
            (Real.log q.z /
              Real.log (q.parameters.theta ^ q.parameters.k)).rpow (1 / 2) := by ring

end

end Erdos448.Stage7.ROOT06.RegularBounds
