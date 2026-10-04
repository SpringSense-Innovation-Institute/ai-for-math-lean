module

import all Mathlib.Basic.Real.Basic
public import Erdos448.stage7.tasks.«ROOT-06».Smoothing

public section

set_option backward.isDefEq.respectTransparency false

namespace Erdos448.Stage7.ROOT06.Outer

open Erdos448.Stage4
open Erdos448.Stage4.Contracts
open Erdos448.Stage4.WrapupFamilies
open Erdos448.Stage7.ROOT06.ShiftEngine
open Erdos448.Stage7.ROOT06.RegularBounds
open Erdos448.Stage7.ROOT06.MainNodes
open Finset
open scoped BigOperators

noncomputable section

instance (p : Prop) : Decidable p := Classical.propDecidable p

theorem outerAlgebra (q : WeightParameters)
    (hsH : q.sigma ≤ q.theta ^ q.k) :
    (q.theta * q.theta ^ q.k / Real.log (q.theta * q.theta ^ q.k)) *
      ((Real.log (q.theta ^ q.k) / Real.log q.sigma).rpow (q.y / 2) *
        (Real.log (q.theta * q.theta ^ q.k) /
          Real.log (q.theta ^ q.k)).rpow (1 / 2)) ≤
      q.theta * max 1 ((Real.log q.theta).rpow (-1)) *
        q.theta ^ q.k * (Real.log q.sigma).rpow (-q.y / 2) *
        (q.k : ℝ).rpow (q.y / 2 - 1) := by
  have ht0 : 0 < q.theta := lt_of_lt_of_le (by norm_num) q.theta_ge_two
  have hk0 : (0 : ℝ) < q.k := by exact_mod_cast q.k_pos
  have hs2 : 2 ≤ q.sigma := q.theta_ge_two.trans q.sigma_ge_theta
  have hH2 : 2 ≤ q.theta ^ q.k := hs2.trans hsH
  have hth : 0 < Real.log q.theta := Real.log_pos (one_lt_two.trans_le q.theta_ge_two)
  have hls : 0 < Real.log q.sigma := Real.log_pos (one_lt_two.trans_le hs2)
  have hlH : 0 < Real.log (q.theta ^ q.k) := Real.log_pos (one_lt_two.trans_le hH2)
  have hz2 : 2 ≤ q.theta * q.theta ^ q.k := by
    have hH1 : 1 ≤ q.theta ^ q.k := (by norm_num : (1 : ℝ) ≤ 2).trans hH2
    have hm := mul_le_mul_of_nonneg_left hH1 ht0.le
    exact q.theta_ge_two.trans (by simpa using hm)
  have hlz : 0 < Real.log (q.theta * q.theta ^ q.k) := by
    exact Real.log_pos (one_lt_two.trans_le hz2)
  have hk1 : (1 : ℝ) ≤ q.k := by exact_mod_cast q.k_pos
  have hy : 0 < q.y := q.y_pos
  have hy1 : q.y < 1 := q.y_lt_one
  rw [show q.theta * q.theta ^ q.k = q.theta ^ (q.k + 1) by rw [pow_succ]; ring,
    Real.log_pow, Real.log_pow]
  have hcast : ((q.k + 1 : ℕ) : ℝ) = (q.k : ℝ) + 1 := by push_cast; ring
  rw [hcast]
  have hfac :
      (q.theta ^ (q.k + 1) / (((q.k : ℝ) + 1) * Real.log q.theta)) *
        ((((q.k : ℝ) * Real.log q.theta) / Real.log q.sigma).rpow (q.y / 2) *
          ((((q.k : ℝ) + 1) * Real.log q.theta) /
            ((q.k : ℝ) * Real.log q.theta)).rpow (1 / 2)) =
      q.theta ^ (q.k + 1) * (Real.log q.sigma).rpow (-q.y / 2) *
        (q.k : ℝ).rpow (q.y / 2 - 1 / 2) *
        ((q.k : ℝ) + 1).rpow (-1 / 2) *
        (Real.log q.theta).rpow (q.y / 2 - 1) := by
    have hkp : 0 < (q.k : ℝ) + 1 := by linarith
    have hkt : 0 < (q.k : ℝ) * Real.log q.theta := mul_pos hk0 hth
    have hkpt : 0 < ((q.k : ℝ) + 1) * Real.log q.theta := mul_pos hkp hth
    have hkcombine : (q.k : ℝ).rpow (q.y / 2) *
        (q.k : ℝ).rpow (-1 / 2) =
        (q.k : ℝ).rpow (q.y / 2 - 1 / 2) := by
      calc
        _ = (q.k : ℝ).rpow (q.y / 2 + (-1 / 2)) := rpow_mul_same hk0
        _ = _ := by ring_nf
    have hkpcombine : ((q.k : ℝ) + 1).rpow (-1) *
        ((q.k : ℝ) + 1).rpow (1 / 2) =
        ((q.k : ℝ) + 1).rpow (-1 / 2) := by
      calc
        _ = ((q.k : ℝ) + 1).rpow ((-1 : ℝ) + 1 / 2) := rpow_mul_same hkp
        _ = _ := by norm_num
    have htcombine : (Real.log q.theta).rpow (-1) *
        (Real.log q.theta).rpow (q.y / 2) *
        ((Real.log q.theta).rpow (1 / 2) *
          (Real.log q.theta).rpow (-1 / 2)) =
        (Real.log q.theta).rpow (q.y / 2 - 1) := by
      have hcancel : (Real.log q.theta).rpow (1 / 2) *
          (Real.log q.theta).rpow (-1 / 2) = 1 := by
        have hzpow : (Real.log q.theta).rpow (0 : ℝ) = 1 := by
          rw [Real.rpow_eq_pow]
          exact Real.rpow_zero _
        calc
          _ = (Real.log q.theta).rpow ((1 / 2 : ℝ) + (-1 / 2)) :=
            rpow_mul_same hth
          _ = 1 := by convert hzpow using 1 <;> ring
      rw [hcancel, mul_one]
      calc
        _ = (Real.log q.theta).rpow ((-1 : ℝ) + q.y / 2) := rpow_mul_same hth
        _ = _ := by ring_nf
    rw [show q.theta ^ (q.k + 1) /
        (((q.k : ℝ) + 1) * Real.log q.theta) =
        q.theta ^ (q.k + 1) * (((q.k : ℝ) + 1)⁻¹) *
          (Real.log q.theta)⁻¹ by field_simp,
      show (((q.k : ℝ) + 1)⁻¹) = ((q.k : ℝ) + 1).rpow (-1) by
        simpa using (Real.rpow_neg_one ((q.k : ℝ) + 1)).symm,
      show (Real.log q.theta)⁻¹ = (Real.log q.theta).rpow (-1) by
        simpa using (Real.rpow_neg_one (Real.log q.theta)).symm,
      rpow_div_pos hkt hls, rpow_div_pos hkpt hkt,
      rpow_mul_pos hk0 hth, rpow_mul_pos hkp hth,
      rpow_mul_pos hk0 hth]
    rw [show -(q.y / 2) = -q.y / 2 by ring,
      show -(1 / 2 : ℝ) = -1 / 2 by ring]
    calc
      q.theta ^ (q.k + 1) * ((q.k : ℝ) + 1).rpow (-1) *
          (Real.log q.theta).rpow (-1) *
          (((q.k : ℝ).rpow (q.y / 2) *
            (Real.log q.theta).rpow (q.y / 2)) *
            (Real.log q.sigma).rpow (-q.y / 2) *
            (((q.k : ℝ) + 1).rpow (1 / 2) *
              (Real.log q.theta).rpow (1 / 2) *
              ((q.k : ℝ).rpow (-1 / 2) *
                (Real.log q.theta).rpow (-1 / 2)))) =
        q.theta ^ (q.k + 1) * (Real.log q.sigma).rpow (-q.y / 2) *
          ((q.k : ℝ).rpow (q.y / 2) * (q.k : ℝ).rpow (-1 / 2)) *
          (((q.k : ℝ) + 1).rpow (-1) *
            ((q.k : ℝ) + 1).rpow (1 / 2)) *
          ((Real.log q.theta).rpow (-1) *
            (Real.log q.theta).rpow (q.y / 2) *
            ((Real.log q.theta).rpow (1 / 2) *
              (Real.log q.theta).rpow (-1 / 2))) := by ring
      _ = _ := by rw [hkcombine, hkpcombine, htcombine]
  rw [hfac]
  have hkRatio : (q.k : ℝ).rpow (q.y / 2 - 1 / 2) *
      ((q.k : ℝ) + 1).rpow (-1 / 2) ≤
      (q.k : ℝ).rpow (q.y / 2 - 1) := by
    have hsqrt : ((q.k : ℝ) + 1).rpow (-1 / 2) ≤
        (q.k : ℝ).rpow (-1 / 2) := by
      exact (Real.rpow_le_rpow_iff_of_neg (by linarith : 0 < (q.k : ℝ) + 1)
        hk0 (by norm_num)).2 (by linarith)
    calc
      (q.k : ℝ).rpow (q.y / 2 - 1 / 2) *
          ((q.k : ℝ) + 1).rpow (-1 / 2)
        ≤ (q.k : ℝ).rpow (q.y / 2 - 1 / 2) *
          (q.k : ℝ).rpow (-1 / 2) :=
            mul_le_mul_of_nonneg_left hsqrt (Real.rpow_nonneg hk0.le _)
      _ = (q.k : ℝ).rpow (q.y / 2 - 1) := by
        calc
          _ = (q.k : ℝ).rpow ((q.y / 2 - 1 / 2) + (-1 / 2)) :=
            rpow_mul_same hk0
          _ = _ := by ring_nf
  have htheta : (Real.log q.theta).rpow (q.y / 2 - 1) ≤
      max 1 ((Real.log q.theta).rpow (-1)) := by
    have he0 : q.y / 2 - 1 ≤ 0 := by linarith
    have he1 : -1 ≤ q.y / 2 - 1 := by linarith
    by_cases h1 : 1 ≤ Real.log q.theta
    · exact (Real.rpow_le_one_of_one_le_of_nonpos h1 he0).trans (le_max_left _ _)
    · exact (Real.rpow_le_rpow_of_exponent_ge hth (le_of_not_ge h1) he1).trans
        (le_max_right _ _)
  rw [pow_succ]
  have hbase0 : 0 ≤ q.theta * q.theta ^ q.k *
      (Real.log q.sigma).rpow (-q.y / 2) :=
    mul_nonneg (mul_nonneg ht0.le (pow_nonneg ht0.le _))
      (Real.rpow_nonneg hls.le _)
  have hkfinal0 : 0 ≤ (q.k : ℝ).rpow (q.y / 2 - 1) :=
    Real.rpow_nonneg hk0.le _
  have htPow0 : 0 ≤ (Real.log q.theta).rpow (q.y / 2 - 1) :=
    Real.rpow_nonneg hth.le _
  calc
    q.theta ^ q.k * q.theta * (Real.log q.sigma).rpow (-q.y / 2) *
          (q.k : ℝ).rpow (q.y / 2 - 1 / 2) *
          ((q.k : ℝ) + 1).rpow (-1 / 2) *
          (Real.log q.theta).rpow (q.y / 2 - 1) =
      (q.theta * q.theta ^ q.k * (Real.log q.sigma).rpow (-q.y / 2)) *
        ((q.k : ℝ).rpow (q.y / 2 - 1 / 2) *
          ((q.k : ℝ) + 1).rpow (-1 / 2)) *
        (Real.log q.theta).rpow (q.y / 2 - 1) := by ring
    _ ≤ (q.theta * q.theta ^ q.k * (Real.log q.sigma).rpow (-q.y / 2)) *
        (q.k : ℝ).rpow (q.y / 2 - 1) *
        (Real.log q.theta).rpow (q.y / 2 - 1) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hkRatio hbase0) htPow0
    _ ≤ (q.theta * q.theta ^ q.k * (Real.log q.sigma).rpow (-q.y / 2)) *
        (q.k : ℝ).rpow (q.y / 2 - 1) *
        max 1 ((Real.log q.theta).rpow (-1)) :=
      mul_le_mul_of_nonneg_left htheta (mul_nonneg hbase0 hkfinal0)
    _ = q.theta * max 1 ((Real.log q.theta).rpow (-1)) *
        q.theta ^ q.k * (Real.log q.sigma).rpow (-q.y / 2) *
        (q.k : ℝ).rpow (q.y / 2 - 1) := by ring

theorem p058 (hP005 : P005Statement) (hP008 : P008Statement.{0})
    (chain : WeightChainSpec) (W : CommonWeightWitnesses)
    (h051H : P051HStatement) (h054 : P054Statement) : P058Statement := by
  obtain ⟨P⟩ := hP005 (fun _ => W.LambdaStar)
    (fun _ => W.LambdaStar_pos.le) 1 zero_le_one (by norm_num)
  obtain ⟨B, hB, hEuler⟩ := productBounds hP008 W h051H
  intro theta htheta
  let Cout := theta * P.constant * B ^ 2 *
    max 1 ((Real.log theta).rpow (-1))
  have hCout : 0 < Cout := by
    dsimp [Cout]
    exact mul_pos (mul_pos (mul_pos (lt_of_lt_of_le zero_lt_two htheta)
      P.constant_pos) (sq_pos_of_pos (zero_lt_one.trans_le hB)))
      (zero_lt_one.trans_le (le_max_left _ _))
  refine ⟨Cout, hCout, ?_⟩
  intro q hq hsH
  have ht0 : 0 < q.theta := lt_of_lt_of_le (by norm_num) q.theta_ge_two
  have hendpoint : q.theta ^ (q.k + 1) = q.theta * q.theta ^ q.k := by
    rw [pow_succ]
    ring
  have hz2 : 2 ≤ q.theta * q.theta ^ q.k := by
    have hH1 : 1 ≤ q.theta ^ q.k := one_le_pow₀ (by linarith [q.theta_ge_two])
    nlinarith
  let qi : RegularIndex :=
    { parameters := q, member := .w3, regular := hsH,
      z := q.theta * q.theta ^ q.k, z_ge_two := hz2 }
  have hraw (d' : ℕ) (hd' : 0 < d') :
      Contracts.shiftedMean (w3Weight q) (modifierWeight q) ⟨d', hd'⟩
          (q.theta * q.theta ^ q.k) ≤
        P.constant * w4Weight q d' *
          ((q.theta * q.theta ^ q.k) /
            Real.log (q.theta * q.theta ^ q.k)) *
          (∏ p ∈ strictPrimeRange (q.theta * q.theta ^ q.k),
            regularEuler qi p) := by
    have h := MainNodes.p005Raw W P q .w3 (by simpa [selectedWeight] using chain.w4_shift q)
      ⟨d', hd'⟩ (q.theta * q.theta ^ q.k) hz2
    simpa [selectedWeight, w4Weight, qi, regularEuler] using h
  have heuler := (hEuler qi).2 (by
    dsimp [qi]
    have hH0 : 0 ≤ q.theta ^ q.k := by positivity
    nlinarith)
  have hinner (d' : ℕ) (hd' : 0 < d') :
      Contracts.shiftedMean (w3Weight q) (modifierWeight q) ⟨d', hd'⟩
          (q.theta * q.theta ^ q.k) ≤
        P.constant * B ^ 2 * w4Weight q d' *
          (q.theta * max 1 ((Real.log q.theta).rpow (-1)) *
            q.theta ^ q.k * (Real.log q.sigma).rpow (-q.y / 2) *
            (q.k : ℝ).rpow (q.y / 2 - 1)) := by
    calc
      Contracts.shiftedMean (w3Weight q) (modifierWeight q) ⟨d', hd'⟩
          (q.theta * q.theta ^ q.k)
        ≤ P.constant * w4Weight q d' *
          ((q.theta * q.theta ^ q.k) /
            Real.log (q.theta * q.theta ^ q.k)) *
          (∏ p ∈ strictPrimeRange (q.theta * q.theta ^ q.k), regularEuler qi p) := hraw d' hd'
      _ ≤ P.constant * w4Weight q d' *
          ((q.theta * q.theta ^ q.k) / Real.log (q.theta * q.theta ^ q.k)) *
          (B ^ 2 *
            (Real.log (q.theta ^ q.k) / Real.log q.sigma).rpow (q.y / 2) *
            (Real.log (q.theta * q.theta ^ q.k) /
              Real.log (q.theta ^ q.k)).rpow (1 / 2)) := by
                have hw4 := (W.weight_type q .w4).nonnegative_multiplicative.nonnegative d' hd'
                have hdiv : 0 ≤ (q.theta * q.theta ^ q.k) /
                    Real.log (q.theta * q.theta ^ q.k) := div_nonneg
                  (zero_le_two.trans hz2) (Real.log_nonneg (one_le_two.trans hz2))
                exact mul_le_mul_of_nonneg_left heuler
                  (mul_nonneg (mul_nonneg P.constant_pos.le hw4) hdiv)
      _ ≤ P.constant * B ^ 2 * w4Weight q d' *
          (q.theta * max 1 ((Real.log q.theta).rpow (-1)) *
            q.theta ^ q.k * (Real.log q.sigma).rpow (-q.y / 2) *
            (q.k : ℝ).rpow (q.y / 2 - 1)) := by
              have ha := outerAlgebra q hsH
              have hw4 := (W.weight_type q .w4).nonnegative_multiplicative.nonnegative d' hd'
              have hcoef : 0 ≤ P.constant * B ^ 2 * w4Weight q d' :=
                mul_nonneg (mul_nonneg P.constant_pos.le (sq_nonneg B)) hw4
              calc
                P.constant * w4Weight q d' *
                    ((q.theta * q.theta ^ q.k) / Real.log (q.theta * q.theta ^ q.k)) *
                    (B ^ 2 *
                      (Real.log (q.theta ^ q.k) / Real.log q.sigma).rpow (q.y / 2) *
                      (Real.log (q.theta * q.theta ^ q.k) /
                        Real.log (q.theta ^ q.k)).rpow (1 / 2)) =
                  (P.constant * B ^ 2 * w4Weight q d') *
                    (((q.theta * q.theta ^ q.k) / Real.log (q.theta * q.theta ^ q.k)) *
                      ((Real.log (q.theta ^ q.k) / Real.log q.sigma).rpow (q.y / 2) *
                        (Real.log (q.theta * q.theta ^ q.k) /
                          Real.log (q.theta ^ q.k)).rpow (1 / 2))) := by ring
                _ ≤ (P.constant * B ^ 2 * w4Weight q d') *
                    (q.theta * max 1 ((Real.log q.theta).rpow (-1)) *
                      q.theta ^ q.k * (Real.log q.sigma).rpow (-q.y / 2) *
                      (q.k : ℝ).rpow (q.y / 2 - 1)) :=
                        mul_le_mul_of_nonneg_left ha hcoef
                _ = _ := by ring
  unfold regularOuter outerPairSum
  rw [Finset.sum_comm]
  calc
    ∑ d' ∈ positiveNatsBelow (q.theta ^ (q.k + 2)),
        ∑ d ∈ positiveNatsBelow (q.theta ^ (q.k + 1)),
          (if hd : 0 < d then
            if hd' : 0 < d' then
              if q.theta ^ q.k ≤ (d : ℝ) ∧ Close q.theta ⟨d, hd⟩ ⟨d', hd'⟩ then
                (roughIndicator d q.sigma : ℝ) *
                  q.y.rpow (omegaBelowRaw d (q.theta ^ q.k) : ℝ) *
                    w3Weight q (d * d') else 0 else 0 else 0)
      ≤ ∑ d' ∈ positiveNatsBelow (q.theta ^ (q.k + 2)),
          if q.theta ^ (q.k - 1) < (d' : ℝ) then
            if hd' : 0 < d' then
              Contracts.shiftedMean (w3Weight q) (modifierWeight q)
                ⟨d', hd'⟩ (q.theta * q.theta ^ q.k)
            else 0 else 0 := by
        apply Finset.sum_le_sum
        intro d' hd'
        have hd'pos := (Finset.mem_filter.mp hd').2.1
        by_cases hwin : q.theta ^ (q.k - 1) < (d' : ℝ)
        · simp only [hwin, if_true, dif_pos hd'pos]
          rw [Contracts.shiftedMean, ← hendpoint]
          apply Finset.sum_le_sum
          intro d hd
          have hdpos := (Finset.mem_filter.mp hd).2.1
          by_cases hcond : q.theta ^ q.k ≤ (d : ℝ) ∧
              Close q.theta ⟨d, hdpos⟩ ⟨d', hd'pos⟩
          · simp [hdpos, hd'pos, hcond, modifierWeight, mul_comm, mul_left_comm]
          · simp only [hdpos, hd'pos, hcond, ↓reduceDIte, if_false, zero_le]
            exact mul_nonneg
              ((W.weight_type q .w3).nonnegative_multiplicative.nonnegative
                (d' * d) (Nat.mul_pos hd'pos hdpos))
              ((W.modifier q).nonnegative_multiplicative.nonnegative d hdpos)
        · simp only [hwin, if_false]
          apply le_of_eq
          apply Finset.sum_eq_zero
          intro d hd
          have hdpos := (Finset.mem_filter.mp hd).2.1
          by_cases hcond : q.theta ^ q.k ≤ (d : ℝ) ∧
              Close q.theta ⟨d, hdpos⟩ ⟨d', hd'pos⟩
          · exfalso
            apply hwin
            exact (h054 q.k q.k_pos q.theta (by linarith [q.theta_ge_two])
              ⟨d, hdpos⟩ ⟨d', hd'pos⟩ hcond.1
              ((Finset.mem_filter.mp hd).2.2) hcond.2).second_lower
          · simp [hdpos, hd'pos, hcond]
    _ ≤ P.constant * B ^ 2 *
          (q.theta * max 1 ((Real.log q.theta).rpow (-1)) *
            q.theta ^ q.k * (Real.log q.sigma).rpow (-q.y / 2) *
            (q.k : ℝ).rpow (q.y / 2 - 1)) * w4WindowSum q := by
      unfold w4WindowSum
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro d' hd'
      have hd'pos := (Finset.mem_filter.mp hd').2.1
      by_cases hwin : q.theta ^ (q.k - 1) < (d' : ℝ)
      · simp only [hwin, if_true, dif_pos hd'pos]
        have hi := hinner d' hd'pos
        simpa [mul_assoc, mul_left_comm, mul_comm] using hi
      · simp [hwin]
    _ = Cout * q.theta ^ q.k * (Real.log q.sigma).rpow (-q.y / 2) *
          (q.k : ℝ).rpow (q.y / 2 - 1) * w4WindowSum q := by
      dsimp [Cout]
      rw [hq]
      ring

end

end Erdos448.Stage7.ROOT06.Outer
