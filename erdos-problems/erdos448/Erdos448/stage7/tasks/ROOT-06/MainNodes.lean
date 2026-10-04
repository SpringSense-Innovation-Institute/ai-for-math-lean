module

import all Mathlib.Basic.Real.Basic
public import Erdos448.stage7.tasks.«ROOT-06».ShiftEngine
public import Erdos448.stage7.tasks.«ROOT-06».RegularBounds
public import Erdos448.stage7.tasks.«ROOT-06».LogBounds

public section

set_option backward.isDefEq.respectTransparency false

namespace Erdos448.Stage7.ROOT06.MainNodes

open Erdos448.Stage4
open Erdos448.Stage4.Contracts
open Erdos448.Stage4.WrapupFamilies
open Erdos448.Stage7.ROOT06.ShiftEngine
open Erdos448.Stage7.ROOT06.RegularBounds
open Erdos448.Stage7.ROOT06.LogBounds
open Finset
open scoped BigOperators

noncomputable section

instance (p : Prop) : Decidable p := Classical.propDecidable p

lemma rpow_neg_eq_inv {x e : ℝ} (hx : 0 ≤ x) :
    x.rpow (-e) = (x.rpow e)⁻¹ := by
  simpa using Real.rpow_neg hx e

lemma rpow_div_pos {x y e : ℝ} (hx : 0 < x) (hy : 0 < y) :
    (x / y).rpow e = x.rpow e * y.rpow (-e) := by
  calc
    (x / y).rpow e = x.rpow e / y.rpow e := by
      simpa using Real.div_rpow hx.le hy.le e
    _ = x.rpow e * y.rpow (-e) := by
      rw [div_eq_mul_inv, rpow_neg_eq_inv hy.le]

lemma rpow_mul_pos {x y e : ℝ} (hx : 0 < x) (hy : 0 < y) :
    (x * y).rpow e = x.rpow e * y.rpow e := by
  simpa using Real.mul_rpow hx.le hy.le

lemma rpow_mul_same {x a b : ℝ} (hx : 0 < x) :
    x.rpow a * x.rpow b = x.rpow (a + b) := by
  simpa using (Real.rpow_add hx a b).symm

theorem stage4_shifted_eq_contract (q : WeightParameters) (Ksh : PosNat)
    (z : ℝ) :
    Erdos448.Stage4.shiftedMean q z Ksh =
      Contracts.shiftedMean w1Weight (modifierWeight q) Ksh z := by
  unfold Erdos448.Stage4.shiftedMean Contracts.shiftedMean
  apply Finset.sum_congr rfl
  intro n hn
  ring_nf

theorem p005Raw
    (W : CommonWeightWitnesses)
    (P : P005Output (fun _ => W.LambdaStar) 1)
    (q : WeightParameters) (member : WeightMember)
    (hs : ShiftSpecification (selectedWeight q member) (modifierWeight q))
    (Ksh : PosNat) (z : ℝ) (hz : 2 ≤ z) :
    Contracts.shiftedMean (selectedWeight q member) (modifierWeight q) Ksh z ≤
      P.constant * maxShift (selectedWeight q member) (modifierWeight q) Ksh.1 *
        (z / Real.log z) *
        (∏ p ∈ strictPrimeRange z,
          localEulerFactor (selectedWeight q member) (modifierWeight q) p) := by
  have h := P.bound (selectedWeight q member) (modifierWeight q)
    (W.weight_type q member).nonnegative_multiplicative
    (W.modifier q).nonnegative_multiplicative
    (geometricBounds W q member) Ksh z hz
  have hprod := shiftedPrimeProduct_le_maxShift
    (W.weight_type q member).nonnegative_multiplicative hs Ksh z
  have heuler0 : 0 ≤ ∏ p ∈ strictPrimeRange z,
      localEulerFactor (selectedWeight q member) (modifierWeight q) p := by
    apply Finset.prod_nonneg
    intro p hp
    exact (Erdos448.Stage7.Shared.localEulerFactor_ge_one
      (Erdos448.Stage7.ROOT06.EulerEngine.mem_strictPrimeRange.mp hp).1
      (W.weight_type q member).nonnegative_multiplicative
      (W.weight_type q member).normalized (W.modifier q)
      (hs.admissible.denominator_summable p
        (Erdos448.Stage7.ROOT06.EulerEngine.mem_strictPrimeRange.mp hp).1)).trans'
          zero_le_one
  calc
    Contracts.shiftedMean (selectedWeight q member) (modifierWeight q) Ksh z
        ≤ P.constant * shiftedPrimeProduct (selectedWeight q member)
            (modifierWeight q) Ksh z * (z / Real.log z) *
            (∏ p ∈ strictPrimeRange z,
              localEulerFactor (selectedWeight q member) (modifierWeight q) p) := by
                simpa [localEulerFactor, localEulerSeries] using h
    _ ≤ P.constant * maxShift (selectedWeight q member)
          (modifierWeight q) Ksh.1 * (z / Real.log z) *
          (∏ p ∈ strictPrimeRange z,
            localEulerFactor (selectedWeight q member) (modifierWeight q) p) := by
      have hdiv : 0 ≤ z / Real.log z := div_nonneg
        (zero_le_two.trans hz) (Real.log_nonneg (one_le_two.trans hz))
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hprod P.constant_pos.le) hdiv) heuler0

theorem upperAlgebra
    (q : WeightParameters) {z : ℝ}
    (hzH : q.theta ^ q.k ≤ z) (hsH : q.sigma ≤ q.theta ^ q.k) :
    (z / Real.log z) *
          (Real.log (q.theta ^ q.k) / Real.log q.sigma).rpow (q.y / 2) *
          (Real.log z / Real.log (q.theta ^ q.k)).rpow (1 / 2) ≤
      logLoss * max 1 ((Real.log q.theta).rpow (-1)) * z *
        (Real.log q.sigma).rpow (-q.y / 2) *
        (q.k : ℝ).rpow ((q.y - 1) / 2) *
        (safeLog z).rpow (-1 / 2) := by
  have htheta0 : 0 < q.theta := lt_of_lt_of_le (by norm_num) q.theta_ge_two
  have hsigma2 : 2 ≤ q.sigma := q.theta_ge_two.trans q.sigma_ge_theta
  have hH2 : 2 ≤ q.theta ^ q.k := hsigma2.trans hsH
  have hz2 : 2 ≤ z := hH2.trans hzH
  have hlt : 0 < Real.log q.theta := Real.log_pos (one_lt_two.trans_le q.theta_ge_two)
  have hls : 0 < Real.log q.sigma := Real.log_pos (one_lt_two.trans_le hsigma2)
  have hlH : 0 < Real.log (q.theta ^ q.k) := Real.log_pos (one_lt_two.trans_le hH2)
  have hlz : 0 < Real.log z := Real.log_pos (one_lt_two.trans_le hz2)
  have hk0 : (0 : ℝ) < q.k := by exact_mod_cast q.k_pos
  have he : -1 ≤ (q.y - 1) / 2 := by linarith [q.y_pos]
  have he0 : (q.y - 1) / 2 ≤ 0 := by linarith [q.y_lt_one]
  have hsafe := log_rpow_le_loss_safeLog hz2 (by norm_num : (-1 / 2 : ℝ) ≤ 0)
    (by norm_num : (-1 : ℝ) ≤ -1 / 2)
  have htheta : (Real.log q.theta).rpow ((q.y - 1) / 2) ≤
      max 1 ((Real.log q.theta).rpow (-1)) := by
    by_cases h1 : 1 ≤ Real.log q.theta
    · exact (Real.rpow_le_one_of_one_le_of_nonpos h1 he0).trans (le_max_left _ _)
    · have hlt1 : Real.log q.theta < 1 := lt_of_not_ge h1
      exact (Real.rpow_le_rpow_of_exponent_ge hlt hlt1.le he).trans
        (le_max_right _ _)
  rw [Real.log_pow] at hlH ⊢
  have hsplitH : ((q.k : ℝ) * Real.log q.theta).rpow ((q.y - 1) / 2) =
      (q.k : ℝ).rpow ((q.y - 1) / 2) *
        (Real.log q.theta).rpow ((q.y - 1) / 2) := by
    exact rpow_mul_pos hk0 hlt
  have hfac :
      (z / Real.log z) *
          (((q.k : ℝ) * Real.log q.theta) / Real.log q.sigma).rpow (q.y / 2) *
          (Real.log z / ((q.k : ℝ) * Real.log q.theta)).rpow (1 / 2) =
        z * (Real.log q.sigma).rpow (-q.y / 2) *
          (((q.k : ℝ) * Real.log q.theta).rpow ((q.y - 1) / 2)) *
          (Real.log z).rpow (-1 / 2) := by
    have hHlog : 0 < (q.k : ℝ) * Real.log q.theta := mul_pos hk0 hlt
    have hzdiv : z / Real.log z = z * (Real.log z).rpow (-1) := by
      rw [show (Real.log z).rpow (-1 : ℝ) = (Real.log z)⁻¹ by
        simpa using Real.rpow_neg_one (Real.log z)]
      ring
    have hHcombine : ((q.k : ℝ) * Real.log q.theta).rpow (q.y / 2) *
        ((q.k : ℝ) * Real.log q.theta).rpow (-1 / 2) =
        ((q.k : ℝ) * Real.log q.theta).rpow ((q.y - 1) / 2) := by
      calc
        _ = ((q.k : ℝ) * Real.log q.theta).rpow
            (q.y / 2 + (-1 / 2)) := rpow_mul_same hHlog
        _ = _ := by ring_nf
    have hzcombine : (Real.log z).rpow (-1) *
        (Real.log z).rpow (1 / 2) = (Real.log z).rpow (-1 / 2) := by
      calc
        _ = (Real.log z).rpow ((-1 : ℝ) + 1 / 2) := rpow_mul_same hlz
        _ = _ := by norm_num
    rw [hzdiv, rpow_div_pos hHlog hls, rpow_div_pos hlz hHlog]
    rw [show -(q.y / 2) = -q.y / 2 by ring,
      show -(1 / 2 : ℝ) = -1 / 2 by ring]
    calc
      z * (Real.log z).rpow (-1) *
          (((q.k : ℝ) * Real.log q.theta).rpow (q.y / 2) *
            (Real.log q.sigma).rpow (-q.y / 2)) *
          ((Real.log z).rpow (1 / 2) *
            ((q.k : ℝ) * Real.log q.theta).rpow (-1 / 2)) =
        z * (Real.log q.sigma).rpow (-q.y / 2) *
          (((q.k : ℝ) * Real.log q.theta).rpow (q.y / 2) *
            ((q.k : ℝ) * Real.log q.theta).rpow (-1 / 2)) *
          ((Real.log z).rpow (-1) * (Real.log z).rpow (1 / 2)) := by ring
      _ = z * (Real.log q.sigma).rpow (-q.y / 2) *
          (((q.k : ℝ) * Real.log q.theta).rpow ((q.y - 1) / 2)) *
          (Real.log z).rpow (-1 / 2) := by rw [hHcombine, hzcombine]
  rw [hfac, hsplitH]
  have hz0 : 0 ≤ z := zero_le_two.trans hz2
  have hs0 : 0 ≤ (Real.log q.sigma).rpow (-q.y / 2) :=
    Real.rpow_nonneg hls.le _
  have hkpow0 : 0 ≤ (q.k : ℝ).rpow ((q.y - 1) / 2) :=
    Real.rpow_nonneg hk0.le _
  have hlogzpow0 : 0 ≤ (Real.log z).rpow (-1 / 2) :=
    Real.rpow_nonneg hlz.le _
  have hprefix0 : 0 ≤ z * (Real.log q.sigma).rpow (-q.y / 2) *
      ((q.k : ℝ).rpow ((q.y - 1) / 2) *
        max 1 ((Real.log q.theta).rpow (-1))) := by positivity
  have hthetaStep :
      z * (Real.log q.sigma).rpow (-q.y / 2) *
          ((q.k : ℝ).rpow ((q.y - 1) / 2) *
            (Real.log q.theta).rpow ((q.y - 1) / 2)) *
          (Real.log z).rpow (-1 / 2) ≤
      z * (Real.log q.sigma).rpow (-q.y / 2) *
          ((q.k : ℝ).rpow ((q.y - 1) / 2) *
            max 1 ((Real.log q.theta).rpow (-1))) *
          (Real.log z).rpow (-1 / 2) := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left htheta hkpow0)
        (mul_nonneg hz0 hs0)) hlogzpow0
  calc
    z * (Real.log q.sigma).rpow (-q.y / 2) *
          ((q.k : ℝ).rpow ((q.y - 1) / 2) *
            (Real.log q.theta).rpow ((q.y - 1) / 2)) *
          (Real.log z).rpow (-1 / 2)
        ≤ z * (Real.log q.sigma).rpow (-q.y / 2) *
          ((q.k : ℝ).rpow ((q.y - 1) / 2) *
            max 1 ((Real.log q.theta).rpow (-1))) *
          (Real.log z).rpow (-1 / 2) := hthetaStep
    _ ≤ z * (Real.log q.sigma).rpow (-q.y / 2) *
          ((q.k : ℝ).rpow ((q.y - 1) / 2) *
            max 1 ((Real.log q.theta).rpow (-1))) *
          (logLoss * (safeLog z).rpow (-1 / 2)) :=
      mul_le_mul_of_nonneg_left hsafe hprefix0
    _ = logLoss * max 1 ((Real.log q.theta).rpow (-1)) * z *
        (Real.log q.sigma).rpow (-q.y / 2) *
        (q.k : ℝ).rpow ((q.y - 1) / 2) *
        (safeLog z).rpow (-1 / 2) := by ring

theorem midAlgebra
    (q : WeightParameters) {z : ℝ} (hz : q.sigma ≤ z) :
    (z / Real.log z) *
      (Real.log z / Real.log q.sigma).rpow (q.y / 2) ≤
      logLoss * z * (Real.log q.sigma).rpow (-q.y / 2) *
        (safeLog z).rpow (q.y / 2 - 1) := by
  have hsigma2 : 2 ≤ q.sigma := q.theta_ge_two.trans q.sigma_ge_theta
  have hz2 : 2 ≤ z := hsigma2.trans hz
  have hls : 0 < Real.log q.sigma := Real.log_pos (one_lt_two.trans_le hsigma2)
  have hlz : 0 < Real.log z := Real.log_pos (one_lt_two.trans_le hz2)
  have he0 : q.y / 2 - 1 ≤ 0 := by linarith [q.y_lt_one]
  have he1 : -1 ≤ q.y / 2 - 1 := by linarith [q.y_pos]
  have hsafe := log_rpow_le_loss_safeLog hz2 he0 he1
  have hfac :
      (z / Real.log z) *
          (Real.log z / Real.log q.sigma).rpow (q.y / 2) =
        z * (Real.log q.sigma).rpow (-q.y / 2) *
          (Real.log z).rpow (q.y / 2 - 1) := by
    have hzdiv : z / Real.log z = z * (Real.log z).rpow (-1) := by
      rw [show (Real.log z).rpow (-1 : ℝ) = (Real.log z)⁻¹ by
        simpa using Real.rpow_neg_one (Real.log z)]
      ring
    have hzcombine : (Real.log z).rpow (-1) *
        (Real.log z).rpow (q.y / 2) =
        (Real.log z).rpow (q.y / 2 - 1) := by
      calc
        _ = (Real.log z).rpow ((-1 : ℝ) + q.y / 2) := rpow_mul_same hlz
        _ = _ := by ring_nf
    rw [hzdiv, rpow_div_pos hlz hls]
    rw [show -(q.y / 2) = -q.y / 2 by ring]
    calc
      z * (Real.log z).rpow (-1) *
          ((Real.log z).rpow (q.y / 2) *
            (Real.log q.sigma).rpow (-q.y / 2)) =
        z * (Real.log q.sigma).rpow (-q.y / 2) *
          ((Real.log z).rpow (-1) * (Real.log z).rpow (q.y / 2)) := by ring
      _ = _ := by rw [hzcombine]
  rw [hfac]
  have hprefix0 : 0 ≤ z * (Real.log q.sigma).rpow (-q.y / 2) :=
    mul_nonneg (zero_le_two.trans hz2) (Real.rpow_nonneg hls.le _)
  calc
    z * (Real.log q.sigma).rpow (-q.y / 2) *
        (Real.log z).rpow (q.y / 2 - 1)
      ≤ z * (Real.log q.sigma).rpow (-q.y / 2) *
        (logLoss * (safeLog z).rpow (q.y / 2 - 1)) :=
          mul_le_mul_of_nonneg_left hsafe hprefix0
    _ = logLoss * z * (Real.log q.sigma).rpow (-q.y / 2) *
        (safeLog z).rpow (q.y / 2 - 1) := by ring

theorem p055 (hP005 : P005Statement) (hP008 : P008Statement.{0})
    (chain : WeightChainSpec) (W : CommonWeightWitnesses)
    (h051H : P051HStatement) : P055Statement := by
  obtain ⟨P⟩ := hP005 (fun _ => W.LambdaStar)
    (fun _ => W.LambdaStar_pos.le) 1 zero_le_one (by norm_num)
  obtain ⟨B, hB, hEuler⟩ := productBounds hP008 W h051H
  intro theta htheta
  let Cup := P.constant * B ^ 2 * logLoss *
    max 1 ((Real.log theta).rpow (-1))
  have hCup : 0 < Cup := by
    dsimp [Cup]
    have hBpos : 0 < B := zero_lt_one.trans_le hB
    exact mul_pos (mul_pos (mul_pos P.constant_pos (sq_pos_of_pos hBpos))
      logLoss_pos) (zero_lt_one.trans_le (le_max_left _ _))
  refine ⟨Cup, hCup, ?_⟩
  intro q hq Ksh z hzH hsH
  have hz2 : 2 ≤ z :=
    q.theta_ge_two.trans (q.sigma_ge_theta.trans (hsH.trans hzH))
  let qi : RegularIndex :=
    { parameters := q, member := .w1, regular := hsH, z := z, z_ge_two := hz2 }
  have hraw := p005Raw W P q .w1 (by simpa [selectedWeight] using chain.w2_shift q) Ksh z hz2
  have he := (hEuler qi).2 hzH
  rw [show selectedWeight q .w1 = w1Weight by rfl,
    show maxShift w1Weight (modifierWeight q) = w2Weight q by rfl] at hraw
  calc
    Erdos448.Stage4.shiftedMean q z Ksh =
        Contracts.shiftedMean w1Weight (modifierWeight q) Ksh z :=
          stage4_shifted_eq_contract q Ksh z
    _
      ≤ P.constant * w2Weight q Ksh.1 * (z / Real.log z) *
          (∏ p ∈ strictPrimeRange z, regularEuler qi p) := by simpa [qi, regularEuler, selectedWeight] using hraw
    _ ≤ P.constant * w2Weight q Ksh.1 *
        ((z / Real.log z) *
          (B ^ 2 *
            (Real.log (q.theta ^ q.k) / Real.log q.sigma).rpow (q.y / 2) *
            (Real.log z / Real.log (q.theta ^ q.k)).rpow (1 / 2))) := by
          have hw2 : 0 ≤ w2Weight q Ksh.1 :=
            (W.weight_type q .w2).nonnegative_multiplicative.nonnegative Ksh.1 Ksh.2
          have hdiv : 0 ≤ z / Real.log z := div_nonneg
            (zero_le_two.trans hz2) (Real.log_nonneg (one_le_two.trans hz2))
          calc
            P.constant * w2Weight q Ksh.1 * (z / Real.log z) *
                (∏ p ∈ strictPrimeRange z, regularEuler qi p) ≤
              P.constant * w2Weight q Ksh.1 * (z / Real.log z) *
                (B ^ 2 *
                  (Real.log (q.theta ^ q.k) / Real.log q.sigma).rpow (q.y / 2) *
                  (Real.log z / Real.log (q.theta ^ q.k)).rpow (1 / 2)) :=
                mul_le_mul_of_nonneg_left he
                  (mul_nonneg (mul_nonneg P.constant_pos.le hw2) hdiv)
            _ = _ := by ring
    _ ≤ Cup * z * w2Weight q Ksh.1 *
        (Real.log q.sigma).rpow (-q.y / 2) *
        (q.k : ℝ).rpow ((q.y - 1) / 2) *
        (safeLog z).rpow (-1 / 2) := by
          have ha := upperAlgebra q hzH hsH
          have hw2 : 0 ≤ w2Weight q Ksh.1 :=
            (W.weight_type q .w2).nonnegative_multiplicative.nonnegative Ksh.1 Ksh.2
          have hcoef : 0 ≤ P.constant * B ^ 2 * w2Weight q Ksh.1 :=
            mul_nonneg (mul_nonneg P.constant_pos.le (sq_nonneg B)) hw2
          calc
            P.constant * w2Weight q Ksh.1 *
                ((z / Real.log z) *
                  (B ^ 2 *
                    (Real.log (q.theta ^ q.k) / Real.log q.sigma).rpow (q.y / 2) *
                    (Real.log z / Real.log (q.theta ^ q.k)).rpow (1 / 2))) =
              (P.constant * B ^ 2 * w2Weight q Ksh.1) *
                ((z / Real.log z) *
                  (Real.log (q.theta ^ q.k) / Real.log q.sigma).rpow (q.y / 2) *
                  (Real.log z / Real.log (q.theta ^ q.k)).rpow (1 / 2)) := by ring
            _ ≤ (P.constant * B ^ 2 * w2Weight q Ksh.1) *
                (logLoss * max 1 ((Real.log q.theta).rpow (-1)) * z *
                  (Real.log q.sigma).rpow (-q.y / 2) *
                  (q.k : ℝ).rpow ((q.y - 1) / 2) *
                  (safeLog z).rpow (-1 / 2)) :=
                    mul_le_mul_of_nonneg_left ha hcoef
            _ = Cup * z * w2Weight q Ksh.1 *
                (Real.log q.sigma).rpow (-q.y / 2) *
                (q.k : ℝ).rpow ((q.y - 1) / 2) *
                (safeLog z).rpow (-1 / 2) := by
                  dsimp [Cup]
                  rw [hq]
                  ring

theorem p056 (hP005 : P005Statement) (hP008 : P008Statement.{0})
    (chain : WeightChainSpec) (W : CommonWeightWitnesses)
    (h051H : P051HStatement) : P056Statement := by
  obtain ⟨P⟩ := hP005 (fun _ => W.LambdaStar)
    (fun _ => W.LambdaStar_pos.le) 1 zero_le_one (by norm_num)
  obtain ⟨B, hB, hEuler⟩ := productBounds hP008 W h051H
  intro theta htheta
  let Cmid := P.constant * B * logLoss
  have hCmid : 0 < Cmid := by
    dsimp [Cmid]
    exact mul_pos (mul_pos P.constant_pos (zero_lt_one.trans_le hB)) logLoss_pos
  refine ⟨Cmid, hCmid, ?_⟩
  intro q hq Ksh z hz hsig hzh
  have hz2 : 2 ≤ z :=
    q.theta_ge_two.trans (q.sigma_ge_theta.trans hsig)
  let qi : RegularIndex :=
    { parameters := q, member := .w1, regular := hsig.trans (le_of_lt hzh),
      z := z, z_ge_two := hz2 }
  have hraw := p005Raw W P q .w1 (by simpa [selectedWeight] using chain.w2_shift q) Ksh z hz2
  have he := (hEuler qi).1 hsig (le_of_lt hzh)
  rw [show selectedWeight q .w1 = w1Weight by rfl,
    show maxShift w1Weight (modifierWeight q) = w2Weight q by rfl] at hraw
  calc
    Erdos448.Stage4.shiftedMean q z Ksh =
        Contracts.shiftedMean w1Weight (modifierWeight q) Ksh z :=
          stage4_shifted_eq_contract q Ksh z
    _
      ≤ P.constant * w2Weight q Ksh.1 * (z / Real.log z) *
          (∏ p ∈ strictPrimeRange z, regularEuler qi p) := by simpa [qi, regularEuler, selectedWeight] using hraw
    _ ≤ P.constant * w2Weight q Ksh.1 *
        ((z / Real.log z) *
          (B * (Real.log z / Real.log q.sigma).rpow (q.y / 2))) := by
            have hw2 : 0 ≤ w2Weight q Ksh.1 :=
              (W.weight_type q .w2).nonnegative_multiplicative.nonnegative Ksh.1 Ksh.2
            have hdiv : 0 ≤ z / Real.log z := div_nonneg
              (zero_le_two.trans hz2) (Real.log_nonneg (one_le_two.trans hz2))
            calc
              P.constant * w2Weight q Ksh.1 * (z / Real.log z) *
                  (∏ p ∈ strictPrimeRange z, regularEuler qi p) ≤
                P.constant * w2Weight q Ksh.1 * (z / Real.log z) *
                  (B * (Real.log z / Real.log q.sigma).rpow (q.y / 2)) :=
                    mul_le_mul_of_nonneg_left he
                      (mul_nonneg (mul_nonneg P.constant_pos.le hw2) hdiv)
              _ = _ := by ring
    _ ≤ Cmid * z * w2Weight q Ksh.1 *
        (Real.log q.sigma).rpow (-q.y / 2) *
        (safeLog z).rpow (q.y / 2 - 1) := by
          have ha := midAlgebra q hsig
          have hw2 : 0 ≤ w2Weight q Ksh.1 :=
            (W.weight_type q .w2).nonnegative_multiplicative.nonnegative Ksh.1 Ksh.2
          have hcoef : 0 ≤ P.constant * B * w2Weight q Ksh.1 :=
            mul_nonneg (mul_nonneg P.constant_pos.le (zero_le_one.trans hB)) hw2
          calc
            P.constant * w2Weight q Ksh.1 *
                ((z / Real.log z) *
                  (B * (Real.log z / Real.log q.sigma).rpow (q.y / 2))) =
              (P.constant * B * w2Weight q Ksh.1) *
                ((z / Real.log z) *
                  (Real.log z / Real.log q.sigma).rpow (q.y / 2)) := by ring
            _ ≤ (P.constant * B * w2Weight q Ksh.1) *
                (logLoss * z * (Real.log q.sigma).rpow (-q.y / 2) *
                  (safeLog z).rpow (q.y / 2 - 1)) :=
                    mul_le_mul_of_nonneg_left ha hcoef
            _ = Cmid * z * w2Weight q Ksh.1 *
                (Real.log q.sigma).rpow (-q.y / 2) *
                (safeLog z).rpow (q.y / 2 - 1) := by
                  dsimp [Cmid]
                  ring

end

end Erdos448.Stage7.ROOT06.MainNodes
