module

import all Mathlib.Basic.Real.Basic
public import Erdos448.stage6.TaskContracts

public section

set_option backward.isDefEq.respectTransparency false

namespace Erdos448.Stage7.ROOT07.Family

open Finset
open scoped BigOperators

open Erdos448.Stage4
open Erdos448.Stage4.Contracts

noncomputable section

@[expose] def adaptWeightType {w : ArithmeticWeight} {c C Lambda : ℝ}
    (h : WeightTypeSpec w c C Lambda) : P070WeightTypeSpec w c C Lambda where
  nonnegative_multiplicative := h.nonnegative_multiplicative
  normalized := h.normalized
  prime_power_error := by
    intro p hp i hi
    simpa only [Nat.cast_add, Nat.cast_one] using h.prime_power p hp i hi
  prime_power_bounds := h.prime_power_bounds

@[expose] def exampleParameters : WeightParameters where
  theta := 2
  theta_ge_two := le_rfl
  y := 1 / 2
  y_pos := by norm_num
  y_lt_one := by norm_num
  k := 1
  k_pos := le_rfl
  sigma := 2
  sigma_ge_theta := le_rfl

lemma window_le_prefix (W : CommonWeightWitnesses)
    (q : WeightParameters) :
    w4WindowSum q <= familyPartialSum w4Weight q (q.theta ^ (q.k + 2)) := by
  unfold w4WindowSum familyPartialSum
  apply Finset.sum_le_sum
  intro r hr
  split
  · exact le_rfl
  · exact (W.weight_type q .w4).nonnegative_multiplicative.nonnegative r
      (Finset.mem_filter.mp hr).2.1

lemma endpoint_bound (C : ℝ) (hC : 0 < C)
    (q : WeightParameters) :
    C * q.theta ^ (q.k + 2) *
        (Real.log (q.theta ^ (q.k + 2))).rpow (-1 / 2) <=
      p070C4
          { Cfam := C, Cfam_pos := hC,
            theta := q.theta, theta_ge_two := q.theta_ge_two } *
        q.theta ^ q.k * (q.k : ℝ).rpow (-1 / 2) := by
  have htheta_pos : 0 < q.theta := lt_of_lt_of_le (by norm_num) q.theta_ge_two
  have hlog_pos : 0 < Real.log q.theta :=
    Real.log_pos (lt_of_lt_of_le (by norm_num) q.theta_ge_two)
  have hk_pos : 0 < (q.k : ℝ) := by exact_mod_cast q.k_pos
  have hk2_pos : 0 < (q.k + 2 : ℝ) := by positivity
  have hlogpow : Real.log (q.theta ^ (q.k + 2)) =
      (q.k + 2 : ℝ) * Real.log q.theta := by
    simpa using Real.log_pow q.theta (q.k + 2)
  have hbase : (q.k : ℝ) * Real.log q.theta <=
      Real.log (q.theta ^ (q.k + 2)) := by
    rw [hlogpow]
    nlinarith [hlog_pos]
  have hsmall_pos : 0 < (q.k : ℝ) * Real.log q.theta := mul_pos hk_pos hlog_pos
  have hrpow :
      (Real.log (q.theta ^ (q.k + 2))).rpow (-1 / 2) <=
        ((q.k : ℝ) * Real.log q.theta).rpow (-1 / 2) := by
    exact Real.rpow_le_rpow_of_nonpos hsmall_pos hbase (by norm_num)
  have hfactor : ((q.k : ℝ) * Real.log q.theta).rpow (-1 / 2) =
      (q.k : ℝ).rpow (-1 / 2) / Real.sqrt (Real.log q.theta) := by
    calc
      ((q.k : ℝ) * Real.log q.theta).rpow (-1 / 2) =
          (q.k : ℝ).rpow (-1 / 2) *
            (Real.log q.theta).rpow (-1 / 2) :=
        Real.mul_rpow (le_of_lt hk_pos) (le_of_lt hlog_pos)
      _ = (q.k : ℝ).rpow (-1 / 2) / Real.sqrt (Real.log q.theta) := by
        have hneg : (Real.log q.theta).rpow (-(1 / 2)) =
            ((Real.log q.theta).rpow (1 / 2))⁻¹ :=
          Real.rpow_neg (le_of_lt hlog_pos) (1 / 2)
        have hsqrt : Real.sqrt (Real.log q.theta) =
            (Real.log q.theta).rpow (1 / 2) :=
          Real.sqrt_eq_rpow (Real.log q.theta)
        rw [show (-1 / 2 : ℝ) = -(1 / 2) by ring, hneg, hsqrt]
        ring
  have hpow : q.theta ^ (q.k + 2) = q.theta ^ 2 * q.theta ^ q.k := by
    rw [pow_add]
    ring
  unfold p070C4
  dsimp
  calc
    C * q.theta ^ (q.k + 2) *
          (Real.log (q.theta ^ (q.k + 2))).rpow (-1 / 2) <=
        C * q.theta ^ (q.k + 2) *
          ((q.k : ℝ).rpow (-1 / 2) / Real.sqrt (Real.log q.theta)) := by
      gcongr
      exact hrpow.trans_eq hfactor
    _ = C * q.theta ^ 2 / Real.sqrt (Real.log q.theta) *
          q.theta ^ q.k * (q.k : ℝ).rpow (-1 / 2) := by
      rw [hpow]
      ring

theorem p070 (W : CommonWeightWitnesses) (h059 : P059Statement.{0}) :
    P070Statement := by
  let common : P070CommonWeightWitnesses :=
    { cStar := W.cStar
      CStar := W.CStar
      LambdaStar := W.LambdaStar
      cStar_pos := W.cStar_pos
      CStar_pos := W.CStar_pos
      LambdaStar_pos := W.LambdaStar_pos
      a0_type := adaptWeightType (W.weight_type exampleParameters .a0)
      w1_type := adaptWeightType (W.weight_type exampleParameters .w1)
      w2_type := fun q => adaptWeightType (W.weight_type q .w2)
      w3_type := fun q => adaptWeightType (W.weight_type q .w3)
      w4_type := fun q => adaptWeightType (W.weight_type q .w4) }
  obtain ⟨Cmean, hCmean, hmean⟩ :=
    h059 WeightParameters w4Weight ⟨exampleParameters⟩
      W.cStar W.CStar W.LambdaStar W.cStar_pos W.CStar_pos W.LambdaStar_pos
      (fun q => W.weight_type q .w4)
  refine ⟨{
    common := common
    Cfam := Cmean
    Cfam_pos := hCmean
    c4_positive := ?_
    family_mean := ?_
    window := ?_ }⟩
  · intro theta htheta
    unfold p070C4
    have htheta_pos : 0 < theta := lt_of_lt_of_le (by norm_num) htheta
    have hlog_pos : 0 < Real.log theta :=
      Real.log_pos (lt_of_lt_of_le (by norm_num) htheta)
    positivity
  · intro q Z hZ
    exact hmean q Z hZ
  · intro q
    have htop : 2 <= q.theta ^ (q.k + 2) := by
      calc
        2 <= q.theta := q.theta_ge_two
        _ <= q.theta ^ (q.k + 2) := by
          have htheta_one : 1 <= q.theta := by linarith [q.theta_ge_two]
          have hpow_one : 1 <= q.theta ^ (q.k + 1) := one_le_pow₀ htheta_one
          rw [show q.k + 2 = 1 + (q.k + 1) by omega, pow_add]
          nlinarith
    calc
      w4WindowSum q <= familyPartialSum w4Weight q (q.theta ^ (q.k + 2)) :=
        window_le_prefix W q
      _ <= Cmean * q.theta ^ (q.k + 2) *
          (Real.log (q.theta ^ (q.k + 2))).rpow (-1 / 2) := hmean q _ htop
      _ <= p070C4
          { Cfam := Cmean, Cfam_pos := hCmean,
            theta := q.theta, theta_ge_two := q.theta_ge_two } *
          q.theta ^ q.k * (q.k : ℝ).rpow (-1 / 2) :=
        endpoint_bound Cmean hCmean q

end

end Erdos448.Stage7.ROOT07.Family
