module

import all Mathlib.Basic.Real.Basic
public import Erdos448.stage4.contracts.GroupA

public section

set_option backward.isDefEq.respectTransparency false

namespace Erdos448.Stage7.ROOT02.Threshold

open Filter
open Erdos448.Stage4
open Erdos448.Stage4.Contracts

theorem p017 : P017Statement := by
  intro q
  have hepsilon : 0 < 0.01 * q.epsilonInt :=
    mul_pos (by norm_num) q.epsilonInt_pos
  have hloglog :
      Tendsto (fun xi : ℝ => Real.log (Real.log xi)) atTop atTop :=
    Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  have hinv :
      Tendsto (fun xi : ℝ => 1 / Real.log (Real.log xi)) atTop (nhds 0) := by
    simpa only [one_div, Pi.inv_def] using hloglog.inv_tendsto_atTop
  have hsmallLog :
      ∀ᶠ xi : ℝ in atTop,
        1 / Real.log (Real.log xi) < 0.01 * q.epsilonInt :=
    hinv.eventually_lt_const hepsilon
  have halpha : 0 < 0.001 * q.epsilonInt ^ 2 :=
    mul_pos (by norm_num) (sq_pos_of_pos q.epsilonInt_pos)
  have hrpow :
      Tendsto
        (fun xi : ℝ =>
          (Real.log xi).rpow (-(0.001 * q.epsilonInt ^ 2)))
        atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop halpha).comp Real.tendsto_log_atTop
  have hscaled :
      Tendsto
        (fun xi : ℝ =>
          10 * q.Cgrid *
            (Real.log xi).rpow (-(0.001 * q.epsilonInt ^ 2)))
        atTop (nhds 0) := by
    simpa [mul_assoc] using hrpow.const_mul (10 * q.Cgrid)
  have hsmallPow :
      ∀ᶠ xi : ℝ in atTop,
        10 * q.Cgrid *
            (Real.log xi).rpow (-(0.001 * q.epsilonInt ^ 2)) < 1 :=
    hscaled.eventually_lt_const zero_lt_one
  have hlarge : ∀ᶠ xi : ℝ in atTop, Real.exp 1 < xi :=
    eventually_gt_atTop (Real.exp 1)
  have hall := hlarge.and (hsmallLog.and hsmallPow)
  rcases Filter.eventually_atTop.1 hall with ⟨X, hX⟩
  let Xi0 : ℝ := max X (Real.exp 1 + 1)
  have hXi0_exp : Real.exp 1 < Xi0 := by
    dsimp [Xi0]
    exact lt_of_lt_of_le (lt_add_one _) (le_max_right _ _)
  have hXi0_one : 1 < Xi0 :=
    lt_trans (Real.one_lt_exp_iff.mpr zero_lt_one) hXi0_exp
  refine ⟨{
    Xi0 := Xi0
    Xi0_gt_one := hXi0_one
    threshold_spec := ?_
  }⟩
  refine ⟨hXi0_one, ?_⟩
  intro xi hxi
  have hXXi0 : X ≤ Xi0 := by
    dsimp [Xi0]
    exact le_max_left _ _
  have hXxi : X ≤ xi := hXXi0.trans hxi
  rcases hX xi hXxi with ⟨hxi_exp, hxi_log, hxi_pow⟩
  refine ⟨hxi_exp, hxi_log.le, ?_⟩
  have hlog_pos : 0 < Real.log xi :=
    Real.log_pos (lt_trans (Real.one_lt_exp_iff.mpr zero_lt_one) hxi_exp)
  have hexponent :
      -0.901 * q.epsilonInt ^ 2 =
        (-0.9 * q.epsilonInt ^ 2) +
          (-(0.001 * q.epsilonInt ^ 2)) := by ring
  rw [hexponent]
  have hrpow_add :
      (Real.log xi).rpow
          ((-0.9 * q.epsilonInt ^ 2) + (-(0.001 * q.epsilonInt ^ 2))) =
        (Real.log xi).rpow (-0.9 * q.epsilonInt ^ 2) *
          (Real.log xi).rpow (-(0.001 * q.epsilonInt ^ 2)) :=
    Real.rpow_add hlog_pos _ _
  rw [hrpow_add]
  calc
    10 * q.Cgrid *
          ((Real.log xi).rpow (-0.9 * q.epsilonInt ^ 2) *
            (Real.log xi).rpow (-(0.001 * q.epsilonInt ^ 2))) =
        (10 * q.Cgrid *
            (Real.log xi).rpow (-(0.001 * q.epsilonInt ^ 2))) *
          (Real.log xi).rpow (-0.9 * q.epsilonInt ^ 2) := by ring
    _ ≤ 1 * (Real.log xi).rpow (-0.9 * q.epsilonInt ^ 2) := by
      exact mul_le_mul_of_nonneg_right hxi_pow.le (Real.rpow_nonneg hlog_pos.le _)
    _ = (Real.log xi).rpow (-0.9 * q.epsilonInt ^ 2) := one_mul _

end Erdos448.Stage7.ROOT02.Threshold
