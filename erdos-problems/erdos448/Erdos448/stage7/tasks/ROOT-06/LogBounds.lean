module

import all Mathlib.Basic.Real.Basic
public import Erdos448.stage6.TaskContracts

public section

set_option backward.isDefEq.respectTransparency false

namespace Erdos448.Stage7.ROOT06.LogBounds

open Erdos448.Stage4

noncomputable section

@[expose] def logLoss : ℝ := (Real.log 2)⁻¹

theorem logLoss_pos : 0 < logLoss := inv_pos.mpr (Real.log_pos one_lt_two)

theorem logLoss_ge_one : 1 ≤ logLoss := by
  have hlog2pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlog2le : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  exact (one_le_inv₀ hlog2pos).2 hlog2le

theorem log_rpow_le_loss_safeLog
    {x e : ℝ} (hx : 2 ≤ x) (he0 : e ≤ 0) (he1 : -1 ≤ e) :
    (Real.log x).rpow e ≤ logLoss * (safeLog x).rpow e := by
  have hlog2pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlogxpos : 0 < Real.log x := Real.log_pos (one_lt_two.trans_le hx)
  have hlog2x : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  by_cases hx1 : 1 ≤ Real.log x
  · rw [safeLog, max_eq_right hx1]
    exact (le_mul_iff_one_le_left (Real.rpow_pos_of_pos hlogxpos e)).2 logLoss_ge_one
  · have hlogx1 : Real.log x < 1 := lt_of_not_ge hx1
    rw [safeLog, max_eq_left (le_of_not_ge hx1)]
    have hone : Real.rpow 1 e = 1 := Real.one_rpow e
    rw [hone, mul_one]
    have hinv : (Real.log x).rpow e ≤ (Real.log x)⁻¹ := by
      rw [← Real.rpow_neg_one]
      exact Real.rpow_le_rpow_of_exponent_ge hlogxpos hlogx1.le he1
    change (Real.log x).rpow e ≤ (Real.log 2)⁻¹
    exact hinv.trans ((inv_le_inv₀ hlogxpos hlog2pos).2 hlog2x)

end

end Erdos448.Stage7.ROOT06.LogBounds
