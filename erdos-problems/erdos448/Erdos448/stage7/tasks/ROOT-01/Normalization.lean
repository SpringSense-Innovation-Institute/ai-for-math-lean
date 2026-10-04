module

import all Mathlib.Basic.Real.Basic
public import Erdos448.stage7.tasks.«ROOT-01».ErrorProducts
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

public section

set_option backward.isDefEq.respectTransparency false

namespace Erdos448.Stage7.ROOT01

open Erdos448.Stage4
open Erdos448.Stage4.Contracts
open Finset Nat Set
open scoped BigOperators Topology

noncomputable section

lemma log_one_sub_quadratic
    {x : ℝ} (hx0 : 0 ≤ x) (hxhalf : x ≤ 1 / 2) :
    |Real.log (1 - x) + x| ≤ 2 * x ^ 2 := by
  have hxabs : |x| < 1 := by rw [abs_of_nonneg hx0]; linarith
  have h := Real.abs_log_sub_add_sum_range_le hxabs 1
  norm_num at h
  rw [abs_of_nonneg hx0] at h
  have hden : 1 / 2 ≤ 1 - x := by linarith
  have hx2 : 0 ≤ x ^ 2 := sq_nonneg x
  calc
    |Real.log (1 - x) + x| = |x + Real.log (1 - x)| := by rw [add_comm]
    _ ≤ x ^ 2 / (1 - x) := h
    _ ≤ 2 * x ^ 2 := by
      apply (div_le_iff₀ (by linarith : 0 < 1 - x)).2
      nlinarith

lemma abs_log_one_sub_le
    {x : ℝ} (hx0 : 0 ≤ x) (hxhalf : x ≤ 1 / 2) :
    |Real.log (1 - x)| ≤ 2 * x := by
  have hq := log_one_sub_quadratic hx0 hxhalf
  calc
    |Real.log (1 - x)| = |(Real.log (1 - x) + x) - x| := by ring_nf
    _ ≤ |Real.log (1 - x) + x| + |x| := abs_sub _ _
    _ ≤ 2 * x ^ 2 + x := by rw [abs_of_nonneg hx0]; gcongr
    _ ≤ 2 * x := by nlinarith [sq_nonneg x]

lemma normalizedLinearFactor_bound
    {K c x : ℝ} (hK : 0 ≤ K) (hc : |c| ≤ K)
    (hx0 : 0 ≤ x) (hxsmall : x ≤ 1 / (4 * (K + 1))) :
    |(1 + c * x) * (1 - x).rpow c - 1| ≤
      20 * (K + 1) ^ 2 * x ^ 2 := by
  have hK1 : 1 ≤ K + 1 := by linarith
  have hden : 0 < 4 * (K + 1) := mul_pos (by norm_num) (by linarith)
  have hxquarter : x ≤ 1 / 4 := by
    calc x ≤ 1 / (4 * (K + 1)) := hxsmall
      _ ≤ 1 / 4 := by
        apply one_div_le_one_div_of_le (by norm_num) (by nlinarith)
  have hxhalf : x ≤ 1 / 2 := hxquarter.trans (by norm_num)
  have hbase : 0 < 1 - x := by linarith
  let z := c * Real.log (1 - x)
  have hzabs : |z| ≤ 2 * K * x := by
    dsimp [z]
    rw [abs_mul]
    calc
      |c| * |Real.log (1 - x)| ≤ K * (2 * x) :=
        mul_le_mul hc (abs_log_one_sub_le hx0 hxhalf) (abs_nonneg _) hK
      _ = 2 * K * x := by ring
  have hKx : K * x ≤ 1 / 4 := by
    have hmul := mul_le_mul_of_nonneg_left hxsmall hK
    calc
      K * x ≤ K * (1 / (4 * (K + 1))) := hmul
      _ ≤ 1 / 4 := by
        rw [one_div, ← div_eq_mul_inv]
        apply (div_le_iff₀ hden).2
        nlinarith
  have hzone : |z| ≤ 1 := hzabs.trans (by linarith)
  have hdelta : |z + c * x| ≤ 2 * K * x ^ 2 := by
    dsimp [z]
    rw [← mul_add, abs_mul]
    calc
      |c| * |Real.log (1 - x) + x| ≤ K * (2 * x ^ 2) :=
        mul_le_mul hc (log_one_sub_quadratic hx0 hxhalf) (abs_nonneg _) hK
      _ = 2 * K * x ^ 2 := by ring
  have hexp1 := Real.abs_exp_sub_one_le hzone
  have hexp2 := Real.abs_exp_sub_one_sub_id_le hzone
  rw [show (1 - x).rpow c = Real.exp (Real.log (1 - x) * c) by
    exact Real.rpow_def_of_pos hbase c]
  have hzexp : Real.exp (Real.log (1 - x) * c) = Real.exp z := by
    congr 1
    dsimp [z]
    ring
  rw [hzexp]
  have hrewrite :
      (1 + c * x) * Real.exp z - 1 =
        (Real.exp z - 1 - z) + (z + c * x) +
          (c * x) * (Real.exp z - 1) := by ring
  rw [hrewrite]
  calc
    |(Real.exp z - 1 - z) + (z + c * x) +
        (c * x) * (Real.exp z - 1)| ≤
        |Real.exp z - 1 - z| + |z + c * x| +
          |c * x| * |Real.exp z - 1| := by
      calc
        _ ≤ |Real.exp z - 1 - z| + |z + c * x| +
            |(c * x) * (Real.exp z - 1)| := abs_add_three _ _ _
        _ = _ := by rw [abs_mul]
    _ ≤ z ^ 2 + 2 * K * x ^ 2 + |c * x| * (2 * |z|) := by gcongr
    _ ≤ (2 * K * x) ^ 2 + 2 * K * x ^ 2 +
          (K * x) * (2 * (2 * K * x)) := by
      have hKx0 : 0 ≤ 2 * K * x := by positivity
      have hz2 : z ^ 2 ≤ (2 * K * x) ^ 2 := by
        rw [← sq_abs z]
        exact (sq_le_sq₀ (abs_nonneg z) hKx0).2 hzabs
      have hcabs : |c * x| ≤ K * x := by
        rw [abs_mul, abs_of_nonneg hx0]
        exact mul_le_mul_of_nonneg_right hc hx0
      have htwoz : 2 * |z| ≤ 2 * (2 * K * x) :=
        mul_le_mul_of_nonneg_left hzabs (by norm_num)
      exact add_le_add (add_le_add hz2 le_rfl)
        (mul_le_mul hcabs htwoz
          (mul_nonneg (by norm_num) (abs_nonneg z)) (mul_nonneg hK hx0))
    _ ≤ 20 * (K + 1) ^ 2 * x ^ 2 := by
      nlinarith [sq_nonneg K, sq_nonneg x, mul_nonneg hK hx0]

lemma normalizedPrimeFactor_bound
    {K c : ℝ} (hK : 0 ≤ K) (hc : |c| ≤ K)
    {p : ℕ} (hp : p.Prime) (hpLarge : 4 * (K + 1) ≤ (p : ℝ)) :
    |(1 + c / p) * (mertensFactor p).rpow c - 1| ≤
      20 * (K + 1) ^ 2 * (p : ℝ).rpow (-2) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hx0 : 0 ≤ (1 / (p : ℝ)) := by positivity
  have hxsmall : 1 / (p : ℝ) ≤ 1 / (4 * (K + 1)) := by
    exact one_div_le_one_div_of_le (by positivity) hpLarge
  have h := normalizedLinearFactor_bound hK hc hx0 hxsmall
  unfold mertensFactor
  rw [div_eq_mul_inv]
  convert h using 1
  · ring
  · have hrpow : (p : ℝ).rpow (-2) = (1 / (p : ℝ)) ^ 2 := by
      change (p : ℝ) ^ (-2 : ℝ) = _
      rw [show (-2 : ℝ) = -(2 : ℕ) by norm_num, Real.rpow_neg_natCast]
      norm_num [zpow_neg]
    rw [hrpow]

lemma mertensFactor_rpow_upper
    {K c : ℝ} (hK : 0 ≤ K) (hc : |c| ≤ K)
    {p : ℕ} (hp : p.Prime) :
    (mertensFactor p).rpow c ≤ Real.exp K := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le (by norm_num) hp2
  have hx0 : 0 ≤ (1 / (p : ℝ)) := by positivity
  have hxhalf : 1 / (p : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp2
  have hbase : 0 < mertensFactor p := by
    unfold mertensFactor
    exact sub_pos.mpr ((div_lt_iff₀ hp0).2 (by nlinarith))
  rw [show (mertensFactor p).rpow c =
      Real.exp (Real.log (mertensFactor p) * c) by
    exact Real.rpow_def_of_pos hbase c]
  apply Real.exp_le_exp.mpr
  calc
    Real.log (mertensFactor p) * c ≤
        |Real.log (mertensFactor p) * c| := le_abs_self _
    _ = |Real.log (mertensFactor p)| * |c| := abs_mul _ _
    _ ≤ (2 * (1 / (p : ℝ))) * K := by
      unfold mertensFactor
      exact mul_le_mul (abs_log_one_sub_le hx0 hxhalf) hc (abs_nonneg _) (by positivity)
    _ ≤ K := by
      have htwo : 2 * (1 / (p : ℝ)) ≤ 1 := by
        rw [one_div, ← div_eq_mul_inv]
        apply (div_le_iff₀ hp0).2
        nlinarith
      nlinarith

lemma normalizedLocalFactor_bound
    {K c eta CErr : ℝ} (hK : 0 ≤ K) (hc : |c| ≤ K)
    (heta : 0 < eta) (hCErr : 0 ≤ CErr)
    (L : ℕ → ℝ) {p : ℕ} (hp : p.Prime)
    (hpLarge : 4 * (K + 1) ≤ (p : ℝ))
    (herror : |L p - (1 + c / p)| ≤
      CErr * (p : ℝ).rpow (-1 - eta)) :
    |L p * (mertensFactor p).rpow c - 1| ≤
      (CErr * Real.exp K + 20 * (K + 1) ^ 2) *
        (p : ℝ).rpow (-1 - min eta 1) := by
  let M := (mertensFactor p).rpow c
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
  have hmert0 : 0 ≤ mertensFactor p := by
    unfold mertensFactor
    apply sub_nonneg.mpr
    apply (div_le_iff₀ (lt_of_lt_of_le zero_lt_one hp1)).2
    nlinarith
  have hM0 : 0 ≤ M := Real.rpow_nonneg hmert0 c
  have hMle : M ≤ Real.exp K := mertensFactor_rpow_upper hK hc hp
  have hnorm := normalizedPrimeFactor_bound hK hc hp hpLarge
  have hid : L p * M - 1 =
      (L p - (1 + c / p)) * M + ((1 + c / p) * M - 1) := by ring
  have hraw : |L p * M - 1| ≤
      CErr * Real.exp K * (p : ℝ).rpow (-1 - eta) +
        20 * (K + 1) ^ 2 * (p : ℝ).rpow (-2) := by
    rw [hid]
    calc
      |(L p - (1 + c / p)) * M + ((1 + c / p) * M - 1)| ≤
          |L p - (1 + c / p)| * M + |(1 + c / p) * M - 1| := by
        calc
          _ ≤ |(L p - (1 + c / p)) * M| + |(1 + c / p) * M - 1| :=
            abs_add_le _ _
          _ = _ := by rw [abs_mul, abs_of_nonneg hM0]
      _ ≤ (CErr * (p : ℝ).rpow (-1 - eta)) * Real.exp K +
          20 * (K + 1) ^ 2 * (p : ℝ).rpow (-2) := by
        exact add_le_add
          (mul_le_mul herror hMle hM0
            (mul_nonneg hCErr (Real.rpow_nonneg (Nat.cast_nonneg p) _)))
          hnorm
      _ = _ := by ring
  have hmuEta : -1 - eta ≤ -1 - min eta 1 := by
    linarith [min_le_left eta 1]
  have hmuOne : (-2 : ℝ) ≤ -1 - min eta 1 := by
    have := min_le_right eta 1
    linarith
  have hpowEta : (p : ℝ).rpow (-1 - eta) ≤
      (p : ℝ).rpow (-1 - min eta 1) :=
    Real.rpow_le_rpow_of_exponent_le hp1 hmuEta
  have hpowTwo : (p : ℝ).rpow (-2) ≤
      (p : ℝ).rpow (-1 - min eta 1) :=
    Real.rpow_le_rpow_of_exponent_le hp1 hmuOne
  calc
    |L p * M - 1| ≤ _ := hraw
    _ ≤ CErr * Real.exp K * (p : ℝ).rpow (-1 - min eta 1) +
        20 * (K + 1) ^ 2 * (p : ℝ).rpow (-1 - min eta 1) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hpowEta
          (mul_nonneg hCErr (Real.exp_pos K).le))
        (mul_le_mul_of_nonneg_left hpowTwo (by positivity))
    _ = _ := by ring

end

end Erdos448.Stage7.ROOT01
