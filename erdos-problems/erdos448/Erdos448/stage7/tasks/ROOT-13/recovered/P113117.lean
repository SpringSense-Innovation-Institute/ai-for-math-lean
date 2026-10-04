module

import all Mathlib.Basic.Real.Basic
public import Erdos448.stage6.TaskContracts

public section

set_option backward.isDefEq.respectTransparency false

namespace Erdos448.Stage7.ROOT13.Recovered.P113117

open Filter Finset Set
open scoped Topology

open Erdos448.Stage4
open Erdos448.Stage4.Contracts
open Erdos448.Stage6.TaskContracts

noncomputable section

lemma upperDensityAtMost_mono_bound {A : Set ℕ} {c d : ℝ}
    (hcd : c ≤ d) (hA : UpperDensityAtMost A c) :
    UpperDensityAtMost A d := by
  intro epsilon hepsilon
  filter_upwards [hA epsilon hepsilon] with x hx
  linarith

lemma prefixDensity_le_one (A : Set ℕ) (x : ℕ) :
    prefixDensity A x ≤ 1 := by
  classical
  by_cases hx : x = 0
  · subst x
    simp [prefixDensity, prefixCount]
  · have hxpos : (0 : ℝ) < x := by exact_mod_cast Nat.pos_of_ne_zero hx
    have hcard :
        ((Finset.range x).filter (fun n => 0 < n ∧ n ∈ A)).card ≤ x := by
      simpa using Finset.card_filter_le (Finset.range x) (fun n => 0 < n ∧ n ∈ A)
    unfold prefixDensity prefixCount
    rw [div_le_iff₀ hxpos]
    norm_num
    exact_mod_cast hcard

lemma every_upperDensityAtMost_one (A : Set ℕ) :
    UpperDensityAtMost A 1 := by
  intro epsilon hepsilon
  filter_upwards with x
  exact (prefixDensity_le_one A x).trans (by linarith)

lemma p113_proof : P113Statement := by
  intro delta hdelta_pos hdelta_lt_one
  let t : ℝ := delta / 100
  let y : ℝ := Real.exp (-t)
  have ht_pos : 0 < t := by
    dsimp [t]
    linarith
  have ht_lt : t < 1 / 100 := by
    dsimp [t]
    linarith
  have hy_pos : 0 < y := by
    dsimp [y]
    exact Real.exp_pos _
  have hy_lt_one : y < 1 := by
    dsimp [y]
    rw [Real.exp_lt_one_iff]
    linarith
  have hlog_y : Real.log y = -t := by
    simp [y]
  have hexp_lower : 1 + t < Real.exp t := by
    simpa [add_comm] using Real.add_one_lt_exp ht_pos.ne'
  have hone_add_pos : 0 < 1 + t := by linarith
  have hrecip : y < 1 / (1 + t) := by
    have hinv := one_div_lt_one_div_of_lt hone_add_pos hexp_lower
    simpa [y, Real.exp_neg, one_div] using hinv
  have hrecip_linear : 1 / (1 + t) < 1 - (3 / 5 : ℝ) * t := by
    rw [div_lt_iff₀ hone_add_pos]
    nlinarith [ht_pos, ht_lt]
  have hy_linear : y < 1 - (3 / 5 : ℝ) * t := hrecip.trans hrecip_linear
  have hadmissible :
      1 / 10 < -(1 - y + (1 / 2) * Real.log y) / Real.log y := by
    rw [hlog_y]
    have hnum : (1 / 10 : ℝ) * t < 1 - y - (1 / 2) * t := by
      nlinarith
    have hrewrite :
        -(1 - y + (1 / 2 : ℝ) * (-t)) / (-t) =
          (1 - y - (1 / 2) * t) / t := by
      field_simp [ht_pos.ne']
      <;> ring
    rw [hrewrite]
    exact (lt_div_iff₀ ht_pos).2 hnum
  have hden_pos : 0 < 0.009 - 0.6 * Real.log y := by
    rw [hlog_y]
    nlinarith
  have hexponent_loss :
      0.009 / (0.009 - 0.6 * Real.log y) ≥ 1 - delta := by
    rw [hlog_y]
    have hden_t : 0 < 0.009 - 0.6 * (-t) := by nlinarith
    apply (le_div_iff₀ hden_t).2
    dsimp [t]
    nlinarith [mul_self_nonneg delta]
  exact ⟨{
    y := y
    y_pos := hy_pos
    y_lt_one := hy_lt_one
    admissible := hadmissible
    exponent_loss := hexponent_loss
  }⟩

lemma p114_proof : P114Statement := by
  intro y alpha hy_pos hy_lt_one halpha_pos halpha_lt_one
  dsimp
  let a : ℝ := -0.6 * Real.log y
  let b : ℝ := 0.009
  let s : ℝ := a + b
  let L : ℝ := alpha.rpow (-1 / s)
  have hlog_y_neg : Real.log y < 0 := Real.log_neg hy_pos hy_lt_one
  have ha_pos : 0 < a := by
    dsimp [a]
    nlinarith
  have hb_pos : 0 < b := by norm_num [b]
  have hs_pos : 0 < s := by dsimp [s]; positivity
  have hL_pos : 0 < L := by
    dsimp [L]
    exact Real.rpow_pos_of_pos halpha_pos _
  have hL_power (z : ℝ) : L.rpow z = alpha.rpow ((-1 / s) * z) := by
    dsimp [L]
    change (alpha ^ (-1 / s)) ^ z = alpha ^ ((-1 / s) * z)
    exact (Real.rpow_mul halpha_pos.le _ _).symm
  have hfirst : alpha * L.rpow a = alpha.rpow (b / s) := by
    rw [hL_power]
    calc
      alpha * alpha.rpow ((-1 / s) * a) =
          alpha.rpow 1 * alpha.rpow ((-1 / s) * a) := by
            change alpha * alpha.rpow ((-1 / s) * a) =
              alpha ^ (1 : ℝ) * alpha.rpow ((-1 / s) * a)
            rw [Real.rpow_one]
      _ = alpha.rpow (1 + (-1 / s) * a) :=
        (Real.rpow_add halpha_pos _ _).symm
      _ = alpha.rpow (b / s) := by
        congr 1
        field_simp [hs_pos.ne']
        ring
  have hsecond : L.rpow (-b) = alpha.rpow (b / s) := by
    rw [hL_power]
    congr 1
    field_simp [hs_pos.ne']
  have hquotient : b / s = 0.009 / (0.009 - 0.6 * Real.log y) := by
    dsimp [a, b, s]
    ring
  change 0 < a ∧ 0 < b ∧ 0 < L ∧ Real.log (Real.exp L) = L ∧
    alpha * L.rpow a = L.rpow (-b) ∧
    L.rpow (-b) = alpha.rpow (b / s) ∧
    b / s = 0.009 / (0.009 - 0.6 * Real.log y)
  exact ⟨ha_pos, hb_pos, hL_pos, Real.log_exp L,
    hfirst.trans hsecond.symm, hsecond, hquotient⟩

lemma p116_proof : P116Statement := by
  intro delta alpha0 alpha hdelta_pos hdelta_lt_one halpha0_pos
    halpha0_le_one halpha0_le_alpha halpha_le_one
  constructor
  · exact every_upperDensityAtMost_one (densityEvent alpha)
  · have hexponent_pos : 0 < 1 - delta := by linarith
    have halpha0_power_pos : 0 < alpha0.rpow (-(1 - delta)) :=
      Real.rpow_pos_of_pos halpha0_pos _
    have hpower_mono :
        alpha0.rpow (1 - delta) ≤ alpha.rpow (1 - delta) :=
      Real.rpow_le_rpow halpha0_pos.le halpha0_le_alpha hexponent_pos.le
    have hmul := mul_le_mul_of_nonneg_left hpower_mono halpha0_power_pos.le
    calc
      1 = alpha0.rpow (-(1 - delta)) * alpha0.rpow (1 - delta) := by
        change 1 = alpha0 ^ (-(1 - delta)) * alpha0 ^ (1 - delta)
        rw [← Real.rpow_add halpha0_pos]
        norm_num
      _ ≤ alpha0.rpow (-(1 - delta)) * alpha.rpow (1 - delta) := hmul

lemma p115_proof (h112 : P112Statement) (h114 : P114Statement) :
    P115Statement := by
  intro delta hdelta_pos hdelta_lt_one selected
  let q : P112Parameters := {
    epsilonInt := 1 / 10
    epsilonInt_pos := by norm_num
    epsilonInt_le_tenth := le_rfl
    y := selected.y
    y_pos := selected.y_pos
    y_lt_one := selected.y_lt_one
    admissible := selected.admissible
  }
  obtain ⟨upstream⟩ := h112 q
  let a : ℝ := -0.6 * Real.log selected.y
  let b : ℝ := 0.009
  let s : ℝ := a + b
  have hlog_y_neg : Real.log selected.y < 0 :=
    Real.log_neg selected.y_pos selected.y_lt_one
  have ha_pos : 0 < a := by dsimp [a]; nlinarith
  have hb_pos : 0 < b := by norm_num [b]
  have hs_pos : 0 < s := by dsimp [s]; positivity
  have hXi0_pos : 0 < upstream.Xi0 :=
    (by norm_num : (0 : ℝ) < 1).trans upstream.Xi0_gt_one
  let cutoff : ℝ := upstream.Xi0.rpow (-s)
  let alpha0 : ℝ := min (2 / 5) cutoff
  have hcutoff_pos : 0 < cutoff := by
    dsimp [cutoff]
    exact Real.rpow_pos_of_pos hXi0_pos _
  have halpha0_pos : 0 < alpha0 := by
    dsimp [alpha0]
    exact lt_min (by norm_num) hcutoff_pos
  have halpha0_le_two_fifths : alpha0 ≤ 2 / 5 := min_le_left _ _
  let Csmall : ℝ := 2 * upstream.Cden
  have hCsmall_pos : 0 < Csmall := by
    dsimp [Csmall]
    nlinarith [upstream.Cden_pos]
  refine ⟨{
    Cgrid := upstream.Cgrid
    Cgrid_pos := upstream.Cgrid_pos
    Xi0 := upstream.Xi0
    Xi0_gt_one := upstream.Xi0_gt_one
    CP4 := upstream.CP4
    CP4_pos := upstream.CP4_pos
    Cden := upstream.Cden
    Cden_pos := upstream.Cden_pos
    alpha0 := alpha0
    alpha0_pos := halpha0_pos
    alpha0_le_two_fifths := halpha0_le_two_fifths
    Csmall := Csmall
    Csmall_pos := hCsmall_pos
    small_alpha_bound := ?_
  }⟩
  intro alpha halpha_pos halpha_lt_alpha0
  dsimp
  have halpha_lt_one : alpha < 1 :=
    halpha_lt_alpha0.trans_le <| halpha0_le_two_fifths.trans (by norm_num)
  obtain ⟨_, _, hL_pos, hlog_xi, hbalanced, hbalanced_power, hquotient⟩ :=
    h114 selected.y alpha selected.y_pos selected.y_lt_one
      halpha_pos halpha_lt_one
  have halpha_lt_cutoff : alpha < cutoff :=
    halpha_lt_alpha0.trans_le (min_le_right _ _)
  have hnegative_exponent : -1 / s < 0 :=
    div_neg_of_neg_of_pos (by norm_num) hs_pos
  have hthreshold_power :
      cutoff.rpow (-1 / s) < alpha.rpow (-1 / s) := by
    exact Real.rpow_lt_rpow_of_neg halpha_pos halpha_lt_cutoff hnegative_exponent
  have hcutoff_cancel : cutoff.rpow (-1 / s) = upstream.Xi0 := by
    dsimp [cutoff]
    rw [← Real.rpow_mul hXi0_pos.le]
    have : (-s) * (-1 / s) = 1 := by field_simp [hs_pos.ne']
    rw [this, Real.rpow_one]
  have hXi0_lt_L : upstream.Xi0 < alpha.rpow (-1 / s) := by
    rwa [hcutoff_cancel] at hthreshold_power
  have hXi0_le_xi : upstream.Xi0 ≤ Real.exp (alpha.rpow (-1 / s)) :=
    (hXi0_lt_L.trans (by linarith [Real.add_one_le_exp (alpha.rpow (-1 / s))])).le
  have hq_a : P112ABal q = a := by
    dsimp [P112ABal, q, a]
    ring
  have hq_b : P112BBal q = b := by
    dsimp [P112BBal, q, b]
    norm_num
  have halpha_le_two_fifths : alpha ≤ 2 / 5 :=
    (le_of_lt halpha_lt_alpha0).trans halpha0_le_two_fifths
  have hupstream := upstream.density_bound
    (Real.exp (alpha.rpow (-1 / s))) hXi0_le_xi alpha
    halpha_pos halpha_le_two_fifths
  rw [Real.log_exp, hq_a, hq_b] at hupstream
  refine ⟨hXi0_le_xi, ?_⟩
  change UpperDensityAtMost (densityEvent alpha)
      (Csmall * alpha.rpow (1 - delta))
  apply upperDensityAtMost_mono_bound _ hupstream
  rw [hbalanced, hbalanced_power, hquotient]
  have halpha_le_one : alpha ≤ 1 := halpha_lt_one.le
  have hpower_le :
      alpha.rpow (0.009 / (0.009 - 0.6 * Real.log selected.y)) ≤
        alpha.rpow (1 - delta) :=
    Real.rpow_le_rpow_of_exponent_ge halpha_pos halpha_le_one selected.exponent_loss
  dsimp [Csmall]
  have hsum_le := add_le_add hpower_le hpower_le
  calc
    upstream.Cden *
        (alpha.rpow (0.009 / (0.009 - 0.6 * Real.log selected.y)) +
          alpha.rpow (0.009 / (0.009 - 0.6 * Real.log selected.y))) ≤
      upstream.Cden *
        (alpha.rpow (1 - delta) + alpha.rpow (1 - delta)) :=
      mul_le_mul_of_nonneg_left hsum_le upstream.Cden_pos.le
    _ = 2 * upstream.Cden * alpha.rpow (1 - delta) := by ring

lemma p117_proof (h113 : P113Statement) (h115 : P115Statement)
    (h116 : P116Statement) : P117Statement := by
  intro delta hdelta_pos hdelta_lt_one
  obtain ⟨selected⟩ := h113 delta hdelta_pos hdelta_lt_one
  obtain ⟨small⟩ := h115 delta hdelta_pos hdelta_lt_one selected
  let Cdelta : ℝ :=
    max small.Csmall (small.alpha0.rpow (-(1 - delta)))
  have hcompact_pos : 0 < small.alpha0.rpow (-(1 - delta)) :=
    Real.rpow_pos_of_pos small.alpha0_pos _
  have hCdelta_pos : 0 < Cdelta := by
    dsimp [Cdelta]
    exact lt_of_lt_of_le small.Csmall_pos (le_max_left _ _)
  refine ⟨{
    constant := Cdelta
    constant_pos := hCdelta_pos
    bound := ?_
  }⟩
  intro alpha halpha_pos halpha_le_one
  by_cases halpha_small : alpha < small.alpha0
  · have hsmall := small.small_alpha_bound alpha halpha_pos halpha_small
    dsimp at hsmall
    exact upperDensityAtMost_mono_bound
      (mul_le_mul_of_nonneg_right (le_max_left _ _)
        (Real.rpow_nonneg halpha_pos.le (1 - delta))) hsmall.2
  · have halpha0_le_alpha : small.alpha0 ≤ alpha := le_of_not_gt halpha_small
    have hcompact := h116 delta small.alpha0 alpha hdelta_pos hdelta_lt_one
      small.alpha0_pos
      (small.alpha0_le_two_fifths.trans (by norm_num))
      halpha0_le_alpha halpha_le_one
    apply upperDensityAtMost_mono_bound _ hcompact.1
    have hcoeff : small.alpha0.rpow (-(1 - delta)) ≤ Cdelta :=
      le_max_right _ _
    have hpower_nonneg : 0 ≤ alpha.rpow (1 - delta) :=
      Real.rpow_nonneg halpha_pos.le _
    calc
      1 ≤ small.alpha0.rpow (-(1 - delta)) * alpha.rpow (1 - delta) :=
        hcompact.2
      _ ≤ Cdelta * alpha.rpow (1 - delta) :=
        mul_le_mul_of_nonneg_right hcoeff hpower_nonneg

theorem node_p113 : P113Statement :=
  p113_proof

theorem node_p114 : P114Statement :=
  p114_proof

theorem node_p115 (h112 : P112Statement) : P115Statement :=
  p115_proof h112 p114_proof

theorem node_p116 : P116Statement :=
  p116_proof

theorem node_p117 (h112 : P112Statement) : P117Statement :=
  p117_proof p113_proof (p115_proof h112 p114_proof) p116_proof

end

end Erdos448.Stage7.ROOT13.Recovered.P113117
