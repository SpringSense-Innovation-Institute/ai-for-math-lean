module

import all Mathlib.Basic.Real.Basic
public import Erdos448.stage6.TaskContracts

public section

set_option backward.isDefEq.respectTransparency false

namespace Erdos448.Stage7.ROOT13.Recovered.P120FT

open Filter Finset Set
open scoped Topology

open Erdos448.Stage4
open Erdos448.Stage4.Contracts
open Erdos448.Stage6.TaskContracts

noncomputable section

lemma prefixDensity_mono {A B : Set ℕ} (hAB : A ⊆ B) (x : ℕ) :
    prefixDensity A x ≤ prefixDensity B x := by
  classical
  unfold prefixDensity
  apply div_le_div_of_nonneg_right
  · exact_mod_cast Finset.card_le_card (show
      (Finset.range x).filter (fun n => 0 < n ∧ n ∈ A) ⊆
        (Finset.range x).filter (fun n => 0 < n ∧ n ∈ B) by
      intro n hn
      simp only [Finset.mem_filter, Finset.mem_range] at hn ⊢
      exact ⟨hn.1, hn.2.1, hAB hn.2.2⟩)
  · positivity

lemma upperDensityAtMost_mono {A B : Set ℕ} {c : ℝ}
    (hAB : A ⊆ B) (hB : UpperDensityAtMost B c) :
    UpperDensityAtMost A c := by
  intro epsilon hepsilon
  filter_upwards [hB epsilon hepsilon] with x hx
  exact (prefixDensity_mono hAB x).trans hx

lemma strictEvent_subset_densityEvent (alpha : ℝ) :
    strictEvent alpha ⊆ densityEvent alpha := by
  intro n hn
  simp only [strictEvent, densityEvent, Set.mem_setOf_eq] at hn ⊢
  by_cases hnpos : 0 < n
  · simp only [hnpos, ↓reduceDIte] at hn ⊢
    exact hn.le
  · simp only [hnpos, ↓reduceDIte] at hn

lemma coefficient_rpow_lt_one
    {C delta alpha : ℝ} (hC : 0 < C) (hdelta : delta < 1)
    (halpha : 0 < alpha)
    (halpha_cutoff : alpha < C.rpow (-1 / (1 - delta))) :
    C * alpha.rpow (1 - delta) < 1 := by
  have hexponent : 0 < 1 - delta := sub_pos.mpr hdelta
  have hC0 : 0 ≤ C := hC.le
  have hcutoff_power :
      (C.rpow (-1 / (1 - delta))).rpow (1 - delta) = C⁻¹ := by
    change (C ^ (-1 / (1 - delta))) ^ (1 - delta) = C⁻¹
    rw [← Real.rpow_mul hC0 (-1 / (1 - delta)) (1 - delta)]
    have hne : 1 - delta ≠ 0 := ne_of_gt hexponent
    rw [show (-1 / (1 - delta)) * (1 - delta) = -1 by field_simp]
    exact Real.rpow_neg_one C
  have halpha_power :
      alpha.rpow (1 - delta) < C⁻¹ := by
    rw [← hcutoff_power]
    exact Real.rpow_lt_rpow halpha.le halpha_cutoff hexponent
  have hscaled : C * alpha.rpow (1 - delta) < C * C⁻¹ := by
    have hgap : 0 < C⁻¹ - alpha.rpow (1 - delta) :=
      sub_pos.mpr halpha_power
    have hpositive_product : 0 < C * (C⁻¹ - alpha.rpow (1 - delta)) :=
      mul_pos hC hgap
    nlinarith
  calc
    C * alpha.rpow (1 - delta) < C * C⁻¹ := hscaled
    _ = 1 := mul_inv_cancel₀ hC.ne'

lemma not_density_one_of_upperDensityLtOne {A : Set ℕ}
    (hsmall : UpperDensityLtOne A) : ¬ HasNaturalDensity A 1 := by
  rintro hdensity
  obtain ⟨c, hc, hupper⟩ := hsmall
  let b : ℝ := (c + 1) / 2
  let epsilon : ℝ := (1 - c) / 4
  have hb : b < 1 := by
    dsimp [b]
    linarith
  have hepsilon : 0 < epsilon := by
    dsimp [epsilon]
    linarith
  have hlower : ∀ᶠ x : ℕ in atTop, b < prefixDensity A x :=
    hdensity.eventually_const_lt hb
  have hupper' : ∀ᶠ x : ℕ in atTop, prefixDensity A x ≤ c + epsilon :=
    hupper epsilon hepsilon
  obtain ⟨x, hx_lower, hx_upper⟩ := (hlower.and hupper').exists
  dsimp [b, epsilon] at hx_lower hx_upper
  linarith

lemma p120_of_p117 (h117 : P117Statement) : P120Statement := by
  let delta : ℝ := 1 / 2
  have hdelta_pos : 0 < delta := by
    norm_num [delta]
  have hdelta_lt_one : delta < 1 := by
    norm_num [delta]
  obtain ⟨interior⟩ := h117 delta hdelta_pos hdelta_lt_one
  let cutoff : ℝ :=
    min 1 (interior.constant.rpow (-1 / (1 - delta)))
  have hcutoff_pos : 0 < cutoff := by
    apply lt_min
    · norm_num
    · exact Real.rpow_pos_of_pos interior.constant_pos _
  let alpha : ℝ := cutoff / 2
  have halpha_pos : 0 < alpha := by
    dsimp [alpha]
    positivity
  have halpha_lt_cutoff : alpha < cutoff := by
    dsimp [alpha]
    linarith
  have halpha_le_one : alpha ≤ 1 :=
    (le_of_lt halpha_lt_cutoff).trans (min_le_left _ _)
  have hnon_strict : UpperDensityAtMost (densityEvent alpha)
      (interior.constant * alpha.rpow (1 - delta)) :=
    interior.bound alpha halpha_pos halpha_le_one
  have hstrict : UpperDensityAtMost (strictEvent alpha)
      (interior.constant * alpha.rpow (1 - delta)) :=
    upperDensityAtMost_mono (strictEvent_subset_densityEvent alpha) hnon_strict
  have halpha_lt_power :
      alpha < interior.constant.rpow (-1 / (1 - delta)) :=
    halpha_lt_cutoff.trans_le (min_le_right _ _)
  have hcoefficient_lt_one :
      interior.constant * alpha.rpow (1 - delta) < 1 :=
    coefficient_rpow_lt_one interior.constant_pos hdelta_lt_one
      halpha_pos halpha_lt_power
  exact ⟨{
    delta := delta
    delta_pos := hdelta_pos
    delta_lt_one := hdelta_lt_one
    Cdelta := interior.constant
    Cdelta_pos := interior.constant_pos
    counterexample := {
      epsilon := alpha
      epsilon_pos := halpha_pos
      strict_event_small :=
        ⟨interior.constant * alpha.rpow (1 - delta),
          hcoefficient_lt_one, hstrict⟩ }
    alpha_lt_cutoff := halpha_lt_cutoff
  }⟩

theorem node_p120 (h117 : P117Statement) : P120Statement :=
  p120_of_p117 h117

theorem node_final (h117 : P117Statement) : NegativeAnswer := by
  intro horiginal
  obtain ⟨w⟩ := p120_of_p117 h117
  exact not_density_one_of_upperDensityLtOne
    w.counterexample.strict_event_small
    (horiginal w.counterexample.epsilon w.counterexample.epsilon_pos)

end

end Erdos448.Stage7.ROOT13.Recovered.P120FT
