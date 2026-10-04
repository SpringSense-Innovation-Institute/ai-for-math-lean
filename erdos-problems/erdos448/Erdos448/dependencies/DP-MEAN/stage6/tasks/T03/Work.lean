module

import all Mathlib.Basic.Real.Basic
public import Erdos448.dependencies.«DP-MEAN».stage6.shared.TaskInterfaces

public section

set_option backward.isDefEq.respectTransparency false

namespace Erdos448.DPMean.TaskT03

open MeasureTheory

@[expose] abbrev PublicTarget : Prop := Erdos448.DPMean.S6.T03Target

lemma mem_inclusiveNatDomain {x : ℝ} (hx : 0 ≤ x) {n : ℕ} :
    n ∈ inclusiveNatDomain x ↔ 0 < n ∧ (n : ℝ) ≤ x := by
  simp only [inclusiveNatDomain, Finset.mem_filter, Finset.mem_range,
    Nat.lt_add_one_iff, Nat.le_floor_iff hx]
  tauto

lemma inclusiveMean_eq_tail_sum_ae (h : ArithmeticFunction) {x : ℝ}
    (hx : 1 ≤ x) :
    ∀ᵐ t : ℝ, t ∈ Set.uIoc (1 : ℝ) x →
      inclusiveMean h t / t =
        ∑ n ∈ inclusiveNatDomain x,
          if (n : ℝ) < t then h n / t else 0 := by
  let s := inclusiveNatDomain x
  have havoid : ∀ᵐ t : ℝ, ∀ n ∈ s, t ≠ (n : ℝ) := by
    rw [Finset.eventually_all]
    intro n hn
    exact MeasureTheory.Measure.ae_ne volume (n : ℝ)
  filter_upwards [havoid] with t htavoid htI
  have htI' : t ∈ Set.Ioc (1 : ℝ) x := by
    simpa [Set.uIoc_of_le hx] using htI
  have ht0 : 0 ≤ t := le_trans (by norm_num) htI'.1.le
  have hsub : inclusiveNatDomain t ⊆ s := by
    intro n hn
    rw [mem_inclusiveNatDomain ht0] at hn
    rw [show s = inclusiveNatDomain x by rfl,
      mem_inclusiveNatDomain (le_trans (by norm_num) hx)]
    exact ⟨hn.1, hn.2.trans htI'.2⟩
  rw [inclusiveMean, Finset.sum_div]
  calc
    (∑ n ∈ inclusiveNatDomain t, h n / t) =
        ∑ n ∈ inclusiveNatDomain t,
          if (n : ℝ) < t then h n / t else 0 := by
      apply Finset.sum_congr rfl
      intro n hn
      have hnle : (n : ℝ) ≤ t :=
        (mem_inclusiveNatDomain ht0).1 hn |>.2
      have hnlt : (n : ℝ) < t :=
        lt_of_le_of_ne hnle (Ne.symm (htavoid n (hsub hn)))
      simp [hnlt]
    _ = ∑ n ∈ s, if (n : ℝ) < t then h n / t else 0 := by
      apply Finset.sum_subset hsub
      intro n hns hnnot
      have hnpos : 0 < n :=
        ((mem_inclusiveNatDomain (le_trans (by norm_num) hx)).1 hns).1
      have hnnotle : ¬(n : ℝ) ≤ t := by
        intro hnle
        exact hnnot ((mem_inclusiveNatDomain ht0).2 ⟨hnpos, hnle⟩)
      simp [not_lt_of_ge (le_of_not_ge hnnotle)]

lemma tailTerm_intervalIntegrable (h : ArithmeticFunction) {x : ℝ}
    (hx : 1 ≤ x) (n : ℕ) :
    IntervalIntegrable
      (fun t : ℝ => if (n : ℝ) < t then h n / t else 0) volume 1 x := by
  have hInv : IntervalIntegrable (fun t : ℝ => 1 / t) volume 1 x := by
    apply intervalIntegral.intervalIntegrable_one_div
    · intro t ht
      have ht' : t ∈ Set.Icc (1 : ℝ) x := by
        simpa [Set.uIcc_of_le hx] using ht
      exact ne_of_gt (lt_of_lt_of_le (by norm_num) ht'.1)
    · fun_prop
  have hInd : IntervalIntegrable
      (Set.indicator {t : ℝ | t ≤ (n : ℝ)} (fun t => 1 / t)) volume 1 x := by
    constructor
    · exact hInv.1.indicator measurableSet_Iic
    · exact hInv.2.indicator measurableSet_Iic
  have hBase := (hInv.sub hInd).const_mul (h n)
  apply hBase.congr
  intro t ht
  by_cases hnt : (n : ℝ) < t
  · simp [hnt, not_le.mpr hnt]
    ring
  · have htn : t ≤ (n : ℝ) := le_of_not_gt hnt
    simp [hnt, htn]

lemma integral_tailTerm (h : ArithmeticFunction) {x : ℝ} (hx : 1 ≤ x)
    {n : ℕ} (hnpos : 0 < n) (hnx : (n : ℝ) ≤ x) :
    (∫ t : ℝ in (1 : ℝ)..x,
      if (n : ℝ) < t then h n / t else 0) =
      h n * Real.log (x / (n : ℝ)) := by
  have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hnposR : 0 < (n : ℝ) := Nat.cast_pos.mpr hnpos
  have hnIcc : (n : ℝ) ∈ Set.Icc (1 : ℝ) x :=
    ⟨by exact_mod_cast hnpos, hnx⟩
  have hInv : IntervalIntegrable (fun t : ℝ => 1 / t) volume 1 x := by
    apply intervalIntegral.intervalIntegrable_one_div
    · intro t ht
      have ht' : t ∈ Set.Icc (1 : ℝ) x := by
        simpa [Set.uIcc_of_le hx] using ht
      exact ne_of_gt (lt_of_lt_of_le (by norm_num) ht'.1)
    · fun_prop
  have hInd : IntervalIntegrable
      (Set.indicator {t : ℝ | t ≤ (n : ℝ)} (fun t => 1 / t)) volume 1 x := by
    constructor
    · exact hInv.1.indicator measurableSet_Iic
    · exact hInv.2.indicator measurableSet_Iic
  calc
    (∫ t : ℝ in (1 : ℝ)..x,
        if (n : ℝ) < t then h n / t else 0) =
        ∫ t : ℝ in (1 : ℝ)..x,
          h n * ((1 / t) -
            Set.indicator {u : ℝ | u ≤ (n : ℝ)} (fun u => 1 / u) t) := by
      apply intervalIntegral.integral_congr
      intro t ht
      by_cases hnt : (n : ℝ) < t
      · simp [hnt, not_le.mpr hnt]
        ring
      · have htn : t ≤ (n : ℝ) := le_of_not_gt hnt
        simp [hnt, htn]
    _ = h n * (∫ t : ℝ in (1 : ℝ)..x,
          ((1 / t) -
            Set.indicator {u : ℝ | u ≤ (n : ℝ)} (fun u => 1 / u) t)) := by
      exact intervalIntegral.integral_const_mul (h n) _
    _ = h n * ((∫ t : ℝ in (1 : ℝ)..x, 1 / t) -
        ∫ t : ℝ in (1 : ℝ)..x,
          Set.indicator {u : ℝ | u ≤ (n : ℝ)} (fun u => 1 / u) t) := by
      congr 1
      exact intervalIntegral.integral_sub hInv hInd
    _ = h n * ((∫ t : ℝ in (1 : ℝ)..x, 1 / t) -
        ∫ t : ℝ in (1 : ℝ)..(n : ℝ), 1 / t) := by
      rw [intervalIntegral.integral_indicator hnIcc]
    _ = h n * (Real.log (x / 1) - Real.log ((n : ℝ) / 1)) := by
      rw [integral_one_div_of_pos (by norm_num) hxpos,
        integral_one_div_of_pos (by norm_num) hnposR]
    _ = h n * Real.log (x / (n : ℝ)) := by
      rw [Real.log_div (ne_of_gt hxpos) (ne_of_gt hnposR)]
      simp

theorem smoothing_definition : SmoothingDefinitionStatement := by
  intro h x hx
  have hx0 : 0 ≤ x := le_trans (by norm_num) hx
  unfold smoothingIntegral smoothingWeightedSum
  calc
    (∫ t : ℝ in (1 : ℝ)..x, inclusiveMean h t / t) =
        ∫ t : ℝ in (1 : ℝ)..x,
          ∑ n ∈ inclusiveNatDomain x,
            if (n : ℝ) < t then h n / t else 0 := by
      exact intervalIntegral.integral_congr_ae
        (inclusiveMean_eq_tail_sum_ae h hx)
    _ = ∑ n ∈ inclusiveNatDomain x,
          ∫ t : ℝ in (1 : ℝ)..x,
            if (n : ℝ) < t then h n / t else 0 := by
      apply intervalIntegral.integral_finset_sum
      intro n hn
      exact tailTerm_intervalIntegrable h hx n
    _ = ∑ n ∈ inclusiveNatDomain x,
          h n * Real.log (x / (n : ℝ)) := by
      apply Finset.sum_congr rfl
      intro n hn
      exact integral_tailTerm h hx
        ((mem_inclusiveNatDomain hx0).1 hn).1
        ((mem_inclusiveNatDomain hx0).1 hn).2

theorem p004 : P004Statement := by
  intro h hnon x hx
  have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hx0 : 0 ≤ x := hxpos.le
  have hcombined : inclusiveMean h x + smoothingIntegral h x ≤
      x * reciprocalMean h x := by
    rw [smoothing_definition h x hx]
    simp only [inclusiveMean, smoothingWeightedSum, reciprocalMean,
      ← Finset.sum_add_distrib, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n hn
    have hnmem := (mem_inclusiveNatDomain hx0).1 hn
    have hnposR : 0 < (n : ℝ) := Nat.cast_pos.mpr hnmem.1
    have hhn : 0 ≤ h n := hnon n hnmem.1
    have hu : 0 < x / (n : ℝ) := div_pos hxpos hnposR
    have hlog := Real.log_le_sub_one_of_pos hu
    calc
      h n + h n * Real.log (x / (n : ℝ)) =
          h n * (1 + Real.log (x / (n : ℝ))) := by ring
      _ ≤ h n * (x / (n : ℝ)) := by
        apply mul_le_mul_of_nonneg_left
        · linarith
        · exact hhn
      _ = x * (h n / (n : ℝ)) := by field_simp
  refine ⟨hcombined, ?_⟩
  have hmean_nonneg : 0 ≤ inclusiveMean h x := by
    unfold inclusiveMean
    apply Finset.sum_nonneg
    intro n hn
    exact hnon n ((mem_inclusiveNatDomain hx0).1 hn).1
  linarith

theorem p005 : P005Statement := by
  intro h hnon x hx
  have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hx0 : 0 ≤ x := hxpos.le
  rw [smoothing_definition h x hx]
  simp only [inclusiveMean, weightedLogMean, smoothingWeightedSum,
    Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  have hnpos : 0 < (n : ℝ) :=
    Nat.cast_pos.mpr ((mem_inclusiveNatDomain hx0).1 hn).1
  rw [Real.log_div (ne_of_gt hxpos) (ne_of_gt hnpos)]
  ring

theorem direct : PublicTarget := by
  exact ⟨smoothing_definition, p004, p005⟩

end Erdos448.DPMean.TaskT03
