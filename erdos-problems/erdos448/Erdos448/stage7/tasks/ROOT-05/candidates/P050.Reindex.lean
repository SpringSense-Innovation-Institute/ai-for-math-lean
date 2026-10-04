module

import all Mathlib.Basic.Real.Basic
public import Erdos448.stage6.TaskContracts

public section

set_option backward.isDefEq.respectTransparency false

namespace Erdos448.Stage7.ROOT05.P050Reindex

open Finset Set
open scoped BigOperators

open Erdos448.Stage4
open Erdos448.Stage4.Contracts

noncomputable section

lemma mem_positiveNatsBelow {x : ℝ} {n : ℕ}
    (hn : n ∈ positiveNatsBelow x) : 0 < n ∧ (n : ℝ) < x := by
  exact (Finset.mem_filter.mp hn).2

lemma positive_mem_below {x : ℝ} {n : ℕ}
    (hn : 0 < n) (hnx : (n : ℝ) < x) : n ∈ positiveNatsBelow x := by
  rw [positiveNatsBelow, Finset.mem_filter]
  exact ⟨by simpa using Nat.lt_ceil.mpr hnx, hn, hnx⟩

theorem sum_multiples (F : ℕ → ℝ) {a : ℕ} (ha : 0 < a) (x : ℝ) :
    (∑ n ∈ positiveNatsBelow x, if a ∣ n then F n else 0) =
      ∑ m ∈ positiveNatsBelow (x / a), F (m * a) := by
  rw [← Finset.sum_filter]
  symm
  apply Finset.sum_bij (fun m _ => m * a)
  · intro m hm
    have hm' := mem_positiveNatsBelow hm
    rw [Finset.mem_filter]
    refine ⟨positive_mem_below (Nat.mul_pos hm'.1 ha) ?_, dvd_mul_left a m⟩
    have haR : (0 : ℝ) < a := by exact_mod_cast ha
    have := (lt_div_iff₀ haR).mp hm'.2
    simpa [Nat.cast_mul, mul_comm] using this
  · intro m₁ hm₁ m₂ hm₂ h
    exact Nat.eq_of_mul_eq_mul_right ha h
  · intro n hn
    have hn' := Finset.mem_filter.mp hn
    refine ⟨n / a, ?_, ?_⟩
    · have hnpos := (mem_positiveNatsBelow hn'.1).1
      have hdivpos : 0 < n / a := Nat.div_pos (Nat.le_of_dvd hnpos hn'.2) ha
      apply positive_mem_below hdivpos
      have haR : (0 : ℝ) < a := by exact_mod_cast ha
      apply (lt_div_iff₀ haR).mpr
      rw [← Nat.cast_mul, Nat.div_mul_cancel hn'.2]
      exact (mem_positiveNatsBelow hn'.1).2
    · exact Nat.div_mul_cancel hn'.2
  · intro m hm
    rfl

end

end Erdos448.Stage7.ROOT05.P050Reindex
