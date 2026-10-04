module

import all Mathlib.Basic.Real.Basic
public import Erdos448.stage7.tasks.«ROOT-01».Normalization

public section

set_option backward.isDefEq.respectTransparency false

namespace Erdos448.Stage7.ROOT01

open Erdos448.Stage4
open Erdos448.Stage4.Contracts
open Finset Nat Set
open scoped BigOperators

noncomputable section

lemma strictPrimeRange_mono {A B : ℝ} (hAB : A ≤ B) :
    strictPrimeRange A ⊆ strictPrimeRange B := by
  intro p hp
  exact mem_strictPrimeRange.mpr
    ⟨(mem_strictPrimeRange.mp hp).1, (mem_strictPrimeRange.mp hp).2.trans_le hAB⟩

lemma intervalProduct_extend_right
    (L : ℕ → ℝ) {A C B : ℝ} (hCB : C ≤ B) :
    primeIntervalProduct L A C =
      ∏ p ∈ strictPrimeRange B,
        if A ≤ (p : ℝ) ∧ (p : ℝ) < C then L p else 1 := by
  unfold primeIntervalProduct
  apply Finset.prod_subset_one_on_sdiff (strictPrimeRange_mono hCB)
  · intro p hpDiff
    have hpB := (Finset.mem_sdiff.mp hpDiff).1
    have hpNotC := (Finset.mem_sdiff.mp hpDiff).2
    have hpNotLtC : ¬(p : ℝ) < C := by
      intro hpLtC
      exact hpNotC (mem_strictPrimeRange.mpr
        ⟨(mem_strictPrimeRange.mp hpB).1, hpLtC⟩)
    simp [hpNotLtC]
  · intro p hpC
    have hpLtC := (mem_strictPrimeRange.mp hpC).2
    by_cases hpA : A ≤ (p : ℝ) <;> simp [hpA, hpLtC]

lemma primeIntervalProduct_mul
    (L : ℕ → ℝ) {A C B : ℝ} (hAC : A ≤ C) (hCB : C ≤ B) :
    primeIntervalProduct L A B =
      primeIntervalProduct L A C * primeIntervalProduct L C B := by
  rw [intervalProduct_extend_right L hCB]
  unfold primeIntervalProduct
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p hpB
  have hpLtB := (mem_strictPrimeRange.mp hpB).2
  by_cases hpA : A ≤ (p : ℝ)
  · by_cases hpC : C ≤ (p : ℝ)
    · simp [hpA, hpC, not_lt.mpr hpC]
    · have hpLtC : (p : ℝ) < C := lt_of_not_ge hpC
      simp [hpA, hpC, hpLtC]
  · have hpC : ¬C ≤ (p : ℝ) := fun h => hpA (hAC.trans h)
    simp [hpA, hpC]

lemma primeIntervalProduct_div
    (L : ℕ → ℝ) (hL : ∀ p : ℕ, p.Prime → 0 < L p)
    {A C B : ℝ} (hAC : A ≤ C) (hCB : C ≤ B) :
    primeIntervalProduct L C B =
      primeIntervalProduct L A B / primeIntervalProduct L A C := by
  rw [primeIntervalProduct_mul L hAC hCB]
  field_simp [ne_of_gt (primeIntervalProduct_pos L hL A C)]

end

end Erdos448.Stage7.ROOT01
