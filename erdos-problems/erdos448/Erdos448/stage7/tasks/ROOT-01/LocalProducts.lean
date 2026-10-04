module

import all Mathlib.Basic.Real.Basic
public import Erdos448.stage6.TaskContracts

public section

set_option backward.isDefEq.respectTransparency false

namespace Erdos448.Stage7.ROOT01

open Erdos448.Stage4
open Erdos448.Stage4.Contracts
open Finset
open scoped BigOperators

noncomputable section

lemma mem_strictPrimeRange {x : ℝ} {p : ℕ} :
    p ∈ strictPrimeRange x ↔ p.Prime ∧ (p : ℝ) < x := by
  rw [strictPrimeRange, Finset.mem_filter]
  constructor
  · rintro ⟨hpRange, hp⟩
    exact ⟨hp, (Finset.mem_filter.mp hpRange).2.2⟩
  · rintro ⟨hp, hpx⟩
    exact ⟨Finset.mem_filter.mpr
      ⟨by simpa using Nat.lt_ceil.mpr hpx, hp.pos, hpx⟩, hp⟩

lemma primeIntervalProduct_pos
    (L : ℕ → ℝ) (hL : ∀ p : ℕ, p.Prime → 0 < L p) (A B : ℝ) :
    0 < primeIntervalProduct L A B := by
  unfold primeIntervalProduct
  apply Finset.prod_pos
  intro p hp
  split_ifs
  · exact hL p (mem_strictPrimeRange.mp hp).1
  · exact zero_lt_one

lemma primeIntervalProduct_eq_one_of_le
    (L : ℕ → ℝ) {A B : ℝ} (hBA : B ≤ A) :
    primeIntervalProduct L A B = 1 := by
  unfold primeIntervalProduct
  apply Finset.prod_eq_one
  intro p hp
  have hpB := (mem_strictPrimeRange.mp hp).2
  simp [not_le.mpr (hpB.trans_le hBA)]

end

end Erdos448.Stage7.ROOT01
