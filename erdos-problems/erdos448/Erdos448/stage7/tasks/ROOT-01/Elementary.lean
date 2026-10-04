module

import all Mathlib.Basic.Real.Basic
public import Erdos448.stage6.TaskContracts

public section

set_option backward.isDefEq.respectTransparency false

namespace Erdos448.Stage7.ROOT01

open Erdos448.Stage4
open Erdos448.Stage4.Contracts
open Finset

noncomputable section

lemma mem_positiveNatsBelow {X : ℝ} {n : ℕ} :
    n ∈ positiveNatsBelow X ↔ 0 < n ∧ (n : ℝ) < X := by
  constructor
  · intro hn
    exact (Finset.mem_filter.mp hn).2
  · rintro ⟨hnpos, hnX⟩
    rw [positiveNatsBelow, Finset.mem_filter]
    exact ⟨by simpa using Nat.lt_ceil.mpr hnX, hnpos, hnX⟩

lemma positiveNatsBelow_eq_empty_of_le_one {X : ℝ} (hX : X ≤ 1) :
    positiveNatsBelow X = ∅ := by
  apply Finset.eq_empty_of_forall_notMem
  intro n hn
  have hn' := mem_positiveNatsBelow.mp hn
  have hone : (1 : ℝ) ≤ n := by exact_mod_cast hn'.1
  exact (not_lt_of_ge hone (hn'.2.trans_le hX)).elim

lemma positiveNatsBelow_eq_singleton_one {X : ℝ} (hX1 : 1 < X) (hX2 : X < 2) :
    positiveNatsBelow X = {1} := by
  ext n
  rw [mem_positiveNatsBelow, Finset.mem_singleton]
  constructor
  · rintro ⟨hnpos, hnX⟩
    have hnlt : n < 2 := by exact_mod_cast hnX.trans hX2
    omega
  · rintro rfl
    norm_num [hX1]

theorem p001A : P001AStatement := by
  intro g hg X hX
  constructor
  · intro hX1
    simp [initialSegment, strictMean, positiveNatsBelow_eq_empty_of_le_one hX1]
  · intro h1X hX2
    simp [initialSegment, strictMean, positiveNatsBelow_eq_singleton_one h1X hX2]

end

end Erdos448.Stage7.ROOT01
