module

import all Mathlib.Basic.Real.Basic
public import Erdos448.stage7.tasks.«ROOT-01».ShiftedMean
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.SpecialFunctions.Log.Summable

public section

set_option backward.isDefEq.respectTransparency false

namespace Erdos448.Stage7.ROOT01

open Erdos448.Stage4
open Erdos448.Stage4.Contracts
open Finset Nat Set
open scoped BigOperators Topology

noncomputable section

@[expose] def primeError (r : ℕ → ℝ) (n : ℕ) : ℝ :=
  if n.Prime then r n else 0

lemma primeError_summable
    {C eta : ℝ} (hC : 0 < C) (heta : 0 < eta)
    (r : ℕ → ℝ)
    (hr : ∀ p : ℕ, p.Prime → |r p| ≤ C * (p : ℝ).rpow (-1 - eta)) :
    Summable (fun n : ℕ => ‖primeError r n‖) := by
  have hpow : Summable (fun n : ℕ => (n : ℝ).rpow (-1 - eta)) := by
    exact (Real.summable_nat_rpow).2 (by linarith)
  apply Summable.of_nonneg_of_le
  · intro n
    positivity
  · intro n
    unfold primeError
    by_cases hn : n.Prime
    · simp only [hn, if_true, Real.norm_eq_abs]
      exact hr n hn
    · rw [if_neg hn]
      have hnonneg := mul_nonneg hC.le
        (Real.rpow_nonneg (Nat.cast_nonneg n) (-1 - eta))
      norm_num at hnonneg ⊢
      exact hnonneg
  · exact hpow.mul_left C

lemma intervalProduct_eq_errorProduct
    (r : ℕ → ℝ) (A B : ℝ) :
    primeIntervalProduct (fun p => 1 + r p) A B =
      ∏ p ∈ (strictPrimeRange B).filter (fun p : ℕ => A ≤ (p : ℝ)),
        (1 + primeError r p) := by
  unfold primeIntervalProduct
  rw [Finset.prod_ite]
  simp only [Finset.prod_const_one, mul_one]
  apply Finset.prod_congr
  · ext p
    simp
  · intro p hp
    simp [primeError, (mem_strictPrimeRange.mp (Finset.mem_filter.mp hp).1).1]

lemma intervalProduct_eq_product
    (r : ℕ → ℝ) (A B : ℝ) :
    primeIntervalProduct (fun p => 1 + r p) A B =
      ∏ p ∈ (strictPrimeRange B).filter (fun p : ℕ => A ≤ (p : ℝ)),
        (1 + r p) := by
  unfold primeIntervalProduct
  rw [Finset.prod_ite]
  simp only [Finset.prod_const_one, mul_one]

lemma summableError_tail_bounds
    (r : ℕ → ℝ) (hrsum : Summable (fun n : ℕ => ‖r n‖)) :
    ∃ P0 : ℝ, 2 ≤ P0 ∧ ∀ A B : ℝ, P0 ≤ A → A < B →
      (1 / 2 : ℝ) ≤ primeIntervalProduct (fun p => 1 + r p) A B ∧
        primeIntervalProduct (fun p => 1 + r p) A B ≤ 3 / 2 := by
  obtain ⟨s, hs⟩ := prod_vanishing_of_summable_norm hrsum
    (show (0 : ℝ) < 1 / 2 by norm_num)
  let N : ℕ := s.sup id + 1
  let P0 : ℝ := max 2 N
  refine ⟨P0, le_max_left _ _, ?_⟩
  intro A B hP0A hAB
  let t : Finset ℕ := (strictPrimeRange B).filter (fun p => A ≤ (p : ℝ))
  have hdisj : Disjoint t s := by
    rw [Finset.disjoint_left]
    intro p hpt hps
    have hpA : A ≤ (p : ℝ) := (Finset.mem_filter.mp hpt).2
    have hple : p ≤ s.sup id := Finset.le_sup (f := id) hps
    have hNle : (N : ℝ) ≤ p := by
      exact (le_max_right (2 : ℝ) N).trans (hP0A.trans hpA)
    dsimp [N] at hNle
    have hNleNat : s.sup id + 1 ≤ p := by exact_mod_cast hNle
    omega
  have hclose := hs t hdisj
  have heq := intervalProduct_eq_product r A B
  change primeIntervalProduct (fun p => 1 + r p) A B =
    ∏ p ∈ t, (1 + r p) at heq
  rw [← heq] at hclose
  rw [Real.norm_eq_abs, abs_lt] at hclose
  constructor <;> linarith

lemma tailProduct_bounds
    {r : ℕ → ℝ} (hrsum : Summable (fun n : ℕ => ‖primeError r n‖)) :
    ∃ P0 : ℝ, 2 ≤ P0 ∧ ∀ B : ℝ, P0 < B →
      (1 / 2 : ℝ) ≤ primeIntervalProduct (fun p => 1 + r p) P0 B ∧
        primeIntervalProduct (fun p => 1 + r p) P0 B ≤ 3 / 2 := by
  obtain ⟨P0, hP0, hbounds⟩ :=
    summableError_tail_bounds (primeError r) hrsum
  refine ⟨P0, hP0, ?_⟩
  intro B hB
  have hb := hbounds P0 B le_rfl hB
  have heq : primeIntervalProduct (fun p => 1 + primeError r p) P0 B =
      primeIntervalProduct (fun p => 1 + r p) P0 B := by
    unfold primeIntervalProduct
    apply Finset.prod_congr rfl
    intro p hp
    simp [primeError, (mem_strictPrimeRange.mp hp).1]
  rw [heq] at hb
  exact hb

theorem p006 : P006Statement := by
  intro C eta hC heta r hr hrpos
  have hrsum := primeError_summable hC heta r hr
  obtain ⟨P0, hP0, hbounds⟩ := tailProduct_bounds hrsum
  exact ⟨{
    P0 := P0
    lower := 1 / 2
    upper := 3 / 2
    P0_ge_two := hP0
    lower_pos := by norm_num
    upper_pos := by norm_num
    uniform_bounds := hbounds
  }⟩

end

end Erdos448.Stage7.ROOT01
