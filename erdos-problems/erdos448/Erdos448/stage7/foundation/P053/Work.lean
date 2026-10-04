module

import all Mathlib.Basic.Real.Basic
public import Erdos448.stage6.TaskContracts

public section

set_option backward.isDefEq.respectTransparency false

namespace Erdos448.Stage7.FoundationP053.Work

open Erdos448.Stage4
open Erdos448.Stage4.Contracts
open Erdos448.Stage6.TaskContracts

lemma one_le_safeLog (x : ℝ) : 1 ≤ safeLog x := by
  exact le_max_left _ _

lemma safeLog_pos (x : ℝ) : 0 < safeLog x :=
  lt_of_lt_of_le zero_lt_one (one_le_safeLog x)

lemma rpow_neg_half_eq_inv_sqrt (x : ℝ) (hx : 0 ≤ x) :
    x.rpow (-1 / 2) = (Real.sqrt x)⁻¹ := by
  rw [Real.sqrt_eq_rpow]
  simpa only [Real.rpow_eq_pow, show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by ring] using
    Real.rpow_neg hx (1 / 2 : ℝ)

lemma weight_le_one (x : ℝ) :
    (safeLog x).rpow (-1 / 2) ≤ 1 := by
  have h := (Real.rpow_le_rpow_iff_of_neg (safeLog_pos x) zero_lt_one
    (by norm_num : (-1 / 2 : ℝ) < 0)).2 (one_le_safeLog x)
  simpa using h

lemma safeLog_le_two_safeLog_of_sqrt_le {x y : ℝ}
    (hx : 0 < x) (hxy : Real.sqrt x ≤ y) :
    safeLog x ≤ 2 * safeLog y := by
  have hsqrt_pos : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
  have hy : 0 < y := lt_of_lt_of_le hsqrt_pos hxy
  have hsq : x ≤ y ^ 2 := by
    nlinarith [Real.sq_sqrt (le_of_lt hx)]
  have hlog : Real.log x ≤ 2 * Real.log y := by
    calc
      Real.log x ≤ Real.log (y ^ 2) := Real.log_le_log hx hsq
      _ = 2 * Real.log y := by rw [Real.log_pow]; norm_num
  unfold safeLog
  apply max_le
  · have hy_one : 1 ≤ max 1 (Real.log y) := le_max_left _ _
    linarith
  · calc
      Real.log x ≤ 2 * Real.log y := hlog
      _ ≤ 2 * max 1 (Real.log y) := by
        gcongr
        exact le_max_right _ _

lemma inv_sqrt_le_two_inv_sqrt {a L : ℝ}
    (ha : 0 < a) (hL : 0 < L) (h : L ≤ 2 * a) :
    (Real.sqrt a)⁻¹ ≤ 2 * (Real.sqrt L)⁻¹ := by
  have hsa : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  have hsL : 0 < Real.sqrt L := Real.sqrt_pos.2 hL
  have hsqrt : Real.sqrt L ≤ 2 * Real.sqrt a := by
    nlinarith [Real.sq_sqrt (le_of_lt ha), Real.sq_sqrt (le_of_lt hL),
      Real.sqrt_nonneg a, Real.sqrt_nonneg L]
  calc
    (Real.sqrt a)⁻¹ = Real.sqrt L / (Real.sqrt a * Real.sqrt L) := by
      field_simp
    _ ≤ (2 * Real.sqrt a) / (Real.sqrt a * Real.sqrt L) := by
      exact div_le_div_of_nonneg_right hsqrt (by positivity)
    _ = 2 * (Real.sqrt L)⁻¹ := by
      field_simp

lemma large_weight_bound {x y : ℝ} (hx : 0 < x)
    (hxy : Real.sqrt x ≤ y) :
    (safeLog y).rpow (-1 / 2) ≤
      2 * (safeLog x).rpow (-1 / 2) := by
  have h := safeLog_le_two_safeLog_of_sqrt_le hx hxy
  rw [rpow_neg_half_eq_inv_sqrt _ (le_of_lt (safeLog_pos y)),
    rpow_neg_half_eq_inv_sqrt _ (le_of_lt (safeLog_pos x))]
  exact inv_sqrt_le_two_inv_sqrt (safeLog_pos y) (safeLog_pos x) h

lemma safeLog_le_self {x : ℝ} (hx : 2 < x) : safeLog x ≤ x := by
  have hx0 : 0 < x := lt_trans (by norm_num) hx
  have hlog := Real.log_le_sub_one_of_pos hx0
  unfold safeLog
  exact max_le (by linarith) (by linarith)

lemma sqrt_add_one_bound {x L : ℝ} (hx : 2 < x)
    (hL : 0 < L) (hLx : L ≤ x) :
    Real.sqrt x + 1 ≤ 2 * x * (Real.sqrt L)⁻¹ := by
  have hx0 : 0 < x := lt_trans (by norm_num) hx
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.2 hx0
  have hsL : 0 < Real.sqrt L := Real.sqrt_pos.2 hL
  have hsqrt : Real.sqrt L ≤ Real.sqrt x := Real.sqrt_le_sqrt hLx
  have hinv : (Real.sqrt x)⁻¹ ≤ (Real.sqrt L)⁻¹ :=
    (inv_le_inv₀ hsx hsL).2 hsqrt
  have hsx_one : 1 ≤ Real.sqrt x := by
    nlinarith [Real.sq_sqrt (le_of_lt hx0), Real.sqrt_nonneg x]
  have heq : 2 * Real.sqrt x = 2 * x * (Real.sqrt x)⁻¹ := by
    field_simp
    nlinarith [Real.sq_sqrt (le_of_lt hx0)]
  calc
    Real.sqrt x + 1 ≤ 2 * Real.sqrt x := by linarith
    _ = 2 * x * (Real.sqrt x)⁻¹ := heq
    _ ≤ 2 * x * (Real.sqrt L)⁻¹ := by
      gcongr

lemma positiveNatsBelow_eq_empty {M : ℝ} (hM : M ≤ 1) :
    positiveNatsBelow M = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.2
  intro n hn
  rw [positiveNatsBelow, Finset.mem_filter] at hn
  rcases hn with ⟨_, hnpos, hnM⟩
  have hn_one : (1 : ℝ) ≤ n := by exact_mod_cast hnpos
  linarith

/-- The endpoint-safe logarithmic partial sum, with one absolute constant
chosen before every positive endpoint. -/
theorem result : FoundationP053Target := by
  refine ⟨⟨8, by norm_num, ?_⟩⟩
  intro M hM
  by_cases hsmallM : M ≤ 1
  · rw [safeLogHalfSum, positiveNatsBelow_eq_empty hsmallM]
    simp only [Finset.sum_empty]
    exact mul_nonneg (mul_nonneg (by norm_num) (le_of_lt hM))
      (Real.rpow_nonneg (le_trans zero_le_one (one_le_safeLog _)) _)
  · have hM_one : 1 < M := lt_of_not_ge hsmallM
    let x : ℝ := 2 * M
    let L : ℝ := safeLog x
    let s : Finset ℕ := positiveNatsBelow M
    let small : Finset ℕ := s.filter fun m => (m : ℝ) < Real.sqrt x
    let large : Finset ℕ := s.filter fun m => ¬(m : ℝ) < Real.sqrt x
    have hx : 2 < x := by dsimp [x]; linarith
    have hx0 : 0 < x := lt_trans (by norm_num) hx
    have hL : 0 < L := by exact safeLog_pos x
    have hLx : L ≤ x := by exact safeLog_le_self hx
    have hsmall_sum :
        (∑ m ∈ small, (safeLog m).rpow (-1 / 2)) ≤
          4 * M * L.rpow (-1 / 2) := by
      have hsum_card :
          (∑ m ∈ small, (safeLog m).rpow (-1 / 2)) ≤ (small.card : ℝ) := by
        have h := Finset.sum_le_card_nsmul small
          (fun m : ℕ => (safeLog m).rpow (-1 / 2)) (1 : ℝ) (by
            intro m hm
            exact weight_le_one m)
        simpa using h
      have hsubset : small ⊆ Finset.range (Nat.ceil (Real.sqrt x)) := by
        intro m hm
        have hm_lt : (m : ℝ) < Real.sqrt x := (Finset.mem_filter.1 hm).2
        exact Finset.mem_range.2 (Nat.lt_ceil.mpr hm_lt)
      have hcard_nat : small.card ≤ Nat.ceil (Real.sqrt x) := by
        simpa using Finset.card_le_card hsubset
      have hcard : (small.card : ℝ) ≤ Nat.ceil (Real.sqrt x) := by
        exact_mod_cast hcard_nat
      have hceil : (Nat.ceil (Real.sqrt x) : ℝ) < Real.sqrt x + 1 :=
        Nat.ceil_lt_add_one (Real.sqrt_nonneg x)
      have hsqrt_bound :
          Real.sqrt x + 1 ≤ 2 * x * (Real.sqrt L)⁻¹ :=
        sqrt_add_one_bound hx hL hLx
      rw [rpow_neg_half_eq_inv_sqrt L (le_of_lt hL)]
      dsimp [x] at hsqrt_bound ⊢
      calc
        (∑ m ∈ small, (safeLog m).rpow (-1 / 2)) ≤ (small.card : ℝ) := hsum_card
        _ ≤ (Nat.ceil (Real.sqrt (2 * M)) : ℝ) := hcard
        _ ≤ Real.sqrt (2 * M) + 1 := le_of_lt hceil
        _ ≤ 2 * (2 * M) * (Real.sqrt L)⁻¹ := hsqrt_bound
        _ = 4 * M * (Real.sqrt L)⁻¹ := by ring
    have hlarge_sum :
        (∑ m ∈ large, (safeLog m).rpow (-1 / 2)) ≤
          4 * M * L.rpow (-1 / 2) := by
      have hpoint : ∀ m ∈ large,
          (safeLog m).rpow (-1 / 2) ≤ 2 * L.rpow (-1 / 2) := by
        intro m hm
        have hm_large : Real.sqrt x ≤ (m : ℝ) := by
          exact le_of_not_gt (Finset.mem_filter.1 hm).2
        exact large_weight_bound hx0 hm_large
      have hsum_card := Finset.sum_le_card_nsmul large
        (fun m : ℕ => (safeLog m).rpow (-1 / 2))
        (2 * L.rpow (-1 / 2)) hpoint
      have hlarge_sub : large ⊆ s := Finset.filter_subset _ _
      have hs_sub : s ⊆ Finset.range (Nat.ceil M) := by
        intro m hm
        exact (Finset.mem_filter.1 hm).1
      have hcard_nat : large.card ≤ Nat.ceil M :=
        le_trans (Finset.card_le_card hlarge_sub) (by
          simpa using Finset.card_le_card hs_sub)
      have hcard : (large.card : ℝ) ≤ Nat.ceil M := by exact_mod_cast hcard_nat
      have hceil : (Nat.ceil M : ℝ) < M + 1 :=
        Nat.ceil_lt_add_one (le_of_lt hM)
      have hq : 0 ≤ 2 * L.rpow (-1 / 2) :=
        mul_nonneg (by norm_num) (Real.rpow_nonneg (le_of_lt hL) _)
      calc
        (∑ m ∈ large, (safeLog m).rpow (-1 / 2)) ≤
            (large.card : ℝ) * (2 * L.rpow (-1 / 2)) := by
              simpa [nsmul_eq_mul] using hsum_card
        _ ≤ (Nat.ceil M : ℝ) * (2 * L.rpow (-1 / 2)) := by gcongr
        _ ≤ (M + 1) * (2 * L.rpow (-1 / 2)) := by gcongr
        _ ≤ (2 * M) * (2 * L.rpow (-1 / 2)) := by
          gcongr
          linarith
        _ = 4 * M * L.rpow (-1 / 2) := by ring
    rw [safeLogHalfSum]
    change (∑ m ∈ s, (safeLog m).rpow (-1 / 2)) ≤ _
    have hsplit :
        (∑ m ∈ s, (safeLog m).rpow (-1 / 2)) =
          (∑ m ∈ small, (safeLog m).rpow (-1 / 2)) +
          (∑ m ∈ large, (safeLog m).rpow (-1 / 2)) := by
      dsimp [small, large]
      exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm
    rw [hsplit]
    dsimp [L, x] at hsmall_sum hlarge_sum ⊢
    nlinarith

end Erdos448.Stage7.FoundationP053.Work
