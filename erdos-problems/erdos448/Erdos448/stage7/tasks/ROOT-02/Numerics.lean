module

import all Mathlib.Basic.Real.Basic
public import Erdos448.stage4.contracts.GroupA

public section

set_option backward.isDefEq.respectTransparency false

namespace Erdos448.Stage7.ROOT02.Numerics

open Erdos448.Stage4.Contracts

lemma nonneg_pow_le_pow_of_le_one_fifth
    {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 1 / 5) (n : ℕ) :
    t ^ n ≤ (1 / 5 : ℝ) ^ n := by
  exact pow_le_pow_left₀ ht0 ht n

set_option maxHeartbeats 800000 in
theorem p014 : P014Statement := by
  intro epsilonInt hepsilonInt_pos hepsilonInt_le
  dsimp
  let t : ℝ := 1.96 * epsilonInt
  have ht0 : 0 ≤ t := by positivity
  have ht : t ≤ 49 / 250 := by
    dsimp [t]
    norm_num at hepsilonInt_le ⊢
    nlinarith
  have ht_fifth : t ≤ 1 / 5 := by norm_num at ht ⊢; linarith
  have habs : |(-t)| < 1 := by
    rw [abs_neg, abs_of_nonneg ht0]
    linarith
  have hTaylor := Real.abs_log_sub_add_sum_range_le (x := -t) habs 8
  norm_num [Finset.sum_range_succ] at hTaylor
  have hden_pos : 0 < 1 - t := by linarith
  have hrem_nonneg : 0 ≤ t ^ 9 / (1 - t) :=
    div_nonneg (pow_nonneg ht0 _) hden_pos.le
  have hlog :
      t - t ^ 2 / 2 + t ^ 3 / 3 - t ^ 4 / 4 + t ^ 5 / 5 -
          t ^ 6 / 6 + t ^ 7 / 7 - t ^ 8 / 8 - t ^ 9 / (1 - t) ≤
        Real.log (1 + t) := by
    have hlower := (abs_le.mp hTaylor).1
    rw [abs_of_nonneg ht0] at hlower
    nlinarith
  have ht2 : t ^ 2 ≤ (1 / 5 : ℝ) ^ 2 :=
    nonneg_pow_le_pow_of_le_one_fifth ht0 ht_fifth 2
  have ht3 : t ^ 3 ≤ (1 / 5 : ℝ) ^ 3 :=
    nonneg_pow_le_pow_of_le_one_fifth ht0 ht_fifth 3
  have ht5 : t ^ 5 ≤ (1 / 5 : ℝ) ^ 5 :=
    nonneg_pow_le_pow_of_le_one_fifth ht0 ht_fifth 5
  have ht7 : t ^ 7 ≤ (1 / 5 : ℝ) ^ 7 :=
    nonneg_pow_le_pow_of_le_one_fifth ht0 ht_fifth 7
  have hpair : -(3 / 100 : ℝ) * t ^ 2 ≤ -t ^ 3 / 6 + t ^ 4 / 12 := by
    have haux : t * (2 - t) ≤ 9 / 25 := by nlinarith [sq_nonneg (t - 1)]
    nlinarith [sq_nonneg t]
  have hpow5 : t ^ 5 ≤ (1 / 125 : ℝ) * t ^ 2 := by
    have := mul_le_mul_of_nonneg_left ht3 (sq_nonneg t)
    norm_num at this ⊢
    ring_nf at this ⊢
    exact this
  have hpow7 : t ^ 7 ≤ (1 / 3125 : ℝ) * t ^ 2 := by
    have := mul_le_mul_of_nonneg_left ht5 (sq_nonneg t)
    norm_num at this ⊢
    ring_nf at this ⊢
    exact this
  have hpow9 : t ^ 9 ≤ (1 / 78125 : ℝ) * t ^ 2 := by
    have := mul_le_mul_of_nonneg_left ht7 (sq_nonneg t)
    norm_num at this ⊢
    ring_nf at this ⊢
    exact this
  have hratio : (1 + t) / (1 - t) ≤ 3 / 2 := by
    have hden : 0 < 1 - t := by linarith
    rw [div_le_iff₀ hden]
    nlinarith
  have hrem :
      (1 + t) * (t ^ 9 / (1 - t)) ≤
        (3 / (2 * 78125) : ℝ) * t ^ 2 := by
    calc
      (1 + t) * (t ^ 9 / (1 - t)) =
          t ^ 9 * ((1 + t) / (1 - t)) := by
            field_simp [hden_pos.ne']
      _ ≤ t ^ 9 * (3 / 2) := by
        gcongr
      _ ≤ ((1 / 78125 : ℝ) * t ^ 2) * (3 / 2) := by
        gcongr
      _ = (3 / (2 * 78125) : ℝ) * t ^ 2 := by ring
  have hmul := mul_le_mul_of_nonneg_left hlog (by linarith : 0 ≤ 1 + t)
  have hseries :
      t ^ 2 / 2 - t ^ 3 / 6 + t ^ 4 / 12 - t ^ 5 / 20 +
          t ^ 6 / 30 - t ^ 7 / 42 + t ^ 8 / 56 - t ^ 9 / 8 -
          (1 + t) * (t ^ 9 / (1 - t)) ≤
        (1 + t) * Real.log (1 + t) - t := by
    calc
      _ = (1 + t) *
          (t - t ^ 2 / 2 + t ^ 3 / 3 - t ^ 4 / 4 + t ^ 5 / 5 -
            t ^ 6 / 6 + t ^ 7 / 7 - t ^ 8 / 8 - t ^ 9 / (1 - t)) - t := by
              ring
      _ ≤ (1 + t) * Real.log (1 + t) - t := sub_le_sub_right hmul t
  have hmain_t :
      (4691 / 10000 : ℝ) * t ^ 2 ≤
        (1 + t) * Real.log (1 + t) - t := by
    have ht6 : 0 ≤ t ^ 6 := pow_nonneg ht0 _
    have ht8 : 0 ≤ t ^ 8 := pow_nonneg ht0 _
    nlinarith [hseries, hpair, hpow5, hpow7, hpow9, hrem]
  have hmain :
      (1802 / 1000 : ℝ) * epsilonInt ^ 2 ≤
        (1 + t) * Real.log (1 + t) - t := by
    have heq : t = (49 / 25 : ℝ) * epsilonInt := by
      dsimp [t]
      norm_num
    rw [heq] at hmain_t
    calc
      (1802 / 1000 : ℝ) * epsilonInt ^ 2 ≤
          (4691 / 10000 : ℝ) * ((49 / 25 : ℝ) * epsilonInt) ^ 2 := by
            nlinarith [sq_nonneg epsilonInt]
      _ ≤ (1 + (49 / 25 : ℝ) * epsilonInt) *
          Real.log (1 + (49 / 25 : ℝ) * epsilonInt) -
            (49 / 25 : ℝ) * epsilonInt := hmain_t
      _ = (1 + t) * Real.log (1 + t) - t := by rw [heq]
  dsimp [t] at hmain ⊢
  norm_num at hmain ⊢
  linarith

set_option maxHeartbeats 800000 in
theorem p015 : P015Statement := by
  intro epsilonInt hepsilonInt_pos hepsilonInt_le
  dsimp
  let t : ℝ := 1.96 * epsilonInt
  have ht0 : 0 ≤ t := by positivity
  have ht_fifth : t ≤ 1 / 5 := by
    dsimp [t]
    norm_num at hepsilonInt_le ⊢
    nlinarith
  have habs : |t| < 1 := by
    rw [abs_of_nonneg ht0]
    linarith
  have hTaylor := Real.abs_log_sub_add_sum_range_le (x := t) habs 4
  norm_num [Finset.sum_range_succ] at hTaylor
  have hlog :
      -(t + t ^ 2 / 2 + t ^ 3 / 3 + t ^ 4 / 4) - t ^ 5 / (1 - t) ≤
        Real.log (1 - t) := by
    have hlower := (abs_le.mp hTaylor).1
    rw [abs_of_nonneg ht0] at hlower
    nlinarith
  have ht3 : t ^ 3 ≤ (1 / 5 : ℝ) ^ 3 :=
    nonneg_pow_le_pow_of_le_one_fifth ht0 ht_fifth 3
  have hpow5 : t ^ 5 ≤ (1 / 125 : ℝ) * t ^ 2 := by
    have := mul_le_mul_of_nonneg_left ht3 (sq_nonneg t)
    norm_num at this ⊢
    ring_nf at this ⊢
    exact this
  have hden_pos : 0 < 1 - t := by linarith
  have hmul := mul_le_mul_of_nonneg_left hlog hden_pos.le
  have hcancel : (1 - t) * (t ^ 5 / (1 - t)) = t ^ 5 := by
    field_simp [hden_pos.ne']
  have hseries :
      t ^ 2 / 2 + t ^ 3 / 6 + t ^ 4 / 12 - (3 / 4 : ℝ) * t ^ 5 ≤
        (1 - t) * Real.log (1 - t) + t := by
    calc
      _ = (1 - t) *
          (-(t + t ^ 2 / 2 + t ^ 3 / 3 + t ^ 4 / 4) -
            t ^ 5 / (1 - t)) + t := by
              field_simp [hden_pos.ne']
              ring
      _ ≤ (1 - t) * Real.log (1 - t) + t := by
        simpa [add_comm] using add_le_add_right hmul t
  have heq : t = (49 / 25 : ℝ) * epsilonInt := by
    dsimp [t]
    norm_num
  have hmain_t : (49 / 100 : ℝ) * t ^ 2 ≤
      (1 - t) * Real.log (1 - t) + t := by
    nlinarith [hseries, hpow5, pow_nonneg ht0 3, pow_nonneg ht0 4]
  rw [heq] at hmain_t
  norm_num at hmain_t ⊢
  nlinarith [hmain_t, sq_nonneg epsilonInt]

end Erdos448.Stage7.ROOT02.Numerics
