module

import all Mathlib.Basic.Real.Basic
public import Erdos448.stage6.TaskContracts

public section

set_option backward.isDefEq.respectTransparency false

namespace Erdos448.Stage7.ROOT06.Elementary

open Erdos448.Stage4
open Erdos448.Stage4.Contracts
open Finset
open scoped BigOperators

noncomputable section

instance (p : Prop) : Decidable p := Classical.propDecidable p

theorem p054 : P054Statement := by
  intro k hk theta htheta d d' hdlo hdhi hclose
  have htpos : 0 < theta := lt_trans zero_lt_one htheta
  have hdpos : (0 : ℝ) < d.1 := by exact_mod_cast d.2
  have hd'pos : (0 : ℝ) < d'.1 := by exact_mod_cast d'.2
  have hratio_lo := hclose.2.1
  have hratio_hi := hclose.2.2
  have hd'_lo : (d.1 : ℝ) / theta < d'.1 := by
    have h := (lt_div_iff₀ hdpos).mp hratio_lo
    calc
      (d.1 : ℝ) / theta = (1 / theta) * d.1 := by ring
      _ < d'.1 := h
  have hd'_hi : (d'.1 : ℝ) < theta * d.1 := by
    exact (div_lt_iff₀ hdpos).mp hratio_hi
  have hk_split : k = (k - 1) + 1 := by omega
  have hsecond_lo : theta ^ (k - 1) < (d'.1 : ℝ) := by
    rw [hk_split, pow_succ] at hdlo
    have := (le_div_iff₀ htpos).2 hdlo
    exact this.trans_lt hd'_lo
  have hsecond_hi : (d'.1 : ℝ) < theta ^ (k + 2) := by
    calc
      (d'.1 : ℝ) < theta * (d.1 : ℝ) := hd'_hi
      _ < theta * theta ^ (k + 1) := by
        have hscale : 0 < theta * (theta ^ (k + 1) - (d.1 : ℝ)) :=
          mul_pos htpos (sub_pos.mpr hdhi)
        nlinarith
      _ = theta ^ (k + 2) := by rw [show k + 2 = (k + 1) + 1 by omega, pow_succ]; ring
  have hprod_lo : theta ^ (2 * k - 1) < ((d.1 * d'.1 : ℕ) : ℝ) := by
    have hmul : (d.1 : ℝ) * theta ^ (k - 1) < (d.1 : ℝ) * (d'.1 : ℝ) := by
      have hscale : 0 < (d.1 : ℝ) * ((d'.1 : ℝ) - theta ^ (k - 1)) :=
        mul_pos hdpos (sub_pos.mpr hsecond_lo)
      nlinarith
    have hpow : theta ^ (2 * k - 1) = theta ^ k * theta ^ (k - 1) := by
      rw [← pow_add]
      congr 1
      omega
    rw [hpow]
    exact (mul_le_mul_of_nonneg_right hdlo (by positivity)).trans_lt (by simpa using hmul)
  have hprod_hi : (((d.1 * d'.1 : ℕ) : ℝ)) < theta ^ (2 * k + 3) := by
    have hmul1 : (d.1 : ℝ) * (d'.1 : ℝ) <
        theta ^ (k + 1) * (d'.1 : ℝ) := by
      have hscale : 0 < (d'.1 : ℝ) * (theta ^ (k + 1) - (d.1 : ℝ)) :=
        mul_pos hd'pos (sub_pos.mpr hdhi)
      nlinarith
    have hmul2 : theta ^ (k + 1) * (d'.1 : ℝ) ≤
        theta ^ (k + 1) * theta ^ (k + 2) := by
      exact mul_le_mul_of_nonneg_left (le_of_lt hsecond_hi) (pow_nonneg (le_of_lt htpos) _)
    have hmul : (d.1 : ℝ) * (d'.1 : ℝ) <
        theta ^ (k + 1) * theta ^ (k + 2) := hmul1.trans_le hmul2
    rw [← pow_add] at hmul
    convert hmul using 1 <;> norm_num <;> ring
  refine ⟨?_, ?_, hsecond_lo, hsecond_hi⟩
  · exact_mod_cast hprod_lo
  · exact_mod_cast hprod_hi

theorem p054A : P054AStatement := by
  intro g hg k hk theta htheta sigma hsigma
  constructor <;> unfold intervalSum <;> apply Finset.sum_le_sum <;>
    intro d hd <;> split_ifs
  · exact le_rfl
  · have hdpos : 0 < d := (Finset.mem_filter.mp hd).2.1
    exact hg d hdpos
  · exact le_rfl
  · have hdpos : 0 < d := (Finset.mem_filter.mp hd).2.1
    exact hg d hdpos

lemma modifier_eq_zero_of_lt_sigma_ne_one
    (q : WeightParameters) {t : ℕ} (ht : 0 < t) (htsigma : (t : ℝ) < q.sigma)
    (ht1 : t ≠ 1) : modifierWeight q t = 0 := by
  have htgt : 1 < t := by omega
  obtain ⟨p, hp, hpt⟩ := Nat.exists_prime_and_dvd (ne_of_gt htgt)
  have hple : p ≤ t := Nat.le_of_dvd ht hpt
  have hnotrough : ¬ IsRough t q.sigma := by
    intro hrough
    have hsigp := hrough p hp hpt
    have hptreal : (p : ℝ) ≤ t := by exact_mod_cast hple
    linarith
  have hri : roughIndicator t q.sigma = 0 := by
    simp [roughIndicator, hnotrough]
  simp [modifierWeight, ht, hri]

theorem p057 (W : CommonWeightWitnesses) : P057Statement := by
  intro q Ksh z hz hzsigma
  have hw1_nonneg : 0 ≤ w1Weight Ksh.1 :=
    (W.weight_type q .w1).nonnegative_multiplicative.nonnegative Ksh.1 Ksh.2
  unfold Erdos448.Stage4.shiftedMean
  by_cases hmem : 1 ∈ positiveNatsBelow z
  · calc
      ∑ t ∈ positiveNatsBelow z, modifierWeight q t * w1Weight (t * Ksh.1) =
          modifierWeight q 1 * w1Weight (1 * Ksh.1) := by
            apply Finset.sum_eq_single 1
            intro t ht ht1
            have htdata := (Finset.mem_filter.mp ht).2
            rw [modifier_eq_zero_of_lt_sigma_ne_one q htdata.1
              (htdata.2.trans hzsigma) ht1]
            simp
            intro hnot
            exact (hnot hmem).elim
      _ = w1Weight Ksh.1 := by rw [(W.modifier q).normalized]; simp
      _ ≤ w1Weight Ksh.1 := le_rfl
  · have hzero : ∑ t ∈ positiveNatsBelow z,
        modifierWeight q t * w1Weight (t * Ksh.1) = 0 := by
      apply Finset.sum_eq_zero
      intro t ht
      have ht1 : t ≠ 1 := by
        intro h
        subst t
        exact hmem ht
      have htdata := (Finset.mem_filter.mp ht).2
      rw [modifier_eq_zero_of_lt_sigma_ne_one q htdata.1
        (htdata.2.trans hzsigma) ht1]
      simp
    rw [hzero]
    exact hw1_nonneg

end

end Erdos448.Stage7.ROOT06.Elementary
