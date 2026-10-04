module

import all Mathlib.Basic.Real.Basic
public import Erdos448.stage6.TaskContracts

public section

set_option backward.isDefEq.respectTransparency false

namespace Erdos448.Stage7.ROOT07.Smoothing

open Finset
open scoped BigOperators

open Erdos448.Stage4
open Erdos448.Stage4.Contracts

noncomputable section

lemma mem_positiveNatsBelow {z : ℝ} {n : ℕ} :
    n ∈ positiveNatsBelow z ↔ 0 < n ∧ (n : ℝ) < z := by
  constructor
  · intro hn
    exact (Finset.mem_filter.mp hn).2
  · rintro ⟨hn, hnz⟩
    rw [positiveNatsBelow, Finset.mem_filter]
    exact ⟨by simpa using Nat.lt_ceil.mpr hnz, hn, hnz⟩

lemma isRough_mul_iff (a b : ℕ) (s : ℝ) :
    IsRough (a * b) s ↔ IsRough a s ∧ IsRough b s := by
  constructor
  · intro h
    exact ⟨fun p hp hpa => h p hp (dvd_mul_of_dvd_left hpa b),
      fun p hp hpb => h p hp (dvd_mul_of_dvd_right hpb a)⟩
  · rintro ⟨ha, hb⟩ p hp hpab
    rcases hp.dvd_mul.mp hpab with hpa | hpb
    · exact ha p hp hpa
    · exact hb p hp hpb

lemma roughIndicator_mul (a b : ℕ) (s : ℝ) :
    roughIndicator (a * b) s = roughIndicator a s * roughIndicator b s := by
  by_cases ha : IsRough a s <;> by_cases hb : IsRough b s
  · have hab := (isRough_mul_iff a b s).2 ⟨ha, hb⟩
    simp [roughIndicator, ha, hb, hab]
  · have hab : ¬ IsRough (a * b) s := fun h => hb ((isRough_mul_iff a b s).1 h).2
    simp [roughIndicator, ha, hb, hab]
  · have hab : ¬ IsRough (a * b) s := fun h => ha ((isRough_mul_iff a b s).1 h).1
    simp [roughIndicator, ha, hb, hab]
  · have hab : ¬ IsRough (a * b) s := fun h => ha ((isRough_mul_iff a b s).1 h).1
    simp [roughIndicator, ha, hb, hab]

lemma omegaBelowRaw_mul {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (u : ℝ) :
    omegaBelowRaw (a * b) u = omegaBelowRaw a u + omegaBelowRaw b u := by
  simp only [omegaBelowRaw, dif_pos ha, dif_pos hb, dif_pos (Nat.mul_pos ha hb),
    omegaBelow]
  change (a * b).factorization.sum (fun p e => if (p : ℝ) < u then e else 0) =
    a.factorization.sum (fun p e => if (p : ℝ) < u then e else 0) +
      b.factorization.sum (fun p e => if (p : ℝ) < u then e else 0)
  rw [Nat.factorization_mul (Nat.ne_of_gt ha) (Nat.ne_of_gt hb)]
  apply Finsupp.sum_add_index'
  · intro p
    simp
  · intro p e₁ e₂
    by_cases hp : (p : ℝ) < u <;> simp [hp]

lemma modifier_split (q : WeightParameters) {d t : ℕ}
    (hd : 0 < d) (ht : 0 < t) :
    (roughIndicator (d * t) q.sigma : ℝ) *
        q.y.rpow (omegaBelowRaw (d * t) (q.theta ^ q.k) : ℝ) =
      ((roughIndicator d q.sigma : ℝ) *
        q.y.rpow (omegaBelowRaw d (q.theta ^ q.k) : ℝ)) *
        modifierWeight q t := by
  simp only [modifierWeight, if_pos ht]
  rw [roughIndicator_mul, omegaBelowRaw_mul hd ht, Nat.cast_add]
  have hyadd :
      q.y.rpow ((omegaBelowRaw d (q.theta ^ q.k) : ℝ) +
          (omegaBelowRaw t (q.theta ^ q.k) : ℝ)) =
        q.y.rpow (omegaBelowRaw d (q.theta ^ q.k) : ℝ) *
          q.y.rpow (omegaBelowRaw t (q.theta ^ q.k) : ℝ) :=
    Real.rpow_add q.y_pos _ _
  rw [hyadd]
  push_cast
  ring

lemma triangular_inner_eq (x : ℝ) {D t : ℕ}
    (hD : 0 < D) (ht : 0 < t) :
    positiveNatsBelow (x / (t * D : ℕ)) =
      (positiveNatsBelow (x / D)).filter
        (fun m => t ∈ positiveNatsBelow (x / (m * D : ℕ))) := by
  ext m
  simp only [Finset.mem_filter, mem_positiveNatsBelow]
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  constructor
  · rintro ⟨hm, hmBound⟩
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm
    have hprod : (m : ℝ) * (t : ℝ) * (D : ℝ) < x := by
      have := (lt_div_iff₀ (show (0 : ℝ) < (t * D : ℕ) by positivity)).mp hmBound
      norm_num [Nat.cast_mul] at this ⊢
      nlinarith
    have hmOuter : (m : ℝ) < x / (D : ℝ) := by
      apply (lt_div_iff₀ hDR).2
      have htOne : (1 : ℝ) ≤ t := by exact_mod_cast ht
      calc
        (m : ℝ) * D = (m : ℝ) * 1 * D := by ring
        _ ≤ (m : ℝ) * t * D := by gcongr
        _ < x := hprod
    have htInner : (t : ℝ) < x / (m * D : ℕ) := by
      apply (lt_div_iff₀ (show (0 : ℝ) < (m * D : ℕ) by positivity)).2
      norm_num [Nat.cast_mul]
      nlinarith
    exact ⟨⟨hm, hmOuter⟩, ht, htInner⟩
  · rintro ⟨⟨hm, hmOuter⟩, htMem, htBound⟩
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm
    have hprod : (t : ℝ) * ((m : ℝ) * (D : ℝ)) < x := by
      have := (lt_div_iff₀ (show (0 : ℝ) < (m * D : ℕ) by positivity)).mp htBound
      norm_num [Nat.cast_mul] at this ⊢
      exact this
    refine ⟨hm, (lt_div_iff₀ (show (0 : ℝ) < (t * D : ℕ) by positivity)).2 ?_⟩
    norm_num [Nat.cast_mul]
    nlinarith

lemma triangular_swap (x : ℝ) {D : ℕ} (hD : 0 < D)
    (f : ℕ → ℕ → ℝ) :
    (∑ t ∈ positiveNatsBelow (x / D),
        ∑ m ∈ positiveNatsBelow (x / (t * D : ℕ)), f t m) =
      ∑ m ∈ positiveNatsBelow (x / D),
        ∑ t ∈ positiveNatsBelow (x / (m * D : ℕ)), f t m := by
  classical
  let S := positiveNatsBelow (x / D)
  calc
    (∑ t ∈ S, ∑ m ∈ positiveNatsBelow (x / (t * D : ℕ)), f t m) =
        ∑ t ∈ S, ∑ m ∈ S,
          if t ∈ positiveNatsBelow (x / (m * D : ℕ)) then f t m else 0 := by
      apply Finset.sum_congr rfl
      intro t htS
      have ht : 0 < t := (mem_positiveNatsBelow.mp htS).1
      rw [triangular_inner_eq x hD ht]
      simp only [Finset.sum_filter]
      rfl
    _ = ∑ m ∈ S, ∑ t ∈ S,
          if t ∈ positiveNatsBelow (x / (m * D : ℕ)) then f t m else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ m ∈ S, ∑ t ∈ positiveNatsBelow (x / (m * D : ℕ)), f t m := by
      apply Finset.sum_congr rfl
      intro m hmS
      have hm : 0 < m := (mem_positiveNatsBelow.mp hmS).1
      rw [← Finset.sum_filter]
      congr 1
      ext t
      simp only [Finset.mem_filter]
      constructor
      · exact fun h => h.2
      · intro htInner
        have heq := triangular_inner_eq x hD hm
        have hmem : t ∈ (positiveNatsBelow (x / D)).filter
            (fun t => m ∈ positiveNatsBelow (x / (t * D : ℕ))) := by
          rw [← heq]
          exact htInner
        exact ⟨(Finset.mem_filter.mp hmem).1, htInner⟩

theorem p060 (h050 : P050Statement) (h052 : P052Statement) : P060Statement := by
  intro theta htheta
  obtain ⟨C, hC, hsm⟩ := h052 theta htheta
  refine ⟨C, hC, ?_⟩
  intro q hq hSigma x hx
  classical
  rw [h050 q x hx]
  unfold fourVariableInversion smoothedRegular
  simp only [partitionAccepts, if_true]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro d hdSet
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro d' hd'Set
  by_cases hd : 0 < d
  · by_cases hd' : 0 < d'
    · by_cases houter : q.theta ^ q.k ≤ (d : ℝ) ∧
          Close q.theta ⟨d, hd⟩ ⟨d', hd'⟩
      · simp only [hd, hd', houter, true_and, and_true, dite_true, if_true]
        let D := d * d'
        let A : ℝ := (roughIndicator d q.sigma : ℝ) *
          q.y.rpow (omegaBelowRaw d (q.theta ^ q.k) : ℝ)
        have hD : 0 < D := Nat.mul_pos hd hd'
        have hA : 0 ≤ A := mul_nonneg (by positivity) (Real.rpow_nonneg q.y_pos.le _)
        have hxPos : 0 < x := by
          have hp : 0 < q.theta ^ (2 * q.k - 1) :=
            pow_pos (lt_of_lt_of_le (by norm_num) q.theta_ge_two) _
          linarith
        have hterms :
            (∑ t ∈ positiveNatsBelow (x / D),
              (roughIndicator (d * t) q.sigma : ℝ) *
                q.y.rpow (omegaBelowRaw (d * t) (q.theta ^ q.k) : ℝ) *
                (∑ m ∈ positiveNatsBelow (x / (t * d * d' : ℕ)),
                  a0Weight (m * t * d * d'))) ≤
              C * (A * ∑ m ∈ positiveNatsBelow (x / D),
                (safeLog m).rpow (-1 / 2) *
                  shiftedMean q (zValue x m d d') ⟨D, hD⟩) := by
          calc
            _ ≤ ∑ t ∈ positiveNatsBelow (x / D),
                (roughIndicator (d * t) q.sigma : ℝ) *
                  q.y.rpow (omegaBelowRaw (d * t) (q.theta ^ q.k) : ℝ) *
                  (C * w1Weight (t * D) * safeLogHalfSum (x / (t * D : ℕ))) := by
              apply Finset.sum_le_sum
              intro t htSet
              have ht : 0 < t := (mem_positiveNatsBelow.mp htSet).1
              have hz : 0 < x / (t * D : ℕ) := div_pos hxPos (by positivity)
              have hbound := hsm q hq ⟨t * D, Nat.mul_pos ht hD⟩
                (x / (t * D : ℕ)) hz
              have hcoeff : 0 ≤ (roughIndicator (d * t) q.sigma : ℝ) *
                  q.y.rpow (omegaBelowRaw (d * t) (q.theta ^ q.k) : ℝ) :=
                mul_nonneg (by positivity) (Real.rpow_nonneg q.y_pos.le _)
              have hin :
                  (∑ m ∈ positiveNatsBelow (x / (t * d * d' : ℕ)),
                    a0Weight (m * t * d * d')) =
                    reciprocalDivisorSum (x / (t * D : ℕ)) ⟨t * D, Nat.mul_pos ht hD⟩ := by
                unfold reciprocalDivisorSum D
                simp only [Nat.mul_assoc]
              rw [hin]
              exact mul_le_mul_of_nonneg_left hbound hcoeff
            _ = C * (A * ∑ m ∈ positiveNatsBelow (x / D),
                (safeLog m).rpow (-1 / 2) *
                  shiftedMean q (zValue x m d d') ⟨D, hD⟩) := by
              have hsplit :
                  (∑ t ∈ positiveNatsBelow (x / D),
                    (roughIndicator (d * t) q.sigma : ℝ) *
                      q.y.rpow (omegaBelowRaw (d * t) (q.theta ^ q.k) : ℝ) *
                      (C * w1Weight (t * D) * safeLogHalfSum (x / (t * D : ℕ)))) =
                    ∑ t ∈ positiveNatsBelow (x / D),
                      (A * modifierWeight q t) *
                        (C * w1Weight (t * D) * safeLogHalfSum (x / (t * D : ℕ))) := by
                apply Finset.sum_congr rfl
                intro t htSet
                rw [modifier_split q hd (mem_positiveNatsBelow.mp htSet).1]
              rw [hsplit]
              simp_rw [safeLogHalfSum, Finset.mul_sum]
              rw [triangular_swap x hD (fun t m =>
                (A * modifierWeight q t) *
                  (C * w1Weight (t * D) * (safeLog m).rpow (-1 / 2)))]
              unfold Erdos448.Stage4.shiftedMean zValue A D
              simp_rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro m hm
              simp only [Nat.mul_assoc]
              apply Finset.sum_congr rfl
              intro t ht
              ring
        simpa [D, A] using hterms
      · simp [hd, hd', houter]
    · simp [hd']
  · simp [hd]

end

end Erdos448.Stage7.ROOT07.Smoothing
