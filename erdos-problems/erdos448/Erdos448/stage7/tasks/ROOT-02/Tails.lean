module

import all Mathlib.Basic.Real.Basic
public import Erdos448.stage7.tasks.«ROOT-02».Mean

public section

set_option backward.isDefEq.respectTransparency false

namespace Erdos448.Stage7.ROOT02.Tails

open Finset Set
open scoped BigOperators
open Erdos448.Stage4
open Erdos448.Stage4.Contracts

noncomputable section

instance (p : Prop) : Decidable p := Classical.propDecidable p

lemma roughTau_pos (n : PosNat) (s : ℝ) : 0 < roughTau n s := by
  unfold roughTau divisorSet
  have hone : 1 ∈ n.1.divisors :=
    Nat.mem_divisors.mpr ⟨one_dvd _, n.property.ne'⟩
  have hr : IsRough 1 s := by
    intro p hp hpd
    exact (hp.ne_one (Nat.dvd_one.mp hpd)).elim
  have hind : roughIndicator 1 s = 1 := by
    simp [roughIndicator, hr]
  have h := Finset.single_le_sum
    (fun d _ => Nat.zero_le (roughIndicator d s)) hone
  have hsum : 1 ≤ ∑ d ∈ n.1.divisors, roughIndicator d s := by
    simpa only [hind] using h
  omega

lemma log_ratio_gt_one (q : MomentParameters) :
    1 < Real.log q.u / Real.log q.sigma := by
  have hs1 : 1 < q.sigma :=
    one_lt_two.trans_le (q.theta_ge_two.trans q.sigma_ge_theta)
  have hslog : 0 < Real.log q.sigma := Real.log_pos hs1
  have hulog : Real.log q.sigma < Real.log q.u :=
    Real.strictMonoOn_log
      (show q.sigma ∈ Set.Ioi 0 by exact zero_lt_one.trans hs1)
      (show q.u ∈ Set.Ioi 0 by exact (zero_lt_one.trans hs1).trans q.u_gt_sigma)
      q.u_gt_sigma
  exact (one_lt_div hslog).2 hulog

lemma upper_markov_term
    {y R : ℝ} (hy : 1 < y) (hR : 1 < R) {k : ℕ}
    (hk : (y / 2) * Real.log R < k) :
    1 ≤ y.rpow (k : ℝ) * R.rpow (-(y / 2) * Real.log y) := by
  have hy0 : 0 < y := zero_lt_one.trans hy
  have hR0 : 0 < R := zero_lt_one.trans hR
  have hconvert :
      R.rpow (-(y / 2) * Real.log y) =
        y.rpow (-((y / 2) * Real.log R)) := by
    change R ^ (-(y / 2) * Real.log y) =
      y ^ (-((y / 2) * Real.log R))
    rw [Real.rpow_def_of_pos hR0, Real.rpow_def_of_pos hy0]
    congr 1
    ring
  rw [hconvert]
  change 1 ≤ y ^ (k : ℝ) * y ^ (-((y / 2) * Real.log R))
  rw [← Real.rpow_add hy0]
  apply Real.one_le_rpow hy.le
  exact sub_nonneg.mpr hk.le

lemma lower_markov_term
    {y R : ℝ} (hy : 0 < y) (hy1 : y < 1) (hR : 1 < R) {k : ℕ}
    (hk : (k : ℝ) < (y / 2) * Real.log R) :
    1 ≤ y.rpow (k : ℝ) * R.rpow (-(y / 2) * Real.log y) := by
  have hR0 : 0 < R := zero_lt_one.trans hR
  have hconvert :
      R.rpow (-(y / 2) * Real.log y) =
        y.rpow (-((y / 2) * Real.log R)) := by
    change R ^ (-(y / 2) * Real.log y) =
      y ^ (-((y / 2) * Real.log R))
    rw [Real.rpow_def_of_pos hR0, Real.rpow_def_of_pos hy]
    congr 1
    ring
  rw [hconvert]
  change 1 ≤ y ^ (k : ℝ) * y ^ (-((y / 2) * Real.log R))
  rw [← Real.rpow_add hy]
  apply Real.one_le_rpow_of_pos_of_le_one_of_nonpos hy hy1.le
  exact sub_nonpos.mpr hk.le

lemma upper_count_bound (q : MomentParameters) (hy : 1 < q.y)
    (n : PosNat) :
    (upperTailCount q n : ℝ) ≤
      (∑ d ∈ divisorSet n,
          q.y.rpow (omegaBelowRaw d q.u : ℝ) *
            (roughIndicator d q.sigma : ℝ)) *
        (Real.log q.u / Real.log q.sigma).rpow
          (-(q.y / 2) * Real.log q.y) := by
  let S := (divisorSet n).filter fun d =>
    roughIndicator d q.sigma = 1 ∧
      (q.y / 2) * Real.log (Real.log q.u / Real.log q.sigma) <
        omegaBelowRaw d q.u
  let T := (Real.log q.u / Real.log q.sigma).rpow
    (-(q.y / 2) * Real.log q.y)
  have hR := log_ratio_gt_one q
  have hT0 : 0 ≤ T := Real.rpow_nonneg (zero_lt_one.trans hR).le _
  change (S.card : ℝ) ≤ _
  rw [Finset.sum_mul]
  calc
    (S.card : ℝ) = ∑ d ∈ S, (1 : ℝ) := by simp
    _ ≤ ∑ d ∈ S,
        (q.y.rpow (omegaBelowRaw d q.u : ℝ) *
          (roughIndicator d q.sigma : ℝ)) * T := by
      apply Finset.sum_le_sum
      intro d hd
      have hd' := (Finset.mem_filter.mp hd).2
      rw [show (roughIndicator d q.sigma : ℝ) = 1 by exact_mod_cast hd'.1]
      simp only [mul_one]
      exact upper_markov_term hy hR hd'.2
    _ ≤ ∑ d ∈ divisorSet n,
        (q.y.rpow (omegaBelowRaw d q.u : ℝ) *
          (roughIndicator d q.sigma : ℝ)) * T := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro d hd hdS
      exact mul_nonneg
        (mul_nonneg (Real.rpow_nonneg q.y_pos.le _) (Nat.cast_nonneg _)) hT0

lemma lower_count_bound (q : MomentParameters) (hy1 : q.y < 1)
    (n : PosNat) :
    (lowerTailCount q n : ℝ) ≤
      (∑ d ∈ divisorSet n,
          q.y.rpow (omegaBelowRaw d q.u : ℝ) *
            (roughIndicator d q.sigma : ℝ)) *
        (Real.log q.u / Real.log q.sigma).rpow
          (-(q.y / 2) * Real.log q.y) := by
  let S := (divisorSet n).filter fun d =>
    roughIndicator d q.sigma = 1 ∧
      (omegaBelowRaw d q.u : ℝ) <
        (q.y / 2) * Real.log (Real.log q.u / Real.log q.sigma)
  let T := (Real.log q.u / Real.log q.sigma).rpow
    (-(q.y / 2) * Real.log q.y)
  have hR := log_ratio_gt_one q
  have hT0 : 0 ≤ T := Real.rpow_nonneg (zero_lt_one.trans hR).le _
  change (S.card : ℝ) ≤ _
  rw [Finset.sum_mul]
  calc
    (S.card : ℝ) = ∑ d ∈ S, (1 : ℝ) := by simp
    _ ≤ ∑ d ∈ S,
        (q.y.rpow (omegaBelowRaw d q.u : ℝ) *
          (roughIndicator d q.sigma : ℝ)) * T := by
      apply Finset.sum_le_sum
      intro d hd
      have hd' := (Finset.mem_filter.mp hd).2
      rw [show (roughIndicator d q.sigma : ℝ) = 1 by exact_mod_cast hd'.1]
      simp only [mul_one]
      exact lower_markov_term q.y_pos hy1 hR hd'.2
    _ ≤ ∑ d ∈ divisorSet n,
        (q.y.rpow (omegaBelowRaw d q.u : ℝ) *
          (roughIndicator d q.sigma : ℝ)) * T := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro d hd hdS
      exact mul_nonneg
        (mul_nonneg (Real.rpow_nonneg q.y_pos.le _) (Nat.cast_nonneg _)) hT0

lemma upper_point_bound (q : MomentParameters) (hy : 1 < q.y)
    (n : PosNat) :
    tailPointSubject true q n ≤
      moment q n *
        (Real.log q.u / Real.log q.sigma).rpow
          (-(q.y / 2) * Real.log q.y) := by
  unfold tailPointSubject moment
  simp only [if_true]
  have hfactor : 0 ≤
      (roughIndicator n.1 q.theta : ℝ) / roughTau n q.sigma :=
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_left (upper_count_bound q hy n) hfactor

lemma lower_point_bound (q : MomentParameters) (hy : q.y < 1)
    (n : PosNat) :
    tailPointSubject false q n ≤
      moment q n *
        (Real.log q.u / Real.log q.sigma).rpow
          (-(q.y / 2) * Real.log q.y) := by
  simp only [tailPointSubject, Bool.false_eq_true, ite_false, moment]
  have hfactor : 0 ≤
      (roughIndicator n.1 q.theta : ℝ) / roughTau n q.sigma :=
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_left (lower_count_bound q hy n) hfactor

lemma singleton_domain {y : ℝ} (hy0 : 0 < y) (hy2 : y < 2) :
    CompactMomentDomain ({y} : Set ℝ) := by
  refine ⟨Set.singleton_nonempty y, isCompact_singleton, ?_⟩
  intro z hz
  simpa only [Set.mem_singleton_iff] using hz.symm ▸ ⟨hy0, hy2⟩

lemma tail_mean_bound
    (h011 : P011Statement) (upper : Bool)
    (y : ℝ) (hy0 : 0 < y) (hy2 : y < 2)
    (hpoint : ∀ q : MomentParameters, q.y = y → ∀ n : PosNat,
      tailPointSubject upper q n ≤
        moment q n *
          (Real.log q.u / Real.log q.sigma).rpow
            (-(q.y / 2) * Real.log q.y)) :
    Nonempty (TailOutput upper y hy0 hy2) := by
  let Y : Set ℝ := {y}
  have hY : CompactMomentDomain Y := singleton_domain hy0 hy2
  rcases h011 Y hY with ⟨mean⟩
  refine ⟨{
    C_y := mean.C_Y
    C_y_pos := mean.C_Y_pos
    bound := ?_
  }⟩
  intro theta sigma u x htheta hsigma hu hux hx
  dsimp
  let q : MomentParameters :=
    { y := y, y_pos := hy0, y_lt_two := hy2,
      theta := theta, theta_ge_two := htheta,
      sigma := sigma, sigma_ge_theta := hsigma,
      u := u, u_gt_sigma := hu }
  let T := (Real.log u / Real.log sigma).rpow
    (-(y / 2) * Real.log y)
  have hpoint' : ∀ n : PosNat,
      tailPointSubject upper q n ≤ moment q n * T := by
    intro n
    exact hpoint q rfl n
  have hmeanPoint : tailMeanSubject upper q x ≤
      strictMean (momentWeight q) x * T := by
    unfold tailMeanSubject strictMean
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro n hn
    have hnpos : 0 < n := (Finset.mem_filter.mp hn).2.1
    simp only [dif_pos hnpos]
    simpa [momentWeight, hnpos] using hpoint' ⟨n, hnpos⟩
  have hyY : y ∈ Y := Set.mem_singleton y
  have hmean := mean.bound y hyY theta sigma u x htheta hsigma hu hux hx
  dsimp only at hmean
  have hR0 : 0 < Real.log u / Real.log sigma := by
    simpa [q] using zero_lt_one.trans (log_ratio_gt_one q)
  have hT0 : 0 ≤ T := Real.rpow_nonneg hR0.le _
  refine ⟨?_, ?_⟩
  · exact hpoint'
  · calc
      tailMeanSubject upper q x ≤ strictMean (momentWeight q) x * T := hmeanPoint
      _ ≤ (mean.C_Y * x * roughDensity theta *
          (Real.log u / Real.log sigma).rpow ((y - 1) / 2)) * T :=
        mul_le_mul_of_nonneg_right hmean hT0
      _ = mean.C_Y * x * roughDensity theta *
          (Real.log u / Real.log sigma).rpow
            ((y - 1 - y * Real.log y) / 2) := by
        have hR : 0 < Real.log u / Real.log sigma := by
          exact zero_lt_one.trans (log_ratio_gt_one q)
        dsimp [T]
        let A := mean.C_Y * x * roughDensity theta
        calc
          A * (Real.log u / Real.log sigma).rpow ((y - 1) / 2) *
              (Real.log u / Real.log sigma).rpow (-(y / 2) * Real.log y) =
              A * ((Real.log u / Real.log sigma).rpow ((y - 1) / 2) *
                (Real.log u / Real.log sigma).rpow (-(y / 2) * Real.log y)) := by ring
          _ = A * (Real.log u / Real.log sigma).rpow
              ((y - 1) / 2 + (-(y / 2) * Real.log y)) := by
                change A * ((Real.log u / Real.log sigma) ^ ((y - 1) / 2) *
                    (Real.log u / Real.log sigma) ^ (-(y / 2) * Real.log y)) =
                  A * (Real.log u / Real.log sigma) ^
                    ((y - 1) / 2 + (-(y / 2) * Real.log y))
                rw [Real.rpow_add hR]
          _ = A * (Real.log u / Real.log sigma).rpow
              ((y - 1 - y * Real.log y) / 2) := by
                congr 2
                ring

theorem p012 (h011 : P011Statement) : P012Statement := by
  intro y hy hy2
  apply tail_mean_bound h011 true y (zero_lt_one.trans hy) hy2
  intro q hqy n
  subst y
  exact upper_point_bound q hy n

theorem p013 (h011 : P011Statement) : P013Statement := by
  intro y hy hy1
  apply tail_mean_bound h011 false y hy (hy1.trans one_lt_two)
  intro q hqy n
  subst y
  exact lower_point_bound q hy1 n

end

end Erdos448.Stage7.ROOT02.Tails
