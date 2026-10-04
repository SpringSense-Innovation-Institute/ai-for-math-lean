module

import all Mathlib.Basic.Real.Basic
public import Erdos448.stage6.TaskContracts

public section

set_option backward.isDefEq.respectTransparency false

namespace Erdos448.Stage7.ROOT04.Helpers

open Erdos448.Stage4
open Erdos448.Stage4.Contracts
open Finset
open scoped BigOperators

noncomputable section

instance (p : Prop) : Decidable p := Classical.propDecidable p

lemma isRough_mul_iff (a b : ℕ) (s : ℝ) :
    IsRough (a * b) s ↔ IsRough a s ∧ IsRough b s := by
  constructor
  · intro h
    constructor
    · intro p hp hpa
      exact h p hp (dvd_mul_of_dvd_left hpa b)
    · intro p hp hpb
      exact h p hp (dvd_mul_of_dvd_right hpb a)
  · rintro ⟨ha, hb⟩ p hp hpab
    rcases hp.dvd_mul.mp hpab with hpa | hpb
    · exact ha p hp hpa
    · exact hb p hp hpb

lemma roughIndicator_mul (a b : ℕ) (s : ℝ) :
    roughIndicator (a * b) s = roughIndicator a s * roughIndicator b s := by
  classical
  by_cases ha : IsRough a s <;> by_cases hb : IsRough b s
  · have hab : IsRough (a * b) s := (isRough_mul_iff a b s).2 ⟨ha, hb⟩
    simp [roughIndicator, ha, hb, hab]
  · have hab : ¬ IsRough (a * b) s := fun h => hb ((isRough_mul_iff a b s).1 h).2
    simp [roughIndicator, ha, hb, hab]
  · have hab : ¬ IsRough (a * b) s := fun h => ha ((isRough_mul_iff a b s).1 h).1
    simp [roughIndicator, ha, hb, hab]
  · have hab : ¬ IsRough (a * b) s := fun h => ha ((isRough_mul_iff a b s).1 h).1
    simp [roughIndicator, ha, hb, hab]

lemma roughIndicator_eq_one_iff (a : ℕ) (s : ℝ) :
    roughIndicator a s = 1 ↔ IsRough a s := by
  classical
  simp [roughIndicator]

lemma roughIndicator_nonneg (a : ℕ) (s : ℝ) :
    0 ≤ (roughIndicator a s : ℝ) := by positivity

lemma omegaBelow_mono {m : PosNat} {u v : ℝ} (huv : u ≤ v) :
    omegaBelow m u ≤ omegaBelow m v := by
  unfold omegaBelow
  exact Finset.sum_le_sum fun p hp => by
    by_cases hpu : (p : ℝ) < u
    · have hpv : (p : ℝ) < v := lt_of_lt_of_le hpu huv
      simp [hpu, hpv]
    · simp [hpu]

lemma omegaBelowRaw_mono {m : ℕ} {u v : ℝ} (huv : u ≤ v) :
    omegaBelowRaw m u ≤ omegaBelowRaw m v := by
  by_cases hm : 0 < m
  · simpa [omegaBelowRaw, hm] using omegaBelow_mono (m := ⟨m, hm⟩) huv
  · simp [omegaBelowRaw, hm]

lemma good_upper (q : GoodParameters) (n m : PosNat) (hgood : Good q n m)
    {u : ℝ} (hU : goodU0 q ≤ u) (hun : u < n.1) :
    (omegaBelow m u : ℝ) ≤
      (1 / 2 + q.epsilonInt) * Real.log (Real.log u / Real.log q.sigma) := by
  have h := hgood u hU hun
  have hle :
      (omegaBelow m u : ℝ) -
          (1 / 2) * Real.log (Real.log u / Real.log q.sigma) ≤
        |(omegaBelow m u : ℝ) -
          (1 / 2) * Real.log (Real.log u / Real.log q.sigma)| :=
    le_abs_self _
  nlinarith

lemma log_xi_pos (q : GoodParameters) : 0 < Real.log q.xi :=
  Real.log_pos q.xi_gt_one

lemma log_sigma_pos (q : GoodParameters) : 0 < Real.log q.sigma :=
  Real.log_pos (lt_of_lt_of_le (by norm_num) q.sigma_ge_two)

lemma good_forces_one_le_log_xi (q : GoodParameters) (n m : PosNat)
    (hn : goodU0 q < n.1) (hgood : Good q n m) :
    1 ≤ Real.log q.xi := by
  have hdev := hgood (goodU0 q) le_rfl hn
  have heps : 0 < q.epsilonInt := q.epsilonInt_pos
  have hnonneg : 0 ≤ Real.log (Real.log (goodU0 q) / Real.log q.sigma) := by
    have habs : 0 ≤ |(omegaBelow m (goodU0 q) : ℝ) -
        (1 / 2) * Real.log (Real.log (goodU0 q) / Real.log q.sigma)| := abs_nonneg _
    nlinarith
  have hlogs : Real.log q.sigma ≠ 0 := ne_of_gt (log_sigma_pos q)
  have hprod : 0 < Real.log q.xi * Real.log q.sigma :=
    mul_pos (log_xi_pos q) (log_sigma_pos q)
  have hlogU : Real.log (goodU0 q) = Real.log q.xi * Real.log q.sigma := by
    simp [goodU0, hprod.ne']
  have hratio : Real.log (goodU0 q) / Real.log q.sigma = Real.log q.xi := by
    rw [hlogU]
    field_simp
  rw [hratio] at hnonneg
  exact (Real.log_nonneg_iff (log_xi_pos q)).mp hnonneg

lemma one_le_rpow_product {B y Q om : ℝ}
    (hB : 0 < B) (hy0 : 0 < y) (hy1 : y < 1)
    (hom : om ≤ Q * Real.log B) :
    1 ≤ B.rpow (-Q * Real.log y) * y.rpow om := by
  change 1 ≤ B ^ (-Q * Real.log y) * y ^ om
  rw [Real.rpow_def_of_pos hB, Real.rpow_def_of_pos hy0, ← Real.exp_add, ← Real.exp_zero]
  apply Real.exp_le_exp.mpr
  have hlogy : Real.log y < 0 := Real.log_neg hy0 hy1
  nlinarith

lemma fkSharp_nonneg (q : SharpParameters) (n : PosNat) : 0 ≤ fkSharp q n := by
  unfold fkSharp
  apply mul_nonneg
  · positivity
  · apply Finset.sum_nonneg
    intro d hd
    apply Finset.sum_nonneg
    intro d' hd'
    apply Finset.sum_nonneg
    intro t ht
    split_ifs
    · exact mul_nonneg
        (mul_nonneg (roughIndicator_nonneg d q.sigma)
          (Real.rpow_nonneg (le_of_lt q.y_pos) _))
        (roughIndicator_nonneg t q.sigma)
    all_goals positivity

end

end Erdos448.Stage7.ROOT04.Helpers
