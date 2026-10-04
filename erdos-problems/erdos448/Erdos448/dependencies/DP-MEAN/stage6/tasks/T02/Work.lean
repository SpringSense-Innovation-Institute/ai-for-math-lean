module

import all Mathlib.Basic.Real.Basic
public import Erdos448.dependencies.«DP-MEAN».stage6.shared.TaskInterfaces

public section

set_option backward.isDefEq.respectTransparency false

namespace Erdos448.DPMean.TaskT02

open Erdos448.DPMean

@[expose] abbrev PublicTarget : Prop := Erdos448.DPMean.S6.T02Target

lemma weightedGeometricTail_summable (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Summable (fun r : ℕ => if 2 ≤ r then (r : ℝ) * q ^ r else 0) := by
  have hfull : Summable (fun r : ℕ => (r : ℝ) * q ^ r) :=
    (hasSum_coe_mul_geometric_of_norm_lt_one
      (by simpa [Real.norm_eq_abs, abs_of_nonneg hq0] using hq1)).summable
  apply (hfull.indicator {r : ℕ | 2 ≤ r}).congr
  intro r
  by_cases hr : 2 ≤ r <;> simp [Set.indicator, hr]

lemma weightedGeometricTail_tsum (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    (∑' r : ℕ, if 2 ≤ r then (r : ℝ) * q ^ r else 0) =
      q ^ 2 * (2 - q) / (1 - q) ^ 2 := by
  let f : ℕ → ℝ := fun r => (r : ℝ) * q ^ r
  have hnorm : ‖q‖ < 1 := by
    simpa [Real.norm_eq_abs, abs_of_nonneg hq0] using hq1
  have hfull : Summable f :=
    (hasSum_coe_mul_geometric_of_norm_lt_one hnorm).summable
  have hcut : Summable (fun r : ℕ => if 2 ≤ r then f r else 0) := by
    apply (hfull.indicator {r : ℕ | 2 ≤ r}).congr
    intro r
    by_cases hr : 2 ≤ r <;> simp [Set.indicator, hr]
  have hcut_shift :
      (∑' r : ℕ, if 2 ≤ r then f r else 0) = ∑' n : ℕ, f (n + 2) := by
    have hsplit := hcut.sum_add_tsum_nat_add 2
    norm_num [f, Finset.sum_range_succ] at hsplit
    calc
      (∑' r : ℕ, if 2 ≤ r then f r else 0) =
          ∑' n : ℕ, (if 2 ≤ n + 2 then f (n + 2) else 0) := by
            simpa [f] using hsplit.symm
      _ = ∑' n : ℕ, f (n + 2) := by
        apply tsum_congr
        intro n
        simp
  have htail : (∑' n : ℕ, f (n + 2)) = q / (1 - q) ^ 2 - q := by
    have hsplit := hfull.sum_add_tsum_nat_add 2
    rw [tsum_coe_mul_geometric_of_norm_lt_one hnorm] at hsplit
    norm_num [f, Finset.sum_range_succ] at hsplit
    simpa [f] using (eq_sub_of_add_eq' hsplit)
  rw [hcut_shift, htail]
  field_simp [sub_ne_zero.mpr hq1.ne']
  ring

lemma primeLogSquareTerm_nonneg (p : ℕ) : 0 ≤ primeLogSquareTerm p := by
  simp only [primeLogSquareTerm]
  split_ifs with hp
  · exact div_nonneg (Real.log_natCast_nonneg p) (sq_nonneg (p : ℝ))
  · exact le_rfl

lemma primeLogSquareTerm_summable : Summable primeLogSquareTerm := by
  have hbase : Summable (fun n : ℕ => 2 * (n : ℝ) ^ (-(3 / 2 : ℝ))) := by
    exact (Real.summable_nat_rpow.mpr (by norm_num)).mul_left 2
  refine hbase.of_nonneg_of_le primeLogSquareTerm_nonneg ?_
  intro n
  simp only [primeLogSquareTerm]
  split_ifs with hn
  · have hn0 : n ≠ 0 := hn.ne_zero
    have hnx : 0 < (n : ℝ) := by exact_mod_cast hn.pos
    have hlog := Real.log_natCast_le_rpow_div n (show (0 : ℝ) < 1 / 2 by norm_num)
    have hpow : (n : ℝ) ^ (-(3 / 2 : ℝ)) =
        (n : ℝ) ^ (1 / 2 : ℝ) / (n : ℝ) ^ 2 := by
      rw [show -(3 / 2 : ℝ) = (1 / 2 : ℝ) - 2 by norm_num,
        Real.rpow_sub hnx]
      exact congrArg (fun z : ℝ => (n : ℝ) ^ (1 / 2 : ℝ) / z)
        (Real.rpow_natCast (n : ℝ) 2)
    calc
      Real.log (n : ℝ) / (n : ℝ) ^ 2 ≤
          ((n : ℝ) ^ (1 / 2 : ℝ) / (1 / 2 : ℝ)) / (n : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right hlog (sq_nonneg (n : ℝ))
      _ = 2 * (n : ℝ) ^ (-(3 / 2 : ℝ)) := by rw [hpow]; ring
  · exact mul_nonneg (by norm_num) (Real.rpow_nonneg (Nat.cast_nonneg n) _)

lemma localHigherPowerSummable
    (lambda2 : ℝ) (hlambda2_nonneg : 0 ≤ lambda2) (hlambda2_lt_two : lambda2 < 2)
    (p : ℕ) (hp : Nat.Prime p) :
    Summable (fun r : ℕ => higherPowerTerm lambda2 p r) := by
  have hp2 : 2 ≤ p := hp.two_le
  have hp0 : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  let q : ℝ := lambda2 / (p : ℝ)
  have hq0 : 0 ≤ q := div_nonneg hlambda2_nonneg hp0.le
  have hq1 : q < 1 := by
    dsimp [q]
    rw [div_lt_one hp0]
    exact lt_of_lt_of_le hlambda2_lt_two (by exact_mod_cast hp2)
  have htail := weightedGeometricTail_summable q hq0 hq1
  have hmul := htail.mul_left (Real.log (p : ℝ))
  apply hmul.congr
  intro r
  simp only [higherPowerTerm, hp, true_and, q]
  split_ifs <;> ring

lemma innerHigherPower_nonneg
    (lambda2 : ℝ) (hlambda2_nonneg : 0 ≤ lambda2) (p r : ℕ) :
    0 ≤ higherPowerTerm lambda2 p r := by
  simp only [higherPowerTerm]
  split_ifs with h
  · exact mul_nonneg
      (mul_nonneg (Nat.cast_nonneg r) (Real.log_natCast_nonneg p))
      (pow_nonneg (div_nonneg hlambda2_nonneg (Nat.cast_nonneg p)) r)
  · exact le_rfl

lemma innerHigherPower_bound
    (lambda2 : ℝ) (hlambda2_nonneg : 0 ≤ lambda2) (hlambda2_lt_two : lambda2 < 2)
    (p : ℕ) :
    (∑' r : ℕ, higherPowerTerm lambda2 p r) ≤
      (2 * lambda2 ^ 2 / (1 - lambda2 / 2) ^ 2) * primeLogSquareTerm p := by
  by_cases hp : Nat.Prime p
  · have hp2 : 2 ≤ p := hp.two_le
    have hp0 : 0 < (p : ℝ) := by exact_mod_cast hp.pos
    have hlog0 : 0 ≤ Real.log (p : ℝ) := Real.log_natCast_nonneg p
    let q : ℝ := lambda2 / (p : ℝ)
    let rho : ℝ := lambda2 / 2
    have hrho0 : 0 ≤ rho := div_nonneg hlambda2_nonneg (by norm_num)
    have hrho1 : rho < 1 := by dsimp [rho]; linarith
    have hq0 : 0 ≤ q := div_nonneg hlambda2_nonneg hp0.le
    have hq_le_rho : q ≤ rho := by
      dsimp [q, rho]
      rw [div_le_iff₀ hp0]
      calc
        lambda2 = (lambda2 / 2) * 2 := by ring
        _ ≤ (lambda2 / 2) * (p : ℝ) := by
          gcongr
          exact_mod_cast hp2
    have hq1 : q < 1 := hq_le_rho.trans_lt hrho1
    have hden_q : 0 < 1 - q := sub_pos.mpr hq1
    have hden_rho : 0 < 1 - rho := sub_pos.mpr hrho1
    have hfrac : (2 - q) / (1 - q) ^ 2 ≤ 2 / (1 - rho) ^ 2 := by
      rw [div_le_div_iff₀ (sq_pos_of_pos hden_q) (sq_pos_of_pos hden_rho)]
      have hsquare : (1 - rho) ^ 2 ≤ (1 - q) ^ 2 :=
        (sq_le_sq₀ hden_rho.le hden_q.le).2 (by linarith)
      calc
        (2 - q) * (1 - rho) ^ 2 ≤ 2 * (1 - rho) ^ 2 := by
          exact mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg (1 - rho))
        _ ≤ 2 * (1 - q) ^ 2 := by gcongr
    have htsum :
        (∑' r : ℕ, higherPowerTerm lambda2 p r) =
          Real.log (p : ℝ) * (q ^ 2 * (2 - q) / (1 - q) ^ 2) := by
      rw [show (fun r : ℕ => higherPowerTerm lambda2 p r) =
          fun r : ℕ => Real.log (p : ℝ) *
            (if 2 ≤ r then (r : ℝ) * q ^ r else 0) by
        funext r
        simp only [higherPowerTerm, hp, true_and, q]
        split_ifs <;> ring]
      calc
        (∑' r : ℕ, Real.log (p : ℝ) *
            (if 2 ≤ r then (r : ℝ) * q ^ r else 0)) =
            Real.log (p : ℝ) *
              ∑' r : ℕ, (if 2 ≤ r then (r : ℝ) * q ^ r else 0) := tsum_mul_left
        _ = Real.log (p : ℝ) * (q ^ 2 * (2 - q) / (1 - q) ^ 2) := by
          rw [weightedGeometricTail_tsum q hq0 hq1]
    rw [htsum]
    have hmul := mul_le_mul_of_nonneg_left hfrac (mul_nonneg hlog0 (sq_nonneg q))
    calc
      Real.log (p : ℝ) * (q ^ 2 * (2 - q) / (1 - q) ^ 2) =
          (Real.log (p : ℝ) * q ^ 2) * ((2 - q) / (1 - q) ^ 2) := by ring
      _ ≤ (Real.log (p : ℝ) * q ^ 2) * (2 / (1 - rho) ^ 2) := hmul
      _ = (2 * lambda2 ^ 2 / (1 - lambda2 / 2) ^ 2) *
          primeLogSquareTerm p := by
        simp only [primeLogSquareTerm, hp, if_true]
        dsimp [q, rho]
        field_simp [hp0.ne', hden_rho.ne']
  · simp [higherPowerTerm, primeLogSquareTerm, hp]

theorem publicTarget : PublicTarget := by
  intro lambda1 lambda2 hrange
  have hprime : Summable primeLogSquareTerm := primeLogSquareTerm_summable
  have hinner_nonneg : ∀ p : ℕ,
      0 ≤ ∑' r : ℕ, higherPowerTerm lambda2 p r := fun p =>
    tsum_nonneg (innerHigherPower_nonneg lambda2 hrange.lambda2_nonnegative p)
  have hinner_bound : ∀ p : ℕ,
      (∑' r : ℕ, higherPowerTerm lambda2 p r) ≤
        (2 * lambda2 ^ 2 / (1 - lambda2 / 2) ^ 2) * primeLogSquareTerm p :=
    innerHigherPower_bound lambda2 hrange.lambda2_nonnegative hrange.lambda2_lt_two
  have hmajor : Summable (fun p : ℕ =>
      (2 * lambda2 ^ 2 / (1 - lambda2 / 2) ^ 2) * primeLogSquareTerm p) :=
    hprime.mul_left _
  have houter : Summable (fun p : ℕ =>
      ∑' r : ℕ, higherPowerTerm lambda2 p r) :=
    hmajor.of_nonneg_of_le hinner_nonneg hinner_bound
  refine {
    local_summable := fun p hp =>
      localHigherPowerSummable lambda2 hrange.lambda2_nonnegative hrange.lambda2_lt_two p hp
    outer_summable := houter
    prime_log_square_summable := hprime
    bound := ?_
  }
  have hsum := Summable.tsum_le_tsum hinner_bound houter hmajor
  have hmul := mul_le_mul_of_nonneg_left hsum hrange.lambda1_nonnegative
  rw [higherPowerConstant, geometricMajorant]
  calc
    lambda1 * ∑' p : ℕ, ∑' r : ℕ, higherPowerTerm lambda2 p r ≤
        lambda1 * ∑' p : ℕ,
          (2 * lambda2 ^ 2 / (1 - lambda2 / 2) ^ 2) * primeLogSquareTerm p := hmul
    _ = (2 * lambda1 * lambda2 ^ 2 / (1 - lambda2 / 2) ^ 2) *
        ∑' p : ℕ, primeLogSquareTerm p := by
      have hfactor :
          (∑' p : ℕ, (2 * lambda2 ^ 2 / (1 - lambda2 / 2) ^ 2) *
            primeLogSquareTerm p) =
            (2 * lambda2 ^ 2 / (1 - lambda2 / 2) ^ 2) *
              ∑' p : ℕ, primeLogSquareTerm p := tsum_mul_left
      rw [hfactor]
      ring

end Erdos448.DPMean.TaskT02
