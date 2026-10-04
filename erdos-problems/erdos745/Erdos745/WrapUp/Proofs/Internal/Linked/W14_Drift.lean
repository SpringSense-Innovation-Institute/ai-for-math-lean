module

public import Erdos745.WrapUp.Proofs.Internal.Linked.W14_Queue
public import Erdos745.WrapUp.Proofs.Internal.Linked.W14_Base
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Trigonometric

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local simp] Pi.div_def Pi.mul_def Pi.add_def Pi.sub_def Pi.neg_def Pi.inv_def Function.comp_def Pi.pow_def Pi.smul_def Real.rpow_eq_pow

@[expose] public section


/-!
# Exact finite drift and interpolation of the exploration walk

The predictable increment is the actual query size times the remaining
pool density, minus one.  The finite identity below keeps the root correction
and the distinction between the initial and current pool densities.
-/

namespace Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_DriftFinite

open Erdos745.WrapUp
open Erdos745.WrapUp.Proofs.Internal.W01_ENUM_Finite
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_Finite
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_Reveal
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_FiniteHorizon
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_Horizon
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_QueueControl
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

def rootIndicator {n : ℕ} (G : Graph n) (j : ℕ) : ℝ :=
  if (explore G j).queue = [] then 1 else 0

/-- Query size, time, the active queue, and the new-root indicator partition
the `n` vertices before exploration terminates. -/
theorem queryCard_balance {n : ℕ} (G : Graph n) (j : ℕ)
    (hj : j < n) :
    ((revealQuery (explore G j)).card : ℝ) + j +
      ((explore G j).queue.length : ℝ) + rootIndicator G j = n := by
  have hd := queryCard_exact G j hj
  have hparts := processed_card_add_queue_length G j
  rw [processed_card_of_le G j hj.le] at hparts
  have hseen : (explore G j).seen.card ≤ n := by
    simpa using! Finset.card_le_card
      (Finset.subset_univ (explore G j).seen)
  have hq : j + (explore G j).queue.length ≤ n := by omega
  have hfull : j + (explore G j).queue.length +
      (if (explore G j).queue = [] then 1 else 0) ≤ n := by
    by_cases hroot : (explore G j).queue = []
    · simp [hroot] at *
      omega
    · simp [hroot] at *
      omega
  have hnat : (revealQuery (explore G j)).card + j +
      (explore G j).queue.length +
      (if (explore G j).queue = [] then 1 else 0) = n := by
    omega
  have hreal : ((revealQuery (explore G j)).card : ℝ) + j +
      ((explore G j).queue.length : ℝ) +
      ((if (explore G j).queue = [] then 1 else 0 : ℕ) : ℝ) = n := by
    exact_mod_cast hnat
  simpa [rootIndicator] using! hreal

private theorem sum_range_cast (k : ℕ) :
    (∑ j ∈ Finset.range k, (j : ℝ)) =
      (k : ℝ) * ((k : ℝ) - 1) / 2 := by
  induction k with
  | zero => norm_num
  | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring

/-- Exact E5 finite drift sum.  In particular, `poolDensity M G 0` is
`M / capacity n`; it is never identified with a density at a later time. -/
theorem predictablePartial_exact {n M : ℕ} (G : Graph n) (k : ℕ)
    (hk : k ≤ n) :
    predictablePartial M G k =
      (k : ℝ) * ((n : ℝ) * poolDensity M G 0 - 1) -
        poolDensity M G 0 * (k : ℝ) * ((k : ℝ) - 1) / 2 -
        poolDensity M G 0 *
          (∑ j ∈ Finset.range k, ((explore G j).queue.length : ℝ)) -
        poolDensity M G 0 *
          (∑ j ∈ Finset.range k, rootIndicator G j) +
        ∑ j ∈ Finset.range k,
          ((revealQuery (explore G j)).card : ℝ) *
            (poolDensity M G j - poolDensity M G 0) := by
  have hterm (j : ℕ) (hj : j < k) :
      queryMean M G j - 1 =
        ((n : ℝ) * poolDensity M G 0 - 1) -
          (j : ℝ) * poolDensity M G 0 -
          ((explore G j).queue.length : ℝ) * poolDensity M G 0 -
          rootIndicator G j * poolDensity M G 0 +
          ((revealQuery (explore G j)).card : ℝ) *
            (poolDensity M G j - poolDensity M G 0) := by
    have hbal := queryCard_balance G j (by omega)
    have hmul := congrArg (fun x : ℝ => x * poolDensity M G 0) hbal
    unfold queryMean
    nlinarith [hmul]
  change (∑ j ∈ Finset.range k, (queryMean M G j - 1)) = _
  calc
    (∑ j ∈ Finset.range k, (queryMean M G j - 1)) =
        ∑ j ∈ Finset.range k,
          (((n : ℝ) * poolDensity M G 0 - 1) -
            (j : ℝ) * poolDensity M G 0 -
            ((explore G j).queue.length : ℝ) * poolDensity M G 0 -
            rootIndicator G j * poolDensity M G 0 +
            ((revealQuery (explore G j)).card : ℝ) *
              (poolDensity M G j - poolDensity M G 0)) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact hterm j (Finset.mem_range.mp hj)
    _ = _ := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
        Finset.sum_const, Finset.card_range]
      simp only [← Finset.sum_mul]
      rw [sum_range_cast]
      ring

/-- The initial density carries the exact `n/(n-1)` correction. -/
theorem rawExploration_affine_decomposition {n : ℕ} (M : ℕ)
    (G : Graph n) (t : NNReal) :
    let x := (t : ℝ) * n23 n
    let j := ⌊x⌋₊
    let theta := x - (j : ℝ)
    rawExploration G t =
      ((1 - theta) *
          (martingalePartial G (fun i => queryMean M G i - 1) j +
            predictablePartial M G j) +
        theta *
          (martingalePartial G (fun i => queryMean M G i - 1) (j + 1) +
            predictablePartial M G (j + 1))) / n13 n := by
  dsimp [rawExploration]
  rw [walk_martingale_drift_decomposition G
    (fun i => queryMean M G i - 1) ⌊(t : ℝ) * n23 n⌋₊]
  rw [← explore_succ]
  rw [walk_martingale_drift_decomposition G
    (fun i => queryMean M G i - 1) (⌊(t : ℝ) * n23 n⌋₊ + 1)]
  rfl

/- A guarded endpoint version for a horizon `J`: the second affine
endpoint is within the `n` exploration steps whenever the cell index is
at most `J` and `J+1 ≤ n`. -/
end

end Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_DriftFinite


/-!
# Uniform drift of the concrete exploration

The bounds here are under the actual fixed-edge law.  The finite E5 identity
is imported from DriftFinite; the old DriftVariance file remains unverified.
-/

namespace Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_Drift

open Erdos745.WrapUp
open Erdos745.WrapUp.Proofs.Internal.W01_ENUM_Finite
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_Finite
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_Reveal
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_FiniteHorizon
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_Horizon
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_CriticalBudget
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_PoolConcentration
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_QueueControl
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_DriftFinite
open Filter
open scoped BigOperators Topology

noncomputable section
attribute [local instance] Classical.propDecidable
local instance : ContinuousInv₀ ℝ := IsTopologicalDivisionRing.toContinuousInv₀
set_option maxHeartbeats 1000000

def driftTarget (lam a : ℝ) (k : ℕ) : ℝ :=
  lam * ((k : ℝ) / a) - ((k : ℝ) / a) ^ 2 / 2

def gridDriftError {n : ℕ} (M : ℕ) (lam : ℝ) (G : Graph n)
    (k : ℕ) : ℝ :=
  |predictablePartial M G k / n13 n - driftTarget lam (n23 n) k|

def gridDriftErrorMax {n : ℕ} (M : ℕ) (lam : ℝ) (G : Graph n)
    (J : ℕ) : ℝ :=
  (Finset.range (J + 1)).sup' (by simp) (gridDriftError M lam G)

theorem gridDriftError_le_max {n M J : ℕ} (G : Graph n) (lam : ℝ)
    {k : ℕ} (hk : k ≤ J) :
    gridDriftError M lam G k ≤ gridDriftErrorMax M lam G J := by
  unfold gridDriftErrorMax
  exact Finset.le_sup' _ (Finset.mem_range.mpr (by omega))

theorem gridDriftErrorMax_le {n M J : ℕ} (G : Graph n) (lam c : ℝ)
    (h : ∀ k ≤ J, gridDriftError M lam G k ≤ c) :
    gridDriftErrorMax M lam G J ≤ c := by
  unfold gridDriftErrorMax
  apply Finset.sup'_le _ _
  intro k hk
  exact h k (Nat.le_of_lt_succ (Finset.mem_range.mp hk))

private theorem n_div_pred_tendsto_one :
    Tendsto (fun n : ℕ => (n : ℝ) / ((n : ℝ) - 1)) atTop (𝓝 1) := by
  have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun n : ℕ => ((n : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hnat
  have hden : Tendsto (fun n : ℕ => 1 - ((n : ℝ))⁻¹)
      atTop (𝓝 (1 : ℝ)) := by
    simpa using! tendsto_const_nhds.sub hinv
  have hrec := hden.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  have heq : (fun n : ℕ => (1 - ((n : ℝ))⁻¹)⁻¹) =ᶠ[atTop]
      (fun n : ℕ => (n : ℝ) / ((n : ℝ) - 1)) := by
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
    have hnr : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hpred : (0 : ℝ) < (n : ℝ) - 1 := by
      have hh : (2 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    field_simp
  simpa using! hrec.congr' heq

private theorem n23_tendsto_atTop : Tendsto n23 atTop atTop := by
  exact (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 3)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))

/-- The finite-size factor `n/(n-1)` is retained until after the limit. -/
theorem critical_initial_drift_tendsto (M : NatSeq) (lam : ℝ)
    (hcritical : criticalWindow M lam) :
    Tendsto (fun n => n13 n *
      ((n : ℝ) * ((M n : ℝ) / (capacity n : ℝ)) - 1))
      atTop (𝓝 lam) := by
  let r : ℕ → ℝ := fun n =>
    (2 * (M n : ℝ) - (n : ℝ)) / n23 n
  let c : ℕ → ℝ := fun n => (n : ℝ) / ((n : ℝ) - 1)
  have hr : Tendsto r atTop (𝓝 lam) := hcritical.2
  have hc : Tendsto c atTop (𝓝 1) := n_div_pred_tendsto_one
  have hinv : Tendsto (fun n => (n23 n)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp n23_tendsto_atTop
  have hsmall : Tendsto (fun n => (n23 n)⁻¹ * c n) atTop (𝓝 0) := by
    simpa only [zero_mul] using! hinv.mul hc
  have hmain : Tendsto (fun n => c n * r n + (n23 n)⁻¹ * c n)
      atTop (𝓝 lam) := by
    simpa only [one_mul, add_zero] using! (hc.mul hr).add hsmall
  have heq : (fun n => c n * r n + (n23 n)⁻¹ * c n) =ᶠ[atTop]
      (fun n => n13 n *
        ((n : ℝ) * ((M n : ℝ) / (capacity n : ℝ)) - 1)) := by
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
    have hn0 : 0 < n := by omega
    have hnr : (0 : ℝ) < n := by exact_mod_cast hn0
    have ha := n23_pos n hn0
    have hb : 0 < n13 n := by
      unfold n13
      exact Real.rpow_pos_of_pos hnr _
    have hprod := n23_mul_n13 n hn0
    have hpred : (0 : ℝ) < (n : ℝ) - 1 := by
      have hh : (2 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    have hcap : (capacity n : ℝ) =
        (n : ℝ) * ((n : ℝ) - 1) / 2 := by
      simpa only [capacity] using! (Nat.cast_choose_two (K := ℝ) n)
    have hcap0 : (0 : ℝ) < capacity n := by
      rw [hcap]
      positivity
    dsimp [c, r]
    rw [hcap]
    field_simp
    nlinarith [hprod]
  exact hmain.congr' heq

theorem critical_initial_density_tendsto_one (M : NatSeq) (lam : ℝ)
    (hcritical : criticalWindow M lam) :
    Tendsto (fun n : ℕ => (n : ℝ) * ((M n : ℝ) / (capacity n : ℝ)))
      atTop (𝓝 1) := by
  have hscaled := critical_initial_drift_tendsto M lam hcritical
  have hinv : Tendsto (fun n => (n13 n)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp n13_tendsto_atTop
  have hprod := hscaled.mul hinv
  have heq : (fun n => n13 n *
      ((n : ℝ) * ((M n : ℝ) / (capacity n : ℝ)) - 1) *
        (n13 n)⁻¹) =ᶠ[atTop]
      (fun n => (n : ℝ) * ((M n : ℝ) / (capacity n : ℝ)) - 1) := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hb : n13 n ≠ 0 := ne_of_gt (by
      unfold n13
      exact Real.rpow_pos_of_pos (by exact_mod_cast hn) _)
    field_simp
  have hdiff : Tendsto (fun n : ℕ => (n : ℝ) *
      ((M n : ℝ) / (capacity n : ℝ)) - 1) atTop (𝓝 0) := by
    simpa only [mul_zero] using! hprod.congr' heq
  have hsum := hdiff.const_add (1 : ℝ)
  simpa only [add_zero] using! hsum.congr' (Filter.Eventually.of_forall
    (fun n : ℕ => by ring))

theorem critical_initial_density_tendsto_zero (M : NatSeq) (lam : ℝ)
    (hcritical : criticalWindow M lam) :
    Tendsto (fun n : ℕ => (M n : ℝ) / (capacity n : ℝ)) atTop (𝓝 0) := by
  have hnp := critical_initial_density_tendsto_one M lam hcritical
  have hninv : Tendsto (fun n : ℕ => ((n : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hprod := hnp.mul hninv
  have heq : (fun n : ℕ => ((n : ℝ) * ((M n : ℝ) / (capacity n : ℝ))) *
      (n : ℝ)⁻¹) =ᶠ[atTop]
      (fun n : ℕ => (M n : ℝ) / (capacity n : ℝ)) := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hne : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    field_simp
  simpa only [one_mul] using! hprod.congr' heq

/-- The finite drift error is controlled by the initial correction, queue,
new-root, and pool terms separately. -/
theorem gridDriftError_finite_bound {n M J : ℕ} (G : Graph n)
    (lam delta q : ℝ) (k : ℕ) (hJ : J ≤ n) (hk : k ≤ J)
    (hn : 0 < n) (_hdelta : 0 ≤ delta) (_hq : 0 ≤ q)
    (hqueue : ∀ j < J, ((explore G j).queue.length : ℝ) ≤ q)
    (hpool : ∀ j < J,
      |poolDensity M G j - poolDensity M G 0| ≤ delta) :
    gridDriftError M lam G k ≤
      ((k : ℝ) / n23 n) *
        |n13 n * ((n : ℝ) * poolDensity M G 0 - 1) - lam| +
      (((k : ℝ) / n23 n) ^ 2 / 2) *
        |(n : ℝ) * poolDensity M G 0 - 1| +
      poolDensity M G 0 * (k : ℝ) / (2 * n13 n) +
      poolDensity M G 0 * (k : ℝ) * q / n13 n +
      poolDensity M G 0 * (k : ℝ) / n13 n +
      (k : ℝ) * (n : ℝ) * delta / n13 n := by
  let p0 := poolDensity M G 0
  let a := n23 n
  let b := n13 n
  have ha : 0 < a := n23_pos n hn
  have hb : 0 < b := by
    dsimp [b, n13]
    exact Real.rpow_pos_of_pos (by exact_mod_cast hn) _
  have hp0 : 0 ≤ p0 := by dsimp [p0, poolDensity]; positivity
  have hsq : a = b ^ 2 := n23_eq_n13_square n hn
  have hcub : b ^ 3 = (n : ℝ) := n13_cube n hn
  have htime : 0 ≤ (k : ℝ) / a := by positivity
  have hquad : 0 ≤ ((k : ℝ) / a) ^ 2 / 2 := by positivity
  have hqsum : (∑ j ∈ Finset.range k,
      ((explore G j).queue.length : ℝ)) ≤ (k : ℝ) * q := by
    calc
      (∑ j ∈ Finset.range k, ((explore G j).queue.length : ℝ)) ≤
          ∑ _j ∈ Finset.range k, q := by
            apply Finset.sum_le_sum
            intro j hj
            exact hqueue j (by have := Finset.mem_range.mp hj; omega)
      _ = (k : ℝ) * q := by simp
  have hqsum0 : 0 ≤ (∑ j ∈ Finset.range k,
      ((explore G j).queue.length : ℝ)) := by positivity
  have hrsum : (∑ j ∈ Finset.range k, rootIndicator G j) ≤ (k : ℝ) := by
    calc
      (∑ j ∈ Finset.range k, rootIndicator G j) ≤
          ∑ _j ∈ Finset.range k, (1 : ℝ) := by
            apply Finset.sum_le_sum
            intro j hj
            unfold rootIndicator
            split_ifs <;> norm_num
      _ = (k : ℝ) := by simp
  have hrsum0 : 0 ≤ (∑ j ∈ Finset.range k, rootIndicator G j) := by
    apply Finset.sum_nonneg
    intro j hj
    unfold rootIndicator
    split_ifs <;> norm_num
  let S : ℝ := ∑ j ∈ Finset.range k,
    ((revealQuery (explore G j)).card : ℝ) *
      (poolDensity M G j - p0)
  have hS : |S| ≤ (k : ℝ) * (n : ℝ) * delta := by
    calc
      |S| ≤ ∑ j ∈ Finset.range k,
          |((revealQuery (explore G j)).card : ℝ) *
            (poolDensity M G j - p0)| :=
              Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j ∈ Finset.range k, (n : ℝ) * delta := by
        apply Finset.sum_le_sum
        intro j hj
        have hd := queryCard_le_order G j (by
          have := Finset.mem_range.mp hj
          omega : j < n)
        have hdr : ((revealQuery (explore G j)).card : ℝ) ≤ n := by
          exact_mod_cast hd
        rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
        exact mul_le_mul hdr (hpool j (by
          have := Finset.mem_range.mp hj
          omega))
          (abs_nonneg _) (Nat.cast_nonneg _)
      _ = (k : ℝ) * (n : ℝ) * delta := by simp; ring
  have hE5 := predictablePartial_exact (M := M) G k (hk.trans hJ)
  have hidentity : predictablePartial M G k / b -
      driftTarget lam a k =
      ((k : ℝ) / a) *
        (b * ((n : ℝ) * p0 - 1) - lam) -
      (((k : ℝ) / a) ^ 2 / 2) * ((n : ℝ) * p0 - 1) +
      p0 * (k : ℝ) / (2 * b) -
      p0 * (∑ j ∈ Finset.range k,
        ((explore G j).queue.length : ℝ)) / b -
      p0 * (∑ j ∈ Finset.range k, rootIndicator G j) / b +
      S / b := by
    dsimp [p0, a, b, S, driftTarget]
    rw [hE5]
    rw [n23_eq_n13_square n hn, ← n13_cube n hn]
    field_simp
    ring
  have hfirst := abs_le.mp (le_refl
    (|b * ((n : ℝ) * p0 - 1) - lam|))
  have hsecond := abs_le.mp (le_refl (|(n : ℝ) * p0 - 1|))
  have hSbounds := abs_le.mp hS
  unfold gridDriftError
  change |predictablePartial M G k / b - driftTarget lam a k| ≤ _
  rw [hidentity]
  have hqpos : 0 ≤ p0 *
      (∑ j ∈ Finset.range k, ((explore G j).queue.length : ℝ)) / b := by
    positivity
  have hrpos : 0 ≤ p0 *
      (∑ j ∈ Finset.range k, rootIndicator G j) / b := by
    positivity
  have hfirstUpper := mul_le_mul_of_nonneg_left hfirst.2 htime
  have hfirstLower := mul_le_mul_of_nonneg_left hfirst.1 htime
  have hsecondUpper := mul_le_mul_of_nonneg_left hsecond.2 hquad
  have hsecondLower := mul_le_mul_of_nonneg_left hsecond.1 hquad
  have hqueueScaled : p0 *
      (∑ j ∈ Finset.range k, ((explore G j).queue.length : ℝ)) / b ≤
      p0 * (k : ℝ) * q / b := by
    convert div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hqsum hp0) hb.le using 1
    ring
  have hrootScaled : p0 *
      (∑ j ∈ Finset.range k, rootIndicator G j) / b ≤
      p0 * (k : ℝ) / b := by
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hrsum hp0) hb.le
  have hSupper : S / b ≤ (k : ℝ) * (n : ℝ) * delta / b :=
    div_le_div_of_nonneg_right hSbounds.2 hb.le
  have hSlower : -((k : ℝ) * (n : ℝ) * delta / b) ≤ S / b := by
    have hh := div_le_div_of_nonneg_right hSbounds.1 hb.le
    simpa only [neg_div] using! hh
  have hmidpos : 0 ≤ p0 * (k : ℝ) / (2 * b) := by positivity
  apply abs_le.mpr
  constructor <;> dsimp [p0, a, b] at * <;>
    nlinarith [hfirstUpper, hfirstLower, hsecondUpper, hsecondLower,
      hqueueScaled, hrootScaled, hSupper, hSlower, hqpos, hrpos, hmidpos]


private theorem probM_mono {n M : ℕ} (P Q : Graph n → Prop)
    (h : ∀ G, P G → Q G) : probM n M P ≤ probM n M Q := by
  unfold probM
  have hs : (fixedGraphs n M).filter P ⊆
      (fixedGraphs n M).filter Q := by
    intro G hG
    exact Finset.mem_filter.mpr
      ⟨(Finset.mem_filter.mp hG).1, h G (Finset.mem_filter.mp hG).2⟩
  have hc : (((fixedGraphs n M).filter P).card : ℝ) ≤
      (((fixedGraphs n M).filter Q).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hs
  exact div_le_div_of_nonneg_right hc (Nat.cast_nonneg _)

private theorem probM_or_le {n M : ℕ} (P Q : Graph n → Prop)
    (hM : M ≤ capacity n) :
    probM n M (fun G => P G ∨ Q G) ≤ probM n M P + probM n M Q := by
  have hF : (0 : ℝ) < ((fixedGraphs n M).card : ℝ) := by
    exact_mod_cast (Finset.card_pos.mpr (fixedGraphs_nonempty hM))
  have hfilter : (fixedGraphs n M).filter (fun G => P G ∨ Q G) =
      (fixedGraphs n M).filter P ∪ (fixedGraphs n M).filter Q := by
    ext G
    simp [and_or_left]
  have hc := Finset.card_union_le
    ((fixedGraphs n M).filter P) ((fixedGraphs n M).filter Q)
  have hcr : (((fixedGraphs n M).filter P ∪
      (fixedGraphs n M).filter Q).card : ℝ) ≤
      ((fixedGraphs n M).filter P).card +
        ((fixedGraphs n M).filter Q).card := by exact_mod_cast hc
  unfold probM
  rw [← add_div]
  have hbound := div_le_div_of_nonneg_right hcr hF.le
  convert hbound using 1
  congr 1
  congr 1
  congr 1
  ext G
  simp [and_or_left]

private theorem probM_nonneg {n M : ℕ} (P : Graph n → Prop) :
    0 ≤ probM n M P := by
  unfold probM
  positivity

/-- The normalization of every term of E5, before any limit is taken. -/
def driftEnvelopeAt (n M J : ℕ) (lam K δ : ℝ) : ℝ :=
  let b := n13 n
  let a := n23 n
  let p := (M : ℝ) / (capacity n : ℝ)
  let u := (J : ℝ) / a
  u * |b * ((n : ℝ) * p - 1) - lam| +
    u ^ 2 / 2 * |(n : ℝ) * p - 1| +
    u * (p * b) / 2 + u * K * (p * b ^ 2) +
    u * (p * b) + u * δ

/-- On a realized finite horizon, queue and pool envelopes control every
+grid point of the predictable drift. -/
theorem gridDriftErrorMax_of_controls {n M J : ℕ} (G : Graph n)
    (lam K δ : ℝ) (hn : 0 < n) (hJ : J ≤ n)
    (hK : 0 ≤ K) (hδ : 0 ≤ δ)
    (hqueue : ∀ j < J,
      ((explore G j).queue.length : ℝ) ≤ K * n13 n)
    (hpool : ∀ j < J,
      |poolDensity M G j - poolDensity M G 0| ≤ δ / (n13 n) ^ 4) :
    gridDriftErrorMax M lam G J ≤ driftEnvelopeAt n M J lam K δ := by
  let b := n13 n
  let a := n23 n
  let p := (M : ℝ) / (capacity n : ℝ)
  let u := (J : ℝ) / a
  have hb : 0 < b := by
    dsimp [b, n13]
    exact Real.rpow_pos_of_pos (by exact_mod_cast hn) _
  have ha : 0 < a := n23_pos n hn
  have hp : 0 ≤ p := by dsimp [p]; positivity
  have hsq : a = b ^ 2 := n23_eq_n13_square n hn
  have hcub : b ^ 3 = (n : ℝ) := n13_cube n hn
  have hu : 0 ≤ u := by dsimp [u]; positivity
  apply gridDriftErrorMax_le
  intro k hk
  have hkreal : (k : ℝ) ≤ J := by exact_mod_cast hk
  have hx : (k : ℝ) / a ≤ u :=
    div_le_div_of_nonneg_right hkreal ha.le
  have hx0 : 0 ≤ (k : ℝ) / a := by positivity
  have hα : 0 ≤ |b * ((n : ℝ) * p - 1) - lam| := abs_nonneg _
  have hβ : 0 ≤ |(n : ℝ) * p - 1| := abs_nonneg _
  have hfinite := gridDriftError_finite_bound G lam
    (δ / b ^ 4) (K * b) k hJ hk hn
    (by positivity) (mul_nonneg hK hb.le) hqueue hpool
  have hform :
      ((k : ℝ) / a) * |b * ((n : ℝ) * p - 1) - lam| +
        (((k : ℝ) / a) ^ 2 / 2) * |(n : ℝ) * p - 1| +
        p * (k : ℝ) / (2 * b) +
        p * (k : ℝ) * (K * b) / b +
        p * (k : ℝ) / b +
        (k : ℝ) * (n : ℝ) * (δ / b ^ 4) / b =
      ((k : ℝ) / a) * |b * ((n : ℝ) * p - 1) - lam| +
        ((k : ℝ) / a) ^ 2 / 2 * |(n : ℝ) * p - 1| +
        ((k : ℝ) / a) * (p * b) / 2 +
        ((k : ℝ) / a) * K * (p * b ^ 2) +
        ((k : ℝ) / a) * (p * b) +
        ((k : ℝ) / a) * δ := by
    rw [hsq, ← hcub]
    field_simp
  have hlocal : gridDriftError M lam G k ≤
      ((k : ℝ) / a) * |b * ((n : ℝ) * p - 1) - lam| +
        ((k : ℝ) / a) ^ 2 / 2 * |(n : ℝ) * p - 1| +
        ((k : ℝ) / a) * (p * b) / 2 +
        ((k : ℝ) / a) * K * (p * b ^ 2) +
        ((k : ℝ) / a) * (p * b) +
        ((k : ℝ) / a) * δ := by
    simpa only [b, a, p] using! hfinite.trans_eq hform
  have hxsq : ((k : ℝ) / a) ^ 2 ≤ u ^ 2 := by gcongr
  have h₁ := mul_le_mul_of_nonneg_right hx hα
  have h₂ := mul_le_mul_of_nonneg_right hxsq hβ
  have h₃ := mul_le_mul_of_nonneg_right hx (mul_nonneg hp hb.le)
  have h₄ := mul_le_mul_of_nonneg_right hx
    (mul_nonneg hK (mul_nonneg hp (sq_nonneg b)))
  have h₅ := mul_le_mul_of_nonneg_right hx hδ
  dsimp [driftEnvelopeAt, b, a, p, u]
  nlinarith [hlocal, h₁, h₂, h₃, h₄, h₅]

private theorem horizonRatio_tendsto (T : ℝ) (hT : 0 ≤ T) :
    Tendsto (fun n : ℕ =>
      (⌊T * n23 n⌋₊ : ℝ) / n23 n) atTop (𝓝 T) := by
  have ha : Tendsto n23 atTop atTop := n23_tendsto_atTop
  have hinv : Tendsto (fun n => (n23 n)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp ha
  have hlow : Tendsto (fun n => T - (n23 n)⁻¹)
      atTop (𝓝 T) := by simpa using! tendsto_const_nhds.sub hinv
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow
    tendsto_const_nhds
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hapos := n23_pos n hn
    have hfloor := Nat.lt_floor_add_one (T * n23 n)
    have hmul : (T - (n23 n)⁻¹) * n23 n ≤
        (⌊T * n23 n⌋₊ : ℝ) := by
      field_simp
      linarith
    exact (le_div_iff₀ hapos).mpr hmul
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hapos := n23_pos n hn
    have hfloor : (⌊T * n23 n⌋₊ : ℝ) ≤ T * n23 n :=
      Nat.floor_le (mul_nonneg hT hapos.le)
    exact (div_le_iff₀ hapos).mpr hfloor

private theorem scaled_initial_density_square_tendsto_zero
    (M : NatSeq) (lam : ℝ) (hcritical : criticalWindow M lam) :
    Tendsto (fun n => ((M n : ℝ) / (capacity n : ℝ)) * n13 n ^ 2)
      atTop (𝓝 0) := by
  have hnp := critical_initial_density_tendsto_one M lam hcritical
  have hinv : Tendsto (fun n => (n13 n)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp n13_tendsto_atTop
  have hprod := hnp.mul hinv
  have heq : (fun n : ℕ => ((n : ℝ) *
      ((M n : ℝ) / (capacity n : ℝ))) * (n13 n)⁻¹) =ᶠ[atTop]
      (fun n : ℕ => ((M n : ℝ) / (capacity n : ℝ)) * n13 n ^ 2) := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hb : 0 < n13 n := by
      unfold n13
      exact Real.rpow_pos_of_pos (by exact_mod_cast hn) _
    have hcub := n13_cube n hn
    rw [← hcub]
    field_simp
  simpa only [one_mul] using! hprod.congr' heq

private theorem scaled_initial_density_tendsto_zero
    (M : NatSeq) (lam : ℝ) (hcritical : criticalWindow M lam) :
    Tendsto (fun n => ((M n : ℝ) / (capacity n : ℝ)) * n13 n)
      atTop (𝓝 0) := by
  have hsq := scaled_initial_density_square_tendsto_zero M lam hcritical
  have hinv : Tendsto (fun n => (n13 n)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp n13_tendsto_atTop
  have hprod := hsq.mul hinv
  have heq : (fun n =>
      (((M n : ℝ) / (capacity n : ℝ)) * n13 n ^ 2) *
        (n13 n)⁻¹) =ᶠ[atTop]
      (fun n => ((M n : ℝ) / (capacity n : ℝ)) * n13 n) := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hb : n13 n ≠ 0 := ne_of_gt (by
      unfold n13
      exact Real.rpow_pos_of_pos (by exact_mod_cast hn) _)
    field_simp
  simpa only [zero_mul] using! hprod.congr' heq

private theorem driftEnvelopeAt_tendsto (M : NatSeq) (lam T K δ : ℝ)
    (hcritical : criticalWindow M lam) (hT : 0 ≤ T) :
    Tendsto (fun n => driftEnvelopeAt n (M n) ⌊T * n23 n⌋₊ lam K δ)
      atTop (𝓝 (T * δ)) := by
  let u : ℕ → ℝ := fun n => (⌊T * n23 n⌋₊ : ℝ) / n23 n
  let p : ℕ → ℝ := fun n => (M n : ℝ) / (capacity n : ℝ)
  let b : ℕ → ℝ := n13
  have hu : Tendsto u atTop (𝓝 T) := horizonRatio_tendsto T hT
  have hs : Tendsto (fun n => b n * ((n : ℝ) * p n - 1))
      atTop (𝓝 lam) := critical_initial_drift_tendsto M lam hcritical
  have hs0 : Tendsto (fun n : ℕ =>
      |b n * ((n : ℝ) * p n - 1) - lam|) atTop (𝓝 0) := by
    simpa using! (hs.sub (tendsto_const_nhds (x := lam))).abs
  have hnp : Tendsto (fun n : ℕ => (n : ℝ) * p n) atTop (𝓝 1) :=
    critical_initial_density_tendsto_one M lam hcritical
  have hnp0 : Tendsto (fun n : ℕ => |(n : ℝ) * p n - 1|)
      atTop (𝓝 0) := by
    simpa using! (hnp.sub (tendsto_const_nhds (x := (1 : ℝ)))).abs
  have hp2 : Tendsto (fun n => p n * b n ^ 2) atTop (𝓝 0) :=
    scaled_initial_density_square_tendsto_zero M lam hcritical
  have hp1 : Tendsto (fun n => p n * b n) atTop (𝓝 0) :=
    scaled_initial_density_tendsto_zero M lam hcritical
  have hlim : Tendsto (fun n =>
      u n * |b n * ((n : ℝ) * p n - 1) - lam| +
        u n ^ 2 / 2 * |(n : ℝ) * p n - 1| +
        u n * (p n * b n) / 2 +
        u n * K * (p n * b n ^ 2) +
        u n * (p n * b n) + u n * δ)
      atTop (𝓝 (T * δ)) := by
    convert (((((hu.mul hs0).add
      (((hu.pow 2).div_const 2).mul hnp0)).add
      (((hu.mul hp1).div_const 2))).add
      (((hu.mul_const K).mul hp2))).add
      (hu.mul hp1)).add (hu.mul_const δ) using 1
    norm_num
  convert! hlim using 1

/-- Uniform grid drift convergence under the actual fixed-edge law. -/
theorem critical_grid_drift_concentration
    (hfinite : FiniteEnumerationStatement) (M : NatSeq) (lam T ε : ℝ)
    (hcritical : criticalWindow M lam) (hT : 0 ≤ T) (hε : 0 < ε) :
    Tendsto (fun n => probM n (M n) (fun G =>
      ε ≤ gridDriftErrorMax (M n) lam G ⌊T * n23 n⌋₊))
      atTop (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro c hc
    exact Filter.Eventually.of_forall (fun n =>
      lt_of_lt_of_le hc (probM_nonneg _))
  · intro d hd
    have hd4 : 0 < d / 4 := by linarith
    let δ : ℝ := ε / (4 * (T + 1))
    have hT1 : 0 < T + 1 := by linarith
    have hδ : 0 < δ := by dsimp [δ]; positivity
    have hδT : T * δ < ε := by
      dsimp [δ]
      have hden : 0 < 4 * (T + 1) := by positivity
      rw [← mul_div_assoc]
      apply (div_lt_iff₀ hden).mpr
      nlinarith [mul_pos hε hT1]
    obtain ⟨K, hK, hqueue⟩ :=
      critical_queue_tight hfinite M lam T (d / 4) hcritical hT hd4
    have hpool := (critical_poolDensity_concentration hfinite M lam T δ
      hcritical hT hδ).eventually_lt_const hd4
    have henv := (driftEnvelopeAt_tendsto M lam T K δ hcritical hT).eventually_lt_const hδT
    filter_upwards [hcritical.1,
      eventually_horizonBudget M lam T hcritical hT,
      eventually_ge_atTop (1 : ℕ), hqueue, hpool, henv]
      with n hM hbudget hn hqb hpb heb
    let J : ℕ := ⌊T * n23 n⌋₊
    let b : ℝ := n13 n
    let Q : Graph n → Prop := fun G =>
      ∃ j ≤ J, K * b < ((explore G j).queue.length : ℝ)
    let P : Graph n → Prop := fun G =>
      ∃ j ≤ J, δ / b ^ 4 ≤
        |poolDensity (M n) G j - poolDensity (M n) G 0|
    let A : Graph n → Prop := fun G =>
      ε ≤ gridDriftErrorMax (M n) lam G J
    have hcontain : ∀ G : Graph n, A G → Q G ∨ P G := by
      intro G hA
      by_cases hQ : Q G
      · exact Or.inl hQ
      by_cases hP : P G
      · exact Or.inr hP
      exfalso
      have hqn : ∀ j < J,
          ((explore G j).queue.length : ℝ) ≤ K * b := by
        intro j hj
        exact le_of_not_gt (fun hh => hQ ⟨j, hj.le, hh⟩)
      have hpn : ∀ j < J,
          |poolDensity (M n) G j - poolDensity (M n) G 0| ≤
            δ / b ^ 4 := by
        intro j hj
        exact le_of_not_gt (fun hh => hP ⟨j, hj.le, hh.le⟩)
      have hbound := gridDriftErrorMax_of_controls G lam K δ hn
        hbudget.1 hK.le hδ.le hqn hpn
      have henv' : driftEnvelopeAt n (M n) J lam K δ < ε := by
        simpa only [J] using! heb
      exact (not_lt_of_ge hA) (lt_of_le_of_lt hbound henv')
    have hmono := probM_mono (n := n) (M := M n) A
      (fun G => Q G ∨ P G) hcontain
    have hor := probM_or_le Q P hM
    have hq : probM n (M n) Q ≤ d / 4 := by
      simpa only [Q, J, b] using! hqb
    have hp : probM n (M n) P < d / 4 := by
      simpa only [P, J, b] using! hpb
    have hfinal : probM n (M n) A < d := by linarith
    simpa only [A, J] using! hfinal

/-- The affine interpolation of the predictable partial sums on the same
mesh and at the same scale as `rawExploration`. -/
def polygonalDrift {n : ℕ} (M : ℕ) (G : Graph n) (t : NNReal) : ℝ :=
  let x := (t : ℝ) * n23 n
  let j := ⌊x⌋₊
  let theta := x - (j : ℝ)
  ((1 - theta) * predictablePartial M G j +
    theta * predictablePartial M G (j + 1)) / n13 n

def driftCurve (lam : ℝ) (t : NNReal) : ℝ :=
  lam * (t : ℝ) - (t : ℝ) ^ 2 / 2

/-- The endpoint cell lies on the enlarged `T+1` horizon. -/
theorem horizon_endpoint_guard (n : ℕ) (T : ℝ) (t : NNReal)
    (_hT : 0 ≤ T) (ht : (t : ℝ) ≤ T) (ha : 1 ≤ n23 n) :
    ⌊(t : ℝ) * n23 n⌋₊ ≤ ⌊T * n23 n⌋₊ ∧
      ⌊(t : ℝ) * n23 n⌋₊ + 1 ≤ ⌊(T + 1) * n23 n⌋₊ := by
  have hapos : 0 < n23 n := by linarith
  have hx : 0 ≤ (t : ℝ) * n23 n := by positivity
  have hfloor : (⌊(t : ℝ) * n23 n⌋₊ : ℝ) ≤
      (t : ℝ) * n23 n := Nat.floor_le hx
  have hle : (t : ℝ) * n23 n ≤ T * n23 n :=
    mul_le_mul_of_nonneg_right ht hapos.le
  have hfirst : ⌊(t : ℝ) * n23 n⌋₊ ≤ ⌊T * n23 n⌋₊ := by
    apply Nat.le_floor
    linarith
  have hnext : ((⌊(t : ℝ) * n23 n⌋₊ + 1 : ℕ) : ℝ) ≤
      (T + 1) * n23 n := by
    push_cast
    nlinarith
  exact ⟨hfirst, Nat.le_floor hnext⟩

/-- Between two mesh points, only the curvature of the deterministic
quadratic remains after affine interpolation. -/
theorem polygonalDrift_error_le_grid {n M J : ℕ} (G : Graph n)
    (lam : ℝ) (t : NNReal) (hn : 0 < n)
    (hcell : ⌊(t : ℝ) * n23 n⌋₊ + 1 ≤ J) :
    |polygonalDrift M G t - driftCurve lam t| ≤
      gridDriftErrorMax M lam G J + 1 / (2 * n23 n ^ 2) := by
  let a := n23 n
  let b := n13 n
  let x := (t : ℝ) * a
  let j := ⌊x⌋₊
  let theta := x - (j : ℝ)
  let B : ℕ → ℝ := fun k => predictablePartial M G k / b
  let F : ℕ → ℝ := fun k => driftTarget lam a k
  have ha : 0 < a := n23_pos n hn
  have hb : 0 < b := by
    dsimp [b, n13]
    exact Real.rpow_pos_of_pos (by exact_mod_cast hn) _
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hfloor : (j : ℝ) ≤ x := Nat.floor_le hx
  have hfloor' : x < (j : ℝ) + 1 := Nat.lt_floor_add_one x
  have htheta0 : 0 ≤ theta := by dsimp [theta]; linarith
  have htheta1 : theta ≤ 1 := by dsimp [theta]; linarith
  have hj : j ≤ J := by
    change j + 1 ≤ J at hcell
    omega
  have hBj : |B j - F j| ≤ gridDriftErrorMax M lam G J := by
    simpa only [B, F, gridDriftError, a, b] using!
      gridDriftError_le_max G lam hj
  have hBj1 : |B (j + 1) - F (j + 1)| ≤
      gridDriftErrorMax M lam G J := by
    simpa only [B, F, gridDriftError, a, b] using!
      gridDriftError_le_max G lam hcell
  have htime : (t : ℝ) = x / a := by
    dsimp [x]
    field_simp
  have hcurve :
      (1 - theta) * F j + theta * F (j + 1) -
        driftCurve lam t = theta * (theta - 1) / (2 * a ^ 2) := by
    dsimp [driftCurve]
    rw [htime]
    dsimp [F, driftTarget, theta, x]
    push_cast
    field_simp
    ring
  have hpoly : polygonalDrift M G t =
      (1 - theta) * B j + theta * B (j + 1) := by
    dsimp [polygonalDrift, B, x, j, theta, a, b]
    ring
  have hidentity : polygonalDrift M G t - driftCurve lam t =
      (1 - theta) * (B j - F j) +
        theta * (B (j + 1) - F (j + 1)) +
        theta * (theta - 1) / (2 * a ^ 2) := by
    rw [hpoly]
    linarith [hcurve]
  have hcurv : |theta * (theta - 1) / (2 * a ^ 2)| ≤
      1 / (2 * a ^ 2) := by
    have hprod : |theta * (theta - 1)| ≤ 1 := by
      apply abs_le.mpr
      constructor <;> nlinarith [sq_nonneg (theta - 1 / 2)]
    rw [abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * a ^ 2)]
    exact div_le_div_of_nonneg_right hprod (by positivity)
  rw [hidentity]
  calc
    |(1 - theta) * (B j - F j) +
        theta * (B (j + 1) - F (j + 1)) +
        theta * (theta - 1) / (2 * a ^ 2)| ≤
        (1 - theta) * |B j - F j| +
          theta * |B (j + 1) - F (j + 1)| +
          |theta * (theta - 1) / (2 * a ^ 2)| := by
            calc
              _ ≤ |(1 - theta) * (B j - F j)| +
                  |theta * (B (j + 1) - F (j + 1))| +
                  |theta * (theta - 1) / (2 * a ^ 2)| := by
                    nlinarith [abs_add_le
                      ((1 - theta) * (B j - F j) +
                        theta * (B (j + 1) - F (j + 1)))
                      (theta * (theta - 1) / (2 * a ^ 2)),
                      abs_add_le ((1 - theta) * (B j - F j))
                        (theta * (B (j + 1) - F (j + 1)))]
              _ = _ := by
                rw [abs_mul, abs_mul, abs_of_nonneg (by linarith : 0 ≤ 1 - theta),
                  abs_of_nonneg htheta0]
    _ ≤ gridDriftErrorMax M lam G J + 1 / (2 * a ^ 2) := by
      have h₁ := mul_le_mul_of_nonneg_left hBj
        (by linarith : 0 ≤ 1 - theta)
      have h₂ := mul_le_mul_of_nonneg_left hBj1 htheta0
      nlinarith [h₁, h₂, hcurv]

/-- Actual supremum of the polygonal predictable drift error on `[0,T]`.
For the eventual critical horizon the error set is bounded by the finite
grid maximum and the quadratic cell error. -/
def polygonalDriftErrorSup {n : ℕ} (M : ℕ) (lam T : ℝ)
    (G : Graph n) : ℝ :=
  sSup {z : ℝ | ∃ t : NNReal, (t : ℝ) ≤ T ∧
    z = |polygonalDrift M G t - driftCurve lam t|}

/-- Uniform polygonal drift convergence under the same fixed-edge law.
The `T+1` grid supplies the `J+1` interpolation endpoint. -/
theorem critical_polygonal_drift_concentration
    (hfinite : FiniteEnumerationStatement) (M : NatSeq) (lam T ε : ℝ)
    (hcritical : criticalWindow M lam) (hT : 0 ≤ T) (hε : 0 < ε) :
    Tendsto (fun n => probM n (M n) (fun G =>
      ε ≤ polygonalDriftErrorSup (M n) lam T G))
      atTop (𝓝 0) := by
  let H : ℝ := T + 1
  have hH : 0 ≤ H := by dsimp [H]; linarith
  have hε2 : 0 < ε / 2 := by linarith
  have hgrid := critical_grid_drift_concentration hfinite M lam H
    (ε / 2) hcritical hH hε2
  have hinv : Tendsto (fun n => (n23 n)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp n23_tendsto_atTop
  have hcurve0 : Tendsto (fun n => 1 / (2 * n23 n ^ 2))
      atTop (𝓝 0) := by
    have hpow := hinv.pow 2
    have heq : (fun n => 1 / (2 * n23 n ^ 2)) =ᶠ[atTop]
        (fun n => ((n23 n)⁻¹) ^ 2 / 2) := by
      filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
      have ha := n23_pos n hn
      field_simp
    have hh : Tendsto (fun n => ((n23 n)⁻¹) ^ 2 / 2)
        atTop (𝓝 0) := by simpa using! hpow.div_const 2
    exact hh.congr' heq.symm
  have hsmall := hcurve0.eventually_lt_const hε2
  have ha1 := n23_tendsto_atTop.eventually_ge_atTop (1 : ℝ)
  have hguard := eventually_eighth_horizon H hH
  have hbound : ∀ᶠ n : ℕ in atTop,
      probM n (M n) (fun G =>
        ε ≤ polygonalDriftErrorSup (M n) lam T G) ≤
      probM n (M n) (fun G =>
        ε / 2 ≤ gridDriftErrorMax (M n) lam G ⌊H * n23 n⌋₊) := by
    filter_upwards [eventually_ge_atTop (8 : ℕ), ha1, hsmall, hguard]
      with n hn ha hsmall hguard
    let J : ℕ := ⌊H * n23 n⌋₊
    have hJ : J + 1 ≤ n := by
      have h8 : 8 * J ≤ n := hguard
      omega
    apply probM_mono
    intro G hbad
    have hsup : polygonalDriftErrorSup (M n) lam T G ≤
        gridDriftErrorMax (M n) lam G J +
          1 / (2 * n23 n ^ 2) := by
      unfold polygonalDriftErrorSup
      apply csSup_le
      · refine ⟨|polygonalDrift (M n) G 0 - driftCurve lam 0|, ?_⟩
        exact ⟨0, by simpa using! hT, rfl⟩
      · intro z hz
        obtain ⟨t, ht, rfl⟩ := hz
        have hcell := (horizon_endpoint_guard n T t hT ht ha).2
        have hcell' : ⌊(t : ℝ) * n23 n⌋₊ + 1 ≤ J := by
          simpa only [H, J] using! hcell
        exact polygonalDrift_error_le_grid G lam t (by omega) hcell'
    have hgridbad : ε / 2 ≤ gridDriftErrorMax (M n) lam G J := by
      linarith
    simpa only [J] using! hgridbad
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hgrid
  · exact Filter.Eventually.of_forall (fun n => probM_nonneg _)
  · exact hbound

end

end Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_Drift


/-!
# Predictable query variance on the critical exploration horizon

All statements concern positive realized history atoms under the actual
fixed-edge law.  The finite-population correction is retained exactly.
-/

namespace Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_Variance

open Erdos745.WrapUp
open Erdos745.WrapUp.Proofs.Internal.W01_ENUM_Finite
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_Finite
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_Reveal
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_FiniteHorizon
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_FiniteAtoms
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_Asymptotics
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_MomentBounds
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_PoolUniform
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_Horizon
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_CriticalBudget
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_PoolConcentration
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_QueueControl
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_DriftFinite
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_Drift
open Filter
open scoped BigOperators Topology

noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1000000

def varianceAt {n : ℕ} (M : ℕ) (G : Graph n) (j : ℕ) : ℝ :=
  conditionalQueryRawMoment M G j 2 -
    (conditionalQueryRawMoment M G j 1) ^ 2

def varianceErrorMax {n : ℕ} (M : ℕ) (G : Graph n) (J : ℕ) : ℝ :=
  (Finset.range (J + 1)).sup' (by simp)
    (fun j => if j < J then |varianceAt M G j - 1| else 0)

theorem varianceError_le_max {n M J : ℕ} (G : Graph n)
    {j : ℕ} (hj : j < J) :
    |varianceAt M G j - 1| ≤ varianceErrorMax M G J := by
  unfold varianceErrorMax
  have hm := Finset.le_sup'
    (s := Finset.range (J + 1))
    (f := fun i => if i < J then |varianceAt M G i - 1| else 0)
    (Finset.mem_range.mpr (by omega : j < J + 1))
  simpa [hj] using! hm

theorem varianceErrorMax_le {n M J : ℕ} (G : Graph n) (c : ℝ)
    (hc : 0 ≤ c) (h : ∀ j < J, |varianceAt M G j - 1| ≤ c) :
    varianceErrorMax M G J ≤ c := by
  unfold varianceErrorMax
  apply Finset.sup'_le _ _
  intro j hj
  by_cases hlt : j < J
  · simpa [hlt] using! h j hlt
  · simp [hlt, hc]

/-- The formula is applied only after the realized atom supplies positivity,
`R ≤ E`, `d ≤ E`, and the horizon supplies `E ≥ 2`. -/
theorem varianceAt_exact {n M J : ℕ}
    (hfinite : FiniteEnumerationStatement) (hM : M ≤ capacity n)
    (G : Graph n) (j : ℕ) (hG : G.card = M)
    (hbudget : HorizonBudget n M J 8) (hj : j < J) :
    let E := capacity n - (revealTrace G j).yes.card -
      (revealTrace G j).no.card
    let R := M - (revealTrace G j).yes.card
    let d := (revealQuery (explore G j)).card
    varianceAt M G j =
      (d : ℝ) * ((R : ℝ) / E) * (1 - (R : ℝ) / E) *
        ((E - d : ℕ) : ℝ) / ((E : ℝ) - 1) := by
  have hEeq : capacity n - (revealTrace G j).yes.card -
      (revealTrace G j).no.card = poolEdgeCount G j := by
    unfold poolEdgeCount answeredCount
    rw [Finset.card_union_of_disjoint (revealTrace_yes_no_disjoint G j)]
    omega
  have hR : M - (revealTrace G j).yes.card ≤
      capacity n - (revealTrace G j).yes.card -
        (revealTrace G j).no.card := by
    rw [hEeq]
    exact poolSuccessCount_le_poolEdgeCount G j hG
  have hd : (revealQuery (explore G j)).card ≤
      capacity n - (revealTrace G j).yes.card -
        (revealTrace G j).no.card := by
    rw [hEeq]
    exact queryCard_le_poolEdgeCount G j
  have hE : 2 ≤ capacity n - (revealTrace G j).yes.card -
      (revealTrace G j).no.card := by
    rw [hEeq]
    have h8 := poolEdgeCount_ge_eight G j hbudget hj.le
    omega
  have hpos := historyAtom_probability_pos G j hG
  simpa only [varianceAt] using!
    (conditionalQueryVariance_eq hfinite hM G j hpos hR hd hE)

theorem varianceAt_between {n M J : ℕ}
    (hfinite : FiniteEnumerationStatement) (hM : M ≤ capacity n)
    (G : Graph n) (j : ℕ) (hG : G.card = M)
    (hbudget : HorizonBudget n M J 8) (hj : j < J) :
    0 ≤ varianceAt M G j ∧ varianceAt M G j ≤ 4 := by
  simpa only [varianceAt, show (8 : ℝ) / 2 = 4 by norm_num] using!
    (horizon_conditional_variance_le hfinite hM G j hG hbudget hj
      (historyAtom_probability_pos G j hG))

private theorem variance_factor_error (m p q A P R : ℝ)
    (hm0 : 0 ≤ m) (hm4 : m ≤ 4) (hp0 : 0 ≤ p)
    (hpP : p ≤ P) (hq0 : 0 ≤ q) (hq2 : q ≤ 2)
    (hm : |m - 1| ≤ A) (hq : |q - 1| ≤ R) :
    |m * (1 - p) * q - 1| ≤ A + 4 * (R + 2 * P) := by
  have hpq : p * q ≤ 2 * P := by
    have h₁ := mul_le_mul_of_nonneg_left hq2 hp0
    have h₂ := mul_le_mul_of_nonneg_left hpP (by norm_num : (0 : ℝ) ≤ 2)
    nlinarith
  have hδ : |(1 - p) * q - 1| ≤ R + 2 * P := by
    apply abs_le.mpr
    have hq' := abs_le.mp hq
    constructor <;> nlinarith [hpq, mul_nonneg hp0 hq0]
  have hδ0 : 0 ≤ R + 2 * P := le_trans (abs_nonneg _) hδ
  have hmul : |m * ((1 - p) * q - 1)| ≤ 4 * (R + 2 * P) := by
    rw [abs_mul, abs_of_nonneg hm0]
    exact (mul_le_mul_of_nonneg_left hδ hm0).trans
      (mul_le_mul_of_nonneg_right hm4 hδ0)
  have hdecomp : m * (1 - p) * q - 1 =
      (m - 1) + m * ((1 - p) * q - 1) := by ring
  rw [hdecomp]
  exact (abs_add_le _ _).trans (add_le_add hm hmul)

private theorem pool_factor_bounds {n M J : ℕ} (G : Graph n)
    (j : ℕ) (hn : 32 ≤ n) (hJ : 8 * J ≤ n)
    (hbudget : HorizonBudget n M J 8) (hj : j < J) :
    let E := poolEdgeCount G j
    let d := (revealQuery (explore G j)).card
    let q := ((E - d : ℕ) : ℝ) / ((E : ℝ) - 1)
    0 ≤ q ∧ q ≤ 2 ∧ |q - 1| ≤ 8 / (n : ℝ) := by
  dsimp
  let E := poolEdgeCount G j
  let d := (revealQuery (explore G j)).card
  let q := ((E - d : ℕ) : ℝ) / ((E : ℝ) - 1)
  have hd : d ≤ E := queryCard_le_poolEdgeCount G j
  have hdn : d ≤ n := queryCard_le_order G j (by
    have h := hbudget.1
    omega)
  have hE8 : 8 ≤ E := poolEdgeCount_ge_eight G j hbudget hj.le
  have hElo : (n : ℝ) ^ 2 / 4 ≤ E := by
    have hh := horizon_pool_lower hn hJ hbudget
    have hh' := poolEdgeCount_ge_horizon G j hbudget hj.le
    exact hh.trans (by exact_mod_cast hh')
  have hnr : (32 : ℝ) ≤ n := by exact_mod_cast hn
  have hdr : (d : ℝ) ≤ n := by exact_mod_cast hdn
  have hEr : (8 : ℝ) ≤ E := by exact_mod_cast hE8
  have hden : (0 : ℝ) < E - 1 := by linarith
  have hdiff : ((E - d : ℕ) : ℝ) = (E : ℝ) - d := by
    exact Nat.cast_sub hd
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hq2 : q ≤ 2 := by
    dsimp [q]
    rw [hdiff]
    apply (div_le_iff₀ hden).mpr
    have hdd : (0 : ℝ) ≤ d := Nat.cast_nonneg _
    linarith
  have hcore : (n : ℝ) * ((d : ℝ) + 1) ≤ 8 * ((E : ℝ) - 1) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hnr) (sub_nonneg.mpr hnr)]
  have hratio : |q - 1| ≤ 8 / (n : ℝ) := by
    have hnum : |1 - (d : ℝ)| ≤ (d : ℝ) + 1 := by
      apply abs_le.mpr
      constructor <;> linarith [show (0 : ℝ) ≤ d by exact_mod_cast Nat.zero_le d]
    have hqeq : q - 1 = (1 - (d : ℝ)) / ((E : ℝ) - 1) := by
      dsimp [q]
      rw [hdiff]
      field_simp
      ring
    have hnpos : (0 : ℝ) < n := by linarith
    have hfrac : ((d : ℝ) + 1) / ((E : ℝ) - 1) ≤ 8 / (n : ℝ) := by
      apply (div_le_iff₀ hden).mpr
      have hh : (d : ℝ) + 1 ≤ (8 * ((E : ℝ) - 1)) / (n : ℝ) :=
        (le_div_iff₀ hnpos).mpr (by nlinarith [hcore])
      convert hh using 1; ring
    rw [hqeq, abs_div, abs_of_pos hden]
    exact (div_le_div_of_nonneg_right hnum hden.le).trans hfrac
  exact ⟨hq0, hq2, hratio⟩

private theorem variance_mean_error_of_controls {n M J : ℕ} (G : Graph n)
    (j : ℕ) (hj : j < J) (hJ : J ≤ n) (hn : 0 < n)
    (K δ : ℝ) (_hK : 0 ≤ K) (_hδ : 0 ≤ δ)
    (hqueue : ((explore G j).queue.length : ℝ) ≤ K * n13 n)
    (hpool : |poolDensity M G j - poolDensity M G 0| ≤ δ / n13 n ^ 4) :
    |queryMean M G j - 1| ≤
      |(n : ℝ) * poolDensity M G 0 - 1| +
      poolDensity M G 0 * ((J : ℝ) + K * n13 n + 1) +
      (n : ℝ) * (δ / n13 n ^ 4) := by
  let p := poolDensity M G 0
  let d : ℝ := (revealQuery (explore G j)).card
  let q : ℝ := (explore G j).queue.length
  let r := rootIndicator G j
  have hp : 0 ≤ p := by dsimp [p, poolDensity]; positivity
  have hd0 : 0 ≤ d := Nat.cast_nonneg _
  have hdN : d ≤ n := by
    dsimp [d]
    exact_mod_cast queryCard_le_order G j (by omega : j < n)
  have hjJ : (j : ℝ) ≤ J := by exact_mod_cast hj.le
  have hq : q ≤ K * n13 n := hqueue
  have hr : 0 ≤ r ∧ r ≤ 1 := by
    dsimp [r, rootIndicator]
    split_ifs <;> norm_num
  have hbalance := queryCard_balance G j (by omega : j < n)
  have hpool' := abs_le.mp hpool
  have hmean : queryMean M G j - 1 =
      ((n : ℝ) * p - 1) - p * ((j : ℝ) + q + r) +
        d * (poolDensity M G j - p) := by
    dsimp [queryMean, p, d, q, r] at *
    nlinarith [congrArg (fun x : ℝ => x * poolDensity M G 0) hbalance]
  have hqsum : 0 ≤ (j : ℝ) + q + r := by
    have hq0 : 0 ≤ q := by dsimp [q]; positivity
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg _
    linarith [hr.1]
  have hqbound : (j : ℝ) + q + r ≤ (J : ℝ) + K * n13 n + 1 := by
    linarith [hr.2]
  have hpscaled := mul_le_mul_of_nonneg_left hqbound hp
  have hpoolscaled : |d * (poolDensity M G j - p)| ≤
      (n : ℝ) * (δ / n13 n ^ 4) := by
    rw [abs_mul, abs_of_nonneg hd0]
    exact mul_le_mul hdN hpool (abs_nonneg _)
      (by positivity : (0 : ℝ) ≤ n)
  rw [hmean]
  calc
    |((n : ℝ) * p - 1) - p * ((j : ℝ) + q + r) +
        d * (poolDensity M G j - p)| ≤
        |(n : ℝ) * p - 1| + p * ((j : ℝ) + q + r) +
          |d * (poolDensity M G j - p)| := by
            have hpq : 0 ≤ p * ((j : ℝ) + q + r) := mul_nonneg hp hqsum
            calc
              _ ≤ |((n : ℝ) * p - 1) - p * ((j : ℝ) + q + r)| +
                  |d * (poolDensity M G j - p)| := abs_add_le _ _
              _ ≤ |(n : ℝ) * p - 1| + |p * ((j : ℝ) + q + r)| +
                  |d * (poolDensity M G j - p)| := by
                    gcongr
                    simpa only [abs_neg, sub_eq_add_neg] using!
                      abs_add_le ((n : ℝ) * p - 1)
                        (-(p * ((j : ℝ) + q + r)))
              _ = _ := by rw [abs_of_nonneg hpq]
    _ ≤ _ := by linarith [hpscaled, hpoolscaled]

def varianceEnvelope (n M : ℕ) (T K : ℝ) : ℝ :=
  let b := n13 n
  let p := (M : ℝ) / (capacity n : ℝ)
  |(n : ℝ) * p - 1| +
    p * (T * b ^ 2 + K * b + 1) +
    (n : ℝ) / b ^ 4 +
    4 * (8 / (n : ℝ) + 2 * (p + 1 / b ^ 4))

private theorem varianceErrorMax_of_controls {n M J : ℕ} (G : Graph n)
    (hfinite : FiniteEnumerationStatement) (hM : M ≤ capacity n)
    (hG : G.card = M) (T K : ℝ) (hT : 0 ≤ T) (hK : 0 ≤ K)
    (hn : 32 ≤ n) (hJ8 : 8 * J ≤ n)
    (hbudget : HorizonBudget n M J 8)
    (hfloor : (J : ℝ) ≤ T * n23 n)
    (hqueue : ∀ j < J, ((explore G j).queue.length : ℝ) ≤ K * n13 n)
    (hpool : ∀ j < J,
      |poolDensity M G j - poolDensity M G 0| ≤ 1 / n13 n ^ 4) :
    varianceErrorMax M G J ≤ varianceEnvelope n M T K := by
  let b := n13 n
  let p := (M : ℝ) / (capacity n : ℝ)
  have hb : 0 < b := by
    dsimp [b, n13]
    exact Real.rpow_pos_of_pos (by exact_mod_cast (by omega : 0 < n)) _
  have hp : 0 ≤ p := by dsimp [p]; positivity
  have hsq : n23 n = b ^ 2 := n23_eq_n13_square n (by omega)
  have hfloor' : (J : ℝ) ≤ T * b ^ 2 := by simpa only [hsq] using! hfloor
  have hden : 0 ≤ 1 / b ^ 4 := by positivity
  have henv0 : 0 ≤ varianceEnvelope n M T K := by
    dsimp [varianceEnvelope]
    positivity
  apply varianceErrorMax_le G (varianceEnvelope n M T K) henv0
  intro j hj
  have hbetween := varianceAt_between hfinite hM G j hG hbudget hj
  have hm : queryMean M G j =
      ((revealQuery (explore G j)).card : ℝ) * poolDensity M G j := rfl
  have hmean : queryMean M G j ≤ 4 := by
    have hpos := historyAtom_probability_pos G j hG
    have hle := horizon_conditional_mean_le hfinite hM G j hG hbudget hj hpos
    have hEeq : capacity n - (revealTrace G j).yes.card -
        (revealTrace G j).no.card = poolEdgeCount G j := by
      unfold poolEdgeCount answeredCount
      rw [Finset.card_union_of_disjoint (revealTrace_yes_no_disjoint G j)]
      omega
    have hR : M - (revealTrace G j).yes.card ≤
        capacity n - (revealTrace G j).yes.card -
          (revealTrace G j).no.card := by
      rw [hEeq]
      exact poolSuccessCount_le_poolEdgeCount G j hG
    have hd : (revealQuery (explore G j)).card ≤
        capacity n - (revealTrace G j).yes.card -
          (revealTrace G j).no.card := by
      rw [hEeq]
      exact queryCard_le_poolEdgeCount G j
    have hraw := conditionalQueryMean_all hfinite hM G j hpos hR hd
    rw [hraw] at hle
    simpa only [queryMean, show (8 : ℝ) / 2 = 4 by norm_num] using! hle
  have hmean0 : 0 ≤ queryMean M G j := by
    dsimp [queryMean, poolDensity]
    positivity
  let E := capacity n - (revealTrace G j).yes.card -
    (revealTrace G j).no.card
  let R := M - (revealTrace G j).yes.card
  let d := (revealQuery (explore G j)).card
  let pj : ℝ := (R : ℝ) / E
  let q : ℝ := ((E - d : ℕ) : ℝ) / ((E : ℝ) - 1)
  have hEeq : E = poolEdgeCount G j := by
    dsimp [E, poolEdgeCount, answeredCount]
    rw [Finset.card_union_of_disjoint (revealTrace_yes_no_disjoint G j)]
    omega
  have hpjeq : pj = poolDensity M G j := by
    dsimp [pj, poolDensity, poolSuccessCount]
    rw [hEeq]
  have hpj0 : 0 ≤ pj := by dsimp [pj]; positivity
  have hpjP : pj ≤ p + 1 / b ^ 4 := by
    rw [hpjeq]
    have hh := (abs_le.mp (hpool j hj)).2
    rw [initial_pool_density] at hh
    simpa only [p, b] using! (show poolDensity M G j ≤
      (M : ℝ) / (capacity n : ℝ) + 1 / n13 n ^ 4 by linarith)
  have hq0 : 0 ≤ q ∧ q ≤ 2 ∧ |q - 1| ≤ 8 / (n : ℝ) := by
    simpa only [q, E, d, hEeq] using!
      pool_factor_bounds G j hn hJ8 hbudget hj
  have hmean' : (d : ℝ) * pj = queryMean M G j := by
    rw [hpjeq]
    rfl
  have hvar : varianceAt M G j = queryMean M G j * (1 - pj) * q := by
    have hv := varianceAt_exact hfinite hM G j hG hbudget hj
    calc
      varianceAt M G j = (d : ℝ) * pj * (1 - pj) * q := by
        convert hv using 1; ring
      _ = queryMean M G j * (1 - pj) * q := by rw [hmean']
  have hmeanerr := variance_mean_error_of_controls G j hj hbudget.1
    (by omega : 0 < n) K 1 hK (by norm_num) (hqueue j hj) (hpool j hj)
  have hmeanbound : |queryMean M G j - 1| ≤
      |(n : ℝ) * p - 1| +
        p * (T * b ^ 2 + K * b + 1) + (n : ℝ) / b ^ 4 := by
    rw [initial_pool_density] at hmeanerr
    have heq : (n : ℝ) * (1 / b ^ 4) = (n : ℝ) / b ^ 4 := by ring
    have hmul : p * ((J : ℝ) + K * b + 1) ≤
        p * (T * b ^ 2 + K * b + 1) :=
      mul_le_mul_of_nonneg_left (by linarith [hfloor']) hp
    calc
      _ ≤ |(n : ℝ) * p - 1| +
          p * ((J : ℝ) + K * b + 1) + (n : ℝ) * (1 / b ^ 4) := by
            simpa only [p, b] using! hmeanerr
      _ ≤ _ := by rw [heq]; linarith [hmul]
  have hfactor := variance_factor_error (queryMean M G j) pj q
    (|(n : ℝ) * p - 1| + p * (T * b ^ 2 + K * b + 1) +
      (n : ℝ) / b ^ 4) (p + 1 / b ^ 4) (8 / (n : ℝ))
      hmean0 hmean hpj0 hpjP hq0.1 hq0.2.1 hmeanbound hq0.2.2
  rw [hvar]
  simpa only [varianceEnvelope, b, p] using! hfactor

private theorem varianceEnvelope_tendsto (M : NatSeq) (lam T K : ℝ)
    (hcritical : criticalWindow M lam) :
    Tendsto (fun n => varianceEnvelope n (M n) T K) atTop (𝓝 0) := by
  let p : ℕ → ℝ := fun n => (M n : ℝ) / (capacity n : ℝ)
  let b : ℕ → ℝ := n13
  have hnp := critical_initial_density_tendsto_one M lam hcritical
  have hdiff : Tendsto (fun n : ℕ => |(n : ℝ) * p n - 1|)
      atTop (𝓝 0) := by
    simpa only [p, sub_self, abs_zero] using!
      (hnp.sub (tendsto_const_nhds (x := (1 : ℝ)))).abs
  have hbInv : Tendsto (fun n => (b n)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp n13_tendsto_atTop
  have hnInv : Tendsto (fun n : ℕ => ((n : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hp : Tendsto p atTop (𝓝 0) := by
    simpa only [p] using!
      critical_initial_density_tendsto_zero M lam hcritical
  have hpb2 : Tendsto (fun n => p n * b n ^ 2) atTop (𝓝 0) := by
    have hh : Tendsto (fun n : ℕ => ((n : ℝ) * p n) * (b n)⁻¹)
        atTop (𝓝 0) := by
      simpa only [p, one_mul, mul_zero] using! hnp.mul hbInv
    have heq : (fun n : ℕ => ((n : ℝ) * p n) * (b n)⁻¹) =ᶠ[atTop]
        (fun n => p n * b n ^ 2) := by
      filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
      have hbn : 0 < b n := by
        dsimp [b, n13]
        exact Real.rpow_pos_of_pos (by exact_mod_cast hn) _
      have hcub := n13_cube n hn
      dsimp [p, b] at *
      rw [← hcub]
      field_simp
    exact hh.congr' heq
  have hpb : Tendsto (fun n => p n * b n) atTop (𝓝 0) := by
    have hh : Tendsto (fun n : ℕ => (p n * b n ^ 2) * (b n)⁻¹)
        atTop (𝓝 0) := by
      simpa only [zero_mul] using! hpb2.mul hbInv
    have heq : (fun n : ℕ => (p n * b n ^ 2) * (b n)⁻¹) =ᶠ[atTop]
        (fun n => p n * b n) := by
      filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
      have hbn : b n ≠ 0 := ne_of_gt (by
        dsimp [b, n13]
        exact Real.rpow_pos_of_pos (by exact_mod_cast hn) _)
      field_simp
    exact hh.congr' heq
  have hb4 : Tendsto (fun n : ℕ => 1 / b n ^ 4) atTop (𝓝 0) := by
    have hh := hbInv.pow 4
    simpa only [inv_pow, one_div, zero_pow (by norm_num : 4 ≠ 0)] using! hh
  have hnb4 : Tendsto (fun n : ℕ => (n : ℝ) / b n ^ 4) atTop (𝓝 0) := by
    have heq : (fun n : ℕ => (b n)⁻¹) =ᶠ[atTop]
        (fun n => (n : ℝ) / b n ^ 4) := by
      filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
      have hbn : 0 < b n := by
        dsimp [b, n13]
        exact Real.rpow_pos_of_pos (by exact_mod_cast hn) _
      have hcub := n13_cube n hn
      dsimp [b] at *
      rw [← hcub]
      field_simp
    exact hbInv.congr' heq
  have hlim : Tendsto (fun n : ℕ =>
      |(n : ℝ) * p n - 1| +
        (T * (p n * b n ^ 2) + K * (p n * b n) + p n) +
        (n : ℝ) / b n ^ 4 +
        4 * (8 * (n : ℝ)⁻¹ + 2 * (p n + 1 / b n ^ 4)))
      atTop (𝓝 0) := by
    convert (((hdiff.add (((hpb2.mul_const T).add
      (hpb.mul_const K)).add hp)).add hnb4).add
      (((hnInv.mul_const 8).add ((hp.add hb4).mul_const 2)).mul_const 4)) using 1
    · funext n; ring
    · ring_nf
  exact hlim.congr' (Filter.Eventually.of_forall (fun n => by
    dsimp [varianceEnvelope, p, b]
    ring))

private theorem probM_mono {n M : ℕ} (P Q : Graph n → Prop)
    (h : ∀ G, P G → Q G) : probM n M P ≤ probM n M Q := by
  unfold probM
  have hs : (fixedGraphs n M).filter P ⊆ (fixedGraphs n M).filter Q := by
    intro G hG
    exact Finset.mem_filter.mpr
      ⟨(Finset.mem_filter.mp hG).1, h G (Finset.mem_filter.mp hG).2⟩
  have hc : (((fixedGraphs n M).filter P).card : ℝ) ≤
      (((fixedGraphs n M).filter Q).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hs
  exact div_le_div_of_nonneg_right hc (Nat.cast_nonneg _)

private theorem probM_or_le {n M : ℕ} (P Q : Graph n → Prop)
    (hM : M ≤ capacity n) :
    probM n M (fun G => P G ∨ Q G) ≤ probM n M P + probM n M Q := by
  have hF : (0 : ℝ) < ((fixedGraphs n M).card : ℝ) := by
    exact_mod_cast (Finset.card_pos.mpr (fixedGraphs_nonempty hM))
  have hc := Finset.card_union_le
    ((fixedGraphs n M).filter P) ((fixedGraphs n M).filter Q)
  have hcr : (((fixedGraphs n M).filter P ∪
      (fixedGraphs n M).filter Q).card : ℝ) ≤
      ((fixedGraphs n M).filter P).card +
        ((fixedGraphs n M).filter Q).card := by exact_mod_cast hc
  unfold probM
  rw [← add_div]
  have hbound := div_le_div_of_nonneg_right hcr hF.le
  convert hbound using 1
  congr 1
  congr 1
  congr 1
  ext G
  simp [and_or_left]

/-- The maximum over `j<J` converges to zero in probability under the
same fixed-edge law as the drift theorem. -/
theorem critical_variance_probability
    (hfinite : FiniteEnumerationStatement) (M : NatSeq) (lam T ε : ℝ)
    (hcritical : criticalWindow M lam) (hT : 0 ≤ T) (hε : 0 < ε) :
    Tendsto (fun n => probM n (M n) (fun G =>
      ε < varianceErrorMax (M n) G ⌊T * n23 n⌋₊)) atTop (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro c hc
    exact Filter.Eventually.of_forall (fun n =>
      lt_of_lt_of_le hc (by unfold probM; positivity))
  · intro d hd
    have hd4 : 0 < d / 4 := by linarith
    obtain ⟨K, hK, hqueue⟩ :=
      critical_queue_tight hfinite M lam T (d / 4) hcritical hT hd4
    have hpool := (critical_poolDensity_concentration hfinite M lam T 1
      hcritical hT (by norm_num)).eventually_lt_const hd4
    have henv := (varianceEnvelope_tendsto M lam T K hcritical).eventually_lt_const hε
    filter_upwards [hcritical.1,
      eventually_horizonBudget M lam T hcritical hT,
      eventually_eighth_horizon T hT,
      eventually_ge_atTop (32 : ℕ), hqueue, hpool, henv]
      with n hM hbudget hJ8 hn hqb hpb heb
    let J : ℕ := ⌊T * n23 n⌋₊
    let b : ℝ := n13 n
    let Q : Graph n → Prop := fun G =>
      ∃ j ≤ J, K * b < ((explore G j).queue.length : ℝ)
    let P : Graph n → Prop := fun G =>
      ∃ j ≤ J, 1 / b ^ 4 ≤
        |poolDensity (M n) G j - poolDensity (M n) G 0|
    let A : Graph n → Prop := fun G =>
      ε < varianceErrorMax (M n) G J
    have hfloor : (J : ℝ) ≤ T * n23 n :=
      Nat.floor_le (mul_nonneg hT (n23_pos n (by omega)).le)
    have hcontain : ∀ G : Graph n, G.card = M n → A G → Q G ∨ P G := by
      intro G hG hA
      by_cases hQ : Q G
      · exact Or.inl hQ
      by_cases hP : P G
      · exact Or.inr hP
      exfalso
      have hqn : ∀ j < J,
          ((explore G j).queue.length : ℝ) ≤ K * b := by
        intro j hj
        exact le_of_not_gt (fun hh => hQ ⟨j, hj.le, hh⟩)
      have hpn : ∀ j < J,
          |poolDensity (M n) G j - poolDensity (M n) G 0| ≤ 1 / b ^ 4 := by
        intro j hj
        exact le_of_not_gt (fun hh => hP ⟨j, hj.le, hh.le⟩)
      have hbound := varianceErrorMax_of_controls G hfinite hM hG T K hT hK.le
        hn hJ8 hbudget hfloor hqn hpn
      have henv' : varianceEnvelope n (M n) T K < ε := heb
      exact (not_lt_of_ge (le_trans hbound henv'.le)) hA
    have hmono : probM n (M n) A ≤
        probM n (M n) (fun G => Q G ∨ P G) := by
      calc
        probM n (M n) A =
            probM n (M n) (fun G => G.card = M n ∧ A G) := by
              unfold probM
              congr 1
              apply congrArg (fun s : Finset (Graph n) => (s.card : ℝ))
              ext G
              simp only [Finset.mem_filter]
              constructor
              · intro ⟨hG, hA⟩
                exact ⟨hG, (Finset.mem_filter.mp hG).2, hA⟩
              · intro ⟨hG, _, hA⟩
                exact ⟨hG, hA⟩
        _ ≤ probM n (M n) (fun G => Q G ∨ P G) :=
          probM_mono _ _ (fun G h => hcontain G h.1 h.2)
    have hor := probM_or_le Q P hM
    have hq : probM n (M n) Q ≤ d / 4 := by
      simpa only [Q, J, b] using! hqb
    have hp : probM n (M n) P < d / 4 := by
      simpa only [P, J, b] using! hpb
    have hfinal : probM n (M n) A < d := by linarith
    simpa only [A, J] using! hfinal

private theorem varianceErrorMax_bound {n M J : ℕ}
    (hfinite : FiniteEnumerationStatement) (hM : M ≤ capacity n)
    (hbudget : HorizonBudget n M J 8) (G : Graph n) (hG : G.card = M) :
    0 ≤ varianceErrorMax M G J ∧ varianceErrorMax M G J ≤ 3 := by
  have hnonneg : 0 ≤ varianceErrorMax M G J := by
    unfold varianceErrorMax
    have hh := Finset.le_sup'
      (s := Finset.range (J + 1))
      (f := fun j => if j < J then |varianceAt M G j - 1| else 0)
      (Finset.mem_range.mpr (by omega : J < J + 1))
    simpa using! hh
  refine ⟨hnonneg, varianceErrorMax_le G 3 (by norm_num) ?_⟩
  intro j hj
  have hv := varianceAt_between hfinite hM G j hG hbudget hj
  apply abs_le.mpr
  constructor <;> linarith

private theorem expectation_split {n M : ℕ} (hM : M ≤ capacity n)
    (X : Graph n → ℝ) (ε C : ℝ) (hε : 0 ≤ ε) (_hC : 0 ≤ C)
    (hX : ∀ G ∈ fixedGraphs n M, 0 ≤ X G ∧ X G ≤ C) :
    expectM n M X ≤ ε + C * probM n M (fun G => ε < X G) := by
  have hF : (0 : ℝ) < ((fixedGraphs n M).card : ℝ) := by
    exact_mod_cast (Finset.card_pos.mpr (fixedGraphs_nonempty hM))
  have hpoint : ∀ G ∈ fixedGraphs n M,
      X G ≤ ε + C * (if ε < X G then 1 else 0) := by
    intro G hG
    by_cases hb : ε < X G
    · simp only [if_pos hb, mul_one]
      linarith [(hX G hG).2]
    · simp only [if_neg hb, mul_zero, add_zero]
      exact le_of_not_gt hb
  have hsum := Finset.sum_le_sum hpoint
  have hfilter : (∑ G ∈ fixedGraphs n M,
      (if ε < X G then (1 : ℝ) else 0)) =
      (((fixedGraphs n M).filter (fun G => ε < X G)).card : ℝ) := by
    simp
  have hbound : (fixedGraphs n M).sum X ≤
      ε * ((fixedGraphs n M).card : ℝ) +
        C * (((fixedGraphs n M).filter (fun G => ε < X G)).card : ℝ) := by
    calc
      _ ≤ (fixedGraphs n M).sum
          (fun G => ε + C * (if ε < X G then 1 else 0)) := hsum
      _ = _ := by
        rw [Finset.sum_add_distrib]
        simp only [Finset.sum_const, nsmul_eq_mul]
        rw [← Finset.mul_sum, hfilter]
        ring
  unfold expectM probM
  calc
    _ ≤ (ε * ((fixedGraphs n M).card : ℝ) +
        C * (((fixedGraphs n M).filter (fun G => ε < X G)).card : ℝ)) /
          ((fixedGraphs n M).card : ℝ) :=
      div_le_div_of_nonneg_right hbound hF.le
    _ = _ := by field_simp

/-- The deterministic conditional-variance budget upgrades the maximum
probability limit to L1, with no change of the fixed-edge measure. -/
theorem critical_variance_L1
    (hfinite : FiniteEnumerationStatement) (M : NatSeq) (lam T : ℝ)
    (hcritical : criticalWindow M lam) (hT : 0 ≤ T) :
    Tendsto (fun n => expectM n (M n) (fun G =>
      varianceErrorMax (M n) G ⌊T * n23 n⌋₊)) atTop (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro c hc
    exact Filter.Eventually.of_forall (fun n => by
      have hpoint : ∀ G : Graph n,
          0 ≤ varianceErrorMax (M n) G ⌊T * n23 n⌋₊ := by
        intro G
        unfold varianceErrorMax
        have hh := Finset.le_sup'
          (s := Finset.range (⌊T * n23 n⌋₊ + 1))
          (f := fun j => if j < ⌊T * n23 n⌋₊ then
            |varianceAt (M n) G j - 1| else 0)
          (Finset.mem_range.mpr (by omega : ⌊T * n23 n⌋₊ <
            ⌊T * n23 n⌋₊ + 1))
        simpa using! hh
      unfold expectM
      have hsum : 0 ≤ (fixedGraphs n (M n)).sum (fun G =>
          varianceErrorMax (M n) G ⌊T * n23 n⌋₊) :=
        Finset.sum_nonneg (fun G hG => hpoint G)
      exact lt_of_lt_of_le hc (div_nonneg hsum (Nat.cast_nonneg _)))
  · intro d hd
    let ε : ℝ := d / 2
    have hε : 0 < ε := by dsimp [ε]; linarith
    have hprob' := (critical_variance_probability hfinite M lam T ε
      hcritical hT hε).eventually_lt_const
        (by linarith : (0 : ℝ) < d / 6)
    filter_upwards [hcritical.1,
      eventually_horizonBudget M lam T hcritical hT, hprob']
      with n hM hbudget hpr
    let J : ℕ := ⌊T * n23 n⌋₊
    have hbound := expectation_split hM
      (fun G : Graph n => varianceErrorMax (M n) G J) ε 3 hε.le
      (by norm_num) (by
        intro G hG
        exact varianceErrorMax_bound hfinite hM hbudget G
          (Finset.mem_filter.mp hG).2)
    have hpr' : probM n (M n) (fun G =>
        ε < varianceErrorMax (M n) G J) < d / 6 := by
      simpa only [J] using! hpr
    have hf : expectM n (M n) (fun G =>
        varianceErrorMax (M n) G J) < d := by
      dsimp [ε] at hbound
      linarith
    simpa only [J] using! hf

end

end Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_Variance


/-!
# Characteristic functions of the centered exploration

The averaging below is always over the actual fixed-edge support.  In
particular the conditional characteristic coefficient is a function of the
realized history and remains inside the outer expectation.
-/

namespace Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_Characteristic

open Erdos745.WrapUp
open Erdos745.WrapUp.Proofs.Internal.W01_ENUM_Finite
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_Reveal
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_FiniteHorizon
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_FiniteAtoms
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_Asymptotics
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_Horizon
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_CriticalBudget
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_PoolMartingale
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_QueueControl
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_Variance
open Filter
open scoped BigOperators Topology

noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1000000

def complexExpectM (n M : ℕ) (f : Graph n → ℂ) : ℂ :=
  (fixedGraphs n M).sum f / ((fixedGraphs n M).card : ℂ)

def complexHistoryAverage {n : ℕ} (M : ℕ) (G : Graph n)
    (j : ℕ) (f : Graph n → ℂ) : ℂ :=
  (historyAtom M G j).sum f / ((historyAtom M G j).card : ℂ)

def centeredQuery {n : ℕ} (M : ℕ) (G : Graph n) (j : ℕ) : ℝ :=
  (queryCount G j : ℝ) - queryMean M G j

def meshIndex (n : ℕ) (t : ℝ) : ℕ := ⌊t * n23 n⌋₊

def stepCoefficient {m : ℕ} (n : ℕ) (t z : Fin m → ℝ) (j : ℕ) : ℝ :=
  ∑ i : Fin m, if j < meshIndex n (t i) then z i else 0

def stepSum {n : ℕ} (M : ℕ) (G : Graph n)
    (theta : ℕ → ℝ) (b : ℝ) (k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range k, theta j * centeredQuery M G j / b

def stepAlpha (n M : ℕ) (theta : ℕ → ℝ)
    (b : ℝ) (k : ℕ) : ℂ :=
  complexExpectM n M (fun G => Complex.exp
    (Complex.I * (stepSum M G theta b k : ℂ)))

def conditionalCoefficient {n : ℕ} (M : ℕ) (theta : ℕ → ℝ)
    (b : ℝ) (G : Graph n) (j : ℕ) : ℂ :=
  complexHistoryAverage M G j (fun H => Complex.exp
    (Complex.I * ((theta j * centeredQuery M H j / b : ℝ) : ℂ)))

def gaussianCoefficient (theta : ℕ → ℝ) (b : ℝ) (j : ℕ) : ℂ :=
  Complex.exp ((-(theta j ^ 2 / (2 * b ^ 2)) : ℝ) : ℂ)

/-- Each finite-dimensional linear combination is a deterministic weighted
sum of the same centered query increments. -/
theorem mesh_linear_combination {n m M J : ℕ} (G : Graph n)
    (t z : Fin m → ℝ) (b : ℝ)
    (hJ : ∀ i : Fin m, meshIndex n (t i) ≤ J) :
    (∑ i : Fin m, z i * centeredPartial M G (meshIndex n (t i))) / b =
      stepSum M G (stepCoefficient n t z) b J := by
  unfold stepSum stepCoefficient centeredPartial centeredQuery
  have hcore :
    (∑ i : Fin m, z i *
        ∑ j ∈ Finset.range (meshIndex n (t i)),
          ((queryCount G j : ℝ) - queryMean M G j)) =
        ∑ j ∈ Finset.range J,
          (∑ i : Fin m, if j < meshIndex n (t i) then z i else 0) *
            ((queryCount G j : ℝ) - queryMean M G j) := by
    calc
      _ = ∑ i : Fin m, ∑ j ∈ Finset.range J,
          (if j < meshIndex n (t i) then z i else 0) *
            ((queryCount G j : ℝ) - queryMean M G j) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.mul_sum]
          have hfilter : (Finset.range J).filter
              (fun j => j < meshIndex n (t i)) =
              Finset.range (meshIndex n (t i)) := by
            ext j
            simp only [Finset.mem_filter, Finset.mem_range]
            have hk := hJ i
            omega
          rw [← hfilter, Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro j hj
          split_ifs <;> simp
      _ = ∑ j ∈ Finset.range J,
          (∑ i : Fin m, if j < meshIndex n (t i) then z i else 0) *
            ((queryCount G j : ℝ) - queryMean M G j) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro j hj
          rw [Finset.sum_mul]
  rw [hcore, Finset.sum_div]

theorem stepCoefficient_abs_le {m n : ℕ} (t z : Fin m → ℝ) (j : ℕ) :
    |stepCoefficient n t z j| ≤ ∑ i : Fin m, |z i| := by
  unfold stepCoefficient
  calc
    |∑ i : Fin m, if j < meshIndex n (t i) then z i else 0| ≤
        ∑ i : Fin m, |if j < meshIndex n (t i) then z i else 0| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin m, |z i| := by
      apply Finset.sum_le_sum
      intro i hi
      split_ifs <;> simp

private theorem stepSum_zero {n M : ℕ} (G : Graph n)
    (theta : ℕ → ℝ) (b : ℝ) : stepSum M G theta b 0 = 0 := by
  simp [stepSum]

private theorem stepSum_succ {n M : ℕ} (G : Graph n)
    (theta : ℕ → ℝ) (b : ℝ) (j : ℕ) :
    stepSum M G theta b (j + 1) =
      stepSum M G theta b j + theta j * centeredQuery M G j / b := by
  simp [stepSum, Finset.sum_range_succ]

private theorem stepSum_eq_of_trace {n M : ℕ} (G H : Graph n)
    (theta : ℕ → ℝ) (b : ℝ) (j : ℕ)
    (h : revealTrace H j = revealTrace G j) :
    stepSum M H theta b j = stepSum M G theta b j := by
  unfold stepSum
  apply Finset.sum_congr rfl
  intro i hi
  have hij := Finset.mem_range.mp hi
  congr 1
  unfold centeredQuery
  rw [queryCount_eq_of_later_trace G H hij h,
    queryMean_eq_of_trace G H i
      (trace_eq_of_later G H hij.le h)]

private theorem complex_fiber_average {n M : ℕ} (hM : M ≤ capacity n)
    (j : ℕ) (F f : Graph n → ℂ)
    (hF : ∀ G H, G ∈ fixedGraphs n M → H ∈ fixedGraphs n M →
      revealTrace H j = revealTrace G j → F H = F G) :
    complexExpectM n M (fun G => F G * f G) =
      complexExpectM n M (fun G => F G *
        complexHistoryAverage M G j f) := by
  let s := fixedGraphs n M
  let t := s.image (fun G => revealTrace G j)
  have hmaps : ∀ G ∈ s, revealTrace G j ∈ t := by
    intro G hG
    exact Finset.mem_image.mpr ⟨G, hG, rfl⟩
  have hnum : (∑ G ∈ s, F G * f G) =
      ∑ G ∈ s, F G * complexHistoryAverage M G j f := by
    rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun G => F G * f G),
      ← Finset.sum_fiberwise_of_maps_to hmaps
        (fun G => F G * complexHistoryAverage M G j f)]
    apply Finset.sum_congr rfl
    intro r hr
    obtain ⟨G, hG, rfl⟩ := Finset.mem_image.mp hr
    have hcard : ((historyAtom M G j).card : ℂ) ≠ 0 := by
      have hGc : G.card = M := (Finset.mem_filter.mp hG).2
      exact_mod_cast (Finset.card_ne_zero.mpr
        (historyAtom_nonempty G j hGc))
    have hatom : s.filter (fun H => revealTrace H j = revealTrace G j) =
        historyAtom M G j := rfl
    rw [hatom]
    calc
      (∑ H ∈ historyAtom M G j, F H * f H) =
          F G * ∑ H ∈ historyAtom M G j, f H := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro H hH
            rw [hF G H hG (Finset.mem_filter.mp hH).1
              (Finset.mem_filter.mp hH).2]
      _ = ∑ H ∈ historyAtom M G j,
          F H * complexHistoryAverage M H j f := by
            have hconst : ∀ H ∈ historyAtom M G j,
                F H * complexHistoryAverage M H j f =
                  F G * complexHistoryAverage M G j f := by
              intro H hH
              rw [hF G H hG (Finset.mem_filter.mp hH).1
                (Finset.mem_filter.mp hH).2]
              have hs : historyAtom M H j = historyAtom M G j := by
                unfold historyAtom
                ext X
                simp [(Finset.mem_filter.mp hH).2]
              unfold complexHistoryAverage
              rw [hs]
            symm
            calc
              (∑ H ∈ historyAtom M G j,
                  F H * complexHistoryAverage M H j f) =
                  ∑ _H ∈ historyAtom M G j,
                    F G * complexHistoryAverage M G j f := by
                    apply Finset.sum_congr rfl
                    intro H hH
                    exact hconst H hH
              _ = F G * ∑ H ∈ historyAtom M G j, f H := by
                    simp only [Finset.sum_const, nsmul_eq_mul]
                    unfold complexHistoryAverage
                    field_simp [hcard]
  unfold complexExpectM
  exact congrArg (fun x : ℂ => x / (s.card : ℂ)) hnum

/-- The adapted recursion retains the random history coefficient under
`complexExpectM`; no independence of successive queries is used. -/
theorem stepAlpha_recursion {n M : ℕ} (hM : M ≤ capacity n)
    (theta : ℕ → ℝ) (b : ℝ) (j : ℕ) :
    stepAlpha n M theta b (j + 1) =
      gaussianCoefficient theta b j * stepAlpha n M theta b j +
      complexExpectM n M (fun G =>
        Complex.exp (Complex.I * (stepSum M G theta b j : ℂ)) *
          (conditionalCoefficient M theta b G j -
            gaussianCoefficient theta b j)) := by
  have hF : ∀ G H : Graph n, G ∈ fixedGraphs n M →
      H ∈ fixedGraphs n M → revealTrace H j = revealTrace G j →
      Complex.exp (Complex.I * (stepSum M H theta b j : ℂ)) =
        Complex.exp (Complex.I * (stepSum M G theta b j : ℂ)) := by
    intro G H hG hH h
    rw [stepSum_eq_of_trace G H theta b j h]
  have hfiber := complex_fiber_average hM j
    (fun G : Graph n =>
      Complex.exp (Complex.I * (stepSum M G theta b j : ℂ)))
    (fun G : Graph n =>
      Complex.exp (Complex.I * ((theta j * centeredQuery M G j / b : ℝ) : ℂ))) hF
  have hstep : stepAlpha n M theta b (j + 1) =
      complexExpectM n M (fun G =>
        Complex.exp (Complex.I * (stepSum M G theta b j : ℂ)) *
          conditionalCoefficient M theta b G j) := by
    unfold stepAlpha
    change complexExpectM n M (fun G =>
        Complex.exp (Complex.I * (stepSum M G theta b (j + 1) : ℂ))) =
      complexExpectM n M (fun G =>
        Complex.exp (Complex.I * (stepSum M G theta b j : ℂ)) *
          complexHistoryAverage M G j (fun H =>
            Complex.exp (Complex.I *
              ((theta j * centeredQuery M H j / b : ℝ) : ℂ))))
    rw [← hfiber]
    unfold complexExpectM
    congr 1
    apply Finset.sum_congr rfl
    intro G hG
    rw [stepSum_succ]
    have heq : Complex.I *
        ((stepSum M G theta b j + theta j * centeredQuery M G j / b : ℝ) : ℂ) =
        Complex.I * (stepSum M G theta b j : ℂ) +
          Complex.I * ((theta j * centeredQuery M G j / b : ℝ) : ℂ) := by
      push_cast
      ring
    rw [heq, Complex.exp_add]
  rw [hstep]
  unfold stepAlpha complexExpectM
  rw [← mul_div_assoc, ← add_div, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro G hG
  ring

theorem stepAlpha_zero {n M : ℕ} (hM : M ≤ capacity n)
    (theta : ℕ → ℝ) (b : ℝ) : stepAlpha n M theta b 0 = 1 := by
  have hne : ((fixedGraphs n M).card : ℂ) ≠ 0 := by
    exact_mod_cast (Finset.card_ne_zero.mpr (fixedGraphs_nonempty hM))
  simp [stepAlpha, complexExpectM, stepSum_zero, hne]

theorem gaussianCoefficient_norm_le (theta : ℕ → ℝ)
    (b : ℝ) (j : ℕ) : ‖gaussianCoefficient theta b j‖ ≤ 1 := by
  unfold gaussianCoefficient
  rw [← Complex.ofReal_exp, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  exact (Real.exp_le_one_iff).2 (neg_nonpos.mpr (by positivity))

private theorem complex_unit_exp (u : ℝ) :
    ‖Complex.exp (Complex.I * (u : ℂ))‖ = 1 :=
  Complex.norm_exp_I_mul_ofReal u

/-- A global cubic Taylor bound on the imaginary axis.  For large `u`,
unit modulus and the polynomial terms give the same cubic majorant. -/
theorem imaginary_exp_taylor (u : ℝ) :
    ‖Complex.exp (Complex.I * (u : ℂ)) -
      (1 + Complex.I * (u : ℂ) - ((u ^ 2 / 2 : ℝ) : ℂ))‖ ≤
      4 * |u| ^ 3 := by
  let z : ℂ := Complex.I * (u : ℂ)
  have hz : ‖z‖ = |u| := by
    dsimp [z]
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
  have hpoly : (∑ m ∈ Finset.range 3, z ^ m / (m.factorial : ℂ)) =
      1 + Complex.I * (u : ℂ) - ((u ^ 2 / 2 : ℝ) : ℂ) := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    dsimp [z]
    norm_num
    rw [mul_pow, Complex.I_sq]
    push_cast
    ring
  by_cases hu : |u| ≤ 1
  · have h := Complex.exp_bound (x := z) (by simpa [hz] using! hu)
        (n := 3) (by norm_num)
    rw [hpoly, hz] at h
    nlinarith [abs_nonneg u, pow_nonneg (abs_nonneg u) 3]
  · have hu1 : 1 ≤ |u| := le_of_not_ge hu
    have h1 : 1 ≤ |u| ^ 3 := by nlinarith [sq_nonneg (|u| - 1)]
    have h2 : |u| ≤ |u| ^ 3 := by nlinarith [sq_nonneg (|u| - 1)]
    have h3 : |u| ^ 2 / 2 ≤ |u| ^ 3 := by
      nlinarith [sq_nonneg (|u| - 1)]
    have hnorm : ‖Complex.I * (u : ℂ)‖ = |u| := hz
    have hsq : ‖((u ^ 2 / 2 : ℝ) : ℂ)‖ = |u| ^ 2 / 2 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      rw [← sq_abs]
    calc
      _ ≤ ‖Complex.exp z‖ + ‖(1 : ℂ)‖ + ‖z‖ +
            ‖((u ^ 2 / 2 : ℝ) : ℂ)‖ := by
            dsimp [z]
            have ha := norm_sub_le (Complex.exp (Complex.I * (u : ℂ)))
              (1 + Complex.I * (u : ℂ) - ((u ^ 2 / 2 : ℝ) : ℂ))
            have hb := norm_add_le (1 : ℂ) (Complex.I * (u : ℂ))
            have hc := norm_sub_le (1 + Complex.I * (u : ℂ))
              (((u ^ 2 / 2 : ℝ) : ℂ))
            linarith
      _ = 2 + |u| + |u| ^ 2 / 2 := by
            rw [complex_unit_exp, norm_one, hnorm, hsq]
            ring
      _ ≤ 4 * |u| ^ 3 := by nlinarith

private theorem centered_fourth_point (x m : ℝ) (hx : 0 ≤ x)
    (hm : 0 ≤ m) : |x - m| ^ 4 ≤ 8 * (x ^ 4 + m ^ 4) := by
  have htri : |x - m| ≤ x + m := by
    calc
      |x - m| ≤ |x| + |m| := abs_sub x m
      _ = x + m := by rw [abs_of_nonneg hx, abs_of_nonneg hm]
  have hpow := pow_le_pow_left₀ (abs_nonneg _) htri 4
  simpa only [show 2 ^ (4 - 1) = (8 : ℝ) by norm_num] using!
    hpow.trans (add_pow_le hx hm 4)

private theorem cube_le_fourth (x : ℝ) : |x| ^ 3 ≤ 1 + |x| ^ 4 := by
  by_cases h : |x| ≤ 1
  · have h0 := abs_nonneg x
    have hh : |x| ^ 3 ≤ 1 := pow_le_one₀ h0 h
    nlinarith [pow_nonneg h0 4]
  · have h1 : 1 ≤ |x| := le_of_not_ge h
    have h0 := abs_nonneg x
    have hh : 0 ≤ |x| ^ 3 * (|x| - 1) :=
      mul_nonneg (pow_nonneg h0 3) (sub_nonneg.mpr h1)
    nlinarith

private def C4 : ℝ := (8 : ℝ) ^ 4 + 6 * 8 ^ 3 + 7 * 8 ^ 2 + 8
private def C3 : ℝ := 1 + 8 * (C4 + 4 ^ 4)

private theorem history_mean_eq_queryMean {n M : ℕ}
    (hfinite : FiniteEnumerationStatement) (hM : M ≤ capacity n)
    (G : Graph n) (j : ℕ) (hG : G.card = M) :
    historyAverage M G j (fun H => (queryCount H j : ℝ)) =
      queryMean M G j := by
  have hz := historyAverage_centeredQuery_zero hfinite hM G j hG
  have hc := historyAverage_const G j hG (queryMean M G j)
  change historyAverage M G j (fun H => (queryCount H j : ℝ) -
      queryMean M G j) = 0 at hz
  have hlinear : historyAverage M G j (fun H => (queryCount H j : ℝ) -
      queryMean M G j) =
      historyAverage M G j (fun H => (queryCount H j : ℝ)) -
        historyAverage M G j (fun _ => queryMean M G j) := by
    unfold historyAverage
    rw [Finset.sum_sub_distrib, sub_div]
  rw [hlinear, hc] at hz
  exact sub_eq_zero.mp hz

private theorem history_centered_square {n M : ℕ}
    (hfinite : FiniteEnumerationStatement) (hM : M ≤ capacity n)
    (G : Graph n) (j : ℕ) (hG : G.card = M) :
    historyAverage M G j (fun H => centeredQuery M H j ^ 2) =
      varianceAt M G j := by
  let s := historyAtom M G j
  let m := queryMean M G j
  have hcard : (s.card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_ne_zero.mpr (historyAtom_nonempty G j hG))
  have hmean := history_mean_eq_queryMean hfinite hM G j hG
  have hraw1 := historyAverage_queryCount hM G j hG
  have hraw2 := historyAverage_querySquare hM G j hG
  have hconst := historyAverage_const G j hG (m ^ 2)
  have hmean' : conditionalQueryRawMoment M G j 1 = m := by
    rw [← hraw1, hmean]
  have htrace : ∀ H ∈ s, queryMean M H j = m := by
    intro H hH
    exact queryMean_eq_of_trace G H j (Finset.mem_filter.mp hH).2
  have hexpand : (s.sum (fun H => centeredQuery M H j ^ 2)) =
      s.sum (fun H => (queryCount H j : ℝ) ^ 2) -
        2 * m * s.sum (fun H => (queryCount H j : ℝ)) +
        (s.card : ℝ) * m ^ 2 := by
    calc
      _ = s.sum (fun H => (queryCount H j : ℝ) ^ 2 -
          2 * m * (queryCount H j : ℝ) + m ^ 2) := by
            apply Finset.sum_congr rfl
            intro H hH
            unfold centeredQuery
            rw [htrace H hH]
            ring
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
        simp only [Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
  unfold historyAverage varianceAt at *
  change (s.sum (fun H => centeredQuery M H j ^ 2)) / s.card = _
  rw [hexpand]
  have hraw1' : (s.sum (fun H => (queryCount H j : ℝ))) / s.card = m := hmean
  have hraw2' : (s.sum (fun H => (queryCount H j : ℝ) ^ 2)) / s.card =
      conditionalQueryRawMoment M G j 2 := hraw2
  rw [hmean']
  field_simp at hraw1' hraw2' ⊢
  rw [hraw1', hraw2']
  ring

private theorem history_centered_third_le {n M J : ℕ}
    (hfinite : FiniteEnumerationStatement) (hM : M ≤ capacity n)
    (G : Graph n) (j : ℕ) (hG : G.card = M)
    (hbudget : HorizonBudget n M J 8) (hj : j < J) :
    historyAverage M G j (fun H => |centeredQuery M H j| ^ 3) ≤ C3 := by
  let s := historyAtom M G j
  let m := queryMean M G j
  have hcard : (0 : ℝ) < s.card := by
    exact_mod_cast (Finset.card_pos.mpr (historyAtom_nonempty G j hG))
  have hmean0 : 0 ≤ m := by unfold m queryMean poolDensity; positivity
  have hmean4 : m ≤ 4 := by
    have hh := (historyAtom_horizon_moments hfinite hM G j hG hbudget hj).1
    rwa [history_mean_eq_queryMean hfinite hM G j hG] at hh
  have hfour := (historyAtom_horizon_moments hfinite hM G j hG hbudget hj).2.2.2
  have htrace : ∀ H ∈ s, queryMean M H j = m := by
    intro H hH
    exact queryMean_eq_of_trace G H j (Finset.mem_filter.mp hH).2
  have hpoint : ∀ H ∈ s,
      |centeredQuery M H j| ^ 3 ≤
        1 + 8 * ((queryCount H j : ℝ) ^ 4 + 4 ^ 4) := by
    intro H hH
    have hq : (0 : ℝ) ≤ queryCount H j := Nat.cast_nonneg _
    have hdm := centered_fourth_point (queryCount H j : ℝ) m hq hmean0
    have hm4 : m ^ 4 ≤ (4 : ℝ) ^ 4 := by gcongr
    unfold centeredQuery
    rw [htrace H hH]
    calc
      |(queryCount H j : ℝ) - m| ^ 3 ≤
          1 + |(queryCount H j : ℝ) - m| ^ 4 := cube_le_fourth _
      _ ≤ 1 + 8 * ((queryCount H j : ℝ) ^ 4 + 4 ^ 4) := by
        nlinarith [hdm, hm4]
  have hsum := Finset.sum_le_sum hpoint
  unfold historyAverage at hfour ⊢
  have hfour' : s.sum (fun H => (queryCount H j : ℝ) ^ 4) ≤
      C4 * (s.card : ℝ) := by
    apply (div_le_iff₀ hcard).mp
    simpa [C4, s] using! hfour
  apply (div_le_iff₀ hcard).mpr
  calc
    s.sum (fun H => |centeredQuery M H j| ^ 3) ≤
        s.sum (fun H => 1 + 8 * ((queryCount H j : ℝ) ^ 4 + 4 ^ 4)) := hsum
    _ ≤ C3 * (s.card : ℝ) := by
      have heq : s.sum (fun H => 1 + 8 *
          ((queryCount H j : ℝ) ^ 4 + 4 ^ 4)) =
          (s.card : ℝ) + 8 *
            (s.sum (fun H => (queryCount H j : ℝ) ^ 4) +
              (s.card : ℝ) * 4 ^ 4) := by
        simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
          ← Finset.mul_sum]
        ring
      rw [heq]
      dsimp [C3]
      nlinarith [hfour']

private theorem complexHistoryAverage_ofReal {n M : ℕ}
    (G : Graph n) (j : ℕ) (f : Graph n → ℝ) :
    complexHistoryAverage M G j (fun H => (f H : ℂ)) =
      (historyAverage M G j f : ℂ) := by
  unfold complexHistoryAverage historyAverage
  push_cast
  rfl

private theorem complexHistoryAverage_const {n M : ℕ}
    (G : Graph n) (j : ℕ) (hG : G.card = M) (c : ℂ) :
    complexHistoryAverage M G j (fun _ => c) = c := by
  unfold complexHistoryAverage
  have hne : ((historyAtom M G j).card : ℂ) ≠ 0 := by
    exact_mod_cast (Finset.card_ne_zero.mpr (historyAtom_nonempty G j hG))
  simp [hne]

private theorem complexHistoryAverage_add {n M : ℕ}
    (G : Graph n) (j : ℕ) (f g : Graph n → ℂ) :
    complexHistoryAverage M G j (fun H => f H + g H) =
      complexHistoryAverage M G j f + complexHistoryAverage M G j g := by
  unfold complexHistoryAverage
  rw [Finset.sum_add_distrib, add_div]

private theorem complexHistoryAverage_sub {n M : ℕ}
    (G : Graph n) (j : ℕ) (f g : Graph n → ℂ) :
    complexHistoryAverage M G j (fun H => f H - g H) =
      complexHistoryAverage M G j f - complexHistoryAverage M G j g := by
  unfold complexHistoryAverage
  rw [Finset.sum_sub_distrib, sub_div]

private theorem complexHistoryAverage_mul_const {n M : ℕ}
    (G : Graph n) (j : ℕ) (f : Graph n → ℂ) (c : ℂ) :
    complexHistoryAverage M G j (fun H => c * f H) =
      c * complexHistoryAverage M G j f := by
  unfold complexHistoryAverage
  rw [← Finset.mul_sum]
  ring

private theorem history_centered_zero {n M : ℕ}
    (hfinite : FiniteEnumerationStatement) (hM : M ≤ capacity n)
    (G : Graph n) (j : ℕ) (hG : G.card = M) :
    historyAverage M G j (fun H => centeredQuery M H j) = 0 := by
  have htrace : ∀ H ∈ historyAtom M G j,
      queryMean M H j = queryMean M G j := by
    intro H hH
    exact queryMean_eq_of_trace G H j (Finset.mem_filter.mp hH).2
  have hz := historyAverage_centeredQuery_zero hfinite hM G j hG
  unfold historyAverage at hz ⊢
  have hs : (historyAtom M G j).sum (fun H => centeredQuery M H j) =
      (historyAtom M G j).sum (fun H =>
        (queryCount H j : ℝ) - queryMean M G j) := by
    apply Finset.sum_congr rfl
    intro H hH
    unfold centeredQuery
    rw [htrace H hH]
  rw [hs]
  exact hz

private theorem complexHistoryAverage_norm_le {n M : ℕ}
    (G : Graph n) (j : ℕ) (hG : G.card = M)
    (f : Graph n → ℂ) :
    ‖complexHistoryAverage M G j f‖ ≤
      historyAverage M G j (fun H => ‖f H‖) := by
  have hcard : (0 : ℝ) < (historyAtom M G j).card := by
    exact_mod_cast (Finset.card_pos.mpr (historyAtom_nonempty G j hG))
  unfold complexHistoryAverage historyAverage
  rw [norm_div, Complex.norm_natCast]
  exact div_le_div_of_nonneg_right
    (norm_sum_le (historyAtom M G j) f) hcard.le

/-- The random conditional coefficient has the second-order expansion
with a uniform cubic moment remainder on every positive realized atom. -/
theorem conditionalCoefficient_taylor {n M J : ℕ}
    (hfinite : FiniteEnumerationStatement) (hM : M ≤ capacity n)
    (hbudget : HorizonBudget n M J 8) (G : Graph n)
    (hG : G.card = M) (j : ℕ) (hj : j < J)
    (theta : ℕ → ℝ) (b : ℝ) (hb : 0 < b) :
    ‖conditionalCoefficient M theta b G j -
        ((1 - theta j ^ 2 * varianceAt M G j / (2 * b ^ 2) : ℝ) : ℂ)‖ ≤
      4 * C3 * |theta j| ^ 3 / b ^ 3 := by
  let u : Graph n → ℝ := fun H => theta j * centeredQuery M H j / b
  let r : Graph n → ℂ := fun H =>
    Complex.exp (Complex.I * (u H : ℂ)) -
      (1 + Complex.I * (u H : ℂ) - ((u H ^ 2 / 2 : ℝ) : ℂ))
  have hzero := history_centered_zero hfinite hM G j hG
  have hsquare := history_centered_square hfinite hM G j hG
  have huZero : complexHistoryAverage M G j (fun H =>
      Complex.I * (u H : ℂ)) = 0 := by
    rw [complexHistoryAverage_mul_const,
      complexHistoryAverage_ofReal]
    have heq : historyAverage M G j u =
        theta j / b * historyAverage M G j
          (fun H => centeredQuery M H j) := by
      unfold historyAverage u
      have hfac : ∀ H : Graph n,
          theta j * centeredQuery M H j / b =
            (theta j / b) * centeredQuery M H j := by intro H; ring
      simp_rw [hfac]
      rw [← Finset.mul_sum]
      ring
    rw [heq, hzero]
    simp
  have huSquare : complexHistoryAverage M G j (fun H =>
      ((u H ^ 2 / 2 : ℝ) : ℂ)) =
      ((theta j ^ 2 * varianceAt M G j / (2 * b ^ 2) : ℝ) : ℂ) := by
    rw [complexHistoryAverage_ofReal]
    have heq : historyAverage M G j (fun H => u H ^ 2 / 2) =
        theta j ^ 2 / (2 * b ^ 2) *
          historyAverage M G j (fun H => centeredQuery M H j ^ 2) := by
      unfold historyAverage u
      have hfac : ∀ H : Graph n,
          (theta j * centeredQuery M H j / b) ^ 2 / 2 =
            (theta j ^ 2 / (2 * b ^ 2)) * centeredQuery M H j ^ 2 := by
        intro H
        field_simp
      simp_rw [hfac]
      rw [← Finset.mul_sum]
      ring
    rw [heq, hsquare]
    push_cast
    ring
  have hidentity : conditionalCoefficient M theta b G j -
      ((1 - theta j ^ 2 * varianceAt M G j / (2 * b ^ 2) : ℝ) : ℂ) =
        complexHistoryAverage M G j r := by
    have hconst := complexHistoryAverage_const G j hG (1 : ℂ)
    unfold r
    rw [complexHistoryAverage_sub, complexHistoryAverage_sub,
      complexHistoryAverage_add, hconst, huZero, huSquare]
    unfold conditionalCoefficient
    push_cast
    unfold complexHistoryAverage
    have hsum : (∑ H ∈ historyAtom M G j,
        Complex.exp (Complex.I *
          ((theta j : ℂ) * (centeredQuery M H j : ℂ) / (b : ℂ)))) =
        ∑ H ∈ historyAtom M G j,
          Complex.exp (Complex.I * (u H : ℂ)) := by
      apply Finset.sum_congr rfl
      intro H hH
      dsimp [u]
      congr 1
      push_cast
      ring
    rw [hsum]
    ring
  rw [hidentity]
  calc
    ‖complexHistoryAverage M G j r‖ ≤
        historyAverage M G j (fun H => ‖r H‖) :=
          complexHistoryAverage_norm_le G j hG r
    _ ≤ historyAverage M G j (fun H => 4 * |u H| ^ 3) := by
      unfold historyAverage
      apply div_le_div_of_nonneg_right
        (Finset.sum_le_sum (fun H hH => imaginary_exp_taylor (u H)))
        (Nat.cast_nonneg _)
    _ ≤ 4 * C3 * |theta j| ^ 3 / b ^ 3 := by
      have hthird := history_centered_third_le hfinite hM G j hG hbudget hj
      have hfactor : ∀ H : Graph n,
          4 * |u H| ^ 3 =
            (4 * |theta j| ^ 3 / b ^ 3) * |centeredQuery M H j| ^ 3 := by
        intro H
        dsimp [u]
        rw [abs_div, abs_mul, abs_of_pos hb]
        ring
      simp_rw [hfactor]
      unfold historyAverage at *
      rw [← Finset.mul_sum]
      have hfac : 0 ≤ 4 * |theta j| ^ 3 / b ^ 3 := by positivity
      have hh := mul_le_mul_of_nonneg_left hthird hfac
      convert hh using 1 <;> ring

private theorem gaussian_linear_error (x : ℝ) (hx : 0 ≤ x)
    (hsmall : x ≤ 1) : |Real.exp (-x) - (1 - x)| ≤ x ^ 2 := by
  have h := Real.norm_exp_sub_one_sub_id_le (x := -x) (by
    rw [Real.norm_eq_abs, abs_neg, abs_of_nonneg hx]
    exact hsmall)
  have h' : |Real.exp (-x) - 1 + x| ≤ x ^ 2 := by
    have hs : ‖Real.exp (-x) - 1 - -x‖ =
        |Real.exp (-x) - 1 + x| := by
      rw [Real.norm_eq_abs]
      congr 1
      ring
    rw [hs] at h
    simpa [Real.norm_eq_abs, abs_of_nonneg hx] using! h
  convert h' using 1
  congr 1
  ring

theorem conditionalCoefficient_gaussian_error {n M J : ℕ}
    (hfinite : FiniteEnumerationStatement) (hM : M ≤ capacity n)
    (hbudget : HorizonBudget n M J 8) (G : Graph n)
    (hG : G.card = M) (j : ℕ) (hj : j < J)
    (theta : ℕ → ℝ) (b : ℝ) (hb : 0 < b)
    (hsmall : theta j ^ 2 / (2 * b ^ 2) ≤ 1) :
    ‖conditionalCoefficient M theta b G j - gaussianCoefficient theta b j‖ ≤
      theta j ^ 2 / (2 * b ^ 2) * |varianceAt M G j - 1| +
        4 * C3 * |theta j| ^ 3 / b ^ 3 +
        theta j ^ 4 / (4 * b ^ 4) := by
  have ht := conditionalCoefficient_taylor hfinite hM hbudget G hG j hj
    theta b hb
  let x : ℝ := theta j ^ 2 / (2 * b ^ 2)
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have he := gaussian_linear_error x hx hsmall
  have hgauss : gaussianCoefficient theta b j =
      ((Real.exp (-x) : ℝ) : ℂ) := by
    unfold gaussianCoefficient
    rw [← Complex.ofReal_exp]
  have hnorm : ‖(((1 - x * varianceAt M G j : ℝ) : ℂ) -
      gaussianCoefficient theta b j)‖ ≤
      x * |varianceAt M G j - 1| + x ^ 2 := by
    rw [hgauss, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    have hid : 1 - x * varianceAt M G j - Real.exp (-x) =
        -(x * (varianceAt M G j - 1)) - (Real.exp (-x) - (1 - x)) := by ring
    rw [hid]
    calc
      _ ≤ |-(x * (varianceAt M G j - 1))| +
          |Real.exp (-x) - (1 - x)| := abs_sub _ _
      _ ≤ x * |varianceAt M G j - 1| + x ^ 2 := by
        rw [abs_neg, abs_mul, abs_of_nonneg hx]
        linarith
  have htri : ‖conditionalCoefficient M theta b G j -
      gaussianCoefficient theta b j‖ ≤
      ‖conditionalCoefficient M theta b G j -
        ((1 - x * varianceAt M G j : ℝ) : ℂ)‖ +
      ‖((1 - x * varianceAt M G j : ℝ) : ℂ) -
        gaussianCoefficient theta b j‖ := by
    have heq : conditionalCoefficient M theta b G j -
        gaussianCoefficient theta b j =
        (conditionalCoefficient M theta b G j -
          ((1 - x * varianceAt M G j : ℝ) : ℂ)) +
        (((1 - x * varianceAt M G j : ℝ) : ℂ) -
          gaussianCoefficient theta b j) := by ring
    rw [heq]
    exact norm_add_le _ _
  have hx2 : x ^ 2 = theta j ^ 4 / (4 * b ^ 4) := by
    dsimp [x]
    ring
  have hcast : ((1 - theta j ^ 2 * varianceAt M G j /
      (2 * b ^ 2) : ℝ) : ℂ) =
      ((1 - theta j ^ 2 / (2 * b ^ 2) * varianceAt M G j : ℝ) : ℂ) := by
    congr 1
    ring
  rw [hcast] at ht
  dsimp [x] at hnorm htri
  nlinarith [ht, hnorm, htri, hx2]

private theorem complexExpect_norm_le {n M : ℕ}
    (hM : M ≤ capacity n) (f : Graph n → ℂ) :
    ‖complexExpectM n M f‖ ≤ expectM n M (fun G => ‖f G‖) := by
  have hcard : (0 : ℝ) < ((fixedGraphs n M).card : ℝ) := by
    exact_mod_cast (Finset.card_pos.mpr (fixedGraphs_nonempty hM))
  unfold complexExpectM expectM
  rw [norm_div, Complex.norm_natCast]
  exact div_le_div_of_nonneg_right (norm_sum_le (fixedGraphs n M) f) hcard.le

private theorem expectM_mono {n M : ℕ} (f g : Graph n → ℝ)
    (h : ∀ G ∈ fixedGraphs n M, f G ≤ g G) :
    expectM n M f ≤ expectM n M g := by
  unfold expectM
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum h) (Nat.cast_nonneg _)

private theorem expectM_const {n M : ℕ} (hM : M ≤ capacity n)
    (c : ℝ) : expectM n M (fun _ => c) = c := by
  unfold expectM
  have hne : ((fixedGraphs n M).card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_ne_zero.mpr (fixedGraphs_nonempty hM))
  simp [hne]

private theorem expectM_add {n M : ℕ} (f g : Graph n → ℝ) :
    expectM n M (fun G => f G + g G) =
      expectM n M f + expectM n M g := by
  unfold expectM
  rw [Finset.sum_add_distrib, add_div]

private theorem expectM_mul_const {n M : ℕ} (c : ℝ)
    (f : Graph n → ℝ) :
    expectM n M (fun G => c * f G) = c * expectM n M f := by
  unfold expectM
  rw [← Finset.mul_sum]
  ring

private theorem step_error_bound {n M J : ℕ}
    (hfinite : FiniteEnumerationStatement) (hM : M ≤ capacity n)
    (hbudget : HorizonBudget n M J 8)
    (theta : ℕ → ℝ) (b L : ℝ) (hb : 0 < b) (hL : 0 ≤ L)
    (hθ : ∀ j < J, |theta j| ≤ L)
    (hsmall : L ^ 2 / (2 * b ^ 2) ≤ 1)
    (j : ℕ) (hj : j < J) :
    ‖complexExpectM n M (fun G : Graph n =>
        Complex.exp (Complex.I * (stepSum M G theta b j : ℂ)) *
          (conditionalCoefficient M theta b G j -
            gaussianCoefficient theta b j))‖ ≤
      L ^ 2 / (2 * b ^ 2) *
        expectM n M (fun G => varianceErrorMax M G J) +
      4 * C3 * L ^ 3 / b ^ 3 + L ^ 4 / (4 * b ^ 4) := by
  have hθj := hθ j hj
  have hθ2 : theta j ^ 2 ≤ L ^ 2 := by
    calc
      theta j ^ 2 = |theta j| ^ 2 := by rw [sq_abs]
      _ ≤ L ^ 2 := by gcongr
  have hθ3 : |theta j| ^ 3 ≤ L ^ 3 := by gcongr
  have hC3 : 0 ≤ C3 := by unfold C3 C4; norm_num
  have hθ4 : theta j ^ 4 ≤ L ^ 4 := by
    calc
      theta j ^ 4 = |theta j| ^ 4 := by
        calc
          theta j ^ 4 = (theta j ^ 2) ^ 2 := by ring
          _ = (|theta j| ^ 2) ^ 2 := by rw [sq_abs]
          _ = |theta j| ^ 4 := by ring
      _ ≤ L ^ 4 := by gcongr
  have hb2 : 0 < 2 * b ^ 2 := by positivity
  have hsmallj : theta j ^ 2 / (2 * b ^ 2) ≤ 1 :=
    (div_le_div_of_nonneg_right hθ2 hb2.le).trans hsmall
  have hpoint : ∀ G ∈ fixedGraphs n M,
      ‖Complex.exp (Complex.I * (stepSum M G theta b j : ℂ)) *
          (conditionalCoefficient M theta b G j -
            gaussianCoefficient theta b j)‖ ≤
        L ^ 2 / (2 * b ^ 2) * varianceErrorMax M G J +
          4 * C3 * L ^ 3 / b ^ 3 + L ^ 4 / (4 * b ^ 4) := by
    intro G hG
    have hGc : G.card = M := (Finset.mem_filter.mp hG).2
    have hTaylor := conditionalCoefficient_gaussian_error hfinite hM
      hbudget G hGc j hj theta b hb hsmallj
    have hvar := varianceError_le_max (M := M) G hj
    have hmax0 : 0 ≤ varianceErrorMax M G J := by
      unfold varianceErrorMax
      have hh := Finset.le_sup'
        (s := Finset.range (J + 1))
        (f := fun i => if i < J then |varianceAt M G i - 1| else 0)
        (Finset.mem_range.mpr (by omega : J < J + 1))
      simpa using! hh
    rw [norm_mul, complex_unit_exp, one_mul]
    have hfac : 0 ≤ theta j ^ 2 / (2 * b ^ 2) := by positivity
    have hle1 := mul_le_mul_of_nonneg_left hvar hfac
    have hle2 := mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right hθ2 hb2.le) hmax0
    have hle3 := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hθ3 (by positivity : 0 ≤ 4 * C3))
      (pow_nonneg hb.le 3)
    have hle4 := div_le_div_of_nonneg_right hθ4 (by positivity : 0 ≤ 4 * b ^ 4)
    linarith
  calc
    _ ≤ expectM n M (fun G =>
        ‖Complex.exp (Complex.I * (stepSum M G theta b j : ℂ)) *
          (conditionalCoefficient M theta b G j -
            gaussianCoefficient theta b j)‖) := complexExpect_norm_le hM _
    _ ≤ expectM n M (fun G =>
        L ^ 2 / (2 * b ^ 2) * varianceErrorMax M G J +
          4 * C3 * L ^ 3 / b ^ 3 + L ^ 4 / (4 * b ^ 4)) :=
            expectM_mono _ _ hpoint
    _ = _ := by
      simp only [expectM_add, expectM_mul_const, expectM_const hM]

theorem finite_characteristic_error {n M J : ℕ}
    (hfinite : FiniteEnumerationStatement) (hM : M ≤ capacity n)
    (hbudget : HorizonBudget n M J 8)
    (theta : ℕ → ℝ) (b L : ℝ) (hb : 0 < b) (hL : 0 ≤ L)
    (hθ : ∀ j < J, |theta j| ≤ L)
    (hsmall : L ^ 2 / (2 * b ^ 2) ≤ 1) :
    ‖stepAlpha n M theta b J -
      Complex.exp ((-(∑ j ∈ Finset.range J,
        theta j ^ 2 / (2 * b ^ 2)) : ℝ) : ℂ)‖ ≤
      (J : ℝ) *
        (L ^ 2 / (2 * b ^ 2) *
          expectM n M (fun G => varianceErrorMax M G J) +
          4 * C3 * L ^ 3 / b ^ 3 + L ^ 4 / (4 * b ^ 4)) := by
  let err : ℕ → ℂ := fun j => complexExpectM n M (fun G =>
    Complex.exp (Complex.I * (stepSum M G theta b j : ℂ)) *
      (conditionalCoefficient M theta b G j -
        gaussianCoefficient theta b j))
  have ht := characteristic_telescope
    (stepAlpha n M theta b) (gaussianCoefficient theta b)
    err J (stepAlpha_zero hM theta b)
    (fun j hj => stepAlpha_recursion hM theta b j)
    (fun j hj => gaussianCoefficient_norm_le theta b j)
  have hprod : (∏ j ∈ Finset.range J, gaussianCoefficient theta b j) =
      Complex.exp ((-(∑ j ∈ Finset.range J,
        theta j ^ 2 / (2 * b ^ 2)) : ℝ) : ℂ) := by
    simp only [gaussianCoefficient]
    rw [← Complex.exp_sum]
    congr 1
    push_cast
    rw [Finset.sum_neg_distrib]
  rw [hprod] at ht
  have hsum : (∑ j ∈ Finset.range J, ‖err j‖) ≤
      (J : ℝ) *
        (L ^ 2 / (2 * b ^ 2) *
          expectM n M (fun G => varianceErrorMax M G J) +
          4 * C3 * L ^ 3 / b ^ 3 + L ^ 4 / (4 * b ^ 4)) := by
    calc
      _ ≤ ∑ _j ∈ Finset.range J,
          (L ^ 2 / (2 * b ^ 2) *
            expectM n M (fun G => varianceErrorMax M G J) +
            4 * C3 * L ^ 3 / b ^ 3 + L ^ 4 / (4 * b ^ 4)) := by
              apply Finset.sum_le_sum
              intro j hj
              exact step_error_bound hfinite hM hbudget theta b L hb hL
                hθ hsmall j (Finset.mem_range.mp hj)
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  exact ht.trans hsum

private theorem n23_tendsto_atTop : Tendsto n23 atTop atTop := by
  exact (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 3)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))

private theorem mesh_ratio_tendsto (T : ℝ) (hT : 0 ≤ T) :
    Tendsto (fun n : ℕ => (meshIndex n T : ℝ) / n23 n)
      atTop (𝓝 T) := by
  exact (tendsto_nat_floor_mul_div_atTop hT).comp n23_tendsto_atTop

private theorem mesh_ratio_b_tendsto (T : ℝ) (hT : 0 ≤ T) :
    Tendsto (fun n : ℕ => (meshIndex n T : ℝ) / n13 n ^ 2)
      atTop (𝓝 T) := by
  have heq : (fun n : ℕ => (meshIndex n T : ℝ) / n23 n) =ᶠ[atTop]
      (fun n : ℕ => (meshIndex n T : ℝ) / n13 n ^ 2) := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    rw [n23_eq_n13_square n hn]
  exact (mesh_ratio_tendsto T hT).congr' heq

/-- The characteristic telescope for deterministic bounded step weights.
The only stochastic error is exactly the B03V L1 variance maximum. -/
theorem critical_step_characteristic
    (hfinite : FiniteEnumerationStatement) (M : NatSeq) (lam T L V : ℝ)
    (hcritical : criticalWindow M lam) (hT : 0 ≤ T) (hL : 0 ≤ L)
    (theta : ℕ → ℕ → ℝ)
    (hθ : ∀ n j, |theta n j| ≤ L)
    (hvariance : Tendsto (fun n =>
      ∑ j ∈ Finset.range (meshIndex n T),
        theta n j ^ 2 / n23 n) atTop (𝓝 V)) :
    Tendsto (fun n => stepAlpha n (M n) (theta n) (n13 n)
      (meshIndex n T)) atTop
      (𝓝 (Complex.exp ((-V / 2 : ℝ) : ℂ))) := by
  let J : ℕ → ℕ := fun n => meshIndex n T
  let b : ℕ → ℝ := n13
  let E : ℕ → ℝ := fun n => expectM n (M n)
    (fun G => varianceErrorMax (M n) G (J n))
  have hE : Tendsto E atTop (𝓝 0) := by
    simpa only [E, J, meshIndex] using!
      critical_variance_L1 hfinite M lam T hcritical hT
  have hJ : Tendsto (fun n => (J n : ℝ) / b n ^ 2)
      atTop (𝓝 T) := by
    simpa only [J, b] using! mesh_ratio_b_tendsto T hT
  have hbinv : Tendsto (fun n => (b n)⁻¹) atTop (𝓝 0) := by
    simpa only [b] using!
      tendsto_inv_atTop_zero.comp n13_tendsto_atTop
  have hbinv2 : Tendsto (fun n => (b n)⁻¹ ^ 2) atTop (𝓝 0) := by
    simpa using! hbinv.pow 2
  have hterms : Tendsto (fun n =>
      ((J n : ℝ) / b n ^ 2) *
        ((L ^ 2 / 2) * E n +
          (4 * C3 * L ^ 3) * (b n)⁻¹ +
          (L ^ 4 / 4) * (b n)⁻¹ ^ 2)) atTop (𝓝 0) := by
    have hinside : Tendsto (fun n =>
        (L ^ 2 / 2) * E n +
          (4 * C3 * L ^ 3) * (b n)⁻¹ +
          (L ^ 4 / 4) * (b n)⁻¹ ^ 2) atTop (𝓝 0) := by
      convert ((hE.const_mul (L ^ 2 / 2)).add
        (hbinv.const_mul (4 * C3 * L ^ 3))).add
        (hbinv2.const_mul (L ^ 4 / 4)) using 1 <;> ring
    simpa using! hJ.mul hinside
  have herror : Tendsto (fun n =>
      ‖stepAlpha n (M n) (theta n) (b n) (J n) -
        Complex.exp ((-(∑ j ∈ Finset.range (J n),
          theta n j ^ 2 / (2 * b n ^ 2)) : ℝ) : ℂ)‖)
      atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hterms
    · exact Filter.Eventually.of_forall (fun n => norm_nonneg _)
    · filter_upwards [hcritical.1,
        eventually_horizonBudget M lam T hcritical hT,
        n13_tendsto_atTop.eventually_ge_atTop (max 1 L),
        eventually_ge_atTop (1 : ℕ)] with n hM hbudget hb hn
      have hbpos : 0 < b n := by
        have hh : 1 ≤ b n := le_trans (le_max_left _ _) hb
        linarith
      have hsmall : L ^ 2 / (2 * (b n) ^ 2) ≤ 1 := by
        have hLb : L ≤ b n := le_trans (le_max_right _ _) hb
        have hsq : L ^ 2 ≤ (b n) ^ 2 := by gcongr
        apply (div_le_iff₀ (by positivity : 0 < 2 * (b n) ^ 2)).mpr
        nlinarith [sq_nonneg (b n)]
      have hfinite := finite_characteristic_error hfinite hM hbudget
        (theta n) (b n) L hbpos hL (fun j hj => hθ n j) hsmall
      have heq : (J n : ℝ) *
          (L ^ 2 / (2 * (b n) ^ 2) * E n +
            4 * C3 * L ^ 3 / (b n) ^ 3 +
            L ^ 4 / (4 * (b n) ^ 4)) =
          ((J n : ℝ) / (b n) ^ 2) *
          ((L ^ 2 / 2) * E n +
            (4 * C3 * L ^ 3) * (b n)⁻¹ +
            (L ^ 4 / 4) * (b n)⁻¹ ^ 2) := by
        field_simp
      simpa only [J, b, E] using! hfinite.trans_eq heq
  have hgaussian : Tendsto (fun n =>
      Complex.exp ((-(∑ j ∈ Finset.range (J n),
        theta n j ^ 2 / (2 * b n ^ 2)) : ℝ) : ℂ))
      atTop (𝓝 (Complex.exp ((-V / 2 : ℝ) : ℂ))) := by
    have heq : (fun n =>
        -(∑ j ∈ Finset.range (J n), theta n j ^ 2 / (2 * b n ^ 2))) =ᶠ[atTop]
        (fun n => -(∑ j ∈ Finset.range (J n),
          theta n j ^ 2 / n23 n) / 2) := by
      filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
      rw [n23_eq_n13_square n hn]
      have hterm (j : ℕ) :
          theta n j ^ 2 / (2 * b n ^ 2) =
            (theta n j ^ 2 / b n ^ 2) / 2 := by ring
      simp_rw [hterm]
      have hsum : (∑ j ∈ Finset.range (J n),
          theta n j ^ 2 / b n ^ 2 / 2) =
          (∑ j ∈ Finset.range (J n), theta n j ^ 2 / b n ^ 2) / 2 := by
        rw [Finset.sum_div]
      rw [hsum]
      ring
    have hmain : Tendsto (fun n =>
        -(∑ j ∈ Finset.range (J n),
          theta n j ^ 2 / n23 n) / 2) atTop (𝓝 (-V / 2)) := by
      simpa using! (hvariance.neg.div_const 2)
    have hreal := hmain.congr' heq.symm
    exact (Complex.continuous_exp.tendsto _).comp
      (Complex.continuous_ofReal.tendsto _ |>.comp hreal)
  have hdiff : Tendsto (fun n =>
      stepAlpha n (M n) (theta n) (b n) (J n) -
      Complex.exp ((-(∑ j ∈ Finset.range (J n),
        theta n j ^ 2 / (2 * b n ^ 2)) : ℝ) : ℂ))
      atTop (𝓝 0) := by
    exact (tendsto_iff_norm_sub_tendsto_zero).2 (by simpa using! herror)
  have hsum := hdiff.add hgaussian
  simpa only [zero_add, sub_add_cancel] using! hsum

private theorem indicator_count (J k : ℕ) :
    (∑ j ∈ Finset.range J, if j < k then (1 : ℝ) else 0) =
      (min J k : ℝ) := by
  induction J with
  | zero => simp
  | succ J ih =>
      rw [Finset.sum_range_succ, ih]
      by_cases h : J < k
      · have hmin : min (J + 1) k = min J k + 1 := by omega
        simp only [if_pos h]
        exact_mod_cast hmin.symm
      · have hmin : min (J + 1) k = min J k := by omega
        simp only [if_neg h, add_zero]
        exact_mod_cast hmin.symm

private theorem indicator_pair_sum (J k l : ℕ) (x y : ℝ)
    (hk : k ≤ J) (hl : l ≤ J) :
    (∑ j ∈ Finset.range J,
      (if j < k then x else 0) * (if j < l then y else 0)) =
        (min k l : ℝ) * x * y := by
  have hpoint : ∀ j,
      (if j < k then x else 0) * (if j < l then y else 0) =
        (if j < min k l then (1 : ℝ) else 0) * x * y := by
    intro j
    by_cases h₁ : j < k <;> by_cases h₂ : j < l <;>
      simp [h₁, h₂, Nat.lt_min]
  simp_rw [hpoint]
  rw [← Finset.sum_mul, ← Finset.sum_mul, indicator_count]
  have hmin : min J (min k l) = min k l := by omega
  have hreal : min (J : ℝ) ((min k l : ℕ) : ℝ) =
      (min k l : ℝ) := by exact_mod_cast hmin
  have hreal' : (min k l : ℝ) = min (k : ℝ) (l : ℝ) := by norm_cast
  rw [hreal, hreal']

private theorem step_variance_exact {m n J : ℕ}
    (t z : Fin m → ℝ)
    (hJ : ∀ i : Fin m, meshIndex n (t i) ≤ J) :
    (∑ j ∈ Finset.range J, stepCoefficient n t z j ^ 2) =
      ∑ i : Fin m, ∑ l : Fin m,
        (min (meshIndex n (t i)) (meshIndex n (t l)) : ℝ) * z i * z l := by
  unfold stepCoefficient
  calc
    (∑ j ∈ Finset.range J,
        (∑ i : Fin m, if j < meshIndex n (t i) then z i else 0) ^ 2) =
      ∑ j ∈ Finset.range J, ∑ i : Fin m, ∑ l : Fin m,
        (if j < meshIndex n (t i) then z i else 0) *
          (if j < meshIndex n (t l) then z l else 0) := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [pow_two, Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro i hi
            rw [Finset.mul_sum]
    _ = ∑ i : Fin m, ∑ l : Fin m, ∑ j ∈ Finset.range J,
        (if j < meshIndex n (t i) then z i else 0) *
          (if j < meshIndex n (t l) then z l else 0) := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro i hi
            rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro l hl
      exact indicator_pair_sum J _ _ (z i) (z l) (hJ i) (hJ l)

private theorem meshIndex_mono {n : ℕ} {s t : ℝ}
    (hst : s ≤ t) : meshIndex n s ≤ meshIndex n t := by
  unfold meshIndex
  apply Nat.floor_mono
  exact mul_le_mul_of_nonneg_right hst (Real.rpow_nonneg (Nat.cast_nonneg n) _)

private theorem mesh_min (n : ℕ) (s t : ℝ) :
    min (meshIndex n s) (meshIndex n t) = meshIndex n (min s t) := by
  rcases le_total s t with h | h
  · rw [min_eq_left h, min_eq_left (meshIndex_mono h)]
  · rw [min_eq_right h, min_eq_right (meshIndex_mono h)]

private theorem step_variance_tendsto {m : ℕ}
    (T : ℝ) (hT : 0 ≤ T) (t z : Fin m → ℝ)
    (ht0 : ∀ i, 0 ≤ t i) (htT : ∀ i, t i ≤ T) :
    Tendsto (fun n : ℕ =>
      ∑ j ∈ Finset.range (meshIndex n T),
        stepCoefficient n t z j ^ 2 / n23 n)
      atTop (𝓝 (∑ i : Fin m, ∑ l : Fin m,
        min (t i) (t l) * z i * z l)) := by
  have hJ (n : ℕ) (i : Fin m) :
      meshIndex n (t i) ≤ meshIndex n T := meshIndex_mono (htT i)
  have heq (n : ℕ) :
      (∑ j ∈ Finset.range (meshIndex n T),
        stepCoefficient n t z j ^ 2 / n23 n) =
      ∑ i : Fin m, ∑ l : Fin m,
        ((meshIndex n (min (t i) (t l)) : ℝ) / n23 n) * z i * z l := by
    rw [← Finset.sum_div, step_variance_exact t z (hJ n)]
    conv_lhs => rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i hi
    conv_lhs => rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro l hl
    have hcast : min ((meshIndex n (t i) : ℕ) : ℝ)
        ((meshIndex n (t l) : ℕ) : ℝ) =
        ((meshIndex n (min (t i) (t l)) : ℕ) : ℝ) := by
      exact_mod_cast mesh_min n (t i) (t l)
    rw [hcast]
    ring
  have hpoint (i l : Fin m) : Tendsto (fun n : ℕ =>
      ((meshIndex n (min (t i) (t l)) : ℝ) / n23 n) * z i * z l)
      atTop (𝓝 (min (t i) (t l) * z i * z l)) := by
    have hm : 0 ≤ min (t i) (t l) := le_min (ht0 i) (ht0 l)
    simpa using! ((mesh_ratio_tendsto _ hm).mul_const (z i)).mul_const (z l)
  have hlim : Tendsto (fun n =>
      ∑ i : Fin m, ∑ l : Fin m,
        ((meshIndex n (min (t i) (t l)) : ℝ) / n23 n) * z i * z l)
      atTop (𝓝 (∑ i : Fin m, ∑ l : Fin m,
        min (t i) (t l) * z i * z l)) := by
    apply tendsto_finset_sum
    intro i hi
    apply tendsto_finset_sum
    intro l hl
    exact hpoint i l
  exact hlim.congr' (Filter.Eventually.of_forall (fun n => (heq n).symm))

/-- B04's vector boundary.  Repeated observation times and zero times are
included directly: their deterministic step coefficients combine in the same
finite sum.  B05 may apply this characteristic limit to any real test vector
of the scaled centered mesh values. -/
theorem critical_centered_vector_characteristic
    (hfinite : FiniteEnumerationStatement) (M : NatSeq) (lam T : ℝ)
    (hcritical : criticalWindow M lam) (hT : 0 ≤ T)
    {m : ℕ} (t z : Fin m → ℝ)
    (ht0 : ∀ i, 0 ≤ t i) (htT : ∀ i, t i ≤ T) :
    Tendsto (fun n => complexExpectM n (M n) (fun G =>
      Complex.exp (Complex.I *
        (((∑ i : Fin m, z i *
          centeredPartial (M n) G (meshIndex n (t i))) /
            n13 n : ℝ) : ℂ)))) atTop
      (𝓝 (Complex.exp ((-(∑ i : Fin m, ∑ l : Fin m,
        min (t i) (t l) * z i * z l) / 2 : ℝ) : ℂ))) := by
  let L : ℝ := ∑ i : Fin m, |z i|
  have hL : 0 ≤ L := Finset.sum_nonneg (fun i hi => abs_nonneg _)
  have hθ (n j : ℕ) : |stepCoefficient n t z j| ≤ L :=
    stepCoefficient_abs_le t z j
  have hvar := step_variance_tendsto T hT t z ht0 htT
  have hmain := critical_step_characteristic hfinite M lam T L
    (∑ i : Fin m, ∑ l : Fin m,
      min (t i) (t l) * z i * z l)
    hcritical hT hL (fun n => stepCoefficient n t z) hθ hvar
  have hJ (n : ℕ) (i : Fin m) :
      meshIndex n (t i) ≤ meshIndex n T := meshIndex_mono (htT i)
  convert hmain using 1
  funext n
  unfold stepAlpha complexExpectM
  congr 1
  apply Finset.sum_congr rfl
  intro G hG
  rw [← mesh_linear_combination G t z (n13 n) (hJ n)]

end

end Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_Characteristic
