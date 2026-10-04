module

import all Mathlib.Basic.Real.Basic
public import Erdos448.dependencies.«DP-MERTENS».stage6.FrozenTaskContracts

public section

set_option backward.isDefEq.respectTransparency false

open Filter Finset
open scoped BigOperators Topology

namespace Erdos448.DPMertens.Tasks.MertCorrection

noncomputable section

open Erdos448.DPMertens
open Erdos448.DPMertens.Lowering

lemma logTail_hasSum {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    HasSum (fun k : ℕ ↦ if 2 ≤ k then u ^ k / (k : ℝ) else 0)
      (-Real.log (1 - u) - u) := by
  have hlog := Real.hasSum_pow_div_log_of_abs_lt_one
    (x := u) (by simpa [abs_of_nonneg hu0] using hu1)
  let f : ℕ → ℝ := fun n ↦ u ^ (n + 1) / (n + 1 : ℕ)
  have hshift :
      HasSum (fun n : ℕ ↦ u ^ (n + 2) / (n + 2 : ℕ))
        (-Real.log (1 - u) - u) := by
    change HasSum (fun n : ℕ ↦ f (n + 1)) _
    rw [hasSum_nat_add_iff]
    simpa [f, Finset.sum_range_one] using hlog
  let g : ℕ → ℝ := fun k ↦ if 2 ≤ k then u ^ k / (k : ℝ) else 0
  change HasSum g _
  simpa [g, Finset.sum_range_succ, Nat.cast_add, Nat.cast_ofNat] using
    ((hasSum_nat_add_iff (f := g) 2).mp (by simpa [g] using hshift))

lemma geometricTail_hasSum {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    HasSum (fun k : ℕ ↦ if 2 ≤ k then u ^ k else 0) (u ^ 2 / (1 - u)) := by
  have hgeo : HasSum (fun n : ℕ ↦ u ^ (n + 2)) (u ^ 2 / (1 - u)) := by
    simpa only [pow_add, div_eq_mul_inv, mul_comm] using
      (hasSum_geometric_of_lt_one hu0 hu1).mul_left (u ^ 2)
  let g : ℕ → ℝ := fun k ↦ if 2 ≤ k then u ^ k else 0
  change HasSum g _
  simpa [g, Finset.sum_range_succ] using
    ((hasSum_nat_add_iff (f := g) 2).mp (by simpa [g] using hgeo))

lemma localCorrection (p : ℕ) (hp : p.Prime) :
    correction p = correctionPowerSeries p ∧
      0 ≤ correction p ∧ correction p ≤ 2 / (p : ℝ) ^ 2 := by
  have hp2 : 2 ≤ p := hp.two_le
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  let u : ℝ := (p : ℝ)⁻¹
  have hu0 : 0 ≤ u := inv_nonneg.mpr hp0.le
  have hu1 : u < 1 := (inv_lt_one₀ hp0).2 (by exact_mod_cast hp.one_lt)
  have huHalf : u ≤ (1 : ℝ) / 2 := by
    have hp2r : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
    simpa [u] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hp2r
  have htail := logTail_hasSum hu0 hu1
  have hseries : correctionPowerSeries p = -Real.log (1 - u) - u := by
    rw [← htail.tsum_eq]
    apply tsum_congr
    intro k
    by_cases hk : 2 ≤ k
    · simp only [correctionPowerSeries, hk, if_true]
      dsimp [u]
      rw [one_div, mul_inv_rev, inv_pow]
      ring
    · simp [correctionPowerSeries, hk]
  have hcorr : correction p = correctionPowerSeries p := by
    rw [hseries]
    simp [correction, u]
  have hnonneg : 0 ≤ correctionPowerSeries p := by
    rw [hseries, ← htail.tsum_eq]
    exact tsum_nonneg fun k ↦ by
      split_ifs with hk
      · positivity
      · exact le_rfl
  have hgeo := geometricTail_hasSum hu0 hu1
  have hseries_le : correctionPowerSeries p ≤ u ^ 2 / (1 - u) := by
    rw [hseries, ← htail.tsum_eq]
    have hpoint (k : ℕ) :
        (if 2 ≤ k then u ^ k / (k : ℝ) else 0) ≤
          (if 2 ≤ k then u ^ k else 0) := by
      by_cases hk : 2 ≤ k
      · simp only [if_pos hk]
        apply div_le_self (pow_nonneg hu0 k)
        norm_cast
        omega
      · simp [hk]
    calc
      (∑' k : ℕ, if 2 ≤ k then u ^ k / (k : ℝ) else 0) ≤
          ∑' k : ℕ, if 2 ≤ k then u ^ k else 0 :=
        htail.summable.tsum_le_tsum hpoint hgeo.summable
      _ = u ^ 2 / (1 - u) := hgeo.tsum_eq
  have hden : (1 : ℝ) / 2 ≤ 1 - u := by linarith
  have hgeo_le : u ^ 2 / (1 - u) ≤ 2 / (p : ℝ) ^ 2 := by
    calc
      u ^ 2 / (1 - u) ≤ u ^ 2 / ((1 : ℝ) / 2) := by
        gcongr
      _ = 2 / (p : ℝ) ^ 2 := by
        dsimp [u]
        rw [inv_pow]
        field_simp
  exact ⟨hcorr, hcorr ▸ hnonneg, hcorr ▸ hseries_le.trans hgeo_le⟩

lemma correctionSeq_nonneg (n : ℕ) : 0 ≤ correctionSeq n := by
  by_cases hn : n.Prime
  · simp [correctionSeq, hn, (localCorrection n hn).2.1]
  · simp [correctionSeq, hn]

lemma correctionSeq_le (n : ℕ) :
    correctionSeq n ≤ 2 / (n : ℝ) ^ 2 := by
  by_cases hn : n.Prime
  · simpa [correctionSeq, hn] using (localCorrection n hn).2.2
  · rw [correctionSeq, if_neg hn]
    exact div_nonneg (by norm_num) (sq_nonneg _)

lemma correctionSeq_norm_summable :
    Summable (fun n : ℕ ↦ ‖correctionSeq n‖) := by
  have hbase : Summable (fun n : ℕ ↦ 1 / (n : ℝ) ^ 2) :=
    (Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num)
  have hmajor : Summable (fun n : ℕ ↦ 2 / (n : ℝ) ^ 2) :=
    by simpa [div_eq_mul_inv] using hbase.mul_left 2
  have hs : Summable correctionSeq :=
    hmajor.of_nonneg_of_le correctionSeq_nonneg correctionSeq_le
  exact hs.congr fun n ↦ by
    simp [Real.norm_eq_abs, abs_of_nonneg (correctionSeq_nonneg n)]

lemma correctionLE_eq_sum_range (x : ℝ) :
    correctionLE x = ∑ n ∈ Finset.range (Nat.floor x + 1), correctionSeq n := by
  unfold correctionLE primesLE correctionSeq
  rw [Finset.sum_filter]

lemma correctionPartial_tendsto :
    Tendsto correctionLE atTop (𝓝 (∑' n : ℕ, correctionSeq n)) := by
  have hs : Summable correctionSeq := correctionSeq_norm_summable.of_norm
  have hindex : Tendsto (fun x : ℝ ↦ Nat.floor x + 1) atTop atTop :=
    (tendsto_add_atTop_nat 1).comp tendsto_nat_floor_atTop
  exact (hs.hasSum.tendsto_sum_nat.comp hindex).congr
    (fun x ↦ (correctionLE_eq_sum_range x).symm)

lemma telescoping_sum (N K : ℕ) :
    (∑ n ∈ Finset.range K,
        2 * (1 / ((N : ℝ) + n - 1) - 1 / ((N : ℝ) + n))) =
      2 * (1 / ((N : ℝ) - 1) - 1 / ((N : ℝ) + K - 1)) := by
  induction K with
  | zero => simp
  | succ K ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring

lemma pseriesShift_tail_le (N : ℕ) (hN : 2 ≤ N) :
    (∑' n : ℕ, 2 / ((n + N : ℕ) : ℝ) ^ 2) ≤ 2 / ((N - 1 : ℕ) : ℝ) := by
  have hterm (n : ℕ) :
      2 / ((n + N : ℕ) : ℝ) ^ 2 ≤
        2 * (1 / ((N : ℝ) + n - 1) - 1 / ((N : ℝ) + n)) := by
    have hm : (1 : ℝ) < (N : ℝ) + n := by
      have : 1 < N + n := lt_of_lt_of_le Nat.one_lt_two (hN.trans (Nat.le_add_right N n))
      exact_mod_cast this
    have hdiff :
        1 / ((N : ℝ) + n - 1) - 1 / ((N : ℝ) + n) =
          1 / (((N : ℝ) + n - 1) * ((N : ℝ) + n)) := by
      field_simp [ne_of_gt (by linarith : 0 < (N : ℝ) + n - 1),
        ne_of_gt (by linarith : 0 < (N : ℝ) + n)]
      ring
    rw [hdiff]
    norm_num only [Nat.cast_add]
    have hprod : ((N : ℝ) + n - 1) * ((N : ℝ) + n) ≤ ((N : ℝ) + n) ^ 2 := by
      nlinarith
    have hp : 0 < ((N : ℝ) + n - 1) * ((N : ℝ) + n) := mul_pos (by linarith) (by linarith)
    have hs : 0 < ((N : ℝ) + n) ^ 2 := sq_pos_of_pos (by linarith)
    have hinv : 1 / ((N : ℝ) + n) ^ 2 ≤
        1 / (((N : ℝ) + n - 1) * ((N : ℝ) + n)) := by
      exact one_div_le_one_div_of_le hp hprod
    simpa [Nat.cast_add, add_comm, div_eq_mul_inv] using
      (mul_le_mul_of_nonneg_left hinv (by norm_num : (0 : ℝ) ≤ 2))
  apply Real.tsum_le_of_sum_range_le (fun n ↦ by positivity)
  intro K
  calc
    (∑ n ∈ Finset.range K, 2 / ((n + N : ℕ) : ℝ) ^ 2) ≤
        ∑ n ∈ Finset.range K,
          2 * (1 / ((N : ℝ) + n - 1) - 1 / ((N : ℝ) + n)) := by
            exact Finset.sum_le_sum fun n _ ↦ hterm n
    _ = 2 * (1 / ((N : ℝ) - 1) - 1 / ((N : ℝ) + K - 1)) :=
      telescoping_sum N K
    _ ≤ 2 / ((N - 1 : ℕ) : ℝ) := by
      have hNK : 0 ≤ 1 / ((N : ℝ) + K - 1) := by
        have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
        have hKr : (0 : ℝ) ≤ K := by positivity
        exact one_div_nonneg.mpr (by linarith)
      rw [Nat.cast_sub (by omega : 1 ≤ N)]
      norm_num only [Nat.cast_one]
      calc
        2 * (1 / ((N : ℝ) - 1) - 1 / ((N : ℝ) + K - 1)) ≤
            2 * (1 / ((N : ℝ) - 1)) := by nlinarith
        _ = 2 / ((N : ℝ) - 1) := by ring

lemma correctionTail (x : ℝ) (hx : 2 ≤ x) :
    0 ≤ (∑' n : ℕ, correctionSeq n) - correctionLE x ∧
      (∑' n : ℕ, correctionSeq n) - correctionLE x ≤ 2 / (x - 1) := by
  let N := Nat.floor x + 1
  have hfloor : 2 ≤ Nat.floor x := Nat.le_floor hx
  have hN : 2 ≤ N := by dsimp [N]; omega
  have hs : Summable correctionSeq := correctionSeq_norm_summable.of_norm
  have hsplit := hs.sum_add_tsum_nat_add N
  have htail :
      (∑' n : ℕ, correctionSeq n) - correctionLE x =
        ∑' n : ℕ, correctionSeq (n + N) := by
    rw [correctionLE_eq_sum_range]
    linarith
  rw [htail]
  constructor
  · exact tsum_nonneg fun n ↦ correctionSeq_nonneg (n + N)
  · have hshift : (∑' n : ℕ, correctionSeq (n + N)) ≤
        ∑' n : ℕ, 2 / ((n + N : ℕ) : ℝ) ^ 2 := by
      have hbase : Summable (fun n : ℕ ↦ 1 / (n : ℝ) ^ 2) :=
        (Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num)
      have hmajor0 : Summable (fun n : ℕ ↦ 2 / (n : ℝ) ^ 2) := by
        simpa [div_eq_mul_inv] using hbase.mul_left 2
      have hmajor : Summable (fun n : ℕ ↦ 2 / ((n + N : ℕ) : ℝ) ^ 2) :=
        hmajor0.comp_injective (fun _ _ h ↦ Nat.add_right_cancel h)
      have hshiftSummable : Summable (fun n : ℕ ↦ correctionSeq (n + N)) :=
        hs.comp_injective (fun _ _ h ↦ Nat.add_right_cancel h)
      exact hshiftSummable.tsum_le_tsum (fun n ↦ correctionSeq_le (n + N)) hmajor
    refine hshift.trans ((pseriesShift_tail_le N hN).trans ?_)
    have hx1 : 0 < x - 1 := by linarith
    have hfloor0 : 0 < (Nat.floor x : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hfloor)
    have hxfloor : x - 1 ≤ (Nat.floor x : ℝ) := by
      have := Nat.lt_floor_add_one x
      linarith
    dsimp [N]
    exact div_le_div_of_nonneg_left (by norm_num) hx1 hxfloor

/-- P-MERT-01, P-MERT-02, and P-MSC-07 over one correction sum witness. -/
@[expose] def result : Erdos448.DPMertens.Lowering.TASK_MERT_CORRECTION_Target where
  H := ∑' n : ℕ, correctionSeq n
  localCorrection := fun p hp ↦ localCorrection p hp
  convergence := ⟨correctionSeq_norm_summable,
    correctionSeq_norm_summable.of_norm.hasSum, correctionPartial_tendsto⟩
  tail := correctionTail

end

end Erdos448.DPMertens.Tasks.MertCorrection
