module

public import Erdos745.WrapUp.Proofs.Internal.Linked.W09_NearVariance
public import Erdos745.WrapUp.Proofs.Internal.Linked.W08_Fixed
public import Erdos745.WrapUp.Proofs.Internal.Linked.W11_Fixed

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local simp] Pi.div_def Pi.mul_def Pi.add_def Pi.sub_def Pi.neg_def Pi.inv_def Function.comp_def Pi.pow_def Pi.smul_def Real.rpow_eq_pow

@[expose] public section


namespace Erdos745.WrapUp.Proofs.Internal.W09_TREE_MASS_FixedCutoff

noncomputable section
open Filter
open scoped BigOperators Topology
open Erdos745.WrapUp.Proofs.W06_POISSON
open Erdos745.WrapUp.Proofs.Internal.W08_CYCLIC_FixedLocal
open Erdos745.WrapUp.Proofs.Internal.W11_FIXED_Analytic

lemma tupleTail_mono_cutoff {n M q power : ℕ} {B₀ B : ℝ}
    (hB : B₀ ≤ B) (hlog : 0 ≤ Real.log (n : ℝ)) :
    tupleTail n M q power B ≤ tupleTail n M q power B₀ := by
  unfold tupleTail
  apply Finset.sum_le_sum
  intro ks hks
  by_cases hpos : ∀ i, 0 < (ks i).val
  · by_cases hfar : ∃ i, B * Real.log (n : ℝ) < ((ks i).val : ℝ)
    · have hfar₀ : ∃ i, B₀ * Real.log (n : ℝ) < ((ks i).val : ℝ) := by
        obtain ⟨i, hi⟩ := hfar
        exact ⟨i, lt_of_le_of_lt (mul_le_mul_of_nonneg_right hB hlog) hi⟩
      simp [hpos, hfar, hfar₀]
    · simp only [hfar, and_false, ↓reduceIte]
      split_ifs
      · apply mul_nonneg
        · positivity
        · exact W09_TREE_MASS_Finite.expectM_nonneg (fun G => by positivity)
      · exact le_refl 0
  · have hpos' : ¬∀ i, 0 < ks i := by simpa using! hpos
    simp [hpos']

lemma fixed_cutoff_eventual_ranges (B : ℝ) (hB : 0 < B) :
    ∀ᶠ n : ℕ in atTop,
      1 ≤ Real.log (n : ℝ) ∧
      0 < logCutoff B n ∧
      logCutoff B n ≤ n ∧
      logCutoff B n < largeCutoff n ∧
      (logCutoff B n : ℝ) ≤ (B + 1) * Real.log n := by
  have hlog : ∀ᶠ n : ℕ in atTop, 1 ≤ Real.log (n : ℝ) :=
    (tendsto_atTop.1 (Real.tendsto_log_atTop.comp
      tendsto_natCast_atTop_atTop)) 1
  have hvertex := logCutoff_le_vertices_eventually (fun n => n)
    tendsto_id B hB
  have hlarge := logCutoff_le_largeCutoff_eventually (fun n => n)
    tendsto_id (B + 1) (by linarith)
  filter_upwards [hlog, hvertex, hlarge] with n hnlog hnvert hnlarge
  have hBLog : 0 < B * Real.log (n : ℝ) := by
    exact mul_pos hB (zero_lt_one.trans_le hnlog)
  have hpositive : 0 < logCutoff B n := by
    unfold logCutoff
    have hceil := Nat.le_ceil (B * Real.log (n : ℝ))
    have : (0 : ℝ) < (⌈B * Real.log (n : ℝ)⌉₊ : ℝ) := lt_of_lt_of_le hBLog hceil
    exact_mod_cast this
  have hceil : (logCutoff B n : ℝ) < B * Real.log n + 1 := by
    exact Nat.ceil_lt_add_one hBLog.le
  have hsmaller : (logCutoff B n : ℝ) < (B + 1) * Real.log n := by
    nlinarith
  have hleceil : (B + 1) * Real.log n ≤
      (logCutoff (B + 1) n : ℝ) := by
    exact Nat.le_ceil _
  have hstrict : logCutoff B n < logCutoff (B + 1) n := by
    exact_mod_cast (lt_of_lt_of_le hsmaller hleceil)
  exact ⟨hnlog, hpositive, hnvert, lt_of_lt_of_le hstrict hnlarge,
    hsmaller.le⟩

lemma fixed_log_sq_over_n_eventually (B C : ℝ) :
    ∀ᶠ n : ℕ in atTop,
      C * (B * Real.log (n : ℝ)) ^ 2 / n ≤ 1 := by
  have ht := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero).comp
    tendsto_natCast_atTop_atTop
  have ht' : Tendsto (fun n : ℕ =>
      C * (B * Real.log (n : ℝ)) ^ 2 / n) atTop (𝓝 0) := by
    convert ht.const_mul (C * B ^ 2) using 1
    · funext n
      simp [div_eq_mul_inv]
      ring
    · simp
  exact ((tendsto_order.1 ht').2 1 zero_lt_one).mono fun _ h => h.le

lemma fixed_common_cutoff
    (hRate : RateStatement) (hT : TupleEstimatesStatement)
    {M : NatSeq} {lam : ℝ} (hadm : admissible M)
    (hlam : 1 < lam) (hdeg : Tendsto (degree M) atTop (𝓝 lam)) :
    ∃ lo hi delta a B : ℝ,
      0 < lo ∧ lo ≤ hi ∧ 0 < delta ∧ 0 < a ∧ 0 < B ∧ 2 / a ≤ B ∧
      ∀ᶠ n : ℕ in atTop,
        M n ≤ capacity n ∧ lo ≤ degree M n ∧ degree M n ≤ hi ∧
        a ≤ rate (degree M n) ∧ delta ≤ |degree M n - 1| ∧
        1 ≤ Real.log (n : ℝ) ∧
        0 < logCutoff B n ∧ logCutoff B n ≤ n ∧
        logCutoff B n < largeCutoff n ∧
        (logCutoff B n : ℝ) ≤ (B + 1) * Real.log n ∧
        tupleTail n (M n) 1 1 B ≤ Real.rpow (n : ℝ) (-2 : ℝ) ∧
        tupleTail n (M n) 1 2 B ≤ Real.rpow (n : ℝ) (-2 : ℝ) ∧
        tupleTail n (M n) 2 1 B ≤ Real.rpow (n : ℝ) (-2 : ℝ) := by
  obtain ⟨lo, hi, a, hlo, hlohi, ha, hcompact⟩ :=
    fixed_compact_data hRate (zero_lt_one.trans hlam) hlam.ne' hdeg
  let delta : ℝ := (lam - 1) / 2
  have hdelta : 0 < delta := by dsimp [delta]; linarith
  have hsep : ∀ᶠ n in atTop, delta ≤ |degree M n - 1| := by
    have ht : Tendsto (fun n => |degree M n - 1|) atTop (𝓝 |lam - 1|) := by
      simpa using! (hdeg.sub_const 1).abs
    have habs : |lam - 1| = lam - 1 := abs_of_pos (by linarith)
    exact ((tendsto_order.1 ht).1 delta (by dsimp [delta]; rw [habs]; linarith)).mono
      fun _ h => h.le
  obtain ⟨B₁₁, hB₁₁, n₁₁, ht₁₁⟩ :=
    hT.2.2.2 lo hi delta 2 1 1 hlo hlohi hdelta (by norm_num) (by omega)
  obtain ⟨B₁₂, hB₁₂, n₁₂, ht₁₂⟩ :=
    hT.2.2.2 lo hi delta 2 1 2 hlo hlohi hdelta (by norm_num) (by omega)
  obtain ⟨B₂₁, hB₂₁, n₂₁, ht₂₁⟩ :=
    hT.2.2.2 lo hi delta 2 2 1 hlo hlohi hdelta (by norm_num) (by omega)
  let B := max 1 (max B₁₁ (max B₁₂ (max B₂₁ (2 / a))))
  have hB : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hB₁₁le : B₁₁ ≤ B :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hB₁₂le : B₁₂ ≤ B := by
    dsimp [B]
    exact le_max_of_le_right (le_max_of_le_right (le_max_left _ _))
  have hB₂₁le : B₂₁ ≤ B := by
    dsimp [B]
    exact le_max_of_le_right (le_max_of_le_right
      (le_max_of_le_right (le_max_left _ _)))
  have hBale : 2 / a ≤ B := by
    dsimp [B]
    exact le_max_of_le_right (le_max_of_le_right
      (le_max_of_le_right (le_max_right _ _)))
  refine ⟨lo, hi, delta, a, B, hlo, hlohi, hdelta, ha, hB, hBale, ?_⟩
  filter_upwards [hadm, hcompact, hsep, fixed_cutoff_eventual_ranges B hB,
    eventually_ge_atTop (max n₁₁ (max n₁₂ n₂₁))]
    with n hcap hcomp hsepN hrange hn₀
  obtain ⟨hloN, hhiN, haN⟩ := hcomp
  obtain ⟨hlog, hHpos, hHn, hHlarge, hHlog⟩ := hrange
  have hn₁₁ : n₁₁ ≤ n := le_trans (Nat.le_max_left ..) hn₀
  have hn₁₂ : n₁₂ ≤ n := le_trans
    ((Nat.le_max_left ..).trans (Nat.le_max_right ..)) hn₀
  have hn₂₁ : n₂₁ ≤ n := le_trans
    ((Nat.le_max_right ..).trans (Nat.le_max_right ..)) hn₀
  have h₁₁ := ht₁₁ n (M n) hn₁₁ hcap hloN hhiN hsepN
  have h₁₂ := ht₁₂ n (M n) hn₁₂ hcap hloN hhiN hsepN
  have h₂₁ := ht₂₁ n (M n) hn₂₁ hcap hloN hhiN hsepN
  have h₁₁' := (tupleTail_mono_cutoff hB₁₁le (by linarith)).trans h₁₁
  have h₁₂' := (tupleTail_mono_cutoff hB₁₂le (by linarith)).trans h₁₂
  have h₂₁' := (tupleTail_mono_cutoff hB₂₁le (by linarith)).trans h₂₁
  exact ⟨hcap, hloN, hhiN, haN, hsepN, hlog, hHpos, hHn,
    hHlarge, hHlog, h₁₁', h₁₂', h₂₁'⟩

end
end Erdos745.WrapUp.Proofs.Internal.W09_TREE_MASS_FixedCutoff


namespace Erdos745.WrapUp.Proofs.Internal.W09_TREE_MASS_FixedTail

noncomputable section
open Filter
open scoped BigOperators Topology
open Erdos745.WrapUp.Proofs.W06_POISSON
open Erdos745.WrapUp.Proofs.Internal.W09_TREE_MASS_Finite
open Erdos745.WrapUp.Proofs.Internal.W09_TREE_MASS_Analytic

private lemma tupleTail_one_reindex (n M power : ℕ) (B : ℝ) :
    tupleTail n M 1 power B =
      ∑ k : Fin (n + 1),
        if 0 < k.val ∧ B * Real.log n < (k.val : ℝ) then
          (k.val : ℝ) ^ power * momentOne n M k.val else 0 := by
  classical
  unfold tupleTail
  apply Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin (n + 1)))
  intro ks
  have hfun : (fun i : Fin 1 => (ks i).val) =
      fun _ => (ks 0).val := by
    funext i
    fin_cases i
    rfl
  simp [Equiv.funUnique, momentOne, hfun]

private lemma tupleTail_two_reindex (n M : ℕ) (B : ℝ) :
    tupleTail n M 2 1 B =
      ∑ k : Fin (n + 1), ∑ l : Fin (n + 1),
        if (0 < k.val ∧ 0 < l.val) ∧
            (B * Real.log n < (k.val : ℝ) ∨
              B * Real.log n < (l.val : ℝ)) then
          (k.val : ℝ) * l.val * momentTwo n M k.val l.val else 0 := by
  classical
  unfold tupleTail
  rw [Fintype.sum_equiv (finTwoArrowEquiv (Fin (n + 1)))
    (fun ks : Fin 2 → Fin (n + 1) =>
      if (∀ i, 0 < (ks i).val) ∧
          (∃ i, B * Real.log n < ((ks i).val : ℝ)) then
        (∏ i, (((ks i).val : ℝ) ^ (1 : ℕ))) *
          tupleMoment n M 2 (fun i => (ks i).val) else 0)
    (fun p : Fin (n + 1) × Fin (n + 1) =>
      if (0 < p.1.val ∧ 0 < p.2.val) ∧
          (B * Real.log n < (p.1.val : ℝ) ∨
            B * Real.log n < (p.2.val : ℝ)) then
        (p.1.val : ℝ) * p.2.val * momentTwo n M p.1.val p.2.val else 0)
    (by
      intro ks
      have hfun : (fun i : Fin 2 => (ks i).val) =
          pairSizes (ks 0).val (ks 1).val := by
        funext i
        fin_cases i <;> rfl
      simp [finTwoArrowEquiv, Fin.forall_fin_two, Fin.exists_fin_two,
        Fin.prod_univ_two, momentTwo, hfun])]
  exact Fintype.sum_prod_type _

private lemma tail_one_le_tupleTail {n M H N power : ℕ} {B : ℝ}
    (hN : N ≤ n + 1) (hH : B * Real.log n ≤ (H : ℝ)) :
    (∑ k ∈ Finset.Ico (H + 1) N,
      (k : ℝ) ^ power * momentOne n M k) ≤
      tupleTail n M 1 power B := by
  classical
  rw [tupleTail_one_reindex]
  let f : ℕ → ℝ := fun k =>
    if 0 < k ∧ B * Real.log n < (k : ℝ) then
      (k : ℝ) ^ power * momentOne n M k else 0
  have hrewrite :
      (∑ k : Fin (n + 1),
        if 0 < k.val ∧ B * Real.log n < (k.val : ℝ) then
          (k.val : ℝ) ^ power * momentOne n M k.val else 0) =
      ∑ k ∈ Finset.range (n + 1), f k := by
    rw [Finset.sum_fin_eq_sum_range]
    apply Finset.sum_congr rfl
    intro k hk
    simp only [Finset.mem_range] at hk
    simp [f, hk]
  rw [hrewrite]
  have hsubset : Finset.Ico (H + 1) N ⊆ Finset.range (n + 1) := by
    intro k hk
    exact Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_Ico.mp hk).2 hN)
  calc
    (∑ k ∈ Finset.Ico (H + 1) N,
        (k : ℝ) ^ power * momentOne n M k) =
        ∑ k ∈ Finset.Ico (H + 1) N, f k := by
          apply Finset.sum_congr rfl
          intro k hk
          have hkpos : 0 < k := by
            have hklo := (Finset.mem_Ico.mp hk).1
            omega
          have hkfar : B * Real.log n < (k : ℝ) := by
            have : H < k := by
              have hklo := (Finset.mem_Ico.mp hk).1
              omega
            exact lt_of_le_of_lt hH (by exact_mod_cast this)
          simp [f, hkpos, hkfar]
    _ ≤ ∑ k ∈ Finset.range (n + 1), f k := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
      intro k hk hnot
      dsimp [f]
      split_ifs
      · exact mul_nonneg (by positivity) (momentOne_nonneg n M k)
      · exact le_refl 0

private lemma tail_two_le_tupleTail {n M H N : ℕ} {B : ℝ}
    (hN : N ≤ n + 1) (hH : B * Real.log n ≤ (H : ℝ)) :
    (∑ k ∈ Finset.Ico (H + 1) N,
      ∑ l ∈ Finset.Ico (H + 1) N,
        (k : ℝ) * l * momentTwo n M k l) ≤
      tupleTail n M 2 1 B := by
  classical
  let s := Finset.Ico (H + 1) N
  let t := Finset.range (n + 1)
  let f : ℕ × ℕ → ℝ := fun p =>
    if (0 < p.1 ∧ 0 < p.2) ∧
        (B * Real.log n < (p.1 : ℝ) ∨ B * Real.log n < (p.2 : ℝ)) then
      (p.1 : ℝ) * p.2 * momentTwo n M p.1 p.2 else 0
  have hsubset : s ×ˢ s ⊆ t ×ˢ t := by
    intro p hp
    have hp' := Finset.mem_product.mp hp
    apply Finset.mem_product.mpr
    constructor
    · exact Finset.mem_range.mpr
        (lt_of_lt_of_le (Finset.mem_Ico.mp hp'.1).2 hN)
    · exact Finset.mem_range.mpr
        (lt_of_lt_of_le (Finset.mem_Ico.mp hp'.2).2 hN)
  have hnonneg : ∀ p ∈ t ×ˢ t, 0 ≤ f p := by
    intro p hp
    dsimp [f]
    split_ifs
    · exact mul_nonneg (mul_nonneg (by positivity) (by positivity))
        (momentTwo_nonneg n M p.1 p.2)
    · exact le_refl 0
  have hpart :
      (∑ k ∈ s, ∑ l ∈ s,
        (k : ℝ) * l * momentTwo n M k l) =
      ∑ p ∈ s ×ˢ s, f p := by
    rw [Finset.sum_product]
    apply Finset.sum_congr rfl
    intro k hk
    apply Finset.sum_congr rfl
    intro l hl
    have hkpos : 0 < k := by have := (Finset.mem_Ico.mp hk).1; omega
    have hlpos : 0 < l := by have := (Finset.mem_Ico.mp hl).1; omega
    have hkfar : B * Real.log n < (k : ℝ) := by
      change k ∈ Finset.Ico (H + 1) N at hk
      have : H < k := by
        have hklo := (Finset.mem_Ico.mp hk).1
        omega
      exact lt_of_le_of_lt hH (by exact_mod_cast this)
    simp [f, hkpos, hlpos, hkfar]
  have hall : (∑ p ∈ t ×ˢ t, f p) = tupleTail n M 2 1 B := by
    rw [tupleTail_two_reindex]
    rw [Finset.sum_product]
    simp only [t]
    rw [Finset.sum_fin_eq_sum_range]
    apply Finset.sum_congr rfl
    intro k hk
    simp only [Finset.mem_range] at hk
    simp only [dif_pos hk]
    rw [Finset.sum_fin_eq_sum_range]
    apply Finset.sum_congr rfl
    intro l hl
    simp only [Finset.mem_range] at hl
    simp [f, hl]
  calc
    _ = ∑ p ∈ s ×ˢ s, f p := hpart
    _ ≤ ∑ p ∈ t ×ˢ t, f p :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun p hp _ => hnonneg p hp)
    _ = _ := hall

lemma fixed_actual_mean_tail_bound {n M H N : ℕ} {B : ℝ}
    (hN : N ≤ n + 1) (hH : B * Real.log n ≤ (H : ℝ))
    (ht : tupleTail n M 1 1 B ≤ Real.rpow (n : ℝ) (-2 : ℝ)) :
    (∑ k ∈ Finset.Ico (H + 1) N, massTerm n M k) ≤
      Real.rpow (n : ℝ) (-2 : ℝ) := by
  simpa [massTerm, momentOne] using!
    (tail_one_le_tupleTail (n := n) (M := M) (H := H) (N := N)
      (power := 1) hN hH).trans ht

lemma fixed_discarded_second_bound {n M H N : ℕ} {B : ℝ}
    (hN : N ≤ n + 1) (hH : B * Real.log n ≤ (H : ℝ))
    (ht₁₂ : tupleTail n M 1 2 B ≤ Real.rpow (n : ℝ) (-2 : ℝ))
    (ht₂₁ : tupleTail n M 2 1 B ≤ Real.rpow (n : ℝ) (-2 : ℝ)) :
    expectM n M (fun G => treeMassSum G (Finset.Ico (H + 1) N) ^ 2) ≤
      2 * Real.rpow (n : ℝ) (-2 : ℝ) := by
  rw [expect_treeMassSum_sq]
  have hdiag := (tail_one_le_tupleTail (n := n) (M := M)
    (H := H) (N := N) (power := 2) hN hH).trans ht₁₂
  have hpair := (tail_two_le_tupleTail (n := n) (M := M)
    (H := H) (N := N) hN hH).trans ht₂₁
  simp only [momentOne, momentTwo] at hdiag hpair
  linarith

end
end Erdos745.WrapUp.Proofs.Internal.W09_TREE_MASS_FixedTail


namespace Erdos745.WrapUp.Proofs.Internal.W09_TREE_MASS_FixedLocal

noncomputable section
open Filter
open scoped BigOperators Topology
open Erdos745.WrapUp.Proofs.W06_POISSON
open Erdos745.WrapUp.Proofs.Internal.W09_TREE_MASS_Finite
open Erdos745.WrapUp.Proofs.Internal.W09_TREE_MASS_Analytic

lemma fixed_one_relative {n M k : ℕ} {C : ℝ}
    (hk : 0 < k) (hlam : 0 < degreeAt n M)
    (hJ : 0 < momentOne n M k)
    (hlog : |Real.log (momentOne n M k / treeLeading n M k)| ≤
      C * (k : ℝ) ^ 2 / n)
    (hsmall : C * (k : ℝ) ^ 2 / n ≤ 1) :
    |massTerm n M k - leadingMassTerm n M k| ≤
      2 * C * leadingMassTerm n M k * (k : ℝ) ^ 2 / n := by
  have hL : 0 < treeLeading n M k := by
    have hn : 0 < n := by
      by_contra hn0
      have : n = 0 := Nat.eq_zero_of_not_pos hn0
      subst n
      simp [degreeAt] at hlam
    simpa [tupleLeading] using!
      (W04_TUPLES_Foundation.tupleLeading_pos n M 1 (fun _ => k)
        hn hlam (fun _ => hk))
  have hrel := abs_log_ratio_to_relative hJ hL hlog hsmall
  unfold massTerm leadingMassTerm momentOne
  rw [show (k : ℝ) * tupleMoment n M 1 (fun _ => k) -
      (k : ℝ) * treeLeading n M k =
      (k : ℝ) * (tupleMoment n M 1 (fun _ => k) - treeLeading n M k) by ring,
    abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ k)]
  have hm := mul_le_mul_of_nonneg_left hrel (by positivity : (0 : ℝ) ≤ k)
  convert! hm using 1; ring

lemma fixed_one_upper {n M k : ℕ} {C : ℝ}
    (hk : 0 < k) (hlam : 0 < degreeAt n M)
    (hJ : 0 < momentOne n M k)
    (hlog : |Real.log (momentOne n M k / treeLeading n M k)| ≤
      C * (k : ℝ) ^ 2 / n)
    (hsmall : C * (k : ℝ) ^ 2 / n ≤ 1) :
    massTerm n M k ≤ 3 * leadingMassTerm n M k := by
  have hrel := fixed_one_relative hk hlam hJ hlog hsmall
  have hnonneg := leadingMassTerm_nonneg (n := n) (M := M) (k := k) hlam
  have hE : 0 ≤ C * (k : ℝ) ^ 2 / n := by
    exact (abs_nonneg _).trans hlog
  have habs := le_trans (le_abs_self _) hrel
  have hmul : 2 * C * leadingMassTerm n M k * (k : ℝ) ^ 2 / n ≤
      2 * leadingMassTerm n M k := by
    calc
      _ = 2 * leadingMassTerm n M k * (C * (k : ℝ) ^ 2 / n) := by ring
      _ ≤ 2 * leadingMassTerm n M k := by
        convert mul_le_mul_of_nonneg_left hsmall (by positivity :
          0 ≤ 2 * leadingMassTerm n M k) using 1; ring
  linarith

lemma fixed_pair_le_leading {n M k l : ℕ} {C : ℝ}
    (hk : 0 < k) (hl : 0 < l) (hlam : 0 < degreeAt n M)
    (hJ : 0 < momentTwo n M k l)
    (hlog : |Real.log (momentTwo n M k l /
      (treeLeading n M k * treeLeading n M l))| ≤
      C * ((k : ℝ) + l) ^ 2 / n)
    (hsmall : C * ((k : ℝ) + l) ^ 2 / n ≤ 1) :
    |(k : ℝ) * l * momentTwo n M k l -
      leadingMassTerm n M k * leadingMassTerm n M l| ≤
      2 * C * leadingMassTerm n M k * leadingMassTerm n M l *
        ((k : ℝ) + l) ^ 2 / n := by
  have hLk : 0 < treeLeading n M k := by
    have hn : 0 < n := by
      by_contra hn0
      have : n = 0 := Nat.eq_zero_of_not_pos hn0
      subst n
      simp [degreeAt] at hlam
    have h := W04_TUPLES_Foundation.tupleLeading_pos n M 1 (fun _ => k)
      hn hlam (fun _ => hk)
    simpa [tupleLeading] using! h
  have hLl : 0 < treeLeading n M l := by
    have hn : 0 < n := by
      by_contra hn0
      have : n = 0 := Nat.eq_zero_of_not_pos hn0
      subst n
      simp [degreeAt] at hlam
    have h := W04_TUPLES_Foundation.tupleLeading_pos n M 1 (fun _ => l)
      hn hlam (fun _ => hl)
    simpa [tupleLeading] using! h
  have hrel := abs_log_ratio_to_relative hJ (mul_pos hLk hLl) hlog hsmall
  have hmul := mul_le_mul_of_nonneg_left hrel
    (by positivity : (0 : ℝ) ≤ (k : ℝ) * l)
  unfold leadingMassTerm
  rw [show (k : ℝ) * l * momentTwo n M k l -
    ((k : ℝ) * treeLeading n M k) *
      ((l : ℝ) * treeLeading n M l) =
    ((k : ℝ) * l) *
      (momentTwo n M k l - treeLeading n M k * treeLeading n M l) by ring,
    abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (k : ℝ) * l)]
  convert hmul using 1; ring

lemma fixed_covariance_le {n M k l : ℕ} {C₁ C₂ : ℝ}
    (hk : 0 < k) (hl : 0 < l) (hlam : 0 < degreeAt n M)
    (hC₁ : 0 ≤ C₁) (_hC₂ : 0 ≤ C₂)
    (hJk : 0 < momentOne n M k) (hJl : 0 < momentOne n M l)
    (hJ₂ : 0 < momentTwo n M k l)
    (hlogk : |Real.log (momentOne n M k / treeLeading n M k)| ≤
      C₁ * (k : ℝ) ^ 2 / n)
    (hlogl : |Real.log (momentOne n M l / treeLeading n M l)| ≤
      C₁ * (l : ℝ) ^ 2 / n)
    (hlog₂ : |Real.log (momentTwo n M k l /
      (treeLeading n M k * treeLeading n M l))| ≤
      C₂ * ((k : ℝ) + l) ^ 2 / n)
    (hsmallk : C₁ * (k : ℝ) ^ 2 / n ≤ 1)
    (hsmalll : C₁ * (l : ℝ) ^ 2 / n ≤ 1)
    (hsmall₂ : C₂ * ((k : ℝ) + l) ^ 2 / n ≤ 1) :
    (k : ℝ) * l * momentTwo n M k l -
      massTerm n M k * massTerm n M l ≤
      (2 * C₂ + 8 * C₁) * leadingMassTerm n M k *
        leadingMassTerm n M l * ((k : ℝ) + l) ^ 2 / n := by
  let Ak := massTerm n M k
  let Al := massTerm n M l
  let bk := leadingMassTerm n M k
  let bl := leadingMassTerm n M l
  have hbk : 0 ≤ bk := leadingMassTerm_nonneg hlam
  have hbl : 0 ≤ bl := leadingMassTerm_nonneg hlam
  have hAl : 0 ≤ Al := massTerm_nonneg n M l
  have hAl3 : Al ≤ 3 * bl := fixed_one_upper hl hlam hJl hlogl hsmalll
  have hEk := fixed_one_relative hk hlam hJk hlogk hsmallk
  have hEl := fixed_one_relative hl hlam hJl hlogl hsmalll
  have hP := fixed_pair_le_leading hk hl hlam hJ₂ hlog₂ hsmall₂
  have hkk : (k : ℝ) ^ 2 ≤ ((k : ℝ) + l) ^ 2 := by
    have hkR : 0 ≤ (k : ℝ) := by positivity
    have hlR : 0 ≤ (l : ℝ) := by positivity
    nlinarith only [hkR, hlR]
  have hll : (l : ℝ) ^ 2 ≤ ((k : ℝ) + l) ^ 2 := by
    have hkR : 0 ≤ (k : ℝ) := by positivity
    have hlR : 0 ≤ (l : ℝ) := by positivity
    nlinarith only [hkR, hlR]
  have hn : 0 < (n : ℝ) := by
    by_contra hn0
    have : n = 0 := by exact_mod_cast (le_antisymm (le_of_not_gt hn0) (by positivity))
    subst n
    simp [degreeAt] at hlam
  have hdiff : bk * bl - Ak * Al ≤
      8 * C₁ * bk * bl * ((k : ℝ) + l) ^ 2 / n := by
    have hkabs : bk - Ak ≤ 2 * C₁ * bk * (k : ℝ) ^ 2 / n := by
      dsimp [bk, Ak]
      linarith [neg_le_of_abs_le hEk]
    have hlabs : bl - Al ≤ 2 * C₁ * bl * (l : ℝ) ^ 2 / n := by
      dsimp [bl, Al]
      linarith [neg_le_of_abs_le hEl]
    have hstep : bk * bl - Ak * Al = (bk - Ak) * Al + bk * (bl - Al) := by ring
    rw [hstep]
    have h₁ : (bk - Ak) * Al ≤
        (2 * C₁ * bk * (k : ℝ) ^ 2 / n) * (3 * bl) := by
      gcongr
    have h₂ : bk * (bl - Al) ≤
        bk * (2 * C₁ * bl * (l : ℝ) ^ 2 / n) := by
      gcongr
    have h₃ : (2 * C₁ * bk * (k : ℝ) ^ 2 / n) * (3 * bl) +
        bk * (2 * C₁ * bl * (l : ℝ) ^ 2 / n) ≤
        8 * C₁ * bk * bl * ((k : ℝ) + l) ^ 2 / n := by
      have hfac : 0 ≤ C₁ * bk * bl / (n : ℝ) := by positivity
      have hk' := mul_le_mul_of_nonneg_left hkk hfac
      have hl' := mul_le_mul_of_nonneg_left hll hfac
      calc
        (2 * C₁ * bk * (k : ℝ) ^ 2 / n) * (3 * bl) +
            bk * (2 * C₁ * bl * (l : ℝ) ^ 2 / n) =
          6 * ((C₁ * bk * bl / n) * (k : ℝ) ^ 2) +
            2 * ((C₁ * bk * bl / n) * (l : ℝ) ^ 2) := by ring
        _ ≤ 6 * ((C₁ * bk * bl / n) * ((k : ℝ) + l) ^ 2) +
            2 * ((C₁ * bk * bl / n) * ((k : ℝ) + l) ^ 2) :=
          add_le_add (mul_le_mul_of_nonneg_left hk' (by norm_num))
            (mul_le_mul_of_nonneg_left hl' (by norm_num))
        _ = _ := by ring
    linarith
  have hP' := le_trans (le_abs_self _) hP
  calc
    (k : ℝ) * l * momentTwo n M k l - massTerm n M k * massTerm n M l =
        ((k : ℝ) * l * momentTwo n M k l - bk * bl) +
          (bk * bl - Ak * Al) := by dsimp [Ak, Al]; ring
    _ ≤ 2 * C₂ * bk * bl * ((k : ℝ) + l) ^ 2 / n +
        8 * C₁ * bk * bl * ((k : ℝ) + l) ^ 2 / n :=
      add_le_add hP' hdiff
    _ = _ := by dsimp [bk, bl]; ring

end
end Erdos745.WrapUp.Proofs.Internal.W09_TREE_MASS_FixedLocal


namespace Erdos745.WrapUp.Proofs.Internal.W09_TREE_MASS_FixedSums

noncomputable section
open Filter
open scoped BigOperators Topology
open Erdos745.WrapUp.Proofs.W06_POISSON
open Erdos745.WrapUp.Proofs.Internal.W09_TREE_MASS_Analytic

lemma fixed_leading_mass_bound {n M k : ℕ} {D a : ℝ}
    (hk : 0 < k) (hlo : 1 / 2 ≤ degreeAt n M)
    (ha : a ≤ rate (degreeAt n M)) (_ha0 : 0 < a) (hDpos : 0 ≤ D)
    (hD : ∀ n M k : ℕ, 0 < k → 1 / 2 ≤ degreeAt n M →
      leadingMassTerm n M k ≤ D * n *
        Real.rpow (k : ℝ) (-(3 / 2) : ℝ) *
        Real.exp (-rate (degreeAt n M) * k)) :
    leadingMassTerm n M k ≤ D * n *
      Real.rpow (k : ℝ) (-(3 / 2) : ℝ) * Real.exp (-a * k) := by
  have hb := hD n M k hk hlo
  have hexp : Real.exp (-rate (degreeAt n M) * k) ≤
      Real.exp (-a * k) := Real.exp_le_exp.mpr (by nlinarith)
  have hfac : 0 ≤ D * (n : ℝ) * Real.rpow (k : ℝ) (-(3 / 2) : ℝ) :=
    mul_nonneg (mul_nonneg hDpos (by positivity))
      (Real.rpow_nonneg (by positivity) _)
  exact hb.trans (mul_le_mul_of_nonneg_left hexp hfac)

def fixedSumConstant (hA : AnalyticSumsStatement) (D a : ℝ) : ℝ :=
  D * (Classical.choose
    (analytic_power_bound hA (-(1 / 2) : ℝ) (by norm_num)) *
      Real.rpow (min a 1) (-(1 / 2) : ℝ) +
    Classical.choose
    (analytic_power_bound hA (1 / 2 : ℝ) (by norm_num)) *
      Real.rpow (min a 1) (-(3 / 2) : ℝ))

lemma fixedSumConstant_pos (hA : AnalyticSumsStatement) {D a : ℝ}
    (hD : 0 < D) (ha : 0 < a) : 0 < fixedSumConstant hA D a := by
  unfold fixedSumConstant
  have hq₁ := (Classical.choose_spec
    (analytic_power_bound hA (-(1 / 2) : ℝ) (by norm_num))).1
  have hq₂ := (Classical.choose_spec
    (analytic_power_bound hA (1 / 2 : ℝ) (by norm_num))).1
  have hu : 0 < min a 1 := lt_min ha zero_lt_one
  exact mul_pos hD (add_pos
    (mul_pos hq₁ (Real.rpow_pos_of_pos hu _))
    (mul_pos hq₂ (Real.rpow_pos_of_pos hu _)))

lemma fixed_power_sums (hA : AnalyticSumsStatement) {n M H : ℕ}
    {D a : ℝ} (hn : 0 < n) (hD : 0 < D) (ha : 0 < a)
    (hlam : 0 < degreeAt n M)
    (hpoint : ∀ k ∈ Finset.Ico 1 (H + 1),
      leadingMassTerm n M k ≤ D * n *
        Real.rpow (k : ℝ) (-(3 / 2) : ℝ) * Real.exp (-a * k)) :
    (∑ k ∈ Finset.Ico 1 (H + 1), leadingMassTerm n M k) ≤
      fixedSumConstant hA D a * n ∧
      (∑ k ∈ Finset.Ico 1 (H + 1), leadingMassTerm n M k * k) ≤
        fixedSumConstant hA D a * n ∧
      (∑ k ∈ Finset.Ico 1 (H + 1), leadingMassTerm n M k * (k : ℝ) ^ 2) ≤
        fixedSumConstant hA D a * n := by
  let u := min a 1
  have hu : 0 < u := lt_min ha zero_lt_one
  have hu1 : u ≤ 1 := min_le_right ..
  have hbeta₁ : -1 < (-(1 / 2) : ℝ) := by norm_num
  have hbeta₂ : -1 < (1 / 2 : ℝ) := by norm_num
  let Q₁ := Classical.choose
    (analytic_power_bound hA (-(1 / 2) : ℝ) hbeta₁)
  let Q₂ := Classical.choose
    (analytic_power_bound hA (1 / 2 : ℝ) hbeta₂)
  have hQ₁ : 0 < Q₁ := (Classical.choose_spec
    (analytic_power_bound hA (-(1 / 2) : ℝ) hbeta₁)).1
  have hQ₂ : 0 < Q₂ := (Classical.choose_spec
    (analytic_power_bound hA (1 / 2 : ℝ) hbeta₂)).1
  let A := D * (Q₁ * Real.rpow u (-(1 / 2) : ℝ) +
    Q₂ * Real.rpow u (-(3 / 2) : ℝ))
  have hApos : 0 < A := by
    dsimp [A]
    exact mul_pos hD (add_pos
      (mul_pos hQ₁ (Real.rpow_pos_of_pos hu _))
      (mul_pos hQ₂ (Real.rpow_pos_of_pos hu _)))
  change (∑ k ∈ Finset.Ico 1 (H + 1), leadingMassTerm n M k) ≤ A * n ∧
    (∑ k ∈ Finset.Ico 1 (H + 1), leadingMassTerm n M k * k) ≤ A * n ∧
    (∑ k ∈ Finset.Ico 1 (H + 1), leadingMassTerm n M k * (k : ℝ) ^ 2) ≤
      A * n
  have hhead1 :
      (∑ k ∈ Finset.Ico 1 (H + 1), leadingMassTerm n M k * k) ≤
      D * n * Q₁ * Real.rpow u (-(1 / 2) : ℝ) := by
    calc
      _ ≤ ∑ k ∈ Finset.Ico 1 (H + 1),
          D * n * (Real.rpow (k : ℝ) (-(1 / 2) : ℝ) *
            Real.exp (-u * k)) := by
        apply Finset.sum_le_sum
        intro k hk
        have hkpos := (Finset.mem_Ico.mp hk).1
        have hexp : Real.exp (-a * k) ≤ Real.exp (-u * k) :=
          Real.exp_le_exp.mpr (by
            have huA : u ≤ a := min_le_left ..
            nlinarith)
        have hfac : 0 ≤ D * (n : ℝ) * Real.rpow (k : ℝ) (-(3 / 2) : ℝ) :=
          mul_nonneg (mul_nonneg hD.le (by positivity))
            (Real.rpow_nonneg (by positivity) _)
        have hb := (hpoint k hk).trans
          (mul_le_mul_of_nonneg_left hexp hfac)
        have hmul := mul_le_mul_of_nonneg_right hb (by positivity : (0 : ℝ) ≤ k)
        calc
          _ ≤ (D * n * Real.rpow (k : ℝ) (-(3 / 2) : ℝ) *
              Real.exp (-u * k)) * k := hmul
          _ = _ := by rw [← mul_rpow_neg_three_half k hkpos]; ring
      _ = D * n * (∑ k ∈ Finset.Ico 1 (H + 1),
          Real.rpow (k : ℝ) (-(1 / 2) : ℝ) * Real.exp (-u * k)) := by
        rw [Finset.mul_sum]
      _ ≤ D * n * (Q₁ * Real.rpow u (-(1 / 2) : ℝ)) := by
        gcongr
        have hs := finite_power_exp_sum_le hA hbeta₁ hu hu1 H
        change _ ≤ Q₁ * Real.rpow u (-(-(1 / 2 : ℝ)) - 1) at hs
        calc
          _ ≤ Q₁ * Real.rpow u (-(-(1 / 2 : ℝ)) - 1) := hs
          _ = _ := by congr 1; congr 1; ring
      _ = _ := by ring
  have hhead2 :
      (∑ k ∈ Finset.Ico 1 (H + 1),
        leadingMassTerm n M k * (k : ℝ) ^ 2) ≤
      D * n * Q₂ * Real.rpow u (-(3 / 2) : ℝ) := by
    calc
      _ ≤ ∑ k ∈ Finset.Ico 1 (H + 1),
          D * n * (Real.rpow (k : ℝ) (1 / 2 : ℝ) *
            Real.exp (-u * k)) := by
        apply Finset.sum_le_sum
        intro k hk
        have hkpos := (Finset.mem_Ico.mp hk).1
        have hexp : Real.exp (-a * k) ≤ Real.exp (-u * k) :=
          Real.exp_le_exp.mpr (by
            have huA : u ≤ a := min_le_left ..
            nlinarith)
        have hfac : 0 ≤ D * (n : ℝ) * Real.rpow (k : ℝ) (-(3 / 2) : ℝ) :=
          mul_nonneg (mul_nonneg hD.le (by positivity))
            (Real.rpow_nonneg (by positivity) _)
        have hb := (hpoint k hk).trans
          (mul_le_mul_of_nonneg_left hexp hfac)
        have hmul := mul_le_mul_of_nonneg_right hb
          (by positivity : (0 : ℝ) ≤ (k : ℝ) ^ 2)
        calc
          _ ≤ (D * n * Real.rpow (k : ℝ) (-(3 / 2) : ℝ) *
              Real.exp (-u * k)) * (k : ℝ) ^ 2 := hmul
          _ = _ := by rw [← sq_mul_rpow_neg_three_half k hkpos]; ring
      _ = D * n * (∑ k ∈ Finset.Ico 1 (H + 1),
          Real.rpow (k : ℝ) (1 / 2 : ℝ) * Real.exp (-u * k)) := by
        rw [Finset.mul_sum]
      _ ≤ D * n * (Q₂ * Real.rpow u (-(3 / 2) : ℝ)) := by
        gcongr
        have hs := finite_power_exp_sum_le hA hbeta₂ hu hu1 H
        change _ ≤ Q₂ * Real.rpow u (-(1 / 2 : ℝ) - 1) at hs
        calc
          _ ≤ Q₂ * Real.rpow u (-(1 / 2 : ℝ) - 1) := hs
          _ = _ := by congr 1; congr 1; ring
      _ = _ := by ring
  have hzero :
      (∑ k ∈ Finset.Ico 1 (H + 1), leadingMassTerm n M k) ≤
      ∑ k ∈ Finset.Ico 1 (H + 1), leadingMassTerm n M k * k := by
    apply Finset.sum_le_sum
    intro k hk
    have hk1 : 1 ≤ (k : ℝ) := by exact_mod_cast (Finset.mem_Ico.mp hk).1
    have hk0 := leadingMassTerm_nonneg (n := n) (M := M) (k := k) hlam
    calc
      leadingMassTerm n M k = leadingMassTerm n M k * 1 := by ring
      _ ≤ leadingMassTerm n M k * k :=
        mul_le_mul_of_nonneg_left hk1 hk0
  refine ⟨?_, ?_, ?_⟩
  · have hterm : 0 ≤ D * n * Q₂ * Real.rpow u (-(3 / 2) : ℝ) := by
      exact mul_nonneg (mul_nonneg (mul_nonneg hD.le (by positivity)) hQ₂.le)
        (Real.rpow_pos_of_pos hu _).le
    calc
      _ ≤ ∑ k ∈ Finset.Ico 1 (H + 1), leadingMassTerm n M k * k := hzero
      _ ≤ D * n * Q₁ * Real.rpow u (-(1 / 2) : ℝ) := hhead1
      _ ≤ A * n := by
        calc
          _ ≤ D * n * Q₁ * Real.rpow u (-(1 / 2) : ℝ) +
              D * n * Q₂ * Real.rpow u (-(3 / 2) : ℝ) :=
            le_add_of_nonneg_right hterm
          _ = _ := by dsimp [A]; ring
  · have hterm : 0 ≤ D * n * Q₂ * Real.rpow u (-(3 / 2) : ℝ) := by
      exact mul_nonneg (mul_nonneg (mul_nonneg hD.le (by positivity)) hQ₂.le)
        (Real.rpow_pos_of_pos hu _).le
    calc
      _ ≤ D * n * Q₁ * Real.rpow u (-(1 / 2) : ℝ) := hhead1
      _ ≤ A * n := by
        calc
          _ ≤ D * n * Q₁ * Real.rpow u (-(1 / 2) : ℝ) +
              D * n * Q₂ * Real.rpow u (-(3 / 2) : ℝ) :=
            le_add_of_nonneg_right hterm
          _ = _ := by dsimp [A]; ring
  · have hterm : 0 ≤ D * n * Q₁ * Real.rpow u (-(1 / 2) : ℝ) := by
      exact mul_nonneg (mul_nonneg (mul_nonneg hD.le (by positivity)) hQ₁.le)
        (Real.rpow_pos_of_pos hu _).le
    calc
      _ ≤ D * n * Q₂ * Real.rpow u (-(3 / 2) : ℝ) := hhead2
      _ ≤ A * n := by
        calc
          _ ≤ D * n * Q₁ * Real.rpow u (-(1 / 2) : ℝ) +
              D * n * Q₂ * Real.rpow u (-(3 / 2) : ℝ) :=
            le_add_of_nonneg_left hterm
          _ = _ := by dsimp [A]; ring

lemma fixed_cutoff_exp_bound {n H : ℕ} {a B : ℝ}
    (hn : 1 ≤ n) (ha : 0 < a) (hB : 1 / a ≤ B)
    (hlog : 0 ≤ Real.log (n : ℝ))
    (hH : B * Real.log n ≤ (H : ℝ)) :
    (n : ℝ) * Real.exp (-a * H) ≤ 1 := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (Nat.zero_lt_one.trans_le hn)
  have haB : 1 ≤ a * B := by
    have := mul_le_mul_of_nonneg_left hB ha.le
    have hid : a * (1 / a) = 1 := by field_simp
    linarith
  have harg : -(a * (H : ℝ)) ≤ -Real.log n := by
    nlinarith [mul_nonneg ha.le hlog]
  have hExp : Real.exp (-a * H) ≤ Real.exp (-Real.log n) :=
    Real.exp_le_exp.mpr (by simpa only [neg_mul] using! harg)
  have hEq : (n : ℝ) * Real.exp (-Real.log n) = 1 := by
    rw [Real.exp_neg, Real.exp_log hnR]
    field_simp
  nlinarith

lemma fixed_leading_tail_bound {n M H N : ℕ} {D a B : ℝ}
    (hn : 1 ≤ n) (hD : 0 < D) (ha : 0 < a)
    (hB : 1 / a ≤ B) (hlog : 0 ≤ Real.log (n : ℝ))
    (hH : B * Real.log n ≤ (H : ℝ))
    (hpoint : ∀ k ∈ Finset.Ico (H + 1) (N + 1),
      leadingMassTerm n M k ≤ D * n *
        Real.rpow (k : ℝ) (-(3 / 2) : ℝ) * Real.exp (-a * k)) :
    (∑ k ∈ Finset.Ico (H + 1) (N + 1),
      leadingMassTerm n M k) ≤ 3 * D := by
  have hsum := negThreeHalf_exp_tail_le (N := N) (H := H) ha.le
  have hpow : Real.rpow ((H + 1 : ℕ) : ℝ) (-(1 / 2) : ℝ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos
      (by exact_mod_cast (Nat.succ_le_succ (Nat.zero_le H))) (by norm_num)
  have hExp := fixed_cutoff_exp_bound hn ha hB hlog hH
  calc
    _ ≤ ∑ k ∈ Finset.Ico (H + 1) (N + 1),
        D * n * (Real.rpow (k : ℝ) (-(3 / 2) : ℝ) *
          Real.exp (-a * k)) := by
        apply Finset.sum_le_sum
        intro k hk
        simpa [mul_assoc] using! hpoint k hk
    _ = D * n *
        (∑ k ∈ Finset.Ico (H + 1) (N + 1),
          Real.rpow (k : ℝ) (-(3 / 2) : ℝ) *
            Real.exp (-a * k)) := by rw [Finset.mul_sum]
    _ ≤ D * n *
        (3 * Real.rpow ((H + 1 : ℕ) : ℝ) (-(1 / 2) : ℝ) *
          Real.exp (-a * H)) := by gcongr
    _ ≤ 3 * D := by
      have hfac : 0 ≤ Real.rpow ((H + 1 : ℕ) : ℝ) (-(1 / 2) : ℝ) :=
        Real.rpow_nonneg (by positivity) _
      nlinarith [mul_nonneg hD.le hfac]

end
end Erdos745.WrapUp.Proofs.Internal.W09_TREE_MASS_FixedSums
