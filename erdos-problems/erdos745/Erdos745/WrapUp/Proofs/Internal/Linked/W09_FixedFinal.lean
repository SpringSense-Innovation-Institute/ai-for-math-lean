module

public import Erdos745.WrapUp.Proofs.Internal.Linked.W09_FixedLocal

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local simp] Pi.div_def Pi.mul_def Pi.add_def Pi.sub_def Pi.neg_def Pi.inv_def Function.comp_def Pi.pow_def Pi.smul_def Real.rpow_eq_pow

@[expose] public section


namespace Erdos745.WrapUp.Proofs.Internal.W09_TREE_MASS_FixedMean

noncomputable section
open Filter
open scoped BigOperators Topology
open Erdos745.WrapUp.Proofs.W06_POISSON
open Erdos745.WrapUp.Proofs.Internal.W09_TREE_MASS_Finite
open Erdos745.WrapUp.Proofs.Internal.W09_TREE_MASS_Analytic
open Erdos745.WrapUp.Proofs.Internal.W09_TREE_MASS_FixedCutoff
open Erdos745.WrapUp.Proofs.Internal.W09_TREE_MASS_FixedTail
open Erdos745.WrapUp.Proofs.Internal.W09_TREE_MASS_FixedLocal
open Erdos745.WrapUp.Proofs.Internal.W09_TREE_MASS_FixedSums

private lemma finite_head_series_error
    {f g : ℕ → ℝ} {H h : ℕ} {z L A D : ℝ}
    (hseries : HasSum g z) (hgzero : g 0 = 0)
    (hg : ∀ k, 0 ≤ g k) (hf : ∀ k, 0 ≤ f k)
    (hH : H + 1 ≤ h)
    (hlocal : (∑ k ∈ Finset.Ico 1 (H + 1), |f k - g k|) ≤ L)
    (hactual : (∑ k ∈ Finset.Ico (H + 1) h, f k) ≤ A)
    (hleading : ∀ N : ℕ,
      (∑ k ∈ Finset.Ico (H + 1) (N + 1), g k) ≤ D) :
    |(∑ k ∈ Finset.Ico 1 h, f k) - z| ≤ L + A + D := by
  let head := ∑ k ∈ Finset.Ico 1 (H + 1), g k
  have hprefix : ∀ N : ℕ,
      (∑ k ∈ Finset.Ico 1 N, g k) = ∑ k ∈ Finset.range N, g k := by
    intro N
    by_cases hN : 1 ≤ N
    · have hs := Finset.sum_Ico_consecutive g (m := 0) (n := 1) (k := N)
        (by omega) hN
      have hzero : (∑ k ∈ Finset.Ico 0 1, g k) = 0 := by simp [hgzero]
      rw [Finset.range_eq_Ico]
      simpa only [hzero, zero_add] using! hs
    · have hN0 : N = 0 := by omega
      subst N
      simp
  have hfull : Tendsto (fun N : ℕ => ∑ k ∈ Finset.Ico 1 N, g k)
      atTop (𝓝 z) := by
    simpa only [hprefix] using! hseries.tendsto_sum_nat
  have hhead_le : head ≤ z := by
    rw [← hseries.tsum_eq]
    exact hseries.summable.sum_le_tsum (Finset.Ico 1 (H + 1))
      (fun k _ => hg k)
  have hz_le : z ≤ head + D := by
    apply le_of_tendsto hfull
    filter_upwards [eventually_ge_atTop (H + 1)] with N hN
    have htail : (∑ k ∈ Finset.Ico (H + 1) N, g k) ≤ D := by
      have hsubset : Finset.Ico (H + 1) N ⊆
          Finset.Ico (H + 1) (N + 1) :=
        Finset.Ico_subset_Ico_right (Nat.le_succ N)
      exact (Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun k _ _ => hg k)).trans (hleading N)
    have hs := Finset.sum_Ico_consecutive g (m := 1) (n := H + 1)
      (k := N) (by omega) hN
    dsimp [head] at *
    linarith
  have hhead_diff :
      |(∑ k ∈ Finset.Ico 1 (H + 1), f k) - head| ≤ L := by
    calc
      _ = |∑ k ∈ Finset.Ico 1 (H + 1), (f k - g k)| := by
        simp only [Finset.sum_sub_distrib, head]
      _ ≤ ∑ k ∈ Finset.Ico 1 (H + 1), |f k - g k| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ L := hlocal
  have hactual_nonneg : 0 ≤ ∑ k ∈ Finset.Ico (H + 1) h, f k :=
    Finset.sum_nonneg (fun k _ => hf k)
  have hsplit := Finset.sum_Ico_consecutive f (m := 1) (n := H + 1)
    (k := h) (by omega) hH
  rw [← hsplit]
  have hdiff := abs_sub_le_iff.mp hhead_diff
  apply abs_sub_le_iff.mpr
  constructor <;> dsimp [head] at * <;> linarith

lemma fixed_mean_boundedBy
    (hRate : RateStatement) (hT : TupleEstimatesStatement)
    (hA : AnalyticSumsStatement) {M : NatSeq} {lam : ℝ}
    (hadm : admissible M) (hlam : 1 < lam)
    (hdeg : Tendsto (degree M) atTop (𝓝 lam)) :
    boundedBy (treeMeanError M) (fun _ => 1) := by
  obtain ⟨lo, hi, delta, a, B, hlo, hlohi, hdelta, ha, hB, hBa,
    hcommon⟩ := fixed_common_cutoff hRate hT hadm hlam hdeg
  obtain ⟨C₁, hC₁, n₁, hlocal₁⟩ := hT.2.2.1 lo hi (B + 1) 1
    hlo hlohi (by linarith) (by omega)
  obtain ⟨D, hD, hDpoint⟩ := leadingMassTerm_bound
  let A := fixedSumConstant hA D a
  have hApos := fixedSumConstant_pos hA hD ha
  have hsmall := fixed_log_sq_over_n_eventually (B + 1) C₁
  have hsuper : ∀ᶠ n in atTop, 1 < degree M n :=
    ((tendsto_order.1 hdeg).1 1 hlam).mono fun _ h => h
  have hhalf : ∀ᶠ n in atTop, 1 / 2 ≤ degree M n :=
    ((tendsto_order.1 hdeg).1 (1 / 2) (by linarith)).mono fun _ h => h.le
  have hnlarge : ∀ᶠ n : ℕ in atTop, 1 ≤ n := eventually_ge_atTop 1
  refine ⟨2 * C₁ * A + 3 * D + 1, by positivity, ?_⟩
  filter_upwards [hcommon, hsmall, hsuper, hhalf, hnlarge,
    Erdos745.WrapUp.Proofs.Internal.W08_CYCLIC_Cutoff.cutoff_geometry,
    eventually_ge_atTop n₁] with n hc hs hsupern hhalfn hn hgeom hn₁
  obtain ⟨hcap, hloN, hhiN, haN, hsepN, hlog, hHpos,
    hHn, hHlarge, hHlog, ht₁₁, ht₁₂, ht₂₁⟩ := hc
  let H := logCutoff B n
  have hlargeN : largeCutoff n ≤ n + 1 := by
    by_cases hz : largeCutoff n = 0
    · omega
    · have hpos : 0 < largeCutoff n := Nat.pos_of_ne_zero hz
      have hlt : largeCutoff n - 1 < largeCutoff n := Nat.sub_lt hpos (by omega)
      have hh := (hgeom.2 (largeCutoff n - 1) hlt).1
      omega
  have hHle : B * Real.log n ≤ (H : ℝ) := Nat.le_ceil _
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hlamN : 0 < degreeAt n (M n) := by
    simpa [degree, degreeAt] using! (zero_lt_one.trans hsupern)
  have hhalfN : 1 / 2 ≤ degreeAt n (M n) := by
    simpa [degree, degreeAt] using! hhalfn
  have hlocalPoint : ∀ k ∈ Finset.Ico 1 (H + 1),
      |massTerm n (M n) k - leadingMassTerm n (M n) k| ≤
        2 * C₁ * leadingMassTerm n (M n) k * (k : ℝ) ^ 2 / n := by
    intro k hk
    have hkpos := (Finset.mem_Ico.mp hk).1
    have hkH : k ≤ H := by
      have hkhi := (Finset.mem_Ico.mp hk).2
      omega
    have hklog : (k : ℝ) ≤ (B + 1) * Real.log n := by
      exact (by exact_mod_cast hkH : (k : ℝ) ≤ (H : ℝ)).trans hHlog
    have hloc := hlocal₁ n (M n) (fun _ => k) hn₁ hcap
      (by simpa [degree, degreeAt] using! hloN)
      (by simpa [degree, degreeAt] using! hhiN)
      (fun _ => hkpos) (by simpa using! hklog)
    have hsmallk : C₁ * (k : ℝ) ^ 2 / n ≤ 1 := by
      calc
        _ ≤ C₁ * ((B + 1) * Real.log n) ^ 2 / n := by gcongr
        _ ≤ 1 := hs
    have hlogk : |Real.log (momentOne n (M n) k /
        treeLeading n (M n) k)| ≤ C₁ * (k : ℝ) ^ 2 / n := by
      simpa [tupleLeading, momentOne, Fin.sum_univ_one] using! hloc.2
    exact fixed_one_relative hkpos hlamN hloc.1 hlogk hsmallk
  have hleadPoint : ∀ k ∈ Finset.Ico 1 (H + 1),
      leadingMassTerm n (M n) k ≤ D * n *
        Real.rpow (k : ℝ) (-(3 / 2) : ℝ) * Real.exp (-a * k) := by
    intro k hk
    exact fixed_leading_mass_bound (Finset.mem_Ico.mp hk).1 hhalfN
      (by simpa [degree, degreeAt] using! haN) ha hD.le hDpoint
  have hsums := fixed_power_sums hA (by omega) hD ha hlamN hleadPoint
  have hlocalSum :
      (∑ k ∈ Finset.Ico 1 (H + 1),
        |massTerm n (M n) k - leadingMassTerm n (M n) k|) ≤
        2 * C₁ * A := by
    calc
      _ ≤ ∑ k ∈ Finset.Ico 1 (H + 1),
          2 * C₁ * leadingMassTerm n (M n) k * (k : ℝ) ^ 2 / n :=
        Finset.sum_le_sum hlocalPoint
      _ = 2 * C₁ / n *
          (∑ k ∈ Finset.Ico 1 (H + 1),
            leadingMassTerm n (M n) k * (k : ℝ) ^ 2) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        ring
      _ ≤ 2 * C₁ / n * (A * n) :=
        mul_le_mul_of_nonneg_left hsums.2.2 (by positivity)
      _ = 2 * C₁ * A := by field_simp
  have hactual :
      (∑ k ∈ Finset.Ico (H + 1) (largeCutoff n),
        massTerm n (M n) k) ≤ 1 := by
    have htail := fixed_actual_mean_tail_bound
      (n := n) (M := M n) (H := H) (N := largeCutoff n)
      hlargeN hHle ht₁₁
    have hpow : Real.rpow (n : ℝ) (-2 : ℝ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hn) (by norm_num)
    exact htail.trans hpow
  have hleadTail : ∀ N : ℕ,
      (∑ k ∈ Finset.Ico (H + 1) (N + 1),
        leadingMassTerm n (M n) k) ≤ 3 * D := by
    intro N
    apply fixed_leading_tail_bound hn hD ha
      ((div_le_div_of_nonneg_right (by norm_num) ha.le).trans hBa)
      (by linarith) hHle
    intro k hk
    exact fixed_leading_mass_bound (by
      have hklo := (Finset.mem_Ico.mp hk).1
      omega) hhalfN
      (by simpa [degree, degreeAt] using! haN) ha hD.le hDpoint
  have hseries := leadingMassTerm_hasSum hA hsupern
  have hbridge := finite_head_series_error
    (f := massTerm n (M n)) (g := leadingMassTerm n (M n))
    (H := H) (h := largeCutoff n)
    (L := 2 * C₁ * A) (A := 1) (D := 3 * D)
    hseries (by simp [leadingMassTerm])
    (fun k => leadingMassTerm_nonneg hlamN)
    (fun k => massTerm_nonneg n (M n) k)
    (by omega) hlocalSum hactual hleadTail
  have hmean : |treeMeanError M n| ≤ 2 * C₁ * A + 1 + 3 * D := by
    simpa [treeMeanError, expect_treeMassBelow, massTerm, degree, degreeAt]
      using! hbridge
  simpa only [mul_one] using! (show
    |treeMeanError M n| ≤ (2 * C₁ * A + 3 * D + 1) * 1 by
      dsimp [A] at *
      linarith)

end
end Erdos745.WrapUp.Proofs.Internal.W09_TREE_MASS_FixedMean


namespace Erdos745.WrapUp.Proofs.Internal.W09_TREE_MASS_FixedVariance

noncomputable section
open Filter
open scoped BigOperators Topology
open Erdos745.WrapUp.Proofs.W06_POISSON
open Erdos745.WrapUp.Proofs.Internal.W09_TREE_MASS_Finite
open Erdos745.WrapUp.Proofs.Internal.W09_TREE_MASS_Analytic
open Erdos745.WrapUp.Proofs.Internal.W09_TREE_MASS_FixedCutoff
open Erdos745.WrapUp.Proofs.Internal.W09_TREE_MASS_FixedTail
open Erdos745.WrapUp.Proofs.Internal.W09_TREE_MASS_FixedLocal
open Erdos745.WrapUp.Proofs.Internal.W09_TREE_MASS_FixedSums

private lemma double_sum_mul (s : Finset ℕ) (f g : ℕ → ℝ) :
    (∑ k ∈ s, ∑ l ∈ s, f k * g l) =
      (∑ k ∈ s, f k) * (∑ l ∈ s, g l) := by
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mul_sum]

private lemma fixed_covariance_sum_algebra (s : Finset ℕ) (b : ℕ → ℝ) :
    (∑ k ∈ s, ∑ l ∈ s,
      b k * b l * ((k : ℝ) + l) ^ 2) =
    2 * (∑ k ∈ s, b k) * (∑ k ∈ s, b k * (k : ℝ) ^ 2) +
      2 * (∑ k ∈ s, b k * k) ^ 2 := by
  have h₁ := double_sum_mul s (fun k => b k * (k : ℝ) ^ 2) b
  have h₂ := double_sum_mul s b (fun l => b l * (l : ℝ) ^ 2)
  have h₃ := double_sum_mul s (fun k => b k * k) (fun l => b l * l)
  have hterm (k l : ℕ) :
      b k * b l * ((k : ℝ) + l) ^ 2 =
        (b k * (k : ℝ) ^ 2) * b l +
          b k * (b l * (l : ℝ) ^ 2) +
          2 * ((b k * k) * (b l * l)) := by ring
  have hrewrite :
      (∑ k ∈ s, ∑ l ∈ s,
        b k * b l * ((k : ℝ) + l) ^ 2) =
      (∑ k ∈ s, ∑ l ∈ s, (b k * (k : ℝ) ^ 2) * b l) +
      (∑ k ∈ s, ∑ l ∈ s, b k * (b l * (l : ℝ) ^ 2)) +
      2 * (∑ k ∈ s, ∑ l ∈ s, (b k * k) * (b l * l)) := by
    simp_rw [hterm, Finset.sum_add_distrib, Finset.mul_sum]
  rw [hrewrite, h₁, h₂, h₃]
  ring

private lemma fixed_variance_from_sums {n M H : ℕ} {A C : ℝ}
    (hn : 0 < n) (hA : 0 < A) (hC : 0 ≤ C)
    (hnorm : expectM n M (fun _ => 1) = 1)
    (hsums :
      (∑ k ∈ Finset.Ico 1 (H + 1), leadingMassTerm n M k) ≤ A * n ∧
      (∑ k ∈ Finset.Ico 1 (H + 1), leadingMassTerm n M k * k) ≤ A * n ∧
      (∑ k ∈ Finset.Ico 1 (H + 1),
        leadingMassTerm n M k * (k : ℝ) ^ 2) ≤ A * n)
    (hupper : ∀ k ∈ Finset.Ico 1 (H + 1),
      massTerm n M k ≤ 3 * leadingMassTerm n M k)
    (hcov : ∀ k ∈ Finset.Ico 1 (H + 1),
      ∀ l ∈ Finset.Ico 1 (H + 1),
      (k : ℝ) * l * momentTwo n M k l -
        massTerm n M k * massTerm n M l ≤
        C * leadingMassTerm n M k * leadingMassTerm n M l *
          ((k : ℝ) + l) ^ 2 / n)
    (hlead : ∀ k ∈ Finset.Ico 1 (H + 1),
      0 ≤ leadingMassTerm n M k) :
    varianceM n M (fun G => treeMassSum G (Finset.Ico 1 (H + 1))) ≤
      (3 * A + 4 * C * A ^ 2) * n := by
  let s := Finset.Ico 1 (H + 1)
  let S₀ := ∑ k ∈ s, leadingMassTerm n M k
  let S₁ := ∑ k ∈ s, leadingMassTerm n M k * k
  let S₂ := ∑ k ∈ s, leadingMassTerm n M k * (k : ℝ) ^ 2
  have hS₀ : S₀ ≤ A * n := hsums.1
  have hS₁ : S₁ ≤ A * n := hsums.2.1
  have hS₂ : S₂ ≤ A * n := hsums.2.2
  have hS₀nonneg : 0 ≤ S₀ := Finset.sum_nonneg (fun k hk => hlead k hk)
  have hS₁nonneg : 0 ≤ S₁ := Finset.sum_nonneg (fun k hk =>
    mul_nonneg (hlead k hk) (by positivity))
  have hS₂nonneg : 0 ≤ S₂ := Finset.sum_nonneg (fun k hk =>
    mul_nonneg (hlead k hk) (sq_nonneg _))
  have hdiag :
      (∑ k ∈ s, (k : ℝ) ^ 2 * momentOne n M k) ≤ 3 * A * n := by
    calc
      _ = ∑ k ∈ s, massTerm n M k * k := by
        apply Finset.sum_congr rfl
        intro k hk
        simp [massTerm]
        ring
      _ ≤ ∑ k ∈ s, 3 * leadingMassTerm n M k * k := by
        apply Finset.sum_le_sum
        intro k hk
        exact mul_le_mul_of_nonneg_right (hupper k hk) (by positivity)
      _ = 3 * S₁ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        ring
      _ ≤ 3 * A * n := by nlinarith
  have hcovsum :
      (∑ k ∈ s, ∑ l ∈ s,
        ((k : ℝ) * l * momentTwo n M k l -
          massTerm n M k * massTerm n M l)) ≤
      C / n * (2 * S₀ * S₂ + 2 * S₁ ^ 2) := by
    calc
      _ ≤ ∑ k ∈ s, ∑ l ∈ s,
        C / n * (leadingMassTerm n M k * leadingMassTerm n M l *
          ((k : ℝ) + l) ^ 2) := by
        apply Finset.sum_le_sum
        intro k hk
        apply Finset.sum_le_sum
        intro l hl
        convert hcov k hk l hl using 1; ring
      _ = C / n *
          (∑ k ∈ s, ∑ l ∈ s,
            leadingMassTerm n M k * leadingMassTerm n M l *
              ((k : ℝ) + l) ^ 2) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        rw [Finset.mul_sum]
      _ = _ := by rw [fixed_covariance_sum_algebra]
  have hprod₀₂ : S₀ * S₂ ≤ (A * n) ^ 2 :=
    (mul_le_mul hS₀ hS₂ hS₂nonneg (by positivity)).trans_eq (by ring)
  have hprod₁₁ : S₁ ^ 2 ≤ (A * n) ^ 2 := by nlinarith
  have hcovfinal :
      C / n * (2 * S₀ * S₂ + 2 * S₁ ^ 2) ≤
      4 * C * A ^ 2 * n := by
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    have hmain : 2 * S₀ * S₂ + 2 * S₁ ^ 2 ≤ 4 * (A * n) ^ 2 := by
      nlinarith [hprod₀₂, hprod₁₁]
    have hmul := mul_le_mul_of_nonneg_left hmain (div_nonneg hC hnR.le)
    have hn0 : (n : ℝ) ≠ 0 := hnR.ne'
    calc
      _ ≤ C / n * (4 * (A * n) ^ 2) := hmul
      _ = 4 * C * A ^ 2 * n := by field_simp
  rw [variance_treeMassSum_eq s hnorm]
  calc
    (∑ k ∈ s, (k : ℝ) ^ 2 * momentOne n M k) +
        (∑ k ∈ s, ∑ l ∈ s,
          ((k : ℝ) * l * momentTwo n M k l -
            massTerm n M k * massTerm n M l)) ≤
        3 * A * n + 4 * C * A ^ 2 * n := by
          exact add_le_add hdiag (hcovsum.trans hcovfinal)
    _ = _ := by ring

lemma fixed_variance_boundedBy
    (hF : FiniteEnumerationStatement) (hRate : RateStatement)
    (hT : TupleEstimatesStatement) (hA : AnalyticSumsStatement)
    {M : NatSeq} {lam : ℝ} (hadm : admissible M)
    (hlam : 1 < lam) (hdeg : Tendsto (degree M) atTop (𝓝 lam)) :
    boundedBy (fun n => varianceM n (M n)
      (fun G => treeMassBelow G (largeCutoff n))) (fun n => (n : ℝ)) := by
  obtain ⟨lo, hi, delta, a, B, hlo, hlohi, hdelta, ha, hB, hBa,
    hcommon⟩ := fixed_common_cutoff hRate hT hadm hlam hdeg
  obtain ⟨C₁, hC₁, n₁, hlocal₁⟩ := hT.2.2.1 lo hi (B + 1) 1
    hlo hlohi (by linarith) (by omega)
  obtain ⟨C₂, hC₂, n₂, hlocal₂⟩ := hT.2.2.1 lo hi (2 * (B + 1)) 2
    hlo hlohi (by positivity) (by omega)
  obtain ⟨D, hD, hDpoint⟩ := leadingMassTerm_bound
  let A := fixedSumConstant hA D a
  let C := 2 * C₂ + 8 * C₁
  have hApos := fixedSumConstant_pos hA hD ha
  have hCpos : 0 < C := by dsimp [C]; positivity
  have hsmall₁ := fixed_log_sq_over_n_eventually (B + 1) C₁
  have hsmall₂ := fixed_log_sq_over_n_eventually (2 * (B + 1)) C₂
  have hsuper : ∀ᶠ n in atTop, 1 < degree M n :=
    ((tendsto_order.1 hdeg).1 1 hlam).mono fun _ h => h
  have hhalf : ∀ᶠ n in atTop, 1 / 2 ≤ degree M n :=
    ((tendsto_order.1 hdeg).1 (1 / 2) (by linarith)).mono fun _ h => h.le
  refine ⟨2 * (3 * A + 4 * C * A ^ 2) + 4, by positivity, ?_⟩
  filter_upwards [hcommon, hsmall₁, hsmall₂, hsuper, hhalf,
    Erdos745.WrapUp.Proofs.Internal.W08_CYCLIC_Cutoff.cutoff_geometry,
    eventually_ge_atTop (max 1 (max n₁ n₂))]
    with n hc hsmall₁n hsmall₂n hsupern hhalfn hgeom hn₀
  obtain ⟨hcap, hloN, hhiN, haN, hsepN, hlog, hHpos,
    hHn, hHlarge, hHlog, ht₁₁, ht₁₂, ht₂₁⟩ := hc
  have hn : 0 < n := by omega
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hn₁ : n₁ ≤ n := by omega
  have hn₂ : n₂ ≤ n := by omega
  let H := logCutoff B n
  have hlargeN : largeCutoff n ≤ n + 1 := by
    by_cases hz : largeCutoff n = 0
    · omega
    · have hpos : 0 < largeCutoff n := Nat.pos_of_ne_zero hz
      have hlt : largeCutoff n - 1 < largeCutoff n := Nat.sub_lt hpos (by omega)
      have hh := (hgeom.2 (largeCutoff n - 1) hlt).1
      omega
  let s := Finset.Ico 1 (H + 1)
  have hHle : B * Real.log n ≤ (H : ℝ) := Nat.le_ceil _
  have hlamN : 0 < degreeAt n (M n) := by
    simpa [degree, degreeAt] using! (zero_lt_one.trans hsupern)
  have hhalfN : 1 / 2 ≤ degreeAt n (M n) := by
    simpa [degree, degreeAt] using! hhalfn
  have hloN' : lo ≤ degreeAt n (M n) := by simpa [degree, degreeAt] using! hloN
  have hhiN' : degreeAt n (M n) ≤ hi := by simpa [degree, degreeAt] using! hhiN
  have hleadPoint : ∀ k ∈ s,
      leadingMassTerm n (M n) k ≤ D * n *
        Real.rpow (k : ℝ) (-(3 / 2) : ℝ) * Real.exp (-a * k) := by
    intro k hk
    exact fixed_leading_mass_bound (Finset.mem_Ico.mp hk).1 hhalfN
      (by simpa [degree, degreeAt] using! haN) ha hD.le hDpoint
  have hsums := fixed_power_sums hA hn hD ha hlamN hleadPoint
  have hlocalOne : ∀ k ∈ s,
      0 < momentOne n (M n) k ∧
      |Real.log (momentOne n (M n) k /
        treeLeading n (M n) k)| ≤ C₁ * (k : ℝ) ^ 2 / n ∧
      C₁ * (k : ℝ) ^ 2 / n ≤ 1 := by
    intro k hk
    have hkpos := (Finset.mem_Ico.mp hk).1
    have hkH : k ≤ H := by
      have hkhi := (Finset.mem_Ico.mp hk).2
      omega
    have hklog : (k : ℝ) ≤ (B + 1) * Real.log n :=
      (by exact_mod_cast hkH : (k : ℝ) ≤ (H : ℝ)).trans hHlog
    have hloc := hlocal₁ n (M n) (fun _ => k) hn₁ hcap hloN' hhiN'
      (fun _ => hkpos) (by simpa using! hklog)
    have hlogk : |Real.log (momentOne n (M n) k /
        treeLeading n (M n) k)| ≤ C₁ * (k : ℝ) ^ 2 / n := by
      simpa [tupleLeading, momentOne, Fin.sum_univ_one] using! hloc.2
    have hsmallk : C₁ * (k : ℝ) ^ 2 / n ≤ 1 := by
      calc
        _ ≤ C₁ * ((B + 1) * Real.log n) ^ 2 / n := by gcongr
        _ ≤ 1 := hsmall₁n
    exact ⟨hloc.1, hlogk, hsmallk⟩
  have hupper : ∀ k ∈ s,
      massTerm n (M n) k ≤ 3 * leadingMassTerm n (M n) k := by
    intro k hk
    exact fixed_one_upper (Finset.mem_Ico.mp hk).1 hlamN
      (hlocalOne k hk).1 (hlocalOne k hk).2.1 (hlocalOne k hk).2.2
  have hcov : ∀ k ∈ s, ∀ l ∈ s,
      (k : ℝ) * l * momentTwo n (M n) k l -
        massTerm n (M n) k * massTerm n (M n) l ≤
        C * leadingMassTerm n (M n) k * leadingMassTerm n (M n) l *
          ((k : ℝ) + l) ^ 2 / n := by
    intro k hk l hl
    have hkpos := (Finset.mem_Ico.mp hk).1
    have hlpos := (Finset.mem_Ico.mp hl).1
    have hkH : k ≤ H := by
      have hkhi := (Finset.mem_Ico.mp hk).2
      omega
    have hlH : l ≤ H := by
      have hlhi := (Finset.mem_Ico.mp hl).2
      omega
    have hsum : (k : ℝ) + l ≤ 2 * (B + 1) * Real.log n := by
      have hkr : (k : ℝ) ≤ (H : ℝ) := by exact_mod_cast hkH
      have hlr : (l : ℝ) ≤ (H : ℝ) := by exact_mod_cast hlH
      nlinarith
    have hloc₂ := hlocal₂ n (M n) (pairSizes k l) hn₂ hcap
      hloN' hhiN'
      (by
        intro i
        fin_cases i
        · simpa [pairSizes] using! hkpos
        · simpa [pairSizes] using! hlpos)
      (by simpa [pairSizes, Fin.sum_univ_two] using! hsum)
    have hlog₂ : |Real.log (momentTwo n (M n) k l /
        (treeLeading n (M n) k * treeLeading n (M n) l))| ≤
        C₂ * ((k : ℝ) + l) ^ 2 / n := by
      simpa [momentTwo, pairLeading_eq, pairSizes, Fin.sum_univ_two]
        using! hloc₂.2
    have hsmall₂ : C₂ * ((k : ℝ) + l) ^ 2 / n ≤ 1 := by
      calc
        _ ≤ C₂ * (2 * (B + 1) * Real.log n) ^ 2 / n := by gcongr
        _ ≤ 1 := hsmall₂n
    exact fixed_covariance_le hkpos hlpos hlamN hC₁.le hC₂.le
      (hlocalOne k hk).1 (hlocalOne l hl).1 hloc₂.1
      (hlocalOne k hk).2.1 (hlocalOne l hl).2.1 hlog₂
      (hlocalOne k hk).2.2 (hlocalOne l hl).2.2 hsmall₂
  have hhead := fixed_variance_from_sums hn hApos hCpos.le
    (hF.1 n (M n) hcap) hsums hupper hcov
    (fun k hk => leadingMassTerm_nonneg hlamN)
  have htail := fixed_discarded_second_bound
    (n := n) (M := M n) (H := H) (N := largeCutoff n)
    hlargeN hHle ht₁₂ ht₂₁
  let U := fun G : Graph n => treeMassSum G s
  let V := fun G : Graph n =>
    treeMassSum G (Finset.Ico (H + 1) (largeCutoff n))
  have hsplit : (fun G : Graph n => treeMassBelow G (largeCutoff n)) =
      fun G => U G + V G := by
    funext G
    exact treeMassBelow_split G (by omega)
  have hV := variance_le_second V (hF.1 n (M n) hcap)
  have hnonneg := variance_nonneg (n := n) (M := M n)
    (fun G => treeMassBelow G (largeCutoff n))
  have hpow : Real.rpow (n : ℝ) (-2 : ℝ) ≤ (n : ℝ) := by
    have hnOne : (1 : ℝ) ≤ n := by
      exact_mod_cast (show 1 ≤ n by omega)
    have hle1 := Real.rpow_le_one_of_one_le_of_nonpos
      hnOne (by norm_num : (-2 : ℝ) ≤ 0)
    exact hle1.trans hnOne
  have hmain : varianceM n (M n)
      (fun G => treeMassBelow G (largeCutoff n)) ≤
      (2 * (3 * A + 4 * C * A ^ 2) + 4) * n := by
    rw [hsplit]
    calc
      varianceM n (M n) (fun G => U G + V G) ≤
          2 * varianceM n (M n) U + 2 * varianceM n (M n) V :=
        variance_add_le U V
      _ ≤ 2 * ((3 * A + 4 * C * A ^ 2) * n) +
          2 * (2 * Real.rpow (n : ℝ) (-2 : ℝ)) := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left (by simpa [U, s] using! hhead) (by norm_num)
        · exact mul_le_mul_of_nonneg_left
            (hV.trans (by simpa [V] using! htail)) (by norm_num)
      _ ≤ (2 * (3 * A + 4 * C * A ^ 2) + 4) * n := by nlinarith
  rw [abs_of_nonneg hnonneg]
  exact hmain

end
end Erdos745.WrapUp.Proofs.Internal.W09_TREE_MASS_FixedVariance
