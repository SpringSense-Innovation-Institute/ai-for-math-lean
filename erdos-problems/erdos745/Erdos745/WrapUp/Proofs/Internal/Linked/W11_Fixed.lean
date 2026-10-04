module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Erdos745.WrapUp.Proofs.Internal.Linked.W06_P02
public import Erdos745.WrapUp.Contracts
public import Erdos745.WrapUp.Proofs.Internal.Linked.W10_Core

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local simp] Pi.div_def Pi.mul_def Pi.add_def Pi.sub_def Pi.neg_def Pi.inv_def Function.comp_def Pi.pow_def Pi.smul_def Real.rpow_eq_pow

@[expose] public section


namespace Erdos745.WrapUp.Proofs.Internal.W11_FIXED_Analytic

open Erdos745.WrapUp
open Filter Set
open scoped Topology

noncomputable section

open Erdos745.WrapUp.Proofs.W06_POISSON

lemma poissonCDF_zero (nu : ℝ) :
    poissonCDF nu 0 = Real.exp (-nu) := by
  simp [poissonCDF]

lemma poissonCDF_one (nu : ℝ) :
    poissonCDF nu 1 = Real.exp (-nu) * (1 + nu) := by
  norm_num [poissonCDF, Finset.sum_range_succ]

lemma poissonCDF_zero_antitone : Antitone (fun nu : ℝ ↦ poissonCDF nu 0) := by
  intro x y hxy
  change poissonCDF y 0 ≤ poissonCDF x 0
  rw [poissonCDF_zero, poissonCDF_zero]
  exact Real.exp_le_exp.mpr (neg_le_neg hxy)

private lemma poisson_one_hasDerivAt (x : ℝ) :
    HasDerivAt (fun nu : ℝ ↦ Real.exp (-nu) * (1 + nu))
      (-x * Real.exp (-x)) x := by
  convert (((Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_id x).neg).mul
    ((hasDerivAt_const x 1).add (hasDerivAt_id x))) using 1 <;>
      simp [Function.comp_apply] <;> ring

lemma poissonCDF_one_antitoneOn :
    AntitoneOn (fun nu : ℝ ↦ poissonCDF nu 1) (Set.Ici 0) := by
  rw [show (fun nu : ℝ ↦ poissonCDF nu 1) =
      (fun nu : ℝ ↦ Real.exp (-nu) * (1 + nu)) by
    funext nu
    exact poissonCDF_one nu]
  apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
  · exact (Real.continuous_exp.comp continuous_neg).mul
      (continuous_const.add continuous_id) |>.continuousOn
  · intro x _
    exact (poisson_one_hasDerivAt x).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    rw [(poisson_one_hasDerivAt x).deriv]
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hx.le) (Real.exp_pos _).le

lemma poissonCDF_zero_one_antitoneOn (q : ℕ) (hq : q ≤ 1) :
    AntitoneOn (fun nu : ℝ ↦ poissonCDF nu q) (Set.Ici 0) := by
  interval_cases q
  · exact poissonCDF_zero_antitone.antitoneOn _
  · exact poissonCDF_one_antitoneOn

private def latticeCoefficient (lam : ℝ) : ℝ :=
  Real.rpow (rate lam) (5 / 2 : ℝ) /
    (lam * Real.sqrt (2 * Real.pi) * (1 - Real.exp (-rate lam)))

private lemma latticeCoefficient_pos (hRate : RateStatement) (lam : ℝ)
    (hlam : 0 < lam) (hlam1 : lam ≠ 1) :
    0 < latticeCoefficient lam := by
  have ha : 0 < rate lam := hRate.1 lam hlam hlam1
  have hexp : Real.exp (-rate lam) < 1 :=
    Real.exp_lt_one_iff.mpr (by linarith)
  unfold latticeCoefficient
  exact div_pos (Real.rpow_pos_of_pos ha _)
    (mul_pos (mul_pos hlam (by positivity)) (sub_pos.mpr hexp))

private lemma latticeRate_eq_coefficient (lam ell : ℝ) :
    latticeRate lam ell = latticeCoefficient lam * Real.exp (-rate lam * ell) := by
  rw [latticeRate, latticeCoefficient]
  ring

lemma latticeRate_antitone (hRate : RateStatement) (lam : ℝ)
    (hlam : 0 < lam) (hlam1 : lam ≠ 1) :
    Antitone (latticeRate lam) := by
  intro x y hxy
  rw [latticeRate_eq_coefficient, latticeRate_eq_coefficient]
  apply mul_le_mul_of_nonneg_left _ (latticeCoefficient_pos hRate lam hlam hlam1).le
  apply Real.exp_le_exp.mpr
  have ha := hRate.1 lam hlam hlam1
  nlinarith

private lemma latticeRate_left_tendsto_atTop (hRate : RateStatement) (lam : ℝ)
    (hlam : 0 < lam) (hlam1 : lam ≠ 1) :
    Tendsto (fun K : ℝ ↦ latticeRate lam (1 - K)) atTop atTop := by
  have ha : 0 < rate lam := hRate.1 lam hlam hlam1
  have hlin : Tendsto (fun K : ℝ ↦ -rate lam * (1 - K)) atTop atTop := by
    have h := tendsto_id.atTop_mul_const ha
    have h' : Tendsto (fun K : ℝ ↦ K * rate lam - rate lam) atTop atTop := by
      simpa [sub_eq_add_neg] using!
        tendsto_atTop_add_const_right atTop (-rate lam) h
    apply h'.congr'
    filter_upwards with K
    ring
  have hexp := Real.tendsto_exp_atTop.comp hlin
  rw [show (fun K : ℝ ↦ latticeRate lam (1 - K)) =
      (fun K ↦ latticeCoefficient lam * Real.exp (-rate lam * (1 - K))) by
    funext K
    exact latticeRate_eq_coefficient lam (1 - K)]
  exact hexp.const_mul_atTop (latticeCoefficient_pos hRate lam hlam hlam1)

private lemma latticeRate_right_tendsto_zero (hRate : RateStatement) (lam : ℝ)
    (hlam : 0 < lam) (hlam1 : lam ≠ 1) :
    Tendsto (fun K : ℝ ↦ latticeRate lam K) atTop (𝓝 0) := by
  have ha : 0 < rate lam := hRate.1 lam hlam hlam1
  have hlin : Tendsto (fun K : ℝ ↦ -rate lam * K) atTop atBot := by
    simpa [mul_comm] using! tendsto_id.atTop_mul_const_of_neg (neg_lt_zero.mpr ha)
  have hexp : Tendsto (fun K : ℝ ↦ Real.exp (-rate lam * K)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp hlin
  rw [show (fun K : ℝ ↦ latticeRate lam K) =
      (fun K ↦ latticeCoefficient lam * Real.exp (-rate lam * K)) by
    funext K
    exact latticeRate_eq_coefficient lam K]
  simpa using! tendsto_const_nhds.mul hexp

private lemma poissonCDF_left_endpoint_tendsto_zero
    (hRate : RateStatement) (lam : ℝ) (q : ℕ)
    (hlam : 0 < lam) (hlam1 : lam ≠ 1) (hq : q ≤ 1) :
    Tendsto (fun K : ℝ ↦ poissonCDF (latticeRate lam (1 - K)) q)
      atTop (𝓝 0) := by
  have hnu := latticeRate_left_tendsto_atTop hRate lam hlam hlam1
  interval_cases q
  · rw [show (fun K : ℝ ↦ poissonCDF (latticeRate lam (1 - K)) 0) =
        (fun K ↦ Real.exp (-latticeRate lam (1 - K))) by
      funext K
      exact poissonCDF_zero _]
    exact Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hnu)
  · have hzero : Tendsto
        (fun K : ℝ ↦ Real.exp (-latticeRate lam (1 - K))) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hnu)
    have hpoly := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hnu
    have hadd := hzero.add hpoly
    convert hadd using 1
    · funext K
      simp only [Function.comp_apply]
      rw [poissonCDF_one]
      ring
    · norm_num

private lemma poissonCDF_right_endpoint_one_sub_tendsto_zero
    (hRate : RateStatement) (lam : ℝ) (q : ℕ)
    (hlam : 0 < lam) (hlam1 : lam ≠ 1) (hq : q ≤ 1) :
    Tendsto (fun K : ℝ ↦ 1 - poissonCDF (latticeRate lam K) q)
      atTop (𝓝 0) := by
  have hnu := latticeRate_right_tendsto_zero hRate lam hlam hlam1
  have hexp : Tendsto (fun K : ℝ ↦ Real.exp (-latticeRate lam K)) atTop (𝓝 1) := by
    simpa using! Real.continuous_exp.continuousAt.tendsto.comp hnu.neg
  have hCDF : Tendsto (fun K : ℝ ↦ poissonCDF (latticeRate lam K) q)
      atTop (𝓝 1) := by
    interval_cases q
    · simpa [poissonCDF_zero] using! hexp
    · have hone : Tendsto (fun _ : ℝ ↦ (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
      have hmul := hexp.mul (hone.add hnu)
      simpa [poissonCDF_one] using! hmul
  simpa using! (tendsto_const_nhds.sub hCDF : Tendsto
    (fun K : ℝ ↦ (1 : ℝ) - poissonCDF (latticeRate lam K) q) atTop (𝓝 (1 - 1)))

theorem compact_poisson_tails_zero_one
    (hRate : RateStatement) (lam : ℝ) (q : ℕ)
    (hlam : 0 < lam) (hlam1 : lam ≠ 1) (hq : q ≤ 1) :
    ∀ d : ℝ, 0 < d → ∃ K : ℝ, 1 < K ∧
      (∀ ell ∈ Set.Icc (-K) (1 - K),
        poissonCDF (latticeRate lam ell) q < d / 4) ∧
      (∀ ell ∈ Set.Icc K (K + 1),
        1 - poissonCDF (latticeRate lam ell) q < d / 4) := by
  intro d hd
  have hleft := (poissonCDF_left_endpoint_tendsto_zero
    hRate lam q hlam hlam1 hq).eventually_lt_const (by positivity : 0 < d / 4)
  have hright := (poissonCDF_right_endpoint_one_sub_tendsto_zero
    hRate lam q hlam hlam1 hq).eventually_lt_const (by positivity : 0 < d / 4)
  obtain ⟨K, ⟨hK, hleftK⟩, hrightK⟩ :=
    (eventually_gt_atTop (1 : ℝ) |>.and hleft |>.and hright).exists
  refine ⟨K, hK, ?_, ?_⟩
  · intro ell hell
    have hnu := latticeRate_antitone hRate lam hlam hlam1 hell.2
    have hmono := poissonCDF_zero_one_antitoneOn q hq
      (latticeRate_pos hRate lam (1 - K) hlam hlam1).le
      (latticeRate_pos hRate lam ell hlam hlam1).le hnu
    exact hmono.trans_lt hleftK
  · intro ell hell
    have hnu := latticeRate_antitone hRate lam hlam hlam1 hell.1
    have hmono := poissonCDF_zero_one_antitoneOn q hq
      (latticeRate_pos hRate lam ell hlam hlam1).le
      (latticeRate_pos hRate lam K hlam hlam1).le hnu
    linarith

lemma fixedDensity_center_tendsto_atTop
    (hRate : RateStatement) (M : NatSeq) (lam : ℝ)
    (hlam : 0 < lam) (hlam1 : lam ≠ 1)
    (hdegree : Tendsto (degree M) atTop (𝓝 lam)) :
    Tendsto (center M) atTop atTop := by
  let N : RealSeq := fun n ↦ (n : ℝ)
  let L : RealSeq := fun n ↦ Real.log (N n)
  let a : RealSeq := fun n ↦ rate (degree M n)
  have hN : Tendsto N atTop atTop := tendsto_natCast_atTop_atTop
  have hL : Tendsto L atTop atTop := Real.tendsto_log_atTop.comp hN
  have ha : Tendsto a atTop (𝓝 (rate lam)) :=
    tendsto_rate_of_tendsto hlam hdegree
  have hrate : 0 < rate lam := hRate.1 lam hlam hlam1
  have hloglogDiv : Tendsto (fun n ↦ Real.log (L n) / L n) atTop (𝓝 0) :=
    (Real.isLittleO_log_id_atTop.comp_tendsto hL).tendsto_div_nhds_zero
  have hnumRatio : Tendsto
      (fun n ↦ (L n - (5 / 2 : ℝ) * Real.log (L n)) / L n)
      atTop (𝓝 1) := by
    have hscaled : Tendsto
        (fun n ↦ (5 / 2 : ℝ) * (Real.log (L n) / L n)) atTop (𝓝 0) := by
      simpa only [mul_zero] using!
        (tendsto_const_nhds.mul hloglogDiv : Tendsto
          (fun n ↦ (5 / 2 : ℝ) * (Real.log (L n) / L n)) atTop
            (𝓝 ((5 / 2 : ℝ) * 0)))
    have hsub := (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 1)).sub
      hscaled
    have hsub' : Tendsto
        (fun n ↦ 1 - (5 / 2 : ℝ) * (Real.log (L n) / L n)) atTop (𝓝 1) := by
      simpa using! hsub
    apply hsub'.congr'
    have hLne : ∀ᶠ n in atTop, L n ≠ 0 :=
      ((tendsto_atTop.1 hL) 1).mono fun _ hn ↦ (zero_lt_one.trans_le hn).ne'
    filter_upwards [hLne] with n hn
    field_simp
  have hcenterRatio : Tendsto (fun n ↦ center M n / L n)
      atTop (𝓝 (1 / rate lam)) := by
    have hdiv := hnumRatio.div ha hrate.ne'
    apply hdiv.congr'
    have hLne : ∀ᶠ n in atTop, L n ≠ 0 :=
      ((tendsto_atTop.1 hL) 1).mono fun _ hn ↦ (zero_lt_one.trans_le hn).ne'
    filter_upwards [hLne] with n hn
    dsimp [a, L, N]
    rw [center]
    field_simp
  have hprod := hL.atTop_mul_pos (one_div_pos.mpr hrate) hcenterRatio
  apply hprod.congr'
  have hLne : ∀ᶠ n in atTop, L n ≠ 0 :=
    ((tendsto_atTop.1 hL) 1).mono fun _ hn ↦ (zero_lt_one.trans_le hn).ne'
  filter_upwards [hLne] with n hn
  field_simp

lemma logCutoff_le_largeCutoff_eventually
    (ns : NatSeq) (hns : Tendsto ns atTop atTop) (D : ℝ) (hD : 0 < D) :
    ∀ᶠ j in atTop, logCutoff D (ns j) ≤ largeCutoff (ns j) := by
  let N : RealSeq := fun j ↦ (ns j : ℝ)
  have hN : Tendsto N atTop atTop := tendsto_natCast_atTop_atTop.comp hns
  have hratio : Tendsto
      (fun j ↦ D * Real.log (N j) / Real.rpow (N j) (2 / 3 : ℝ))
      atTop (𝓝 0) := by
    have h := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 3)).tendsto_div_nhds_zero
    simpa [N, mul_div_assoc] using! (h.comp hN).const_mul D
  have hlt : ∀ᶠ j in atTop,
      D * Real.log (N j) / Real.rpow (N j) (2 / 3 : ℝ) < 1 :=
    (tendsto_order.1 hratio).2 1 zero_lt_one
  have hNpos : ∀ᶠ j in atTop, 0 < N j :=
    ((tendsto_atTop.1 hN) 1).mono fun _ hn ↦ zero_lt_one.trans_le hn
  filter_upwards [hlt, hNpos] with j hj hNj
  have hpow : 0 < Real.rpow (N j) (2 / 3 : ℝ) := Real.rpow_pos_of_pos hNj _
  have hreal : D * Real.log (N j) ≤ Real.rpow (N j) (2 / 3 : ℝ) :=
    (div_lt_one hpow).mp hj |>.le
  unfold logCutoff largeCutoff n23
  exact Nat.ceil_mono (by simpa [N] using! hreal)

lemma fixedDensity_threshold_eventually_between
    (hRate : RateStatement) (M ns h : NatSeq) (lam ell : ℝ)
    (hlam : 0 < lam) (hlam1 : lam ≠ 1)
    (hdegree : Tendsto (degree M) atTop (𝓝 lam))
    (hns : StrictMono ns)
    (hoffset : Tendsto (fun j ↦ (h j : ℝ) - center M (ns j)) atTop (𝓝 ell)) :
    ∀ᶠ j in atTop, 0 < h j ∧ h j ≤ largeCutoff (ns j) := by
  have hasym := fixedDensity_threshold_asymptotics hRate M ns h lam ell
    hlam hlam1 hdegree hns hoffset
  have hpos : ∀ᶠ j in atTop, 0 < h j :=
    (tendsto_atTop.1 hasym.2 1).mono fun _ hj ↦ Nat.zero_lt_one.trans_le hj
  let D : ℝ := 2 / rate lam
  have hrate : 0 < rate lam := hRate.1 lam hlam hlam1
  have hD : 0 < D := by dsimp [D]; positivity
  have hcenterD : 1 / rate lam < D := by
    dsimp [D]
    exact (div_lt_div_iff_of_pos_right hrate).2 (by norm_num)
  have hlog := fixedDensity_threshold_le_logCutoff_eventually hRate M ns h
    lam ell D hlam hlam1 hdegree hns hoffset hcenterD
  have hcut := logCutoff_le_largeCutoff_eventually ns hns.tendsto_atTop D hD
  filter_upwards [hpos, hlog, hcut] with j hp hl hc
  exact ⟨hp, hl.trans hc⟩

end

end Erdos745.WrapUp.Proofs.Internal.W11_FIXED_Analytic


/-!
# Fixed-density lattice laws imply all-sequence tightness

This module packages the common tightness argument for the subcritical and
supercritical fixed-density branches.  Its hypotheses separate the numerical
Poisson tail estimates from the compact-offset/subsequence argument.
-/

namespace Erdos745.WrapUp.Proofs.Internal.W11_FIXED_Tightness

open Erdos745.WrapUp
open Filter Set
open scoped Topology

noncomputable section
attribute [local instance] Classical.propDecidable

lemma probM_compl (n m : ℕ) (A : Graph n → Prop) :
    probM n m (fun G ↦ ¬ A G) =
      probM n m (fun _ ↦ True) - probM n m A := by
  have hcard := Finset.card_filter_add_card_filter_not (s := fixedGraphs n m) A
  have hcast :
      ((fixedGraphs n m).card : ℝ) =
        (((fixedGraphs n m).filter A).card : ℝ) +
          (((fixedGraphs n m).filter fun G ↦ ¬ A G).card : ℝ) := by
    exact_mod_cast hcard.symm
  unfold probM
  simp only [Finset.filter_true]
  rw [hcast]
  ring_nf
  congr 2
  apply congrArg Finset.card
  ext G
  simp

lemma probM_cover (n m : ℕ) (A B C : Graph n → Prop)
    (hcover : ∀ G, A G → B G ∨ C G) :
    probM n m A ≤ probM n m B + probM n m C := by
  have hsub :
      (fixedGraphs n m).filter A ⊆
        (fixedGraphs n m).filter B ∪ (fixedGraphs n m).filter C := by
    intro G hG
    have hmem := Finset.mem_filter.mp hG
    rcases hcover G hmem.2 with hB | hC
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hmem.1, hB⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hmem.1, hC⟩)
  have hcard :
      ((fixedGraphs n m).filter A).card ≤
        ((fixedGraphs n m).filter B).card +
          ((fixedGraphs n m).filter C).card :=
    (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hcast :
      (((fixedGraphs n m).filter A).card : ℝ) ≤
        (((fixedGraphs n m).filter B).card : ℝ) +
          (((fixedGraphs n m).filter C).card : ℝ) := by
    exact_mod_cast hcard
  unfold probM
  rw [← add_div]
  exact div_le_div_of_nonneg_right hcast (by positivity)

lemma lower_rounding_event (x : ℕ) (c K : ℝ) :
    (x : ℝ) - c < -K ↔ x < ⌈c - K⌉₊ := by
  rw [Nat.lt_ceil]
  constructor <;> intro h <;> linarith

lemma upper_rounding_event (x : ℕ) (c K : ℝ) (hpos : 0 ≤ c + K) :
    (x : ℝ) - c > K ↔ ¬ x < ⌊c + K⌋₊ + 1 := by
  rw [show (¬ x < ⌊c + K⌋₊ + 1) ↔ ⌊c + K⌋₊ < x by omega]
  rw [Nat.floor_lt hpos]
  constructor <;> intro h <;> linarith

lemma lower_offset_mem (c K : ℝ) (hpos : 0 ≤ c - K) :
    ((⌈c - K⌉₊ : ℝ) - c) ∈ Set.Icc (-K) (1 - K) := by
  constructor
  · have h := Nat.le_ceil (c - K)
    linarith
  · have h := (Nat.ceil_lt_add_one hpos).le
    linarith

lemma upper_offset_mem (c K : ℝ) (hpos : 0 ≤ c + K) :
    (((⌊c + K⌋₊ + 1 : ℕ) : ℝ) - c) ∈ Set.Icc K (K + 1) := by
  constructor
  · have h := (Nat.lt_floor_add_one (c + K)).le
    norm_num at h ⊢
    linarith
  · have h := Nat.floor_le hpos
    norm_num at h ⊢
    linarith

/--
The common Section 8 argument.  `F` is the lattice-limit CDF (with either
Poisson cutoff `q = 1` or `q = 0`).  The two compact-interval hypotheses are
exactly the uniform numerical tails supplied by Section 7.
-/
theorem tightScaled_of_lattice_compact_tails
    (M : NatSeq) (X : (n : ℕ) → Graph n → ℕ) (c : RealSeq) (F : ℝ → ℝ)
    (hnorm : ∀ᶠ n in atTop, probM n (M n) (fun _ ↦ True) = 1)
    (hcenter : Tendsto c atTop atTop)
    (hCDF : ∀ (ns h : NatSeq) (ell : ℝ), StrictMono ns →
      Tendsto (fun j ↦ (h j : ℝ) - c (ns j)) atTop (nhds ell) →
      Tendsto (fun j ↦ probM (ns j) (M (ns j))
        (fun G ↦ X (ns j) G < h j)) atTop (nhds (F ell)))
    (htails : ∀ d : ℝ, 0 < d → ∃ K : ℝ, 1 < K ∧
      (∀ ell ∈ Set.Icc (-K) (1 - K), F ell < d / 4) ∧
      (∀ ell ∈ Set.Icc K (K + 1), 1 - F ell < d / 4)) :
    tightScaled M (fun n G ↦ (X n G : ℝ)) c (fun _ ↦ 1) := by
  intro d hd
  obtain ⟨K, hK, hleft, hright⟩ := htails d hd
  refine ⟨K, by linarith, ?_⟩
  let hminus : NatSeq := fun n ↦ ⌈c n - K⌉₊
  let hplus : NatSeq := fun n ↦ ⌊c n + K⌋₊ + 1
  have hc_ge : ∀ᶠ n in atTop, K ≤ c n :=
    hcenter.eventually (eventually_ge_atTop K)
  have hcplus_nonneg : ∀ᶠ n in atTop, 0 ≤ c n + K := by
    filter_upwards [hc_ge] with n hn
    linarith
  have hminus_mem : ∀ᶠ n in atTop,
      ((hminus n : ℝ) - c n) ∈ Set.Icc (-K) (1 - K) := by
    filter_upwards [hc_ge] with n hn
    exact lower_offset_mem (c n) K (by linarith)
  have hplus_mem : ∀ᶠ n in atTop,
      ((hplus n : ℝ) - c n) ∈ Set.Icc K (K + 1) := by
    filter_upwards [hcplus_nonneg] with n hn
    exact upper_offset_mem (c n) K hn
  have hlower : ∀ᶠ n in atTop,
      probM n (M n) (fun G ↦ X n G < hminus n) ≤ d / 2 := by
    by_contra hnot
    have hfreq : ∃ᶠ n in atTop,
        ¬ probM n (M n) (fun G ↦ X n G < hminus n) ≤ d / 2 :=
      Filter.not_eventually.mp hnot
    obtain ⟨ns, hns, hbad⟩ := extraction_of_frequently_atTop hfreq
    have hoffFreq : ∃ᶠ j in atTop,
        ((hminus (ns j) : ℝ) - c (ns j)) ∈ Set.Icc (-K) (1 - K) :=
      (hns.tendsto_atTop.eventually hminus_mem).frequently
    obtain ⟨ell, hell, r, hr, hoff⟩ :=
      isCompact_Icc.tendsto_subseq' hoffFreq
    have hcomp : StrictMono (ns ∘ r) := hns.comp hr
    have hoff' : Tendsto
        (fun j ↦ ((hminus ∘ ns ∘ r) j : ℝ) - c ((ns ∘ r) j))
        atTop (nhds ell) := by
      simpa [Function.comp_def] using! hoff
    have hlim := hCDF (ns ∘ r) (hminus ∘ ns ∘ r) ell hcomp hoff'
    have hsmall := hlim.eventually_lt_const (hleft ell hell)
    obtain ⟨j, hj⟩ := hsmall.exists
    have hjbad := hbad (r j)
    simp only [Function.comp_apply] at hj
    linarith
  have hupper : ∀ᶠ n in atTop,
      1 - probM n (M n) (fun G ↦ X n G < hplus n) ≤ d / 2 := by
    by_contra hnot
    have hfreq : ∃ᶠ n in atTop,
        ¬ 1 - probM n (M n) (fun G ↦ X n G < hplus n) ≤ d / 2 :=
      Filter.not_eventually.mp hnot
    obtain ⟨ns, hns, hbad⟩ := extraction_of_frequently_atTop hfreq
    have hoffFreq : ∃ᶠ j in atTop,
        ((hplus (ns j) : ℝ) - c (ns j)) ∈ Set.Icc K (K + 1) :=
      (hns.tendsto_atTop.eventually hplus_mem).frequently
    obtain ⟨ell, hell, r, hr, hoff⟩ :=
      isCompact_Icc.tendsto_subseq' hoffFreq
    have hcomp : StrictMono (ns ∘ r) := hns.comp hr
    have hoff' : Tendsto
        (fun j ↦ ((hplus ∘ ns ∘ r) j : ℝ) - c ((ns ∘ r) j))
        atTop (nhds ell) := by
      simpa [Function.comp_def] using! hoff
    have hlim := hCDF (ns ∘ r) (hplus ∘ ns ∘ r) ell hcomp hoff'
    have hlim' : Tendsto
        (fun j ↦ 1 - probM ((ns ∘ r) j) (M ((ns ∘ r) j))
          (fun G ↦ X ((ns ∘ r) j) G < (hplus ∘ ns ∘ r) j))
        atTop (nhds (1 - F ell)) :=
      tendsto_const_nhds.sub hlim
    have hsmall := hlim'.eventually_lt_const (hright ell hell)
    obtain ⟨j, hj⟩ := hsmall.exists
    have hjbad := hbad (r j)
    simp only [Function.comp_apply] at hj
    linarith
  filter_upwards [hnorm, hcplus_nonneg, hlower, hupper] with n hnormn hcpos hlo hup
  have hcover : ∀ G : Graph n,
      |(X n G : ℝ) - c n| > K * 1 →
        (X n G : ℝ) - c n < -K ∨ (X n G : ℝ) - c n > K := by
    intro G hG
    by_cases hz : 0 ≤ (X n G : ℝ) - c n
    · right
      rw [abs_of_nonneg hz] at hG
      simpa using! hG
    · left
      have hz' : (X n G : ℝ) - c n < 0 := lt_of_not_ge hz
      rw [abs_of_neg hz'] at hG
      norm_num at hG ⊢
      linarith
  calc
    probM n (M n) (fun G ↦ |(X n G : ℝ) - c n| > K * 1) ≤
        probM n (M n) (fun G ↦ (X n G : ℝ) - c n < -K) +
          probM n (M n) (fun G ↦ (X n G : ℝ) - c n > K) :=
      probM_cover n (M n) _ _ _ hcover
    _ = probM n (M n) (fun G ↦ X n G < hminus n) +
          (1 - probM n (M n) (fun G ↦ X n G < hplus n)) := by
      have hlowEvent :
          (fun G : Graph n ↦ (X n G : ℝ) - c n < -K) =
            (fun G ↦ X n G < hminus n) := by
        funext G
        apply propext
        exact lower_rounding_event (X n G) (c n) K
      have huppEvent :
          (fun G : Graph n ↦ (X n G : ℝ) - c n > K) =
            (fun G ↦ ¬ X n G < hplus n) := by
        funext G
        apply propext
        exact upper_rounding_event (X n G) (c n) K hcpos
      rw [hlowEvent, huppEvent, probM_compl, hnormn]
    _ ≤ d := by linarith

end

end Erdos745.WrapUp.Proofs.Internal.W11_FIXED_Tightness


namespace Erdos745.WrapUp.Proofs.Internal.W11_FIXED_Laws

open Erdos745.WrapUp
open Filter
open scoped Topology

noncomputable section
attribute [local instance] Classical.propDecidable

open Erdos745.WrapUp.Proofs.W06_POISSON
open Erdos745.WrapUp.Proofs.Internal.W10_GIANT_Components
open Erdos745.WrapUp.Proofs.Internal.W11_FIXED_Analytic
open Erdos745.WrapUp.Proofs.Internal.W11_FIXED_Tightness

lemma enum_normalization (hF : FiniteEnumerationStatement) :
    ∀ n M : ℕ, M ≤ capacity n → expectM n M (fun _ ↦ 1) = 1 := by
  rcases hF with ⟨h, _⟩
  exact h

lemma enum_rank (hF : FiniteEnumerationStatement) :
    ∀ (n : ℕ) (G : Graph n) (i h : ℕ), 0 < i → 0 < h →
      (rankSize G i < h ↔ countGE G h ≤ i - 1) := by
  rcases hF with ⟨_, _, _, _, _, _, _, _, _, _, h, _, _⟩
  exact h

lemma probM_nonneg (n M : ℕ) (A : Graph n → Prop) : 0 ≤ probM n M A := by
  unfold probM
  positivity

lemma probM_mono {n M : ℕ} {A B : Graph n → Prop}
    (hAB : ∀ G, A G → B G) : probM n M A ≤ probM n M B := by
  unfold probM
  apply div_le_div_of_nonneg_right _ (by positivity)
  norm_cast
  apply Finset.card_le_card
  intro G hG
  exact Finset.mem_filter.mpr
    ⟨(Finset.mem_filter.mp hG).1, hAB G (Finset.mem_filter.mp hG).2⟩

lemma probM_event_difference_le {n M : ℕ}
    (A B Bad : Graph n → Prop)
    (hgood : ∀ G, ¬ Bad G → (A G ↔ B G)) :
    |probM n M A - probM n M B| ≤ probM n M Bad := by
  have hAB : probM n M A ≤ probM n M B + probM n M Bad := by
    calc
      probM n M A ≤ probM n M (fun G ↦ B G ∨ Bad G) := by
        apply probM_mono
        intro G hA
        by_cases hbad : Bad G
        · exact Or.inr hbad
        · exact Or.inl ((hgood G hbad).mp hA)
      _ ≤ _ := probM_cover n M _ _ _ (fun _ ↦ id)
  have hBA : probM n M B ≤ probM n M A + probM n M Bad := by
    calc
      probM n M B ≤ probM n M (fun G ↦ A G ∨ Bad G) := by
        apply probM_mono
        intro G hB
        by_cases hbad : Bad G
        · exact Or.inr hbad
        · exact Or.inl ((hgood G hbad).mpr hB)
      _ ≤ _ := probM_cover n M _ _ _ (fun _ ↦ id)
  rw [abs_le]
  constructor <;> linarith

lemma probM_or_tendsto_zero {M : NatSeq} {A B : (n : ℕ) → Graph n → Prop}
    (hA : Tendsto (fun n ↦ probM n (M n) (A n)) atTop (𝓝 0))
    (hB : Tendsto (fun n ↦ probM n (M n) (B n)) atTop (𝓝 0)) :
    Tendsto (fun n ↦ probM n (M n) (fun G ↦ A n G ∨ B n G)) atTop (𝓝 0) := by
  apply squeeze_zero'
  · filter_upwards with n
    exact probM_nonneg n (M n) _
  · filter_upwards with n
    exact probM_cover n (M n) _ _ _ (fun _ ↦ id)
  · simpa using! hA.add hB

lemma probability_tendsto_zero_of_upper {M : NatSeq}
    {A : (n : ℕ) → Graph n → Prop} {u : RealSeq}
    (hu : Tendsto u atTop (𝓝 0))
    (hupper : ∀ᶠ n in atTop, probM n (M n) (A n) ≤ u n) :
    Tendsto (fun n ↦ probM n (M n) (A n)) atTop (𝓝 0) := by
  apply squeeze_zero'
  · filter_upwards with n
    exact probM_nonneg n (M n) _
  · exact hupper
  · exact hu

lemma probM_true_eq_expect_one (n M : ℕ) :
    probM n M (fun _ ↦ True) = expectM n M (fun _ ↦ 1) := by
  unfold probM expectM
  simp [Finset.sum_const, nsmul_eq_mul]

lemma normalization_eventually (hF : FiniteEnumerationStatement)
    {M : NatSeq} (hM : admissible M) :
    ∀ᶠ n in atTop, probM n (M n) (fun _ ↦ True) = 1 := by
  filter_upwards [hM] with n hn
  rw [probM_true_eq_expect_one]
  exact enum_normalization hF n (M n) hn

lemma nat_rank_event (hF : FiniteEnumerationStatement) {n : ℕ}
    (G : Graph n) (h : ℕ) (hh : 0 < h) :
    ((rankSize G 2 : ℝ) < (h : ℝ) ↔ countGE G h ≤ 1) := by
  have hr := enum_rank hF n G 2 h (by omega) hh
  norm_num at hr
  exact_mod_cast hr

lemma sub_count_eq_treeCount {n h : ℕ} {G : Graph n}
    (hno : noComplex G) (hcyc : ¬ cyclicAbove G (h : ℝ)) :
    countGE G h = treeCountGE G h := by
  unfold countGE treeCountGE
  congr 1
  ext S
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hS, hSh⟩
    rcases component_tree_or_unicyclic hS (hno S hS) with htree | huni
    · exact ⟨hS, htree, hSh⟩
    · exfalso
      apply hcyc
      exact ⟨S, hS, huni, by exact_mod_cast hSh⟩
  · rintro ⟨hS, _, hSh⟩
    exact ⟨hS, hSh⟩

lemma super_count_eq_one_add_treeCount {n h : ℕ} {G : Graph n}
    (hhc : h ≤ largeCutoff n)
    (hsep : separatedStructure G) (hcyc : ¬ cyclicAbove G (h : ℝ)) :
    countGE G h = 1 + treeCountGE G h := by
  let L := (components G).filter fun S ↦ largeCutoff n ≤ S.card
  let T := (components G).filter fun S ↦ isTree G S ∧ h ≤ S.card
  have hdecomp : (components G).filter (fun S ↦ h ≤ S.card) = L ∪ T := by
    dsimp [L, T]
    ext S
    simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨hS, hSh⟩
      by_cases hlarge : largeCutoff n ≤ S.card
      · exact Or.inl ⟨hS, hlarge⟩
      · right
        have hsmall : S.card < largeCutoff n := Nat.lt_of_not_ge hlarge
        rcases component_tree_or_unicyclic hS (hsep.2.1 S hS hsmall) with htree | huni
        · exact ⟨hS, htree, hSh⟩
        · exfalso
          apply hcyc
          exact ⟨S, hS, huni, by exact_mod_cast hSh⟩
    · rintro (⟨hS, hlarge⟩ | ⟨hS, _, hSh⟩)
      · exact ⟨hS, hhc.trans hlarge⟩
      · exact ⟨hS, hSh⟩
  have hdis : Disjoint L T := by
    dsimp [L, T]
    rw [Finset.disjoint_left]
    intro S hSL hST
    have hlarge := (Finset.mem_filter.mp hSL).2
    have htree := (Finset.mem_filter.mp hST).2.1
    have hexcess := hsep.2.2 S htree.1 hlarge
    have htreeEq : edgesInside G S + 1 = S.card := htree.2
    have hedgeless : edgesInside G S < S.card := by omega
    exact (lt_asymm hedgeless hexcess).elim
  unfold countGE treeCountGE
  rw [hdecomp, Finset.card_union_of_disjoint hdis]
  have hLcard : L.card = 1 := by
    simpa [L, countGE] using! hsep.1
  rw [hLcard]

lemma sub_bad_tendsto_zero (hS : SubcriticalExclusionStatement)
    {M : NatSeq} {lam : ℝ} (hM : admissible M)
    (hlam : 0 < lam) (hlam1 : lam < 1)
    (hdegree : Tendsto (degree M) atTop (𝓝 lam)) :
    Tendsto (fun n ↦ probM n (M n) (fun G ↦ ¬ noComplex G)) atTop (𝓝 0) := by
  rcases hS with ⟨C, hC, hbound⟩
  let e : ℝ := (1 - lam) / 2
  have he : 0 < e := by dsimp [e]; linarith
  have hdeg : ∀ᶠ n in atTop, degree M n ≤ 1 - e := by
    have ht : ∀ᶠ n in atTop, degree M n < lam + e :=
      (tendsto_order.1 hdegree).2 (lam + e) (by linarith)
    exact ht.mono fun _ hn ↦ by dsimp [e] at hn ⊢; linarith
  have hfour : ∀ᶠ n : ℕ in atTop, 4 / (n : ℝ) ≤ e := by
    have ht := tendsto_const_div_atTop_nhds_zero_nat (4 : ℝ)
    exact ((tendsto_order.1 ht).2 e he).mono fun _ hn ↦ hn.le
  have hupper : ∀ᶠ n in atTop,
      probM n (M n) (fun G ↦ ¬ noComplex G) ≤ C / ((n : ℝ) * e ^ 3) := by
    filter_upwards [eventually_ge_atTop 2, hM, hfour, hdeg] with n hn hMn h4 hd
    exact hbound n (M n) e hn hMn he h4 hd
  have hden : Tendsto (fun n : ℕ ↦ (n : ℝ) * e ^ 3) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_mul_const (pow_pos he 3)
  exact probability_tendsto_zero_of_upper (tendsto_const_nhds.div_atTop hden) hupper

lemma sub_lattice_law
    (hF : FiniteEnumerationStatement) (hR : RateStatement)
    (hP : PoissonStatement) (hS : SubcriticalExclusionStatement)
    (hC : CyclicStructureStatement)
    {M ns h : NatSeq} {lam ell : ℝ}
    (hM : admissible M) (hlam : 0 < lam) (hlam1 : lam < 1)
    (hdegree : Tendsto (degree M) atTop (𝓝 lam))
    (hns : StrictMono ns)
    (hoffset : Tendsto (fun j ↦ (h j : ℝ) - center M (ns j)) atTop (𝓝 ell)) :
    Tendsto (fun j ↦ fixedCDF (ns j) (M (ns j)) 2 (h j)) atTop
      (𝓝 (poissonCDF (latticeRate lam ell) 1)) := by
  have hne : lam ≠ 1 := ne_of_lt hlam1
  have hbetween := fixedDensity_threshold_eventually_between hR M ns h lam ell
    hlam hne hdegree hns hoffset
  have hbad := (sub_bad_tendsto_zero hS hM hlam hlam1 hdegree).comp hns.tendsto_atTop
  have hcyc := hC.2 M lam hM hlam hne hdegree |>.2.2.2 ns h ell hns hoffset
  have hu : Tendsto (fun j ↦
      probM (ns j) (M (ns j)) (fun G ↦ ¬ noComplex G) +
        probM (ns j) (M (ns j)) (fun G ↦ cyclicAbove G (h j : ℝ)))
      atTop (𝓝 0) := by
    simpa only [add_zero] using! hbad.add hcyc
  have herror : Tendsto (fun j ↦
      |fixedCDF (ns j) (M (ns j)) 2 (h j) -
        countCDF (ns j) (M (ns j)) (h j) 1|) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun _ ↦ abs_nonneg _) _ hu
    filter_upwards [hbetween] with j hj
    unfold fixedCDF countCDF
    refine (probM_event_difference_le _ _
      (fun G ↦ ¬ noComplex G ∨ cyclicAbove G (h j : ℝ)) ?_).trans
        (probM_cover (ns j) (M (ns j)) _ _ _ (fun _ ↦ id))
    intro G hgood
    push_neg at hgood
    rw [nat_rank_event hF G (h j) hj.1]
    rw [sub_count_eq_treeCount hgood.1 hgood.2]
  have hdiff : Tendsto (fun j ↦
      fixedCDF (ns j) (M (ns j)) 2 (h j) -
        countCDF (ns j) (M (ns j)) (h j) 1) atTop (𝓝 0) := by
    exact (tendsto_zero_iff_abs_tendsto_zero _).2 herror
  have hpoi := hP.2.1 M lam hM hlam hne hdegree ns h ell hns hoffset 1
  simpa only [zero_add, sub_add_cancel] using! hdiff.add hpoi

lemma super_not_separated_tendsto_zero
    (hF : FiniteEnumerationStatement) (hG : GiantStatement)
    {M : NatSeq} {lam : ℝ} (hM : admissible M) (hlam : 1 < lam)
    (hdegree : Tendsto (degree M) atTop (𝓝 lam)) :
    Tendsto (fun n ↦ probM n (M n) (fun G ↦ ¬ separatedStructure G))
      atTop (𝓝 0) := by
  have hsep := (hG.2 M lam hM hlam hdegree).2.2
  have hnorm := normalization_eventually hF hM
  have hcomp : ∀ᶠ n in atTop,
      probM n (M n) (fun G ↦ ¬ separatedStructure G) =
        1 - probM n (M n) separatedStructure := by
    filter_upwards [hnorm] with n hn
    rw [probM_compl, hn]
  have hcomp' : (fun n ↦ 1 - probM n (M n) separatedStructure) =ᶠ[atTop]
      (fun n ↦ probM n (M n) (fun G ↦ ¬ separatedStructure G)) := by
    filter_upwards [hcomp] with n hn
    exact hn.symm
  have ht : Tendsto (fun n ↦ (1 : ℝ) - probM n (M n) separatedStructure)
      atTop (𝓝 0) := by
    simpa using! ((tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 1)).sub hsep)
  exact ht.congr' hcomp'

lemma super_lattice_law
    (hF : FiniteEnumerationStatement) (hR : RateStatement)
    (hP : PoissonStatement) (hC : CyclicStructureStatement)
    (hG : GiantStatement)
    {M ns h : NatSeq} {lam ell : ℝ}
    (hM : admissible M) (hlam : 1 < lam)
    (hdegree : Tendsto (degree M) atTop (𝓝 lam))
    (hns : StrictMono ns)
    (hoffset : Tendsto (fun j ↦ (h j : ℝ) - center M (ns j)) atTop (𝓝 ell)) :
    Tendsto (fun j ↦ fixedCDF (ns j) (M (ns j)) 2 (h j)) atTop
      (𝓝 (poissonCDF (latticeRate lam ell) 0)) := by
  have hpos : 0 < lam := zero_lt_one.trans hlam
  have hne : lam ≠ 1 := ne_of_gt hlam
  have hbetween := fixedDensity_threshold_eventually_between hR M ns h lam ell
    hpos hne hdegree hns hoffset
  have hsep := (super_not_separated_tendsto_zero hF hG hM hlam hdegree).comp
    hns.tendsto_atTop
  have hcyc := hC.2 M lam hM hpos hne hdegree |>.2.2.2 ns h ell hns hoffset
  have hu : Tendsto (fun j ↦
      probM (ns j) (M (ns j)) (fun G ↦ ¬ separatedStructure G) +
        probM (ns j) (M (ns j)) (fun G ↦ cyclicAbove G (h j : ℝ)))
      atTop (𝓝 0) := by
    simpa only [add_zero] using! hsep.add hcyc
  have herror : Tendsto (fun j ↦
      |fixedCDF (ns j) (M (ns j)) 2 (h j) -
        countCDF (ns j) (M (ns j)) (h j) 0|) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun _ ↦ abs_nonneg _) _ hu
    filter_upwards [hbetween] with j hj
    unfold fixedCDF countCDF
    refine (probM_event_difference_le _ _
      (fun G ↦ ¬ separatedStructure G ∨ cyclicAbove G (h j : ℝ)) ?_).trans
        (probM_cover (ns j) (M (ns j)) _ _ _ (fun _ ↦ id))
    intro G hgood
    push_neg at hgood
    rw [nat_rank_event hF G (h j) hj.1]
    rw [super_count_eq_one_add_treeCount hj.2 hgood.1 hgood.2]
    omega
  have hdiff : Tendsto (fun j ↦
      fixedCDF (ns j) (M (ns j)) 2 (h j) -
        countCDF (ns j) (M (ns j)) (h j) 0) atTop (𝓝 0) := by
    exact (tendsto_zero_iff_abs_tendsto_zero _).2 herror
  have hpoi := hP.2.1 M lam hM hpos hne hdegree ns h ell hns hoffset 0
  simpa only [zero_add, sub_add_cancel] using! hdiff.add hpoi

theorem fixedSubcriticalLaw_of_inputs
    (hF : FiniteEnumerationStatement) (hR : RateStatement)
    (hP : PoissonStatement) (hS : SubcriticalExclusionStatement)
    (hC : CyclicStructureStatement) : fixedSubcriticalLaw := by
  intro M lam hM hlam hlam1 hdegree
  have hne : lam ≠ 1 := ne_of_lt hlam1
  have hnorm := normalization_eventually hF hM
  have hcenter := fixedDensity_center_tendsto_atTop hR M lam hlam hne hdegree
  have hCDF : ∀ (ns h : NatSeq) (ell : ℝ), StrictMono ns →
      Tendsto (fun j ↦ (h j : ℝ) - center M (ns j)) atTop (𝓝 ell) →
      Tendsto (fun j ↦ probM (ns j) (M (ns j))
        (fun G ↦ rankSize G 2 < h j)) atTop
        (𝓝 (poissonCDF (latticeRate lam ell) 1)) := by
    intro ns h ell hns hoff
    simpa [fixedCDF] using!
      sub_lattice_law hF hR hP hS hC hM hlam hlam1 hdegree hns hoff
  have htight := tightScaled_of_lattice_compact_tails M
    (fun _ G ↦ rankSize G 2) (center M)
    (fun ell ↦ poissonCDF (latticeRate lam ell) 1)
    hnorm hcenter hCDF
    (compact_poisson_tails_zero_one hR lam 1 hlam hne (by omega))
  exact ⟨htight, fun ns h ell hns hoff ↦
    sub_lattice_law hF hR hP hS hC hM hlam hlam1 hdegree hns hoff⟩

theorem fixedSupercriticalLaw_of_inputs
    (hF : FiniteEnumerationStatement) (hR : RateStatement)
    (hP : PoissonStatement) (hC : CyclicStructureStatement)
    (hG : GiantStatement) : fixedSupercriticalLaw := by
  intro M lam hM hlam hdegree
  have hpos : 0 < lam := zero_lt_one.trans hlam
  have hne : lam ≠ 1 := ne_of_gt hlam
  have hnorm := normalization_eventually hF hM
  have hcenter := fixedDensity_center_tendsto_atTop hR M lam hpos hne hdegree
  have hCDF : ∀ (ns h : NatSeq) (ell : ℝ), StrictMono ns →
      Tendsto (fun j ↦ (h j : ℝ) - center M (ns j)) atTop (𝓝 ell) →
      Tendsto (fun j ↦ probM (ns j) (M (ns j))
        (fun G ↦ rankSize G 2 < h j)) atTop
        (𝓝 (poissonCDF (latticeRate lam ell) 0)) := by
    intro ns h ell hns hoff
    simpa [fixedCDF] using!
      super_lattice_law hF hR hP hC hG hM hlam hdegree hns hoff
  have htight := tightScaled_of_lattice_compact_tails M
    (fun _ G ↦ rankSize G 2) (center M)
    (fun ell ↦ poissonCDF (latticeRate lam ell) 0)
    hnorm hcenter hCDF
    (compact_poisson_tails_zero_one hR lam 0 hpos hne (by omega))
  have hg := hG.2 M lam hM hlam hdegree
  exact ⟨htight, hg.2.1, hg.2.2,
    fun ns h ell hns hoff ↦
      super_lattice_law hF hR hP hC hG hM hlam hdegree hns hoff⟩

theorem fixedAtlasStatement_of_inputs
    (hF : FiniteEnumerationStatement) (hR : RateStatement)
    (hP : PoissonStatement) (hS : SubcriticalExclusionStatement)
    (hC : CyclicStructureStatement) (hG : GiantStatement) :
    FixedAtlasStatement := by
  exact ⟨fixedSubcriticalLaw_of_inputs hF hR hP hS hC,
    fixedSupercriticalLaw_of_inputs hF hR hP hC hG⟩

end

end Erdos745.WrapUp.Proofs.Internal.W11_FIXED_Laws
