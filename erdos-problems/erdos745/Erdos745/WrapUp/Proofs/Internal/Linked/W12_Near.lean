module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Erdos745.WrapUp.Proofs.Internal.Linked.W06_P03
public import Erdos745.WrapUp.Proofs.Internal.Linked.W10_Core

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local simp] Pi.div_def Pi.mul_def Pi.add_def Pi.sub_def Pi.neg_def Pi.inv_def Function.comp_def Pi.pow_def Pi.smul_def Real.rpow_eq_pow

@[expose] public section


namespace Erdos745.WrapUp.Proofs.Internal.W12_NEAR_Common

open Filter
open scoped Topology BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

open Erdos745.WrapUp.Proofs.W06_POISSON
open Erdos745.WrapUp.Proofs.Internal.W10_GIANT_Components
open Erdos745.WrapUp.Proofs.Internal.W10_GIANT_Closure

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

lemma probM_or_le (n M : ℕ) (A B : Graph n → Prop) :
    probM n M (fun G ↦ A G ∨ B G) ≤ probM n M A + probM n M B :=
  W10_GIANT_Closure.probM_or_le A B

lemma probM_compl_eq_one_sub (hF : FiniteEnumerationStatement)
    {n M : ℕ} (hM : M ≤ capacity n) (A : Graph n → Prop) :
    probM n M A = 1 - probM n M (fun G ↦ ¬ A G) :=
  W10_GIANT_Closure.probM_compl_eq_one_sub hF hM A

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
      _ ≤ _ := probM_or_le n M B Bad
  have hBA : probM n M B ≤ probM n M A + probM n M Bad := by
    calc
      probM n M B ≤ probM n M (fun G ↦ A G ∨ Bad G) := by
        apply probM_mono
        intro G hB
        by_cases hbad : Bad G
        · exact Or.inr hbad
        · exact Or.inl ((hgood G hbad).mpr hB)
      _ ≤ _ := probM_or_le n M A Bad
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
    exact probM_or_le n (M n) _ _
  · simpa using! hA.add hB

lemma probability_tendsto_zero_of_upper {M : NatSeq} {A : (n : ℕ) → Graph n → Prop}
    {u : RealSeq} (hu : Tendsto u atTop (𝓝 0))
    (hupper : ∀ᶠ n in atTop, probM n (M n) (A n) ≤ u n) :
    Tendsto (fun n ↦ probM n (M n) (A n)) atTop (𝓝 0) := by
  apply squeeze_zero'
  · filter_upwards with n
    exact probM_nonneg n (M n) _
  · exact hupper
  · exact hu

lemma nat_rank_event (hF : FiniteEnumerationStatement) {n : ℕ}
    (G : Graph n) (H : ℝ) (hH : 0 < H) :
    ((rankSize G 2 : ℝ) < H ↔ countGE G ⌈H⌉₊ ≤ 1) := by
  calc
    ((rankSize G 2 : ℝ) < H ↔ rankSize G 2 < ⌈H⌉₊) := Nat.lt_ceil.symm
    _ ↔ countGE G ⌈H⌉₊ ≤ 2 - 1 :=
      enum_rank hF n G 2 ⌈H⌉₊ (by omega) (Nat.ceil_pos.mpr hH)
    _ ↔ countGE G ⌈H⌉₊ ≤ 1 := by norm_num

lemma width_rpow_identity {M : NatSeq} {n : ℕ}
    (hn : 0 < n) (he : 0 < epsilon M n) :
    Real.rpow (widthParameter M n) (2 / 3 : ℝ) =
      n23 n * epsilon M n ^ 2 := by
  have hn0 : 0 ≤ (n : ℝ) := by positivity
  have he30 : 0 ≤ epsilon M n ^ 3 := by positivity
  change Real.rpow ((n : ℝ) * epsilon M n ^ 3) (2 / 3 : ℝ) =
    Real.rpow (n : ℝ) (2 / 3 : ℝ) * epsilon M n ^ 2
  calc
    Real.rpow ((n : ℝ) * epsilon M n ^ 3) (2 / 3 : ℝ) =
        Real.rpow (n : ℝ) (2 / 3 : ℝ) *
          Real.rpow (epsilon M n ^ 3) (2 / 3 : ℝ) :=
      Real.mul_rpow hn0 he30
    _ = Real.rpow (n : ℝ) (2 / 3 : ℝ) * epsilon M n ^ 2 := by
      congr 1
      calc
        Real.rpow (epsilon M n ^ 3) (2 / 3 : ℝ) =
            Real.rpow (Real.rpow (epsilon M n) 3) (2 / 3 : ℝ) := by
              exact congrArg (fun x ↦ Real.rpow x (2 / 3 : ℝ))
                (Real.rpow_natCast (epsilon M n) 3).symm
        _ = Real.rpow (epsilon M n) (3 * (2 / 3 : ℝ)) := by
          exact (Real.rpow_mul he.le 3 (2 / 3 : ℝ)).symm
        _ = epsilon M n ^ 2 := by
          norm_num

lemma nearHeight_div_n23_tendsto_zero
    (hRate : RateStatement) {M : NatSeq} (hbare : bareSub M ∨ bareSuper M)
    (r : ℝ) :
    Tendsto (fun n ↦ (nearHeight M r n : ℝ) / n23 n) atTop (𝓝 0) := by
  let w : RealSeq := widthParameter M
  let e : RealSeq := epsilon M
  let L : RealSeq := fun n ↦ Real.log (w n / 8)
  let h : NatSeq := nearHeight M r
  have hw : Tendsto w atTop atTop := bare_width_tendsto_atTop hbare
  have hscale : Tendsto (fun n ↦ e n ^ 2 * (h n : ℝ) / L n)
      atTop (𝓝 2) := by
    simpa [w, e, L, h] using! near_height_scale hRate hbare r
  have hlog : Tendsto (fun n ↦ Real.log (w n) / Real.rpow (w n) (2 / 3 : ℝ))
      atTop (𝓝 0) := by
    exact (isLittleO_log_rpow_atTop (r := (2 / 3 : ℝ)) (by norm_num))
      |>.tendsto_div_nhds_zero.comp hw
  have hpow : Tendsto (fun n ↦ Real.rpow (w n) (2 / 3 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 3)).comp hw
  have hconst : Tendsto (fun n ↦ Real.log 8 / Real.rpow (w n) (2 / 3 : ℝ))
      atTop (𝓝 0) := tendsto_const_nhds.div_atTop hpow
  have hlog8 : Tendsto (fun n ↦ L n / Real.rpow (w n) (2 / 3 : ℝ))
      atTop (𝓝 0) := by
    have hd := hlog.sub hconst
    have hd' : Tendsto (fun n ↦ Real.log (w n) / Real.rpow (w n) (2 / 3 : ℝ) -
        Real.log 8 / Real.rpow (w n) (2 / 3 : ℝ)) atTop (𝓝 0) := by
      simpa using! hd
    have hwpos : ∀ᶠ n in atTop, 0 < w n :=
      ((tendsto_atTop.1 hw) 1).mono fun _ hn ↦ zero_lt_one.trans_le hn
    apply hd'.congr'
    filter_upwards [hwpos] with n hwn
    dsimp [L]
    rw [Real.log_div hwn.ne' (by norm_num : (8 : ℝ) ≠ 0)]
    have hp : 0 < Real.rpow (w n) (2 / 3 : ℝ) :=
      Real.rpow_pos_of_pos hwn _
    field_simp [hp.ne']
  have hprod := hscale.mul hlog8
  have hprod' : Tendsto
      (fun n ↦ (e n ^ 2 * (h n : ℝ) / L n) *
        (L n / Real.rpow (w n) (2 / 3 : ℝ))) atTop (𝓝 0) := by
    simpa using! hprod
  apply hprod'.congr'
  have hn : ∀ᶠ n : ℕ in atTop, 0 < n := eventually_gt_atTop 0
  have he := bare_epsilon_pos hbare
  have hL : ∀ᶠ n in atTop, 0 < L n := by
    simpa [L, w] using!
      ((tendsto_atTop.1 (near_log_width_tendsto_atTop hbare)) 1).mono
        (fun _ hn ↦ zero_lt_one.trans_le hn)
  filter_upwards [hn, he, hL] with n hn he hL
  rw [width_rpow_identity hn he]
  dsimp [e, h, L, w]
  have hn23 : 0 < n23 n := Real.rpow_pos_of_pos (by positivity) _
  field_simp [he.ne', hL.ne', hn23.ne']
  exact mul_div_cancel_right₀ _ hL.ne'

lemma nearHeight_eventually_between
    (hRate : RateStatement) {M : NatSeq} (hbare : bareSub M ∨ bareSuper M)
    (r : ℝ) :
    ∀ᶠ n in atTop, 0 < nearHeight M r n ∧ nearHeight M r n ≤ largeCutoff n := by
  have htop := (near_rounding_asymptotics hRate hbare r).2
  have hpos : ∀ᶠ n in atTop, 0 < nearHeight M r n :=
    ((tendsto_atTop.1 htop) 1).mono fun _ hn ↦ lt_of_lt_of_le Nat.zero_lt_one hn
  have hratio := nearHeight_div_n23_tendsto_zero hRate hbare r
  have hlt : ∀ᶠ n in atTop,
      (nearHeight M r n : ℝ) / n23 n < 1 :=
    (tendsto_order.1 hratio).2 1 zero_lt_one
  have hn : ∀ᶠ n : ℕ in atTop, 0 < n := eventually_gt_atTop 0
  filter_upwards [hpos, hlt, hn] with n hh hratio hn
  refine ⟨hh, ?_⟩
  have hn23 : 0 < n23 n := Real.rpow_pos_of_pos (by positivity) _
  have hreal : (nearHeight M r n : ℝ) < n23 n :=
    (div_lt_one hn23).mp hratio
  have hceil : n23 n ≤ (largeCutoff n : ℝ) := Nat.le_ceil _
  exact_mod_cast hreal.le.trans hceil

lemma sub_count_eq_treeCount {n h : ℕ} {G : Graph n} {H : ℝ}
    (hceil : h = ⌈H⌉₊) (hno : noComplex G) (hcyc : ¬ cyclicAbove G H) :
    countGE G h = treeCountGE G h := by
  unfold countGE treeCountGE
  congr 1
  ext S
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hS, hSh⟩
    have hupper := hno S hS
    rcases component_tree_or_unicyclic hS hupper with htree | huni
    · exact ⟨hS, htree, hSh⟩
    · exfalso
      apply hcyc
      refine ⟨S, hS, huni, ?_⟩
      rw [← Nat.ceil_le, ← hceil]
      exact hSh
  · rintro ⟨hS, _, hSh⟩
    exact ⟨hS, hSh⟩

lemma super_count_eq_one_add_treeCount {n h : ℕ} {G : Graph n} {H : ℝ}
    (hceil : h = ⌈H⌉₊) (hhc : h ≤ largeCutoff n)
    (hsep : separatedStructure G) (hcyc : ¬ cyclicAbove G H) :
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
        have hupper := hsep.2.1 S hS hsmall
        rcases component_tree_or_unicyclic hS hupper with htree | huni
        · exact ⟨hS, htree, hSh⟩
        · exfalso
          apply hcyc
          refine ⟨S, hS, huni, ?_⟩
          rw [← Nat.ceil_le, ← hceil]
          exact hSh
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
    have htreeEq := htree.2
    omega
  unfold countGE treeCountGE
  rw [hdecomp, Finset.card_union_of_disjoint hdis]
  have hLcard : L.card = 1 := by
    simpa [L, countGE] using! hsep.1
  have hTcard : T.card =
      ((components G).filter fun S ↦ isTree G S ∧ h ≤ S.card).card := by
    rfl
  rw [hLcard, hTcard]

end

end Erdos745.WrapUp.Proofs.Internal.W12_NEAR_Common


namespace Erdos745.WrapUp.Proofs.Internal.W12_NEAR_Laws

open Filter
open scoped Topology

noncomputable section
attribute [local instance] Classical.propDecidable

open Erdos745.WrapUp.Proofs.W06_POISSON
open W12_NEAR_Common

lemma sub_bad_tendsto_zero (hS : SubcriticalExclusionStatement)
    {M : NatSeq} (hbare : bareSub M) :
    Tendsto (fun n ↦ probM n (M n) (fun G ↦ ¬ noComplex G)) atTop (𝓝 0) := by
  rcases hS with ⟨C, hC, hbound⟩
  have hw := hbare.2.2.2
  have he : ∀ᶠ n in atTop, 0 < epsilon M n :=
    bare_epsilon_pos (Or.inl hbare)
  have hn : ∀ᶠ n : ℕ in atTop, 2 ≤ n := eventually_ge_atTop 2
  have hadm := hbare.1
  have hside := hbare.2.1
  have hw64 : ∀ᶠ n in atTop, 64 ≤ widthParameter M n :=
    tendsto_atTop.1 hw 64
  have h4 : ∀ᶠ (n : ℕ) in atTop, 4 / (n : ℝ) ≤ epsilon M n := by
    filter_upwards [hn, he, hw64] with n hn he hw64
    have hnpos : 0 < (n : ℝ) := by positivity
    have hxnonneg : 0 ≤ (n : ℝ) * epsilon M n := mul_nonneg hnpos.le he.le
    have hx3 : (4 : ℝ) ^ 3 ≤ ((n : ℝ) * epsilon M n) ^ 3 := by
      have hn2 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by
        norm_num
        nlinarith
      have hw0 : 0 ≤ widthParameter M n := le_trans (by norm_num) hw64
      have hmul : widthParameter M n ≤ (n : ℝ) ^ 2 * widthParameter M n := by
        simpa using! mul_le_mul_of_nonneg_right hn2 hw0
      calc
        (4 : ℝ) ^ 3 = 64 := by norm_num
        _ ≤ widthParameter M n := hw64
        _ ≤ (n : ℝ) ^ 2 * widthParameter M n := hmul
        _ = ((n : ℝ) * epsilon M n) ^ 3 := by
          rw [widthParameter]
          ring
    have hx : (4 : ℝ) ≤ (n : ℝ) * epsilon M n := by
      by_contra hnot
      have hlt : (n : ℝ) * epsilon M n < 4 := lt_of_not_ge hnot
      have hp := pow_lt_pow_left₀ hlt hxnonneg (by norm_num : (3 : ℕ) ≠ 0)
      exact (not_lt_of_ge hx3) hp
    exact (div_le_iff₀ hnpos).2 (by simpa [mul_comm] using! hx)
  have hupper : ∀ᶠ n in atTop,
      probM n (M n) (fun G ↦ ¬ noComplex G) ≤ C / widthParameter M n := by
    filter_upwards [hn, hadm, hside, he, h4] with n hn hadm hside he h4
    have hdeg : degree M n = 1 - epsilon M n := by
      rw [epsilon, abs_of_neg (sub_neg.mpr hside.2)]
      ring
    have hdegLe : degreeAt n (M n) ≤ 1 - epsilon M n := by
      change degree M n ≤ 1 - epsilon M n
      rw [hdeg]
    simpa [widthParameter, hdeg] using!
      hbound n (M n) (epsilon M n) hn hadm he h4 hdegLe
  exact probability_tendsto_zero_of_upper
    (tendsto_const_nhds.div_atTop hw) hupper

lemma sub_fixedCDF (hF : FiniteEnumerationStatement) (hR : RateStatement)
    (hP : PoissonStatement) (hS : SubcriticalExclusionStatement)
    (hC : CyclicStructureStatement) {M : NatSeq} (hbare : bareSub M) (r : ℝ) :
    Tendsto (fun n ↦ fixedCDF n (M n) 2 (nearThreshold M n r))
      atTop (𝓝 (poissonCDF (nearRate r) 1)) := by
  let h : NatSeq := nearHeight M r
  have hbetween := nearHeight_eventually_between hR (Or.inl hbare) r
  have hHpos : ∀ᶠ n in atTop, 0 < nearThreshold M n r := by
    filter_upwards [hbetween] with n hn
    exact Nat.ceil_pos.mp (by simpa [h, nearHeight] using! hn.1)
  have hbad := sub_bad_tendsto_zero hS hbare
  have hcyc := (hC.1 M (Or.inl hbare)).2.2 r
  have herror : Tendsto (fun n ↦
      |fixedCDF n (M n) 2 (nearThreshold M n r) - countCDF n (M n) (h n) 1|)
      atTop (𝓝 0) := by
    have hu := probM_or_tendsto_zero hbad hcyc
    apply squeeze_zero'
    · filter_upwards with n
      positivity
    · filter_upwards [hHpos] with n hpos
      unfold fixedCDF countCDF
      apply probM_event_difference_le _ _
        (fun G ↦ ¬ noComplex G ∨ cyclicAbove G (nearThreshold M n r))
      intro G hgood
      push_neg at hgood
      rw [nat_rank_event hF G _ hpos]
      rw [sub_count_eq_treeCount (H := nearThreshold M n r) (by rfl) hgood.1 hgood.2]
      change treeCountGE G ⌈nearThreshold M n r⌉₊ ≤ 1 ↔
        treeCountGE G ⌈nearThreshold M n r⌉₊ ≤ 1
      rfl
    · exact hu
  have hdiff : Tendsto (fun n ↦
      fixedCDF n (M n) 2 (nearThreshold M n r) - countCDF n (M n) (h n) 1)
      atTop (𝓝 0) := by
    apply (tendsto_zero_iff_norm_tendsto_zero).2
    simpa [Real.norm_eq_abs] using! herror
  have hpois := hP.2.2 M (Or.inl hbare) r 1
  have hadd : Tendsto (fun n ↦
      (fixedCDF n (M n) 2 (nearThreshold M n r) - countCDF n (M n) (h n) 1) +
        countCDF n (M n) ⌈nearThreshold M n r⌉₊ 1)
      atTop (𝓝 (poissonCDF (nearRate r) 1)) := by
    simpa using! hdiff.add hpois
  apply hadd.congr'
  filter_upwards with n
  dsimp [h, nearHeight]
  ring

lemma barelySubcriticalLaw_of_inputs
    (hF : FiniteEnumerationStatement) (hR : RateStatement)
    (hP : PoissonStatement) (hS : SubcriticalExclusionStatement)
    (hC : CyclicStructureStatement) : barelySubcriticalLaw := by
  intro M hbare
  refine ⟨fun r ↦ sub_fixedCDF hF hR hP hS hC hbare r, ?_⟩
  have hbad := sub_bad_tendsto_zero hS hbare
  have hcomp : ∀ᶠ n in atTop,
      probM n (M n) noComplex =
        1 - probM n (M n) (fun G ↦ ¬ noComplex G) := by
    filter_upwards [hbare.1] with n hn
    exact probM_compl_eq_one_sub hF hn noComplex
  have ht := (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 1)).sub hbad
  have ht' := ht.congr' (hcomp.mono fun _ hn ↦ hn.symm)
  simpa [noComplex] using! ht'

lemma super_fixedCDF (hF : FiniteEnumerationStatement) (hR : RateStatement)
    (hP : PoissonStatement) (hC : CyclicStructureStatement)
    (hG : GiantStatement) {M : NatSeq} (hbare : bareSuper M) (r : ℝ) :
    Tendsto (fun n ↦ fixedCDF n (M n) 2 (nearThreshold M n r))
      atTop (𝓝 (poissonCDF (nearRate r) 0)) := by
  let h : NatSeq := nearHeight M r
  have hbetween := nearHeight_eventually_between hR (Or.inr hbare) r
  have hHpos : ∀ᶠ n in atTop, 0 < nearThreshold M n r := by
    filter_upwards [hbetween] with n hn
    exact Nat.ceil_pos.mp (by simpa [h, nearHeight] using! hn.1)
  have hsep := (hG.1 M hbare).2.2
  have hnotsep : Tendsto
      (fun n ↦ probM n (M n) (fun G ↦ ¬ separatedStructure G)) atTop (𝓝 0) := by
    have hcomp : ∀ᶠ n in atTop,
        probM n (M n) (fun G ↦ ¬ separatedStructure G) =
          1 - probM n (M n) separatedStructure := by
      filter_upwards [hbare.1] with n hn
      have hc := probM_compl_eq_one_sub hF hn separatedStructure
      linarith
    have ht := (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 1)).sub hsep
    simpa using! ht.congr' (hcomp.mono fun _ hn ↦ hn.symm)
  have hcyc := (hC.1 M (Or.inr hbare)).2.2 r
  have herror : Tendsto (fun n ↦
      |fixedCDF n (M n) 2 (nearThreshold M n r) - countCDF n (M n) (h n) 0|)
      atTop (𝓝 0) := by
    have hu := probM_or_tendsto_zero hnotsep hcyc
    apply squeeze_zero'
    · filter_upwards with n
      positivity
    · filter_upwards [hHpos, hbetween] with n hpos hbetween
      unfold fixedCDF countCDF
      apply probM_event_difference_le _ _
        (fun G ↦ ¬ separatedStructure G ∨ cyclicAbove G (nearThreshold M n r))
      intro G hgood
      push_neg at hgood
      rw [nat_rank_event hF G _ hpos]
      change countGE G ⌈nearThreshold M n r⌉₊ ≤ 1 ↔
        treeCountGE G ⌈nearThreshold M n r⌉₊ ≤ 0
      rw [super_count_eq_one_add_treeCount (h := ⌈nearThreshold M n r⌉₊)
        (H := nearThreshold M n r) (by rfl)
        (by simpa [nearHeight] using! hbetween.2) hgood.1 hgood.2]
      omega
    · exact hu
  have hdiff : Tendsto (fun n ↦
      fixedCDF n (M n) 2 (nearThreshold M n r) - countCDF n (M n) (h n) 0)
      atTop (𝓝 0) := by
    apply (tendsto_zero_iff_norm_tendsto_zero).2
    simpa [Real.norm_eq_abs] using! herror
  have hpois := hP.2.2 M (Or.inr hbare) r 0
  have hadd : Tendsto (fun n ↦
      (fixedCDF n (M n) 2 (nearThreshold M n r) - countCDF n (M n) (h n) 0) +
        countCDF n (M n) ⌈nearThreshold M n r⌉₊ 0)
      atTop (𝓝 (poissonCDF (nearRate r) 0)) := by
    simpa using! hdiff.add hpois
  apply hadd.congr'
  filter_upwards with n
  dsimp [h, nearHeight]
  ring

lemma super_conjugate_equation (hR : RateStatement)
    {M : NatSeq} (hbare : bareSuper M) :
    ∀ᶠ n in atTop,
      0 < conjugateDisplacement M n ∧ conjugateDisplacement M n < (n : ℝ) / 2 ∧
      (1 - 2 * conjugateDisplacement M n / n) *
        Real.exp (2 * conjugateDisplacement M n / n) =
      (1 + 2 * displacement M n / n) * Real.exp (-2 * displacement M n / n) := by
  have hn : ∀ᶠ n : ℕ in atTop, 0 < n := eventually_gt_atTop 0
  have hside := hbare.2.1
  filter_upwards [hn, hside] with n hn hside
  have he : epsilon M n = degree M n - 1 := by
    rw [epsilon, abs_of_pos (sub_pos.mpr hside)]
  have hdeg : degree M n = 1 + epsilon M n := by linarith
  obtain ⟨hy0, hy1, hconj, _, _⟩ := hR.2.1 (degree M n) hside
  have hnR : (0 : ℝ) < n := by positivity
  have hspos : 0 < conjugateDisplacement M n := by
    unfold conjugateDisplacement
    exact div_pos (mul_pos hnR (sub_pos.mpr hy1)) (by norm_num)
  have hslt : conjugateDisplacement M n < (n : ℝ) / 2 := by
    unfold conjugateDisplacement
    apply div_lt_div_of_pos_right _ (by norm_num)
    have hy : 1 - conjugate (degree M n) < 1 := by linarith
    have hp : 0 < (n : ℝ) * conjugate (degree M n) := mul_pos hnR hy0
    nlinarith
  refine ⟨hspos, hslt, ?_⟩
  have hs : 2 * displacement M n / (n : ℝ) = epsilon M n := by
    unfold displacement
    field_simp [hnR.ne']
  have hsc : 2 * conjugateDisplacement M n / (n : ℝ) =
      1 - conjugate (degree M n) := by
    unfold conjugateDisplacement
    field_simp [hnR.ne']
  rw [hs, hsc, hdeg]
  have hm := congrArg (fun x : ℝ ↦ x * Real.exp 1) hconj
  calc
    (1 - (1 - conjugate (1 + epsilon M n))) *
        Real.exp (1 - conjugate (1 + epsilon M n)) =
        (conjugate (1 + epsilon M n) *
          Real.exp (-conjugate (1 + epsilon M n))) * Real.exp 1 := by
            rw [show 1 - (1 - conjugate (1 + epsilon M n)) =
              conjugate (1 + epsilon M n) by ring]
            rw [show 1 - conjugate (1 + epsilon M n) =
              -conjugate (1 + epsilon M n) + 1 by ring, Real.exp_add]
            ring
    _ = ((1 + epsilon M n) * Real.exp (-(1 + epsilon M n))) * Real.exp 1 := by
      simpa [hdeg] using! hm
    _ = (1 + epsilon M n) * Real.exp (-epsilon M n) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring
    _ = (1 + epsilon M n) * Real.exp (-2 * displacement M n / n) := by
      have hneg := congrArg Neg.neg hs
      have hneg' : -2 * displacement M n / (n : ℝ) = -epsilon M n := by
        convert hneg using 1 <;> ring
      rw [hneg']

lemma super_center_bound (hR : RateStatement) {M : NatSeq} (hbare : bareSuper M) :
    ∀ᶠ n in atTop, |giantCenter M n - 4 * displacement M n| ≤
      (12 : ℝ) * (displacement M n ^ 2 / n) := by
  obtain ⟨C, e0, hC, he0, _, hTaylor⟩ := hR.2.2.2.2.2
  have he0' := (tendsto_order.1 (bare_epsilon_tendsto_zero (Or.inr hbare))).2 e0 he0
  have heC : ∀ᶠ n in atTop, C * epsilon M n ≤ 1 / 3 := by
    have ht := (bare_epsilon_tendsto_zero (Or.inr hbare)).const_mul C
    exact ((tendsto_order.1 ht).2 (1 / 3) (by norm_num)).mono fun _ h ↦ h.le
  have hepos := bare_epsilon_pos (Or.inr hbare)
  have hside := hbare.2.1
  have hn : ∀ᶠ n : ℕ in atTop, 0 < n := eventually_gt_atTop 0
  filter_upwards [he0', heC, hepos, hside, hn] with n he0n heCn hepos hside hn
  have hdeg : degree M n = 1 + epsilon M n := by
    rw [epsilon, abs_of_pos (sub_pos.mpr hside)]
    ring
  have ht := (hTaylor (epsilon M n) hepos he0n).2.2.2
  have hmain : |giantFraction (degree M n) - 2 * epsilon M n| ≤
      3 * epsilon M n ^ 2 := by
    rw [hdeg]
    calc
      |giantFraction (1 + epsilon M n) - 2 * epsilon M n| ≤
          |giantFraction (1 + epsilon M n) -
              (2 * epsilon M n - 8 * epsilon M n ^ 2 / 3)| +
            8 * epsilon M n ^ 2 / 3 := by
              have := abs_sub_le (giantFraction (1 + epsilon M n))
                (2 * epsilon M n - 8 * epsilon M n ^ 2 / 3)
                (2 * epsilon M n)
              simpa [abs_of_nonneg (by positivity : 0 ≤ 8 * epsilon M n ^ 2 / 3)] using! this
      _ ≤ C * epsilon M n ^ 3 + 8 * epsilon M n ^ 2 / 3 :=
        add_le_add ht (le_refl _)
      _ ≤ 3 * epsilon M n ^ 2 := by
        have := mul_le_mul_of_nonneg_right heCn (sq_nonneg (epsilon M n))
        nlinarith
  have hnR : (0 : ℝ) < n := by positivity
  unfold giantCenter displacement
  have hden : (((n : ℝ) * epsilon M n / 2) ^ 2 / (n : ℝ)) =
      (n : ℝ) * epsilon M n ^ 2 / 4 := by
    field_simp [hnR.ne']
    ring
  rw [hden]
  rw [show (n : ℝ) * giantFraction (degree M n) -
      4 * ((n : ℝ) * epsilon M n / 2) =
      (n : ℝ) * (giantFraction (degree M n) - 2 * epsilon M n) by ring]
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ n)]
  calc
    (n : ℝ) * |giantFraction (degree M n) - 2 * epsilon M n| ≤
        (n : ℝ) * (3 * epsilon M n ^ 2) :=
      mul_le_mul_of_nonneg_left hmain hnR.le
    _ = 12 * ((n : ℝ) * epsilon M n ^ 2 / 4) := by ring

/-- The existing center estimate has the same witness 12 for every edge sequence. -/
lemma uniform_super_center_bound (hR : RateStatement) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : NatSeq, bareSuper M →
      ∀ᶠ n in atTop, |giantCenter M n - 4 * displacement M n| ≤
        C * (displacement M n ^ 2 / n) := by
  refine ⟨12, by norm_num, ?_⟩
  intro M hbare
  exact super_center_bound hR hbare

lemma super_tightness_transfer (hF : FiniteEnumerationStatement)
    (hG : GiantStatement) {M : NatSeq} (hbare : bareSuper M)
    (omega : RealSeq) (homega : ∀ᶠ n in atTop, 0 < omega n)
    (homegaTop : Tendsto omega atTop atTop) :
    Tendsto (fun n ↦ probM n (M n) (fun G ↦
      |(rankSize G 1 : ℝ) - giantCenter M n| <
        omega n * (n : ℝ) / Real.sqrt (displacement M n))) atTop (𝓝 1) := by
  let A : (n : ℕ) → Graph n → Prop := fun n G ↦
    |(rankSize G 1 : ℝ) - giantCenter M n| <
      omega n * (n : ℝ) / Real.sqrt (displacement M n)
  have htight := (hG.1 M hbare).2.1
  have hepos := bare_epsilon_pos (Or.inr hbare)
  have hn : ∀ᶠ n : ℕ in atTop, 0 < n := eventually_gt_atTop 0
  have hbad : Tendsto (fun n ↦ probM n (M n) (fun G ↦ ¬ A n G))
      atTop (𝓝 0) := by
    apply tendsto_order.2
    constructor
    · intro a ha
      filter_upwards with n
      exact lt_of_lt_of_le ha (probM_nonneg n (M n) _)
    · intro b hb
      rcases htight (b / 2) (by linarith) with ⟨K, hK, hbound⟩
      have hdom : ∀ᶠ n in atTop, K < Real.sqrt 2 * omega n :=
        ((tendsto_atTop.1
          (homegaTop.const_mul_atTop (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)))
          (K + 1)).mono fun _ h ↦ by linarith)
      filter_upwards [hbound, hdom, homega, hepos, hn] with n ht hdom homega hepos hn
      have hnR : (0 : ℝ) < n := by positivity
      have hspos : 0 < displacement M n := by
        unfold displacement
        positivity
      have hscale : 0 < Real.sqrt ((n : ℝ) / epsilon M n) :=
        Real.sqrt_pos.2 (div_pos hnR hepos)
      have heq : (n : ℝ) / Real.sqrt (displacement M n) =
          Real.sqrt 2 * Real.sqrt ((n : ℝ) / epsilon M n) := by
        have hsqrtS := Real.sq_sqrt hspos.le
        have hsqrtA := Real.sq_sqrt (div_nonneg hnR.le hepos.le)
        have hsqrt2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
        have hlpos : 0 ≤ (n : ℝ) / Real.sqrt (displacement M n) := by positivity
        have hrpos : 0 ≤ Real.sqrt 2 * Real.sqrt ((n : ℝ) / epsilon M n) := by positivity
        have hlsq : ((n : ℝ) / Real.sqrt (displacement M n)) ^ 2 =
            2 * (n : ℝ) / epsilon M n := by
          rw [div_pow, hsqrtS]
          unfold displacement
          field_simp [hepos.ne', hnR.ne']
        have hrsq : (Real.sqrt 2 * Real.sqrt ((n : ℝ) / epsilon M n)) ^ 2 =
            2 * (n : ℝ) / epsilon M n := by
          rw [mul_pow, hsqrt2, hsqrtA]
          ring
        have hsq : ((n : ℝ) / Real.sqrt (displacement M n)) ^ 2 =
            (Real.sqrt 2 * Real.sqrt ((n : ℝ) / epsilon M n)) ^ 2 :=
          hlsq.trans hrsq.symm
        nlinarith
      have hradius : K * Real.sqrt ((n : ℝ) / epsilon M n) <
          omega n * (n : ℝ) / Real.sqrt (displacement M n) := by
        calc
          K * Real.sqrt ((n : ℝ) / epsilon M n) <
              (Real.sqrt 2 * omega n) * Real.sqrt ((n : ℝ) / epsilon M n) :=
            by nlinarith [mul_pos (sub_pos.mpr hdom) hscale]
          _ = omega n * (n : ℝ) / Real.sqrt (displacement M n) := by
            rw [show omega n * (n : ℝ) / Real.sqrt (displacement M n) =
              omega n * ((n : ℝ) / Real.sqrt (displacement M n)) by ring, heq]
            ring
      calc
        probM n (M n) (fun G ↦ ¬ A n G) ≤
            probM n (M n) (fun G ↦
              |(rankSize G 1 : ℝ) - giantCenter M n| >
                K * Real.sqrt ((n : ℝ) / epsilon M n)) := by
          apply probM_mono
          intro G hnot
          dsimp [A] at hnot
          push_neg at hnot
          exact lt_of_lt_of_le hradius hnot
        _ ≤ b / 2 := ht
        _ < b := by linarith
  have hcomp : ∀ᶠ n in atTop,
      probM n (M n) (A n) = 1 - probM n (M n) (fun G ↦ ¬ A n G) := by
    filter_upwards [hbare.1] with n hn
    exact probM_compl_eq_one_sub hF hn (A n)
  have ht := (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 1)).sub hbad
  have ht' := ht.congr' (hcomp.mono fun _ hn ↦ hn.symm)
  simpa [A] using! ht'

lemma barelySupercriticalLaw_of_inputs
    (hF : FiniteEnumerationStatement) (hR : RateStatement)
    (hP : PoissonStatement) (hC : CyclicStructureStatement)
    (hG : GiantStatement) : barelySupercriticalLaw := by
  refine ⟨uniform_super_center_bound hR, ?_⟩
  intro M hbare
  refine ⟨fun r ↦ super_fixedCDF hF hR hP hC hG hbare r,
    (hG.1 M hbare).2.2, super_conjugate_equation hR hbare, ?_⟩
  intro omega homega homegaTop
  exact super_tightness_transfer hF hG hbare omega homega homegaTop

end

end Erdos745.WrapUp.Proofs.Internal.W12_NEAR_Laws
