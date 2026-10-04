module

public import Erdos745.WrapUp.Proofs.Internal.Linked.W10_Core
public import Erdos745.WrapUp.Proofs.Internal.Linked.W06_P03

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local simp] Pi.div_def Pi.mul_def Pi.add_def Pi.sub_def Pi.neg_def Pi.inv_def Function.comp_def Pi.pow_def Pi.smul_def Real.rpow_eq_pow

@[expose] public section


namespace Erdos745.WrapUp.Proofs.Internal.W10_GIANT_Trees

noncomputable section
open Filter
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

open Erdos745.WrapUp.Proofs.W06_POISSON
open Erdos745.WrapUp.Proofs.Internal.W08_CYCLIC_Finite
open Erdos745.WrapUp.Proofs.Internal.W10_GIANT_Exclusions

lemma treeCount_expect_eq_factorialTupleSum (hF : FiniteEnumerationStatement)
    {n M h : ℕ} (hM : M ≤ capacity n) (hh : 0 < h) :
    expectM n M (fun G ↦ (treeCountGE G h : ℝ)) =
      factorialTupleSum n M 1 h := by
  simpa [falling] using!
    (factorialMoment_treeCountGE_internal hF n M 1 h hM hh)

lemma factorialTupleSum_one_eq_outside (n M h : ℕ) (hh : 0 < h) :
    factorialTupleSum n M 1 h =
      outsideRectangleTupleSum n M 1 h (h - 1) := by
  classical
  rw [factorialTupleSum, outsideRectangleTupleSum]
  apply Finset.sum_congr rfl
  intro ks _
  by_cases hk : h ≤ (ks 0).val
  · have hall : ∀ i : Fin 1, h ≤ (ks i).val := by
      intro i
      simpa [Fin.eq_zero i] using! hk
    have hex : ∃ i : Fin 1, h - 1 < (ks i).val := by
      exact ⟨0, by omega⟩
    simp [hall, hex]
  · have hall : ¬∀ i : Fin 1, h ≤ (ks i).val := by
      intro H
      exact hk (H 0)
    simp [hall]

lemma prob_tree_pos_le_expect (hF : FiniteEnumerationStatement)
    {n M h : ℕ} (hM : M ≤ capacity n) :
    probM n M (fun G ↦ 0 < treeCountGE G h) ≤
      expectM n M (fun G ↦ (treeCountGE G h : ℝ)) := by
  apply probM_le_expectM_of_indicator hF hM
  · intro G
    positivity
  · intro G hG
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hG))

lemma near_cutoff_prefactor_le_two :
    ∀ᶠ n : ℕ in atTop,
      (n : ℝ) * finitePowerTail n (largeCutoff n) ≤ 2 := by
  filter_upwards [largeCutoff_eventually_pos, eventually_gt_atTop 0] with n hcut hn
  have htail := finitePowerTail_le n (largeCutoff n) hcut
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn
  have hp : 0 < n23 n := Real.rpow_pos_of_pos hnpos _
  have hceil : n23 n ≤ (largeCutoff n : ℝ) := Nat.le_ceil _
  have hpow : Real.rpow (largeCutoff n : ℝ) (-3 / 2 : ℝ) ≤
      Real.rpow (n23 n) (-3 / 2 : ℝ) :=
    Real.rpow_le_rpow_of_nonpos hp hceil (by norm_num)
  have hn23pow : Real.rpow (n23 n) (-3 / 2 : ℝ) = (n : ℝ)⁻¹ := by
    unfold n23
    calc
      Real.rpow (Real.rpow (n : ℝ) (2 / 3 : ℝ)) (-3 / 2 : ℝ) =
          Real.rpow (n : ℝ) ((2 / 3 : ℝ) * (-3 / 2 : ℝ)) :=
        (Real.rpow_mul hnpos.le (2 / 3 : ℝ) (-3 / 2 : ℝ)).symm
      _ = (n : ℝ)⁻¹ := by
        norm_num
        exact Real.rpow_neg_one (n : ℝ)
  calc
    (n : ℝ) * finitePowerTail n (largeCutoff n) ≤
        (n : ℝ) * (2 * Real.rpow (largeCutoff n : ℝ) (-3 / 2 : ℝ)) := by
      gcongr
    _ ≤ (n : ℝ) * (2 * Real.rpow (n23 n) (-3 / 2 : ℝ)) := by
      gcongr
    _ = 2 := by rw [hn23pow]; field_simp

lemma near_cutoff_exponent_tendsto_atTop {M : NatSeq}
    (hbare : bareSuper M) :
    Tendsto (fun n ↦ epsilon M n ^ 2 * ((largeCutoff n - 1 : ℕ) : ℝ))
      atTop atTop := by
  have hw := hbare.2.2.2
  have hwpow : Tendsto
      (fun n ↦ Real.rpow (widthParameter M n) (2 / 3 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 3)).comp hw
  have he := bare_epsilon_tendsto_zero (Or.inr hbare)
  have he2 : Tendsto (fun n ↦ epsilon M n ^ 2) atTop (𝓝 0) := by
    simpa using! he.pow 2
  have hdiff : Tendsto (fun n ↦
      Real.rpow (widthParameter M n) (2 / 3 : ℝ) - 1) atTop atTop := by
    simpa [sub_eq_add_neg] using!
      (tendsto_atTop_add_const_right atTop (-1 : ℝ) hwpow)
  apply tendsto_atTop_mono' atTop _ hdiff
  filter_upwards [bare_epsilon_pos (Or.inr hbare), eventually_gt_atTop 0,
      (tendsto_order.1 he2).2 1 zero_lt_one]
      with n hepos hn heone
  have hceil : n23 n ≤ (largeCutoff n : ℝ) := Nat.le_ceil _
  have hsub : n23 n - 1 ≤ ((largeCutoff n - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by
      have hp : 0 < n23 n := Real.rpow_pos_of_pos (by exact_mod_cast hn) _
      have hcut : 0 < largeCutoff n := by exact_mod_cast hp.trans_le hceil
      exact hcut)]
    simpa using! sub_le_sub_right hceil (1 : ℝ)
  have hid := width_rpow_two_thirds (M := M) hn hepos
  calc
    Real.rpow (widthParameter M n) (2 / 3 : ℝ) - 1 ≤
        Real.rpow (widthParameter M n) (2 / 3 : ℝ) - epsilon M n ^ 2 := by
          linarith
    _ = epsilon M n ^ 2 * (n23 n - 1) := by rw [hid]; ring
    _ ≤ epsilon M n ^ 2 * ((largeCutoff n - 1 : ℕ) : ℝ) := by gcongr

lemma near_tree_expect_tendsto_zero (hF : FiniteEnumerationStatement)
    (hTuple : TupleEstimatesStatement) {M : NatSeq} (hbare : bareSuper M) :
    Tendsto (fun n ↦ expectM n (M n)
      (fun G ↦ (treeCountGE G (largeCutoff n) : ℝ))) atTop (𝓝 0) := by
  obtain ⟨C, kappa, hC, hkappa, n0, hglobal⟩ := hTuple.1 1 (by omega)
  have hdegLo : ∀ᶠ n in atTop, (1 / 2 : ℝ) ≤ degree M n :=
    ((tendsto_order.1 hbare.2.2.1).1 (1 / 2) (by norm_num)).mono fun _ h ↦ h.le
  have hdegHi : ∀ᶠ n in atTop, degree M n ≤ (3 / 2 : ℝ) :=
    ((tendsto_order.1 hbare.2.2.1).2 (3 / 2) (by norm_num)).mono fun _ h ↦ h.le
  have hexp : Tendsto (fun n ↦
      Real.exp (-kappa * (epsilon M n ^ 2 * ((largeCutoff n - 1 : ℕ) : ℝ))))
      atTop (𝓝 0) := by
    have htop := (near_cutoff_exponent_tendsto_atTop hbare).const_mul_atTop hkappa
    simpa only [Function.comp_def, neg_mul] using!
      Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp htop)
  apply squeeze_zero' (g := fun n ↦
    2 * C * Real.exp (-kappa * (epsilon M n ^ 2 *
      ((largeCutoff n - 1 : ℕ) : ℝ))))
  · filter_upwards with n
    exact W09_TREE_MASS_Finite.expectM_nonneg fun G ↦ by positivity
  · filter_upwards [hbare.1, hdegLo, hdegHi, largeCutoff_eventually_pos,
      eventually_ge_atTop n0, near_cutoff_prefactor_le_two]
      with n hcap hlo hhi hh hn0 hpref
    rw [treeCount_expect_eq_factorialTupleSum hF hcap hh,
      factorialTupleSum_one_eq_outside n (M n) (largeCutoff n) hh]
    have hg := outsideRectangleTupleSum_le_global n (M n) 1
      (largeCutoff n) (largeCutoff n - 1) C kappa hC.le hkappa hlo
      (fun ks hpos ↦ (hglobal n (M n) ks hn0 hcap hlo hhi hpos).1) hh
    have hnonneg : 0 ≤ C * Real.exp
        (-kappa * (epsilon M n ^ 2 * ((largeCutoff n - 1 : ℕ) : ℝ))) := by positivity
    calc
      outsideRectangleTupleSum n (M n) 1 (largeCutoff n) (largeCutoff n - 1) ≤
          C * (n : ℝ) ^ 1 *
            Real.exp (-kappa * epsilon M n ^ 2 * ((largeCutoff n - 1 : ℕ) : ℝ)) *
              finitePowerTail n (largeCutoff n) ^ 1 := hg
      _ = C * Real.exp
          (-kappa * (epsilon M n ^ 2 * ((largeCutoff n - 1 : ℕ) : ℝ))) *
            ((n : ℝ) * finitePowerTail n (largeCutoff n)) := by ring
      _ ≤ C * Real.exp
          (-kappa * (epsilon M n ^ 2 * ((largeCutoff n - 1 : ℕ) : ℝ))) * 2 := by
        gcongr
      _ = 2 * C * Real.exp
          (-kappa * (epsilon M n ^ 2 * ((largeCutoff n - 1 : ℕ) : ℝ))) := by ring
  · simpa using! hexp.const_mul (2 * C)

theorem near_tree_bad_tendsto_zero (hF : FiniteEnumerationStatement)
    (hTuple : TupleEstimatesStatement) {M : NatSeq} (hbare : bareSuper M) :
    Tendsto (fun n ↦ probM n (M n)
      (fun G ↦ 0 < treeCountGE G (largeCutoff n))) atTop (𝓝 0) := by
  apply squeeze_zero'
  · filter_upwards with n
    unfold probM
    positivity
  · filter_upwards [hbare.1] with n hcap
    exact prob_tree_pos_le_expect hF hcap
  · exact near_tree_expect_tendsto_zero hF hTuple hbare

lemma factorialTupleSum_one_le_tupleTail (n M h : ℕ) (B : ℝ)
    (hh : 0 < h) (hlog : B * Real.log (n : ℝ) < h) :
    factorialTupleSum n M 1 h ≤ tupleTail n M 1 0 B := by
  classical
  rw [factorialTupleSum, tupleTail]
  apply Finset.sum_le_sum
  intro ks _
  by_cases hall : ∀ i : Fin 1, h ≤ (ks i).val
  · have hpos : ∀ i : Fin 1, 0 < (ks i).val :=
      fun i ↦ hh.trans_le (hall i)
    have hex : ∃ i : Fin 1, B * Real.log n < ((ks i).val : ℝ) := by
      refine ⟨0, hlog.trans_le ?_⟩
      exact_mod_cast hall 0
    simp [hall, hpos, hex]
  · rw [if_neg hall]
    split_ifs
    · simpa using! tupleMoment_nonneg n M 1 (fun i ↦ (ks i).val)
    · exact le_refl 0

lemma log_lt_largeCutoff_eventually (B : ℝ) :
    ∀ᶠ n : ℕ in atTop, B * Real.log (n : ℝ) < largeCutoff n := by
  let N : RealSeq := fun n ↦ (n : ℝ)
  have hN : Tendsto N atTop atTop := tendsto_natCast_atTop_atTop
  have hratio : Tendsto
      (fun n ↦ B * Real.log (N n) / Real.rpow (N n) (2 / 3 : ℝ))
      atTop (𝓝 0) := by
    have h := (isLittleO_log_rpow_atTop
      (by norm_num : (0 : ℝ) < 2 / 3)).tendsto_div_nhds_zero
    simpa [N, mul_div_assoc] using! (h.comp hN).const_mul B
  have hlt := (tendsto_order.1 hratio).2 1 zero_lt_one
  have hpos := (tendsto_atTop.1 hN) 1
  filter_upwards [hlt, hpos] with n hn hnpos
  have hp : 0 < Real.rpow (N n) (2 / 3 : ℝ) :=
    Real.rpow_pos_of_pos (zero_lt_one.trans_le hnpos) _
  have hreal : B * Real.log (N n) < Real.rpow (N n) (2 / 3 : ℝ) :=
    (div_lt_one hp).mp hn
  exact hreal.trans_le (Nat.le_ceil _)

lemma fixed_tree_expect_tendsto_zero (hF : FiniteEnumerationStatement)
    (hTuple : TupleEstimatesStatement) {M : NatSeq} {lam : ℝ}
    (hM : admissible M) (hlam : 1 < lam)
    (hdeg : Tendsto (degree M) atTop (𝓝 lam)) :
    Tendsto (fun n ↦ expectM n (M n)
      (fun G ↦ (treeCountGE G (largeCutoff n) : ℝ))) atTop (𝓝 0) := by
  let lo : ℝ := lam / 2
  let hi : ℝ := 3 * lam / 2
  let delta : ℝ := (lam - 1) / 2
  have hlo : 0 < lo := by dsimp [lo]; linarith
  have hlohi : lo ≤ hi := by dsimp [lo, hi]; linarith
  have hdelta : 0 < delta := by dsimp [delta]; linarith
  obtain ⟨B, hB, n0, htail⟩ :=
    hTuple.2.2.2 lo hi delta 1 1 0 hlo hlohi hdelta (by norm_num) (by omega)
  have hdegLo : ∀ᶠ n in atTop, lo ≤ degree M n :=
    ((tendsto_order.1 hdeg).1 lo (by dsimp [lo]; linarith)).mono fun _ h ↦ h.le
  have hdegHi : ∀ᶠ n in atTop, degree M n ≤ hi :=
    ((tendsto_order.1 hdeg).2 hi (by dsimp [hi]; linarith)).mono fun _ h ↦ h.le
  have haway : ∀ᶠ n in atTop, delta ≤ |degree M n - 1| := by
    have hlower : ∀ᶠ n in atTop, 1 + delta ≤ degree M n :=
      ((tendsto_order.1 hdeg).1 (1 + delta) (by dsimp [delta]; linarith)).mono
        fun _ h ↦ h.le
    filter_upwards [hlower] with n hn
    rw [abs_of_nonneg (sub_nonneg.mpr (by linarith))]
    linarith
  have hlog := log_lt_largeCutoff_eventually B
  apply squeeze_zero' (g := fun n : ℕ ↦ Real.rpow (n : ℝ) (-1 : ℝ))
  · filter_upwards with n
    exact W09_TREE_MASS_Finite.expectM_nonneg fun G ↦ by positivity
  · filter_upwards [hM, hdegLo, hdegHi, haway, hlog,
      largeCutoff_eventually_pos, eventually_ge_atTop n0]
      with n hcap hdlo hdhi hda hlogn hh hn0
    rw [treeCount_expect_eq_factorialTupleSum hF hcap hh]
    exact (factorialTupleSum_one_le_tupleTail n (M n) (largeCutoff n) B hh hlogn).trans
      (htail n (M n) hn0 hcap hdlo hdhi hda)
  · have hinv : Tendsto (fun n : ℕ ↦ Real.rpow (n : ℝ) (-1 : ℝ))
        atTop (𝓝 0) := by
      simpa using! (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1)).comp
        tendsto_natCast_atTop_atTop
    simpa using! hinv

theorem fixed_tree_bad_tendsto_zero (hF : FiniteEnumerationStatement)
    (hTuple : TupleEstimatesStatement) {M : NatSeq} {lam : ℝ}
    (hM : admissible M) (hlam : 1 < lam)
    (hdeg : Tendsto (degree M) atTop (𝓝 lam)) :
    Tendsto (fun n ↦ probM n (M n)
      (fun G ↦ 0 < treeCountGE G (largeCutoff n))) atTop (𝓝 0) := by
  apply squeeze_zero'
  · filter_upwards with n
    unfold probM
    positivity
  · filter_upwards [hM] with n hcap
    exact prob_tree_pos_le_expect hF hcap
  · exact fixed_tree_expect_tendsto_zero hF hTuple hM hlam hdeg

end
end Erdos745.WrapUp.Proofs.Internal.W10_GIANT_Trees


namespace Erdos745.WrapUp.Proofs.Internal.W10_GIANT_Sprinkling

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

open W01_ENUM_Trees
open W10_GIANT_Components
open W10_GIANT_Bridges

/-! A cut can be indexed by complete old components. This keeps every query
disjoint from the old graph and measures its size by the old large mass. -/

def largeFamily {n : ℕ} (G : Graph n) (h : ℕ) : Finset (Finset (Fin n)) :=
  (components G).filter fun S => h ≤ S.card

def vertices {n : ℕ} (R : Finset (Finset (Fin n))) : Finset (Fin n) :=
  R.biUnion id

lemma mem_vertices {n : ℕ} {R : Finset (Finset (Fin n))} {x : Fin n} :
    x ∈ vertices R ↔ ∃ S ∈ R, x ∈ S := by
  simp [vertices]

lemma vertices_card {n : ℕ} {G : Graph n}
    {R : Finset (Finset (Fin n))} (hR : R ⊆ components G) :
    (vertices R).card = ∑ S ∈ R, S.card := by
  unfold vertices
  rw [Finset.card_biUnion (by
    intro S hS T hT hST
    exact components_pairwiseDisjoint G (hR hS) (hR hT) hST)]
  rfl

lemma largeFamily_subset {n : ℕ} (G : Graph n) (h : ℕ) :
    largeFamily G h ⊆ components G := Finset.filter_subset _ _

lemma largeFamily_vertices {n : ℕ} (G : Graph n) (h : ℕ) :
    vertices (largeFamily G h) = largeVertices G h := by
  ext x
  rw [mem_vertices, mem_largeVertices_iff]
  simp only [largeFamily, Finset.mem_filter]
  tauto

lemma largeFamily_mass {n : ℕ} (G : Graph n) (h : ℕ) :
    largeMass G h = ((vertices (largeFamily G h)).card : ℝ) := by
  rw [largeFamily_vertices, largeMass_eq_card_largeVertices]

lemma vertices_disjoint {n : ℕ} {G : Graph n}
    {R K : Finset (Finset (Fin n))}
    (hR : R ⊆ components G) (hK : K ⊆ components G)
    (hRK : Disjoint R K) : Disjoint (vertices R) (vertices K) := by
  apply Finset.disjoint_left.mpr
  intro x hxR hxK
  rcases mem_vertices.mp hxR with ⟨S, hS, hxS⟩
  rcases mem_vertices.mp hxK with ⟨T, hT, hxT⟩
  by_cases hST : S = T
  · exact (Finset.disjoint_left.mp hRK) hS (hST ▸ hT)
  · exact (Finset.disjoint_left.mp
      (components_pairwiseDisjoint G (hR hS) (hK hT) hST)) hxS hxT

lemma vertices_sdiff_union {n : ℕ} {K R : Finset (Finset (Fin n))}
    (hRK : R ⊆ K) :
    vertices R ∪ vertices (K \ R) = vertices K := by
  ext x
  simp only [Finset.mem_union, mem_vertices, Finset.mem_sdiff]
  constructor
  · rintro (⟨S, hS, hx⟩ | ⟨S, hS, hx⟩)
    · exact ⟨S, hRK hS, hx⟩
    · exact ⟨S, hS.1, hx⟩
  · rintro ⟨S, hS, hx⟩
    by_cases hSR : S ∈ R
    · exact Or.inl ⟨S, hSR, hx⟩
    · exact Or.inr ⟨S, ⟨hS, hSR⟩, hx⟩

lemma vertices_partition_card {n : ℕ} {G : Graph n}
    {K R : Finset (Finset (Fin n))}
    (hK : K ⊆ components G) (hRK : R ⊆ K) :
    (vertices R).card + (vertices (K \ R)).card = (vertices K).card := by
  rw [← Finset.card_union_of_disjoint]
  · exact congrArg Finset.card (vertices_sdiff_union hRK)
  · exact vertices_disjoint (hRK.trans hK) (Finset.sdiff_subset.trans hK)
      (Finset.disjoint_left.mpr (by
        intro S hS hdiff
        exact (Finset.mem_sdiff.mp hdiff).2 hS))

lemma family_card_lower {n h : ℕ} {G : Graph n}
    {R : Finset (Finset (Fin n))} (hR : R ⊆ largeFamily G h) :
    h * R.card ≤ (vertices R).card := by
  rw [vertices_card (hR.trans (largeFamily_subset G h))]
  calc
    h * R.card = ∑ _S ∈ R, h := by simp [Finset.sum_const, Nat.mul_comm]
    _ ≤ ∑ S ∈ R, S.card := by
      apply Finset.sum_le_sum
      intro S hS
      exact (Finset.mem_filter.mp (hR hS)).2

def cutEdges {n : ℕ} (V W : Finset (Fin n)) : Graph n :=
  (Finset.univ : Finset (Edge n)).filter fun e =>
    (e.1.1 ∈ V ∧ e.1.2 ∈ W) ∨ (e.1.1 ∈ W ∧ e.1.2 ∈ V)

lemma mem_cutEdges {n : ℕ} {V W : Finset (Fin n)} {e : Edge n} :
    e ∈ cutEdges V W ↔
      (e.1.1 ∈ V ∧ e.1.2 ∈ W) ∨ (e.1.1 ∈ W ∧ e.1.2 ∈ V) := by
  simp [cutEdges]

lemma cutEdges_symm {n : ℕ} (V W : Finset (Fin n)) :
    cutEdges V W = cutEdges W V := by
  ext e
  simp only [mem_cutEdges]
  tauto

private def orderedEdge {n : ℕ} (u v : Fin n) (hne : u ≠ v) : Edge n :=
  if huv : u < v then ⟨(u, v), huv⟩
  else ⟨(v, u), lt_of_le_of_ne (le_of_not_gt huv) (Ne.symm hne)⟩

private lemma orderedEdge_cross_injective {n : ℕ}
    {V W : Finset (Fin n)} (hVW : Disjoint V W)
    {u u' v v' : Fin n} (hu : u ∈ V) (_hu' : u' ∈ V)
    (_hv : v ∈ W) (hv' : v' ∈ W)
    (hne : u ≠ v) (hne' : u' ≠ v')
    (he : orderedEdge u v hne = orderedEdge u' v' hne') :
    u = u' ∧ v = v' := by
  have hp := congrArg Subtype.val he
  by_cases h1 : u < v <;> by_cases h2 : u' < v'
  · simp only [orderedEdge, dif_pos h1, dif_pos h2] at hp
    exact Prod.mk.inj hp
  · simp only [orderedEdge, dif_pos h1, dif_neg h2] at hp
    have hswap := Prod.mk.inj hp
    exact False.elim ((Finset.disjoint_left.mp hVW) hu (hswap.1 ▸ hv'))
  · simp only [orderedEdge, dif_neg h1, dif_pos h2] at hp
    have hswap := Prod.mk.inj hp
    exact False.elim ((Finset.disjoint_left.mp hVW) hu (hswap.2 ▸ hv'))
  · simp only [orderedEdge, dif_neg h1, dif_neg h2] at hp
    obtain ⟨hvEq, huEq⟩ := Prod.mk.inj hp
    exact ⟨huEq, hvEq⟩

lemma cutEdges_card {n : ℕ} {V W : Finset (Fin n)}
    (hVW : Disjoint V W) :
    (cutEdges V W).card = V.card * W.card := by
  rw [← Finset.card_product]
  symm
  apply Finset.card_bij
    (fun p hp =>
      orderedEdge p.1 p.2 (by
        intro heq
        have hmem := Finset.mem_product.mp hp
        exact (Finset.disjoint_left.mp hVW) hmem.1 (heq ▸ hmem.2)))
  · intro p hp
    have hmem := Finset.mem_product.mp hp
    by_cases hlt : p.1 < p.2
    · exact mem_cutEdges.mpr (Or.inl (by
        simpa [orderedEdge, hlt] using! hmem))
    · exact mem_cutEdges.mpr (Or.inr (by
        simpa [orderedEdge, hlt] using! And.symm hmem))
  · intro p hp q hq heq
    have hpm := Finset.mem_product.mp hp
    have hqm := Finset.mem_product.mp hq
    obtain ⟨hfst, hsnd⟩ := orderedEdge_cross_injective hVW
      hpm.1 hqm.1 hpm.2 hqm.2 _ _ heq
    exact Prod.ext hfst hsnd
  · intro e he
    rcases mem_cutEdges.mp he with h | h
    · refine ⟨(e.1.1, e.1.2), Finset.mem_product.mpr h, ?_⟩
      simp [orderedEdge, e.2]
    · refine ⟨(e.1.2, e.1.1), Finset.mem_product.mpr ⟨h.2, h.1⟩, ?_⟩
      have hlt : ¬ e.1.2 < e.1.1 := not_lt_of_ge e.2.le
      simp [orderedEdge, hlt]

def cutQuery {n : ℕ} (K R : Finset (Finset (Fin n))) : Graph n :=
  cutEdges (vertices R) (vertices (K \ R))

lemma cutQuery_card {n : ℕ} {G : Graph n}
    {K R : Finset (Finset (Fin n))}
    (hK : K ⊆ components G) (hRK : R ⊆ K) :
    (cutQuery K R).card =
      (vertices R).card * (vertices (K \ R)).card := by
  unfold cutQuery
  exact cutEdges_card (vertices_disjoint (hRK.trans hK)
    (Finset.sdiff_subset.trans hK) (Finset.disjoint_left.mpr (by
      intro S hS hdiff
      exact (Finset.mem_sdiff.mp hdiff).2 hS)))

lemma cutQuery_compl {n : ℕ} {K R : Finset (Finset (Fin n))}
    (hRK : R ⊆ K) : cutQuery K (K \ R) = cutQuery K R := by
  unfold cutQuery
  rw [Finset.sdiff_sdiff_eq_self hRK]
  exact cutEdges_symm _ _

private lemma adjacent_same_component {n : ℕ} {G : Graph n}
    {x y : Fin n} (hxy : adj G x y) :
    componentOf G x = componentOf G y :=
  componentOf_eq_of_reach (Relation.ReflTransGen.single hxy)

lemma cutQuery_disjoint_old {n h : ℕ} (G : Graph n)
    {R : Finset (Finset (Fin n))} (hR : R ⊆ largeFamily G h) :
    Disjoint G (cutQuery (largeFamily G h) R) := by
  apply Finset.disjoint_left.mpr
  intro e heG heQ
  rcases mem_cutEdges.mp heQ with hcut | hcut
  · rcases mem_vertices.mp hcut.1 with ⟨S, hS, hxS⟩
    rcases mem_vertices.mp hcut.2 with ⟨T, hT, hyT⟩
    have hST : S = T := by
      have heq := adjacent_same_component (G := G)
        (x := e.1.1) (y := e.1.2) ⟨e, heG, Or.inl ⟨rfl, rfl⟩⟩
      exact (componentOf_eq_of_mem ((largeFamily_subset G h) (hR hS)) hxS).symm.trans
        (heq.trans (componentOf_eq_of_mem
          ((largeFamily_subset G h) (Finset.mem_sdiff.mp hT).1) hyT))
    exact (Finset.mem_sdiff.mp hT).2 (hST ▸ hS)
  · rcases mem_vertices.mp hcut.2 with ⟨S, hS, hxS⟩
    rcases mem_vertices.mp hcut.1 with ⟨T, hT, hyT⟩
    have hST : S = T := by
      have heq := adjacent_same_component (G := G)
        (x := e.1.1) (y := e.1.2) ⟨e, heG, Or.inl ⟨rfl, rfl⟩⟩
      exact (componentOf_eq_of_mem ((largeFamily_subset G h) (hR hS)) hxS).symm.trans
        (heq.symm.trans (componentOf_eq_of_mem
          ((largeFamily_subset G h) (Finset.mem_sdiff.mp hT).1) hyT))
    exact (Finset.mem_sdiff.mp hT).2 (hST ▸ hS)

/-! The finite union bound is stated for an arbitrary family of graph events;
the sprinkling estimate below applies it to all proper component cuts. -/

lemma growProb_mono {n t : ℕ} {G : Graph n}
    {A B : Graph n → Prop} (hAB : ∀ H, A H → B H) :
    growProb G t A ≤ growProb G t B := by
  unfold growProb
  apply div_le_div_of_nonneg_right
  · apply Nat.cast_le.mpr
    apply Finset.card_le_card
    intro H hH
    obtain ⟨hC, hA⟩ := Finset.mem_filter.mp hH
    exact Finset.mem_filter.mpr ⟨hC, hAB H hA⟩
  · positivity

lemma growProb_union_le {n t : ℕ} {G : Graph n}
    (A B : Graph n → Prop) :
    growProb G t (fun H => A H ∨ B H) ≤
      growProb G t A + growProb G t B := by
  let C := (allGraphs n).filter fun H => G ⊆ H ∧ H.card = G.card + t
  have hsub : (C.filter fun H => A H ∨ B H) ⊆
      (C.filter A) ∪ (C.filter B) := by
    intro H hH
    rcases (Finset.mem_filter.mp hH).2 with hA | hB
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr
        ⟨(Finset.mem_filter.mp hH).1, hA⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr
        ⟨(Finset.mem_filter.mp hH).1, hB⟩)
  have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hcr : ((C.filter fun H => A H ∨ B H).card : ℝ) ≤
      ((C.filter A).card : ℝ) + ((C.filter B).card : ℝ) := by
    exact_mod_cast hc
  have hgoal : ((C.filter fun H => A H ∨ B H).card : ℝ) / (C.card : ℝ) ≤
      ((C.filter A).card : ℝ) / (C.card : ℝ) +
      ((C.filter B).card : ℝ) / (C.card : ℝ) := by
    calc
      _ ≤ (((C.filter A).card : ℝ) + ((C.filter B).card : ℝ)) /
          (C.card : ℝ) := div_le_div_of_nonneg_right hcr (by positivity)
      _ = _ := add_div _ _ _
  convert hgoal using 1 <;> simp only [growProb, C] <;>
    congr 1 <;> congr 1 <;> congr 1 <;> ext H <;> simp

lemma growProb_finite_union_le {n t : ℕ} {G : Graph n}
    {ι : Type*} (s : Finset ι) (A : ι → Graph n → Prop) :
    growProb G t (fun H => ∃ i ∈ s, A i H) ≤
      ∑ i ∈ s, growProb G t (A i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [growProb]
  | @insert i s hi ih =>
      have hm : growProb G t (fun H => ∃ j ∈ insert i s, A j H) ≤
          growProb G t (fun H => A i H ∨ ∃ j ∈ s, A j H) :=
        growProb_mono (by
          intro H hH
          rcases hH with ⟨j, hj, hAj⟩
          rcases Finset.mem_insert.mp hj with rfl | hj
          · exact Or.inl hAj
          · exact Or.inr ⟨j, hj, hAj⟩)
      exact (hm.trans (growProb_union_le _ _)).trans (by
        rw [Finset.sum_insert hi]
        linarith)

private lemma no_edge_leaves_component {n : ℕ} {H : Graph n}
    {T : Finset (Fin n)} (hT : T ∈ components H)
    {x y : Fin n} (hx : x ∈ T) (hxy : adj H x y) : y ∈ T := by
  have hxT := componentOf_eq_of_mem hT hx
  have hy : y ∈ componentOf H y := componentOf_self H y
  rw [← adjacent_same_component hxy, hxT] at hy
  exact hy

private lemma vertices_of_selected_subset {n : ℕ}
    {R : Finset (Finset (Fin n))} {T : Finset (Fin n)}
    (hR : ∀ S ∈ R, S ⊆ T) : vertices R ⊆ T := by
  intro x hx
  rcases mem_vertices.mp hx with ⟨S, hS, hxS⟩
  exact hR S hS hxS

lemma exists_separating_cut {n h : ℕ} {G H : Graph n}
    (hGH : G ⊆ H)
    (hex : (largeFamily G h).Nonempty)
    (hfail : ¬ oldLargeJoined G H h) :
    ∃ R : Finset (Finset (Fin n)),
      R ⊆ largeFamily G h ∧ R.Nonempty ∧
      ((largeFamily G h) \ R).Nonempty ∧
      2 * (vertices R).card ≤ (vertices (largeFamily G h)).card ∧
      Disjoint H (cutQuery (largeFamily G h) R) := by
  let K := largeFamily G h
  obtain ⟨S₀, hS₀⟩ := hex
  obtain ⟨T, hT, hS₀T⟩ := component_coarsens hGH
    (largeFamily_subset G h hS₀)
  let R₀ := K.filter fun S => S ⊆ T
  have hR₀K : R₀ ⊆ K := Finset.filter_subset _ _
  have hR₀ : R₀.Nonempty :=
    ⟨S₀, Finset.mem_filter.mpr ⟨hS₀, hS₀T⟩⟩
  have hmissing : ∃ S ∈ K, ¬ S ⊆ T := by
    by_contra hnone
    push_neg at hnone
    apply hfail
    refine ⟨T, hT, ?_⟩
    intro S hS hSl
    have hSK : S ∈ K := Finset.mem_filter.mpr ⟨hS, hSl⟩
    exact hnone S hSK
  obtain ⟨S₁, hS₁, hS₁T⟩ := hmissing
  have hcomp₀ : (K \ R₀).Nonempty := by
    refine ⟨S₁, Finset.mem_sdiff.mpr ⟨hS₁, ?_⟩⟩
    exact fun hmem => hS₁T (Finset.mem_filter.mp hmem).2
  have hinside : vertices R₀ ⊆ T := by
    apply vertices_of_selected_subset
    intro S hS
    exact (Finset.mem_filter.mp hS).2
  have houtside : Disjoint (vertices (K \ R₀)) T := by
    apply Finset.disjoint_left.mpr
    intro x hx hTmem
    rcases mem_vertices.mp hx with ⟨S, hS, hxS⟩
    have hSK : S ∈ K := (Finset.mem_sdiff.mp hS).1
    have hSx := componentOf_eq_of_mem
      (largeFamily_subset G h hSK) hxS
    have hTx := componentOf_eq_of_mem hT hTmem
    have hST : S ⊆ T := by
      rw [← hSx, ← hTx]
      exact componentOf_subset hGH x
    exact (Finset.mem_sdiff.mp hS).2
      (Finset.mem_filter.mpr ⟨hSK, hST⟩)
  have hcut : Disjoint H (cutQuery K R₀) := by
    apply Finset.disjoint_left.mpr
    intro e heH heQ
    rcases mem_cutEdges.mp heQ with h | h
    · have hxT := hinside h.1
      have hyT := no_edge_leaves_component hT hxT
        (show adj H e.1.1 e.1.2 from ⟨e, heH, Or.inl ⟨rfl, rfl⟩⟩)
      exact (Finset.disjoint_left.mp houtside) h.2 hyT
    · have hyT := hinside h.2
      have hxT := no_edge_leaves_component hT hyT
        (show adj H e.1.2 e.1.1 from ⟨e, heH, Or.inr ⟨rfl, rfl⟩⟩)
      exact (Finset.disjoint_left.mp houtside) h.1 hxT
  by_cases hsmall : 2 * (vertices R₀).card ≤ (vertices K).card
  · exact ⟨R₀, hR₀K, hR₀, hcomp₀, hsmall, hcut⟩
  · let R := K \ R₀
    have hpart := vertices_partition_card (largeFamily_subset G h) hR₀K
    have hsmall' : 2 * (vertices R).card ≤ (vertices K).card := by
      dsimp [R, K] at hpart hsmall ⊢
      omega
    have hcomp : (K \ R).Nonempty := by
      simpa [R, Finset.sdiff_sdiff_eq_self hR₀K] using! hR₀
    have hcut' : Disjoint H (cutQuery K R) := by
      simpa only [R, cutQuery_compl hR₀K] using! hcut
    exact ⟨R, Finset.sdiff_subset, hcomp₀, hcomp, hsmall', hcut'⟩

def candidateCuts {n : ℕ} (G : Graph n) (h : ℕ) :
    Finset (Finset (Finset (Fin n))) :=
  ((largeFamily G h).powerset).filter fun R =>
    R.Nonempty ∧ ((largeFamily G h) \ R).Nonempty ∧
      2 * (vertices R).card ≤ (vertices (largeFamily G h)).card

lemma candidateCut_data {n h : ℕ} {G : Graph n}
    {R : Finset (Finset (Fin n))} (hR : R ∈ candidateCuts G h) :
    R ⊆ largeFamily G h ∧ R.Nonempty ∧
      ((largeFamily G h) \ R).Nonempty ∧
      2 * (vertices R).card ≤ (vertices (largeFamily G h)).card := by
  simpa [candidateCuts] using! hR

lemma candidateCut_query_lower {n h : ℕ} {G : Graph n}
    {R : Finset (Finset (Fin n))} (hR : R ∈ candidateCuts G h) :
    h * R.card * (vertices (largeFamily G h)).card ≤
      2 * (cutQuery (largeFamily G h) R).card := by
  obtain ⟨hRK, -, -, hhalf⟩ := candidateCut_data hR
  let K := largeFamily G h
  have hpart := vertices_partition_card (largeFamily_subset G h) hRK
  have hside : (vertices K).card ≤ 2 * (vertices (K \ R)).card := by
    dsimp [K] at hpart hhalf ⊢
    omega
  have hsmall := family_card_lower (G := G) hRK
  rw [cutQuery_card (largeFamily_subset G h) hRK]
  simpa only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using!
    (Nat.mul_le_mul hsmall hside)

lemma growProb_mono_on_completions {n t : ℕ} {G : Graph n}
    {A B : Graph n → Prop}
    (hAB : ∀ H, G ⊆ H → A H → B H) :
    growProb G t A ≤ growProb G t B := by
  unfold growProb
  apply div_le_div_of_nonneg_right
  · apply Nat.cast_le.mpr
    apply Finset.card_le_card
    intro H hH
    obtain ⟨hC, hA⟩ := Finset.mem_filter.mp hH
    exact Finset.mem_filter.mpr ⟨hC,
      hAB H (Finset.mem_filter.mp hC).2.1 hA⟩
  · positivity

theorem finite_sprinkling_bound (hF : FiniteEnumerationStatement)
    {n h t : ℕ} (G : Graph n)
    (hcap : G.card + t ≤ capacity n)
    (hex : (largeFamily G h).Nonempty) :
    growProb G t (fun H => ¬ oldLargeJoined G H h) ≤
      ∑ R ∈ candidateCuts G h,
        Real.exp (-(t : ℝ) * (cutQuery (largeFamily G h) R).card /
          (capacity n : ℝ)) := by
  let K := largeFamily G h
  let cuts := candidateCuts G h
  have hcover : growProb G t (fun H => ¬ oldLargeJoined G H h) ≤
      growProb G t (fun H => ∃ R ∈ cuts, Disjoint H (cutQuery K R)) := by
    apply growProb_mono_on_completions
    intro H hGH hfail
    obtain ⟨R, hRK, hRn, hKn, hhalf, hdis⟩ :=
      exists_separating_cut hGH hex hfail
    exact ⟨R, Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr hRK, ⟨hRn, hKn, hhalf⟩⟩, hdis⟩
  have hsum := growProb_finite_union_le (G := G) (t := t)
    cuts (fun R H => Disjoint H (cutQuery K R))
  have hterms :
      (∑ R ∈ cuts, growProb G t (fun H => Disjoint H (cutQuery K R))) ≤
        ∑ R ∈ cuts,
          Real.exp (-(t : ℝ) * (cutQuery K R).card /
            (capacity n : ℝ)) := by
    apply Finset.sum_le_sum
    intro R hR
    have hRK := (candidateCut_data hR).1
    exact (hF.2.2.2.1 n G (cutQuery K R) t hcap
      (cutQuery_disjoint_old G hRK)).2
  exact hcover.trans (hsum.trans hterms)

end
end Erdos745.WrapUp.Proofs.Internal.W10_GIANT_Sprinkling


namespace Erdos745.WrapUp.Proofs.Internal.W10_GIANT_SprinklingBounds

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1000000

open W10_GIANT_Sprinkling
open W10_GIANT_Bridges
open W09_TREE_MASS_Finite

/-! The component cuts from `W10_GIANT_Sprinkling` are grouped by the number
of old components on their smaller side. The resulting binomial bound keeps
the factor contributed by each selected component. -/

private lemma powerset_nonempty_sum {α : Type*} [DecidableEq α]
    (K : Finset α) (q : ℝ) :
    ∑ R ∈ K.powerset with R.Nonempty, q ^ R.card =
      (1 + q) ^ K.card - 1 := by
  classical
  have herase : K.powerset.filter Finset.Nonempty = K.powerset.erase ∅ := by
    ext R
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.nonempty_iff_ne_empty]
    tauto
  have hprod : (∑ R ∈ K.powerset, q ^ R.card) = (q + 1) ^ K.card := by
    calc
      (∑ R ∈ K.powerset, q ^ R.card) =
          ∑ R ∈ K.powerset, ∏ _x ∈ R, q := by simp
      _ = ∏ _x ∈ K, (q + 1) :=
        (Finset.prod_add_one (s := K) (f := fun _ : α => q)).symm
      _ = (q + 1) ^ K.card := by simp
  have hempty : (∅ : Finset α) ∈ K.powerset := by simp
  have hsplit := Finset.sum_erase_add K.powerset
    (fun R : Finset α => q ^ R.card) hempty
  rw [herase]
  simp only [Finset.card_empty, pow_zero] at hsplit
  rw [← hsplit] at hprod
  rw [add_comm q 1] at hprod
  linarith

private lemma cut_term_le_power {n h t : ℕ} (G : Graph n)
    (hcap : 0 < capacity n)
    {R : Finset (Finset (Fin n))} (hR : R ∈ candidateCuts G h) :
    Real.exp (-(t : ℝ) * (cutQuery (largeFamily G h) R).card /
        (capacity n : ℝ)) ≤
      (Real.exp (-(t : ℝ) * h *
          (vertices (largeFamily G h)).card /
          (2 * (capacity n : ℝ)))) ^ R.card := by
  have hcut : (h : ℝ) * R.card *
      (vertices (largeFamily G h)).card ≤
      2 * ((cutQuery (largeFamily G h) R).card : ℝ) := by
    exact_mod_cast candidateCut_query_lower hR
  have hside : ((h : ℝ) * R.card *
      (vertices (largeFamily G h)).card) / 2 ≤
      ((cutQuery (largeFamily G h) R).card : ℝ) := by
    linarith
  have hmult := mul_le_mul_of_nonneg_left hside
    (show 0 ≤ (t : ℝ) by positivity)
  have hnegative :
      -(t : ℝ) * ((cutQuery (largeFamily G h) R).card : ℝ) ≤
      -(t : ℝ) * (((h : ℝ) * R.card *
        (vertices (largeFamily G h)).card) / 2) := by
    nlinarith
  have hdiv := div_le_div_of_nonneg_right hnegative
    (show 0 ≤ (capacity n : ℝ) by positivity)
  have hexp :
      Real.exp (-(t : ℝ) * (cutQuery (largeFamily G h) R).card /
        (capacity n : ℝ)) ≤
      Real.exp ((R.card : ℝ) *
        (-(t : ℝ) * h * (vertices (largeFamily G h)).card /
          (2 * (capacity n : ℝ)))) := by
    rw [Real.exp_le_exp]
    convert hdiv using 1 <;> ring
  simpa only [Real.exp_nat_mul] using! hexp

theorem cut_sum_le_binomial {n h t : ℕ} (G : Graph n)
    (hcap : 0 < capacity n) :
    (∑ R ∈ candidateCuts G h,
      Real.exp (-(t : ℝ) * (cutQuery (largeFamily G h) R).card /
        (capacity n : ℝ))) ≤
      (1 + Real.exp (-(t : ℝ) * h *
        (vertices (largeFamily G h)).card /
        (2 * (capacity n : ℝ)))) ^ (largeFamily G h).card - 1 := by
  let K := largeFamily G h
  let q : ℝ := Real.exp (-(t : ℝ) * h * (vertices K).card /
    (2 * (capacity n : ℝ)))
  calc
    (∑ R ∈ candidateCuts G h,
        Real.exp (-(t : ℝ) * (cutQuery K R).card /
          (capacity n : ℝ))) ≤
      ∑ R ∈ candidateCuts G h, q ^ R.card := by
        apply Finset.sum_le_sum
        intro R hR
        exact cut_term_le_power G hcap hR
    _ ≤ ∑ R ∈ K.powerset with R.Nonempty, q ^ R.card := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro R hR
          exact Finset.mem_filter.mpr
            ⟨Finset.mem_powerset.mpr (candidateCut_data hR).1,
              (candidateCut_data hR).2.1⟩
        · intro R hR _
          positivity
    _ = (1 + q) ^ K.card - 1 := powerset_nonempty_sum K q

theorem finite_sprinkling_exp_bound (hF : FiniteEnumerationStatement)
    {n h t : ℕ} (G : Graph n)
    (hcap : G.card + t ≤ capacity n)
    (hcap0 : 0 < capacity n)
    (hex : (largeFamily G h).Nonempty) :
    growProb G t (fun H => ¬ oldLargeJoined G H h) ≤
      Real.exp ((largeFamily G h).card *
        Real.exp (-(t : ℝ) * h *
          (vertices (largeFamily G h)).card /
          (2 * (capacity n : ℝ)))) - 1 := by
  let q : ℝ := Real.exp (-(t : ℝ) * h *
    (vertices (largeFamily G h)).card / (2 * (capacity n : ℝ)))
  have hq : 0 ≤ q := Real.exp_nonneg _
  have hpow : (1 + q) ^ (largeFamily G h).card ≤
      Real.exp ((largeFamily G h).card * q) := by
    calc
      (1 + q) ^ (largeFamily G h).card ≤
          (Real.exp q) ^ (largeFamily G h).card := by
            apply pow_le_pow_left₀ (by positivity)
            simpa [add_comm] using! Real.add_one_le_exp q
      _ = Real.exp ((largeFamily G h).card * q) := by
        rw [Real.exp_nat_mul]
  calc
    growProb G t (fun H => ¬ oldLargeJoined G H h) ≤
      ∑ R ∈ candidateCuts G h,
        Real.exp (-(t : ℝ) * (cutQuery (largeFamily G h) R).card /
          (capacity n : ℝ)) := finite_sprinkling_bound hF G hcap hex
    _ ≤ (1 + q) ^ (largeFamily G h).card - 1 :=
      cut_sum_le_binomial G hcap0
    _ ≤ Real.exp ((largeFamily G h).card * q) - 1 := sub_le_sub_right hpow 1

lemma growProb_le_one {n t : ℕ} (G : Graph n) (A : Graph n → Prop) :
    growProb G t A ≤ 1 := by
  unfold growProb
  apply div_le_one_of_le₀
  · exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
  · positivity

lemma expectM_indicator_eq_probM {n M : ℕ} (A : Graph n → Prop) :
    expectM n M (fun G => if A G then (1 : ℝ) else 0) = probM n M A := by
  unfold expectM probM
  congr 1
  norm_cast
  simp

theorem averaged_conditional_failure_bound (hF : FiniteEnumerationStatement)
    {n M t : ℕ} (A : Graph n → Graph n → Prop)
    (Bad : Graph n → Prop) (b : ℝ)
    (hM : M ≤ capacity n)
    (hb : 0 ≤ b)
    (hgood : ∀ G, ¬ Bad G → growProb G t (A G) ≤ b) :
    expectM n M (fun G => growProb G t (A G)) ≤ probM n M Bad + b := by
  have hpoint : ∀ G, growProb G t (A G) ≤
      (if Bad G then (1 : ℝ) else 0) + b := by
    intro G
    by_cases hB : Bad G
    · simp only [if_pos hB]
      have hle := growProb_le_one (t := t) G (A G)
      linarith
    · simpa [hB] using! hgood G hB
  calc
    expectM n M (fun G => growProb G t (A G)) ≤
      expectM n M (fun G =>
        (if Bad G then (1 : ℝ) else 0) + b) := expectM_mono hpoint
    _ = probM n M Bad + b := by
      rw [expectM_add, expectM_indicator_eq_probM,
        expectM_const (hF.1 n M hM)]

end
end Erdos745.WrapUp.Proofs.Internal.W10_GIANT_SprinklingBounds
