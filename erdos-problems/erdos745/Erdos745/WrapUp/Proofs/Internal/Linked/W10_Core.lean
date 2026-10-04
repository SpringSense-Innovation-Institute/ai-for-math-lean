module

public import Erdos745.WrapUp.Proofs.Internal.Linked.W01_FiniteCore
public import Erdos745.WrapUp.Proofs.Internal.Linked.W08_Analytic
public import Erdos745.WrapUp.Proofs.Internal.Linked.W09_NearMean

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local simp] Pi.div_def Pi.mul_def Pi.add_def Pi.sub_def Pi.neg_def Pi.inv_def Function.comp_def Pi.pow_def Pi.smul_def Real.rpow_eq_pow

@[expose] public section


namespace Erdos745.WrapUp.Proofs.Internal.W10_GIANT_Components

noncomputable section
open scoped BigOperators Sym2
attribute [local instance] Classical.propDecidable

open W01_ENUM_Trees

/-! The deterministic component layer for W10.  The private observable below
counts only small unicyclic mass; unlike `unicyclicMass`, it is disjoint from
`largeMass`. -/

def smallUnicyclicMass {n : ℕ} (G : Graph n) (h : ℕ) : ℝ :=
  (components G).sum fun S =>
    if isUnicyclic G S ∧ S.card < h then (S.card : ℝ) else 0

lemma components_pairwiseDisjoint {n : ℕ} (G : Graph n) :
    ((components G : Finset (Finset (Fin n))) : Set (Finset (Fin n))).PairwiseDisjoint id := by
  intro S hS T hT hST
  have hSu : ∃ u : Fin n, componentOf G u = S := by
    simpa [components] using! hS
  have hTv : ∃ v : Fin n, componentOf G v = T := by
    simpa [components] using! hT
  obtain ⟨u, rfl⟩ := hSu
  obtain ⟨v, rfl⟩ := hTv
  apply Finset.disjoint_left.mpr
  intro x hxu hxv
  apply hST
  exact componentOf_eq_of_reach
    ((mem_componentOf_iff.mp hxu).trans
      (reach_symm (mem_componentOf_iff.mp hxv)))

lemma components_biUnion_eq_univ {n : ℕ} (G : Graph n) :
    (components G).biUnion id = (Finset.univ : Finset (Fin n)) := by
  ext x
  simp only [Finset.mem_biUnion, Finset.mem_univ, iff_true]
  exact ⟨componentOf G x, componentOf_mem_components G x, componentOf_self G x⟩

lemma sum_component_cards {n : ℕ} (G : Graph n) :
    ∑ S ∈ components G, S.card = n := by
  have h := congrArg Finset.card (components_biUnion_eq_univ G)
  rw [Finset.card_biUnion (components_pairwiseDisjoint G)] at h
  simpa using! h

lemma sum_component_cards_real {n : ℕ} (G : Graph n) :
    ∑ S ∈ components G, (S.card : ℝ) = n := by
  exact_mod_cast sum_component_cards G

private lemma component_support_eq {n : ℕ} {G : Graph n} (r x : Fin n) :
    x ∈ ((simpleGraph G).connectedComponentMk r).supp ↔
      x ∈ componentOf G r := by
  rw [SimpleGraph.ConnectedComponent.mem_supp_iff,
    SimpleGraph.ConnectedComponent.eq, simpleGraph_reachable_iff,
    mem_componentOf_iff]
  exact ⟨reach_symm, reach_symm⟩

private lemma component_vertex_card {n : ℕ} {G : Graph n} (r : Fin n) :
    Fintype.card ((simpleGraph G).connectedComponentMk r) =
      (componentOf G r).card := by
  let c := (simpleGraph G).connectedComponentMk r
  let e : c ≃ ↥(componentOf G r) :=
    { toFun := fun x =>
        ⟨x.1, (component_support_eq r x.1).mp x.2⟩
      invFun := fun x =>
        ⟨x.1, (component_support_eq r x.1).mpr x.2⟩
      left_inv := fun x => Subtype.ext rfl
      right_inv := fun x => Subtype.ext rfl }
  exact (Fintype.card_congr e).trans (Fintype.card_coe _)

private lemma component_edge_card {n : ℕ} {G : Graph n} (r : Fin n) :
    ((simpleGraph G).connectedComponentMk r).toSimpleGraph.edgeFinset.card =
      edgesInside G (componentOf G r) := by
  let c := (simpleGraph G).connectedComponentMk r
  let inside : Graph n :=
    G.filter fun e => e.1.1 ∈ componentOf G r ∧ e.1.2 ∈ componentOf G r
  have hc (x : Fin n) : x ∈ c.supp ↔ x ∈ componentOf G r :=
    component_support_eq r x
  have hcard : inside.card = c.toSimpleGraph.edgeFinset.card := by
    apply Finset.card_bij
      (fun e he =>
        s(⟨e.1.1, (hc e.1.1).mpr (Finset.mem_filter.mp he).2.1⟩,
          ⟨e.1.2, (hc e.1.2).mpr (Finset.mem_filter.mp he).2.2⟩))
    · intro e he
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
        SimpleGraph.ConnectedComponent.toSimpleGraph_adj, simpleGraph_adj]
      exact ⟨e, (Finset.mem_filter.mp he).1, Or.inl ⟨rfl, rfl⟩⟩
    · intro e₁ he₁ e₂ he₂ heq
      apply Subtype.ext
      apply Prod.ext
      · rcases Sym2.eq_iff.mp heq with heq | heq
        · exact congrArg Subtype.val heq.1
        · have hlt : e₂.1.2 < e₂.1.1 := by
            calc
              e₂.1.2 = e₁.1.1 := (congrArg Subtype.val heq.1).symm
              _ < e₁.1.2 := e₁.2
              _ = e₂.1.1 := congrArg Subtype.val heq.2
          exact (lt_asymm e₂.2 hlt).elim
      · rcases Sym2.eq_iff.mp heq with heq | heq
        · exact congrArg Subtype.val heq.2
        · have hlt : e₂.1.2 < e₂.1.1 := by
            calc
              e₂.1.2 = e₁.1.1 := (congrArg Subtype.val heq.1).symm
              _ < e₁.1.2 := e₁.2
              _ = e₂.1.1 := congrArg Subtype.val heq.2
          exact (lt_asymm e₂.2 hlt).elim
    · intro b hb
      induction b using Sym2.inductionOn with
      | _ u v =>
          have huv : adj G u.1 v.1 := by
            rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
              SimpleGraph.ConnectedComponent.toSimpleGraph_adj,
              simpleGraph_adj] at hb
            exact hb
          rcases huv with ⟨e, he, hends⟩
          have heInside : e ∈ inside := by
            apply Finset.mem_filter.mpr
            refine ⟨he, ?_⟩
            rcases hends with h | h
            · exact ⟨(hc e.1.1).mp (h.1.symm ▸ u.2),
                (hc e.1.2).mp (h.2.symm ▸ v.2)⟩
            · exact ⟨(hc e.1.1).mp (h.1.symm ▸ v.2),
                (hc e.1.2).mp (h.2.symm ▸ u.2)⟩
          refine ⟨e, heInside, ?_⟩
          rcases hends with h | h
          · exact Sym2.eq_iff.mpr
              (Or.inl ⟨Subtype.ext h.1, Subtype.ext h.2⟩)
          · exact Sym2.eq_iff.mpr
              (Or.inr ⟨Subtype.ext h.1, Subtype.ext h.2⟩)
  simpa [inside, edgesInside] using! hcard.symm

lemma component_edge_lower_bound {n : ℕ} {G : Graph n}
    {S : Finset (Fin n)} (hS : S ∈ components G) :
    S.card ≤ edgesInside G S + 1 := by
  simp only [components, Finset.mem_image] at hS
  obtain ⟨r, -, rfl⟩ := hS
  let c := (simpleGraph G).connectedComponentMk r
  have hconn := c.connected_toSubgraph
  have hbound := hconn.coe.card_vert_le_card_edgeSet_add_one
  have hv : Fintype.card c.toSubgraph.verts = (componentOf G r).card := by
    have hv := component_vertex_card (G := G) r
    change Fintype.card {x : Fin n // (simpleGraph G).connectedComponentMk x =
      (simpleGraph G).connectedComponentMk r} = _ at hv
    simpa [c, Fintype.card_subtype, SimpleGraph.ConnectedComponent.eq] using! hv
  have he : Nat.card c.toSubgraph.coe.edgeSet =
      edgesInside G (componentOf G r) := by
    rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card]
    let e : c.toSubgraph.coe ≃g c.toSimpleGraph :=
      { toFun := fun z => ⟨z.1, z.2⟩
        invFun := fun z => ⟨z.1, z.2⟩
        left_inv := fun z => Subtype.ext rfl
        right_inv := fun z => Subtype.ext rfl
        map_rel_iff' := by
          intro a b
          simp only [SimpleGraph.ConnectedComponent.coe_toSubgraph]
          rfl }
    calc
      c.toSubgraph.coe.edgeFinset.card = c.toSimpleGraph.edgeFinset.card :=
        e.card_edgeFinset_eq
      _ = edgesInside G (componentOf G r) := component_edge_card r
  rw [Nat.card_eq_fintype_card, hv, he] at hbound
  exact hbound

lemma component_tree_or_unicyclic {n : ℕ} {G : Graph n}
    {S : Finset (Fin n)} (hS : S ∈ components G)
    (hupper : edgesInside G S ≤ S.card) :
    isTree G S ∨ isUnicyclic G S := by
  have hlower := component_edge_lower_bound hS
  by_cases htree : edgesInside G S + 1 = S.card
  · exact Or.inl ⟨hS, htree⟩
  · right
    refine ⟨hS, ?_⟩
    omega

lemma smallUnicyclicMass_nonneg {n h : ℕ} (G : Graph n) :
    0 ≤ smallUnicyclicMass G h := by
  unfold smallUnicyclicMass
  exact Finset.sum_nonneg fun S _ => by split_ifs <;> positivity

lemma smallUnicyclicMass_le_unicyclicMass {n h : ℕ} (G : Graph n) :
    smallUnicyclicMass G h ≤ unicyclicMass G := by
  unfold smallUnicyclicMass unicyclicMass
  apply Finset.sum_le_sum
  intro S hS
  by_cases hsmall : isUnicyclic G S ∧ S.card < h
  · simp [hsmall]
  · by_cases hU : isUnicyclic G S
    · have hnsmall : ¬ S.card < h := fun hs => hsmall ⟨hU, hs⟩
      simp [hU, hnsmall]
    · simp [hU]

lemma no_small_complex_of_count_eq_zero {n h : ℕ} {G : Graph n}
    (hzero : smallComplexCount G h = 0) {S : Finset (Fin n)}
    (hS : S ∈ components G) (hsmall : S.card < h) :
    edgesInside G S ≤ S.card := by
  by_contra hnot
  have hlt : S.card < edgesInside G S := Nat.lt_of_not_ge hnot
  have hmem : S ∈ (components G).filter
      (fun T => T.card < h ∧ T.card < edgesInside G T) :=
    Finset.mem_filter.mpr ⟨hS, hsmall, hlt⟩
  have hpos : 0 < ((components G).filter
      (fun T => T.card < h ∧ T.card < edgesInside G T)).card :=
    Finset.card_pos.mpr ⟨S, hmem⟩
  unfold smallComplexCount at hzero
  omega

lemma small_mass_decomposition {n h : ℕ} {G : Graph n}
    (hzero : smallComplexCount G h = 0) :
    (n : ℝ) = largeMass G h + treeMassBelow G h +
      smallUnicyclicMass G h := by
  have hpoint (S : Finset (Fin n)) (hS : S ∈ components G) :
      (S.card : ℝ) =
        (if h ≤ S.card then (S.card : ℝ) else 0) +
        (if isTree G S ∧ S.card < h then (S.card : ℝ) else 0) +
        (if isUnicyclic G S ∧ S.card < h then (S.card : ℝ) else 0) := by
    by_cases hlarge : h ≤ S.card
    · have hnsmall : ¬ S.card < h := Nat.not_lt_of_ge hlarge
      simp [hlarge, hnsmall]
    · have hsmall : S.card < h := Nat.lt_of_not_ge hlarge
      have hupper := no_small_complex_of_count_eq_zero hzero hS hsmall
      rcases component_tree_or_unicyclic hS hupper with hT | hU
      · have hnU : ¬ isUnicyclic G S := by
          intro hU
          have := hT.2
          have := hU.2
          omega
        simp [hlarge, hsmall, hT, hnU]
      · have hnT : ¬ isTree G S := by
          intro hT
          have := hT.2
          have := hU.2
          omega
        simp [hlarge, hsmall, hU, hnT]
  rw [← sum_component_cards_real G]
  unfold largeMass treeMassBelow smallUnicyclicMass
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro S hS
  exact hpoint S hS

end
end Erdos745.WrapUp.Proofs.Internal.W10_GIANT_Components


namespace Erdos745.WrapUp.Proofs.Internal.W10_GIANT_Bridges

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

open W01_ENUM_Trees
open W10_GIANT_Components

def largeVertices {n : ℕ} (G : Graph n) (h : ℕ) : Finset (Fin n) :=
  (components G).biUnion fun S => if h ≤ S.card then S else ∅

lemma mem_largeVertices_iff {n h : ℕ} {G : Graph n} {x : Fin n} :
    x ∈ largeVertices G h ↔
      ∃ S ∈ components G, h ≤ S.card ∧ x ∈ S := by
  simp only [largeVertices, Finset.mem_biUnion]
  constructor
  · rintro ⟨S, hS, hx⟩
    by_cases hSl : h ≤ S.card
    · exact ⟨S, hS, hSl, by simpa [hSl] using! hx⟩
    · simp [hSl] at hx
  · rintro ⟨S, hS, hSl, hx⟩
    exact ⟨S, hS, by simpa [hSl] using! hx⟩

lemma largeVertices_card {n h : ℕ} (G : Graph n) :
    (largeVertices G h).card =
      ∑ S ∈ components G, if h ≤ S.card then S.card else 0 := by
  unfold largeVertices
  rw [Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro S hS
    split_ifs <;> simp_all
  · intro S hS T hT hST
    change Disjoint (if h ≤ S.card then S else ∅)
      (if h ≤ T.card then T else ∅)
    by_cases hSl : h ≤ S.card <;> by_cases hTl : h ≤ T.card
    · simpa [hSl, hTl] using!
        (components_pairwiseDisjoint G hS hT hST)
    · simp [hSl, hTl]
    · simp [hSl, hTl]
    · simp [hSl, hTl]

lemma largeMass_eq_card_largeVertices {n h : ℕ} (G : Graph n) :
    largeMass G h = ((largeVertices G h).card : ℝ) := by
  unfold largeMass
  rw [largeVertices_card]
  norm_cast

lemma adj_mono {n : ℕ} {G H : Graph n} (hGH : G ⊆ H)
    {u v : Fin n} (huv : adj G u v) : adj H u v := by
  rcases huv with ⟨e, he, hends⟩
  exact ⟨e, hGH he, hends⟩

lemma reach_mono {n : ℕ} {G H : Graph n} (hGH : G ⊆ H)
    {u v : Fin n} (huv : reach G u v) : reach H u v := by
  induction huv with
  | refl => exact Relation.ReflTransGen.refl
  | tail h hadj ih => exact ih.tail (adj_mono hGH hadj)

lemma componentOf_subset {n : ℕ} {G H : Graph n} (hGH : G ⊆ H)
    (u : Fin n) : componentOf G u ⊆ componentOf H u := by
  intro x hx
  exact mem_componentOf_iff.mpr (reach_mono hGH (mem_componentOf_iff.mp hx))

lemma componentOf_eq_of_mem {n : ℕ} {G : Graph n}
    {S : Finset (Fin n)} (hS : S ∈ components G) {x : Fin n} (hx : x ∈ S) :
    componentOf G x = S := by
  simp only [components, Finset.mem_image] at hS
  obtain ⟨u, -, rfl⟩ := hS
  exact (componentOf_eq_of_reach (mem_componentOf_iff.mp hx)).symm

lemma component_coarsens {n : ℕ} {G H : Graph n} (hGH : G ⊆ H)
    {S : Finset (Fin n)} (hS : S ∈ components G) :
    ∃ T ∈ components H, S ⊆ T := by
  simp only [components, Finset.mem_image] at hS
  obtain ⟨u, -, rfl⟩ := hS
  exact ⟨componentOf H u, componentOf_mem_components H u,
    componentOf_subset hGH u⟩

lemma largeVertices_mono {n h : ℕ} {G H : Graph n} (hGH : G ⊆ H) :
    largeVertices G h ⊆ largeVertices H h := by
  intro x hx
  rcases mem_largeVertices_iff.mp hx with ⟨S, hS, hSl, hxS⟩
  rcases component_coarsens hGH hS with ⟨T, hT, hST⟩
  apply mem_largeVertices_iff.mpr
  exact ⟨T, hT, hSl.trans (Finset.card_le_card hST), hST hxS⟩

lemma component_card_le_univ {n : ℕ} {G : Graph n}
    {S : Finset (Fin n)} (_hS : S ∈ components G) : S.card ≤ n := by
  exact (Finset.card_le_univ S).trans_eq (Fintype.card_fin n)

lemma final_large_contains_old_large {n h : ℕ} {G H : Graph n}
    (hGH : G ⊆ H)
    (hdiff : largeMass H h - largeMass G h < h)
    {T : Finset (Fin n)} (hT : T ∈ components H) (hTl : h ≤ T.card) :
    ∃ S ∈ components G, h ≤ S.card ∧ S ⊆ T := by
  by_contra hnone
  push_neg at hnone
  have hTsub : T ⊆ largeVertices H h \ largeVertices G h := by
    intro x hxT
    have hxH : x ∈ largeVertices H h :=
      mem_largeVertices_iff.mpr ⟨T, hT, hTl, hxT⟩
    refine Finset.mem_sdiff.mpr ⟨hxH, ?_⟩
    intro hxG
    rcases mem_largeVertices_iff.mp hxG with ⟨S, hS, hSl, hxS⟩
    have hSx : componentOf G x = S := componentOf_eq_of_mem hS hxS
    have hTx : componentOf H x = T := componentOf_eq_of_mem hT hxT
    have hST : S ⊆ T := by
      rw [← hSx, ← hTx]
      exact componentOf_subset hGH x
    exact hnone S hS hSl hST
  have hmono := largeVertices_mono (h := h) hGH
  have hcarddiff :
      (largeVertices H h \ largeVertices G h).card =
        (largeVertices H h).card - (largeVertices G h).card := by
    exact Finset.card_sdiff_of_subset hmono
  have hcard : T.card ≤
      (largeVertices H h).card - (largeVertices G h).card := by
    rw [← hcarddiff]
    exact Finset.card_le_card hTsub
  rw [largeMass_eq_card_largeVertices, largeMass_eq_card_largeVertices] at hdiff
  have hcast : ((T.card : ℕ) : ℝ) ≤
      ((largeVertices H h).card : ℝ) - ((largeVertices G h).card : ℝ) := by
    rw [← Nat.cast_sub (Finset.card_le_card hmono)]
    exact_mod_cast hcard
  exact (not_lt_of_ge ((show (h : ℝ) ≤ (T.card : ℝ) by exact_mod_cast hTl).trans hcast)) hdiff

def oldLargeJoined {n : ℕ} (G H : Graph n) (h : ℕ) : Prop :=
  ∃ T ∈ components H,
    ∀ S ∈ components G, h ≤ S.card → S ⊆ T

lemma unique_large_of_joined {n h : ℕ} {G H : Graph n}
    (hGH : G ⊆ H) (hh : 0 < h)
    (hex : ∃ S ∈ components G, h ≤ S.card)
    (hjoin : oldLargeJoined G H h)
    (hdiff : largeMass H h - largeMass G h < h) :
    countGE H h = 1 := by
  rcases hex with ⟨S₀, hS₀, hS₀l⟩
  rcases hjoin with ⟨T, hT, hjoined⟩
  have hS₀T := hjoined S₀ hS₀ hS₀l
  have hTlarge : h ≤ T.card := hS₀l.trans (Finset.card_le_card hS₀T)
  have hunique : ∀ U ∈ components H, h ≤ U.card → U = T := by
    intro U hU hUl
    rcases final_large_contains_old_large hGH hdiff hU hUl with
      ⟨S, hS, hSl, hSU⟩
    have hST := hjoined S hS hSl
    have hSnonempty : S.Nonempty := by
      have : 0 < S.card := hh.trans_le hSl
      exact Finset.card_pos.mp this
    rcases hSnonempty with ⟨x, hxS⟩
    exact (componentOf_eq_of_mem hU (hSU hxS)).symm.trans
      (componentOf_eq_of_mem hT (hST hxS))
  unfold countGE
  rw [Finset.card_eq_one]
  refine ⟨T, Finset.ext ?_⟩
  intro U
  simp only [Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro ⟨hU, hUl⟩
    exact hunique U hU hUl
  · rintro rfl
    exact ⟨hT, hTlarge⟩

lemma unique_large_witness {n h : ℕ} {G : Graph n}
    (hcount : countGE G h = 1) :
    ∃ S ∈ components G, h ≤ S.card ∧
      (∀ T ∈ components G, h ≤ T.card → T = S) := by
  unfold countGE at hcount
  rw [Finset.card_eq_one] at hcount
  rcases hcount with ⟨S, hfilter⟩
  have hSmem : S ∈ (components G).filter (fun T => h ≤ T.card) := by
    rw [hfilter]
    simp
  have hS := Finset.mem_filter.mp hSmem
  refine ⟨S, hS.1, hS.2, ?_⟩
  intro T hT hTl
  have : T ∈ (components G).filter (fun U => h ≤ U.card) :=
    Finset.mem_filter.mpr ⟨hT, hTl⟩
  rw [hfilter] at this
  simpa using! this

lemma largeMass_eq_unique_card {n h : ℕ} {G : Graph n}
    {S : Finset (Fin n)} (hS : S ∈ components G) (hSl : h ≤ S.card)
    (hunique : ∀ T ∈ components G, h ≤ T.card → T = S) :
    largeMass G h = S.card := by
  unfold largeMass
  rw [Finset.sum_eq_single S]
  · simp [hSl]
  · intro T hT hTS
    have hn : ¬ h ≤ T.card := fun hTl => hTS (hunique T hT hTl)
    simp [hn]
  · intro hnot
    exact (hnot hS).elim

lemma rankSize_one_eq_unique_card {n h : ℕ} {G : Graph n}
    {S : Finset (Fin n)} (hS : S ∈ components G) (hSl : h ≤ S.card)
    (hunique : ∀ T ∈ components G, h ≤ T.card → T = S) :
    rankSize G 1 = S.card := by
  unfold rankSize
  simp only [one_ne_zero, if_false]
  apply le_antisymm
  · apply Finset.sup_le
    intro k hk
    by_cases hcount : 1 ≤ countGE G k
    · simp only [hcount, if_true]
      unfold countGE at hcount
      have hnonempty :
          ((components G).filter (fun T => k ≤ T.card)).Nonempty :=
        Finset.card_pos.mp (lt_of_lt_of_le Nat.zero_lt_one hcount)
      rcases hnonempty with ⟨T, hT⟩
      have hTf := Finset.mem_filter.mp hT
      by_cases hkh : h ≤ k
      · have hTS := hunique T hTf.1 (hkh.trans hTf.2)
        simpa [hTS] using! hTf.2
      · exact (Nat.lt_of_not_ge hkh).le.trans hSl
    · simp [hcount]
  · have hSn : S.card ∈ Finset.range (n + 1) := by
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le (component_card_le_univ hS))
    have hcount : 1 ≤ countGE G S.card := by
      unfold countGE
      apply Finset.one_le_card.mpr
      exact ⟨S, Finset.mem_filter.mpr ⟨hS, le_rfl⟩⟩
    have hle := Finset.le_sup (f := fun k => if 1 ≤ countGE G k then k else 0) hSn
    simpa [hcount] using! hle

lemma rank_one_eq_largeMass_of_unique {n h : ℕ} {G : Graph n}
    (hcount : countGE G h = 1) :
    (rankSize G 1 : ℝ) = largeMass G h := by
  rcases unique_large_witness hcount with ⟨S, hS, hSl, hu⟩
  rw [rankSize_one_eq_unique_card hS hSl hu,
    largeMass_eq_unique_card hS hSl hu]

end
end Erdos745.WrapUp.Proofs.Internal.W10_GIANT_Bridges


namespace Erdos745.WrapUp.Proofs.Internal.W10_GIANT_Concentration

noncomputable section
open Filter
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

open W10_GIANT_Components
open W08_CYCLIC_Finite

lemma expectM_div_const {n M : ℕ} (f : Graph n → ℝ) (a : ℝ) :
    expectM n M (fun G => f G / a) = expectM n M f / a := by
  simp only [expectM, div_eq_mul_inv]
  rw [← Finset.sum_mul]
  ring

lemma expectM_smallUnicyclicMass_le {n M h : ℕ} :
    expectM n M (fun G => smallUnicyclicMass G h) ≤
      expectM n M unicyclicMass := by
  exact W09_TREE_MASS_Finite.expectM_mono fun G =>
    smallUnicyclicMass_le_unicyclicMass G

lemma centered_largeMass_identity_seq {n : ℕ} {M : NatSeq} {G : Graph n}
    (hzero : smallComplexCount G (largeCutoff n) = 0) :
    largeMass G (largeCutoff n) - giantCenter M n =
      -(treeMassBelow G (largeCutoff n) -
          expectM n (M n) (fun H => treeMassBelow H (largeCutoff n))) -
        treeMeanError M n - smallUnicyclicMass G (largeCutoff n) := by
  have hmass := small_mass_decomposition hzero
  unfold giantCenter giantFraction treeMeanError
  linear_combination -hmass

lemma largeMass_bad_bound (hF : FiniteEnumerationStatement)
    {n : ℕ} {M : NatSeq} (hM : M n ≤ capacity n) (a : ℝ) (ha : 0 < a)
    (hmean : |treeMeanError M n| ≤ a) :
    probM n (M n) (fun G =>
        |largeMass G (largeCutoff n) - giantCenter M n| > 3 * a) ≤
      expectM n (M n) (fun G =>
        (smallComplexCount G (largeCutoff n) : ℝ)) +
      varianceM n (M n) (fun G => treeMassBelow G (largeCutoff n)) / a ^ 2 +
      expectM n (M n) unicyclicMass / a := by
  let Y : Graph n → ℝ := fun G => treeMassBelow G (largeCutoff n)
  let U : Graph n → ℝ := fun G => smallUnicyclicMass G (largeCutoff n)
  let Q : Graph n → ℝ := fun G =>
    (smallComplexCount G (largeCutoff n) : ℝ) +
      (Y G - expectM n (M n) Y) ^ 2 / a ^ 2 + U G / a
  have hQnonneg : ∀ G, 0 ≤ Q G := by
    intro G
    dsimp [Q]
    have hU : 0 ≤ U G := by
      dsimp [U]
      exact smallUnicyclicMass_nonneg G
    have ha0 : 0 ≤ a := ha.le
    positivity
  have hdom : ∀ G, |largeMass G (largeCutoff n) - giantCenter M n| > 3 * a →
      1 ≤ Q G := by
    intro G hbad
    by_cases hc : smallComplexCount G (largeCutoff n) = 0
    · have hid := centered_largeMass_identity_seq (M := M) (G := G) hc
      by_cases htree : a < |Y G - expectM n (M n) Y|
      · have hsquare : a ^ 2 ≤ (Y G - expectM n (M n) Y) ^ 2 := by
          have hmul := mul_self_le_mul_self ha.le htree.le
          simpa [pow_two, sq_abs] using! hmul
        have hone : 1 ≤ (Y G - expectM n (M n) Y) ^ 2 / a ^ 2 := by
          rw [le_div_iff₀ (sq_pos_of_pos ha)]
          simpa using! hsquare
        dsimp [Q]
        have hU0 : 0 ≤ U G := by
          dsimp [U]
          exact smallUnicyclicMass_nonneg G
        have hU : 0 ≤ U G / a := div_nonneg hU0 ha.le
        have hc0 : (smallComplexCount G (largeCutoff n) : ℝ) = 0 := by
          exact_mod_cast hc
        rw [hc0, zero_add]
        linarith
      · have htree' : |Y G - expectM n (M n) Y| ≤ a := le_of_not_gt htree
        by_cases huni : a < U G
        · have hone : 1 ≤ U G / a := by
            rw [le_div_iff₀ ha]
            simpa using! huni.le
          dsimp [Q]
          have hsquare : 0 ≤ (Y G - expectM n (M n) Y) ^ 2 / a ^ 2 := by
            positivity
          have hc0 : (smallComplexCount G (largeCutoff n) : ℝ) = 0 := by
            exact_mod_cast hc
          rw [hc0, zero_add]
          linarith
        · have huni' : U G ≤ a := le_of_not_gt huni
          have hU0 : 0 ≤ U G := by
            dsimp [U]
            exact smallUnicyclicMass_nonneg G
          have hcalc :
              |-(Y G - expectM n (M n) Y) - treeMeanError M n - U G| ≤
                3 * a := by
            calc
              |-(Y G - expectM n (M n) Y) - treeMeanError M n - U G| ≤
                  |Y G - expectM n (M n) Y| + |treeMeanError M n| + |U G| := by
                    calc
                      |-(Y G - expectM n (M n) Y) - treeMeanError M n - U G| ≤
                          |-(Y G - expectM n (M n) Y) - treeMeanError M n| + |U G| :=
                        abs_sub _ _
                      _ ≤ (|Y G - expectM n (M n) Y| + |treeMeanError M n|) +
                          |U G| := by
                        gcongr
                        calc
                          |-(Y G - expectM n (M n) Y) - treeMeanError M n| ≤
                              |-(Y G - expectM n (M n) Y)| +
                                |treeMeanError M n| := abs_sub _ _
                          _ = |Y G - expectM n (M n) Y| +
                                |treeMeanError M n| := by rw [abs_neg]
              _ ≤ 3 * a := by
                rw [abs_of_nonneg hU0]
                linarith
          rw [hid] at hbad
          exact False.elim ((not_lt_of_ge hcalc) hbad)
    · have hcpos : 1 ≤ smallComplexCount G (largeCutoff n) :=
        Nat.one_le_iff_ne_zero.mpr hc
      dsimp [Q]
      have hsquare : 0 ≤ (Y G - expectM n (M n) Y) ^ 2 / a ^ 2 := by positivity
      have hU0 : 0 ≤ U G := by
        dsimp [U]
        exact smallUnicyclicMass_nonneg G
      have hU : 0 ≤ U G / a := div_nonneg hU0 ha.le
      have hcposR : (1 : ℝ) ≤ (smallComplexCount G (largeCutoff n) : ℝ) := by
        exact_mod_cast hcpos
      linarith
  calc
    probM n (M n) (fun G =>
        |largeMass G (largeCutoff n) - giantCenter M n| > 3 * a) ≤
        expectM n (M n) Q :=
      probM_le_expectM_of_indicator hF hM _ Q hQnonneg hdom
    _ = expectM n (M n) (fun G =>
          (smallComplexCount G (largeCutoff n) : ℝ)) +
        varianceM n (M n) Y / a ^ 2 + expectM n (M n) U / a := by
      dsimp [Q]
      rw [W09_TREE_MASS_Finite.expectM_add,
        W09_TREE_MASS_Finite.expectM_add,
        expectM_div_const, expectM_div_const]
      rfl
    _ ≤ expectM n (M n) (fun G =>
          (smallComplexCount G (largeCutoff n) : ℝ)) +
        varianceM n (M n) (fun G => treeMassBelow G (largeCutoff n)) / a ^ 2 +
        expectM n (M n) unicyclicMass / a := by
      dsimp [Y, U]
      gcongr
      exact expectM_smallUnicyclicMass_le

lemma inv_sq_le_near_scale {n : ℕ} {e : ℝ} (he : 0 < e)
    (hw : 1 ≤ (n : ℝ) * e ^ 3) :
    e⁻¹ ^ 2 ≤ Real.sqrt ((n : ℝ) / e) := by
  apply Real.le_sqrt_of_sq_le
  have hm := mul_le_mul_of_nonneg_right hw (show 0 ≤ e⁻¹ ^ 4 by positivity)
  calc
    (e⁻¹ ^ 2) ^ 2 = 1 * e⁻¹ ^ 4 := by ring
    _ ≤ ((n : ℝ) * e ^ 3) * e⁻¹ ^ 4 := hm
    _ = (n : ℝ) / e := by field_simp [ne_of_gt he]

lemma tight_largeMass_of_bounds (hF : FiniteEnumerationStatement)
    {M : NatSeq} {s : RealSeq} (hM : admissible M)
    (hspos : ∀ᶠ n in atTop, 0 < s n)
    (hcomplex : ∀ d : ℝ, 0 < d →
      ∀ᶠ n in atTop,
        expectM n (M n) (fun G =>
          (smallComplexCount G (largeCutoff n) : ℝ)) ≤ d)
    (huni : ∃ CU : ℝ, 0 < CU ∧
      ∀ᶠ n in atTop, expectM n (M n) unicyclicMass ≤ CU * s n)
    (hvar : ∃ CV : ℝ, 0 < CV ∧
      ∀ᶠ n in atTop,
        varianceM n (M n) (fun G => treeMassBelow G (largeCutoff n)) ≤
          CV * s n ^ 2)
    (hmean : ∃ CE : ℝ, 0 < CE ∧
      ∀ᶠ n in atTop, |treeMeanError M n| ≤ CE * s n) :
    tightScaled M (fun n G => largeMass G (largeCutoff n)) (giantCenter M) s := by
  obtain ⟨CU, hCU, huni⟩ := huni
  obtain ⟨CV, hCV, hvar⟩ := hvar
  obtain ⟨CE, hCE, hmean⟩ := hmean
  intro d hd
  let K : ℝ := 1 + 3 * CE + 9 * CU / d + Real.sqrt (27 * CV / d)
  have hK : 0 < K := by
    dsimp [K]
    positivity
  refine ⟨K, hK, ?_⟩
  have hKb : 3 * CE ≤ K := by
    dsimp [K]
    have hu0 : 0 ≤ 9 * CU / d := (div_pos (by positivity) hd).le
    have hs0 : 0 ≤ Real.sqrt (27 * CV / d) := Real.sqrt_nonneg _
    linarith
  have hKu : 3 * CU / K ≤ d / 3 := by
    rw [div_le_iff₀ hK]
    have hkbase : 9 * CU / d ≤ K := by
      dsimp [K]
      have hs0 : 0 ≤ Real.sqrt (27 * CV / d) := Real.sqrt_nonneg _
      linarith [hCE]
    have := mul_le_mul_of_nonneg_left hkbase hd.le
    field_simp [ne_of_gt hd] at this ⊢
    nlinarith
  have hKv : 9 * CV / K ^ 2 ≤ d / 3 := by
    have hsarg : 0 ≤ 27 * CV / d := by positivity
    have hsqrt : Real.sqrt (27 * CV / d) ^ 2 = 27 * CV / d :=
      Real.sq_sqrt hsarg
    have hkroot : Real.sqrt (27 * CV / d) ≤ K := by
      dsimp [K]
      have hu0 : 0 ≤ 9 * CU / d := (div_pos (by positivity) hd).le
      linarith [hCE]
    have hkroot0 : 0 ≤ Real.sqrt (27 * CV / d) := Real.sqrt_nonneg _
    have hk2 : 27 * CV / d ≤ K ^ 2 := by nlinarith
    have hK2 : 0 < K ^ 2 := sq_pos_of_pos hK
    rw [div_le_iff₀ hK2]
    have := mul_le_mul_of_nonneg_left hk2 hd.le
    field_simp [ne_of_gt hd] at this ⊢
    nlinarith
  filter_upwards [hM, hspos, hcomplex (d / 3) (by positivity), huni, hvar,
    hmean] with n hnM hs hc hu hv hm
  let a := K * s n / 3
  have ha : 0 < a := by dsimp [a]; positivity
  have hmeana : |treeMeanError M n| ≤ a := by
    calc
      |treeMeanError M n| ≤ CE * s n := hm
      _ ≤ K * s n / 3 := by
        have := mul_le_mul_of_nonneg_right hKb hs.le
        linarith
  have hbound := largeMass_bad_bound hF hnM a ha hmeana
  have hthreshold : 3 * a = K * s n := by dsimp [a]; ring
  rw [hthreshold] at hbound
  calc
    probM n (M n) (fun G =>
        |largeMass G (largeCutoff n) - giantCenter M n| > K * s n) ≤
        expectM n (M n) (fun G =>
          (smallComplexCount G (largeCutoff n) : ℝ)) +
        varianceM n (M n) (fun G => treeMassBelow G (largeCutoff n)) / a ^ 2 +
        expectM n (M n) unicyclicMass / a := hbound
    _ ≤ d / 3 + 9 * CV / K ^ 2 + 3 * CU / K := by
      have ha2 : a ^ 2 = K ^ 2 * s n ^ 2 / 9 := by dsimp [a]; ring
      have hs2 : 0 < s n ^ 2 := sq_pos_of_pos hs
      rw [ha2]
      apply add_le_add
      · apply add_le_add hc
        calc
          varianceM n (M n) (fun G => treeMassBelow G (largeCutoff n)) /
              (K ^ 2 * s n ^ 2 / 9) ≤
              (CV * s n ^ 2) / (K ^ 2 * s n ^ 2 / 9) := by
                gcongr
          _ = 9 * CV / K ^ 2 := by field_simp [ne_of_gt hK, ne_of_gt hs]
      · calc
          expectM n (M n) unicyclicMass / a ≤ CU * s n / a := by gcongr
          _ = 3 * CU / K := by dsimp [a]; field_simp [ne_of_gt hK, ne_of_gt hs]
    _ ≤ d := by linarith

lemma near_complex_vanishes (hCyc : CyclicStructureStatement)
    {M : NatSeq} (hbare : bareSuper M) :
    ∀ d : ℝ, 0 < d →
      ∀ᶠ n in atTop,
        expectM n (M n) (fun G =>
          (smallComplexCount G (largeCutoff n) : ℝ)) ≤ d := by
  rcases (hCyc.1 M (Or.inr hbare)).2.1 with ⟨C, hC, hbound⟩
  intro d hd
  have hlarge := hbare.2.2.2.eventually (eventually_ge_atTop (C / d))
  filter_upwards [hbound, hlarge] with n hb hw
  have hnonneg := W08_CYCLIC_Finite.expect_smallComplexCount_nonneg
    n (M n) (largeCutoff n)
  have hwd : 0 < widthParameter M n := lt_of_lt_of_le (div_pos hC hd) hw
  calc
    expectM n (M n) (fun G =>
        (smallComplexCount G (largeCutoff n) : ℝ)) ≤
        C * (widthParameter M n)⁻¹ := (le_abs_self _).trans hb
    _ ≤ d := by
      rw [mul_inv_le_iff₀ hwd]
      simpa [mul_comm] using! (div_le_iff₀ hd).mp hw

lemma near_scale_bounds (hCyc : CyclicStructureStatement)
    (hTree : TreeMassStatement) {M : NatSeq} (hbare : bareSuper M) :
    (∀ᶠ n : ℕ in atTop, 0 < Real.sqrt ((n : ℝ) / epsilon M n)) ∧
    (∃ CU : ℝ, 0 < CU ∧ ∀ᶠ n in atTop,
      expectM n (M n) unicyclicMass ≤
        CU * Real.sqrt ((n : ℝ) / epsilon M n)) ∧
    (∃ CV : ℝ, 0 < CV ∧ ∀ᶠ n in atTop,
      varianceM n (M n) (fun G => treeMassBelow G (largeCutoff n)) ≤
        CV * Real.sqrt ((n : ℝ) / epsilon M n) ^ 2) ∧
    (∃ CE : ℝ, 0 < CE ∧ ∀ᶠ n in atTop,
      |treeMeanError M n| ≤
        CE * Real.sqrt ((n : ℝ) / epsilon M n)) := by
  rcases (hCyc.1 M (Or.inr hbare)).1 with ⟨CU, hCU, hu⟩
  rcases (hTree.1 M hbare).1 with ⟨CE, hCE, he⟩
  rcases (hTree.1 M hbare).2 with ⟨CV, hCV, hv⟩
  have hwidth := hbare.2.2.2.eventually (eventually_ge_atTop (1 : ℝ))
  have hdeg := hbare.2.1
  have hn : ∀ᶠ n : ℕ in atTop, 0 < n := eventually_gt_atTop 0
  have hall : ∀ᶠ n in atTop,
      0 < epsilon M n ∧
      (epsilon M n)⁻¹ ^ 2 ≤ Real.sqrt ((n : ℝ) / epsilon M n) ∧
      0 < Real.sqrt ((n : ℝ) / epsilon M n) := by
    filter_upwards [hwidth, hdeg, hn] with n hw hd hn
    have heps : 0 < epsilon M n := by
      rw [epsilon, abs_of_pos (sub_pos.mpr hd)]
      linarith
    have hscale := inv_sq_le_near_scale heps hw
    have hspos : 0 < Real.sqrt ((n : ℝ) / epsilon M n) := by
      exact Real.sqrt_pos.2 (div_pos (by positivity) heps)
    exact ⟨heps, hscale, hspos⟩
  refine ⟨hall.mono fun n h => h.2.2, ⟨CU, hCU, ?_⟩,
    ⟨CV, hCV, ?_⟩, ⟨CE, hCE, ?_⟩⟩
  · filter_upwards [hu, hall] with n hu hs
    exact (le_abs_self _).trans (hu.trans (mul_le_mul_of_nonneg_left hs.2.1 hCU.le))
  · filter_upwards [hv, hall] with n hv hs
    have hnonneg : 0 ≤ (n : ℝ) / epsilon M n :=
      div_nonneg (by positivity) hs.1.le
    have hsq : Real.sqrt ((n : ℝ) / epsilon M n) ^ 2 =
        (n : ℝ) / epsilon M n := Real.sq_sqrt hnonneg
    calc
      varianceM n (M n) (fun G => treeMassBelow G (largeCutoff n)) ≤
          CV * ((n : ℝ) / epsilon M n) := (le_abs_self _).trans hv
      _ = CV * Real.sqrt ((n : ℝ) / epsilon M n) ^ 2 := by rw [hsq]
  · filter_upwards [he, hall] with n he hs
    exact he.trans (mul_le_mul_of_nonneg_left hs.2.1 hCE.le)

theorem near_largeMass_tight (hF : FiniteEnumerationStatement)
    (hCyc : CyclicStructureStatement) (hTree : TreeMassStatement)
    (M : NatSeq) (hbare : bareSuper M) :
    tightScaled M (fun n G => largeMass G (largeCutoff n)) (giantCenter M)
      (fun n => Real.sqrt ((n : ℝ) / epsilon M n)) := by
  rcases near_scale_bounds hCyc hTree hbare with ⟨hs, hu, hv, he⟩
  exact tight_largeMass_of_bounds hF hbare.1 hs
    (near_complex_vanishes hCyc hbare) hu hv he

lemma fixed_complex_vanishes (hCyc : CyclicStructureStatement)
    {M : NatSeq} {lam : ℝ} (hM : admissible M) (hlam : 1 < lam)
    (hdeg : Tendsto (degree M) atTop (𝓝 lam)) :
    ∀ d : ℝ, 0 < d →
      ∀ᶠ n in atTop,
        expectM n (M n) (fun G =>
          (smallComplexCount G (largeCutoff n) : ℝ)) ≤ d := by
  have hne : lam ≠ 1 := ne_of_gt hlam
  rcases (hCyc.2 M lam hM (by linarith) hne hdeg).2.2.1 with ⟨C, hC, hb⟩
  intro d hd
  have hnlarge := tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop (C / d))
  filter_upwards [hb, hnlarge] with n hb hn
  have hnpos : 0 < (n : ℝ) := lt_of_lt_of_le (div_pos hC hd) hn
  calc
    expectM n (M n) (fun G =>
        (smallComplexCount G (largeCutoff n) : ℝ)) ≤ C * (n : ℝ)⁻¹ :=
      (le_abs_self _).trans hb
    _ ≤ d := by
      rw [mul_inv_le_iff₀ hnpos]
      simpa [mul_comm] using! (div_le_iff₀ hd).mp hn

lemma fixed_scale_bounds (hCyc : CyclicStructureStatement)
    (hTree : TreeMassStatement) {M : NatSeq} {lam : ℝ}
    (hM : admissible M) (hlam : 1 < lam)
    (hdeg : Tendsto (degree M) atTop (𝓝 lam)) :
    (∀ᶠ n : ℕ in atTop, 0 < Real.sqrt (n : ℝ)) ∧
    (∃ CU : ℝ, 0 < CU ∧ ∀ᶠ n in atTop,
      expectM n (M n) unicyclicMass ≤ CU * Real.sqrt (n : ℝ)) ∧
    (∃ CV : ℝ, 0 < CV ∧ ∀ᶠ n in atTop,
      varianceM n (M n) (fun G => treeMassBelow G (largeCutoff n)) ≤
        CV * Real.sqrt (n : ℝ) ^ 2) ∧
    (∃ CE : ℝ, 0 < CE ∧ ∀ᶠ n in atTop,
      |treeMeanError M n| ≤ CE * Real.sqrt (n : ℝ)) := by
  have hne : lam ≠ 1 := ne_of_gt hlam
  have hcy := hCyc.2 M lam hM (by linarith) hne hdeg
  have hL0 := hcy.1
  have hEL := hcy.2.1
  rcases (hTree.2 M lam hM hlam hdeg).1 with ⟨CE, hCE, he⟩
  rcases (hTree.2 M lam hM hlam hdeg).2 with ⟨CV, hCV, hv⟩
  let CU := unicyclicLimit lam + 1
  have hCU : 0 < CU := by dsimp [CU]; linarith
  have hu : ∀ᶠ n in atTop, expectM n (M n) unicyclicMass ≤ CU := by
    have := (tendsto_order.1 hEL).2 CU (by dsimp [CU]; linarith)
    exact this.mono fun n hn => hn.le
  have hs : ∀ᶠ n : ℕ in atTop, 1 ≤ Real.sqrt (n : ℝ) := by
    have hn := tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop (1 : ℝ))
    exact hn.mono fun n hn => (Real.one_le_sqrt).2 hn
  refine ⟨hs.mono fun n hn => zero_lt_one.trans_le hn,
    ⟨CU, hCU, ?_⟩, ⟨CV, hCV, ?_⟩, ⟨CE, hCE, ?_⟩⟩
  · filter_upwards [hu, hs] with n hu hs
    exact hu.trans (le_mul_of_one_le_right hCU.le hs)
  · filter_upwards [hv] with n hv
    have hsquare := Real.sq_sqrt (show 0 ≤ (n : ℝ) by positivity)
    calc
      varianceM n (M n) (fun G => treeMassBelow G (largeCutoff n)) ≤
          CV * (n : ℝ) := (le_abs_self _).trans hv
      _ = CV * Real.sqrt (n : ℝ) ^ 2 := by rw [hsquare]
  · filter_upwards [he, hs] with n he hs
    have hmul := mul_le_mul_of_nonneg_left hs hCE.le
    simpa using! he.trans hmul

theorem fixed_largeMass_tight (hF : FiniteEnumerationStatement)
    (hCyc : CyclicStructureStatement) (hTree : TreeMassStatement)
    (M : NatSeq) (lam : ℝ) (hM : admissible M) (hlam : 1 < lam)
    (hdeg : Tendsto (degree M) atTop (𝓝 lam)) :
    tightScaled M (fun n G => largeMass G (largeCutoff n)) (giantCenter M)
      (fun n => Real.sqrt (n : ℝ)) := by
  rcases fixed_scale_bounds hCyc hTree hM hlam hdeg with ⟨hs, hu, hv, he⟩
  exact tight_largeMass_of_bounds hF hM hs
    (fixed_complex_vanishes hCyc hM hlam hdeg) hu hv he

end
end Erdos745.WrapUp.Proofs.Internal.W10_GIANT_Concentration


namespace Erdos745.WrapUp.Proofs.Internal.W10_GIANT_Closure

noncomputable section
open Filter
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

open W10_GIANT_Components
open W10_GIANT_Bridges

/-! This module is the closure layer of the giant-component argument.  Its
inputs are exactly the four bad events left to the sprinkling and enumeration
estimates: non-uniqueness, a large tree, a large unicyclic component, and a
small positive-excess component. -/

lemma probM_mono {n M : ℕ} {A B : Graph n → Prop}
    (hAB : ∀ G, A G → B G) :
    probM n M A ≤ probM n M B := by
  unfold probM
  apply div_le_div_of_nonneg_right _ (by positivity)
  norm_cast
  apply Finset.card_le_card
  intro G hG
  exact Finset.mem_filter.mpr
    ⟨(Finset.mem_filter.mp hG).1, hAB G (Finset.mem_filter.mp hG).2⟩

lemma probM_or_le {n M : ℕ} (A B : Graph n → Prop) :
    probM n M (fun G ↦ A G ∨ B G) ≤ probM n M A + probM n M B := by
  unfold probM
  rw [Finset.filter_congr_decidable (fixedGraphs n M)
    (fun G ↦ A G ∨ B G) (fun _ ↦ Classical.propDecidable _)]
  rw [← add_div]
  apply div_le_div_of_nonneg_right _ (by positivity)
  rw [← Nat.cast_add, Nat.cast_le]
  calc
    ((fixedGraphs n M).filter fun G ↦ A G ∨ B G).card ≤
        ((fixedGraphs n M).filter A ∪ (fixedGraphs n M).filter B).card := by
      apply Finset.card_le_card
      intro G hG
      rcases (Finset.mem_filter.mp hG).2 with hA | hB
      · exact Finset.mem_union_left _
          (Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hG).1, hA⟩)
      · exact Finset.mem_union_right _
          (Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hG).1, hB⟩)
    _ ≤ ((fixedGraphs n M).filter A).card +
          ((fixedGraphs n M).filter B).card :=
      Finset.card_union_le _ _

lemma probM_compl_eq_one_sub (hF : FiniteEnumerationStatement)
    {n M : ℕ} (hM : M ≤ capacity n) (A : Graph n → Prop) :
    probM n M A = 1 - probM n M (fun G ↦ ¬ A G) := by
  have hnorm := W08_CYCLIC_Finite.enum_normalization hF n M hM
  have hcardpos : 0 < ((fixedGraphs n M).card : ℝ) := by
    unfold expectM at hnorm
    by_contra hnot
    have hz : ((fixedGraphs n M).card : ℝ) = 0 :=
      le_antisymm (le_of_not_gt hnot) (by positivity)
    simp [hz] at hnorm
  unfold probM
  rw [Finset.filter_congr_decidable (fixedGraphs n M)
    (fun G ↦ ¬ A G) (fun _ ↦ Classical.propDecidable _)]
  rw [eq_sub_iff_add_eq, ← add_div]
  field_simp [hcardpos.ne']
  norm_cast
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext G
    by_cases hG : G ∈ fixedGraphs n M <;>
      by_cases hA : A G <;> simp [hG, hA]
  · rw [Finset.disjoint_left]
    intro G hA hnA
    exact (Finset.mem_filter.mp hnA).2 (Finset.mem_filter.mp hA).2

lemma no_large_tree_of_count_eq_zero {n h : ℕ} {G : Graph n}
    (hzero : treeCountGE G h = 0) {S : Finset (Fin n)}
    (hS : S ∈ components G) (hlarge : h ≤ S.card) :
    ¬ isTree G S := by
  intro htree
  have hmem : S ∈ (components G).filter
      (fun T ↦ isTree G T ∧ h ≤ T.card) :=
    Finset.mem_filter.mpr ⟨hS, htree, hlarge⟩
  have hpos : 0 < ((components G).filter
      (fun T ↦ isTree G T ∧ h ≤ T.card)).card :=
    Finset.card_pos.mpr ⟨S, hmem⟩
  unfold treeCountGE at hzero
  omega

lemma no_large_unicyclic_of_mass_lt {n h : ℕ} {G : Graph n}
    (hmass : unicyclicMass G < h) {S : Finset (Fin n)}
    (hS : S ∈ components G) (hlarge : h ≤ S.card) :
    ¬ isUnicyclic G S := by
  intro huni
  have hsingle : (S.card : ℝ) ≤ unicyclicMass G := by
    unfold unicyclicMass
    calc
      (S.card : ℝ) = if isUnicyclic G S then (S.card : ℝ) else 0 := by
        simp [huni]
      _ ≤ ∑ T ∈ components G,
          if isUnicyclic G T then (T.card : ℝ) else 0 := by
        exact Finset.single_le_sum (s := components G)
          (f := fun T ↦ if isUnicyclic G T then (T.card : ℝ) else 0)
          (fun T _ ↦ by by_cases hT : isUnicyclic G T <;> simp [hT]) hS
  have hh : (h : ℝ) ≤ (S.card : ℝ) := by exact_mod_cast hlarge
  exact (not_lt_of_ge (hh.trans hsingle)) hmass

lemma separatedStructure_of_good {n : ℕ} {G : Graph n}
    (hunique : countGE G (largeCutoff n) = 1)
    (htree : treeCountGE G (largeCutoff n) = 0)
    (huni : unicyclicMass G < largeCutoff n)
    (hsmall : smallComplexCount G (largeCutoff n) = 0) :
    separatedStructure G := by
  refine ⟨hunique, ?_, ?_⟩
  · intro S hS hSl
    exact no_small_complex_of_count_eq_zero hsmall hS hSl
  · intro S hS hSl
    have hlower := component_edge_lower_bound hS
    have hnTree := no_large_tree_of_count_eq_zero htree hS hSl
    have hnUni := no_large_unicyclic_of_mass_lt huni hS hSl
    have htreeNe : edgesInside G S + 1 ≠ S.card := by
      intro heq
      exact hnTree ⟨hS, heq⟩
    have huniNe : edgesInside G S ≠ S.card := by
      intro heq
      exact hnUni ⟨hS, heq⟩
    omega

lemma not_separatedStructure_imp_bad {n : ℕ} {G : Graph n}
    (hbad : ¬ separatedStructure G) :
    countGE G (largeCutoff n) ≠ 1 ∨
      0 < treeCountGE G (largeCutoff n) ∨
      (largeCutoff n : ℝ) ≤ unicyclicMass G ∨
      0 < smallComplexCount G (largeCutoff n) := by
  by_contra hnone
  push_neg at hnone
  have htree : treeCountGE G (largeCutoff n) = 0 :=
    Nat.eq_zero_of_le_zero hnone.2.1
  have hsmall : smallComplexCount G (largeCutoff n) = 0 :=
    Nat.eq_zero_of_le_zero hnone.2.2.2
  exact hbad (separatedStructure_of_good hnone.1 htree hnone.2.2.1 hsmall)

lemma prob_not_separatedStructure_le (n M : ℕ) :
    probM n M (fun G ↦ ¬ separatedStructure G) ≤
      probM n M (fun G ↦ countGE G (largeCutoff n) ≠ 1) +
      probM n M (fun G ↦ 0 < treeCountGE G (largeCutoff n)) +
      probM n M (fun G ↦ (largeCutoff n : ℝ) ≤ unicyclicMass G) +
      probM n M (fun G ↦ 0 < smallComplexCount G (largeCutoff n)) := by
  calc
    probM n M (fun G ↦ ¬ separatedStructure G) ≤
        probM n M (fun G ↦
          countGE G (largeCutoff n) ≠ 1 ∨
          (0 < treeCountGE G (largeCutoff n) ∨
          ((largeCutoff n : ℝ) ≤ unicyclicMass G ∨
          0 < smallComplexCount G (largeCutoff n)))) := by
      apply probM_mono
      intro G hG
      rcases not_separatedStructure_imp_bad hG with h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr h))
    _ ≤ probM n M (fun G ↦ countGE G (largeCutoff n) ≠ 1) +
          probM n M (fun G ↦
            0 < treeCountGE G (largeCutoff n) ∨
            ((largeCutoff n : ℝ) ≤ unicyclicMass G ∨
            0 < smallComplexCount G (largeCutoff n))) :=
      probM_or_le _ _
    _ ≤ probM n M (fun G ↦ countGE G (largeCutoff n) ≠ 1) +
          (probM n M (fun G ↦ 0 < treeCountGE G (largeCutoff n)) +
          probM n M (fun G ↦
            (largeCutoff n : ℝ) ≤ unicyclicMass G ∨
            0 < smallComplexCount G (largeCutoff n))) := by
      gcongr
      exact probM_or_le _ _
    _ ≤ probM n M (fun G ↦ countGE G (largeCutoff n) ≠ 1) +
          probM n M (fun G ↦ 0 < treeCountGE G (largeCutoff n)) +
          (probM n M (fun G ↦
            (largeCutoff n : ℝ) ≤ unicyclicMass G) +
          probM n M (fun G ↦ 0 < smallComplexCount G (largeCutoff n))) := by
      have h34 : probM n M (fun G ↦
          (largeCutoff n : ℝ) ≤ unicyclicMass G ∨
          0 < smallComplexCount G (largeCutoff n)) ≤
          probM n M (fun G ↦ (largeCutoff n : ℝ) ≤ unicyclicMass G) +
          probM n M (fun G ↦ 0 < smallComplexCount G (largeCutoff n)) :=
        probM_or_le _ _
      have h234 := add_le_add_left h34
        (probM n M (fun G ↦ 0 < treeCountGE G (largeCutoff n)))
      have h1234 := add_le_add_left h234
        (probM n M (fun G ↦ countGE G (largeCutoff n) ≠ 1))
      linarith [h1234]
    _ = _ := by ac_rfl

theorem separatedStructure_tendsto_one (hF : FiniteEnumerationStatement)
    {M : NatSeq} (hM : admissible M)
    (hunique : Tendsto (fun n ↦ probM n (M n)
      (fun G ↦ countGE G (largeCutoff n) ≠ 1)) atTop (𝓝 0))
    (htree : Tendsto (fun n ↦ probM n (M n)
      (fun G ↦ 0 < treeCountGE G (largeCutoff n))) atTop (𝓝 0))
    (huni : Tendsto (fun n ↦ probM n (M n)
      (fun G ↦ (largeCutoff n : ℝ) ≤ unicyclicMass G)) atTop (𝓝 0))
    (hsmall : Tendsto (fun n ↦ probM n (M n)
      (fun G ↦ 0 < smallComplexCount G (largeCutoff n))) atTop (𝓝 0)) :
    Tendsto (fun n ↦ probM n (M n) separatedStructure) atTop (𝓝 1) := by
  have hsum : Tendsto (fun n ↦
      probM n (M n) (fun G ↦ countGE G (largeCutoff n) ≠ 1) +
      probM n (M n) (fun G ↦ 0 < treeCountGE G (largeCutoff n)) +
      probM n (M n) (fun G ↦ (largeCutoff n : ℝ) ≤ unicyclicMass G) +
      probM n (M n) (fun G ↦ 0 < smallComplexCount G (largeCutoff n)))
      atTop (𝓝 0) := by
    simpa only [zero_add, add_zero] using! ((hunique.add htree).add huni).add hsmall
  have hbad : Tendsto (fun n ↦ probM n (M n)
      (fun G ↦ ¬ separatedStructure G)) atTop (𝓝 0) := by
    apply squeeze_zero'
    · filter_upwards with n
      unfold probM
      positivity
    · filter_upwards with n
      exact prob_not_separatedStructure_le n (M n)
    · exact hsum
  have hcomp : ∀ᶠ n in atTop,
      probM n (M n) separatedStructure =
        1 - probM n (M n) (fun G ↦ ¬ separatedStructure G) := by
    filter_upwards [hM] with n hn
    exact probM_compl_eq_one_sub hF hn separatedStructure
  have ht : Tendsto (fun n ↦ (1 : ℝ) - probM n (M n)
      (fun G ↦ ¬ separatedStructure G)) atTop (𝓝 ((1 : ℝ) - 0)) :=
    tendsto_const_nhds.sub hbad
  have ht' := ht.congr' (hcomp.mono fun n hn ↦ hn.symm)
  simpa using! ht'

theorem rank_one_tight_of_largeMass_tight
    {M : NatSeq} {s : RealSeq}
    (hmass : tightScaled M (fun n G ↦ largeMass G (largeCutoff n))
      (giantCenter M) s)
    (hunique : Tendsto (fun n ↦ probM n (M n)
      (fun G ↦ countGE G (largeCutoff n) ≠ 1)) atTop (𝓝 0)) :
    tightScaled M (fun _ G ↦ (rankSize G 1 : ℝ)) (giantCenter M) s := by
  intro d hd
  rcases hmass (d / 2) (by positivity) with ⟨K, hK, hmassK⟩
  refine ⟨K, hK, ?_⟩
  have huniqueK : ∀ᶠ n in atTop,
      probM n (M n) (fun G ↦ countGE G (largeCutoff n) ≠ 1) < d / 2 :=
    (tendsto_order.1 hunique).2 _ (by positivity)
  filter_upwards [hmassK, huniqueK] with n hm hu
  calc
    probM n (M n) (fun G ↦
        |(rankSize G 1 : ℝ) - giantCenter M n| > K * s n) ≤
        probM n (M n) (fun G ↦
          |largeMass G (largeCutoff n) - giantCenter M n| > K * s n ∨
          countGE G (largeCutoff n) ≠ 1) := by
      apply probM_mono
      intro G hG
      by_cases hc : countGE G (largeCutoff n) = 1
      · left
        rw [← rank_one_eq_largeMass_of_unique hc]
        exact hG
      · exact Or.inr hc
    _ ≤ probM n (M n) (fun G ↦
          |largeMass G (largeCutoff n) - giantCenter M n| > K * s n) +
        probM n (M n) (fun G ↦ countGE G (largeCutoff n) ≠ 1) :=
      probM_or_le _ _
    _ ≤ d := by linarith

theorem giantBranch_of_bad_events (hF : FiniteEnumerationStatement)
    {M : NatSeq} {s : RealSeq} (hM : admissible M)
    (hmass : tightScaled M (fun n G ↦ largeMass G (largeCutoff n))
      (giantCenter M) s)
    (hunique : Tendsto (fun n ↦ probM n (M n)
      (fun G ↦ countGE G (largeCutoff n) ≠ 1)) atTop (𝓝 0))
    (htree : Tendsto (fun n ↦ probM n (M n)
      (fun G ↦ 0 < treeCountGE G (largeCutoff n))) atTop (𝓝 0))
    (huni : Tendsto (fun n ↦ probM n (M n)
      (fun G ↦ (largeCutoff n : ℝ) ≤ unicyclicMass G)) atTop (𝓝 0))
    (hsmall : Tendsto (fun n ↦ probM n (M n)
      (fun G ↦ 0 < smallComplexCount G (largeCutoff n))) atTop (𝓝 0)) :
    tightScaled M (fun n G ↦ largeMass G (largeCutoff n)) (giantCenter M) s ∧
    tightScaled M (fun _ G ↦ (rankSize G 1 : ℝ)) (giantCenter M) s ∧
    Tendsto (fun n ↦ probM n (M n) separatedStructure) atTop (𝓝 1) := by
  exact ⟨hmass, rank_one_tight_of_largeMass_tight hmass hunique,
    separatedStructure_tendsto_one hF hM hunique htree huni hsmall⟩

end
end Erdos745.WrapUp.Proofs.Internal.W10_GIANT_Closure


namespace Erdos745.WrapUp.Proofs.Internal.W10_GIANT_Exclusions

noncomputable section
open Filter
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

open Erdos745.WrapUp.Proofs.W06_POISSON
open W08_CYCLIC_Finite
open W10_GIANT_Concentration
open W10_GIANT_Closure

/-! Cyclic-side bad-event estimates used by both giant-component branches. -/

lemma unicyclicMass_nonneg {n : ℕ} (G : Graph n) :
    0 ≤ unicyclicMass G := by
  unfold unicyclicMass
  exact Finset.sum_nonneg fun S _ ↦ by
    by_cases hS : isUnicyclic G S <;> simp [hS]

lemma prob_smallComplex_pos_le_expect (hF : FiniteEnumerationStatement)
    {n M h : ℕ} (hM : M ≤ capacity n) :
    probM n M (fun G ↦ 0 < smallComplexCount G h) ≤
      expectM n M (fun G ↦ (smallComplexCount G h : ℝ)) := by
  apply probM_le_expectM_of_indicator hF hM
  · intro G
    positivity
  · intro G hG
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hG))

lemma prob_unicyclicMass_ge_le_expect_div (hF : FiniteEnumerationStatement)
    {n M : ℕ} (hM : M ≤ capacity n) {h : ℝ} (hh : 0 < h) :
    probM n M (fun G ↦ h ≤ unicyclicMass G) ≤
      expectM n M unicyclicMass / h := by
  have hbound := probM_le_expectM_of_indicator hF hM
    (fun G ↦ h ≤ unicyclicMass G) (fun G ↦ unicyclicMass G / h)
    (fun G ↦ div_nonneg (unicyclicMass_nonneg G) hh.le)
    (fun G hG ↦ (le_div_iff₀ hh).2 (by simpa using! hG))
  simpa [expectM_div_const] using! hbound

lemma largeCutoff_real_tendsto_atTop :
    Tendsto (fun n : ℕ ↦ (largeCutoff n : ℝ)) atTop atTop := by
  have hn23 : Tendsto n23 atTop atTop := by
    unfold n23
    exact (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 3)).comp
      tendsto_natCast_atTop_atTop
  apply tendsto_atTop_mono' atTop _ hn23
  filter_upwards with n
  exact Nat.le_ceil (n23 n)

lemma largeCutoff_eventually_pos :
    ∀ᶠ n : ℕ in atTop, 0 < largeCutoff n := by
  have hlarge := (tendsto_atTop.1 largeCutoff_real_tendsto_atTop) 1
  filter_upwards [hlarge] with n hn
  exact_mod_cast (zero_lt_one.trans_le hn)

lemma width_rpow_two_thirds {M : NatSeq} {n : ℕ}
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

lemma near_invSq_div_largeCutoff_tendsto_zero {M : NatSeq}
    (hbare : bareSuper M) :
    Tendsto (fun n ↦ (epsilon M n)⁻¹ ^ 2 / (largeCutoff n : ℝ))
      atTop (𝓝 0) := by
  have hw : Tendsto (widthParameter M) atTop atTop := hbare.2.2.2
  have hpow : Tendsto
      (fun n ↦ Real.rpow (widthParameter M n) (2 / 3 : ℝ))
      atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 3)).comp hw
  have hinv : Tendsto
      (fun n ↦ (Real.rpow (widthParameter M n) (2 / 3 : ℝ))⁻¹)
      atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hpow
  apply squeeze_zero'
  · filter_upwards [bare_epsilon_pos (Or.inr hbare), largeCutoff_eventually_pos]
      with n he hh
    positivity
  · filter_upwards [bare_epsilon_pos (Or.inr hbare), eventually_gt_atTop 0]
      with n he hn
    have hn23 : 0 < n23 n := Real.rpow_pos_of_pos (by positivity) _
    have hceil : n23 n ≤ (largeCutoff n : ℝ) := Nat.le_ceil _
    have hcut : 0 < (largeCutoff n : ℝ) := hn23.trans_le hceil
    have hden : n23 n * epsilon M n ^ 2 ≤
        (largeCutoff n : ℝ) * epsilon M n ^ 2 := by
      gcongr
    calc
      (epsilon M n)⁻¹ ^ 2 / (largeCutoff n : ℝ) =
          1 / ((largeCutoff n : ℝ) * epsilon M n ^ 2) := by
        field_simp [he.ne', hcut.ne']
      _ ≤ 1 / (n23 n * epsilon M n ^ 2) :=
        one_div_le_one_div_of_le (mul_pos hn23 (sq_pos_of_pos he)) hden
      _ = (Real.rpow (widthParameter M n) (2 / 3 : ℝ))⁻¹ := by
        rw [width_rpow_two_thirds hn he]
        simp only [one_div]
  · exact hinv

lemma expectation_tendsto_zero_of_nonneg_of_eventually_le
    {f : RealSeq} (hf : ∀ n, 0 ≤ f n)
    (hsmall : ∀ d : ℝ, 0 < d → ∀ᶠ n in atTop, f n ≤ d) :
    Tendsto f atTop (𝓝 0) := by
  rw [tendsto_order]
  constructor
  · intro a ha
    filter_upwards with n
    exact ha.trans_le (hf n)
  · intro b hb
    filter_upwards [hsmall (b / 2) (by positivity)] with n hn
    linarith

lemma smallComplex_bad_tendsto_zero_of_expectation
    (hF : FiniteEnumerationStatement) {M : NatSeq} (hM : admissible M)
    (hsmall : ∀ d : ℝ, 0 < d → ∀ᶠ n in atTop,
      expectM n (M n) (fun G ↦
        (smallComplexCount G (largeCutoff n) : ℝ)) ≤ d) :
    Tendsto (fun n ↦ probM n (M n)
      (fun G ↦ 0 < smallComplexCount G (largeCutoff n))) atTop (𝓝 0) := by
  have hexpect : Tendsto (fun n ↦ expectM n (M n) (fun G ↦
      (smallComplexCount G (largeCutoff n) : ℝ))) atTop (𝓝 0) :=
    expectation_tendsto_zero_of_nonneg_of_eventually_le
      (fun n ↦ expect_smallComplexCount_nonneg n (M n) (largeCutoff n)) hsmall
  apply squeeze_zero'
  · filter_upwards with n
    unfold probM
    positivity
  · filter_upwards [hM] with n hn
    exact prob_smallComplex_pos_le_expect hF hn
  · exact hexpect

lemma unicyclicMass_bad_tendsto_zero_of_ratio
    (hF : FiniteEnumerationStatement) {M : NatSeq} (hM : admissible M)
    (hratio : Tendsto (fun n ↦
      expectM n (M n) unicyclicMass / (largeCutoff n : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n ↦ probM n (M n)
      (fun G ↦ (largeCutoff n : ℝ) ≤ unicyclicMass G)) atTop (𝓝 0) := by
  apply squeeze_zero'
  · filter_upwards with n
    unfold probM
    positivity
  · filter_upwards [hM, largeCutoff_eventually_pos] with n hnM hcut
    exact prob_unicyclicMass_ge_le_expect_div hF hnM (by exact_mod_cast hcut)
  · exact hratio

lemma near_unicyclicMass_ratio_tendsto_zero
    (hCyc : CyclicStructureStatement) {M : NatSeq} (hbare : bareSuper M) :
    Tendsto (fun n ↦ expectM n (M n) unicyclicMass /
      (largeCutoff n : ℝ)) atTop (𝓝 0) := by
  rcases (hCyc.1 M (Or.inr hbare)).1 with ⟨C, hC, hmass⟩
  have hscale := near_invSq_div_largeCutoff_tendsto_zero hbare
  have hupper : ∀ᶠ n in atTop,
      expectM n (M n) unicyclicMass / (largeCutoff n : ℝ) ≤
        C * ((epsilon M n)⁻¹ ^ 2 / (largeCutoff n : ℝ)) := by
    filter_upwards [hmass, largeCutoff_eventually_pos] with n hm hcut
    have hcutR : 0 < (largeCutoff n : ℝ) := by exact_mod_cast hcut
    have hE : expectM n (M n) unicyclicMass ≤
        C * (epsilon M n)⁻¹ ^ 2 :=
      (le_abs_self _).trans hm
    calc
      expectM n (M n) unicyclicMass / (largeCutoff n : ℝ) ≤
          (C * (epsilon M n)⁻¹ ^ 2) / (largeCutoff n : ℝ) := by
        gcongr
      _ = C * ((epsilon M n)⁻¹ ^ 2 / (largeCutoff n : ℝ)) := by ring
  apply squeeze_zero'
  · filter_upwards [largeCutoff_eventually_pos] with n hcut
    exact div_nonneg (expect_unicyclicMass_nonneg n (M n)) (by positivity)
  · exact hupper
  · simpa using! hscale.const_mul C

lemma fixed_unicyclicMass_ratio_tendsto_zero
    (hCyc : CyclicStructureStatement) {M : NatSeq} {lam : ℝ}
    (hM : admissible M) (hlam : 1 < lam)
    (hdeg : Tendsto (degree M) atTop (𝓝 lam)) :
    Tendsto (fun n ↦ expectM n (M n) unicyclicMass /
      (largeCutoff n : ℝ)) atTop (𝓝 0) := by
  have hcyc := hCyc.2 M lam hM (by linarith) (ne_of_gt hlam) hdeg
  have hmass := hcyc.2.1
  have hinv : Tendsto (fun n ↦ ((largeCutoff n : ℝ))⁻¹)
      atTop (𝓝 0) := tendsto_inv_atTop_zero.comp largeCutoff_real_tendsto_atTop
  simpa [div_eq_mul_inv] using! hmass.mul hinv

theorem near_cyclic_bad_limits (hF : FiniteEnumerationStatement)
    (hCyc : CyclicStructureStatement) {M : NatSeq} (hbare : bareSuper M) :
    Tendsto (fun n ↦ probM n (M n)
      (fun G ↦ (largeCutoff n : ℝ) ≤ unicyclicMass G)) atTop (𝓝 0) ∧
    Tendsto (fun n ↦ probM n (M n)
      (fun G ↦ 0 < smallComplexCount G (largeCutoff n))) atTop (𝓝 0) := by
  constructor
  · exact unicyclicMass_bad_tendsto_zero_of_ratio hF hbare.1
      (near_unicyclicMass_ratio_tendsto_zero hCyc hbare)
  · exact smallComplex_bad_tendsto_zero_of_expectation hF hbare.1
      (near_complex_vanishes hCyc hbare)

theorem fixed_cyclic_bad_limits (hF : FiniteEnumerationStatement)
    (hCyc : CyclicStructureStatement) {M : NatSeq} {lam : ℝ}
    (hM : admissible M) (hlam : 1 < lam)
    (hdeg : Tendsto (degree M) atTop (𝓝 lam)) :
    Tendsto (fun n ↦ probM n (M n)
      (fun G ↦ (largeCutoff n : ℝ) ≤ unicyclicMass G)) atTop (𝓝 0) ∧
    Tendsto (fun n ↦ probM n (M n)
      (fun G ↦ 0 < smallComplexCount G (largeCutoff n))) atTop (𝓝 0) := by
  constructor
  · exact unicyclicMass_bad_tendsto_zero_of_ratio hF hM
      (fixed_unicyclicMass_ratio_tendsto_zero hCyc hM hlam hdeg)
  · exact smallComplex_bad_tendsto_zero_of_expectation hF hM
      (fixed_complex_vanishes hCyc hM hlam hdeg)

theorem near_giantBranch_of_unique_tree (hF : FiniteEnumerationStatement)
    (hCyc : CyclicStructureStatement) (hTree : TreeMassStatement)
    (M : NatSeq) (hbare : bareSuper M)
    (hunique : Tendsto (fun n ↦ probM n (M n)
      (fun G ↦ countGE G (largeCutoff n) ≠ 1)) atTop (𝓝 0))
    (htree : Tendsto (fun n ↦ probM n (M n)
      (fun G ↦ 0 < treeCountGE G (largeCutoff n))) atTop (𝓝 0)) :
    tightScaled M (fun n G ↦ largeMass G (largeCutoff n)) (giantCenter M)
        (fun n ↦ Real.sqrt ((n : ℝ) / epsilon M n)) ∧
      tightScaled M (fun _ G ↦ (rankSize G 1 : ℝ)) (giantCenter M)
        (fun n ↦ Real.sqrt ((n : ℝ) / epsilon M n)) ∧
      Tendsto (fun n ↦ probM n (M n) separatedStructure) atTop (𝓝 1) := by
  rcases near_cyclic_bad_limits hF hCyc hbare with ⟨huni, hsmall⟩
  exact giantBranch_of_bad_events hF hbare.1
    (near_largeMass_tight hF hCyc hTree M hbare)
    hunique htree huni hsmall

theorem fixed_giantBranch_of_unique_tree (hF : FiniteEnumerationStatement)
    (hCyc : CyclicStructureStatement) (hTree : TreeMassStatement)
    (M : NatSeq) (lam : ℝ) (hM : admissible M) (hlam : 1 < lam)
    (hdeg : Tendsto (degree M) atTop (𝓝 lam))
    (hunique : Tendsto (fun n ↦ probM n (M n)
      (fun G ↦ countGE G (largeCutoff n) ≠ 1)) atTop (𝓝 0))
    (htree : Tendsto (fun n ↦ probM n (M n)
      (fun G ↦ 0 < treeCountGE G (largeCutoff n))) atTop (𝓝 0)) :
    tightScaled M (fun n G ↦ largeMass G (largeCutoff n)) (giantCenter M)
        (fun n ↦ Real.sqrt (n : ℝ)) ∧
      tightScaled M (fun _ G ↦ (rankSize G 1 : ℝ)) (giantCenter M)
        (fun n ↦ Real.sqrt (n : ℝ)) ∧
      Tendsto (fun n ↦ probM n (M n) separatedStructure) atTop (𝓝 1) := by
  rcases fixed_cyclic_bad_limits hF hCyc hM hlam hdeg with ⟨huni, hsmall⟩
  exact giantBranch_of_bad_events hF hM
    (fixed_largeMass_tight hF hCyc hTree M lam hM hlam hdeg)
    hunique htree huni hsmall

end
end Erdos745.WrapUp.Proofs.Internal.W10_GIANT_Exclusions
