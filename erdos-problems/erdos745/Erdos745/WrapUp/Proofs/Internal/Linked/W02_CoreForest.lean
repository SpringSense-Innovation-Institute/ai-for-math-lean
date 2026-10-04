module

public import Erdos745.WrapUp.Proofs.Internal.Linked.W02_ExpansionCore
public import Erdos745.WrapUp.Proofs.Internal.Linked.W01_FiniteCore
public import Erdos745.WrapUp.Proofs.Internal.Linked.W01_Pruefer

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local simp] Pi.div_def Pi.mul_def Pi.add_def Pi.sub_def Pi.neg_def Pi.inv_def Function.comp_def Pi.pow_def Pi.smul_def Real.rpow_eq_pow

@[expose] public section


/-! Integer excess bookkeeping along deterministic leaf pruning. -/

noncomputable section

namespace Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_CoreExcess

open Erdos745.WrapUp
open Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_Expansion
open Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_Core

end Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_CoreExcess


/-!
# Connected exact-excess cores and their branch set

This is the graph-theoretic front of suppression.  It complements the
deterministic ambient pruning development with an existential presentation on
the surviving vertex type.  Deleting a leaf preserves connectedness and
`edges - vertices`, so the resulting core is connected, has exact excess, and
has minimum degree two.  Its degree surplus then bounds the number of branch
vertices by `2r`.
-/

noncomputable section

namespace Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_CoreConnected

open Erdos745.WrapUp
open Erdos745.WrapUp.Proofs.Internal.W01_ENUM_Trees
open Finset
open scoped Sym2

attribute [local instance] Classical.propDecidable

private def edgeSym2 {k : ℕ} (e : Edge k) : Sym2 (Fin k) :=
  s(e.val.1, e.val.2)

private lemma edgeSym2_injective {k : ℕ} :
    Function.Injective (@edgeSym2 k) := by
  intro e f hef
  apply Subtype.ext
  apply Prod.ext
  · rcases Sym2.eq_iff.mp hef with h | h
    · exact h.1
    · have hfe : f.val.2 < f.val.1 := by
        simpa [h.1, h.2] using! e.property
      exact False.elim ((lt_asymm f.property hfe))
  · rcases Sym2.eq_iff.mp hef with h | h
    · exact h.2
    · have hfe : f.val.2 < f.val.1 := by
        simpa [h.1, h.2] using! e.property
      exact False.elim ((lt_asymm f.property hfe))

private lemma simpleGraph_edgeFinset_card {k : ℕ} (G : Graph k) :
    (simpleGraph G).edgeFinset.card = G.card := by
  symm
  apply Finset.card_bij (fun e _ => edgeSym2 e)
  · intro e he
    rw [SimpleGraph.mem_edgeFinset]
    change s(e.val.1, e.val.2) ∈ (simpleGraph G).edgeSet
    rw [SimpleGraph.mem_edgeSet]
    exact ⟨e, he, Or.inl ⟨rfl, rfl⟩⟩
  · intro e₁ _ e₂ _ h
    exact edgeSym2_injective h
  · intro b hb
    induction b using Sym2.inductionOn with
    | _ u v =>
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at hb
      rcases hb with ⟨e, he, huv | hvu⟩
      · exact ⟨e, he, by simp [edgeSym2, huv.1, huv.2]⟩
      · exact ⟨e, he, by simp [edgeSym2, hvu.1, hvu.2]⟩

/-- A connected, exact-excess, minimum-degree-two subgraph carried by an
explicit set of original labels. -/
structure ConnectedCoreIn {k : ℕ} (G : Graph k) (r : ℕ) where
  v : ℕ
  labels : Fin v ↪ Fin k
  graph : SimpleGraph (Fin v)
  connected : graph.Connected
  edge_card : graph.edgeFinset.card = v + r
  min_degree : ∀ x, 2 ≤ graph.degree x
  subgraph : graph.map labels ≤ simpleGraph G

private def HasConnectedCoreIn {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (r : ℕ) : Prop :=
  ∃ v : ℕ, ∃ f : Fin v ↪ V, ∃ H : SimpleGraph (Fin v),
    H.Connected ∧ H.edgeFinset.card = v + r ∧
      (∀ x, 2 ≤ H.degree x) ∧ H.map f ≤ G

set_option maxHeartbeats 2000000 in
private theorem exists_connectedCore_aux (r m : ℕ) (hr : 0 < r) :
    ∀ (V : Type) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V),
      Fintype.card V = m → G.Connected →
      G.edgeFinset.card = m + r → HasConnectedCoreIn G r := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
      intro V _ _ G hm hG hcard
      by_cases hmin : ∀ x, 2 ≤ G.degree x
      · let e : V ≃ Fin m := (Fintype.equivFin V).trans (finCongr hm)
        let f : Fin m ↪ V := e.symm.toEmbedding
        let H : SimpleGraph (Fin m) := G.comap f
        let iso : H ≃g G := SimpleGraph.Iso.comap e.symm G
        refine ⟨m, f, H, ?_, ?_, ?_, ?_⟩
        · exact iso.connected_iff.mpr hG
        · have hi := iso.card_edgeFinset_eq
          change H.edgeFinset.card = G.edgeFinset.card at hi
          exact hi.trans hcard
        · intro x
          have hi := iso.degree_eq x
          change G.degree (f x) = H.degree x at hi
          simpa only [hi] using! hmin (f x)
        · exact (SimpleGraph.map_le_iff_le_comap).2 le_rfl
      · push_neg at hmin
        obtain ⟨x, hx⟩ := hmin
        have hmpos : 0 < m := by
          rw [← hm]
          exact Fintype.card_pos_iff.mpr hG.nonempty
        have hnontriv : Nontrivial V := by
          rw [← Fintype.one_lt_card_iff_nontrivial, hm]
          by_contra hm1
          have hcap := G.card_edgeFinset_le_card_choose_two
          rw [hcard, hm] at hcap
          have hmle : m ≤ 1 := by omega
          interval_cases m
          all_goals norm_num [Nat.choose] at hcap
        letI : Nontrivial V := hnontriv
        have hdegpos : 0 < G.degree x :=
          hG.preconnected.degree_pos_of_nontrivial x
        have hdeg : G.degree x = 1 := by omega
        let W := {y : V // y ≠ x}
        let G' : SimpleGraph W := G.induce ({x}ᶜ : Set V)
        have hG' : G'.Connected :=
          hG.induce_compl_singleton_of_degree_eq_one hdeg
        have hWcard : Fintype.card W = m - 1 := by simp [W, hm]
        have hG'card : G'.edgeFinset.card = (m - 1) + r := by
          rw [show G'.edgeFinset.card =
              (G.deleteIncidenceSet x).edgeFinset.card by
            exact G.card_edgeFinset_induce_compl_singleton x]
          rw [G.card_edgeFinset_deleteIncidenceSet, hcard, hdeg]
          omega
        have hm1 : m - 1 < m := by omega
        obtain ⟨v, f', H, hH, hHcard, hHmin, hHle⟩ :=
          ih (m - 1) hm1 W G' hWcard hG' hG'card
        let incl : W ↪ V := Function.Embedding.subtype _
        let f : Fin v ↪ V := f'.trans incl
        refine ⟨v, f, H, hH, hHcard, hHmin, ?_⟩
        intro a b hab
        rw [SimpleGraph.map_adj] at hab
        obtain ⟨a', b', ha, hb, hab'⟩ := hab
        subst a; subst b
        have hmap : (H.map f').Adj (f' a') (f' b') := by
          rw [SimpleGraph.map_adj]
          exact ⟨a', b', ha, rfl, rfl⟩
        have hg' := hHle hmap
        simpa [G', incl] using! hg'

/-- Every connected simple labelled graph of exact positive excess contains a
connected minimum-degree-two core with the same exact excess. -/
theorem exists_connectedCore {k r : ℕ} {G : Graph k}
    (hr : 0 < r)
    (hconn : ∀ u v : Fin k, reach G u v)
    (hcard : G.card = k + r) :
    Nonempty (ConnectedCoreIn G r) := by
  have hSG : (simpleGraph G).Connected := by
    have hk : 0 < k := by
      by_contra hk0
      simp at hk0
      subst k
      have hGempty : G = ∅ := by
        ext e
        exact Fin.elim0 e.1.1
      simp [hGempty] at hcard
      omega
    letI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
    apply SimpleGraph.Connected.mk
    intro u v
    exact simpleGraph_reachable_iff.mpr (hconn u v)
  obtain ⟨v, f, H, hH, hHcard, hHmin, hHle⟩ :=
    exists_connectedCore_aux r k hr (Fin k) (simpleGraph G) (by simp) hSG (by
      rw [simpleGraph_edgeFinset_card]
      exact hcard)
  exact ⟨⟨v, f, H, hH, hHcard, hHmin, hHle⟩⟩

/-- The core extracted from a positive-excess graph is nonempty. -/
theorem degree_surplus_sum {v r : ℕ} (H : SimpleGraph (Fin v))
    (hcard : H.edgeFinset.card = v + r)
    (hmin : ∀ x, 2 ≤ H.degree x) :
    ∑ x, (H.degree x - 2) = 2 * r := by
  rw [Finset.sum_tsub_distrib univ (fun x _ => hmin x)]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  rw [SimpleGraph.sum_degrees_eq_twice_card_edges, hcard]
  change 2 * (v + r) - v * 2 = 2 * r
  omega

/-- Vertices surviving degree-two suppression. -/
def branchVertices {v : ℕ} (H : SimpleGraph (Fin v)) : Finset (Fin v) :=
  Finset.univ.filter fun x => 3 ≤ H.degree x

theorem mem_branchVertices {v : ℕ} {H : SimpleGraph (Fin v)} {x : Fin v} :
    x ∈ branchVertices H ↔ 3 ≤ H.degree x := by
  simp [branchVertices]

/-- Positive excess forces at least one branch vertex. -/
theorem branchVertices_nonempty {v r : ℕ} (H : SimpleGraph (Fin v))
    (hr : 0 < r)
    (hcard : H.edgeFinset.card = v + r)
    (hmin : ∀ x, 2 ≤ H.degree x) :
    (branchVertices H).Nonempty := by
  by_contra hnone
  have hempty : branchVertices H = ∅ :=
    Finset.not_nonempty_iff_eq_empty.mp hnone
  have hdeg : ∀ x, H.degree x = 2 := by
    intro x
    have hx : x ∉ branchVertices H := by simp [hempty]
    rw [mem_branchVertices] at hx
    change ¬ 3 ≤ H.degree x at hx
    exact Nat.le_antisymm (by omega) (hmin x)
  have hs := degree_surplus_sum H hcard hmin
  simp [hdeg] at hs
  omega

/-- The number of branch vertices is at most twice the excess. -/
theorem card_branchVertices_le {v r : ℕ} (H : SimpleGraph (Fin v))
    (hcard : H.edgeFinset.card = v + r)
    (hmin : ∀ x, 2 ≤ H.degree x) :
    (branchVertices H).card ≤ 2 * r := by
  have hsurplus := degree_surplus_sum H hcard hmin
  have hone :
      ∑ x ∈ branchVertices H, 1 ≤
        ∑ x ∈ branchVertices H, (H.degree x - 2) := by
    apply Finset.sum_le_sum
    intro x hx
    have hx3 := mem_branchVertices.mp hx
    change 3 ≤ H.degree x at hx3
    have hpos : 0 < H.degree x - 2 := Nat.sub_pos_of_lt (by omega)
    omega
  have hsub :
      ∑ x ∈ branchVertices H, (H.degree x - 2) ≤
        ∑ x : Fin v, (H.degree x - 2) := by
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun _ _ _ => Nat.zero_le _)
  simpa [hsurplus] using! hone.trans hsub

/-- Combined extraction theorem at the exact finite family used by the
suppression orbit.  It supplies a connected exact-excess core and a nonempty
branch set of size at most `2r`. -/
theorem positiveExcessGraph_has_branch_core {k r : ℕ}
    (hr : 0 < r) {G : Graph k} (hG : G ∈
      Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_Expansion.positiveExcessGraphs k r) :
    ∃ C : ConnectedCoreIn G r,
      (branchVertices C.graph).Nonempty ∧
        (branchVertices C.graph).card ≤ 2 * r := by
  change G ∈ (fixedGraphs k (k + r)).filter
    (fun H => 0 < k ∧ ∀ u v : Fin k, reach H u v) at hG
  have hfilter := Finset.mem_filter.mp hG
  have hcard : G.card = k + r := by
    have hfixed := hfilter.1
    unfold fixedGraphs at hfixed
    exact (Finset.mem_filter.mp hfixed).2
  have hconn : ∀ u v : Fin k, reach G u v := hfilter.2.2
  obtain ⟨C⟩ := exists_connectedCore hr hconn hcard
  refine ⟨C, branchVertices_nonempty C.graph hr C.edge_card C.min_degree,
    card_branchVertices_le C.graph C.edge_card C.min_degree⟩

end Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_CoreConnected


/-!
# The rooted-forest complement of an exact-excess core

An embedded connected core with the same excess as the ambient connected
graph uses exactly `v+r` edges.  Its literal edge complement therefore has
`k-v` edges.  Every component of that complement meets the core label set:
otherwise ambient connectivity would force an edge leaving the component,
and every core edge has both endpoints in the core label set.  The elementary
component edge lower bound then forces the complement to have exactly `v`
components, each containing exactly one core label and exactly one fewer edge
than vertices.  Thus it is precisely the rooted forest required by the inverse
kernel expansion.
-/

open scoped Sym2 BigOperators

noncomputable section

namespace Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_CoreForest

open Erdos745.WrapUp
open Erdos745.WrapUp.Proofs.Internal.W01_ENUM_Trees
open Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_CoreConnected

attribute [local instance] Classical.propDecidable

/-- Original labels occupied by an embedded core. -/
def coreLabels {k r : ℕ} {G : Graph k} (C : ConnectedCoreIn G r) :
    Finset (Fin k) :=
  Finset.univ.image C.labels

theorem card_coreLabels {k r : ℕ} {G : Graph k}
    (C : ConnectedCoreIn G r) :
    (coreLabels C).card = C.v := by
  rw [coreLabels, Finset.card_image_of_injective _ C.labels.injective]
  simp

theorem mem_coreLabels_iff {k r : ℕ} {G : Graph k}
    (C : ConnectedCoreIn G r) (x : Fin k) :
    x ∈ coreLabels C ↔ ∃ i : Fin C.v, C.labels i = x := by
  simp [coreLabels]

/-- The concrete ambient edge set occupied by the embedded core. -/
def embeddedCoreEdges {k r : ℕ} {G : Graph k}
    (C : ConnectedCoreIn G r) : Graph k :=
  G.filter fun e => (C.graph.map C.labels).Adj e.1.1 e.1.2

theorem embeddedCoreEdges_subset {k r : ℕ} {G : Graph k}
    (C : ConnectedCoreIn G r) : embeddedCoreEdges C ⊆ G :=
  Finset.filter_subset _ _

theorem simpleGraph_embeddedCoreEdges {k r : ℕ} {G : Graph k}
    (C : ConnectedCoreIn G r) :
    simpleGraph (embeddedCoreEdges C) = C.graph.map C.labels := by
  ext x y
  constructor
  · intro hxy
    change adj (embeddedCoreEdges C) x y at hxy
    rcases hxy with ⟨e, he, hends⟩
    have hcore := (Finset.mem_filter.mp he).2
    rcases hends with h | h
    · simpa [h.1, h.2] using! hcore
    · simpa [h.1, h.2] using! hcore.symm
  · intro hxy
    have hGxy : (simpleGraph G).Adj x y := C.subgraph hxy
    change adj G x y at hGxy
    rcases hGxy with ⟨e, heG, hends⟩
    refine ⟨e, Finset.mem_filter.mpr ⟨heG, ?_⟩, hends⟩
    rcases hends with h | h
    · simpa [h.1, h.2] using! hxy
    · simpa [h.1, h.2] using! hxy.symm

set_option maxHeartbeats 1000000 in
theorem card_embeddedCoreEdges {k r : ℕ} {G : Graph k}
    (C : ConnectedCoreIn G r) :
    (embeddedCoreEdges C).card = C.v + r := by
  calc
    (embeddedCoreEdges C).card =
        (simpleGraph (embeddedCoreEdges C)).edgeFinset.card :=
      (Erdos745.WrapUp.Proofs.Internal.W01_ENUM_Pruefer.simpleGraph_edgeFinset_card _).symm
    _ = Fintype.card (simpleGraph (embeddedCoreEdges C)).edgeSet :=
      SimpleGraph.edgeFinset_card
    _ = Fintype.card (C.graph.map C.labels).edgeSet := by
      exact Fintype.card_congr (Set.equivOfEq
        (congrArg SimpleGraph.edgeSet (simpleGraph_embeddedCoreEdges C)))
    _ = Fintype.card C.graph.edgeSet := by
      exact Fintype.card_congr
        ((Set.equivOfEq (SimpleGraph.edgeSet_map C.labels C.graph)).trans
          (Equiv.Set.image C.labels.sym2Map C.graph.edgeSet
            C.labels.sym2Map.injective).symm)
    _ = C.graph.edgeFinset.card := SimpleGraph.edgeFinset_card.symm
    _ = C.v + r := C.edge_card

theorem embeddedCoreEdge_endpoints {k r : ℕ} {G : Graph k}
    (C : ConnectedCoreIn G r) {e : Edge k}
    (he : e ∈ embeddedCoreEdges C) :
    e.1.1 ∈ coreLabels C ∧ e.1.2 ∈ coreLabels C := by
  have hadj : (C.graph.map C.labels).Adj e.1.1 e.1.2 :=
    (Finset.mem_filter.mp he).2
  rw [SimpleGraph.map_adj] at hadj
  rcases hadj with ⟨x, y, hxy, hx, hy⟩
  exact ⟨(mem_coreLabels_iff C _).2 ⟨x, hx⟩,
    (mem_coreLabels_iff C _).2 ⟨y, hy⟩⟩

/-- Edges outside the embedded exact-excess core. -/
def coreComplement {k r : ℕ} {G : Graph k}
    (C : ConnectedCoreIn G r) : Graph k :=
  G \ embeddedCoreEdges C

theorem card_coreComplement {k r : ℕ} {G : Graph k}
    (C : ConnectedCoreIn G r) (hcard : G.card = k + r) :
    (coreComplement C).card = k - C.v := by
  rw [coreComplement, Finset.card_sdiff_of_subset (embeddedCoreEdges_subset C),
    card_embeddedCoreEdges C, hcard]
  have hvk : C.v ≤ k := by
    simpa using! Fintype.card_le_of_embedding C.labels
  omega

private lemma reach_symm' {k : ℕ} {G : Graph k} {x y : Fin k} :
    reach G x y → reach G y x := by
  exact reach_symm

private lemma mem_componentOf_iff' {k : ℕ} {G : Graph k}
    {x y : Fin k} : y ∈ componentOf G x ↔ reach G x y := by
  simp [componentOf]

private lemma componentOf_self' {k : ℕ} (G : Graph k) (x : Fin k) :
    x ∈ componentOf G x :=
  (mem_componentOf_iff').2 Relation.ReflTransGen.refl

private lemma componentOf_mem_components' {k : ℕ} (G : Graph k)
    (x : Fin k) : componentOf G x ∈ components G := by
  simp [components]

private lemma componentOf_eq_of_reach' {k : ℕ} {G : Graph k}
    {x y : Fin k} (hxy : reach G x y) :
    componentOf G x = componentOf G y := by
  ext z
  rw [mem_componentOf_iff', mem_componentOf_iff']
  exact ⟨fun hxz => (reach_symm' hxy).trans hxz,
    fun hyz => hxy.trans hyz⟩

private lemma components_pairwiseDisjoint {k : ℕ} (G : Graph k) :
    ((components G : Finset (Finset (Fin k))) : Set (Finset (Fin k))).PairwiseDisjoint id := by
  intro S hS T hT hST
  have hSu : ∃ u : Fin k, componentOf G u = S := by
    simpa [components] using! hS
  have hTv : ∃ v : Fin k, componentOf G v = T := by
    simpa [components] using! hT
  obtain ⟨u, hu⟩ := hSu
  obtain ⟨v, hv⟩ := hTv
  apply Finset.disjoint_left.mpr
  intro x hxS hxT
  apply hST
  have hxu : x ∈ componentOf G u := by simpa [hu] using! hxS
  have hxv : x ∈ componentOf G v := by simpa [hv] using! hxT
  calc
    S = componentOf G u := hu.symm
    _ = componentOf G v := componentOf_eq_of_reach'
      (((mem_componentOf_iff').1 hxu).trans
        (reach_symm' ((mem_componentOf_iff').1 hxv)))
    _ = T := hv

private lemma components_biUnion_eq_univ {k : ℕ} (G : Graph k) :
    (components G).biUnion id = (Finset.univ : Finset (Fin k)) := by
  ext x
  simp only [Finset.mem_biUnion, Finset.mem_univ, iff_true]
  exact ⟨componentOf G x, componentOf_mem_components' G x,
    componentOf_self' G x⟩

private def componentEdges {k : ℕ} (G : Graph k)
    (S : Finset (Fin k)) : Graph k :=
  G.filter fun e => e.1.1 ∈ S ∧ e.1.2 ∈ S

private lemma componentEdges_pairwiseDisjoint {k : ℕ} (G : Graph k) :
    ((components G : Finset (Finset (Fin k))) : Set (Finset (Fin k))).PairwiseDisjoint
      (componentEdges G) := by
  intro S hS T hT hST
  have hdis := components_pairwiseDisjoint G hS hT hST
  apply Finset.disjoint_left.mpr
  intro e heS heT
  exact Finset.disjoint_left.mp hdis
    (Finset.mem_filter.mp heS).2.1 (Finset.mem_filter.mp heT).2.1

private lemma componentEdges_biUnion_eq {k : ℕ} (G : Graph k) :
    (components G).biUnion (componentEdges G) = G := by
  ext e
  simp only [Finset.mem_biUnion, componentEdges, Finset.mem_filter]
  constructor
  · rintro ⟨S, -, he, -⟩
    exact he
  · intro he
    let S := componentOf G e.1.1
    have h1 : e.1.1 ∈ S := componentOf_self' G e.1.1
    have h2 : e.1.2 ∈ S := (mem_componentOf_iff').2
      (Relation.ReflTransGen.single
        ⟨e, he, Or.inl ⟨rfl, rfl⟩⟩)
    exact ⟨S, componentOf_mem_components' G e.1.1, he, h1, h2⟩

private lemma sum_component_cards {k : ℕ} (G : Graph k) :
    ∑ S ∈ components G, S.card = k := by
  have h := congrArg Finset.card (components_biUnion_eq_univ G)
  rw [Finset.card_biUnion (components_pairwiseDisjoint G)] at h
  simpa using! h

private lemma sum_component_edges {k : ℕ} (G : Graph k) :
    ∑ S ∈ components G, edgesInside G S = G.card := by
  have h := congrArg Finset.card (componentEdges_biUnion_eq G)
  rw [Finset.card_biUnion (componentEdges_pairwiseDisjoint G)] at h
  simpa [componentEdges, edgesInside] using! h

private def componentRoots {k : ℕ} (roots S : Finset (Fin k)) :
    Finset (Fin k) := S ∩ roots

private lemma componentRoots_pairwiseDisjoint {k : ℕ} (G : Graph k)
    (roots : Finset (Fin k)) :
    ((components G : Finset (Finset (Fin k))) : Set (Finset (Fin k))).PairwiseDisjoint
      (componentRoots roots) := by
  intro S hS T hT hST
  have hdis := components_pairwiseDisjoint G hS hT hST
  apply Finset.disjoint_left.mpr
  intro x hxS hxT
  exact Finset.disjoint_left.mp hdis
    (Finset.mem_inter.mp hxS).1 (Finset.mem_inter.mp hxT).1

private lemma componentRoots_biUnion_eq {k : ℕ} (G : Graph k)
    (roots : Finset (Fin k)) :
    (components G).biUnion (componentRoots roots) = roots := by
  ext x
  simp only [Finset.mem_biUnion, componentRoots, Finset.mem_inter]
  constructor
  · rintro ⟨S, -, -, hx⟩
    exact hx
  · intro hx
    exact ⟨componentOf G x, componentOf_mem_components' G x,
      componentOf_self' G x, hx⟩

private lemma sum_component_root_cards {k : ℕ} (G : Graph k)
    (roots : Finset (Fin k)) :
    ∑ S ∈ components G, (S ∩ roots).card = roots.card := by
  have h := congrArg Finset.card (componentRoots_biUnion_eq G roots)
  rw [Finset.card_biUnion (componentRoots_pairwiseDisjoint G roots)] at h
  simpa [componentRoots] using! h

private lemma component_card_le_edges_add_one {k : ℕ} (G : Graph k)
    (S : Finset (Fin k)) (hS : S ∈ components G) :
    S.card ≤ edgesInside G S + 1 := by
  simp only [components, Finset.mem_image] at hS
  rcases hS with ⟨root, -, rfl⟩
  let c := (simpleGraph G).connectedComponentMk root
  have hc (x : Fin k) : x ∈ c.supp ↔ x ∈ componentOf G root := by
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff,
      SimpleGraph.ConnectedComponent.eq, simpleGraph_reachable_iff,
      mem_componentOf_iff']
    exact ⟨reach_symm', reach_symm'⟩
  let inside : Graph k :=
    G.filter fun e => e.1.1 ∈ componentOf G root ∧
      e.1.2 ∈ componentOf G root
  have hedgecard : inside.card = c.toSimpleGraph.edgeFinset.card := by
    apply Finset.card_bij
      (fun e he =>
        s(⟨e.1.1, (hc e.1.1).2 (Finset.mem_filter.mp he).2.1⟩,
          ⟨e.1.2, (hc e.1.2).2 (Finset.mem_filter.mp he).2.2⟩))
    · intro e he
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
        SimpleGraph.ConnectedComponent.toSimpleGraph_adj, simpleGraph_adj]
      exact ⟨e, (Finset.mem_filter.mp he).1, Or.inl ⟨rfl, rfl⟩⟩
    · intro e₁ he₁ e₂ he₂ h
      apply Subtype.ext
      apply Prod.ext
      · rcases Sym2.eq_iff.mp h with h | h
        · exact congrArg Subtype.val h.1
        · have hlt : e₂.1.2 < e₂.1.1 := by
            calc
              e₂.1.2 = e₁.1.1 := (congrArg Subtype.val h.1).symm
              _ < e₁.1.2 := e₁.2
              _ = e₂.1.1 := congrArg Subtype.val h.2
          exact False.elim (lt_asymm e₂.2 hlt)
      · rcases Sym2.eq_iff.mp h with h | h
        · exact congrArg Subtype.val h.2
        · have hlt : e₂.1.2 < e₂.1.1 := by
            calc
              e₂.1.2 = e₁.1.1 := (congrArg Subtype.val h.1).symm
              _ < e₁.1.2 := e₁.2
              _ = e₂.1.1 := congrArg Subtype.val h.2
          exact False.elim (lt_asymm e₂.2 hlt)
    · intro b hb
      induction b using Sym2.inductionOn with
      | _ u v =>
          have hadj : (simpleGraph G).Adj u.1 v.1 := by
            rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at hb
            exact (SimpleGraph.ConnectedComponent.toSimpleGraph_adj c u.2 v.2).mp hb
          change adj G u.1 v.1 at hadj
          rcases hadj with ⟨e, he, hends⟩
          have hins : e ∈ inside := by
            apply Finset.mem_filter.mpr
            refine ⟨he, ?_⟩
            rcases hends with h | h
            · exact ⟨(hc e.1.1).1 (h.1.symm ▸ u.2),
                (hc e.1.2).1 (h.2.symm ▸ v.2)⟩
            · exact ⟨(hc e.1.1).1 (h.1.symm ▸ v.2),
                (hc e.1.2).1 (h.2.symm ▸ u.2)⟩
          refine ⟨e, hins, ?_⟩
          rcases hends with h | h
          · exact Sym2.eq_iff.mpr (Or.inl ⟨Subtype.ext h.1, Subtype.ext h.2⟩)
          · exact Sym2.eq_iff.mpr (Or.inr ⟨Subtype.ext h.1, Subtype.ext h.2⟩)
  have hcardc : Fintype.card c = (componentOf G root).card := by
    calc
      Fintype.card c = Fintype.card ↑(componentOf G root) :=
        Fintype.card_congr
          { toFun := fun x => ⟨x.1, (hc x.1).1 x.2⟩
            invFun := fun x => ⟨x.1, (hc x.1).2 x.2⟩
            left_inv := fun x => Subtype.ext rfl
            right_inv := fun x => Subtype.ext rfl }
      _ = (componentOf G root).card := Fintype.card_coe _
  have hbound := c.connected_toSimpleGraph.card_vert_le_card_edgeSet_add_one
  rw [Nat.card_eq_fintype_card, hcardc, Nat.card_eq_fintype_card,
    ← SimpleGraph.edgeFinset_card, ← hedgecard] at hbound
  simpa [inside, edgesInside] using! hbound

private lemma component_has_coreLabel {k r : ℕ} {G : Graph k}
    (C : ConnectedCoreIn G r)
    (hconn : ∀ x y : Fin k, reach G x y)
    (S : Finset (Fin k)) (hS : S ∈ components (coreComplement C)) :
    0 < (S ∩ coreLabels C).card := by
  simp only [components, Finset.mem_image] at hS
  rcases hS with ⟨x, -, rfl⟩
  by_contra hnot
  have hzero : (componentOf (coreComplement C) x ∩ coreLabels C).card = 0 :=
    Nat.eq_zero_of_not_pos hnot
  have hv : 0 < C.v := by
    simpa using! (Fintype.card_pos_iff.mpr C.connected.nonempty)
  let i : Fin C.v := ⟨0, hv⟩
  let root : Fin k := C.labels i
  have hroot : root ∈ coreLabels C :=
    (mem_coreLabels_iff C root).2 ⟨i, rfl⟩
  have hclosed : ∀ {a b : Fin k}, a ∈ componentOf (coreComplement C) x →
      adj G a b → b ∈ componentOf (coreComplement C) x := by
    intro a b ha hab
    rcases hab with ⟨e, heG, hends⟩
    have ha_not_root : a ∉ coreLabels C := by
      intro haroot
      have hinter : a ∈ componentOf (coreComplement C) x ∩ coreLabels C :=
        Finset.mem_inter.mpr ⟨ha, haroot⟩
      have hpos := Finset.card_pos.mpr ⟨a, hinter⟩
      omega
    have hnotcore : e ∉ embeddedCoreEdges C := by
      intro hecore
      have hend := embeddedCoreEdge_endpoints C hecore
      rcases hends with h | h
      · exact ha_not_root (h.1 ▸ hend.1)
      · exact ha_not_root (h.2 ▸ hend.2)
    have heF : e ∈ coreComplement C :=
      Finset.mem_sdiff.mpr ⟨heG, hnotcore⟩
    have habF : adj (coreComplement C) a b := ⟨e, heF, hends⟩
    exact (mem_componentOf_iff').2
      (((mem_componentOf_iff').1 ha).trans
        (Relation.ReflTransGen.single habF))
  have hreach : reach G x root := hconn x root
  have hclosureReach : ∀ y : Fin k, reach G x y →
      y ∈ componentOf (coreComplement C) x := by
    intro y hy
    induction hy with
    | refl => exact componentOf_self' _ x
    | tail hxy hyz ih => exact hclosed ih hyz
  have hrootcomp := hclosureReach root hreach
  have hpos := Finset.card_pos.mpr
    ⟨root, Finset.mem_inter.mpr ⟨hrootcomp, hroot⟩⟩
  omega

/-- The literal complement of any connected embedded exact-excess core is a
rooted forest with roots at precisely the embedded core labels. -/
theorem coreComplement_isRootedForest {k r : ℕ} {G : Graph k}
    (C : ConnectedCoreIn G r)
    (hconn : ∀ x y : Fin k, reach G x y)
    (hcard : G.card = k + r) :
    ∀ S ∈ components (coreComplement C),
      isTree (coreComplement C) S ∧ (S ∩ coreLabels C).card = 1 := by
  let F := coreComplement C
  let roots := coreLabels C
  have hFcard : F.card = k - C.v := card_coreComplement C hcard
  have hrootcard : roots.card = C.v := card_coreLabels C
  have hrootpos : ∀ S ∈ components F, 0 < (S ∩ roots).card := by
    intro S hS
    exact component_has_coreLabel C hconn S hS
  have hcomponent_le : (components F).card ≤ roots.card := by
    have hsum := sum_component_root_cards F roots
    calc
      (components F).card = ∑ S ∈ components F, 1 := by simp
      _ ≤ ∑ S ∈ components F, (S ∩ roots).card := by
        gcongr with S hS
        exact hrootpos S hS
      _ = roots.card := hsum
  have hvertex_le : k ≤ F.card + (components F).card := by
    calc
      k = ∑ S ∈ components F, S.card := (sum_component_cards F).symm
      _ ≤
          ∑ S ∈ components F, (edgesInside F S + 1) := by
        gcongr with S hS
        exact component_card_le_edges_add_one F S hS
      _ = (∑ S ∈ components F, edgesInside F S) +
          (components F).card := by
        rw [Finset.sum_add_distrib]
        simp
      _ = F.card + (components F).card := by rw [sum_component_edges F]
  have hvk : C.v ≤ k := by
    simpa using! Fintype.card_le_of_embedding C.labels
  have hcomponent_eq : (components F).card = C.v := by
    have hlow : C.v ≤ (components F).card := by
      rw [hFcard] at hvertex_le
      omega
    have hupp : (components F).card ≤ C.v := by
      simpa [hrootcard] using! hcomponent_le
    omega
  have hroot_one : ∀ S ∈ components F, (S ∩ roots).card = 1 := by
    have hsum := sum_component_root_cards F roots
    have hsplit :
        ∑ S ∈ components F, (S ∩ roots).card =
          (∑ S ∈ components F, ((S ∩ roots).card - 1)) +
            (components F).card := by
      calc
        ∑ S ∈ components F, (S ∩ roots).card =
            ∑ S ∈ components F, (((S ∩ roots).card - 1) + 1) := by
          apply Finset.sum_congr rfl
          intro S hS
          have hp := hrootpos S hS
          omega
        _ = _ := by rw [Finset.sum_add_distrib]; simp
    have hzero : ∑ S ∈ components F, ((S ∩ roots).card - 1) = 0 := by
      have hsum' : ∑ S ∈ components F, (S ∩ roots).card = C.v :=
        hsum.trans hrootcard
      rw [hsum', hcomponent_eq] at hsplit
      omega
    intro S hS
    have hz := (Finset.sum_eq_zero_iff.mp hzero) S hS
    have hp := hrootpos S hS
    omega
  have hedge_eq : ∀ S ∈ components F,
      edgesInside F S + 1 = S.card := by
    have hsumEdges := sum_component_edges F
    have hsumVerts := sum_component_cards F
    have htotal :
        ∑ S ∈ components F, (edgesInside F S + 1) =
          ∑ S ∈ components F, S.card := by
      rw [Finset.sum_add_distrib, hsumEdges, hsumVerts]
      simp [hFcard, hcomponent_eq]
      omega
    have hslack :
        ∑ S ∈ components F, (edgesInside F S + 1 - S.card) = 0 := by
      have hrewrite :
          ∑ S ∈ components F, (edgesInside F S + 1) =
            (∑ S ∈ components F,
              (edgesInside F S + 1 - S.card)) +
              ∑ S ∈ components F, S.card := by
        calc
          ∑ S ∈ components F, (edgesInside F S + 1) =
              ∑ S ∈ components F,
                ((edgesInside F S + 1 - S.card) + S.card) := by
            apply Finset.sum_congr rfl
            intro S hS
            have hle := component_card_le_edges_add_one F S hS
            omega
          _ = _ := by rw [Finset.sum_add_distrib]
      omega
    intro S hS
    have hz := (Finset.sum_eq_zero_iff.mp hslack) S hS
    have hle := component_card_le_edges_add_one F S hS
    omega
  intro S hS
  exact ⟨⟨hS, hedge_eq S hS⟩, hroot_one S hS⟩

/- Positive-excess connected graphs admit an exact embedded core whose edge
complement is already the semantic rooted forest needed by `tau`. -/
end Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_CoreForest
