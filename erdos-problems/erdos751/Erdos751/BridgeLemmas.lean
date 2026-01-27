import Erdos751.Basic

namespace Erdos751

open Classical

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

namespace BV

omit [Fintype V] [DecidableRel G.Adj] in
/-- Any vertex in a bridge component lies outside the cycle vertex-set. -/
theorem mem_bridge_imp_not_mem_cycle
    (C : Cycle (G := G)) (K : Bridge (G := G) C) {v : V} :
    v ∈ bridgeSet (G := G) C K → v ∉ C.vSet (G := G) := by
  classical
  intro hv
  have : v ∈ (C.vSet (G := G))ᶜ := (bridgeSet_subset_compl_vSet (G := G) C K) hv
  simpa [Set.mem_compl_iff] using this

omit [Fintype V] [DecidableRel G.Adj] in
/-- Component uniqueness: if a vertex lies in both components, the components are equal. -/
theorem bridge_eq_of_mem_mem
    (C : Cycle (G := G))
    {K1 K2 : Bridge (G := G) C} {v : V} :
    v ∈ bridgeSet (G := G) C K1 → v ∈ bridgeSet (G := G) C K2 → K1 = K2 := by
  classical
  intro hv1 hv2
  have hnot : ¬ Disjoint (K1 : Set V) (K2 : Set V) := by
    refine Set.not_disjoint_iff.mpr ?_
    refine ⟨v, ?_, ?_⟩
    · simpa [bridgeSet] using hv1
    · simpa [bridgeSet] using hv2
  exact
    (SimpleGraph.ComponentCompl.pairwise_disjoint (G := G) (K := C.vSet (G := G))).eq hnot

omit [Fintype V] [DecidableRel G.Adj] in
/-- If components are different, then their carrier sets are disjoint. -/
theorem disjoint_bridge_of_ne
    (C : Cycle (G := G)) {K1 K2 : Bridge (G := G) C} :
    K1 ≠ K2 → Disjoint (bridgeSet (G := G) C K1) (bridgeSet (G := G) C K2) := by
  classical
  intro hne
  refine Set.disjoint_left.2 ?_
  intro v hv1 hv2
  have : K1 = K2 :=
    bridge_eq_of_mem_mem (G := G) C (K1 := K1) (K2 := K2) (v := v) hv1 hv2
  exact hne this

omit [Fintype V] [DecidableRel G.Adj] in
/-- Any two vertices in a bridge component are joined by a path inside the bridge. -/
theorem exists_path_in_bridge
    (C : Cycle (G := G)) (K : Bridge (G := G) C) {u v : V}
    (hu : u ∈ bridgeSet (G := G) C K) (hv : v ∈ bridgeSet (G := G) C K) :
    ∃ p : G.Walk u v, p.IsPath ∧
      (∀ t : V, t ∈ p.support → t ∈ bridgeSet (G := G) C K) := by
  classical
  -- unwrap membership in the component
  have hu' : u ∈ (K : Set V) := by simpa [bridgeSet] using hu
  have hv' : v ∈ (K : Set V) := by simpa [bridgeSet] using hv
  rcases (SimpleGraph.ComponentCompl.mem_supp_iff (G := G) (K := C.vSet (G := G))
      (C := K) (v := u)).1 hu' with ⟨huK, hcompu⟩
  rcases (SimpleGraph.ComponentCompl.mem_supp_iff (G := G) (K := C.vSet (G := G))
      (C := K) (v := v)).1 hv' with ⟨hvK, hcompv⟩
  -- reachable in the induced complement graph
  have hcomp :
      (G.componentComplMk (K := C.vSet (G := G)) huK) =
        (G.componentComplMk (K := C.vSet (G := G)) hvK) := by
    simp [hcompu, hcompv]
  have hreach :
      (G.induce (C.vSet (G := G))ᶜ).Reachable ⟨u, huK⟩ ⟨v, hvK⟩ := by
    -- `componentComplMk` is `connectedComponentMk` in the induced graph
    simpa [SimpleGraph.componentComplMk] using
      (SimpleGraph.ConnectedComponent.eq
        (G := G.induce (C.vSet (G := G))ᶜ)
        (v := ⟨u, huK⟩) (w := ⟨v, hvK⟩)).1 hcomp
  rcases hreach with ⟨p'⟩
  -- map the walk back to `G`
  let f := (SimpleGraph.Embedding.induce (G := G) (s := (C.vSet (G := G))ᶜ)).toHom
  let p : G.Walk u v := p'.map f
  have hsubset : ∀ t : V, t ∈ p.support → t ∈ bridgeSet (G := G) C K := by
    intro t ht
    -- pull back to a vertex on the walk in the induced graph
    have ht_map : t ∈ p'.support.map f := by
      simpa [p, SimpleGraph.Walk.support_map] using ht
    have ht_ex : ∃ t' : {v // v ∉ C.vSet (G := G)},
        t' ∈ p'.support ∧ f t' = t := by
      simpa using (List.mem_map.1 ht_map)
    rcases ht_ex with ⟨t', ht_mem, ht_eq⟩
    subst ht_eq
    -- show this vertex lies in the component `K`
    have ht_reach :
        (G.induce (C.vSet (G := G))ᶜ).Reachable ⟨u, huK⟩ t' := by
      -- use the prefix walk up to `t'`
      -- take the prefix walk from the start to `t'`
      refine ⟨p'.takeUntil t' ht_mem⟩
    have ht_comp :
        G.componentComplMk (K := C.vSet (G := G)) (t'.property) = K := by
      -- convert reachability to component equality
      have :=
        (SimpleGraph.ConnectedComponent.eq
          (G := G.induce (C.vSet (G := G))ᶜ)
          (v := ⟨u, huK⟩) (w := t')).2 ht_reach
      -- unfold `componentComplMk`
      -- `this` gives `K = componentComplMk _`; flip it.
      simpa [SimpleGraph.componentComplMk, hcompu] using this.symm
    -- conclude membership in the bridge set
    exact (SimpleGraph.ComponentCompl.mem_supp_iff (G := G) (K := C.vSet (G := G))
      (C := K) (v := t')).2 ⟨t'.property, ht_comp⟩
  -- turn the walk into a path without leaving the bridge
  refine ⟨p.toPath, ?_, ?_⟩
  · exact (SimpleGraph.Path.isPath _)
  · intro t ht
    apply hsubset t
    exact (SimpleGraph.Walk.support_toPath_subset (G := G) p) ht

omit [Fintype V] [DecidableRel G.Adj] in
/-- From two attachments, build an x-y path whose internal vertices lie in the bridge. -/
theorem exists_path_between_attach
    (C : Cycle (G := G)) (K : Bridge (G := G) C) {x y : V}
    (hx : x ∈ attachSet (G := G) C K) (hy : y ∈ attachSet (G := G) C K) (hxy : x ≠ y) :
    ∃ p : G.Walk x y, p.IsPath ∧
      (∀ v : V, v ∈ p.support → v = x ∨ v = y ∨ v ∈ bridgeSet (G := G) C K) ∧
      ∃ w : V, w ∈ bridgeSet (G := G) C K ∧ s(x, w) ∈ p.edges := by
  classical
  rcases hx with ⟨hxC, ⟨wx, hwxK, hAdjx⟩⟩
  rcases hy with ⟨hyC, ⟨wy, hwyK, hAdjy⟩⟩
  obtain ⟨pK, hpK_path, hpK_supp⟩ :=
    exists_path_in_bridge (G := G) (C := C) (K := K) hwxK hwyK
  have hx_not_bridge : x ∉ bridgeSet (G := G) C K := by
    intro hxB
    exact (mem_bridge_imp_not_mem_cycle (G := G) C K hxB) hxC
  have hy_not_bridge : y ∉ bridgeSet (G := G) C K := by
    intro hyB
    exact (mem_bridge_imp_not_mem_cycle (G := G) C K hyB) hyC
  have hx_not_pK : x ∉ pK.support := by
    intro hxmem
    exact hx_not_bridge (hpK_supp x hxmem)
  have hy_not_pK : y ∉ pK.support := by
    intro hymem
    exact hy_not_bridge (hpK_supp y hymem)
  let p1 : G.Walk wx y := pK.concat hAdjy.symm
  have hp1_path : p1.IsPath := by
    exact SimpleGraph.Walk.IsPath.concat hpK_path hy_not_pK hAdjy.symm
  have hx_not_p1 : x ∉ p1.support := by
    intro hxmem
    have hxmem' : x ∈ pK.support ∨ x = y := by
      have : x ∈ pK.support ++ [y] := by
        simpa [p1, SimpleGraph.Walk.support_concat, List.concat_eq_append] using hxmem
      rcases List.mem_append.mp this with hxmem'' | hxmem''
      · exact Or.inl hxmem''
      · exact Or.inr (by simpa using hxmem'')
    cases hxmem' with
    | inl hxmem'' => exact hx_not_pK hxmem''
    | inr hxy' => exact hxy hxy'
  let p : G.Walk x y := SimpleGraph.Walk.cons hAdjx p1
  have hp_path : p.IsPath := by
    exact SimpleGraph.Walk.IsPath.cons hp1_path hx_not_p1
  have hp_supp : ∀ v : V, v ∈ p.support → v = x ∨ v = y ∨ v ∈ bridgeSet (G := G) C K := by
    intro v hv
    have hv' : v = x ∨ v ∈ p1.support := by
      simpa [p, SimpleGraph.Walk.support_cons] using hv
    cases hv' with
    | inl hvx => exact Or.inl hvx
    | inr hvp1 =>
        have hvp1' : v ∈ pK.support ++ [y] := by
          simpa [p1, SimpleGraph.Walk.support_concat, List.concat_eq_append] using hvp1
        rcases List.mem_append.mp hvp1' with hvpK | hvy
        · exact Or.inr (Or.inr (hpK_supp v hvpK))
        · exact Or.inr (Or.inl (by simpa using hvy))
  -- the first edge is x-wx, with wx in the bridge
  have hEdge : s(x, wx) ∈ p.edges := by
    simp [p]
  exact ⟨p, hp_path, hp_supp, ⟨wx, hwxK, hEdge⟩⟩

end BV
end Erdos751
