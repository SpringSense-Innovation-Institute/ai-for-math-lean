import Erdos751.BV
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

namespace Erdos751

open Classical

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

namespace Critical

/-
  IMPORTANT ENGINEERING NOTE

  We must *fix* the Fintype instance on the subtype `{v // v ∈ S}`.
  Otherwise, `hδ3` and `hcard4` can be stored under one instance
  (e.g. `Finset.Subtype.fintype S`) while `Main` expects another
  (e.g. `Subtype.fintype ...`), and definitional equality will fail.

  Therefore: use `Finset.Subtype.fintype S` everywhere for the witness subtype.
-/

/-- Canonical (locked) `Fintype` instance on `{v // v ∈ S}`. -/
abbrev instSub (S : Finset V) : Fintype {v : V // v ∈ S} :=
  Finset.Subtype.fintype S

structure Witness where
  S : Finset V
  h2 : BV.VertexTwoConnected (G := G.induce (fun v : V => v ∈ S))

  -- Store hypotheses under the *locked* subtype Fintype instance.
  hδ3 :
    @BV.MinDegreeGE3 {v : V // v ∈ S}
      (instSub (V := V) S)
      (G.induce (fun v : V => v ∈ S))
      (by infer_instance)

  hcard4 :
    @Fintype.card {v : V // v ∈ S} (instSub (V := V) S) ≥ 4

/-- Induced graph carried by a witness (abbrev => definitional equality behaves). -/
abbrev H (W : Witness (G := G)) : SimpleGraph {v : V // v ∈ W.S} :=
  G.induce (fun v : V => v ∈ W.S)

set_option maxHeartbeats 1500000 in
noncomputable def exists_witness_of_chromaticNumber_ge_4
    (hχ : (4 : ℕ∞) ≤ G.chromaticNumber) :
    Witness (G := G) := by
  classical
  -- Minimal (by cardinality) induced subgraph not 3-colorable.
  let bad : Finset V → Prop :=
    fun S => ¬ (G.induce (fun v : V => v ∈ S)).Colorable 3

  have hbad_univ : bad (Finset.univ : Finset V) := by
    intro hcol
    -- convert to colorability of the full graph
    have hcol' : (G.induce (Set.univ : Set V)).Colorable 3 := by
      -- `Set.univ` and `Finset.univ` define the same predicate
      have hpred :
          (Set.univ : Set V) = (fun v : V => v ∈ (Finset.univ : Finset V)) := by
        funext v
        apply propext
        constructor
        · intro _; exact Finset.mem_univ v
        · intro _; exact trivial
      rw [hpred]
      exact hcol
    have hcolG : G.Colorable 3 :=
      SimpleGraph.Colorable.of_hom
        (f := (SimpleGraph.induceUnivIso G).symm.toHom) hcol'
    have hle : G.chromaticNumber ≤ (3 : ℕ) :=
      (SimpleGraph.chromaticNumber_le_iff_colorable (G := G) (n := 3)).2 hcolG
    have : (4 : ℕ∞) ≤ (3 : ℕ) := hχ.trans hle
    exact (by norm_num : ¬ (4 : ℕ∞) ≤ (3 : ℕ)) this

  let cand : Finset (Finset V) :=
    (Finset.univ : Finset V).powerset.filter bad
  have hnonempty : cand.Nonempty := by
    refine ⟨Finset.univ, ?_⟩
    refine (Finset.mem_filter).2 ?_
    refine ⟨?_, hbad_univ⟩
    simp

  let S : Finset V :=
    Classical.choose (Finset.exists_min_image cand (fun S => S.card) hnonempty)
  have hS_spec :=
    Classical.choose_spec (Finset.exists_min_image cand (fun S => S.card) hnonempty)
  have hS_cand : S ∈ cand := hS_spec.1
  have hS_min : ∀ S' ∈ cand, S.card ≤ S'.card := hS_spec.2
  have hS_bad : bad S := (Finset.mem_filter.mp hS_cand).2

  have hcolor_of_ssubset :
      ∀ {T : Finset V}, T ⊂ S → (G.induce (fun v : V => v ∈ T)).Colorable 3 := by
    intro T hTS
    by_contra hTbad
    have hTmem : T ∈ cand := by
      refine (Finset.mem_filter).2 ?_
      refine ⟨?_, hTbad⟩
      have hsubset : T ⊆ (Finset.univ : Finset V) := by
        intro x hx; exact Finset.mem_univ x
      exact (Finset.mem_powerset.2 hsubset)
    have hcard_le : S.card ≤ T.card := hS_min _ hTmem
    have hcard_lt : T.card < S.card := Finset.card_lt_card hTS
    exact (Nat.lt_irrefl _ (lt_of_lt_of_le hcard_lt hcard_le))

  let H : SimpleGraph {v : V // v ∈ S} :=
    G.induce (fun v : V => v ∈ S)

  -- |S| ≥ 4, otherwise 3-colorable by monotonicity.
  have hcard4 :
      (letI : Fintype {v : V // v ∈ S} := instSub (V := V) S
       Fintype.card {v : V // v ∈ S} ≥ 4) := by
    classical
    by_contra hcard4'
    letI : Fintype {v : V // v ∈ S} := instSub (V := V) S
    have hcard_lt4 : Fintype.card {v : V // v ∈ S} < 4 :=
      Nat.lt_of_not_ge hcard4'
    have hcard_le3 : Fintype.card {v : V // v ∈ S} ≤ 3 := by
      have h : Fintype.card {v : V // v ∈ S} < 3 + 1 := by
        simpa using hcard_lt4
      exact Nat.lt_succ_iff.mp h
    have hcol_card :
        (G.induce (fun v : V => v ∈ S)).Colorable
          (Fintype.card {v : V // v ∈ S}) := by
      simpa using (SimpleGraph.selfColoring (G := G.induce (fun v : V => v ∈ S))).colorable
    have hcolS :
        (G.induce (fun v : V => v ∈ S)).Colorable 3 :=
      SimpleGraph.Colorable.mono hcard_le3 hcol_card
    exact hS_bad hcolS

  -- Minimum degree ≥ 3 in the minimal counterexample.
  have hδ3 :
      (letI : Fintype {v : V // v ∈ S} := instSub (V := V) S
       BV.MinDegreeGE3 (G := H)) := by
    classical
    intro v
    by_contra hdeg
    have hdeg' : H.degree v ≤ 2 := by
      have hlt : H.degree v < 3 := Nat.lt_of_not_ge hdeg
      exact Nat.lt_succ_iff.mp hlt
    have hcol_erase :
        (G.induce (fun u : V => u ∈ S.erase v.1)).Colorable 3 := by
      have hss : S.erase v.1 ⊂ S := Finset.erase_ssubset v.property
      exact hcolor_of_ssubset hss
    rcases hcol_erase with ⟨C⟩
    let neigh : Finset {v : V // v ∈ S} := H.neighborFinset v
    let colors : Finset (Fin 3) :=
      neigh.attach.image (fun u =>
        C ⟨u.1.1, by
          have hAdj : H.Adj v u.1 :=
            (SimpleGraph.mem_neighborFinset (G := H) (v := v) (w := u.1)).1 u.2
          have hvu : v ≠ u.1 := H.ne_of_adj hAdj
          have huv : u.1 ≠ v := by simpa [ne_comm] using hvu
          have huv' : u.1.1 ≠ v.1 := by
            intro h
            apply huv
            apply Subtype.ext
            simp [h]
          exact Finset.mem_erase.mpr ⟨huv', u.1.property⟩
        ⟩)
    have hcolors_card : colors.card ≤ 2 := by
      have hneigh_card : neigh.card ≤ 2 := by
        simpa [SimpleGraph.card_neighborFinset_eq_degree] using hdeg'
      have hle : colors.card ≤ neigh.attach.card := Finset.card_image_le
      have hneigh_attach : neigh.attach.card ≤ 2 := by
        simpa [Finset.card_attach] using hneigh_card
      exact hle.trans hneigh_attach
    have hlt_colors :
        colors.card < (Finset.univ : Finset (Fin 3)).card := by
      have : colors.card < 3 := Nat.lt_of_le_of_lt hcolors_card (by decide)
      simpa using this
    obtain ⟨c0, _, hc0_not⟩ :=
      Finset.exists_mem_notMem_of_card_lt_card hlt_colors
    let color : {v : V // v ∈ S} → Fin 3 :=
      fun u =>
        if h : u.1 = v.1 then c0
        else
          C ⟨u.1, by
            exact (Finset.mem_erase.mpr ⟨h, u.property⟩)⟩
    have hvalid : ∀ {u w : {v : V // v ∈ S}}, H.Adj u w → color u ≠ color w := by
      intro u w hAdj
      by_cases hu : u.1 = v.1
      · -- u = v
        have hw : w.1 ≠ v.1 := by
          intro h
          have : u = w := by
            apply Subtype.ext
            simp [hu, h]
          exact (H.ne_of_adj hAdj this).elim
        have hw_mem : w ∈ neigh := by
          have huv : u = v := by
            apply Subtype.ext
            exact hu
          have : H.Adj v w := by
            simpa [huv] using hAdj
          simpa [neigh] using
            (SimpleGraph.mem_neighborFinset (G := H) (v := v) (w := w)).2 this
        have hw_color_mem : color w ∈ colors := by
          refine Finset.mem_image.mpr ?_
          refine ⟨⟨w, hw_mem⟩, by simp, ?_⟩
          simp [color, hw]
        intro hcw
        have hcu : color u = c0 := by
          simp [color, hu]
        have hcw' : color w = c0 := by
          simpa [hcu] using hcw.symm
        have : c0 ∈ colors := by simpa [hcw'] using hw_color_mem
        exact (hc0_not this).elim
      · by_cases hw : w.1 = v.1
        · -- w = v, symmetric
          have hu_mem : u ∈ neigh := by
            have : H.Adj v u := by
              have hwu : w = v := by
                apply Subtype.ext
                exact hw
              simpa [hwu] using hAdj.symm
            simpa [neigh] using
              (SimpleGraph.mem_neighborFinset (G := H) (v := v) (w := u)).2 this
          have hu_color_mem : color u ∈ colors := by
            refine Finset.mem_image.mpr ?_
            refine ⟨⟨u, hu_mem⟩, by simp, ?_⟩
            simp [color, hu]
          intro hcu
          have hcv : color w = c0 := by
            simp [color, hw]
          have hcu' : color u = c0 := by
            simpa [hcv] using hcu
          have : c0 ∈ colors := by simpa [hcu'] using hu_color_mem
          exact (hc0_not this).elim
        · -- both in erased graph
          have hAdj' :
              (G.induce (fun u : V => u ∈ S.erase v.1)).Adj
                ⟨u.1, by exact (Finset.mem_erase.mpr ⟨hu, u.property⟩)⟩
                ⟨w.1, by exact (Finset.mem_erase.mpr ⟨hw, w.property⟩)⟩ := by
            simpa using hAdj
          have hneq := C.valid hAdj'
          simpa [color, hu, hw] using hneq
    have hcolH : H.Colorable 3 := ⟨SimpleGraph.Coloring.mk color hvalid⟩
    exact hS_bad hcolH

  -- Connectivity and vertex-deletion connectivity.
  have h2 : BV.VertexTwoConnected (G := H) := by
    classical
    -- H is connected.
    have hH_conn : H.Connected := by
      by_contra hnot
      letI : Fintype {v : V // v ∈ S} := instSub (V := V) S
      have hnonempty : Nonempty {v : V // v ∈ S} := by
        have hpos : 0 < Fintype.card {v : V // v ∈ S} :=
          lt_of_lt_of_le (by decide : (0 : ℕ) < 4) (by simpa using hcard4)
        exact Fintype.card_pos_iff.mp hpos
      have hcol_all : ∀ c : H.ConnectedComponent, (c.toSimpleGraph).Colorable 3 := by
        intro c
        have hne : (c.supp : Set {v : V // v ∈ S}) ≠ Set.univ := by
          intro hsu
          have hpre : H.Preconnected := by
            intro a b
            have ha : a ∈ c.supp := by simp [hsu]
            have hb : b ∈ c.supp := by simp [hsu]
            exact c.reachable_of_mem_supp ha hb
          haveI := hnonempty
          exact hnot ⟨hpre⟩
        obtain ⟨w, hw⟩ := (Set.ne_univ_iff_exists_notMem (c.supp)).1 hne
        let T : Finset V := c.supp.toFinset.image Subtype.val
        have hT_sub : T ⊆ S := by
          intro x hx
          rcases Finset.mem_image.mp hx with ⟨y, hy, rfl⟩
          exact y.property
        have hT_ne : T ≠ S := by
          intro hEq
          have hwS : w.1 ∈ S := w.property
          have hwT : w.1 ∈ T := by simp [hEq]
          rcases Finset.mem_image.mp hwT with ⟨y, hy, hwy⟩
          have hy' : y ∈ c.supp := by
            simpa using hy
          have : y = w := by
            apply Subtype.ext
            simpa using hwy
          exact hw (this ▸ hy')
        have hT_ss : T ⊂ S := Finset.ssubset_iff_subset_ne.mpr ⟨hT_sub, hT_ne⟩
        have hcolT : (G.induce (fun v : V => v ∈ T)).Colorable 3 :=
          hcolor_of_ssubset hT_ss
        rcases hcolT with ⟨C'⟩
        refine ⟨SimpleGraph.Coloring.mk ?_ ?_⟩
        · intro u
          exact C' ⟨u.1.1, by
            refine Finset.mem_image.mpr ?_
            refine ⟨u.1, ?_, rfl⟩
            simp⟩
        · intro u w huw
          have huw' :
              (G.induce (fun v : V => v ∈ T)).Adj
                ⟨u.1.1, by
                  refine Finset.mem_image.mpr ?_
                  refine ⟨u.1, by simp, rfl⟩⟩
                ⟨w.1.1, by
                  refine Finset.mem_image.mpr ?_
                  refine ⟨w.1, by simp, rfl⟩⟩ := by
            simpa using huw
          exact C'.valid huw'
      have hcolH : H.Colorable 3 :=
        (SimpleGraph.colorable_iff_forall_connectedComponents (G := H) (n := 3)).2 hcol_all
      exact hS_bad hcolH

    -- Deleting any vertex keeps the graph connected.
    have hH_del_conn :
        ∀ v : {v : V // v ∈ S},
          (H.induce (fun w : {v : V // v ∈ S} => w ≠ v)).Connected := by
      intro v
      -- assume disconnected and derive a 3-coloring of H
      by_contra hnot
      let Hdel : SimpleGraph {w : {v : V // v ∈ S} // w ≠ v} :=
        H.induce (fun w : {v : V // v ∈ S} => w ≠ v)
      -- Hdel is nonempty since deg(v) ≥ 3
      have hdel_nonempty : Nonempty {w : {v : V // v ∈ S} // w ≠ v} := by
        have hvdeg : 3 ≤ H.degree v := hδ3 v
        have hdegpos : 0 < H.degree v := lt_of_lt_of_le (by decide : (0 : ℕ) < 3) hvdeg
        have hneigh_nonempty : (H.neighborFinset v).Nonempty := by
          have hcard_pos : 0 < (H.neighborFinset v).card := by
            simpa [SimpleGraph.card_neighborFinset_eq_degree] using hdegpos
          exact Finset.card_pos.mp hcard_pos
        rcases hneigh_nonempty with ⟨u, hu⟩
        have huv : u ≠ v := by
          have : H.Adj v u := by
            simpa using (SimpleGraph.mem_neighborFinset (G := H) (v := v) (w := u)).1 hu
          have hvu : v ≠ u := H.ne_of_adj this
          simpa [ne_comm] using hvu
        exact ⟨⟨u, huv⟩⟩
      -- pick u,w with no path in Hdel
      have hnot' : ¬ ∃ u, ∀ w, Hdel.Reachable u w := by
        intro hex
        exact hnot ((SimpleGraph.connected_iff_exists_forall_reachable (G := Hdel)).2 hex)
      have hforall : ∀ u, ∃ w, ¬ Hdel.Reachable u w := by
        simpa [not_exists] using hnot'
      let u0 : {w : {v : V // v ∈ S} // w ≠ v} := Classical.choice hdel_nonempty
      rcases hforall u0 with ⟨w0, hnotreach⟩
      let c : Hdel.ConnectedComponent := Hdel.connectedComponentMk u0
      have hw_notin : w0 ∉ c.supp := by
        intro hw
        have hEq : Hdel.connectedComponentMk w0 = c := by
          simpa [SimpleGraph.ConnectedComponent.mem_supp_iff] using hw
        have hreach : Hdel.Reachable u0 w0 :=
          (SimpleGraph.ConnectedComponent.eq (G := Hdel)).1 (by
            simpa [c] using hEq.symm)
        exact hnotreach hreach
      -- component vertices as subsets of V
      let A : Finset V := c.supp.toFinset.image (fun w => w.1.1)
      let B : Finset V := (S.erase v.1) \ A
      have hu0_mem : u0 ∈ c.supp := by
        simp [SimpleGraph.ConnectedComponent.mem_supp_iff, c]
      have hA_nonempty : A.Nonempty := by
        refine ⟨u0.1.1, ?_⟩
        refine Finset.mem_image.mpr ?_
        exact ⟨u0, by simpa using hu0_mem, rfl⟩
      have hw0_ne_v : w0.1.1 ≠ v.1 := by
        intro h
        apply w0.property
        apply Subtype.ext
        simp [h]
      have hw0_in_Serase : w0.1.1 ∈ S.erase v.1 := by
        exact Finset.mem_erase.mpr ⟨hw0_ne_v, w0.1.property⟩
      have hw0_notin_A : w0.1.1 ∉ A := by
        intro hA
        rcases Finset.mem_image.mp hA with ⟨y, hy, hwy⟩
        have hy' : y ∈ c.supp := by simpa using hy
        have : y = w0 := by
          apply Subtype.ext
          apply Subtype.ext
          simpa using hwy
        exact hw_notin (this ▸ hy')
      have hB_nonempty : B.Nonempty := by
        refine ⟨w0.1.1, ?_⟩
        exact Finset.mem_sdiff.mpr ⟨hw0_in_Serase, hw0_notin_A⟩
      let A' : Finset V := A ∪ {v.1}
      let B' : Finset V := B ∪ {v.1}
      have hA'_ss : A' ⊂ S := by
        have hsubset : A' ⊆ S := by
          intro x hx
          rcases Finset.mem_union.mp hx with hx | hx
          · -- x in A
            rcases Finset.mem_image.mp hx with ⟨y, hy, rfl⟩
            exact y.1.property
          · simpa using (Finset.mem_singleton.mp hx ▸ v.property)
        have hw0_notin_A' : w0.1.1 ∉ A' := by
          intro h
          rcases Finset.mem_union.mp h with hA | hv
          · exact hw0_notin_A hA
          · exact hw0_ne_v (Finset.mem_singleton.mp hv)
        have hne : A' ≠ S := by
          intro hEq
          have : w0.1.1 ∈ A' := by simp [hEq]
          exact hw0_notin_A' this
        exact Finset.ssubset_iff_subset_ne.mpr ⟨hsubset, hne⟩
      have hu0_ne_v : u0.1.1 ≠ v.1 := by
        intro h
        apply u0.property
        apply Subtype.ext
        simp [h]
      have hu0_in_A : u0.1.1 ∈ A := by
        refine Finset.mem_image.mpr ?_
        exact ⟨u0, by simpa using hu0_mem, rfl⟩
      have hu0_notin_B : u0.1.1 ∉ B := by
        intro hB
        exact (Finset.mem_sdiff.mp hB).2 hu0_in_A
      have hB'_ss : B' ⊂ S := by
        have hsubset : B' ⊆ S := by
          intro x hx
          rcases Finset.mem_union.mp hx with hx | hx
          ·
            have hx' : x ∈ S.erase v.1 := (Finset.mem_sdiff.mp hx).1
            exact Finset.mem_of_subset (Finset.erase_subset _ _) hx'
          · simpa using (Finset.mem_singleton.mp hx ▸ v.property)
        have hu0_notin_B' : u0.1.1 ∉ B' := by
          intro h
          rcases Finset.mem_union.mp h with hB | hv
          · exact hu0_notin_B hB
          · exact hu0_ne_v (Finset.mem_singleton.mp hv)
        have hne : B' ≠ S := by
          intro hEq
          have : u0.1.1 ∈ B' := by simp [hEq]
          exact hu0_notin_B' this
        exact Finset.ssubset_iff_subset_ne.mpr ⟨hsubset, hne⟩
      have hcolA : (G.induce (fun u : V => u ∈ A')).Colorable 3 :=
        hcolor_of_ssubset hA'_ss
      have hcolB : (G.induce (fun u : V => u ∈ B')).Colorable 3 :=
        hcolor_of_ssubset hB'_ss
      rcases hcolA with ⟨CA⟩
      rcases hcolB with ⟨CB⟩
      have hvA' : v.1 ∈ A' :=
        Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl))
      have hvB' : v.1 ∈ B' :=
        Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl))
      let cA : Fin 3 := CA ⟨v.1, hvA'⟩
      let cB : Fin 3 := CB ⟨v.1, hvB'⟩
      let perm : Fin 3 ≃ Fin 3 := if h : cB = cA then Equiv.refl _ else Equiv.swap cB cA
      have hperm : perm cB = cA := by
        by_cases h : cB = cA
        · simp [perm, h]
        · simp [perm, h, Equiv.swap_apply_left]
      let CB' : (G.induce (fun u : V => u ∈ B')).Coloring (Fin 3) :=
        (SimpleGraph.recolorOfEquiv (G := G.induce (fun u : V => u ∈ B')) perm) CB
      have hcv : CB' ⟨v.1, hvB'⟩ = cA := by
        -- recolor sends `cB` to `perm cB = cA`
        simpa [CB', SimpleGraph.coe_recolorOfEquiv, hperm]
      let color : {u : V // u ∈ S} → Fin 3 :=
        fun u =>
          if h : u.1 = v.1 then cA
          else if hA : u.1 ∈ A then
            CA ⟨u.1, by exact Finset.mem_union.mpr (Or.inl hA)⟩
          else
            CB' ⟨u.1, by
              have : u.1 ∈ B := by
                have : u.1 ∈ S.erase v.1 := by
                  exact Finset.mem_erase.mpr ⟨h, u.property⟩
                exact Finset.mem_sdiff.mpr ⟨this, hA⟩
              exact Finset.mem_union.mpr (Or.inl this)⟩
      have hvalid : ∀ {u w : {u : V // u ∈ S}}, H.Adj u w → color u ≠ color w := by
        intro u w hAdj
        by_cases hu : u.1 = v.1
        · -- u is v
          by_cases hwA : w.1 ∈ A
          · -- w in A, use CA on A'
            have hwA' : w.1 ∈ A' := Finset.mem_union.mpr (Or.inl hwA)
            have hAdjG : G.Adj v.1 w.1 := by
              have huv : u = v := by
                apply Subtype.ext
                exact hu
              have hAdjH : H.Adj v w := by
                simpa [huv] using hAdj
              simpa using hAdjH
            have hAdjA :
                (G.induce (fun u : V => u ∈ A')).Adj
                  ⟨v.1, hvA'⟩ ⟨w.1, hwA'⟩ := by
              exact hAdjG
            have hneq := CA.valid hAdjA
            have hcu : color u = cA := by
              simp [color, hu]
            have hcu' : color u = CA ⟨v.1, hvA'⟩ := by
              simpa [cA] using hcu
            have hwv : w.1 ≠ v.1 := by
              intro h
              apply (H.ne_of_adj hAdj)
              apply Subtype.ext
              simp [hu, h]
            have hcw : color w = CA ⟨w.1, hwA'⟩ := by
              simp [color, hwv, hwA]
            intro hEq
            apply hneq
            exact (by simpa [hcu', hcw] using hEq)
          · -- w in B, use CB' on B'
            have hwv : w.1 ≠ v.1 := by
              intro h
              apply (H.ne_of_adj hAdj)
              apply Subtype.ext
              simp [hu, h]
            have hwB : w.1 ∈ B := by
              have : w.1 ∈ S.erase v.1 := by
                exact Finset.mem_erase.mpr ⟨hwv, w.property⟩
              exact Finset.mem_sdiff.mpr ⟨this, hwA⟩
            have hwB' : w.1 ∈ B' := Finset.mem_union.mpr (Or.inl hwB)
            have hAdjG : G.Adj v.1 w.1 := by
              have huv : u = v := by
                apply Subtype.ext
                exact hu
              have hAdjH : H.Adj v w := by
                simpa [huv] using hAdj
              simpa using hAdjH
            have hAdjB :
                (G.induce (fun u : V => u ∈ B')).Adj
                  ⟨v.1, hvB'⟩ ⟨w.1, hwB'⟩ := by
              exact hAdjG
            have hneq := CB'.valid hAdjB
            -- `CB'` sends `v` to `cA`
            have hcu : color u = cA := by
              simp [color, hu]
            have hcw : color w = CB' ⟨w.1, hwB'⟩ := by
              simp [color, hwv, hwA]
            intro hEq
            apply hneq
            have hEq' : CB' ⟨v.1, hvB'⟩ = CB' ⟨w.1, hwB'⟩ := by
              calc
                CB' ⟨v.1, hvB'⟩ = cA := hcv
                _ = color u := by symm; exact hcu
                _ = color w := hEq
                _ = CB' ⟨w.1, hwB'⟩ := hcw
            exact hEq'
        · by_cases hw : w.1 = v.1
          · -- w is v
            by_cases huA : u.1 ∈ A
            · -- u in A, use CA on A'
              have huA' : u.1 ∈ A' := Finset.mem_union.mpr (Or.inl huA)
              have hAdjG : G.Adj u.1 v.1 := by
                have hwu : w = v := by
                  apply Subtype.ext
                  exact hw
                have hAdjH : H.Adj u v := by
                  simpa [hwu] using hAdj
                simpa [hw] using hAdjH
              have hAdjA :
                  (G.induce (fun u : V => u ∈ A')).Adj
                    ⟨u.1, huA'⟩ ⟨v.1, hvA'⟩ := by
                exact hAdjG
              have hneq := CA.valid hAdjA
              have hcw : color w = cA := by
                simp [color, hw]
              have hcu : color u = CA ⟨u.1, huA'⟩ := by
                simp [color, hu, huA]
              intro hEq
              apply hneq
              -- rewrite color u / color w to CA-values
              exact (by
                have hcv' : cA = CA ⟨v.1, hvA'⟩ := by rfl
                simpa [hcu, hcw, hcv'] using hEq)
            · -- u in B, use CB' on B'
              have huB : u.1 ∈ B := by
                have : u.1 ∈ S.erase v.1 := by
                  exact Finset.mem_erase.mpr ⟨hu, u.property⟩
                exact Finset.mem_sdiff.mpr ⟨this, huA⟩
              have huB' : u.1 ∈ B' := Finset.mem_union.mpr (Or.inl huB)
              have hAdjG : G.Adj u.1 v.1 := by
                have hwu : w = v := by
                  apply Subtype.ext
                  exact hw
                have hAdjH : H.Adj u v := by
                  simpa [hwu] using hAdj
                simpa [hw] using hAdjH
              have hAdjB :
                  (G.induce (fun u : V => u ∈ B')).Adj
                    ⟨u.1, huB'⟩ ⟨v.1, hvB'⟩ := by
                exact hAdjG
              have hneq := CB'.valid hAdjB
              -- `CB'` sends v to cA
              have hcw : color w = cA := by
                simp [color, hw]
              have hcu : color u = CB' ⟨u.1, huB'⟩ := by
                simp [color, hu, huA]
              intro hEq
              apply hneq
              have hEq' : CB' ⟨u.1, huB'⟩ = CB' ⟨v.1, hvB'⟩ := by
                calc
                  CB' ⟨u.1, huB'⟩ = color u := by symm; exact hcu
                  _ = color w := hEq
                  _ = cA := hcw
                  _ = CB' ⟨v.1, hvB'⟩ := by symm; exact hcv
              exact hEq'
          · -- u and w both in S \\ {v}
            have hu_ne : u ≠ v := by
              intro h
              apply hu
              exact congrArg Subtype.val h
            have hw_ne : w ≠ v := by
              intro h
              apply hw
              exact congrArg Subtype.val h
            by_cases huA : u.1 ∈ A
            · by_cases hwA : w.1 ∈ A
              ·
                have huA' : u.1 ∈ A' := Finset.mem_union.mpr (Or.inl huA)
                have hwA' : w.1 ∈ A' := Finset.mem_union.mpr (Or.inl hwA)
                have hAdjA :
                    (G.induce (fun u : V => u ∈ A')).Adj
                      ⟨u.1, huA'⟩ ⟨w.1, hwA'⟩ := by
                  simpa using hAdj
                have hneq := CA.valid hAdjA
                have hcu : color u = CA ⟨u.1, huA'⟩ := by
                  simp [color, hu, huA]
                have hcw : color w = CA ⟨w.1, hwA'⟩ := by
                  simp [color, hw, hwA]
                intro hEq
                apply hneq
                exact (by simpa [hcu, hcw] using hEq)
              · -- u in A, w in B is impossible: would connect components in Hdel
                have hwB : w.1 ∈ B := by
                  have : w.1 ∈ S.erase v.1 := by
                    exact Finset.mem_erase.mpr ⟨hw, w.property⟩
                  exact Finset.mem_sdiff.mpr ⟨this, hwA⟩
                -- adjacency in Hdel would put w in the same component
                have hAdj_del :
                    Hdel.Adj ⟨u, hu_ne⟩ ⟨w, hw_ne⟩ := by
                  simpa using hAdj
                have hcomp_eq :
                    Hdel.connectedComponentMk
                        ⟨u, hu_ne⟩ =
                      Hdel.connectedComponentMk
                        ⟨w, hw_ne⟩ :=
                  (SimpleGraph.ConnectedComponent.eq (G := Hdel)).2
                    (SimpleGraph.Adj.reachable (G := Hdel) hAdj_del)
                -- u in c.supp, so w must be in c.supp, contradiction
                have hu_in : ⟨u, hu_ne⟩ ∈ c.supp := by
                  rcases Finset.mem_image.mp huA with ⟨y, hy, hyu⟩
                  have hy' : y ∈ c.supp := by
                    simpa using hy
                  have hyu' : y.1 = u := by
                    apply Subtype.ext
                    simpa using hyu
                  have : y = ⟨u, hu_ne⟩ := by
                    apply Subtype.ext
                    exact hyu'
                  exact this ▸ hy'
                have hw_in : ⟨w, hw_ne⟩ ∈ c.supp := by
                  have hcu_comp :
                      Hdel.connectedComponentMk ⟨u, hu_ne⟩ = c := by
                    simpa [SimpleGraph.ConnectedComponent.mem_supp_iff] using hu_in
                  have : Hdel.connectedComponentMk
                        ⟨w, hw_ne⟩ = c := by
                    calc
                      Hdel.connectedComponentMk ⟨w, hw_ne⟩
                          = Hdel.connectedComponentMk ⟨u, hu_ne⟩ := hcomp_eq.symm
                      _ = c := hcu_comp
                  simpa [SimpleGraph.ConnectedComponent.mem_supp_iff] using this
                -- contradiction: w in A
                have hwA' : w.1 ∈ A := by
                  refine Finset.mem_image.mpr ?_
                  have hw_in_fin : ⟨w, hw_ne⟩ ∈ c.supp.toFinset := by
                    simpa using hw_in
                  exact ⟨⟨w, hw_ne⟩, hw_in_fin, rfl⟩
                exact (hwA hwA').elim
            · -- u in B
              by_cases hwA : w.1 ∈ A
              · -- symmetric impossible case
                have huB : u.1 ∈ B := by
                  have : u.1 ∈ S.erase v.1 := by
                    exact Finset.mem_erase.mpr ⟨hu, u.property⟩
                  exact Finset.mem_sdiff.mpr ⟨this, huA⟩
                have hAdj_del :
                    Hdel.Adj ⟨w, hw_ne⟩ ⟨u, hu_ne⟩ := by
                  simpa using hAdj.symm
                have hcomp_eq :
                    Hdel.connectedComponentMk
                        ⟨w, hw_ne⟩ =
                      Hdel.connectedComponentMk
                        ⟨u, hu_ne⟩ :=
                  (SimpleGraph.ConnectedComponent.eq (G := Hdel)).2
                    (SimpleGraph.Adj.reachable (G := Hdel) hAdj_del)
                have hw_in : ⟨w, hw_ne⟩ ∈ c.supp := by
                  rcases Finset.mem_image.mp hwA with ⟨y, hy, hyw⟩
                  have hy' : y ∈ c.supp := by
                    simpa using hy
                  have hyw' : y.1 = w := by
                    apply Subtype.ext
                    simpa using hyw
                  have : y = ⟨w, hw_ne⟩ := by
                    apply Subtype.ext
                    exact hyw'
                  exact this ▸ hy'
                have hu_in : ⟨u, hu_ne⟩ ∈ c.supp := by
                  have hcw : Hdel.connectedComponentMk ⟨w, hw_ne⟩ = c := by
                    simpa [SimpleGraph.ConnectedComponent.mem_supp_iff] using hw_in
                  have : Hdel.connectedComponentMk ⟨u, hu_ne⟩ = c := by
                    calc
                      Hdel.connectedComponentMk ⟨u, hu_ne⟩
                          = Hdel.connectedComponentMk ⟨w, hw_ne⟩ := hcomp_eq.symm
                      _ = c := hcw
                  simpa [SimpleGraph.ConnectedComponent.mem_supp_iff] using this
                -- u in A, contradiction
                have huA' : u.1 ∈ A := by
                  refine Finset.mem_image.mpr ?_
                  have hu_in_fin : ⟨u, hu_ne⟩ ∈ c.supp.toFinset := by
                    simpa using hu_in
                  exact ⟨⟨u, hu_ne⟩, hu_in_fin, rfl⟩
                exact (huA huA').elim
              · -- both in B
                have huB : u.1 ∈ B := by
                  have : u.1 ∈ S.erase v.1 := by
                    exact Finset.mem_erase.mpr ⟨hu, u.property⟩
                  exact Finset.mem_sdiff.mpr ⟨this, huA⟩
                have hwB : w.1 ∈ B := by
                  have : w.1 ∈ S.erase v.1 := by
                    exact Finset.mem_erase.mpr ⟨hw, w.property⟩
                  exact Finset.mem_sdiff.mpr ⟨this, hwA⟩
                have huB' : u.1 ∈ B' := Finset.mem_union.mpr (Or.inl huB)
                have hwB' : w.1 ∈ B' := Finset.mem_union.mpr (Or.inl hwB)
                have hAdjB :
                    (G.induce (fun u : V => u ∈ B')).Adj
                      ⟨u.1, huB'⟩ ⟨w.1, hwB'⟩ := by
                  simpa using hAdj
                have hneq := CB'.valid hAdjB
                have hcu : color u = CB' ⟨u.1, huB'⟩ := by
                  unfold color
                  by_cases h : u.1 = v.1
                  · exact (hu h).elim
                  · by_cases hA : u.1 ∈ A
                    · exact (huA hA).elim
                    · simp [h, hA]
                have hcw : color w = CB' ⟨w.1, hwB'⟩ := by
                  unfold color
                  by_cases h : w.1 = v.1
                  · exact (hw h).elim
                  · by_cases hA : w.1 ∈ A
                    · exact (hwA hA).elim
                    · simp [h, hA]
                intro hEq
                apply hneq
                have hEq' : CB' ⟨u.1, huB'⟩ = CB' ⟨w.1, hwB'⟩ := by
                  calc
                    CB' ⟨u.1, huB'⟩ = color u := by symm; exact hcu
                    _ = color w := hEq
                    _ = CB' ⟨w.1, hwB'⟩ := hcw
                exact hEq'
      have hcol : H.Colorable 3 := ⟨SimpleGraph.Coloring.mk color hvalid⟩
      exact hS_bad hcol

    exact ⟨hH_conn, hH_del_conn⟩

  letI : Fintype {v : V // v ∈ S} := instSub (V := V) S
  exact
    { S := S
      h2 := h2
      hδ3 := hδ3
      hcard4 := hcard4 }

end Critical
end Erdos751
