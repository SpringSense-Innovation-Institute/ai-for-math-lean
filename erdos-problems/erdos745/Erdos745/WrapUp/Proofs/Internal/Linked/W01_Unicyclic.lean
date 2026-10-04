module

public import Erdos745.WrapUp.Proofs.Internal.Linked.W01_Pruefer
public import Erdos745.WrapUp.Proofs.Internal.Linked.W01_Asymptotic

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local simp] Pi.div_def Pi.mul_def Pi.add_def Pi.sub_def Pi.neg_def Pi.inv_def Function.comp_def Pi.pow_def Pi.smul_def Real.rpow_eq_pow

@[expose] public section


namespace Erdos745.WrapUp.Proofs.Internal.W01_ENUM_Unicyclic

open Erdos745.WrapUp.Proofs.Internal.W01_ENUM_Trees
open Erdos745.WrapUp.Proofs.Internal.W01_ENUM_Asymptotic
open scoped BigOperators

attribute [local instance] Classical.propDecidable

lemma simpleGraph_connected_of_reach {k : ℕ} {G : Graph k}
    (hk : 0 < k) (hconn : ∀ u v : Fin k, reach G u v) :
    (W01_ENUM_Trees.simpleGraph G).Connected := by
  letI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  apply SimpleGraph.Connected.mk
  intro u v
  exact W01_ENUM_Trees.simpleGraph_reachable_iff.mpr (hconn u v)

lemma edgeFinset_subset_of_graph_le {k : ℕ}
    {T G : SimpleGraph (Fin k)} (hTG : T ≤ G) :
    T.edgeFinset ⊆ G.edgeFinset := by
  intro e he
  induction e using Sym2.inductionOn with
  | _ u v =>
      simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he ⊢
      exact hTG he

/-- A connected graph on `k` vertices with `k` edges is a spanning tree plus
one edge.  This is the graph-theoretic entry point for the unique-cycle
decomposition: the added edge and the unique path between its endpoints in
the tree determine the cycle. -/
theorem exists_spanningTree_one_extra {k : ℕ} {G : Graph k}
    (hk : 0 < k) (hcard : G.card = k)
    (hconn : ∀ u v : Fin k, reach G u v) :
    ∃ T : SimpleGraph (Fin k),
      T ≤ W01_ENUM_Trees.simpleGraph G ∧ T.IsTree ∧
        ((W01_ENUM_Trees.simpleGraph G).edgeFinset \ T.edgeFinset).card = 1 := by
  have hGconn := simpleGraph_connected_of_reach hk hconn
  obtain ⟨T, hTG, hT⟩ := hGconn.exists_isTree_le
  refine ⟨T, hTG, hT, ?_⟩
  have hsub : T.edgeFinset ⊆
      (W01_ENUM_Trees.simpleGraph G).edgeFinset :=
    edgeFinset_subset_of_graph_le hTG
  rw [Finset.card_sdiff_of_subset hsub]
  have hGedges : (W01_ENUM_Trees.simpleGraph G).edgeFinset.card = k := by
    rw [W01_ENUM_Pruefer.simpleGraph_edgeFinset_card, hcard]
  have hTedges : T.edgeFinset.card = k - 1 := by
    have htcard := hT.card_edgeFinset
    simp only [Fintype.card_fin] at htcard
    omega
  rw [hGedges, hTedges]
  omega

/-!
The exact counting boundary for the unique-cycle decomposition.  The index
`m` is the number of vertices off the cycle, so the cycle-root set has size
`k - m`.  For every such root set there are `(k-m-1)! / 2` unoriented cyclic
orders and `rootedForestCount k roots` forests attached to those roots.
-/
def CycleForestDecomposition : Prop :=
  ∀ k : ℕ, 3 ≤ k →
    (connectedCount k k : ℝ) =
      ∑ m ∈ Finset.range (k - 2),
        (((k - m - 1).factorial : ℝ) / 2) *
          ∑ roots ∈
              Finset.powersetCard (k - m)
                (Finset.univ : Finset (Fin k)),
            (rootedForestCount k roots : ℝ)

private lemma card_eq_of_mem_powersetCard {k r : ℕ}
    {roots : Finset (Fin k)}
    (hroots : roots ∈
      Finset.powersetCard r (Finset.univ : Finset (Fin k))) :
    roots.card = r := by
  exact (Finset.mem_powersetCard.mp hroots).2

lemma rootedForest_sum_of_formula
    (hforest : RootedForestFormula) (k r : ℕ) :
    (∑ roots ∈
        Finset.powersetCard r (Finset.univ : Finset (Fin k)),
      (rootedForestCount k roots : ℝ)) =
      (k.choose r : ℝ) *
        ((if r = k then 1 else r * k ^ (k - r - 1) : ℕ) : ℝ) := by
  calc
    (∑ roots ∈
        Finset.powersetCard r (Finset.univ : Finset (Fin k)),
      (rootedForestCount k roots : ℝ)) =
        ∑ _roots ∈
            Finset.powersetCard r (Finset.univ : Finset (Fin k)),
          ((if r = k then 1 else r * k ^ (k - r - 1) : ℕ) : ℝ) := by
      apply Finset.sum_congr rfl
      intro roots hroots
      rw [hforest k roots, card_eq_of_mem_powersetCard hroots]
    _ = (k.choose r : ℝ) *
        ((if r = k then 1 else r * k ^ (k - r - 1) : ℕ) : ℝ) := by
      rw [Finset.sum_const, Finset.card_powersetCard]
      simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

private lemma factorial_cast_succ_sub_one (n : ℕ) (hn : 0 < n) :
    (n.factorial : ℝ) = n * ((n - 1).factorial : ℝ) := by
  have hn' : n = (n - 1) + 1 := by omega
  conv_lhs => rw [hn', Nat.factorial_succ]
  push_cast
  have hnR : ((n - 1 : ℕ) : ℝ) + 1 = n := by
    exact_mod_cast hn'.symm
  rw [hnR]

private lemma pow_cast_succ_sub_one (k m : ℕ) (hm : 0 < m) :
    (k : ℝ) ^ m = (k : ℝ) ^ (m - 1) * k := by
  have hm' : m = (m - 1) + 1 := by omega
  nth_rewrite 1 [hm']
  rw [pow_succ]

private lemma choose_cycle_roots_cast (k m : ℕ) (hm : m ≤ k) :
    (k.choose (k - m) : ℝ) =
      (k.factorial : ℝ) /
        (((k - m).factorial : ℝ) * (m.factorial : ℝ)) := by
  rw [Nat.cast_choose (K := ℝ) (Nat.sub_le k m)]
  rw [Nat.sub_sub_self hm]

lemma cycle_forest_summand_eq
    (hforest : RootedForestFormula) {k m : ℕ}
    (hk : 3 ≤ k) (hm : m ∈ Finset.range (k - 2)) :
    (((k - m - 1).factorial : ℝ) / 2) *
        (∑ roots ∈
            Finset.powersetCard (k - m)
              (Finset.univ : Finset (Fin k)),
          (rootedForestCount k roots : ℝ)) =
      ((k - 1).factorial : ℝ) / 2 *
        ((k : ℝ) ^ m / (m.factorial : ℝ)) := by
  have hmlt : m < k - 2 := Finset.mem_range.mp hm
  have hmk : m ≤ k := by omega
  have hrpos : 0 < k - m := by omega
  rw [rootedForest_sum_of_formula hforest]
  by_cases hm0 : m = 0
  · subst m
    simp
  · have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
    have hrne : k - m ≠ k := by omega
    rw [if_neg hrne]
    simp only [Nat.cast_mul, Nat.cast_pow]
    have hsub : k - (k - m) - 1 = m - 1 := by omega
    rw [hsub]
    have hchoose := choose_cycle_roots_cast k m hmk
    rw [hchoose]
    have hkpos : 0 < k := by omega
    have hkfac := factorial_cast_succ_sub_one k hkpos
    have hrfac := factorial_cast_succ_sub_one (k - m) hrpos
    have hkpow := pow_cast_succ_sub_one k m hmpos
    rw [hkfac, hrfac, hkpow]
    have hk0 : (k : ℝ) ≠ 0 := by positivity
    have hr0 : ((k - m : ℕ) : ℝ) ≠ 0 := by positivity
    have hmfac0 : (m.factorial : ℝ) ≠ 0 := by positivity
    field_simp [hk0, hr0, hmfac0]

theorem unicyclic_formula_of_cycle_forest_decomposition
    (hforest : RootedForestFormula)
    (hdecomp : CycleForestDecomposition) : UnicyclicFormula := by
  intro k hk
  rw [hdecomp k hk]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  exact cycle_forest_summand_eq hforest hk hm

end Erdos745.WrapUp.Proofs.Internal.W01_ENUM_Unicyclic


namespace Erdos745.WrapUp.Proofs.Internal.W01_ENUM_Decomposition

open Erdos745.WrapUp.Proofs.Internal.W01_ENUM_Trees
open Erdos745.WrapUp.Proofs.Internal.W01_ENUM_Pruefer
open Erdos745.WrapUp.Proofs.Internal.W01_ENUM_Cycle
open Erdos745.WrapUp.Proofs.Internal.W01_ENUM_Unicyclic
open scoped BigOperators Sym2

attribute [local instance] Classical.propDecidable

private lemma edge_mem_iff_adj {k : ℕ} {G : Graph k} (e : Edge k) :
    e ∈ G ↔ adj G e.val.1 e.val.2 := by
  constructor
  · intro he
    exact ⟨e, he, Or.inl ⟨rfl, rfl⟩⟩
  · rintro ⟨f, hf, h | h⟩
    · have hfe : f = e := by
        apply Subtype.ext
        exact Prod.ext h.1 h.2
      simpa [hfe] using! hf
    · have hback : e.val.2 < e.val.1 := by
        rw [← h.1, ← h.2]
        exact f.property
      exact False.elim (lt_asymm e.property hback)

private lemma edgeSym2_mem_edgeFinset {k : ℕ} {G : Graph k}
    (e : Edge k) :
    edgeSym2 e ∈ (simpleGraph G).edgeFinset ↔ e ∈ G := by
  rw [SimpleGraph.mem_edgeFinset]
  change s(e.val.1, e.val.2) ∈ (simpleGraph G).edgeSet ↔ e ∈ G
  rw [SimpleGraph.mem_edgeSet,
    simpleGraph_adj, edge_mem_iff_adj]

private lemma path_formPerm_end {k : ℕ} {T : SimpleGraph (Fin k)}
    {u v : Fin k} (p : T.Walk u v) (hp : p.IsPath) :
    p.support.formPerm v = u := by
  have hv : v ∈ p.support := p.end_mem_support
  rw [List.formPerm_apply_mem_eq_next hp.support_nodup v hv]
  have hl : p.support ≠ [] := List.ne_nil_of_mem hv
  have hvlast : v = p.support.getLast hl := by
    simpa using! (p.getLast_support hl).symm
  have hlastnot : p.support.getLast hl ∉ p.support.dropLast := by
    have hn := hp.support_nodup
    rw [← List.dropLast_append_getLast hl] at hn
    intro hmem
    exact ((List.nodup_append.mp hn).2.2 _ hmem _ (by simp)) rfl
  have hnext := List.next_getLast_eq_head_of_notMem_dropLast hl hlastnot
  have hnext' : p.support.next v hv = p.support.head hl := by
    simpa only [hvlast] using! hnext
  rw [hnext']
  exact p.head_support

private lemma path_formPerm_adj {k : ℕ} {T G : SimpleGraph (Fin k)}
    {u v : Fin k} (p : T.Walk u v) (hp : p.IsPath)
    (hTG : T ≤ G) (hclose : G.Adj v u) :
    ∀ x, x ∈ p.support → G.Adj x (p.support.formPerm x) := by
  intro x hx
  rw [List.formPerm_apply_mem_eq_next hp.support_nodup x hx]
  by_cases hdrop : x ∈ p.support.dropLast
  · have hinfix := List.nextOr_infix_of_mem_dropLast hdrop
      (p.support.get ⟨0, List.length_pos_of_mem hx⟩)
    have hchain := p.isChain_adj_support.infix hinfix
    apply hTG
    simpa only [List.isChain_pair, List.next] using! hchain
  · have hl : p.support ≠ [] := List.ne_nil_of_mem hx
    have hxlast : x = p.support.getLast hl := by
      by_contra hne
      exact hdrop (List.mem_dropLast_of_mem_of_ne_getLast hx hne)
    subst x
    have hlastnot : p.support.getLast hl ∉ p.support.dropLast := by
      have hn := hp.support_nodup
      rw [← List.dropLast_append_getLast hl] at hn
      intro hmem
      exact ((List.nodup_append.mp hn).2.2 _ hmem _ (by simp)) rfl
    rw [List.next_getLast_eq_head_of_notMem_dropLast hl hlastnot]
    simpa using! hclose

/-- Every connected labelled graph with `k` vertices and `k` edges is the
assembly of one of the already defined oriented cycle/forest data. -/
theorem exists_orientedCycleForest {k : ℕ} (G : ConnectedKGraph k)
    (hk : 3 ≤ k) :
    ∃ r : ℕ, 3 ≤ r ∧ r ≤ k ∧
      ∃ d : OrientedCycleForest k r, assemble d = G.1 := by
  obtain ⟨T, hTG, hT, hdiffcard⟩ :=
    exists_spanningTree_one_extra (G := G.1) (by omega) G.2.1 G.2.2
  obtain ⟨q, hq⟩ := Finset.card_eq_one.mp hdiffcard
  have hqmem : q ∈ (simpleGraph G.1).edgeFinset \ T.edgeFinset := by
    simp [hq]
  have hqG : q ∈ (simpleGraph G.1).edgeFinset :=
    (Finset.mem_sdiff.mp hqmem).1
  have hqT : q ∉ T.edgeFinset := (Finset.mem_sdiff.mp hqmem).2
  induction q using Sym2.inductionOn with
  | _ u v =>
      have hGuv : (simpleGraph G.1).Adj u v := by
        simpa only [SimpleGraph.mem_edgeFinset,
          SimpleGraph.mem_edgeSet] using! hqG
      have hTuv : ¬ T.Adj u v := by
        simpa only [SimpleGraph.mem_edgeFinset,
          SimpleGraph.mem_edgeSet] using! hqT
      obtain ⟨p, hp, -⟩ := hT.existsUnique_path u v
      have huv : u ≠ v := hGuv.ne
      have hp0 : p.length ≠ 0 := fun h => huv (p.eq_of_length_eq_zero h)
      have hp1 : p.length ≠ 1 := fun h => hTuv (p.adj_of_length_eq_one h)
      have hplen : 2 ≤ p.length := by omega
      have hsupportlen : 3 ≤ p.support.length := by
        rw [p.length_support]
        omega
      let σ : Equiv.Perm (Fin k) := p.support.formPerm
      have hσcycle : σ.IsCycle := by
        exact List.isCycle_formPerm hp.support_nodup (by omega)
      have hnotSingleton : ∀ x : Fin k, p.support ≠ [x] := by
        intro x hx
        have hlen := congrArg List.length hx
        simp only [List.length_singleton] at hlen
        omega
      have hσsupport : σ.support = p.support.toFinset := by
        exact List.support_formPerm_of_nodup p.support hp.support_nodup
          hnotSingleton
      let C : Graph k := cycleEdges σ
      have hCG : C ⊆ G.1 := by
        intro e he
        rw [edge_mem_iff_adj] at he ⊢
        rw [adj_cycleEdges_iff] at he
        have hpathAdj := path_formPerm_adj p hp hTG hGuv.symm
        rcases he.2 with hforward | hback
        · have heSupport : e.val.1 ∈ σ.support :=
            support_of_cycle_edge_left he.1 (Or.inl hforward)
          have heList : e.val.1 ∈ p.support := by
            simpa [hσsupport] using! heSupport
          change p.support.formPerm e.val.1 = e.val.2 at hforward
          have hadj := hpathAdj e.val.1 heList
          rw [hforward] at hadj
          exact hadj
        · have heSupport : e.val.2 ∈ σ.support :=
            support_of_cycle_edge_right he.1 (Or.inr hback)
          have heList : e.val.2 ∈ p.support := by
            simpa [hσsupport] using! heSupport
          change p.support.formPerm e.val.2 = e.val.1 at hback
          have hadj := (hpathAdj e.val.2 heList).symm
          rw [hback] at hadj
          exact hadj
      have hCuv : (simpleGraph C).Adj u v := by
        rw [simpleGraph_adj, adj_cycleEdges_iff]
        exact ⟨huv, Or.inr (path_formPerm_end p hp)⟩
      let F : Graph k := G.1 \ C
      have hFT : simpleGraph F ≤ T := by
        intro a b hab
        rcases hab with ⟨e, heF, hends⟩
        have heparts : e ∈ G.1 ∧ e ∉ C := Finset.mem_sdiff.mp heF
        have heT : edgeSym2 e ∈ T.edgeFinset := by
          by_contra hnotT
          have hediff : edgeSym2 e ∈
              (simpleGraph G.1).edgeFinset \ T.edgeFinset := by
            exact Finset.mem_sdiff.mpr
              ⟨(edgeSym2_mem_edgeFinset e).2 heparts.1, hnotT⟩
          have heq : edgeSym2 e = s(u, v) := by
            simpa [hq] using! hediff
          have heCedge : edgeSym2 e ∈ (simpleGraph C).edgeFinset := by
            rw [heq, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
            exact hCuv
          exact heparts.2 ((edgeSym2_mem_edgeFinset e).1 heCedge)
        have hTe : T.Adj e.val.1 e.val.2 := by
          simpa only [SimpleGraph.mem_edgeFinset,
            SimpleGraph.mem_edgeSet] using! heT
        rcases hends with h | h
        · simpa [h.1, h.2] using! hTe
        · simpa [h.1, h.2] using! hTe.symm
      have hFacyclic : (simpleGraph F).IsAcyclic :=
        SimpleGraph.IsAcyclic.anti hFT hT.IsAcyclic
      have htree : ∀ S ∈ components F, isTree F S :=
        component_isTree_of_acyclic hFacyclic
      have hreachRoot : ∀ x : Fin k,
          ∃ root ∈ σ.support, reach F x root := by
        obtain ⟨root0, hroot0⟩ := hσcycle.nonempty_support
        intro x
        have hpathG := G.2.2 root0 x
        have hforward : ∃ root ∈ σ.support, reach F root x := by
          induction hpathG with
          | refl => exact ⟨root0, hroot0, reach_refl root0⟩
          | tail hxy hyz ih =>
              rename_i y z
              rcases ih with ⟨root, hroot, hreach⟩
              rcases hyz with ⟨e, heG, hends⟩
              by_cases heC : e ∈ C
              · have hsupp := cycleEdges_mono_support heC
                have hz : z ∈ σ.support := by
                  rcases hends with h | h
                  · simpa [h.2] using! hsupp.2
                  · simpa [h.1] using! hsupp.1
                exact ⟨z, hz, reach_refl z⟩
              · have heF : e ∈ F := Finset.mem_sdiff.mpr ⟨heG, heC⟩
                exact ⟨root, hroot,
                  reach_trans hreach (reach_of_adj ⟨e, heF, hends⟩)⟩
        rcases hforward with ⟨root, hroot, hreach⟩
        exact ⟨root, hroot, reach_symm hreach⟩
      let r := σ.support.card
      have hr3 : 3 ≤ r := by
        change 3 ≤ σ.support.card
        rw [hσsupport, List.toFinset_card_of_nodup hp.support_nodup]
        exact hsupportlen
      have hrk : r ≤ k := by
        change σ.support.card ≤ k
        simpa using! Finset.card_le_univ σ.support
      have hFcard : F.card = k - r := by
        dsimp only [F, C, r]
        rw [Finset.card_sdiff_of_subset hCG, G.2.1,
          cycleEdges_card hσcycle hr3]
      have hcomponentCard : (components F).card = r := by
        have hcount := component_count_of_forest F htree
        omega
      have hcomponentRootPos : ∀ S ∈ components F,
          0 < (S ∩ σ.support).card := by
        intro S hS
        simp only [components, Finset.mem_image] at hS
        rcases hS with ⟨x, -, rfl⟩
        obtain ⟨root, hroot, hxr⟩ := hreachRoot x
        apply Finset.card_pos.mpr
        exact ⟨root, Finset.mem_inter.mpr
          ⟨mem_componentOf_iff.mpr hxr, hroot⟩⟩
      have hrootSum := sum_component_root_cards F σ.support
      have hsplit :
          ∑ S ∈ components F, (S ∩ σ.support).card =
            (∑ S ∈ components F, ((S ∩ σ.support).card - 1)) +
              (components F).card := by
        calc
          ∑ S ∈ components F, (S ∩ σ.support).card =
              ∑ S ∈ components F, (((S ∩ σ.support).card - 1) + 1) := by
            apply Finset.sum_congr rfl
            intro S hS
            have hp := hcomponentRootPos S hS
            omega
          _ = (∑ S ∈ components F, ((S ∩ σ.support).card - 1)) +
                ∑ _S ∈ components F, 1 := by
            rw [Finset.sum_add_distrib]
          _ = _ := by simp
      have hzero :
          ∑ S ∈ components F, ((S ∩ σ.support).card - 1) = 0 := by
        rw [hrootSum, hcomponentCard] at hsplit
        change σ.support.card = _ + σ.support.card at hsplit
        omega
      have hrootOne : ∀ S ∈ components F,
          (S ∩ σ.support).card = 1 := by
        intro S hS
        have hz : (S ∩ σ.support).card - 1 = 0 :=
          (Finset.sum_eq_zero_iff.mp hzero) S hS
        have hp := hcomponentRootPos S hS
        omega
      let forest : RootedForest k σ.support :=
        ⟨F, fun S hS => ⟨htree S hS, hrootOne S hS⟩⟩
      let d : OrientedCycleForest k r :=
        { cycle := σ
          isCycle := hσcycle
          support_card := rfl
          three_le := hr3
          forest := forest }
      refine ⟨r, hr3, hrk, d, ?_⟩
      change F ∪ C = G.1
      exact Finset.sdiff_union_of_subset hCG

abbrev CycleForestFamily (k : ℕ) :=
  Σ m : {m : ℕ // m ∈ Finset.range (k - 2)},
    UnorientedCycleForest k (k - m)

private lemma cast_unoriented_val {k r s : ℕ} (h : r = s)
    (G : UnorientedCycleForest k r) :
    (cast (congrArg (fun t => UnorientedCycleForest k t) h) G).1 = G.1 := by
  cases h
  rfl

private noncomputable def familyToConnected {k : ℕ} (x : CycleForestFamily k) :
    ConnectedKGraph k := by
  let d : OrientedCycleForest k (k - x.1.1) := x.2.2.choose
  have hd : assemble d = x.2.1 := x.2.2.choose_spec
  exact ⟨x.2.1, by
    constructor
    · rw [← hd]
      exact assemble_card d
    · intro u v
      rw [← hd]
      exact assemble_connected d u v⟩

private lemma familyToConnected_injective {k : ℕ} :
    Function.Injective (@familyToConnected k) := by
  rintro ⟨m, G⟩ ⟨n, H⟩ heq
  have hgraph : G.1 = H.1 := congrArg Subtype.val heq
  let d : OrientedCycleForest k (k - m.1) := G.2.choose
  let e : OrientedCycleForest k (k - n.1) := H.2.choose
  have hd : assemble d = G.1 := G.2.choose_spec
  have he : assemble e = H.1 := H.2.choose_spec
  have hassemble : assemble d = assemble e := hd.trans (hgraph.trans he.symm)
  have hcycle := cycleEdges_eq_of_assemble_eq d e hassemble
  have hsupport := support_eq_of_cycleEdges_eq d.isCycle e.isCycle
    (by simpa [d.support_card] using! d.three_le)
    (by simpa [e.support_card] using! e.three_le) hcycle
  have hr : k - m.1 = k - n.1 := by
    calc
      k - m.1 = d.cycle.support.card := d.support_card.symm
      _ = e.cycle.support.card := congrArg Finset.card hsupport
      _ = k - n.1 := e.support_card
  have hm : m.1 < k - 2 := Finset.mem_range.mp m.2
  have hn : n.1 < k - 2 := Finset.mem_range.mp n.2
  have hmn : m = n := by
    apply Subtype.ext
    omega
  subst n
  have hGH : G = H := Subtype.ext hgraph
  subst H
  rfl

private lemma familyToConnected_surjective {k : ℕ} (hk : 3 ≤ k) :
    Function.Surjective (@familyToConnected k) := by
  intro G
  obtain ⟨r, hr3, hrk, d, hd⟩ := exists_orientedCycleForest G hk
  let m := k - r
  have hm : m ∈ Finset.range (k - 2) := by
    rw [Finset.mem_range]
    dsimp [m]
    omega
  have hkm : k - m = r := by
    dsimp [m]
    omega
  let base : UnorientedCycleForest k r := ⟨G.1, d, hd⟩
  let datum : UnorientedCycleForest k (k - m) :=
    cast (congrArg (fun t => UnorientedCycleForest k t) hkm.symm) base
  refine ⟨⟨⟨m, hm⟩, datum⟩, ?_⟩
  apply Subtype.ext
  change datum.1 = G.1
  calc
    datum.1 = base.1 := cast_unoriented_val hkm.symm base
    _ = G.1 := rfl

noncomputable def cycleForestFamilyEquiv (k : ℕ) (hk : 3 ≤ k) :
    CycleForestFamily k ≃ ConnectedKGraph k :=
  Equiv.ofBijective familyToConnected
    ⟨familyToConnected_injective, familyToConnected_surjective hk⟩

private lemma card_connected_eq_sum (k : ℕ) (hk : 3 ≤ k) :
    connectedCount k k =
      ∑ m ∈ Finset.range (k - 2),
        Fintype.card (UnorientedCycleForest k (k - m)) := by
  calc
    connectedCount k k = Fintype.card (ConnectedKGraph k) :=
      (card_connectedKGraph (by omega)).symm
    _ = Fintype.card (CycleForestFamily k) :=
      (Fintype.card_congr (cycleForestFamilyEquiv k hk)).symm
    _ = ∑ m : {m : ℕ // m ∈ Finset.range (k - 2)},
          Fintype.card (UnorientedCycleForest k (k - m)) :=
      Fintype.card_sigma
    _ = ∑ m ∈ Finset.range (k - 2),
          Fintype.card (UnorientedCycleForest k (k - m)) := by
      exact (Finset.sum_subtype (Finset.range (k - 2))
        (fun _ => Iff.rfl)
        (fun m => Fintype.card
          (UnorientedCycleForest k (k - m)))).symm

private lemma card_unoriented_cast {k r : ℕ} (hr3 : 3 ≤ r)
    (hrk : r ≤ k) :
    (Fintype.card (UnorientedCycleForest k r) : ℝ) =
      (((r - 1).factorial : ℝ) / 2) *
        ∑ roots ∈
            Finset.powersetCard r (Finset.univ : Finset (Fin k)),
          (rootedForestCount k roots : ℝ) := by
  have horiented := card_orientedCycleForest
    W01_ENUM_Pruefer.rootedForestFormula hr3 hrk
  have hfiber := card_oriented_eq_two_mul_unoriented (k := k) (r := r)
  have horientedR := congrArg (fun n : ℕ => (n : ℝ)) horiented
  have hfiberR := congrArg (fun n : ℕ => (n : ℝ)) hfiber
  norm_num only [Nat.cast_mul, Nat.cast_ofNat] at horientedR hfiberR
  rw [hfiberR] at horientedR
  rw [rootedForest_sum_of_formula W01_ENUM_Pruefer.rootedForestFormula]
  calc
    (Fintype.card (UnorientedCycleForest k r) : ℝ) =
        (2 * (Fintype.card (UnorientedCycleForest k r) : ℝ)) / 2 := by ring
    _ = ((((r - 1).factorial : ℝ) * (k.choose r : ℝ)) *
          ((if r = k then 1 else r * k ^ (k - r - 1) : ℕ) : ℝ)) / 2 := by
      rw [horientedR]
    _ = (((r - 1).factorial : ℝ) / 2) *
          ((k.choose r : ℝ) *
            ((if r = k then 1 else r * k ^ (k - r - 1) : ℕ) : ℝ)) := by
      ring

/-- The unconditional unique-cycle decomposition in the exact form consumed
by the public W01 assembler. -/
theorem cycleForestDecomposition : CycleForestDecomposition := by
  intro k hk
  have hnat := card_connected_eq_sum k hk
  have hcast : (connectedCount k k : ℝ) =
      ∑ m ∈ Finset.range (k - 2),
        (Fintype.card (UnorientedCycleForest k (k - m)) : ℝ) := by
    exact_mod_cast hnat
  rw [hcast]
  apply Finset.sum_congr rfl
  intro m hm
  have hmlt : m < k - 2 := Finset.mem_range.mp hm
  apply card_unoriented_cast
  · omega
  · omega

end Erdos745.WrapUp.Proofs.Internal.W01_ENUM_Decomposition
