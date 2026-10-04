module

public import Mathlib.Combinatorics.SimpleGraph.Trails
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.WalkCounting
public import Erdos745.WrapUp.Contracts
public import Erdos745.WrapUp.Proofs.Internal.Linked.W01_FiniteCore

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local simp] Pi.div_def Pi.mul_def Pi.add_def Pi.sub_def Pi.neg_def Pi.inv_def Function.comp_def Pi.pow_def Pi.smul_def Real.rpow_eq_pow

@[expose] public section


/-!
# The finite Euler circuit lemma missing from `SimpleGraph.Trails`

This is the maximal-trail direction needed by the bicyclic-core encoding.  It
is deliberately local to W07: Mathlib currently provides the Eulerian-trail
predicate and its parity consequences, but not the converse existence theorem.
-/

namespace Erdos745.WrapUp.Proofs.Internal.W07_SUBCRIT_Euler

open Finset
open scoped Sym2

noncomputable section
attribute [local instance] Classical.propDecidable

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

private def HasTrailLength (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ u v : V, ∃ p : G.Walk u v, p.IsTrail ∧ p.length = k

private lemma hasTrailLength_zero (hG : G.Connected) : HasTrailLength G 0 := by
  letI := hG.nonempty
  let u : V := Classical.choice (inferInstance : Nonempty V)
  exact ⟨u, u, .nil, .nil, rfl⟩

private lemma exists_maximal_trail (hG : G.Connected) :
    ∃ u v : V, ∃ p : G.Walk u v,
      p.IsTrail ∧
      ∀ {u' v' : V} (q : G.Walk u' v'), q.IsTrail → q.length ≤ p.length := by
  let b := G.edgeFinset.card
  let L := Nat.findGreatest (HasTrailLength G) b
  have hzero : HasTrailLength G 0 := hasTrailLength_zero hG
  have hL : HasTrailLength G L := by
    exact Nat.findGreatest_spec (Nat.zero_le b) hzero
  obtain ⟨u, v, p, hp, hpL⟩ := hL
  refine ⟨u, v, p, hp, ?_⟩
  intro u' v' q hq
  by_contra hnot
  have hlt : L < q.length := by omega
  have hqb : q.length ≤ b := hq.length_le_card_edgeFinset
  exact Nat.findGreatest_is_greatest hlt hqb
    ⟨u', v', q, hq, rfl⟩

private lemma reachable_crosses {P : Set V} {u v : V}
    (h : G.Reachable u v) (hu : u ∈ P) (hv : v ∉ P) :
    ∃ x y : V, x ∈ P ∧ y ∉ P ∧ G.Adj x y := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact False.elim (hv hu)
  | @cons a b c hab p ih =>
      by_cases hb : b ∈ P
      · exact ih hb hv
      · exact ⟨a, b, hu, hb, hab⟩

private lemma usedIncidence_subset {u v : V} (p : G.Walk u v) (hp : p.IsTrail) (x : V) :
    hp.edgesFinset.filter (x ∈ ·) ⊆ G.incidenceFinset x := by
  intro e he
  have hep : e ∈ p.edges := by simpa using! (mem_filter.mp he).1
  have heG : e ∈ G.edgeFinset := by
    rw [G.mem_edgeFinset]
    exact p.edges_subset_edgeSet hep
  have hxe : x ∈ e := (mem_filter.mp he).2
  rw [G.incidenceFinset_eq_filter]
  exact mem_filter.mpr ⟨heG, hxe⟩

private lemma countP_incidence_eq_card {u v : V} (p : G.Walk u v)
    (hp : p.IsTrail) (x : V) :
    p.edges.countP (x ∈ ·) = (hp.edgesFinset.filter (x ∈ ·)).card := by
  rw [← Multiset.coe_countP, Multiset.countP_eq_card_filter]
  rfl

private lemma exists_unused_incident_of_open {u v : V} (p : G.Walk u v)
    (hp : p.IsTrail) (heven : ∀ x, Even (G.degree x)) (huv : u ≠ v) :
    ∃ w : V, G.Adj v w ∧ s(v, w) ∉ p.edges := by
  by_contra hnone
  push_neg at hnone
  have hsub : G.incidenceFinset v ⊆ hp.edgesFinset.filter (v ∈ ·) := by
    intro e he
    let es : G.incidenceSet v := ⟨e, (G.mem_incidenceFinset).mp he⟩
    let w : G.neighborSet v := G.incidenceSetEquivNeighborSet v es
    have hadj : G.Adj v w.1 := w.2
    have heq : s(v, w.1) = e := by
      have hback := (G.incidenceSetEquivNeighborSet v).symm_apply_apply es
      exact congrArg Subtype.val hback
    have heUsed : e ∈ p.edges := by
      rw [← heq]
      exact hnone w.1 hadj
    exact mem_filter.mpr ⟨by simpa using! heUsed, by rw [← heq]; simp⟩
  have heqFin : G.incidenceFinset v = hp.edgesFinset.filter (v ∈ ·) :=
    Subset.antisymm hsub (usedIncidence_subset p hp v)
  have hcount : p.edges.countP (v ∈ ·) = G.degree v := by
    rw [countP_incidence_eq_card p hp v, ← heqFin,
      G.card_incidenceFinset_eq_degree]
  have husedEven : Even (p.edges.countP (v ∈ ·)) := by
    rw [hcount]
    exact heven v
  have hparity := hp.even_countP_edges_iff v
  have hnot : ¬ Even (p.edges.countP (v ∈ ·)) := by
    rw [hparity]
    simp [huv]
  exact hnot husedEven

private lemma extend_trail_at_end {u v : V} (p : G.Walk u v) (hp : p.IsTrail)
    {w : V} (hvw : G.Adj v w) (hnew : s(v, w) ∉ p.edges) :
    ∃ q : G.Walk u w, q.IsTrail ∧ q.length = p.length + 1 := by
  let q : G.Walk u w := (p.reverse.cons hvw.symm).reverse
  have htrailRev : p.reverse.IsTrail := hp.reverse p
  have hnewRev : s(w, v) ∉ p.reverse.edges := by
    simpa [SimpleGraph.Walk.edges_reverse, Sym2.eq_swap] using! hnew
  have hq : q.IsTrail := (htrailRev.cons hvw.symm hnewRev).reverse _
  refine ⟨q, hq, ?_⟩
  simp [q]

private lemma maximal_trail_closed
    (heven : ∀ x, Even (G.degree x))
    {u v : V} (p : G.Walk u v) (hp : p.IsTrail)
    (hmax : ∀ {u' v' : V} (q : G.Walk u' v'), q.IsTrail → q.length ≤ p.length) :
    u = v := by
  by_contra huv
  obtain ⟨w, hvw, hnew⟩ := exists_unused_incident_of_open p hp heven huv
  obtain ⟨q, hq, hlen⟩ := extend_trail_at_end p hp hvw hnew
  have := hmax q hq
  omega

private lemma exists_unused_incident_of_not_eulerian
    (hG : G.Connected) {u : V} (p : G.Walk u u) (hp : p.IsTrail)
    (hne : ¬p.IsEulerian) :
    ∃ x y : V, x ∈ p.support ∧ G.Adj x y ∧ s(x, y) ∉ p.edges := by
  rw [SimpleGraph.Walk.isEulerian_iff] at hne
  push_neg at hne
  obtain ⟨e, heG, heNot⟩ := hne hp
  induction e using Sym2.inductionOn with
  | _ a b =>
      have hab : G.Adj a b := G.mem_edgeSet.mp heG
      by_cases ha : a ∈ p.support
      · exact ⟨a, b, ha, hab, heNot⟩
      by_cases hb : b ∈ p.support
      · exact ⟨b, a, hb, hab.symm, by simpa [Sym2.eq_swap] using! heNot⟩
      · obtain ⟨x, y, hx, hy, hxy⟩ :=
          reachable_crosses (P := {z | z ∈ p.support}) (hG u a)
            p.start_mem_support ha
        have hxyNew : s(x, y) ∉ p.edges := by
          intro hmem
          exact hy (p.snd_mem_support_of_mem_edges hmem)
        exact ⟨x, y, hx, hxy, hxyNew⟩

private lemma rotate_length {u x : V} (p : G.Walk u u) (hx : x ∈ p.support) :
    (p.rotate x hx).length = p.length := by
  have h := (p.rotate_edges x hx).perm.length_eq
  simpa only [SimpleGraph.Walk.length_edges] using! h

/-- Every finite connected graph in which all degrees are even has an Euler
circuit.  The proof selects a longest trail, uses parity to close it, and uses
rotation plus connectedness to rule out an unused edge. -/
theorem exists_eulerianCircuit_of_connected_even
    (hG : G.Connected) (heven : ∀ x, Even (G.degree x)) :
    ∃ u : V, ∃ p : G.Walk u u, p.IsEulerian := by
  obtain ⟨u, v, p, hp, hmax⟩ := exists_maximal_trail hG
  have huv : u = v := maximal_trail_closed heven p hp hmax
  subst v
  refine ⟨u, p, ?_⟩
  by_contra hne
  obtain ⟨x, y, hx, hxy, hnew⟩ :=
    exists_unused_incident_of_not_eulerian hG p hp hne
  let c : G.Walk x x := p.rotate x hx
  have hc : c.IsTrail := hp.rotate hx
  have hnewc : s(x, y) ∉ c.edges := by
    intro hmem
    exact hnew ((p.rotate_edges x hx).mem_iff.mp hmem)
  obtain ⟨q, hq, hqLen⟩ := extend_trail_at_end c hc hxy hnewc
  have hcle : c.length = p.length := rotate_length p hx
  have := hmax q hq
  omega

/-! The open case is obtained from the closed case by adjoining one new
vertex to the two odd vertices.  Cutting the resulting Euler circuit at that
new vertex gives the required open trail.  The following small incidence
identity is also used below to see that the new vertex occurs only at the two
ends of the circuit. -/

lemma countP_edges_incidence {u v : V} (p : G.Walk u v) (x : V) :
    p.edges.countP (x ∈ ·) =
      p.support.dropLast.count x + p.support.tail.count x := by
  induction p with
  | nil => simp
  | @cons a b c hab p ih =>
      have habne : a ≠ b := fun h => by subst b; exact G.loopless.irrefl a hab
      simp only [SimpleGraph.Walk.edges_cons, List.countP_cons,
        SimpleGraph.Walk.support_cons, List.tail_cons]
      rw [List.dropLast_cons_of_ne_nil (p.support_ne_nil)]
      simp only [List.count_cons, ih]
      have hc : p.support.count x =
          (if x = b then 1 else 0) + p.support.tail.count x := by
        rw [p.support_eq_cons]
        simp only [List.count_cons]
        by_cases hxb : x = b
        · subst x; simp [add_comm]
        · simp [hxb, Ne.symm hxb]
      rw [hc]
      by_cases hxa : x = a
      · subst x
        simp [Sym2.mem_iff, habne, Ne.symm habne,
          add_comm, add_left_comm, add_assoc]
      · by_cases hxb : x = b
        · subst x
          simp [Sym2.mem_iff, habne, Ne.symm habne,
            add_comm, add_left_comm, add_assoc]
        · have hmem : ¬x ∈ s(a, b) := by
            simpa [Sym2.mem_iff] using! not_or_intro hxa hxb
          simp [hmem, hxa, hxb, Ne.symm hxa, Ne.symm hxb,
            add_comm, add_left_comm, add_assoc]

/-- An Euler trail uses every incident edge exactly once.  This is the
degree-count form used by the W07 core encoder. -/
lemma Walk.IsEulerian.countP_edges_eq_degree {u v : V} {p : G.Walk u v}
    (hp : p.IsEulerian) (x : V) :
    p.edges.countP (x ∈ ·) = G.degree x := by
  rw [countP_incidence_eq_card p hp.isTrail x, hp.edgesFinset_eq,
    ← G.incidenceFinset_eq_filter, G.card_incidenceFinset_eq_degree]

private def twoOddAugment (G : SimpleGraph V) (u v : V) :
    SimpleGraph (Option V) where
  Adj a b :=
    match a, b with
    | some x, some y => G.Adj x y
    | none, some y => y = u ∨ y = v
    | some x, none => x = u ∨ x = v
    | none, none => False
  symm := ⟨by
    intro a b
    cases a <;> cases b <;> simp only
    · exact id
    · exact id
    · exact id
    · exact fun h => G.symm.symm _ _ h⟩
  loopless := ⟨by
    intro a
    cases a <;> simp⟩

@[simp] private lemma twoOddAugment_some_some (u v x y : V) :
    (twoOddAugment G u v).Adj (some x) (some y) ↔ G.Adj x y := Iff.rfl

@[simp] private lemma twoOddAugment_none_some (u v x : V) :
    (twoOddAugment G u v).Adj none (some x) ↔ x = u ∨ x = v := Iff.rfl

@[simp] private lemma twoOddAugment_some_none (u v x : V) :
    (twoOddAugment G u v).Adj (some x) none ↔ x = u ∨ x = v := Iff.rfl

private lemma twoOddAugment_connected (hG : G.Connected) {u v : V} (huv : u ≠ v) :
    (twoOddAugment G u v).Connected := by
  refine ⟨?_⟩
  intro a b
  let A := twoOddAugment G u v
  let f : G →g A :=
    ⟨some, fun {_ _} h => h⟩
  have hnu : A.Reachable none (some u) :=
    (show A.Adj none (some u) by simp [A]).reachable
  cases a with
  | none =>
      cases b with
      | none => exact SimpleGraph.Reachable.refl none
      | some y => exact hnu.trans ((hG u y).map f)
  | some x =>
      cases b with
      | none => exact (((hG x u).map f).trans hnu.symm)
      | some y => exact (hG x y).map f

private lemma twoOddAugment_degree_none {u v : V} (huv : u ≠ v) :
    (twoOddAugment G u v).degree none = 2 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  have h : (twoOddAugment G u v).neighborFinset none = {some u, some v} := by
    ext z
    cases z <;> simp [twoOddAugment, huv]
  rw [h]
  simp [huv]

private lemma twoOddAugment_neighborFinset_some {u v x : V} (huv : u ≠ v) :
    (twoOddAugment G u v).neighborFinset (some x) =
      if x = u ∨ x = v then
        insert none ((G.neighborFinset x).map
          ⟨some, Option.some_injective V⟩)
      else
        (G.neighborFinset x).map ⟨some, Option.some_injective V⟩ := by
  ext z
  cases z with
  | none => by_cases hx : x = u ∨ x = v <;> simp [twoOddAugment, hx]
  | some y => by_cases hx : x = u ∨ x = v <;> simp [twoOddAugment, hx]

private lemma twoOddAugment_degree_some {u v x : V} (huv : u ≠ v) :
    (twoOddAugment G u v).degree (some x) =
      G.degree x + if x = u ∨ x = v then 1 else 0 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree,
    twoOddAugment_neighborFinset_some (G := G) huv]
  split_ifs with hx
  · rw [Finset.card_insert_of_notMem]
    · simp [SimpleGraph.card_neighborFinset_eq_degree]
    · simp
  · simp [SimpleGraph.card_neighborFinset_eq_degree]

private lemma twoOddAugment_even {u v : V} (huv : u ≠ v)
    (hodd : ∀ x, Odd (G.degree x) ↔ x = u ∨ x = v) :
    ∀ z, Even ((twoOddAugment G u v).degree z) := by
  intro z
  cases z with
  | none =>
      rw [twoOddAugment_degree_none (G := G) huv]
      exact ⟨1, by omega⟩
  | some x =>
      rw [twoOddAugment_degree_some (G := G) huv]
      by_cases hx : x = u ∨ x = v
      · obtain ⟨k, hk⟩ := (hodd x).2 hx
        refine ⟨k + 1, ?_⟩
        simp only [if_pos hx]
        omega
      · have he : Even (G.degree x) := Nat.not_odd_iff_even.mp (mt (hodd x).1 hx)
        simpa [hx] using! he

private lemma support_tail_dropLast_eq {u v : V} (p : G.Walk u v)
    (hlen : 2 ≤ p.length) :
    p.tail.dropLast.support = p.support.tail.dropLast := by
  have hp : ¬p.Nil := by
    rw [SimpleGraph.Walk.nil_iff_length_eq]
    omega
  rw [SimpleGraph.Walk.dropLast,
    SimpleGraph.Walk.take_support_eq_support_take_succ,
    p.support_tail_of_not_nil hp, List.dropLast_eq_take]
  have ht := p.length_tail_add_one hp
  have hs : p.support.tail.length = p.length := by
    simp [List.length_tail, p.length_support]
  congr 1
  omega

private lemma edges_tail_dropLast_eq {u v : V} (p : G.Walk u v)
    (hlen : 2 ≤ p.length) :
    p.tail.dropLast.edges = p.edges.tail.dropLast := by
  have hp : ¬p.Nil := by
    rw [SimpleGraph.Walk.nil_iff_length_eq]
    omega
  rw [SimpleGraph.Walk.dropLast, SimpleGraph.Walk.edges_take,
    SimpleGraph.Walk.tail, SimpleGraph.Walk.edges_drop, List.dropLast_eq_take]
  have ht := p.length_tail_add_one hp
  have he : p.edges.tail.length = p.length - 1 := by
    rw [List.length_tail, p.length_edges]
  change List.take ((p.drop 1).length - 1) (List.drop 1 p.edges) =
    List.take (p.edges.tail.length - 1) p.edges.tail
  rw [show p.drop 1 = p.tail from rfl,
    show List.drop 1 p.edges = p.edges.tail by cases p.edges <;> rfl]
  congr 1
  omega

private lemma snd_ne_penultimate_of_closed_trail {u : V} (p : G.Walk u u)
    (hp : p.IsTrail) (hlen : 2 ≤ p.length) : p.snd ≠ p.penultimate := by
  cases p with
  | nil => simp at hlen
  | cons h q =>
      cases q with
      | nil => simp at hlen
      | cons h' r =>
          have hnodup := hp.edges_nodup
          simp only [SimpleGraph.Walk.edges_cons, List.nodup_cons] at hnodup
          intro heq
          apply hnodup.1
          have hn : ¬(SimpleGraph.Walk.cons h' r).Nil := by simp
          have hmem := (SimpleGraph.Walk.cons h' r).mk_penultimate_end_mem_edges
            hn
          simp only [SimpleGraph.Walk.snd_cons,
            SimpleGraph.Walk.penultimate_cons_cons] at heq
          rw [← heq] at hmem
          simpa [Sym2.eq_swap] using! hmem

/-- A finite connected graph with exactly two specified odd vertices has an
Euler trail between them. -/
theorem exists_eulerianTrail_of_connected_twoOdd
    (hG : G.Connected) {u v : V} (huv : u ≠ v)
    (hodd : ∀ x, Odd (G.degree x) ↔ x = u ∨ x = v) :
    ∃ p : G.Walk u v, p.IsEulerian := by
  let A := twoOddAugment G u v
  obtain ⟨z, c, hc⟩ := exists_eulerianCircuit_of_connected_even
    (G := A) (twoOddAugment_connected hG huv) (twoOddAugment_even huv hodd)
  have hauxEdge : s(none, some u) ∈ A.edgeSet := by
    rw [SimpleGraph.mem_edgeSet]
    simp [A]
  have hnone : none ∈ c.support :=
    c.fst_mem_support_of_mem_edges ((hc.mem_edges_iff).2 hauxEdge)
  let d : A.Walk none none := c.rotate none hnone
  have hd : d.IsEulerian := by
    rw [SimpleGraph.Walk.isEulerian_iff]
    constructor
    · exact hc.isTrail.rotate hnone
    · intro e he
      exact (c.rotate_edges none hnone).mem_iff.mpr ((hc.mem_edges_iff).2 he)
  have hdinc : d.edges.countP (none ∈ ·) = 2 := by
    rw [countP_incidence_eq_card d hd.isTrail none, hd.edgesFinset_eq,
      ← A.incidenceFinset_eq_filter, A.card_incidenceFinset_eq_degree,
      twoOddAugment_degree_none (G := G) huv]
  have hdlen : 2 ≤ d.length := by
    have hlen : d.length = A.edgeFinset.card := by
      rw [← hd.edgesFinset_eq]
      change d.length = d.edges.length
      exact d.length_edges.symm
    have hincsub := A.incidenceFinset_subset none
    have hdeg : (A.incidenceFinset none).card = 2 := by
      rw [SimpleGraph.card_incidenceFinset_eq_degree,
        twoOddAugment_degree_none (G := G) huv]
    rw [hlen]
    exact hdeg ▸ Finset.card_le_card hincsub
  have hdnon : ¬d.Nil := by
    rw [SimpleGraph.Walk.nil_iff_length_eq]
    omega
  have hinner : ∀ x ∈ d.support.tail.dropLast, x ≠ none := by
    intro x hx hxn
    subst x
    have hpos : 0 < d.support.tail.dropLast.count none :=
      List.count_pos_iff.mpr hx
    have hinc := countP_edges_incidence d none
    have hs1 : d.support.dropLast = none :: d.support.tail.dropLast := by
      calc
        d.support.dropLast = (none :: d.support.tail).dropLast :=
          congrArg List.dropLast d.support_eq_cons
        _ = none :: d.support.tail.dropLast :=
          List.dropLast_cons_of_ne_nil (by
            have hl : d.support.tail.length = d.length := by
              simp [List.length_tail, d.length_support]
            intro ht
            rw [ht] at hl
            simp at hl
            omega)
    have hs2 : d.support.tail = d.support.tail.dropLast ++ [none] := by
      have ht : d.support.tail ≠ [] := by
        have hl : d.support.tail.length = d.length := by
          simp [List.length_tail, d.length_support]
        intro ht
        rw [ht] at hl
        simp at hl
        omega
      calc
        d.support.tail = d.support.tail.dropLast ++
            [d.support.tail.getLast ht] := (List.dropLast_append_getLast ht).symm
        _ = d.support.tail.dropLast ++ [none] := by
          congr 2
          have hopt := congrArg List.getLast? d.support_eq_cons
          have hend : d.support.getLast? = some none := by
            rw [List.getLast?_eq_getLast (l := d.support) d.support_ne_nil]
            simp
          rw [hend] at hopt
          simpa [List.getLast?_eq_getLast, ht] using! hopt.symm
    let cnt : List (Option V) → ℕ := fun l =>
      @List.count (Option V) (@instBEqOfDecidableEq (Option V) inferInstance) none l
    rw [hdinc] at hinc
    change 2 = cnt d.support.dropLast + cnt d.support.tail at hinc
    have hc1 : cnt d.support.dropLast =
        1 + cnt d.support.tail.dropLast := by
      calc
        cnt d.support.dropLast = cnt (none :: d.support.tail.dropLast) :=
          congrArg cnt hs1
        _ = 1 + cnt d.support.tail.dropLast := by simp [cnt, add_comm]
    have hc2 : cnt d.support.tail =
        cnt d.support.tail.dropLast + 1 := by
      calc
        cnt d.support.tail = cnt (d.support.tail.dropLast ++ [none]) :=
          congrArg cnt hs2
        _ = cnt d.support.tail.dropLast + 1 := by simp [cnt]
    have hpos' : 0 < cnt d.support.tail.dropLast :=
      (@List.count_pos_iff (Option V)
        (@instBEqOfDecidableEq (Option V) inferInstance) inferInstance none
        d.support.tail.dropLast).2 hx
    have htotal : 2 =
        (1 + cnt d.support.tail.dropLast) +
          (cnt d.support.tail.dropLast + 1) := by
      calc
        2 = cnt d.support.dropLast + cnt d.support.tail := by
          exact hinc
        _ = _ := congrArg₂ (· + ·) hc1 hc2
    clear hinc
    omega
  let q := d.tail.dropLast
  have hqSupp : ∀ x ∈ q.support, x ≠ none := by
    intro x hx
    exact hinner x (by simpa [q, support_tail_dropLast_eq d hdlen] using! hx)
  have hfirst : A.Adj none d.snd := d.adj_snd hdnon
  have hdlastNon : ¬d.reverse.Nil := by simpa using! hdnon
  have hlast : A.Adj d.penultimate none := d.adj_penultimate hdnon
  obtain ⟨u', hu'⟩ : ∃ u', d.snd = some u' := by
    cases hds : d.snd with
    | none => simp [A, hds] at hfirst
    | some u' => exact ⟨u', rfl⟩
  obtain ⟨v', hv'⟩ : ∃ v', d.penultimate = some v' := by
    cases hdp : d.penultimate with
    | none => simp [A, hdp] at hlast
    | some v' => exact ⟨v', rfl⟩
  have huvor : (u' = u ∧ v' = v) ∨ (u' = v ∧ v' = u) := by
    have hfu : u' = u ∨ u' = v := by simpa [A, hu'] using! hfirst
    have hlv : v' = u ∨ v' = v := by simpa [A, hv'] using! hlast
    have hne : u' ≠ v' := by
      intro heq
      apply snd_ne_penultimate_of_closed_trail d hd.isTrail hdlen
      rw [hu', hv', heq]
    rcases hfu with rfl | rfl <;> rcases hlv with rfl | rfl <;> simp_all
  let sV : Set (Option V) := {x | x ≠ none}
  let qi := q.induce sV hqSupp
  let oe : {x : Option V // x ≠ none} ≃ V :=
    { toFun := fun x => match h : x.1 with
        | some a => a
        | none => False.elim (x.2 h)
      invFun := fun a => ⟨some a, by simp⟩
      left_inv := by
        intro x
        rcases x with ⟨_ | a, ha⟩
        · exact False.elim (ha rfl)
        · rfl
      right_inv := by intro a; rfl }
  let back : A.induce sV →g G :=
    ⟨oe, by
      intro a b hab
      rcases a with ⟨_ | a, ha⟩
      · exact False.elim (ha rfl)
      · rcases b with ⟨_ | b, hb⟩
        · exact False.elim (hb rfl)
        · exact hab⟩
  have hbackinj : Function.Injective back := oe.injective
  let p' := qi.map back
  have hqTrail : q.IsTrail := by
    constructor
    rw [edges_tail_dropLast_eq d hdlen]
    have hdrop : ∀ l : List (Sym2 (Option V)), l.Nodup → l.dropLast.Nodup := by
      intro l hl
      induction l with
      | nil => simp
      | cons a l ih =>
          cases l with
          | nil => simp
          | cons b t =>
              rw [List.dropLast_cons_of_ne_nil (by simp)]
              rw [List.nodup_cons] at hl
              rw [List.nodup_cons]
              constructor
              · exact fun ha => hl.1 (List.mem_of_mem_dropLast ha)
              · exact ih hl.2
    exact hdrop _ hd.isTrail.edges_nodup.tail
  have hqiTrail : qi.IsTrail := by
    apply (SimpleGraph.Walk.map_isTrail_iff_of_injective
      (f := (SimpleGraph.Embedding.induce (G := A) sV).toHom)
      (p := qi) (SimpleGraph.Embedding.induce (G := A) sV).injective).mp
    simpa [qi] using! hqTrail
  have hp'Trail : p'.IsTrail :=
    (SimpleGraph.Walk.map_isTrail_iff_of_injective hbackinj).2
      hqiTrail
  have hp'Euler : p'.IsEulerian := by
    apply hp'Trail.isEulerian_of_forall_mem
    intro e he
    induction e using Sym2.inductionOn with
    | _ a b =>
      have heA : s(some a, some b) ∈ A.edgeSet := by
        rw [SimpleGraph.mem_edgeSet] at he ⊢
        simpa [A] using! he
      have hed : s(some a, some b) ∈ d.edges := (hd.mem_edges_iff).2 heA
      have heq : s(some a, some b) ∈ q.edges := by
        rw [edges_tail_dropLast_eq d hdlen]
        have hdges : d.edges ≠ [] := by
          intro he
          have hl := d.length_edges
          rw [he] at hl
          simp at hl
          omega
        have hhead : d.edges.head hdges = s(none, d.snd) :=
          d.head_edges_eq_mk_start_snd hdges
        have htailmem : s(some a, some b) ∈ d.edges.tail := by
          cases heds : d.edges with
          | nil => exact False.elim (hdges heds)
          | cons e l =>
              simp only [heds, List.tail_cons, List.mem_cons] at hed ⊢
              rcases hed with hed | hed
              · have hinc : none ∈ s(some a, some b) := by
                  have hehead : e = s(none, d.snd) := by
                    simpa [heds] using! hhead
                  rw [hed, hehead]
                  simp
                simpa using! hinc
              · exact hed
        have htailne : d.edges.tail ≠ [] := by
          have htl : d.edges.tail.length = d.length - 1 := by
            rw [List.length_tail, d.length_edges]
          intro ht
          have hz : d.length - 1 = 0 := by
            symm
            simpa [ht] using! htl
          omega
        apply List.mem_dropLast_of_mem_of_ne_getLast htailmem
        intro heqLast
        have hget : d.edges.tail.getLast htailne =
            d.edges.getLast hdges := List.getLast_tail htailne
        have hlastEdge : d.edges.getLast hdges = s(d.penultimate, none) :=
          d.getLast_edges_eq_mk_penultimate_end hdges
        have hinc : none ∈ s(some a, some b) := by
          rw [heqLast, hget, hlastEdge]
          simp
        simpa using! hinc
      have heqi : s(⟨some a, Option.some_ne_none a⟩,
          ⟨some b, Option.some_ne_none b⟩) ∈ qi.edges := by
        have hemap : s(some a, some b) ∈
            (qi.map (SimpleGraph.Embedding.induce (G := A) sV).toHom).edges := by
          rw [show qi.map (SimpleGraph.Embedding.induce (G := A) sV).toHom = q by
            simpa [qi] using! q.map_induce hqSupp]
          exact heq
        rw [SimpleGraph.Walk.edges_map] at hemap
        obtain ⟨e, he, hee⟩ := List.mem_map.mp hemap
        have hee' : e = s(⟨some a, Option.some_ne_none a⟩,
            ⟨some b, Option.some_ne_none b⟩) := by
          apply (Sym2.map.injective
            (SimpleGraph.Embedding.induce (G := A) sV).injective)
          simpa using! hee
        simpa [hee'] using! he
      rw [show p'.edges = qi.edges.map (Sym2.map back) by
        simpa [p'] using! (SimpleGraph.Walk.edges_map (f := back) qi)]
      exact List.mem_map.mpr ⟨_, heqi, by rfl⟩
  have hpen : d.tail.penultimate = d.penultimate := by
    change d.tail.getVert (d.tail.length - 1) = d.getVert (d.length - 1)
    rw [d.getVert_tail]
    congr 1
    have := d.length_tail_add_one hdnon
    omega
  rcases huvor with huv' | hvu'
  · have hsu : d.snd = some u := hu'.trans (congrArg some huv'.1)
    have hev : d.penultimate = some v := hv'.trans (congrArg some huv'.2)
    have hs : back ⟨d.snd, by exact hqSupp _ q.start_mem_support⟩ = u := by
      change oe ⟨d.snd, _⟩ = u
      have hsub : (⟨d.snd, by exact hqSupp _ q.start_mem_support⟩ :
          {x : Option V // x ≠ none}) = ⟨some u, Option.some_ne_none u⟩ :=
        Subtype.ext hsu
      rw [hsub]
      rfl
    have he : back ⟨d.tail.penultimate, by exact hqSupp _ q.end_mem_support⟩ = v := by
      change oe ⟨d.tail.penultimate, _⟩ = v
      have hend : d.tail.penultimate = some v := hpen.trans hev
      have hsub : (⟨d.tail.penultimate, by exact hqSupp _ q.end_mem_support⟩ :
          {x : Option V // x ≠ none}) = ⟨some v, Option.some_ne_none v⟩ :=
        Subtype.ext hend
      rw [hsub]
      rfl
    refine ⟨p'.copy hs he, ?_⟩
    intro e heG
    simpa using! hp'Euler e heG
  · have hsv : d.snd = some v := hu'.trans (congrArg some hvu'.1)
    have heu : d.penultimate = some u := hv'.trans (congrArg some hvu'.2)
    have hs : back ⟨d.snd, by exact hqSupp _ q.start_mem_support⟩ = v := by
      change oe ⟨d.snd, _⟩ = v
      have hsub : (⟨d.snd, by exact hqSupp _ q.start_mem_support⟩ :
          {x : Option V // x ≠ none}) = ⟨some v, Option.some_ne_none v⟩ :=
        Subtype.ext hsv
      rw [hsub]
      rfl
    have he : back ⟨d.tail.penultimate, by exact hqSupp _ q.end_mem_support⟩ = u := by
      change oe ⟨d.tail.penultimate, _⟩ = u
      have hend : d.tail.penultimate = some u := hpen.trans heu
      have hsub : (⟨d.tail.penultimate, by exact hqSupp _ q.end_mem_support⟩ :
          {x : Option V // x ≠ none}) = ⟨some u, Option.some_ne_none u⟩ :=
        Subtype.ext hend
      rw [hsub]
      rfl
    let pr : G.Walk v u := p'.copy hs he
    have hpr : pr.IsEulerian := by
      intro e heG
      simpa [pr] using! hp'Euler e heG
    refine ⟨pr.reverse, ?_⟩
    rw [SimpleGraph.Walk.isEulerian_iff]
    constructor
    · exact hpr.isTrail.reverse _
    · intro e heG
      simpa using! (hpr.mem_edges_iff).2 heG

end SimpleGraph
end
end Erdos745.WrapUp.Proofs.Internal.W07_SUBCRIT_Euler


/-!
# Finite witness reduction for the all-order subcritical bound

The graph-theoretic content is isolated in `BicyclicCoreCover`: bad graphs are
covered by labelled cores of size `v`, every core has `v+1` edges, and the
number of cores is controlled by a constant multiple of `v^2 (n)_v`.

This file proves the remaining finite-probability calculation from that exact
cover interface.  In particular, the loss caused by replacing the exact
hypergeometric product by elementary binomial bounds is paid uniformly by the
assumption `4/n <= e`; the resulting contraction is `1-e/4`.
-/

namespace Erdos745.WrapUp.Proofs.Internal.W07_SUBCRIT_Finite

open Erdos745.WrapUp
open scoped BigOperators Sym2
open Finset

noncomputable section
attribute [local instance] Classical.propDecidable

private lemma edge_card_le_capacity (n : ℕ) :
    Fintype.card (Edge n) ≤ capacity n := by
  let f : Edge n → {a : Sym2 (Fin n) // ¬ a.IsDiag} := fun e =>
    ⟨s(e.1.1, e.1.2), by simpa [Sym2.mk_isDiag_iff] using! ne_of_lt e.2⟩
  have hf : Function.Injective f := by
    intro e e' h
    apply Subtype.ext
    simp only [f, Subtype.mk.injEq] at h
    rw [Sym2.eq_iff] at h
    rcases h with h | h
    · exact Prod.ext h.1 h.2
    · have hback : e.1.2 < e.1.1 := by
        rw [h.2, h.1]
        exact e'.2
      exact (lt_asymm e.2 hback).elim
  calc
    Fintype.card (Edge n) ≤ Fintype.card {a : Sym2 (Fin n) // ¬ a.IsDiag} :=
      Fintype.card_le_of_injective f hf
    _ = capacity n := by
      simpa only [capacity, Fintype.card_fin] using!
        (Sym2.card_subtype_not_diag (α := Fin n))

private lemma graph_card_le_capacity {n : ℕ} (F : Graph n) :
    F.card ≤ capacity n := by
  calc
    F.card ≤ (univ : Finset (Edge n)).card := card_le_card (by simp)
    _ = Fintype.card (Edge n) := card_univ
    _ ≤ capacity n := edge_card_le_capacity n

private lemma card_inter_eq_right_iff {n : ℕ} (G F : Graph n) :
    (G ∩ F).card = F.card ↔ F ⊆ G := by
  constructor
  · intro h
    have heq : G ∩ F = F :=
      eq_of_subset_of_card_le inter_subset_right (by simp [h])
    exact inter_eq_right.mp heq
  · intro h
    exact congrArg card (inter_eq_right.mpr h)

private lemma empty_pattern_prob
    (hEnum : FiniteEnumerationStatement) {n M : ℕ}
    (hM : M ≤ capacity n) :
    probM n M (patternEvent ∅ ∅) = 1 := by
  have h := hEnum.1 n M hM
  unfold probM
  rw [show (fixedGraphs n M).filter (patternEvent ∅ ∅) = fixedGraphs n M by
    ext G
    simp [patternEvent]]
  simpa [expectM] using! h

theorem prescribed_probability
    (hEnum : FiniteEnumerationStatement) {n M : ℕ}
    (hM : M ≤ capacity n) (F : Graph n) :
    probM n M (fun G => F ⊆ G) =
      (M.choose F.card : ℝ) / (capacity n).choose F.card := by
  have hbase : 0 < probM n M (patternEvent ∅ ∅) := by
    rw [empty_pattern_prob hEnum hM]
    norm_num
  have h := hEnum.2.1 n M ∅ ∅ F hM (by simp) (by simp) hbase F.card
  have hF : F.card ≤ capacity n := graph_card_le_capacity F
  rw [show conditionalProbM n M (patternEvent ∅ ∅)
      (fun G => (G ∩ F).card = F.card) =
      probM n M (fun G => F ⊆ G) by
    simp only [conditionalProbM, empty_pattern_prob hEnum hM, div_one]
    apply congrArg (probM n M)
    funext G
    apply propext
    simp only [patternEvent, empty_subset, disjoint_empty_left, true_and, and_self,
      card_inter_eq_right_iff]] at h
  simpa [hypergeomMass, hM, hF] using! h

/-- A concrete finite family for each ambient order and core order. -/
abbrev CoreFamily := ∀ n _v : ℕ, Finset (Graph n)

/-- Exact graph-theoretic interface needed by the probability calculation.
The numerical constant `8` allows the three ordered bicyclic shapes to be
encoded by an injection, two cut positions, and harmless endpoint padding. -/
def BicyclicCoreCover (C : CoreFamily) : Prop :=
  (∀ n v F, F ∈ C n v → F.card = v + 1) ∧
  (∀ n v, (C n v).card ≤ 8 * v ^ 2 * n.descFactorial v) ∧
  (∀ n (G : Graph n), ¬ noComplex G →
    ∃ v ∈ Icc 4 n, ∃ F ∈ C n v, F ⊆ G)

def BicyclicWitnessBound : Prop :=
  ∀ (n M : ℕ) (e : ℝ), 2 ≤ n → M ≤ capacity n →
    0 < e → 4 / (n : ℝ) ≤ e → degreeAt n M ≤ 1 - e →
    probM n M (fun G => ¬ noComplex G) ≤
      8 / (n : ℝ) *
        ∑ v ∈ Icc 4 n, (v : ℝ) ^ 2 * (1 - e / 4) ^ v

set_option maxHeartbeats 800000 in
private lemma probability_iUnion_le {n M : ℕ} (s : Finset ℕ)
    (C : ℕ → Finset (Graph n)) (A : Graph n → Prop)
    (hcover : ∀ G, A G → ∃ v ∈ s, ∃ F ∈ C v, F ⊆ G) :
    probM n M A ≤
      ∑ v ∈ s, ∑ F ∈ C v, probM n M (fun G => F ⊆ G) := by
  let U : Finset (Graph n) := s.biUnion fun v =>
    (C v).biUnion fun F => (fixedGraphs n M).filter fun G => F ⊆ G
  have hsub : (fixedGraphs n M).filter A ⊆ U := by
    intro G hG
    have hAG : A G := (mem_filter.mp hG).2
    obtain ⟨v, hv, F, hF, hFG⟩ := hcover G hAG
    simp only [U, mem_biUnion]
    exact ⟨v, hv, F, hF, mem_filter.mpr ⟨(mem_filter.mp hG).1, hFG⟩⟩
  have hU : U.card ≤
      ∑ v ∈ s, ∑ F ∈ C v,
        ((fixedGraphs n M).filter fun G => F ⊆ G).card := by
    calc
      U.card ≤ ∑ v ∈ s,
          ((C v).biUnion fun F =>
            (fixedGraphs n M).filter fun G => F ⊆ G).card :=
        card_biUnion_le
      _ ≤ ∑ v ∈ s, ∑ F ∈ C v,
          ((fixedGraphs n M).filter fun G => F ⊆ G).card := by
        exact sum_le_sum fun v hv => card_biUnion_le
  have hnum : (((fixedGraphs n M).filter A).card : ℝ) ≤
      ∑ v ∈ s, ∑ F ∈ C v,
        (((fixedGraphs n M).filter fun G => F ⊆ G).card : ℝ) := by
    exact_mod_cast (card_le_card hsub |>.trans hU)
  change (((fixedGraphs n M).filter A).card : ℝ) /
      ((fixedGraphs n M).card : ℝ) ≤ _
  calc
    (((fixedGraphs n M).filter A).card : ℝ) /
        ((fixedGraphs n M).card : ℝ) ≤
      (∑ v ∈ s, ∑ F ∈ C v,
        (((fixedGraphs n M).filter fun G => F ⊆ G).card : ℝ)) /
          ((fixedGraphs n M).card : ℝ) :=
      div_le_div_of_nonneg_right hnum (by positivity)
    _ = ∑ v ∈ s, ∑ F ∈ C v,
        probM n M (fun G => F ⊆ G) := by
      rw [sum_div]
      apply sum_congr rfl
      intro v hv
      rw [sum_div]
      apply sum_congr rfl
      intro F hF
      unfold probM
      apply congrArg (fun q : ℕ => (q : ℝ) / ((fixedGraphs n M).card : ℝ))
      apply congrArg Finset.card
      ext G
      simp

private lemma choose_ratio_le_pow (M N d : ℕ) (hbase : 0 < N + 1 - d) :
    (M.choose d : ℝ) / (N.choose d : ℝ) ≤
      ((M : ℝ) / (N + 1 - d : ℕ)) ^ d := by
  have hupper : (M.choose d : ℝ) ≤ (M : ℝ) ^ d / (d.factorial : ℝ) :=
    Nat.choose_le_pow_div d M
  have hlower : ((N + 1 - d : ℕ) : ℝ) ^ d / (d.factorial : ℝ) ≤
      (N.choose d : ℝ) := Nat.pow_le_choose d N
  have hlowpos : 0 < ((N + 1 - d : ℕ) : ℝ) ^ d / (d.factorial : ℝ) := by
    positivity
  calc
    (M.choose d : ℝ) / (N.choose d : ℝ) ≤
        ((M : ℝ) ^ d / (d.factorial : ℝ)) /
          (((N + 1 - d : ℕ) : ℝ) ^ d / (d.factorial : ℝ)) := by
      exact div_le_div₀ (by positivity) hupper hlowpos hlower
    _ = ((M : ℝ) / (N + 1 - d : ℕ)) ^ d := by
      rw [div_pow]
      field_simp

private lemma order_lt_capacity (n : ℕ) (hn : 4 ≤ n) : n < capacity n := by
  rw [capacity, Nat.choose_two_right]
  apply lt_of_lt_of_le (Nat.lt_succ_self n)
  apply (Nat.le_div_iff_mul_le (by norm_num)).2
  calc
    (n + 1) * 2 ≤ n * 3 := by omega
    _ ≤ n * (n - 1) := Nat.mul_le_mul_left n (by omega)

private lemma capacity_sub_core_pos (n v : ℕ) (hn : 4 ≤ n) (hv : v ≤ n) :
    0 < capacity n - v := by
  have := order_lt_capacity n hn
  omega

private lemma capacity_add_one_sub_succ (n v : ℕ) (hv : v ≤ capacity n) :
    capacity n + 1 - (v + 1) = capacity n - v := by omega

private lemma denominator_contraction_real (x m y e : ℝ)
    (hx : 4 ≤ x) (hyx : y ≤ x)
    (hm0 : 0 ≤ m)
    (heps : 4 / x ≤ e) (hdeg : 2 * m / x ≤ 1 - e) :
    x * (m / (x * (x - 1) / 2 - y)) ≤ 1 - e / 4 := by
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hden : 0 < x * (x - 1) / 2 - y := by nlinarith
  have hd : 2 * m ≤ x * (1 - e) := by
    simpa [mul_comm] using! (div_le_iff₀ hx0).mp hdeg
  have he4 : 4 ≤ e * x := (div_le_iff₀ hx0).mp heps
  have he_one : e ≤ 1 := by
    have : 0 ≤ 2 * m / x := div_nonneg (mul_nonneg (by norm_num) hm0) hx0.le
    linarith
  rw [show x * (m / (x * (x - 1) / 2 - y)) =
      (x * m) / (x * (x - 1) / 2 - y) by ring]
  apply (div_le_iff₀ hden).2
  nlinarith [mul_nonneg (sub_nonneg.mpr he_one)
    (sub_nonneg.mpr (by nlinarith : 3 ≤ x))]

private lemma denominator_contraction (n M v : ℕ) (e : ℝ)
    (hn : 4 ≤ n) (hv : v ≤ n)
    (heps : 4 / (n : ℝ) ≤ e) (hdeg : degreeAt n M ≤ 1 - e) :
    (n : ℝ) * ((M : ℝ) / (capacity n - v : ℕ)) ≤ 1 - e / 4 := by
  have hvCap : v ≤ capacity n := hv.trans (order_lt_capacity n hn).le
  have hcast : ((capacity n - v : ℕ) : ℝ) =
      (n : ℝ) * ((n : ℝ) - 1) / 2 - v := by
    rw [Nat.cast_sub hvCap, capacity, Nat.cast_choose_two]
  rw [hcast]
  simpa [degreeAt] using!
    denominator_contraction_real (n : ℝ) (M : ℝ) (v : ℝ) e
      (by exact_mod_cast hn) (by exact_mod_cast hv)
      (by positivity) heps hdeg

private lemma prescribed_probability_le_core_power
    (hEnum : FiniteEnumerationStatement) {n M v : ℕ}
    (hn : 4 ≤ n) (hM : M ≤ capacity n) (hv : v ≤ n)
    (F : Graph n) (hcard : F.card = v + 1) :
    probM n M (fun G => F ⊆ G) ≤
      ((M : ℝ) / (capacity n - v : ℕ)) ^ (v + 1) := by
  rw [prescribed_probability hEnum hM F, hcard]
  have hvCap : v ≤ capacity n := hv.trans (order_lt_capacity n hn).le
  have hdCap : v + 1 ≤ capacity n := by
    have := order_lt_capacity n hn
    omega
  rw [← capacity_add_one_sub_succ n v hvCap]
  exact choose_ratio_le_pow M (capacity n) (v + 1)
    (by simpa [capacity_add_one_sub_succ n v hvCap] using!
      capacity_sub_core_pos n v hn hv)

private lemma core_term_bound (n M v : ℕ) (e : ℝ)
    (hn : 4 ≤ n) (hvn : v ≤ n)
    (heps : 4 / (n : ℝ) ≤ e) (hdeg : degreeAt n M ≤ 1 - e) :
    (n.descFactorial v : ℝ) *
        ((M : ℝ) / (capacity n - v : ℕ)) ^ (v + 1) ≤
      (1 / (n : ℝ)) * (1 - e / 4) ^ v := by
  have hn0 : 0 < (n : ℝ) := by positivity
  have he_one : e ≤ 1 := by
    have hd0 : 0 ≤ degreeAt n M := by unfold degreeAt; positivity
    linarith
  have hr0 : 0 ≤ 1 - e / 4 := by linarith
  have he0 : 0 ≤ e := by
    have : 0 ≤ 4 / (n : ℝ) := by positivity
    linarith
  have hr1 : 1 - e / 4 ≤ 1 := by linarith
  have hp0 : 0 ≤ (M : ℝ) / (capacity n - v : ℕ) := by positivity
  have hfall : (n.descFactorial v : ℝ) ≤ (n : ℝ) ^ v := by
    exact_mod_cast Nat.descFactorial_le_pow n v
  have hq := denominator_contraction n M v e hn hvn heps hdeg
  have hq0 : 0 ≤ (n : ℝ) * ((M : ℝ) / (capacity n - v : ℕ)) := by positivity
  have hpw :
      ((n : ℝ) * ((M : ℝ) / (capacity n - v : ℕ))) ^ (v + 1) ≤
        (1 - e / 4) ^ (v + 1) :=
    pow_le_pow_left₀ hq0 hq (v + 1)
  calc
    (n.descFactorial v : ℝ) *
        ((M : ℝ) / (capacity n - v : ℕ)) ^ (v + 1) ≤
      (n : ℝ) ^ v *
        ((M : ℝ) / (capacity n - v : ℕ)) ^ (v + 1) := by
      exact mul_le_mul_of_nonneg_right hfall (pow_nonneg hp0 _)
    _ = (1 / (n : ℝ)) *
        ((n : ℝ) * ((M : ℝ) / (capacity n - v : ℕ))) ^ (v + 1) := by
      field_simp
      ring
    _ ≤ (1 / (n : ℝ)) * (1 - e / 4) ^ (v + 1) := by
      exact mul_le_mul_of_nonneg_left hpw (by positivity)
    _ ≤ (1 / (n : ℝ)) * (1 - e / 4) ^ v := by
      apply mul_le_mul_of_nonneg_left
      · rw [pow_succ]
        exact mul_le_of_le_one_right (pow_nonneg hr0 v) hr1
      · positivity

/-- The complete fixed-size probability calculation.  Only the finite
graph-theoretic cover remains to establish `BicyclicCoreCover`. -/
theorem bicyclicWitnessBound_of_cover (hEnum : FiniteEnumerationStatement)
    (C : CoreFamily) (hC : BicyclicCoreCover C) : BicyclicWitnessBound := by
  intro n M e hn hM he heps hdeg
  have hd0 : 0 ≤ degreeAt n M := by unfold degreeAt; positivity
  have he_one : e ≤ 1 := by linarith
  have h4r : (4 : ℝ) ≤ n := by
    have hn0 : 0 < (n : ℝ) := by positivity
    exact (div_le_one hn0).mp (heps.trans he_one)
  have h4n : 4 ≤ n := by exact_mod_cast h4r
  have hunion := probability_iUnion_le (n := n) (M := M) (Icc 4 n) (C n)
    (fun G => ¬ noComplex G) (fun G hG => hC.2.2 n G hG)
  calc
    probM n M (fun G => ¬ noComplex G) ≤
        ∑ v ∈ Icc 4 n, ∑ F ∈ C n v,
          probM n M (fun G => F ⊆ G) := hunion
    _ ≤ ∑ v ∈ Icc 4 n,
        (8 * (v : ℝ) ^ 2 * (n.descFactorial v : ℝ)) *
          (((M : ℝ) / (capacity n - v : ℕ)) ^ (v + 1)) := by
      apply sum_le_sum
      intro v hv
      have hv' := mem_Icc.mp hv
      calc
        (∑ F ∈ C n v, probM n M (fun G => F ⊆ G)) ≤
            ∑ _F ∈ C n v,
              (((M : ℝ) / (capacity n - v : ℕ)) ^ (v + 1)) := by
          apply sum_le_sum
          intro F hF
          exact prescribed_probability_le_core_power hEnum h4n hM hv'.2 F
            (hC.1 n v F hF)
        _ = ((C n v).card : ℝ) *
            (((M : ℝ) / (capacity n - v : ℕ)) ^ (v + 1)) := by simp
        _ ≤ (8 * (v : ℝ) ^ 2 * (n.descFactorial v : ℝ)) *
            (((M : ℝ) / (capacity n - v : ℕ)) ^ (v + 1)) := by
          gcongr
          exact_mod_cast hC.2.1 n v
    _ ≤ ∑ v ∈ Icc 4 n,
        8 * (v : ℝ) ^ 2 * ((1 / (n : ℝ)) * (1 - e / 4) ^ v) := by
      apply sum_le_sum
      intro v hv
      have hv' := mem_Icc.mp hv
      have ht := core_term_bound n M v e h4n hv'.2 heps hdeg
      nlinarith [mul_nonneg (by positivity : 0 ≤ 8 * (v : ℝ) ^ 2)
        (sub_nonneg.mpr ht)]
    _ = 8 / (n : ℝ) *
        ∑ v ∈ Icc 4 n, (v : ℝ) ^ 2 * (1 - e / 4) ^ v := by
      rw [Finset.mul_sum]
      apply sum_congr rfl
      intro v hv
      ring

end
end Erdos745.WrapUp.Proofs.Internal.W07_SUBCRIT_Finite


namespace Erdos745.WrapUp.Proofs.Internal.W07_SUBCRIT_Cover

open Erdos745.WrapUp
open Erdos745.WrapUp.Proofs.Internal.W01_ENUM_Trees
open Erdos745.WrapUp.Proofs.Internal.W07_SUBCRIT_Finite
open Erdos745.WrapUp.Proofs.Internal.W07_SUBCRIT_Euler
open Finset
open scoped Sym2

noncomputable section
attribute [local instance] Classical.propDecidable

structure CoreCode (n v : ℕ) where
  labels : Fin v ↪ Fin n
  first : Fin v
  last : Fin v
deriving Fintype, DecidableEq

def CoreCode.equivProd (n v : ℕ) :
    CoreCode n v ≃ ((Fin v ↪ Fin n) × Fin v × Fin v) where
  toFun c := (c.labels, c.first, c.last)
  invFun c := ⟨c.1, c.2.1, c.2.2⟩
  left_inv c := by cases c; rfl
  right_inv c := by rcases c with ⟨f, i, j⟩; rfl

def CoreCode.vertexList {n v : ℕ} (c : CoreCode n v) : List (Fin n) :=
  c.labels c.first :: List.ofFn c.labels ++ [c.labels c.last]

def CoreCode.edgeList {n v : ℕ} (c : CoreCode n v) : List (Sym2 (Fin n)) :=
  List.zipWith (s(·, ·)) c.vertexList c.vertexList.tail

def CoreCode.decode {n v : ℕ} (c : CoreCode n v) : Graph n :=
  (univ : Finset (Edge n)).filter fun e =>
    s(e.1.1, e.1.2) ∈ c.edgeList

def coreFamily (n v : ℕ) : Finset (Graph n) :=
  ((univ : Finset (CoreCode n v)).filter fun c => c.decode.card = v + 1).image
    CoreCode.decode

lemma mem_coreFamily_card {n v : ℕ} {F : Graph n} (hF : F ∈ coreFamily n v) :
    F.card = v + 1 := by
  rw [coreFamily, mem_image] at hF
  obtain ⟨c, hc, rfl⟩ := hF
  exact (mem_filter.mp hc).2

lemma card_coreCode (n v : ℕ) :
    Fintype.card (CoreCode n v) = n.descFactorial v * v ^ 2 := by
  rw [Fintype.card_congr (CoreCode.equivProd n v)]
  simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_embedding_eq]
  ring

lemma card_coreFamily (n v : ℕ) :
    (coreFamily n v).card ≤ 8 * v ^ 2 * n.descFactorial v := by
  calc
    (coreFamily n v).card ≤
        (((univ : Finset (CoreCode n v)).filter fun c =>
          c.decode.card = v + 1)).card := card_image_le
    _ ≤ (univ : Finset (CoreCode n v)).card :=
      card_le_card (filter_subset _ _)
    _ = Fintype.card (CoreCode n v) := card_univ
    _ = n.descFactorial v * v ^ 2 := card_coreCode n v
    _ ≤ 8 * v ^ 2 * n.descFactorial v := by
      have h : n.descFactorial v * v ^ 2 ≤
          8 * (n.descFactorial v * v ^ 2) := Nat.le_mul_of_pos_left _ (by omega)
      simpa [mul_assoc, mul_left_comm, mul_comm] using! h

private lemma edge_mem_decode_iff {n v : ℕ} (c : CoreCode n v) (e : Edge n) :
    e ∈ c.decode ↔ s(e.1.1, e.1.2) ∈ c.edgeList := by
  simp [CoreCode.decode]

private lemma edge_mem_iff_adj {n : ℕ} {G : Graph n} (e : Edge n) :
    e ∈ G ↔ adj G e.1.1 e.1.2 := by
  constructor
  · intro he
    exact ⟨e, he, Or.inl ⟨rfl, rfl⟩⟩
  · rintro ⟨f, hf, h | h⟩
    · have : f = e := by
        apply Subtype.ext
        exact Prod.ext h.1 h.2
      simpa [this] using! hf
    · have hback : e.1.2 < e.1.1 := by
        rw [← h.1, ← h.2]
        exact f.2
      exact (lt_asymm e.2 hback).elim

/-! ## Connected exact-excess cores -/

private def edgeCount {V : Type*} (K : SimpleGraph V) : ℕ := Nat.card K.edgeSet

private lemma edgeCount_eq_edgeFinset {V : Type*} [Fintype V]
    (K : SimpleGraph V) [DecidableRel K.Adj] :
    edgeCount K = K.edgeFinset.card := by
  rw [edgeCount, Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card]

private def CoreCandidate {n : ℕ} (G : Graph n)
    (H : (simpleGraph G).Subgraph) : Prop :=
  H.Connected ∧ Fintype.card H.verts + 1 ≤ edgeCount H.coe

private def coreWeight {n : ℕ} {G : Graph n}
    (H : (simpleGraph G).Subgraph) : ℕ :=
  Fintype.card H.verts + edgeCount H.coe

private def subgraphGraph {n : ℕ} {G : Graph n}
    (H : (simpleGraph G).Subgraph) : Graph n :=
  (univ : Finset (Edge n)).filter fun e => H.Adj e.1.1 e.1.2

private lemma subgraphGraph_subset {n : ℕ} {G : Graph n}
    (H : (simpleGraph G).Subgraph) : subgraphGraph H ⊆ G := by
  intro e he
  have hH : H.Adj e.1.1 e.1.2 := (mem_filter.mp he).2
  exact (edge_mem_iff_adj e).2 hH.adj_sub

private lemma card_subgraphGraph {n : ℕ} {G : Graph n}
    (H : (simpleGraph G).Subgraph) :
    (subgraphGraph H).card = edgeCount H.coe := by
  rw [edgeCount_eq_edgeFinset]
  apply Finset.card_bij
    (fun e he =>
      s(⟨e.1.1, H.edge_vert (mem_filter.mp he).2⟩,
        ⟨e.1.2, H.edge_vert ((mem_filter.mp he).2.symm)⟩))
  · intro e he
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    exact (mem_filter.mp he).2
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
        exact (lt_asymm e₂.2 hlt).elim
    · rcases Sym2.eq_iff.mp h with h | h
      · exact congrArg Subtype.val h.2
      · have hlt : e₂.1.2 < e₂.1.1 := by
          calc
            e₂.1.2 = e₁.1.1 := (congrArg Subtype.val h.1).symm
            _ < e₁.1.2 := e₁.2
            _ = e₂.1.1 := congrArg Subtype.val h.2
        exact (lt_asymm e₂.2 hlt).elim
  · intro b hb
    induction b using Sym2.inductionOn with
    | _ u v =>
        have huv : H.Adj u.1 v.1 := by
          rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at hb
          exact hb
        have hG : adj G u.1 v.1 := huv.adj_sub
        rcases hG with ⟨e, he, hends⟩
        have heH : e ∈ subgraphGraph H := by
          rw [subgraphGraph, mem_filter]
          refine ⟨mem_univ _, ?_⟩
          rcases hends with h | h
          · simpa [h.1, h.2] using! huv
          · simpa [h.1, h.2] using! huv.symm
        refine ⟨e, heH, ?_⟩
        rcases hends with h | h
        · exact Sym2.eq_iff.mpr (Or.inl ⟨Subtype.ext h.1, Subtype.ext h.2⟩)
        · exact Sym2.eq_iff.mpr (Or.inr ⟨Subtype.ext h.1, Subtype.ext h.2⟩)

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
  exact (Fintype.card_congr
    { toFun := fun (x : ((simpleGraph G).connectedComponentMk r)) =>
        ⟨x.1, (component_support_eq r x.1).mp x.2⟩
      invFun := fun (x : ↥(componentOf G r)) =>
        ⟨x.1, (component_support_eq r x.1).mpr x.2⟩
      left_inv := fun x => Subtype.ext rfl
      right_inv := fun x => Subtype.ext rfl }).trans (Fintype.card_coe _)

private lemma component_edge_card {n : ℕ} {G : Graph n} (r : Fin n) :
    ((simpleGraph G).connectedComponentMk r).toSimpleGraph.edgeFinset.card =
      edgesInside G (componentOf G r) := by
  let c := (simpleGraph G).connectedComponentMk r
  let inside : Graph n :=
    G.filter (fun e => e.1.1 ∈ componentOf G r ∧ e.1.2 ∈ componentOf G r)
  have hc (x : Fin n) : x ∈ c.supp ↔ x ∈ componentOf G r :=
    component_support_eq r x
  have hcard : inside.card = c.toSimpleGraph.edgeFinset.card := by
    apply Finset.card_bij
      (fun e he =>
        s(⟨e.1.1, (hc e.1.1).mpr (mem_filter.mp he).2.1⟩,
          ⟨e.1.2, (hc e.1.2).mpr (mem_filter.mp he).2.2⟩))
    · intro e he
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
        SimpleGraph.ConnectedComponent.toSimpleGraph_adj, simpleGraph_adj]
      exact ⟨e, (mem_filter.mp he).1, Or.inl ⟨rfl, rfl⟩⟩
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
          exact (lt_asymm e₂.2 hlt).elim
      · rcases Sym2.eq_iff.mp h with h | h
        · exact congrArg Subtype.val h.2
        · have hlt : e₂.1.2 < e₂.1.1 := by
            calc
              e₂.1.2 = e₁.1.1 := (congrArg Subtype.val h.1).symm
              _ < e₁.1.2 := e₁.2
              _ = e₂.1.1 := congrArg Subtype.val h.2
          exact (lt_asymm e₂.2 hlt).elim
    · intro b hb
      induction b using Sym2.inductionOn with
      | _ u v =>
          have huv : adj G u.1 v.1 := by
            rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
              SimpleGraph.ConnectedComponent.toSimpleGraph_adj, simpleGraph_adj] at hb
            exact hb
          rcases huv with ⟨e, he, hends⟩
          have heInside : e ∈ inside := by
            apply mem_filter.mpr
            refine ⟨he, ?_⟩
            rcases hends with h | h
            · exact ⟨(hc e.1.1).mp (h.1.symm ▸ u.2),
                (hc e.1.2).mp (h.2.symm ▸ v.2)⟩
            · exact ⟨(hc e.1.1).mp (h.1.symm ▸ v.2),
                (hc e.1.2).mp (h.2.symm ▸ u.2)⟩
          refine ⟨e, heInside, ?_⟩
          rcases hends with h | h
          · exact Sym2.eq_iff.mpr (Or.inl ⟨Subtype.ext h.1, Subtype.ext h.2⟩)
          · exact Sym2.eq_iff.mpr (Or.inr ⟨Subtype.ext h.1, Subtype.ext h.2⟩)
  simpa [inside, edgesInside] using! hcard.symm

private lemma exists_candidate_of_complex_component {n : ℕ} {G : Graph n}
    {S : Finset (Fin n)} (hS : S ∈ components G)
    (hcomplex : S.card + 1 ≤ edgesInside G S) :
    ∃ H : (simpleGraph G).Subgraph, CoreCandidate G H := by
  simp only [components, mem_image] at hS
  obtain ⟨r, -, rfl⟩ := hS
  let c := (simpleGraph G).connectedComponentMk r
  refine ⟨c.toSubgraph, c.connected_toSubgraph, ?_⟩
  have hv := component_vertex_card (G := G) r
  change Fintype.card {x : Fin n // (simpleGraph G).connectedComponentMk x =
    (simpleGraph G).connectedComponentMk r} = _ at hv
  have he := component_edge_card (G := G) r
  have hv' : Fintype.card c.toSubgraph.verts = (componentOf G r).card := by
    simpa [c, Fintype.card_subtype, SimpleGraph.ConnectedComponent.mem_supp_iff, SimpleGraph.ConnectedComponent.eq] using! hv
  have he' : edgeCount c.toSubgraph.coe =
      edgesInside G (componentOf G r) := by
    have hi : c.toSubgraph.coe ≃g c.toSimpleGraph :=
      { toFun := fun z => ⟨z.1, z.2⟩
        invFun := fun z => ⟨z.1, z.2⟩
        left_inv := fun z => Subtype.ext rfl
        right_inv := fun z => Subtype.ext rfl
        map_rel_iff' := by
          intro a b
          simp only [SimpleGraph.ConnectedComponent.coe_toSubgraph,
            SimpleGraph.ConnectedComponent.toSimpleGraph_adj]
          rfl }
    calc
      edgeCount c.toSubgraph.coe = c.toSubgraph.coe.edgeFinset.card :=
        edgeCount_eq_edgeFinset _
      _ = c.toSimpleGraph.edgeFinset.card := hi.card_edgeFinset_eq
      _ = edgesInside G (componentOf G r) := he
  rw [hv', he']
  exact hcomplex

private lemma exists_minimal_candidate {n : ℕ} {G : Graph n}
    (hex : ∃ H : (simpleGraph G).Subgraph, CoreCandidate G H) :
    ∃ H : (simpleGraph G).Subgraph,
      CoreCandidate G H ∧
      ∀ K : (simpleGraph G).Subgraph,
        CoreCandidate G K → coreWeight H ≤ coreWeight K := by
  let candidates := (univ : Finset ((simpleGraph G).Subgraph)).filter
    (CoreCandidate G)
  have hnonempty : candidates.Nonempty := by
    obtain ⟨H, hH⟩ := hex
    exact ⟨H, mem_filter.mpr ⟨mem_univ _, hH⟩⟩
  obtain ⟨H, hHmem, hHmin⟩ := candidates.exists_min_image coreWeight hnonempty
  refine ⟨H, (mem_filter.mp hHmem).2, ?_⟩
  intro K hK
  exact hHmin K (mem_filter.mpr ⟨mem_univ _, hK⟩)

private lemma minimal_candidate_edge_card {n : ℕ} {G : Graph n}
    {H : (simpleGraph G).Subgraph} (hH : CoreCandidate G H)
    (hmin : ∀ K : (simpleGraph G).Subgraph,
      CoreCandidate G K → coreWeight H ≤ coreWeight K) :
    edgeCount H.coe = Fintype.card H.verts + 1 := by
  apply le_antisymm
  · by_contra hnot
    have hstrict : Fintype.card H.verts + 1 < edgeCount H.coe := by
      omega
    have hnacyclic : ¬ H.coe.IsAcyclic := by
      intro hac
      have ht : H.coe.IsTree := ⟨hH.1.coe, hac⟩
      have hc := (SimpleGraph.isTree_iff_connected_and_card.mp ht).2
      have hvcard : Nat.card H.verts = Fintype.card H.verts :=
        Nat.card_eq_fintype_card
      rw [hvcard] at hc
      change edgeCount H.coe + 1 = Fintype.card H.verts at hc
      omega
    rw [SimpleGraph.isAcyclic_iff_forall_adj_isBridge] at hnacyclic
    push_neg at hnacyclic
    obtain ⟨x, y, hxy, hnbridge⟩ := hnacyclic
    let es : Finset (Sym2 H.verts) := {s(x, y)}
    let D := H.coe.deleteEdges (↑es : Set (Sym2 H.verts))
    have hDconn : D.Connected := by
      simpa [D, es] using!
        hH.1.coe.preconnected.connected_deleteEdges_of_not_isBridge hnbridge
    let K : (simpleGraph G).Subgraph :=
      { verts := H.verts
        Adj := fun a b => ∃ (ha : a ∈ H.verts) (hb : b ∈ H.verts),
          D.Adj ⟨a, ha⟩ ⟨b, hb⟩
        adj_sub := by
          intro a b hab
          obtain ⟨ha, hb, hab⟩ := hab
          exact H.adj_sub (H.coe.deleteEdges_le _ hab)
        edge_vert := by
          intro a b hab
          exact hab.choose
        symm := ⟨by
          intro a b h
          obtain ⟨ha, hb, hab⟩ := h
          exact ⟨hb, ha, D.symm.symm _ _ hab⟩⟩ }
    let eKD : K.coe ≃g D :=
      { toFun := fun z => ⟨z.1, z.2⟩
        invFun := fun z => ⟨z.1, z.2⟩
        left_inv := fun z => Subtype.ext rfl
        right_inv := fun z => Subtype.ext rfl
        map_rel_iff' := by
          intro a b
          constructor
          · intro h
            exact ⟨a.2, b.2, h⟩
          · rintro ⟨ha, hb, h⟩
            simpa only [Subsingleton.elim ha a.2, Subsingleton.elim hb b.2] using! h }
    have hDcard : edgeCount D = edgeCount H.coe - 1 := by
      rw [edgeCount_eq_edgeFinset, edgeCount_eq_edgeFinset]
      change (H.coe.deleteEdges (↑es : Set (Sym2 H.verts))).edgeFinset.card = _
      have hEF := SimpleGraph.edgeFinset_deleteEdges (G := H.coe) es
      have hEFcard : (H.coe.deleteEdges (↑es : Set (Sym2 H.verts))).edgeFinset.card =
          (H.coe.edgeFinset \ {s(x, y)}).card := by
        simpa [es] using! congrArg Finset.card hEF
      rw [hEFcard, Finset.card_sdiff_of_subset]
      · simp
      · simp only [Finset.singleton_subset_iff, SimpleGraph.mem_edgeFinset,
          SimpleGraph.mem_edgeSet]
        exact hxy
    have hKcand : CoreCandidate G K := by
      constructor
      · exact ⟨(eKD.connected_iff).2 hDconn⟩
      · have hv : Fintype.card K.verts = Fintype.card H.verts :=
          Fintype.card_congr eKD.toEquiv
        have he : edgeCount K.coe = edgeCount D := by
          calc
            edgeCount K.coe = K.coe.edgeFinset.card := edgeCount_eq_edgeFinset _
            _ = D.edgeFinset.card := eKD.card_edgeFinset_eq
            _ = edgeCount D := (edgeCount_eq_edgeFinset _).symm
        rw [hv, he, hDcard]
        omega
    have hw := hmin K hKcand
    unfold coreWeight at hw
    have hv : Fintype.card K.verts = Fintype.card H.verts :=
      Fintype.card_congr eKD.toEquiv
    have he : edgeCount K.coe = edgeCount D := by
      calc
        edgeCount K.coe = K.coe.edgeFinset.card := edgeCount_eq_edgeFinset _
        _ = D.edgeFinset.card := eKD.card_edgeFinset_eq
        _ = edgeCount D := (edgeCount_eq_edgeFinset _).symm
    rw [hv, he, hDcard] at hw
    omega
  · exact hH.2

private lemma candidate_order_four {n : ℕ} {G : Graph n}
    {H : (simpleGraph G).Subgraph} (hH : CoreCandidate G H)
    (hedges : edgeCount H.coe = Fintype.card H.verts + 1) :
    4 ≤ Fintype.card H.verts := by
  have hcap := H.coe.card_edgeFinset_le_card_choose_two
  rw [← edgeCount_eq_edgeFinset, hedges] at hcap
  by_contra hnot
  have hsmall : Fintype.card H.verts ≤ 3 := by omega
  interval_cases hcard : Fintype.card H.verts <;>
    norm_num [hcard, Nat.choose_two_right] at hcap

private lemma minimal_candidate_min_degree {n : ℕ} {G : Graph n}
    {H : (simpleGraph G).Subgraph} (hH : CoreCandidate G H)
    (hmin : ∀ K : (simpleGraph G).Subgraph,
      CoreCandidate G K → coreWeight H ≤ coreWeight K)
    (hedges : edgeCount H.coe = Fintype.card H.verts + 1) :
    ∀ x : H.verts, 2 ≤ H.coe.degree x := by
  have hfour : 4 ≤ Fintype.card H.verts := candidate_order_four hH hedges
  haveI : Nontrivial H.verts := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  intro x
  have hpos : 0 < H.coe.degree x :=
    hH.1.coe.preconnected.degree_pos_of_nontrivial x
  by_contra hnot
  have hdeg : H.coe.degree x = 1 := by omega
  let K : (simpleGraph G).Subgraph := H.deleteVerts {x.1}
  let e : K.coe ≃g H.coe.induce ({x}ᶜ : Set H.verts) :=
    { toFun := fun z =>
        ⟨⟨z.1, z.2.1⟩, fun h => z.2.2 (congrArg Subtype.val h)⟩
      invFun := fun z =>
        ⟨z.1.1, z.1.2, fun h => z.2 (Subtype.ext h)⟩
      left_inv := fun z => Subtype.ext rfl
      right_inv := fun z => Subtype.ext (Subtype.ext rfl)
      map_rel_iff' := by
        intro a b
        constructor
        · intro h
          exact ⟨a.2, b.2, h⟩
        · intro h
          exact h.2.2 }
  have hIconn : (H.coe.induce ({x}ᶜ : Set H.verts)).Connected :=
    hH.1.coe.induce_compl_singleton_of_degree_eq_one hdeg
  have hKconn : K.Connected := ⟨(e.connected_iff).2 hIconn⟩
  have hKverts : Fintype.card K.verts = Fintype.card H.verts - 1 := by
    have hc : Fintype.card K.verts =
        Fintype.card {y : H.verts // y ≠ x} :=
      Fintype.card_congr
        { toFun := fun z =>
            ⟨⟨z.1, z.2.1⟩, fun h => z.2.2 (congrArg Subtype.val h)⟩
          invFun := fun z =>
            ⟨z.1.1, z.1.2, fun h => z.2 (Subtype.ext h)⟩
          left_inv := fun z => Subtype.ext rfl
          right_inv := fun z => Subtype.ext (Subtype.ext rfl) }
    rw [hc]
    simp
  have hKedges : edgeCount K.coe = edgeCount H.coe - 1 := by
    rw [edgeCount_eq_edgeFinset, edgeCount_eq_edgeFinset]
    rw [e.card_edgeFinset_eq]
    rw [H.coe.card_edgeFinset_induce_compl_singleton x,
      H.coe.card_edgeFinset_deleteIncidenceSet x]
    have hdeq : @SimpleGraph.degree _ H.coe x (H.coe.neighborSetFintype x) =
        @SimpleGraph.degree _ H.coe x (SimpleGraph.Subgraph.coeFiniteAt x) := by
      unfold SimpleGraph.degree
      apply congrArg Finset.card
      ext y
      simp
    have hd : @SimpleGraph.degree _ H.coe x (H.coe.neighborSetFintype x) = 1 :=
      hdeq.trans hdeg
    rw [hd]
  have hKcand : CoreCandidate G K := by
    refine ⟨hKconn, ?_⟩
    rw [hKverts]
    rw [hKedges]
    rw [hedges]
    omega
  have hw := hmin K hKcand
  unfold coreWeight at hw
  rw [hKverts] at hw
  rw [hKedges] at hw
  rw [hedges] at hw
  omega

/-! ## A normalized Euler ordering -/

private theorem exists_normalized_euler
    {V : Type*} [Fintype V] [DecidableEq V]
    {K : SimpleGraph V} [DecidableRel K.Adj]
    (hconn : K.Connected)
    (hedges : K.edgeFinset.card = Fintype.card V + 1)
    (hmin : ∀ x : V, 2 ≤ K.degree x) :
    ∃ u v : V, ∃ p : K.Walk u v,
      p.IsEulerian ∧
      ∀ x : V, p.support.tail.dropLast.count x = 1 := by
  let excess : V → ℕ := fun x => K.degree x - 2
  have hexnonneg : ∀ x, 0 ≤ excess x := by
    intro x; exact Nat.zero_le _
  have hsum : ∑ x : V, excess x = 2 := by
    have hsplit : (∑ x : V, K.degree x) =
        (∑ x : V, excess x) + 2 * Fintype.card V := by
      calc
        (∑ x : V, K.degree x) = ∑ x : V, (excess x + 2) := by
          apply sum_congr rfl
          intro x _
          simp only [excess]
          have hx := hmin x
          omega
        _ = (∑ x : V, excess x) + ∑ _x : V, 2 := sum_add_distrib
        _ = (∑ x : V, excess x) + 2 * Fintype.card V := by
          simp [mul_comm]
    rw [K.sum_degrees_eq_twice_card_edges, hedges] at hsplit
    omega
  let O : Finset V := univ.filter fun x => Odd (K.degree x)
  have hOcard : O.card ≤ 2 := by
    have hle : O.card ≤ ∑ x : V, excess x := by
      calc
        O.card = ∑ x ∈ O, 1 := by simp
        _ ≤ ∑ x ∈ O, excess x := by
          exact sum_le_sum fun x hx => by
            have hodd : Odd (K.degree x) := (mem_filter.mp hx).2
            have hlow := hmin x
            obtain ⟨k, hk⟩ := hodd
            dsimp [excess]
            omega
        _ ≤ ∑ x ∈ (univ : Finset V), excess x :=
          sum_le_sum_of_subset (subset_univ O)
    rw [hsum] at hle
    exact hle
  have hOeven : Even O.card := by
    simpa [O] using! K.even_card_odd_degree_vertices
  have hOcases : O.card = 0 ∨ O.card = 2 := by
    obtain ⟨k, hk⟩ := hOeven
    omega
  have hexle : ∀ x, excess x ≤ 2 := by
    intro x
    calc
      excess x ≤ ∑ y ∈ (univ : Finset V), excess y := by
        exact Finset.single_le_sum (fun y _ => hexnonneg y) (mem_univ x)
      _ = 2 := hsum
  have hdeg_le : ∀ x, K.degree x ≤ 4 := by
    intro x
    have := hexle x
    have hlow := hmin x
    dsimp [excess] at this
    omega
  rcases hOcases with hOzero | hOtwo
  · have heven : ∀ x, Even (K.degree x) := by
      intro x
      have hOempty : O = ∅ := Finset.card_eq_zero.mp hOzero
      exact Nat.not_odd_iff_even.mp fun hx => by
        have : x ∈ O := mem_filter.mpr ⟨mem_univ _, hx⟩
        rw [hOempty] at this
        simp at this
    have hex4 : ∃ b : V, K.degree b = 4 := by
      by_contra hnone
      push_neg at hnone
      have hall : ∀ x, K.degree x = 2 := by
        intro x
        have := hmin x
        have := hdeg_le x
        obtain ⟨k, hk⟩ := heven x
        have := hnone x
        omega
      have hz : ∑ x : V, excess x = 0 := by simp [excess, hall]
      omega
    obtain ⟨b, hb4⟩ := hex4
    obtain ⟨a, p, hp⟩ :=
      SimpleGraph.exists_eulerianCircuit_of_connected_even hconn heven
    have hbmem : b ∈ p.support := by
      have hpos : 0 < K.degree b := by omega
      obtain ⟨z, hbz⟩ := (K.degree_pos_iff_exists_adj (v := b)).mp hpos
      exact p.fst_mem_support_of_mem_edges ((hp.mem_edges_iff).2 hbz)
    let q : K.Walk b b := p.rotate b hbmem
    have hq : q.IsEulerian := by
      rw [SimpleGraph.Walk.isEulerian_iff]
      refine ⟨hp.isTrail.rotate hbmem, ?_⟩
      intro e he
      exact (p.rotate_edges b hbmem).mem_iff.mpr ((hp.mem_edges_iff).2 he)
    refine ⟨b, b, q, hq, ?_⟩
    intro x
    let inner := q.support.tail.dropLast
    have hnon : ¬ q.Nil := by
      intro hnil
      have hpos : 0 < K.degree b := by omega
      obtain ⟨z, hbz⟩ := (K.degree_pos_iff_exists_adj (v := b)).mp hpos
      have he : s(b, z) ∈ q.edges := (hq.mem_edges_iff).2 hbz
      rw [SimpleGraph.Walk.edges_eq_nil.mpr hnil] at he
      simp at he
    have htail : q.support.tail ≠ [] := by
      rw [← q.support_tail_of_not_nil hnon]
      exact q.tail.support_ne_nil
    have hs1 : q.support.dropLast = b :: inner := by
      calc
        q.support.dropLast = (b :: q.support.tail).dropLast := by
          rw [← q.support_eq_cons]
        _ = b :: q.support.tail.dropLast :=
          List.dropLast_cons_of_ne_nil htail
        _ = b :: inner := rfl
    have hs2 : q.support.tail = inner ++ [b] := by
      calc
        q.support.tail = q.support.tail.dropLast ++
            [q.support.tail.getLast htail] :=
          (List.dropLast_append_getLast htail).symm
        _ = inner ++ [b] := by
          congr 2
          have hsupp : q.support.getLast q.support_ne_nil = b := q.getLast_support
          have hsupp' : q.tail.support.getLast q.tail.support_ne_nil = b :=
            q.tail.getLast_support
          simpa only [q.support_tail_of_not_nil hnon] using! hsupp'
    have hinc := hq.countP_edges_eq_degree x
    rw [SimpleGraph.countP_edges_incidence q x, hs1, hs2] at hinc
    simp only [List.count_cons, List.count_append, List.count_singleton] at hinc
    by_cases hxb : x = b
    · subst x
      change inner.count b = 1
      simp [hb4] at hinc
      omega
    · have hdx : K.degree x = 2 := by
        have := hmin x
        have := hdeg_le x
        obtain ⟨k, hk⟩ := heven x
        have hne4 : K.degree x ≠ 4 := by
          intro hx4
          have hxex : excess x = 2 := by dsimp [excess]; omega
          have hbex : excess b = 2 := by dsimp [excess]; omega
          have hle : excess b + excess x ≤ ∑ y : V, excess y := by
            calc
              excess b + excess x = ∑ y ∈ ({b, x} : Finset V), excess y := by
                simp [hxb, Ne.symm hxb, add_comm]
              _ ≤ ∑ y ∈ (univ : Finset V), excess y :=
                sum_le_sum_of_subset (by simp)
          rw [hsum, hbex, hxex] at hle
          omega
        omega
      change inner.count x = 1
      simp [hxb, Ne.symm hxb, hdx] at hinc
      omega
  · obtain ⟨u, v, huv, hO⟩ := Finset.card_eq_two.mp hOtwo
    have hodd : ∀ x, Odd (K.degree x) ↔ x = u ∨ x = v := by
      intro x
      have hx : Odd (K.degree x) ↔ x ∈ O := by simp [O]
      rw [hx, hO]
      simp [eq_comm]
    have hdu : K.degree u = 3 := by
      have := hmin u
      have := hdeg_le u
      obtain ⟨k, hk⟩ := (hodd u).2 (Or.inl rfl)
      omega
    have hdv : K.degree v = 3 := by
      have := hmin v
      have := hdeg_le v
      obtain ⟨k, hk⟩ := (hodd v).2 (Or.inr rfl)
      omega
    have hrest : ∀ x, x ≠ u → x ≠ v → K.degree x = 2 := by
      intro x hxu hxv
      have hthree : excess u + excess v + excess x ≤ ∑ y : V, excess y := by
        calc
          excess u + excess v + excess x =
              ∑ y ∈ ({u, v, x} : Finset V), excess y := by
            simp [huv, hxu, hxv, Ne.symm hxu, Ne.symm hxv,
              add_comm, add_left_comm, add_assoc]
          _ ≤ ∑ y ∈ (univ : Finset V), excess y :=
            sum_le_sum_of_subset (by simp)
      have hxmin := hmin x
      simp [excess, hdu, hdv, hsum] at hthree
      omega
    obtain ⟨p, hp⟩ :=
      SimpleGraph.exists_eulerianTrail_of_connected_twoOdd hconn huv hodd
    refine ⟨u, v, p, hp, ?_⟩
    intro x
    let inner := p.support.tail.dropLast
    have hnon : ¬ p.Nil := by
      intro hnil
      exact huv hnil.eq
    have htail : p.support.tail ≠ [] := by
      rw [← p.support_tail_of_not_nil hnon]
      exact p.tail.support_ne_nil
    have hs1 : p.support.dropLast = u :: inner := by
      calc
        p.support.dropLast = (u :: p.support.tail).dropLast := by
          rw [← p.support_eq_cons]
        _ = u :: p.support.tail.dropLast :=
          List.dropLast_cons_of_ne_nil htail
        _ = u :: inner := rfl
    have hs2 : p.support.tail = inner ++ [v] := by
      calc
        p.support.tail = p.support.tail.dropLast ++
            [p.support.tail.getLast htail] :=
          (List.dropLast_append_getLast htail).symm
        _ = inner ++ [v] := by
          congr 2
          have hsupp : p.support.getLast p.support_ne_nil = v := p.getLast_support
          have hsupp' : p.tail.support.getLast p.tail.support_ne_nil = v :=
            p.tail.getLast_support
          simpa only [p.support_tail_of_not_nil hnon] using! hsupp'
    have hinc := hp.countP_edges_eq_degree x
    rw [SimpleGraph.countP_edges_incidence p x, hs1, hs2] at hinc
    simp only [List.count_cons, List.count_append, List.count_singleton] at hinc
    by_cases hxu : x = u
    · subst x
      change inner.count u = 1
      simp [huv, Ne.symm huv, hdu] at hinc
      omega
    · by_cases hxv : x = v
      · subst x
        change inner.count v = 1
        simp [huv, Ne.symm huv, hdv] at hinc
        omega
      · have hdx := hrest x hxu hxv
        change inner.count x = 1
        simp [hxu, hxv, Ne.symm hxu, Ne.symm hxv, hdx] at hinc
        omega

/-! ## Encoding a core by its normalized Euler ordering -/

private lemma mapped_walk_edges_iff {n : ℕ} {G : Graph n}
    (H : (simpleGraph G).Subgraph) {u v : H.verts}
    (p : H.coe.Walk u v) (hp : p.IsEulerian) (a b : Fin n) :
    s(a, b) ∈ (p.map H.hom).edges ↔ H.Adj a b := by
  constructor
  · intro hab
    rw [SimpleGraph.Walk.edges_map] at hab
    obtain ⟨e, he, heq⟩ := List.mem_map.mp hab
    induction e using Sym2.inductionOn with
    | _ x y =>
        have hxy : H.coe.Adj x y := by
          rw [← SimpleGraph.mem_edgeSet]
          exact p.edges_subset_edgeSet he
        rcases Sym2.eq_iff.mp heq with h | h
        · have hx : x.1 = a := h.1
          have hy : y.1 = b := h.2
          subst a
          subst b
          exact hxy
        · have hx : x.1 = b := h.1
          have hy : y.1 = a := h.2
          subst a
          subst b
          exact hxy.symm
  · intro hab
    let a' : H.verts := ⟨a, H.edge_vert hab⟩
    let b' : H.verts := ⟨b, H.edge_vert hab.symm⟩
    have he : s(a', b') ∈ p.edges :=
      (hp.mem_edges_iff).2 (by exact hab)
    rw [SimpleGraph.Walk.edges_map]
    exact List.mem_map.mpr ⟨s(a', b'), he, rfl⟩

private lemma exists_coreCode {n : ℕ} {G : Graph n}
    (H : (simpleGraph G).Subgraph)
    (hconn : H.Connected)
    (hedges : edgeCount H.coe = Fintype.card H.verts + 1)
    (hmin : ∀ x : H.verts, 2 ≤ H.coe.degree x) :
    ∃ c : CoreCode n (Fintype.card H.verts),
      c.decode = subgraphGraph H := by
  letI : BEq H.verts := instBEqOfDecidableEq
  have hedges' : H.coe.edgeFinset.card = Fintype.card H.verts + 1 := by
    rw [← edgeCount_eq_edgeFinset]
    exact hedges
  obtain ⟨u, v, p, hp, hcount⟩ :=
    exists_normalized_euler hconn.coe hedges' (fun x => by convert hmin x)
  let inner := p.support.tail.dropLast
  have hnodup : inner.Nodup :=
    List.nodup_iff_count_le_one.mpr fun x => by
      change inner.count x ≤ 1
      simpa [inner] using! (hcount x).le
  have hall : ∀ x : H.verts, x ∈ inner := fun x =>
    List.count_pos_iff.mp (by
      have hc : inner.count x = 1 := by simpa [inner] using! hcount x
      rw [hc]
      exact Nat.zero_lt_one)
  let einner : Fin inner.length ≃ H.verts :=
    hnodup.getEquivOfForallMemList inner hall
  have hlen : inner.length = Fintype.card H.verts := by
    simpa using! Fintype.card_congr einner
  let e : Fin (Fintype.card H.verts) ≃ H.verts :=
    (finCongr hlen.symm).trans einner
  let labels : Fin (Fintype.card H.verts) ↪ Fin n :=
    e.toEmbedding.trans (Function.Embedding.subtype _)
  let first : Fin (Fintype.card H.verts) := e.symm u
  let last : Fin (Fintype.card H.verts) := e.symm v
  let c : CoreCode n (Fintype.card H.verts) := ⟨labels, first, last⟩
  have hofFn : List.ofFn labels = inner.map (fun x : H.verts => x.1) := by
    apply List.ext_get
    · simp [labels, e, hlen]
    · intro i hi hi'
      simp [labels, e, einner, hlen]
  have hsupport :
      (p.map H.hom).support =
        u.1 :: inner.map (fun x : H.verts => x.1) ++ [v.1] := by
    rw [SimpleGraph.Walk.support_map]
    have hnon : ¬ p.Nil := by
      intro hnil
      have hpos : 0 < H.coe.edgeFinset.card := by rw [hedges']; omega
      obtain ⟨ed, hed⟩ := Finset.card_pos.mp hpos
      have he : ed ∈ p.edges := (hp.mem_edges_iff).2 (by
        simpa [SimpleGraph.mem_edgeFinset] using! hed)
      rw [SimpleGraph.Walk.edges_eq_nil.mpr hnil] at he
      simp at he
    have htail : p.support.tail ≠ [] := by
      rw [← p.support_tail_of_not_nil hnon]
      exact p.tail.support_ne_nil
    have hdecomp : p.support = u :: inner ++ [v] := by
      calc
        p.support = u :: p.support.tail := p.support_eq_cons
        _ = u :: (p.support.tail.dropLast ++
            [p.support.tail.getLast htail]) := by
              rw [List.dropLast_append_getLast htail]
        _ = u :: inner ++ [v] := by
          congr 3
          have hsupp : p.tail.support.getLast p.tail.support_ne_nil = v :=
            p.tail.getLast_support
          simpa only [p.support_tail_of_not_nil hnon] using! hsupp
    rw [hdecomp]
    simp
  have hvertex : c.vertexList = (p.map H.hom).support := by
    rw [hsupport]
    change labels first :: List.ofFn labels ++ [labels last] =
      u.1 :: inner.map (fun x : H.verts => x.1) ++ [v.1]
    rw [hofFn]
    simp only [labels, first, last, Function.Embedding.trans_apply,
      Equiv.coe_toEmbedding, Equiv.apply_symm_apply,
      Function.Embedding.coe_subtype]
  refine ⟨c, ?_⟩
  ext ed
  rw [edge_mem_decode_iff, subgraphGraph, mem_filter]
  simp only [mem_univ, true_and]
  rw [CoreCode.edgeList, hvertex, ← SimpleGraph.Walk.edges_eq_zipWith_support]
  exact mapped_walk_edges_iff H p hp ed.1.1 ed.1.2

private theorem coreFamily_cover : BicyclicCoreCover coreFamily := by
  refine ⟨?_, card_coreFamily, ?_⟩
  · intro n v F hF
    exact mem_coreFamily_card hF
  · intro n G hbad
    unfold noComplex at hbad
    push_neg at hbad
    obtain ⟨S, hS, hcomplex⟩ := hbad
    have hseed := exists_candidate_of_complex_component hS (by omega)
    obtain ⟨H, hH, hminimal⟩ := exists_minimal_candidate hseed
    have hedges := minimal_candidate_edge_card hH hminimal
    have hmindeg := minimal_candidate_min_degree hH hminimal hedges
    let v := Fintype.card H.verts
    have hvn : v ≤ n := by
      simpa [v, Fintype.card_subtype] using! Fintype.card_subtype_le H.verts
    have hv4 : 4 ≤ v := candidate_order_four hH hedges
    obtain ⟨c, hc⟩ := exists_coreCode H hH.1 hedges hmindeg
    let F : Graph n := c.decode
    refine ⟨v, mem_Icc.mpr ⟨hv4, hvn⟩, F, ?_, ?_⟩
    · rw [coreFamily, mem_image]
      refine ⟨c, mem_filter.mpr ⟨mem_univ _, ?_⟩, rfl⟩
      rw [hc, card_subgraphGraph, hedges]
    · change c.decode ⊆ G
      rw [hc]
      exact subgraphGraph_subset H

/-- The concrete all-order bicyclic cover used by the finite probability
calculation. -/
theorem coreFamily_isCover : BicyclicCoreCover coreFamily := coreFamily_cover

end
end Erdos745.WrapUp.Proofs.Internal.W07_SUBCRIT_Cover
