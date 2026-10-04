module

public import Erdos745.WrapUp.Compat
public import Erdos745.WrapUp.Exploration
public import Erdos745.WrapUp.Proofs.Internal.Linked.W01_Asymptotic
public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Probability.ProbabilityMassFunction.Integrals
public import Erdos745.WrapUp.Proofs.Internal.Linked.W01_FiniteCore

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local simp] Pi.div_def Pi.mul_def Pi.add_def Pi.sub_def Pi.neg_def Pi.inv_def Function.comp_def Pi.pow_def Pi.smul_def Real.rpow_eq_pow

@[expose] public section


/-!
# Finite exploration bridge

This module is the common finite foundation for W14 and W15.  It records the
undirected component facts and the exact operational equations of the public
`explore` process, without introducing a second exploration.  Later
probability and record-minimum arguments can therefore reason directly about
the fields of `BFSState`.
-/

namespace Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_Finite

open Erdos745.WrapUp

noncomputable section
attribute [local instance] Classical.propDecidable

/-! ## Undirected reachability and components -/

lemma adj_symmetric {n : ℕ} (G : Graph n) :
    Symmetric (adj G) := by
  intro u v huv
  rcases huv with ⟨e, heG, huv | huv⟩
  · exact ⟨e, heG, Or.inr huv⟩
  · exact ⟨e, heG, Or.inl huv⟩

lemma reach_refl {n : ℕ} (G : Graph n) (v : Fin n) :
    reach G v v := by
  exact Relation.ReflTransGen.refl

lemma reach_symm {n : ℕ} {G : Graph n} {u v : Fin n}
    (h : reach G u v) : reach G v u := by
  haveI : Std.Symm (adj G) := ⟨adj_symmetric G⟩
  exact (Relation.ReflTransGen.symmetric (r := adj G)).symm _ _ h

lemma reach_trans {n : ℕ} {G : Graph n} {u v w : Fin n}
    (huv : reach G u v) (hvw : reach G v w) : reach G u w := by
  exact huv.trans hvw

@[simp] lemma mem_componentOf_iff {n : ℕ} (G : Graph n) (v u : Fin n) :
    u ∈ componentOf G v ↔ reach G v u := by
  simp [componentOf]

@[simp] lemma mem_componentOf_self {n : ℕ} (G : Graph n) (v : Fin n) :
    v ∈ componentOf G v := by
  simp [mem_componentOf_iff, reach_refl]

lemma componentOf_eq_of_reach {n : ℕ} {G : Graph n} {u v : Fin n}
    (huv : reach G u v) : componentOf G u = componentOf G v := by
  ext w
  simp only [mem_componentOf_iff]
  constructor
  · intro huw
    exact reach_trans (reach_symm huv) huw
  · intro hvw
    exact reach_trans huv hvw

lemma componentOf_mem_components {n : ℕ} (G : Graph n) (v : Fin n) :
    componentOf G v ∈ components G := by
  simp [components]

lemma mem_components_iff {n : ℕ} (G : Graph n) (S : Finset (Fin n)) :
    S ∈ components G ↔ ∃ v : Fin n, componentOf G v = S := by
  simp [components]

lemma adjacent_mem_componentOf {n : ℕ} {G : Graph n} {v u w : Fin n}
    (hu : u ∈ componentOf G v) (huw : adj G u w) :
    w ∈ componentOf G v := by
  rw [mem_componentOf_iff] at hu ⊢
  exact hu.tail huw

/-! ## Exact one-step equations -/

def newChildren {n : ℕ} (G : Graph n) (discovered : Finset (Fin n))
    (v : Fin n) : Finset (Fin n) :=
  (Finset.univ : Finset (Fin n)).filter
    (fun u => u ∉ discovered ∧ adj G v u)

@[simp] lemma mem_newChildren_iff {n : ℕ} (G : Graph n)
    (discovered : Finset (Fin n)) (v u : Fin n) :
    u ∈ newChildren G discovered v ↔ u ∉ discovered ∧ adj G v u := by
  simp [newChildren]

@[simp] lemma selectRoot_queue_cons {n : ℕ} (seen : Finset (Fin n))
    (v : Fin n) (rest : List (Fin n)) (z : ℤ) :
    selectRoot (⟨seen, v :: rest, z⟩ : BFSState n) = some (v, rest, seen) := by
  rfl

lemma selectRoot_queue_nil_of_nonempty {n : ℕ} (seen : Finset (Fin n))
    (z : ℤ) (h : ((Finset.univ : Finset (Fin n)) \ seen).Nonempty) :
    selectRoot (⟨seen, [], z⟩ : BFSState n) =
      some (((Finset.univ : Finset (Fin n)) \ seen).min' h, [],
        insert (((Finset.univ : Finset (Fin n)) \ seen).min' h) seen) := by
  simp [selectRoot, h]

theorem bfsStep_queue_cons {n : ℕ} (G : Graph n) (seen : Finset (Fin n))
    (v : Fin n) (rest : List (Fin n)) (z : ℤ) :
    bfsStep G (⟨seen, v :: rest, z⟩ : BFSState n) =
      ⟨seen ∪ newChildren G seen v,
        rest ++ (newChildren G seen v).toList,
        z + ((newChildren G seen v).card : ℤ) - 1⟩ := by
  rfl

theorem bfsStep_queue_nil_of_nonempty {n : ℕ} (G : Graph n)
    (seen : Finset (Fin n)) (z : ℤ)
    (h : ((Finset.univ : Finset (Fin n)) \ seen).Nonempty) :
    let v := ((Finset.univ : Finset (Fin n)) \ seen).min' h
    bfsStep G (⟨seen, [], z⟩ : BFSState n) =
      ⟨insert v seen ∪ newChildren G (insert v seen) v,
        (newChildren G (insert v seen) v).toList,
        z + ((newChildren G (insert v seen) v).card : ℤ) - 1⟩ := by
  simp [bfsStep, selectRoot, h, newChildren]

theorem bfsStep_queue_nil_of_empty {n : ℕ} (G : Graph n)
    (seen : Finset (Fin n)) (z : ℤ)
    (h : ¬ ((Finset.univ : Finset (Fin n)) \ seen).Nonempty) :
    bfsStep G (⟨seen, [], z⟩ : BFSState n) = ⟨seen, [], z⟩ := by
  simp [bfsStep, selectRoot, h]

@[simp] lemma explore_zero {n : ℕ} (G : Graph n) :
    explore G 0 = initialState n := rfl

@[simp] lemma explore_succ {n : ℕ} (G : Graph n) (j : ℕ) :
    explore G (j + 1) = bfsStep G (explore G j) := rfl

@[simp] lemma initial_seen (n : ℕ) : (initialState n).seen = ∅ := rfl

@[simp] lemma initial_queue (n : ℕ) : (initialState n).queue = [] := rfl

@[simp] lemma initial_walk (n : ℕ) : (initialState n).walk = 0 := rfl

/-! ## Monotonicity and processed vertices -/

lemma seen_subset_bfsStep {n : ℕ} (G : Graph n) (s : BFSState n) :
    s.seen ⊆ (bfsStep G s).seen := by
  rcases s with ⟨seen, queue, z⟩
  cases queue with
  | nil =>
      by_cases h : ((Finset.univ : Finset (Fin n)) \ seen).Nonempty
      · rw [bfsStep_queue_nil_of_nonempty G seen z h]
        intro u hu
        simp [hu]
      · rw [bfsStep_queue_nil_of_empty G seen z h]
  | cons v rest =>
      rw [bfsStep_queue_cons]
      exact Finset.subset_union_left

lemma seen_subset_explore_succ {n : ℕ} (G : Graph n) (j : ℕ) :
    (explore G j).seen ⊆ (explore G (j + 1)).seen := by
  rw [explore_succ]
  exact seen_subset_bfsStep G (explore G j)

theorem seen_monotone {n : ℕ} (G : Graph n) :
    Monotone (fun j => (explore G j).seen) := by
  exact monotone_nat_of_le_succ (seen_subset_explore_succ G)

lemma processed_subset_seen {n : ℕ} (G : Graph n) (j : ℕ) :
    processed G j ⊆ (explore G j).seen := by
  exact Finset.sdiff_subset

lemma processed_disjoint_queue {n : ℕ} (G : Graph n) (j : ℕ) :
    Disjoint (processed G j) (explore G j).queue.toFinset := by
  rw [Finset.disjoint_left]
  intro u hu hqueue
  exact (Finset.mem_sdiff.mp hu).2 hqueue

lemma processed_union_queue {n : ℕ} (G : Graph n) (j : ℕ)
    (hqueue : (explore G j).queue.toFinset ⊆ (explore G j).seen) :
    processed G j ∪ (explore G j).queue.toFinset = (explore G j).seen := by
  unfold processed
  exact Finset.sdiff_union_of_subset hqueue

/-! ## Queue well-formedness -/

def QueueWellFormed {n : ℕ} (s : BFSState n) : Prop :=
  s.queue.Nodup ∧ s.queue.toFinset ⊆ s.seen

@[simp] lemma initial_queueWellFormed (n : ℕ) :
    QueueWellFormed (initialState n) := by
  simp [QueueWellFormed, initialState]

lemma queueWellFormed_bfsStep {n : ℕ} (G : Graph n) (s : BFSState n)
    (hs : QueueWellFormed s) : QueueWellFormed (bfsStep G s) := by
  rcases s with ⟨seen, queue, z⟩
  rcases hs with ⟨hnodup, hsubset⟩
  cases queue with
  | nil =>
      by_cases h : ((Finset.univ : Finset (Fin n)) \ seen).Nonempty
      · rw [bfsStep_queue_nil_of_nonempty G seen z h]
        let v := ((Finset.univ : Finset (Fin n)) \ seen).min' h
        let C := newChildren G (insert v seen) v
        change QueueWellFormed
          (⟨insert v seen ∪ C, C.toList,
            z + (C.card : ℤ) - 1⟩ : BFSState n)
        constructor
        · exact Finset.nodup_toList C
        · intro u hu
          have huC : u ∈ C := by simpa [C] using! hu
          exact Finset.mem_union_right _ huC
      · rw [bfsStep_queue_nil_of_empty G seen z h]
        exact ⟨hnodup, hsubset⟩
  | cons v rest =>
      rw [bfsStep_queue_cons]
      let C := newChildren G seen v
      change QueueWellFormed
        (⟨seen ∪ C, rest ++ C.toList,
          z + (C.card : ℤ) - 1⟩ : BFSState n)
      have hrestNodup : rest.Nodup := hnodup.tail
      have hrestSubset : rest.toFinset ⊆ seen := by
        intro u hu
        apply hsubset
        simp only [List.mem_toFinset, List.mem_cons]
        right
        simpa using! hu
      have hdisjoint : List.Disjoint rest C.toList := by
        rw [List.disjoint_left]
        intro u hurest huC
        have huseen : u ∈ seen := hrestSubset (by simpa using! hurest)
        have huC' : u ∈ C := by simpa using! huC
        change u ∈ newChildren G seen v at huC'
        have hunseen : u ∉ seen :=
          ((mem_newChildren_iff G seen v u).mp huC').1
        exact hunseen huseen
      constructor
      · exact hrestNodup.append (Finset.nodup_toList C) hdisjoint
      · intro u hu
        rw [List.toFinset_append] at hu
        rcases Finset.mem_union.mp hu with hurest | huC
        · exact Finset.mem_union_left C (hrestSubset hurest)
        · exact Finset.mem_union_right seen (by simpa [C] using! huC)

theorem explore_queueWellFormed {n : ℕ} (G : Graph n) :
    ∀ j : ℕ, QueueWellFormed (explore G j)
  | 0 => initial_queueWellFormed n
  | j + 1 => queueWellFormed_bfsStep G (explore G j) (explore_queueWellFormed G j)

theorem explore_queue_nodup {n : ℕ} (G : Graph n) (j : ℕ) :
    (explore G j).queue.Nodup :=
  (explore_queueWellFormed G j).1

theorem explore_queue_subset_seen {n : ℕ} (G : Graph n) (j : ℕ) :
    (explore G j).queue.toFinset ⊆ (explore G j).seen :=
  (explore_queueWellFormed G j).2

theorem processed_partition {n : ℕ} (G : Graph n) (j : ℕ) :
    Disjoint (processed G j) (explore G j).queue.toFinset ∧
      processed G j ∪ (explore G j).queue.toFinset = (explore G j).seen := by
  exact ⟨processed_disjoint_queue G j,
    processed_union_queue G j (explore_queue_subset_seen G j)⟩

theorem processed_card_add_queue_length {n : ℕ} (G : Graph n) (j : ℕ) :
    (processed G j).card + (explore G j).queue.length =
      (explore G j).seen.card := by
  have hpart := processed_partition G j
  rw [← hpart.2, Finset.card_union_of_disjoint hpart.1]
  congr 1
  exact (List.toFinset_card_of_nodup (explore_queue_nodup G j)).symm

/-! ## Exactly one processed vertex per successful step -/

def stateProcessed {n : ℕ} (s : BFSState n) : Finset (Fin n) :=
  s.seen \ s.queue.toFinset

@[simp] lemma stateProcessed_explore {n : ℕ} (G : Graph n) (j : ℕ) :
    stateProcessed (explore G j) = processed G j := rfl

lemma stateProcessed_active {n : ℕ} (G : Graph n) (seen : Finset (Fin n))
    (v : Fin n) (rest : List (Fin n)) (z : ℤ)
    (hnodup : (v :: rest).Nodup)
    (hsubset : (v :: rest).toFinset ⊆ seen) :
    stateProcessed (bfsStep G (⟨seen, v :: rest, z⟩ : BFSState n)) =
      insert v (stateProcessed (⟨seen, v :: rest, z⟩ : BFSState n)) := by
  have hvseen : v ∈ seen := hsubset (by simp)
  have hvrest : v ∉ rest := (List.nodup_cons.mp hnodup).1
  ext u
  by_cases huv : u = v
  · subst u
    simp [stateProcessed, bfsStep_queue_cons, newChildren, hvseen, hvrest]
  · by_cases huseen : u ∈ seen
    · simp [stateProcessed, bfsStep_queue_cons, newChildren, huv, huseen]
    · simp [stateProcessed, bfsStep_queue_cons, newChildren, huv, huseen]
      tauto

lemma stateProcessed_root {n : ℕ} (G : Graph n) (seen : Finset (Fin n))
    (z : ℤ) (h : ((Finset.univ : Finset (Fin n)) \ seen).Nonempty) :
    let v := ((Finset.univ : Finset (Fin n)) \ seen).min' h
    stateProcessed (bfsStep G (⟨seen, [], z⟩ : BFSState n)) =
      insert v (stateProcessed (⟨seen, [], z⟩ : BFSState n)) := by
  let v := ((Finset.univ : Finset (Fin n)) \ seen).min' h
  have hv : v ∉ seen := by
    exact (Finset.mem_sdiff.mp (Finset.min'_mem _ h)).2
  ext u
  by_cases huv : u = v
  · subst u
    simp [stateProcessed, bfsStep_queue_nil_of_nonempty G seen z h,
      newChildren, v, hv]
  · by_cases huseen : u ∈ seen
    · simp [stateProcessed, bfsStep_queue_nil_of_nonempty G seen z h,
        newChildren, v, huv, huseen]
    · simp [stateProcessed, bfsStep_queue_nil_of_nonempty G seen z h,
        newChildren, v, huv, huseen]

lemma stateProcessed_card_bfsStep {n : ℕ} (G : Graph n) (s : BFSState n)
    (hs : QueueWellFormed s) (hlt : (stateProcessed s).card < n) :
    (stateProcessed (bfsStep G s)).card = (stateProcessed s).card + 1 := by
  rcases s with ⟨seen, queue, z⟩
  rcases hs with ⟨hnodup, hsubset⟩
  cases queue with
  | cons v rest =>
      rw [stateProcessed_active G seen v rest z hnodup hsubset]
      rw [Finset.card_insert_of_notMem]
      simp [stateProcessed]
  | nil =>
      have hseenlt : seen.card < n := by
        simpa [stateProcessed] using! hlt
      have hcarduniv : (Finset.univ : Finset (Fin n)).card = n := by simp
      have hneutral : ((Finset.univ : Finset (Fin n)) \ seen).Nonempty := by
        apply Finset.sdiff_nonempty_of_card_lt_card
        simpa [hcarduniv] using! hseenlt
      rw [stateProcessed_root G seen z hneutral]
      rw [Finset.card_insert_of_notMem]
      have hvnot : ((Finset.univ : Finset (Fin n)) \ seen).min' hneutral ∉ seen :=
        (Finset.mem_sdiff.mp (Finset.min'_mem _ hneutral)).2
      simpa [stateProcessed] using! hvnot

theorem processed_card_of_le {n : ℕ} (G : Graph n) :
    ∀ j : ℕ, j ≤ n → (processed G j).card = j
  | 0, _ => by simp [processed, initialState]
  | j + 1, hj => by
      have hjlt : j < n := Nat.lt_of_succ_le hj
      have ih := processed_card_of_le G j (Nat.le_of_lt hjlt)
      rw [← stateProcessed_explore G (j + 1), explore_succ]
      rw [stateProcessed_card_bfsStep G (explore G j)
        (explore_queueWellFormed G j) (by simpa [stateProcessed_explore, ih])]
      simpa [stateProcessed_explore, ih]

theorem processed_card_at_order {n : ℕ} (G : Graph n) :
    (processed G n).card = n := processed_card_of_le G n le_rfl

theorem processed_at_order_eq_univ {n : ℕ} (G : Graph n) :
    processed G n = Finset.univ := by
  apply Finset.eq_univ_of_card
  simpa using! processed_card_at_order G

theorem queue_at_order_eq_nil {n : ℕ} (G : Graph n) :
    (explore G n).queue = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro u hu
  have huq : u ∈ (explore G n).queue.toFinset := by simpa using! hu
  have hdis := (processed_partition G n).1
  exact Finset.disjoint_left.mp hdis (by simp [processed_at_order_eq_univ G]) huq

theorem seen_at_order_eq_univ {n : ℕ} (G : Graph n) :
    (explore G n).seen = Finset.univ := by
  rw [← (processed_partition G n).2, processed_at_order_eq_univ]
  simp

theorem bfsStep_at_order_stationary {n : ℕ} (G : Graph n) :
    bfsStep G (explore G n) = explore G n := by
  have hq := queue_at_order_eq_nil G
  have hs := seen_at_order_eq_univ G
  rcases hstate : explore G n with ⟨seen, queue, z⟩
  simp only [hstate, BFSState.queue] at hq
  simp only [hstate, BFSState.seen] at hs
  subst queue
  subst seen
  apply bfsStep_queue_nil_of_empty
  simp

/-! ## Closure of processed vertices and completed components -/

def ProcessedClosed {n : ℕ} (G : Graph n) (s : BFSState n) : Prop :=
  ∀ u ∈ stateProcessed s, ∀ v, adj G u v → v ∈ s.seen

@[simp] lemma initial_processedClosed {n : ℕ} (G : Graph n) :
    ProcessedClosed G (initialState n) := by
  simp [ProcessedClosed, stateProcessed, initialState]

lemma processedClosed_bfsStep {n : ℕ} (G : Graph n) (s : BFSState n)
    (hs : QueueWellFormed s) (hclosed : ProcessedClosed G s) :
    ProcessedClosed G (bfsStep G s) := by
  rcases s with ⟨seen, queue, z⟩
  rcases hs with ⟨hnodup, hsubset⟩
  cases queue with
  | cons head rest =>
      have hproc := stateProcessed_active G seen head rest z hnodup hsubset
      rw [ProcessedClosed]
      intro x hx v hxv
      rw [hproc] at hx
      rw [bfsStep_queue_cons]
      rcases Finset.mem_insert.mp hx with rfl | hxold
      · by_cases hvseen : v ∈ seen
        · exact Finset.mem_union_left _ hvseen
        · exact Finset.mem_union_right _
            ((mem_newChildren_iff G seen x v).mpr ⟨hvseen, hxv⟩)
      · exact Finset.mem_union_left _ (hclosed x hxold v hxv)
  | nil =>
      by_cases h : ((Finset.univ : Finset (Fin n)) \ seen).Nonempty
      · let u := ((Finset.univ : Finset (Fin n)) \ seen).min' h
        have hproc := stateProcessed_root G seen z h
        rw [ProcessedClosed]
        intro x hx v hxv
        rw [hproc] at hx
        rw [bfsStep_queue_nil_of_nonempty G seen z h]
        rcases Finset.mem_insert.mp hx with rfl | hxold
        · by_cases hvdisc : v ∈ insert u seen
          · exact Finset.mem_union_left _ hvdisc
          · exact Finset.mem_union_right _
              ((mem_newChildren_iff G (insert u seen) u v).mpr ⟨hvdisc, hxv⟩)
        · exact Finset.mem_union_left _ (Finset.mem_insert_of_mem (hclosed x hxold v hxv))
      · rw [bfsStep_queue_nil_of_empty G seen z h]
        exact hclosed

theorem explore_processedClosed {n : ℕ} (G : Graph n) :
    ∀ j : ℕ, ProcessedClosed G (explore G j)
  | 0 => initial_processedClosed G
  | j + 1 => processedClosed_bfsStep G (explore G j)
      (explore_queueWellFormed G j) (explore_processedClosed G j)

theorem component_subset_processed_of_queue_empty {n : ℕ} (G : Graph n)
    (j : ℕ) (hqueue : (explore G j).queue = [])
    {v : Fin n} (hv : v ∈ processed G j) :
    componentOf G v ⊆ processed G j := by
  intro u hu
  rw [mem_componentOf_iff] at hu
  have hseenproc : (explore G j).seen = processed G j := by
    rw [← (processed_partition G j).2, hqueue]
    simp
  induction hu with
  | refl => exact hv
  | tail hreach hadj ih =>
      rw [← hseenproc]
      exact explore_processedClosed G j _ ih _ hadj

theorem component_dichotomy_of_queue_empty {n : ℕ} (G : Graph n)
    (j : ℕ) (hqueue : (explore G j).queue = [])
    {S : Finset (Fin n)} (hS : S ∈ components G) :
    S ⊆ processed G j ∨ Disjoint S (processed G j) := by
  rcases (mem_components_iff G S).mp hS with ⟨r, rfl⟩
  by_cases hmeet : ∃ v, v ∈ componentOf G r ∧ v ∈ processed G j
  · left
    rcases hmeet with ⟨v, hvr, hvp⟩
    have hrv : reach G r v := (mem_componentOf_iff G r v).mp hvr
    rw [componentOf_eq_of_reach hrv]
    exact component_subset_processed_of_queue_empty G j hqueue hvp
  · right
    rw [Finset.disjoint_left]
    intro v hvS hvp
    exact hmeet ⟨v, hvS, hvp⟩

/-! ## Walk, queue, roots, and record minima -/

def rootStarts {n : ℕ} (s : BFSState n) : Prop :=
  s.queue = [] ∧ s.seen ≠ Finset.univ

def rootCount {n : ℕ} (G : Graph n) : ℕ → ℕ
  | 0 => 0
  | j + 1 => rootCount G j + if rootStarts (explore G j) then 1 else 0

@[simp] lemma rootCount_zero {n : ℕ} (G : Graph n) : rootCount G 0 = 0 := rfl

@[simp] lemma rootCount_succ {n : ℕ} (G : Graph n) (j : ℕ) :
    rootCount G (j + 1) =
      rootCount G j + if rootStarts (explore G j) then 1 else 0 := rfl

lemma neutral_nonempty_iff {n : ℕ} (seen : Finset (Fin n)) :
    ((Finset.univ : Finset (Fin n)) \ seen).Nonempty ↔ seen ≠ Finset.univ := by
  rw [Finset.sdiff_nonempty]
  constructor
  · intro h hseen
    exact h (by simp [hseen])
  · intro h hsub
    apply h
    exact (Finset.Subset.antisymm hsub (Finset.subset_univ seen)).symm

theorem walk_eq_queue_sub_rootCount {n : ℕ} (G : Graph n) :
    ∀ j : ℕ, (explore G j).walk =
      ((explore G j).queue.length : ℤ) - (rootCount G j : ℤ)
  | 0 => by simp [initialState]
  | j + 1 => by
      have ih := walk_eq_queue_sub_rootCount G j
      rcases hstate : explore G j with ⟨seen, queue, z⟩
      simp only [hstate, BFSState.walk, BFSState.queue] at ih
      cases queue with
      | cons v rest =>
          rw [explore_succ, hstate, bfsStep_queue_cons]
          simp [rootCount, rootStarts, hstate, List.length_append,
            Finset.length_toList] at ih ⊢
          omega
      | nil =>
          by_cases h : ((Finset.univ : Finset (Fin n)) \ seen).Nonempty
          · have hne : seen ≠ Finset.univ := (neutral_nonempty_iff seen).mp h
            rw [explore_succ, hstate, bfsStep_queue_nil_of_nonempty G seen z h]
            simp [rootCount, rootStarts, hstate, hne, Finset.length_toList] at ih ⊢
            omega
          · have heq : seen = Finset.univ := by
              by_contra hne
              exact h ((neutral_nonempty_iff seen).mpr hne)
            rw [explore_succ, hstate, bfsStep_queue_nil_of_empty G seen z h]
            simp [rootCount, rootStarts, hstate, heq] at ih ⊢
            exact ih

theorem walk_eq_neg_rootCount_iff {n : ℕ} (G : Graph n) (j : ℕ) :
    (explore G j).walk = -((rootCount G j : ℕ) : ℤ) ↔
      (explore G j).queue = [] := by
  rw [walk_eq_queue_sub_rootCount]
  constructor
  · intro h
    have hlen : (explore G j).queue.length = 0 := by omega
    exact List.length_eq_zero_iff.mp hlen
  · intro h
    simp [h]

/-! ## Rank endpoint and integrated shared export -/

structure FiniteBridge {n : ℕ} (G : Graph n) : Prop where
  queue_nodup : ∀ j, (explore G j).queue.Nodup
  queue_subset_seen : ∀ j, (explore G j).queue.toFinset ⊆ (explore G j).seen
  processed_card : ∀ j, j ≤ n → (processed G j).card = j
  processed_closed : ∀ j, ProcessedClosed G (explore G j)
  completed_component : ∀ j, (explore G j).queue = [] →
    ∀ v ∈ processed G j, componentOf G v ⊆ processed G j
  component_dichotomy : ∀ j, (explore G j).queue = [] →
    ∀ S ∈ components G, S ⊆ processed G j ∨ Disjoint S (processed G j)
  walk_queue_roots : ∀ j, (explore G j).walk + (rootCount G j : ℤ) =
    ((explore G j).queue.length : ℤ)
  record_iff : ∀ j, (explore G j).walk = -((rootCount G j : ℕ) : ℤ) ↔
    (explore G j).queue = []
  rank_threshold : ∀ i h, 0 < i → 0 < h →
    (rankSize G i < h ↔ countGE G h ≤ i - 1)

end

end Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_Finite


/-!
# The concrete exploration interpolation

The floor formula in `rawExploration` is bundled as an actual continuous map.
Continuity is proved from a finite closed cover: one affine cell for each
successful BFS step and one stationary tail after all `n` vertices have been
processed.
-/

namespace Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_Interpolation

open Erdos745.WrapUp
open Set
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_Finite

noncomputable section
attribute [local instance] Classical.propDecidable

/-! ## Stationarity after the finite exploration has ended -/

theorem explore_add_order {n : ℕ} (G : Graph n) :
    ∀ k : ℕ, explore G (n + k) = explore G n
  | 0 => by simp
  | k + 1 => by
      rw [Nat.add_succ, explore_succ, explore_add_order G k,
        bfsStep_at_order_stationary]

theorem explore_eq_at_order_of_le {n : ℕ} (G : Graph n) {j : ℕ}
    (hj : n ≤ j) : explore G j = explore G n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hj
  exact explore_add_order G k

theorem walk_eq_at_order_of_le {n : ℕ} (G : Graph n) {j : ℕ}
    (hj : n ≤ j) : (explore G j).walk = (explore G n).walk := by
  rw [explore_eq_at_order_of_le G hj]

/-! ## A generic eventually-stationary polygonal interpolation -/

def linearInterpolation (z : ℕ → ℝ) (x : NNReal) : ℝ :=
  let j : ℕ := ⌊(x : ℝ)⌋₊
  let theta : ℝ := (x : ℝ) - j
  (1 - theta) * z j + theta * z (j + 1)

def cellAffine (z : ℕ → ℝ) (j : ℕ) (x : NNReal) : ℝ :=
  let theta : ℝ := (x : ℝ) - j
  (1 - theta) * z j + theta * z (j + 1)

lemma continuous_cellAffine (z : ℕ → ℝ) (j : ℕ) :
    Continuous (cellAffine z j) := by
  unfold cellAffine
  fun_prop

lemma linearInterpolation_eq_cellAffine (z : ℕ → ℝ) (j : ℕ)
    {x : NNReal} (hx : x ∈ Icc (j : NNReal) (j + 1 : NNReal)) :
    linearInterpolation z x = cellAffine z j x := by
  rcases hx with ⟨hx0, hx1⟩
  by_cases hright : x = (j + 1 : NNReal)
  · subst x
    have hcoe : (((j + 1 : NNReal) : ℝ)) = (j + 1 : ℕ) := by norm_num
    have hfloor : ⌊((j : ℝ) + 1)⌋₊ = j + 1 := by
      rw [← Nat.cast_one, ← Nat.cast_add, Nat.floor_natCast]
    simp [linearInterpolation, cellAffine, hcoe, hfloor]
  · have hltNN : x < (j + 1 : NNReal) := lt_of_le_of_ne hx1 hright
    have hcast0 : (j : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx0
    have hcast1 : (x : ℝ) < (j : ℝ) + 1 := by
      exact_mod_cast hltNN
    have hfloor : ⌊(x : ℝ)⌋₊ = j :=
      Nat.floor_eq_on_Ico j (x : ℝ) ⟨hcast0, hcast1⟩
    simp [linearInterpolation, cellAffine, hfloor]

lemma linearInterpolation_eq_tail (z : ℕ → ℝ) (n : ℕ)
    (hstationary : ∀ j, n ≤ j → z j = z n)
    {x : NNReal} (hx : x ∈ Ici (n : NNReal)) :
    linearInterpolation z x = z n := by
  have hcast : (n : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  have hfloor : n ≤ ⌊(x : ℝ)⌋₊ := Nat.le_floor hcast
  have hfloor' : n ≤ ⌊(x : ℝ)⌋₊ + 1 := le_trans hfloor (Nat.le_succ _)
  rw [linearInterpolation]
  rw [hstationary _ hfloor, hstationary _ hfloor']
  ring

def interpolationCell (n : ℕ) : Option (Fin n) → Set NNReal
  | none => Ici (n : NNReal)
  | some j => Icc (j.val : NNReal) (j.val + 1 : NNReal)

lemma interpolationCell_cover (n : ℕ) :
    ⋃ i : Option (Fin n), interpolationCell n i = Set.univ := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  by_cases htail : (n : NNReal) ≤ x
  · exact ⟨none, htail⟩
  · have hxltNN : x < (n : NNReal) := lt_of_not_ge htail
    have hxlt : (x : ℝ) < (n : ℝ) := by exact_mod_cast hxltNN
    have hjlt : ⌊(x : ℝ)⌋₊ < n :=
      (Nat.floor_lt (show 0 ≤ (x : ℝ) by positivity)).mpr hxlt
    let j : Fin n := ⟨⌊(x : ℝ)⌋₊, hjlt⟩
    refine ⟨some j, ?_⟩
    change x ∈ Icc (j.val : NNReal) (j.val + 1 : NNReal)
    constructor
    · exact_mod_cast Nat.floor_le (show 0 ≤ (x : ℝ) by positivity)
    · have hlt : (x : ℝ) < (⌊(x : ℝ)⌋₊ : ℝ) + 1 :=
        Nat.lt_floor_add_one (x : ℝ)
      exact_mod_cast hlt.le

lemma interpolationCell_closed (n : ℕ) (i : Option (Fin n)) :
    IsClosed (interpolationCell n i) := by
  cases i with
  | none => exact isClosed_Ici
  | some j => exact isClosed_Icc

theorem continuous_linearInterpolation_of_stationary (z : ℕ → ℝ) (n : ℕ)
    (hstationary : ∀ j, n ≤ j → z j = z n) :
    Continuous (linearInterpolation z) := by
  let cells := interpolationCell n
  apply (locallyFinite_of_finite cells).continuous (interpolationCell_cover n)
      (interpolationCell_closed n)
  intro i
  cases i with
  | none =>
      exact continuousOn_const.congr fun x hx =>
        linearInterpolation_eq_tail z n hstationary hx
  | some j =>
      exact (continuous_cellAffine z j.val).continuousOn.congr fun x hx =>
        linearInterpolation_eq_cellAffine z j.val hx

/-! ## Identification with the public raw formula -/

def explorationScale (n : ℕ) : NNReal :=
  NNReal.mk (n23 n) (Real.rpow_nonneg (Nat.cast_nonneg n) _)

@[simp] lemma explorationScale_coe (n : ℕ) :
    (explorationScale n : ℝ) = n23 n := by simp [explorationScale]

def explorationWalk {n : ℕ} (G : Graph n) (j : ℕ) : ℝ :=
  ((explore G j).walk : ℝ)

lemma explorationWalk_stationary {n : ℕ} (G : Graph n) :
    ∀ j, n ≤ j → explorationWalk G j = explorationWalk G n := by
  intro j hj
  simp only [explorationWalk, walk_eq_at_order_of_le G hj]

def continuousRawExploration {n : ℕ} (G : Graph n) : BrownianPath where
  toFun t := linearInterpolation (explorationWalk G) (t * explorationScale n) / n13 n
  continuous_toFun :=
    (continuous_linearInterpolation_of_stationary (explorationWalk G) n
      (explorationWalk_stationary G)).comp
        (continuous_id.mul continuous_const) |>.div_const _

lemma continuousRawExploration_apply {n : ℕ} (G : Graph n) (t : NNReal) :
    continuousRawExploration G t = rawExploration G t := by
  simp [continuousRawExploration, rawExploration, linearInterpolation,
    explorationWalk, explorationScale]

def explorationInterpolation : ExplorationPaths :=
  fun _n G => continuousRawExploration G

theorem explorationInterpolation_isInterpolation :
    IsInterpolation explorationInterpolation := by
  intro n G t
  exact continuousRawExploration_apply G t

end

end Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_Interpolation


/-!
# Exact adaptive reveal trace

The trace records the public BFS state together with all positive and negative
answers to the incident edge queries made so far.  Its BFS projection is
definitionally the public `explore`; no competing exploration is introduced.
-/

namespace Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_Reveal

open Erdos745.WrapUp
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_Finite

noncomputable section
attribute [local instance] Classical.propDecidable

def incidentQuery {n : ℕ} (v : Fin n) (discovered : Finset (Fin n)) : Graph n :=
  (Finset.univ : Finset (Edge n)).filter fun e =>
    (e.val.1 = v ∧ e.val.2 ∉ discovered) ∨
    (e.val.2 = v ∧ e.val.1 ∉ discovered)

@[simp] lemma mem_incidentQuery_iff {n : ℕ} (v : Fin n)
    (discovered : Finset (Fin n)) (e : Edge n) :
    e ∈ incidentQuery v discovered ↔
      (e.val.1 = v ∧ e.val.2 ∉ discovered) ∨
      (e.val.2 = v ∧ e.val.1 ∉ discovered) := by
  simp [incidentQuery]

def revealQuery {n : ℕ} (s : BFSState n) : Graph n :=
  match selectRoot s with
  | none => ∅
  | some (v, _rest, discovered) => incidentQuery v discovered

@[simp] lemma revealQuery_queue_cons {n : ℕ} (seen : Finset (Fin n))
    (v : Fin n) (rest : List (Fin n)) (z : ℤ) :
    revealQuery (⟨seen, v :: rest, z⟩ : BFSState n) = incidentQuery v seen := by
  rfl

lemma revealQuery_queue_nil_of_nonempty {n : ℕ} (seen : Finset (Fin n))
    (z : ℤ) (h : ((Finset.univ : Finset (Fin n)) \ seen).Nonempty) :
    let v := ((Finset.univ : Finset (Fin n)) \ seen).min' h
    revealQuery (⟨seen, [], z⟩ : BFSState n) = incidentQuery v (insert v seen) := by
  simp [revealQuery, selectRoot, h]

lemma revealQuery_queue_nil_of_empty {n : ℕ} (seen : Finset (Fin n))
    (z : ℤ) (h : ¬ ((Finset.univ : Finset (Fin n)) \ seen).Nonempty) :
    revealQuery (⟨seen, [], z⟩ : BFSState n) = ∅ := by
  simp [revealQuery, selectRoot, h]

structure RevealState (n : ℕ) where
  bfs : BFSState n
  yes : Graph n
  no : Graph n

def initialReveal (n : ℕ) : RevealState n :=
  ⟨initialState n, ∅, ∅⟩

def revealStep {n : ℕ} (G : Graph n) (r : RevealState n) : RevealState n :=
  let query := revealQuery r.bfs
  ⟨bfsStep G r.bfs, r.yes ∪ (G ∩ query), r.no ∪ (query \ G)⟩

def revealTrace {n : ℕ} (G : Graph n) : ℕ → RevealState n
  | 0 => initialReveal n
  | j + 1 => revealStep G (revealTrace G j)

@[simp] lemma revealTrace_zero {n : ℕ} (G : Graph n) :
    revealTrace G 0 = initialReveal n := rfl

@[simp] lemma revealTrace_succ {n : ℕ} (G : Graph n) (j : ℕ) :
    revealTrace G (j + 1) = revealStep G (revealTrace G j) := rfl

@[simp] lemma initialReveal_bfs (n : ℕ) : (initialReveal n).bfs = initialState n := rfl

@[simp] lemma initialReveal_yes (n : ℕ) : (initialReveal n).yes = ∅ := rfl

@[simp] lemma initialReveal_no (n : ℕ) : (initialReveal n).no = ∅ := rfl

@[simp] lemma revealStep_bfs {n : ℕ} (G : Graph n) (r : RevealState n) :
    (revealStep G r).bfs = bfsStep G r.bfs := rfl

@[simp] lemma revealStep_yes {n : ℕ} (G : Graph n) (r : RevealState n) :
    (revealStep G r).yes = r.yes ∪ (G ∩ revealQuery r.bfs) := rfl

@[simp] lemma revealStep_no {n : ℕ} (G : Graph n) (r : RevealState n) :
    (revealStep G r).no = r.no ∪ (revealQuery r.bfs \ G) := rfl

theorem revealTrace_bfs {n : ℕ} (G : Graph n) :
    ∀ j : ℕ, (revealTrace G j).bfs = explore G j
  | 0 => rfl
  | j + 1 => by
      rw [revealTrace_succ, revealStep_bfs, revealTrace_bfs G j]
      rfl

theorem revealTrace_yes_succ {n : ℕ} (G : Graph n) (j : ℕ) :
    (revealTrace G (j + 1)).yes =
      (revealTrace G j).yes ∪ (G ∩ revealQuery (explore G j)) := by
  rw [revealTrace_succ, revealStep_yes, revealTrace_bfs]

theorem revealTrace_no_succ {n : ℕ} (G : Graph n) (j : ℕ) :
    (revealTrace G (j + 1)).no =
      (revealTrace G j).no ∪ (revealQuery (explore G j) \ G) := by
  rw [revealTrace_succ, revealStep_no, revealTrace_bfs]

theorem revealTrace_coverage_succ {n : ℕ} (G : Graph n) (j : ℕ) :
    (revealTrace G (j + 1)).yes ∪ (revealTrace G (j + 1)).no =
      ((revealTrace G j).yes ∪ (revealTrace G j).no) ∪
        revealQuery (explore G j) := by
  rw [revealTrace_yes_succ, revealTrace_no_succ]
  ext e
  simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
  tauto

theorem revealTrace_yes_mono {n : ℕ} (G : Graph n) :
    Monotone (fun j => (revealTrace G j).yes) := by
  apply monotone_nat_of_le_succ
  intro j
  rw [revealTrace_yes_succ]
  exact Finset.subset_union_left

theorem revealTrace_no_mono {n : ℕ} (G : Graph n) :
    Monotone (fun j => (revealTrace G j).no) := by
  apply monotone_nat_of_le_succ
  intro j
  rw [revealTrace_no_succ]
  exact Finset.subset_union_left

theorem revealTrace_yes_subset_graph {n : ℕ} (G : Graph n) :
    ∀ j : ℕ, (revealTrace G j).yes ⊆ G
  | 0 => by simp [initialReveal]
  | j + 1 => by
      rw [revealTrace_yes_succ]
      exact Finset.union_subset (revealTrace_yes_subset_graph G j)
        Finset.inter_subset_left

theorem revealTrace_no_disjoint_graph {n : ℕ} (G : Graph n) :
    ∀ j : ℕ, Disjoint (revealTrace G j).no G
  | 0 => by simp [initialReveal]
  | j + 1 => by
      rw [revealTrace_no_succ, Finset.disjoint_union_left]
      refine ⟨revealTrace_no_disjoint_graph G j, ?_⟩
      rw [Finset.disjoint_left]
      intro e he hG
      exact (Finset.mem_sdiff.mp he).2 hG

theorem revealTrace_patternEvent {n : ℕ} (G : Graph n) (j : ℕ) :
    patternEvent (revealTrace G j).yes (revealTrace G j).no G := by
  exact ⟨revealTrace_yes_subset_graph G j,
    revealTrace_no_disjoint_graph G j⟩

theorem revealTrace_yes_no_disjoint {n : ℕ} (G : Graph n) (j : ℕ) :
    Disjoint (revealTrace G j).yes (revealTrace G j).no := by
  rw [Finset.disjoint_left]
  intro e heyes heno
  exact Finset.disjoint_left.mp (revealTrace_no_disjoint_graph G j)
    heno (revealTrace_yes_subset_graph G j heyes)

end

end Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_Reveal


/-!
# Deterministic completion bridge for the exploration tails

A queue-empty time completes every component touched earlier.  This module
states that fact directly with the public floor conventions of
`unfinishedEarly`; the probabilistic C04(b) argument only has to produce such
a completion time before its deterministic deadline.
-/

namespace Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_TailsFinite

open Erdos745.WrapUp
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_Finite

noncomputable section
attribute [local instance] Classical.propDecidable

lemma stateProcessed_subset_bfsStep {n : ℕ} (G : Graph n) (s : BFSState n)
    (hs : QueueWellFormed s) :
    stateProcessed s ⊆ stateProcessed (bfsStep G s) := by
  rcases s with ⟨seen, queue, z⟩
  rcases hs with ⟨hnodup, hsubset⟩
  cases queue with
  | cons v rest =>
      rw [stateProcessed_active G seen v rest z hnodup hsubset]
      exact Finset.subset_insert v _
  | nil =>
      by_cases h : ((Finset.univ : Finset (Fin n)) \ seen).Nonempty
      · rw [stateProcessed_root G seen z h]
        exact Finset.subset_insert _ _
      · rw [bfsStep_queue_nil_of_empty G seen z h]

lemma processed_subset_succ {n : ℕ} (G : Graph n) (j : ℕ) :
    processed G j ⊆ processed G (j + 1) := by
  rw [← stateProcessed_explore, ← stateProcessed_explore, explore_succ]
  exact stateProcessed_subset_bfsStep G (explore G j)
    (explore_queueWellFormed G j)

theorem processed_monotone {n : ℕ} (G : Graph n) :
    Monotone (processed G) := by
  exact monotone_nat_of_le_succ (processed_subset_succ G)

theorem seen_subset_processed_of_queue_empty {n : ℕ} (G : Graph n)
    {j l : ℕ} (hjl : j ≤ l) (hqueue : (explore G l).queue = []) :
    (explore G j).seen ⊆ processed G l := by
  intro v hv
  have hseen : v ∈ (explore G l).seen := seen_monotone G hjl hv
  rw [← (processed_partition G l).2, hqueue] at hseen
  simpa using! hseen

theorem component_seen_subset_processed_of_queue_empty {n : ℕ}
    (G : Graph n) {j l : ℕ} (hjl : j ≤ l)
    (hqueue : (explore G l).queue = [])
    {S : Finset (Fin n)} (hS : S ∈ components G)
    (hmeet : ¬ Disjoint S (explore G j).seen) :
    S ⊆ processed G l := by
  rcases (Finset.not_disjoint_iff.mp hmeet) with ⟨v, hvS, hvseen⟩
  have hvproc : v ∈ processed G l :=
    seen_subset_processed_of_queue_empty G hjl hqueue hvseen
  rcases component_dichotomy_of_queue_empty G l hqueue hS with hsub | hdis
  · exact hsub
  · exact False.elim (Finset.disjoint_left.mp hdis hvS hvproc)

theorem completion_between_not_unfinished {n : ℕ} (G : Graph n)
    {j l q : ℕ} (hjl : j ≤ l) (hlq : l ≤ q)
    (hqueue : (explore G l).queue = []) :
    ¬ (∃ S ∈ components G,
      ¬ Disjoint S (explore G j).seen ∧ ¬ S ⊆ processed G q) := by
  rintro ⟨S, hS, hmeet, hnot⟩
  have hcomplete : S ⊆ processed G l :=
    component_seen_subset_processed_of_queue_empty G hjl hqueue hS hmeet
  exact hnot (hcomplete.trans (processed_monotone G hlq))

theorem queue_empty_between_not_unfinishedEarly {n : ℕ} (G : Graph n)
    (T U : ℝ) {l : ℕ}
    (hTl : ⌊T * n23 n⌋₊ ≤ l) (hlU : l ≤ ⌊U * n23 n⌋₊)
    (hqueue : (explore G l).queue = []) :
    ¬ unfinishedEarly G T U := by
  unfold unfinishedEarly
  exact completion_between_not_unfinished G hTl hlU hqueue

end

end Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_TailsFinite


/-!
# The normalized finite fixed-edge law

For every admissible pair `M ≤ capacity n`, this module realizes the public
finite sums as integration against the uniform PMF on `fixedGraphs n M`.
The construction also supplies the measurable path pushforward used in the
weak-convergence argument.
-/

namespace Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_FiniteLaw

open Erdos745.WrapUp
open MeasureTheory
open Erdos745.WrapUp.Proofs.Internal.W01_ENUM_Finite
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_Interpolation

noncomputable section
attribute [local instance] Classical.propDecidable

local instance graphMeasurableSpace (n : ℕ) : MeasurableSpace (Graph n) := ⊤
local instance : MeasurableSpace BrownianPath := borel BrownianPath
local instance : BorelSpace BrownianPath := ⟨rfl⟩

def fixedPMF (n M : ℕ) (hM : M ≤ capacity n) : PMF (Graph n) :=
  PMF.uniformOfFinset (fixedGraphs n M) (fixedGraphs_nonempty hM)

def fixedMeasure (n M : ℕ) (hM : M ≤ capacity n) : Measure (Graph n) :=
  (fixedPMF n M hM).toMeasure

instance fixedMeasure_probability (n M : ℕ) (hM : M ≤ capacity n) :
    IsProbabilityMeasure (fixedMeasure n M hM) := by
  unfold fixedMeasure
  exact PMF.toMeasure.isProbabilityMeasure (fixedPMF n M hM)

@[simp] theorem fixedMeasure_univ (n M : ℕ) (hM : M ≤ capacity n) :
    fixedMeasure n M hM Set.univ = 1 := by
  exact measure_univ

theorem fixedMeasure_apply (n M : ℕ) (hM : M ≤ capacity n)
    (A : Graph n → Prop) :
    fixedMeasure n M hM {G | A G} =
      ((fixedGraphs n M).filter A).card / (fixedGraphs n M).card := by
  rw [fixedMeasure, fixedPMF,
    PMF.toMeasure_uniformOfFinset_apply (fixedGraphs_nonempty hM)
      {G | A G} (by simp)]
  congr 2

theorem fixedMeasure_apply_toReal (n M : ℕ) (hM : M ≤ capacity n)
    (A : Graph n → Prop) :
    (fixedMeasure n M hM {G | A G}).toReal = probM n M A := by
  rw [fixedMeasure_apply]
  simp [probM, ENNReal.toReal_div]

theorem integral_fixedMeasure (n M : ℕ) (hM : M ≤ capacity n)
    (f : Graph n → ℝ) :
    ∫ G, f G ∂fixedMeasure n M hM = expectM n M f := by
  rw [fixedMeasure, PMF.integral_eq_sum]
  unfold fixedPMF expectM
  simp only [PMF.uniformOfFinset_apply, smul_eq_mul]
  calc
    _ = ∑ x, if x ∈ fixedGraphs n M then
          ((fixedGraphs n M).card : ℝ)⁻¹ * f x else 0 := by
            apply Finset.sum_congr rfl
            intro x _hx
            by_cases hx : x ∈ fixedGraphs n M <;> simp [hx]
    _ = ∑ x ∈ fixedGraphs n M,
          ((fixedGraphs n M).card : ℝ)⁻¹ * f x := by
            rw [← Finset.sum_filter]
            simp
    _ = (fixedGraphs n M).sum f / ((fixedGraphs n M).card : ℝ) := by
            rw [← Finset.mul_sum]
            simp only [div_eq_mul_inv]
            ring

theorem measurable_from_fixed_graphs {n : ℕ} {β : Type*}
    [MeasurableSpace β] (f : Graph n → β) : Measurable f := by
  exact measurable_of_finite f

theorem measurable_explorationInterpolation (n : ℕ) :
    Measurable (fun G : Graph n => explorationInterpolation n G) := by
  exact measurable_from_fixed_graphs _

def explorationPathMeasure (n M : ℕ) (hM : M ≤ capacity n) : PathLaw :=
  Measure.map (fun G : Graph n => explorationInterpolation n G)
    (fixedMeasure n M hM)

instance explorationPathMeasure_probability (n M : ℕ)
    (hM : M ≤ capacity n) :
    IsProbabilityMeasure (explorationPathMeasure n M hM) := by
  unfold explorationPathMeasure
  exact Measure.isProbabilityMeasure_map
    (measurable_explorationInterpolation n).aemeasurable

theorem explorationPathMeasure_integral (n M : ℕ)
    (hM : M ≤ capacity n) (F : BrownianPath → ℝ) (hF : Continuous F) :
    ∫ w, F w ∂explorationPathMeasure n M hM =
      expectM n M (fun G => F (explorationInterpolation n G)) := by
  unfold explorationPathMeasure
  calc
    ∫ w, F w ∂Measure.map (fun G : Graph n => explorationInterpolation n G)
        (fixedMeasure n M hM) =
        ∫ G, F (explorationInterpolation n G) ∂fixedMeasure n M hM :=
      MeasureTheory.integral_map
        (measurable_explorationInterpolation n).aemeasurable
        hF.aestronglyMeasurable
    _ = expectM n M (fun G => F (explorationInterpolation n G)) :=
      integral_fixedMeasure n M hM _

end

end Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_FiniteLaw
