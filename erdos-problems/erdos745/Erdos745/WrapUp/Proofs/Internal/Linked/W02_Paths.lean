module

public import Mathlib
public import Erdos745.WrapUp.Proofs.Internal.Linked.W02_Relabel
public import Erdos745.WrapUp.Proofs.Internal.Linked.W02_CoreForest

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local simp] Pi.div_def Pi.mul_def Pi.add_def Pi.sub_def Pi.neg_def Pi.inv_def Function.comp_def Pi.pow_def Pi.smul_def Real.rpow_eq_pow

@[expose] public section


/-!
# Deterministic continuation through degree-two vertices

The suppression walk enters a degree-two vertex along one edge and must leave
along its unique other edge.  This file isolates that finite local operation
and a fuel-bounded follower.  The fuel parameter makes termination structural;
the later maximality proof shows that a connected positive-excess core reaches
a branch vertex before the vertex-cardinality fuel is exhausted.
-/

noncomputable section

namespace Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_PathFollow

attribute [local instance] Classical.propDecidable

/-- The unique continuation after entering a degree-two vertex. -/
structure OtherNeighborSpec {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (prev curr : V) where
  next : V
  adjacent : H.Adj curr next
  ne_prev : next ≠ prev
  unique : ∀ z, H.Adj curr z → z ≠ prev → z = next

/-- A degree-two vertex has exactly one neighbour other than the vertex from
which it was entered. -/
theorem exists_otherNeighborSpec {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) {prev curr : V} (hpc : H.Adj prev curr)
    (hdeg : H.degree curr = 2) : Nonempty (OtherNeighborSpec H prev curr) := by
  have hprev : prev ∈ H.neighborFinset curr := by
    simpa using! H.symm.symm _ _ hpc
  have hcard : ((H.neighborFinset curr).erase prev).card = 1 := by
    rw [Finset.card_erase_of_mem hprev,
      SimpleGraph.card_neighborFinset_eq_degree, hdeg]
  obtain ⟨next, hnextset⟩ := Finset.card_eq_one.mp hcard
  have hnextmem : next ∈ (H.neighborFinset curr).erase prev := by
    rw [hnextset]
    simp
  refine ⟨{
    next := next
    adjacent := by
      simpa using! (Finset.mem_of_mem_erase hnextmem)
    ne_prev := (Finset.mem_erase.mp hnextmem).1
    unique := ?_ }⟩
  intro z hz hzprev
  have hzmem : z ∈ (H.neighborFinset curr).erase prev := by
    exact Finset.mem_erase.mpr
      ⟨hzprev, by simpa using! hz⟩
  rw [hnextset] at hzmem
  simpa using! hzmem

/-- Chosen deterministic continuation at a degree-two vertex. -/
noncomputable def otherNeighborSpec {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) {prev curr : V} (hpc : H.Adj prev curr)
    (hdeg : H.degree curr = 2) : OtherNeighborSpec H prev curr :=
  Classical.choice (exists_otherNeighborSpec H hpc hdeg)

noncomputable def otherNeighbor {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) {prev curr : V} (hpc : H.Adj prev curr)
    (hdeg : H.degree curr = 2) : V :=
  (otherNeighborSpec H hpc hdeg).next

theorem otherNeighbor_adjacent {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) {prev curr : V} (hpc : H.Adj prev curr)
    (hdeg : H.degree curr = 2) :
    H.Adj curr (otherNeighbor H hpc hdeg) :=
  (otherNeighborSpec H hpc hdeg).adjacent

theorem otherNeighbor_ne_prev {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) {prev curr : V} (hpc : H.Adj prev curr)
    (hdeg : H.degree curr = 2) :
    otherNeighbor H hpc hdeg ≠ prev :=
  (otherNeighborSpec H hpc hdeg).ne_prev

theorem eq_otherNeighbor {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) {prev curr z : V} (hpc : H.Adj prev curr)
    (hdeg : H.degree curr = 2) (hcz : H.Adj curr z) (hz : z ≠ prev) :
    z = otherNeighbor H hpc hdeg :=
  (otherNeighborSpec H hpc hdeg).unique z hcz hz

/-- Follow the unique continuation through non-branch vertices.  The returned
list starts at `curr`.  Encountering a branch vertex stops immediately; fuel
exhaustion is the only other stopping condition. -/
noncomputable def follow {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (hmin : ∀ x, 2 ≤ H.degree x) :
    (fuel : ℕ) → (prev curr : V) → H.Adj prev curr → List V
  | 0, _prev, curr, _ => [curr]
  | fuel + 1, prev, curr, hpc =>
      if hbranch : 3 ≤ H.degree curr then
        [curr]
      else
        let hdeg : H.degree curr = 2 := by
          have htwo := hmin curr
          omega
        curr :: follow H hmin fuel curr
          (otherNeighbor H hpc hdeg) (otherNeighbor_adjacent H hpc hdeg)

@[simp]
theorem follow_zero {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (hmin : ∀ x, 2 ≤ H.degree x)
    {prev curr : V} (hpc : H.Adj prev curr) :
    follow H hmin 0 prev curr hpc = [curr] := by
  rfl

theorem head?_follow {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (hmin : ∀ x, 2 ≤ H.degree x)
    (fuel : ℕ) {prev curr : V} (hpc : H.Adj prev curr) :
    (follow H hmin fuel prev curr hpc).head? = some curr := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
      unfold follow
      split <;> rfl

/- Structural fuel bound for the deterministic follower. -/
end Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_PathFollow


/-!
# Edge-labelled kernel occurrences

Degree-two suppression naturally produces edge occurrences, not merely an
adjacency relation: two maximal paths can have the same branch endpoints and
a closed branch-to-branch path produces a loop.  This module keeps those
occurrences labelled until the final conversion to the symmetric-power kernel
array.  Consequently parallel occurrences and loops survive by definition.
-/

open scoped BigOperators

noncomputable section

namespace Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_EdgeLabelled

open Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_Mass
open Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_Occurrences

/-- Forget edge labels while retaining every occurrence with multiplicity. -/
def arrayOfOccurrences {v r : ℕ}
    (edge : Fin (v + r) → KernelIndex v) : KernelArray v r :=
  Sym.mk (List.ofFn edge : Multiset (KernelIndex v)) (by simp)

@[simp]
theorem coe_arrayOfOccurrences {v r : ℕ}
    (edge : Fin (v + r) → KernelIndex v) :
    ((arrayOfOccurrences edge : KernelArray v r) :
      Multiset (KernelIndex v)) = List.ofFn edge := by
  rfl

/-- Multiplicity in the resulting multigraph is literal occurrence count. -/
theorem degree_arrayOfOccurrences {v r : ℕ}
    (edge : Fin (v + r) → KernelIndex v) (i : Fin v) :
    W02_KERNEL_Mass.degree (arrayOfOccurrences edge) i =
      ∑ t : Fin (v + r), incidence i (edge t) := by
  simp [W02_KERNEL_Mass.degree, arrayOfOccurrences, List.map_ofFn, List.sum_ofFn,
    Function.comp_def]

/-- Underlying adjacency expressed directly through labelled occurrences.
The label remains available even when several occurrences share endpoints. -/
def occurrenceAdj {v r : ℕ}
    (edge : Fin (v + r) → KernelIndex v) (i j : Fin v) : Prop :=
  i ≠ j ∧ ∃ t,
    ((edge t).1.1 = i ∧ (edge t).1.2 = j) ∨
      ((edge t).1.1 = j ∧ (edge t).1.2 = i)

/-- Forgetting labels changes neither underlying adjacency nor connectivity. -/
theorem kernelAdj_arrayOfOccurrences_iff {v r : ℕ}
    (edge : Fin (v + r) → KernelIndex v) (i j : Fin v) :
    kernelAdj (arrayOfOccurrences edge) i j ↔ occurrenceAdj edge i j := by
  unfold kernelAdj occurrenceAdj
  change (i ≠ j ∧ ∃ p ∈ (List.ofFn edge : Multiset (KernelIndex v)),
      (p.1.1 = i ∧ p.1.2 = j) ∨ (p.1.1 = j ∧ p.1.2 = i)) ↔ _
  constructor
  · rintro ⟨hij, p, hp, hends⟩
    obtain ⟨t, ht⟩ := List.mem_ofFn.mp (by simpa using! hp)
    exact ⟨hij, t, ht ▸ hends⟩
  · rintro ⟨hij, t, hends⟩
    refine ⟨hij, edge t, ?_, hends⟩
    simpa using! (List.mem_ofFn.mpr ⟨t, rfl⟩)

/-- A labelled occurrence presentation with the two semantic facts required
of a kernel.  This is the native output type of the maximal-path recursion. -/
structure OccurrenceKernel (v r : ℕ) where
  edge : Fin (v + r) → KernelIndex v
  connected : ∀ i j, Relation.ReflTransGen (occurrenceAdj edge) i j
  minDegree : ∀ i, 3 ≤ ∑ t : Fin (v + r), incidence i (edge t)

namespace OccurrenceKernel

/-- The symmetric-power multigraph underlying a labelled occurrence kernel. -/
def array {v r : ℕ} (K : OccurrenceKernel v r) : KernelArray v r :=
  arrayOfOccurrences K.edge

theorem array_connected {v r : ℕ} (K : OccurrenceKernel v r) :
    kernelConnected K.array := by
  intro i j
  exact Relation.ReflTransGen.mono (fun a b hab =>
    (kernelAdj_arrayOfOccurrences_iff K.edge a b).2 hab) i j (K.connected i j)

theorem array_minDegree {v r : ℕ} (K : OccurrenceKernel v r) (i : Fin v) :
    3 ≤ W02_KERNEL_Mass.degree K.array i := by
  rw [array, degree_arrayOfOccurrences]
  exact K.minDegree i

/-- Every occurrence kernel is a member of the exact finite kernel family.
No quotient can erase loops or merge parallel occurrences before this point. -/
theorem array_mem_Kern {v r : ℕ} (K : OccurrenceKernel v r) :
    K.array ∈ Kern v r := by
  classical
  simp only [Kern, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨K.array_connected, K.array_minDegree⟩

/-- Package the occurrence kernel as the subtype consumed by expansion codes. -/
def choice {v r : ℕ} (K : OccurrenceKernel v r) :
    Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_Expansion.KernelChoice v r :=
  ⟨K.array, K.array_mem_Kern⟩

/-- Sorting the kernel slots only permutes the labelled occurrence multiset.
This is the precise bridge between a suppression recursion's path order and
the decoder's canonical occurrence order. -/
theorem ordered_edges_eq_occurrences {v r : ℕ} (K : OccurrenceKernel v r) :
    (orderedKernelEdges K.array : Multiset (KernelIndex v)) =
      (List.ofFn K.edge : Multiset (KernelIndex v)) := by
  rw [coe_orderedKernelEdges]
  rfl

end OccurrenceKernel

end Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_EdgeLabelled


/-!
# Maximal branch-path partitions

This is the durable output boundary of the degree-two follower.  Paths are
indexed by labelled multigraph occurrences, so closed paths remain loops and
distinct paths with equal endpoints remain parallel occurrences.  The two
multiset partition equalities state exactly that every core edge and every
non-branch vertex occurs once.
-/

open scoped BigOperators Sym2

noncomputable section

namespace Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_PathPartition

open Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_CoreConnected
open Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_EdgeLabelled
open Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_Mass

attribute [local instance] Classical.propDecidable

/-- The vertices which disappear under degree-two suppression. -/
def degreeTwoVertices {k r : ℕ} {G : Erdos745.WrapUp.Graph k}
    (C : ConnectedCoreIn G r) : Set (Fin C.v) :=
  {x | x ∉ branchVertices C.graph}

/-- The graph induced by the vertices which disappear under suppression. -/
def degreeTwoGraph {k r : ℕ} {G : Erdos745.WrapUp.Graph k}
    (C : ConnectedCoreIn G r) : SimpleGraph (degreeTwoVertices C) :=
  C.graph.induce (degreeTwoVertices C)

/-- Inclusion of the induced degree-two graph into the core. -/
def degreeTwoInclusion {k r : ℕ} {G : Erdos745.WrapUp.Graph k}
    (C : ConnectedCoreIn G r) : degreeTwoGraph C →g C.graph where
  toFun x := x.1
  map_rel' h := h

@[simp]
theorem degreeTwoInclusion_apply {k r : ℕ} {G : Erdos745.WrapUp.Graph k}
    (C : ConnectedCoreIn G r) (x : degreeTwoVertices C) :
    degreeTwoInclusion C x = x.1 := rfl

/-- Every vertex of the induced graph has core degree exactly two. -/
theorem core_degree_eq_two_of_mem_degreeTwo {k r : ℕ}
    {G : Erdos745.WrapUp.Graph k} (C : ConnectedCoreIn G r)
    (x : degreeTwoVertices C) : C.graph.degree x.1 = 2 := by
  have hnot : ¬ 3 ≤ C.graph.degree x.1 := by
    simpa only [degreeTwoVertices, Set.mem_setOf_eq, mem_branchVertices] using! x.2
  have hmin := C.min_degree x.1
  omega

/-- A cycle made entirely from degree-two core vertices would be a closed
connected component of the core.  Since the core is connected and has a
branch vertex, no such cycle exists. -/
theorem degreeTwoGraph_isAcyclic {k r : ℕ}
    {G : Erdos745.WrapUp.Graph k} (C : ConnectedCoreIn G r)
    (hbranch : (branchVertices C.graph).Nonempty) :
    (degreeTwoGraph C).IsAcyclic := by
  intro x p hp
  let q : C.graph.Walk x.1 x.1 := p.map (degreeTwoInclusion C)
  have hq : q.IsCycle := hp.map (fun _ _ h => Subtype.ext h)
  have hsupport_nonbranch : ∀ y, y ∈ q.support →
      y ∉ branchVertices C.graph := by
    intro y hy
    change y ∈ (p.map (degreeTwoInclusion C)).support at hy
    rw [p.support_map] at hy
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hy
    exact z.2
  have hclosed : ∀ y, y ∈ q.support → ∀ z, C.graph.Adj y z →
      z ∈ q.support := by
    intro y hy z hyz
    have hydeg : C.graph.degree y = 2 := by
      have hynot := hsupport_nonbranch y hy
      have hmin := C.min_degree y
      rw [mem_branchVertices] at hynot
      omega
    have hsub : q.toSubgraph.neighborSet y ⊆ C.graph.neighborSet y :=
      q.toSubgraph.neighborSet_subset y
    have hsubcard : (C.graph.neighborSet y).ncard ≤
        (q.toSubgraph.neighborSet y).ncard := by
      rw [hq.ncard_neighborSet_toSubgraph_eq_two hy]
      have hcardN : (C.graph.neighborSet y).ncard =
          C.graph.degree y := by
        rw [Set.ncard_eq_toFinset_card' (C.graph.neighborSet y)]
        rw [← C.graph.neighborFinset_def]
        exact C.graph.card_neighborFinset_eq_degree y
      omega
    have hneighbors : q.toSubgraph.neighborSet y =
        C.graph.neighborSet y :=
      Set.eq_of_subset_of_ncard_le hsub hsubcard (Set.toFinite _)
    have hzN : z ∈ q.toSubgraph.neighborSet y := by
      rw [hneighbors]
      exact hyz
    have hzverts : z ∈ q.toSubgraph.verts :=
      q.toSubgraph.neighborSet_subset_verts y hzN
    exact q.mem_verts_toSubgraph.mp hzverts
  have hx : x.1 ∈ q.support := by simp [q]
  have hwalk : ∀ {a b : Fin C.v} (w : C.graph.Walk a b),
      a ∈ q.support → b ∈ q.support := by
    intro a b w ha
    induction w with
    | nil => exact ha
    | cons hab w ih => exact ih (hclosed _ ha _ hab)
  obtain ⟨b, hb⟩ := hbranch
  obtain ⟨w⟩ := C.connected.preconnected x.1 b
  have hbq : b ∈ q.support := hwalk w hx
  exact hsupport_nonbranch b hbq hb

/-- Every connected component of the degree-two induced graph is a finite
tree.  These trees are the internal vertex sets of the maximal suppressed
paths. -/
theorem degreeTwoComponent_isTree {k r : ℕ}
    {G : Erdos745.WrapUp.Graph k} (C : ConnectedCoreIn G r)
    (hbranch : (branchVertices C.graph).Nonempty)
    (S : (degreeTwoGraph C).ConnectedComponent) :
    S.toSimpleGraph.IsTree :=
  (degreeTwoGraph_isAcyclic C hbranch).isTree_connectedComponent S

/-- Internal vertices of a branch-to-branch walk, with both endpoints
removed. -/
def walkInternal {V : Type*} {H : SimpleGraph V} {a b : V}
    (w : H.Walk a b) : List V :=
  w.support.tail.dropLast

/-- Exact maximal-path partition of a connected minimum-degree-two core. -/
structure MaximalPathPartition {k r : ℕ} {G : Erdos745.WrapUp.Graph k}
    (C : ConnectedCoreIn G r) where
  v : Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_Expansion.KernelSize r
  branch : Fin v.1 ↪ Fin C.v
  branch_image : Finset.univ.image branch = branchVertices C.graph
  kernel : OccurrenceKernel v.1 r
  walk : ∀ t : Fin (v.1 + r),
    C.graph.Walk (branch (kernel.edge t).1.1)
      (branch (kernel.edge t).1.2)
  trail : ∀ t, (walk t).IsTrail
  positive : ∀ t, 0 < (walk t).length
  internal_degree_two : ∀ t x, x ∈ walkInternal (walk t) →
    C.graph.degree x = 2
  edge_partition :
    (∑ t : Fin (v.1 + r), ((walk t).edges : Multiset (Sym2 (Fin C.v)))) =
      (C.graph.edgeFinset.1 : Multiset (Sym2 (Fin C.v)))
  internal_partition :
    (∑ t : Fin (v.1 + r), (walkInternal (walk t) : Multiset (Fin C.v))) =
      ((Finset.univ \ branchVertices C.graph).1 : Multiset (Fin C.v))
  loop_internal_two : ∀ t,
    (kernel.edge t).1.1 = (kernel.edge t).1.2 →
      2 ≤ (walkInternal (walk t)).length

namespace MaximalPathPartition

theorem card_branchVertices {k r : ℕ} {G : Erdos745.WrapUp.Graph k}
    {C : ConnectedCoreIn G r} (P : MaximalPathPartition C) :
    (branchVertices C.graph).card = P.v.1 := by
  rw [← P.branch_image, Finset.card_image_of_injective _ P.branch.injective]
  simp

/-- The path partition uses every core edge once. -/
theorem sum_internal_lengths {k r : ℕ} {G : Erdos745.WrapUp.Graph k}
    {C : ConnectedCoreIn G r} (P : MaximalPathPartition C) :
    ∑ t : Fin (P.v.1 + r), (walkInternal (P.walk t)).length = C.v - P.v.1 := by
  have h := congrArg Multiset.card P.internal_partition
  have hsubset : branchVertices C.graph ⊆ (Finset.univ : Finset (Fin C.v)) :=
    Finset.subset_univ _
  rw [Multiset.card_sum] at h
  simpa [Finset.card_sdiff_of_subset hsubset, P.card_branchVertices] using! h

/-- Endpoint occurrences of the partition form a genuine finite kernel. -/
def kernelChoice {k r : ℕ} {G : Erdos745.WrapUp.Graph k}
    {C : ConnectedCoreIn G r} (P : MaximalPathPartition C) :
    Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_Expansion.KernelChoice P.v.1 r :=
  P.kernel.choice

end MaximalPathPartition

end Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_PathPartition


/-!
# Boundary incidences of degree-two components

The graph induced by non-branch core vertices is a forest. Each of its
connected components has maximum degree two. The sum of its degree deficits
from two is exactly two, providing the two incidences that attach that
component to branch vertices in a maximal suppression path.
-/

open scoped BigOperators

noncomputable section

namespace Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_PathBoundary

open Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_CoreConnected
open Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_PathPartition

attribute [local instance] Classical.propDecidable

/-- Restricting a finite simple graph to a vertex set cannot increase degree. -/
private theorem degree_induce_le {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (s : Set V) (x : s) :
    (H.induce s).degree x ≤ H.degree x.1 := by
  classical
  have h : (H.neighborFinset x.1 ∩ s.toFinset).card ≤
      (H.neighborFinset x.1).card :=
    Finset.card_le_card Finset.inter_subset_left
  rw [← H.map_neighborFinset_induce x, Finset.card_map] at h
  simpa only [SimpleGraph.card_neighborFinset_eq_degree] using! h

/-- Each induced non-branch vertex has at most two neighbours. -/
theorem degreeTwoGraph_degree_le_two {k r : ℕ}
    {G : Erdos745.WrapUp.Graph k} (C : ConnectedCoreIn G r)
    (x : degreeTwoVertices C) : (degreeTwoGraph C).degree x ≤ 2 := by
  calc
    (degreeTwoGraph C).degree x ≤ C.graph.degree x.1 :=
      degree_induce_le C.graph (degreeTwoVertices C) x
    _ = 2 := core_degree_eq_two_of_mem_degreeTwo C x

/-- Passing to one connected component preserves the degree bound. -/
theorem component_degree_le_two {k r : ℕ}
    {G : Erdos745.WrapUp.Graph k} (C : ConnectedCoreIn G r)
    (S : (degreeTwoGraph C).ConnectedComponent) (x : S) :
    S.toSimpleGraph.degree x ≤ 2 := by
  calc
    S.toSimpleGraph.degree x ≤ (degreeTwoGraph C).degree x.1 :=
      degree_induce_le (degreeTwoGraph C) S.supp x
    _ ≤ 2 := degreeTwoGraph_degree_le_two C x.1

/-- A degree-two component is a finite tree with one fewer edge than vertex. -/
theorem component_edge_card_add_one {k r : ℕ}
    {G : Erdos745.WrapUp.Graph k} (C : ConnectedCoreIn G r)
    (hbranch : (branchVertices C.graph).Nonempty)
    (S : (degreeTwoGraph C).ConnectedComponent) :
    S.toSimpleGraph.edgeFinset.card + 1 = Fintype.card S :=
  (degreeTwoComponent_isTree C hbranch S).card_edgeFinset

/-- The two missing incidences of a degree-two component, counted with
multiplicity. A singleton contributes two; a longer path contributes one at
each end. -/
theorem component_degree_deficit_sum {k r : ℕ}
    {G : Erdos745.WrapUp.Graph k} (C : ConnectedCoreIn G r)
    (hbranch : (branchVertices C.graph).Nonempty)
    (S : (degreeTwoGraph C).ConnectedComponent) :
    ∑ x : S, (2 - S.toSimpleGraph.degree x) = 2 := by
  have hcard := component_edge_card_add_one C hbranch S
  have hsum := S.toSimpleGraph.sum_degrees_eq_twice_card_edges
  rw [Finset.sum_tsub_distrib Finset.univ
    (fun x _ => component_degree_le_two C S x)]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [hsum]
  rw [← hcard]
  norm_cast
  omega

/- Every component has an endpoint, including the singleton case. -/
end Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_PathBoundary


open scoped BigOperators

noncomputable section

namespace Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_PathEndpoints

open Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_CoreConnected
open Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_PathPartition
open Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_PathBoundary

attribute [local instance] Classical.propDecidable

/-- In a non-singleton component, connectivity rules out isolated vertices. -/
theorem component_degree_pos {k r : ℕ} {G : Erdos745.WrapUp.Graph k}
    (C : ConnectedCoreIn G r)
    (S : (degreeTwoGraph C).ConnectedComponent)
    (hcard : 1 < Fintype.card S) (x : S) :
    0 < S.toSimpleGraph.degree x := by
  letI : Nontrivial S := Fintype.one_lt_card_iff_nontrivial.mp hcard
  exact S.connected_toSimpleGraph.preconnected.degree_pos_of_nontrivial x

/-- Every vertex of a non-singleton degree-two component has degree one or two. -/
theorem component_degree_one_or_two {k r : ℕ} {G : Erdos745.WrapUp.Graph k}
    (C : ConnectedCoreIn G r)
    (S : (degreeTwoGraph C).ConnectedComponent)
    (hcard : 1 < Fintype.card S) (x : S) :
    S.toSimpleGraph.degree x = 1 ∨ S.toSimpleGraph.degree x = 2 := by
  have hpos := component_degree_pos C S hcard x
  have hle := component_degree_le_two C S x
  omega

/-- Exactly two vertices of a non-singleton component are endpoints. -/
theorem component_endpoint_card {k r : ℕ} {G : Erdos745.WrapUp.Graph k}
    (C : ConnectedCoreIn G r)
    (hbranch : (branchVertices C.graph).Nonempty)
    (S : (degreeTwoGraph C).ConnectedComponent)
    (hcard : 1 < Fintype.card S) :
    (Finset.univ.filter (fun x : S => S.toSimpleGraph.degree x = 1)).card = 2 := by
  have hsum := component_degree_deficit_sum C hbranch S
  have hterms :
      (∑ x : S, (2 - S.toSimpleGraph.degree x)) =
        ∑ x : S, if S.toSimpleGraph.degree x = 1 then 1 else 0 := by
    apply Finset.sum_congr rfl
    intro x _
    rcases component_degree_one_or_two C S hcard x with h | h
    · simp [h]
    · simp [h]
  rw [hterms] at hsum
  simpa using! (Finset.sum_boole
    (fun x : S => S.toSimpleGraph.degree x = 1) Finset.univ).symm.trans hsum

/-- The two endpoints are distinct and all other vertices are internal. -/
theorem component_endpoint_pair {k r : ℕ} {G : Erdos745.WrapUp.Graph k}
    (C : ConnectedCoreIn G r)
    (hbranch : (branchVertices C.graph).Nonempty)
    (S : (degreeTwoGraph C).ConnectedComponent)
    (hcard : 1 < Fintype.card S) :
    ∃ a b : S, a ≠ b ∧
      S.toSimpleGraph.degree a = 1 ∧ S.toSimpleGraph.degree b = 1 ∧
      (∀ x : S, x ≠ a → x ≠ b → S.toSimpleGraph.degree x = 2) := by
  obtain ⟨a, b, hab, hpair⟩ := Finset.card_eq_two.mp
    (component_endpoint_card C hbranch S hcard)
  refine ⟨a, b, hab, ?_, ?_, ?_⟩
  · have ha : a ∈ (Finset.univ.filter (fun x : S => S.toSimpleGraph.degree x = 1)) := by
      rw [hpair]
      simp
    simpa using! ha
  · have hb : b ∈ (Finset.univ.filter (fun x : S => S.toSimpleGraph.degree x = 1)) := by
      rw [hpair]
      simp
    simpa using! hb
  · intro x hxa hxb
    rcases component_degree_one_or_two C S hcard x with h | h
    · have hx : x ∈ (Finset.univ.filter
          (fun y : S => S.toSimpleGraph.degree y = 1)) := by simp [h]
      rw [hpair] at hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with h | h
      · exact (hxa h).elim
      · exact (hxb h).elim
    · exact h

/-- An induced component with one vertex has no internal edge. -/
theorem singleton_component_degree_zero {k r : ℕ}
    {G : Erdos745.WrapUp.Graph k} (C : ConnectedCoreIn G r)
    (S : (degreeTwoGraph C).ConnectedComponent)
    (hcard : Fintype.card S = 1) (x : S) :
    S.toSimpleGraph.degree x = 0 := by
  rcases Fintype.card_eq_one_iff.mp hcard with ⟨only, hsingle⟩
  by_contra h
  have hpos : 0 < S.toSimpleGraph.degree x := by omega
  obtain ⟨y, hy⟩ := (S.toSimpleGraph.degree_pos_iff_exists_adj x).mp hpos
  have hyx : y = x := (hsingle y).trans (hsingle x).symm
  exact (S.toSimpleGraph.ne_of_adj hy) hyx.symm

/-- Both core neighbours of a singleton component vertex are branch vertices. -/
theorem singleton_neighbor_branch {k r : ℕ}
    {G : Erdos745.WrapUp.Graph k} (C : ConnectedCoreIn G r)
    (S : (degreeTwoGraph C).ConnectedComponent)
    (hcard : Fintype.card S = 1) (x : S)
    {y : Fin C.v} (hxy : C.graph.Adj x.1.1 y) :
    y ∈ branchVertices C.graph := by
  by_contra hy
  let yD : degreeTwoVertices C := ⟨y, hy⟩
  have hD : (degreeTwoGraph C).Adj x.1 yD := hxy
  have hyS : yD ∈ S.supp := S.mem_supp_of_adj_mem_supp x.2 hD
  have hS : S.toSimpleGraph.Adj x ⟨yD, hyS⟩ := hD
  have hzero := singleton_component_degree_zero C S hcard x
  have hpos := (S.toSimpleGraph.degree_pos_iff_exists_adj x).mpr
    ⟨⟨yD, hyS⟩, hS⟩
  omega

/-- A singleton component attaches by two distinct edges to branch vertices. -/
theorem singleton_two_branch_neighbors {k r : ℕ}
    {G : Erdos745.WrapUp.Graph k} (C : ConnectedCoreIn G r)
    (S : (degreeTwoGraph C).ConnectedComponent)
    (hcard : Fintype.card S = 1) (x : S) :
    ∃ a b : Fin C.v, a ≠ b ∧
      C.graph.Adj x.1.1 a ∧ C.graph.Adj x.1.1 b ∧
      a ∈ branchVertices C.graph ∧ b ∈ branchVertices C.graph := by
  have hdeg := core_degree_eq_two_of_mem_degreeTwo C x.1
  have hneighbors : (C.graph.neighborFinset x.1.1).card = 2 := by
    simpa using! hdeg
  obtain ⟨a, b, hab, hpair⟩ := Finset.card_eq_two.mp hneighbors
  have ha : a ∈ C.graph.neighborFinset x.1.1 := by rw [hpair]; simp
  have hb : b ∈ C.graph.neighborFinset x.1.1 := by rw [hpair]; simp
  have hxa : C.graph.Adj x.1.1 a := by simpa using! ha
  have hxb : C.graph.Adj x.1.1 b := by simpa using! hb
  exact ⟨a, b, hab, hxa, hxb,
    singleton_neighbor_branch C S hcard x hxa,
    singleton_neighbor_branch C S hcard x hxb⟩

end Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_PathEndpoints


open scoped BigOperators Sym2

noncomputable section

namespace Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_ComponentPath

open Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_CoreConnected
open Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_PathPartition
open Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_PathBoundary
open Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_PathEndpoints
open Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_PathFollow

attribute [local instance] Classical.propDecidable

private theorem neighbor_ncard_eq_degree {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (x : V) : (H.neighborSet x).ncard = H.degree x := by
  rw [Set.ncard_eq_toFinset_card' (H.neighborSet x)]
  rw [← H.neighborFinset_def]
  exact H.card_neighborFinset_eq_degree x

/-- In a tree of maximum degree two, the path between the two leaves visits
every vertex and uses every edge. -/
theorem tree_path_between_leaves {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (htree : H.IsTree) (a b : V) (hab : a ≠ b)
    (ha : H.degree a = 1) (hb : H.degree b = 1)
    (hinterior : ∀ x, x ≠ a → x ≠ b → H.degree x = 2) :
    ∃ p : H.Walk a b, p.IsHamiltonian ∧
      ∀ x y : V, H.Adj x y ↔ s(x, y) ∈ p.edges := by
  obtain ⟨p, hp, _⟩ := htree.existsUnique_path a b
  have hnonempty : ¬ p.Nil := p.not_nil_of_ne hab
  have hsaturated : ∀ x, x ∈ p.support →
      p.toSubgraph.neighborSet x = H.neighborSet x := by
    intro x hx
    have hsubset : p.toSubgraph.neighborSet x ⊆ H.neighborSet x :=
      p.toSubgraph.neighborSet_subset x
    have hcard : (H.neighborSet x).ncard ≤
        (p.toSubgraph.neighborSet x).ncard := by
      obtain ⟨i, rfl, hi⟩ := p.mem_support_iff_exists_getVert.mp hx
      by_cases hstart : i = 0
      · subst i
        simp only [p.getVert_zero]
        rw [neighbor_ncard_eq_degree H a, ha,
          hp.neighborSet_toSubgraph_startpoint hnonempty]
        simp
      · by_cases hend : i = p.length
        · subst i
          simp only [p.getVert_length]
          rw [neighbor_ncard_eq_degree H b, hb,
            hp.neighborSet_toSubgraph_endpoint hnonempty]
          simp
        · have hia : p.getVert i ≠ a := by
            intro h
            exact hstart ((hp.getVert_eq_start_iff hi).mp h)
          have hib : p.getVert i ≠ b := by
            intro h
            exact hend ((hp.getVert_eq_end_iff hi).mp h)
          rw [neighbor_ncard_eq_degree H (p.getVert i),
            hinterior _ hia hib,
            hp.ncard_neighborSet_toSubgraph_internal_eq_two hstart (by omega)]
    exact Set.eq_of_subset_of_ncard_le hsubset hcard (Set.toFinite _)
  have hclosed : ∀ x, x ∈ p.support → ∀ y, H.Adj x y → y ∈ p.support := by
    intro x hx y hxy
    have hy : y ∈ p.toSubgraph.neighborSet x := by
      rw [hsaturated x hx]
      exact hxy
    exact p.mem_verts_toSubgraph.mp (p.toSubgraph.neighborSet_subset_verts x hy)
  have hwalk : ∀ {x y : V} (w : H.Walk x y),
      x ∈ p.support → y ∈ p.support := by
    intro x y w hx
    induction w with
    | nil => exact hx
    | cons h w ih => exact ih (hclosed _ hx _ h)
  have hall : ∀ x : V, x ∈ p.support := by
    intro x
    obtain ⟨w⟩ := htree.isConnected.preconnected a x
    exact hwalk w p.start_mem_support
  refine ⟨p, hp.isHamiltonian_of_mem hall, ?_⟩
  intro x y
  constructor
  · intro hxy
    apply p.adj_toSubgraph_iff_mem_edges.mp
    change y ∈ p.toSubgraph.neighborSet x
    rw [hsaturated x (hall x)]
    exact hxy
  · intro hxy
    exact p.toSubgraph.adj_sub (p.adj_toSubgraph_iff_mem_edges.mpr hxy)

/-- Every endpoint of a nontrivial degree-two component has exactly one
neighbour among the branch vertices of the original core. -/
theorem endpoint_unique_branch_neighbor {k r : ℕ}
    {G : Erdos745.WrapUp.Graph k} (C : ConnectedCoreIn G r)
    (S : (degreeTwoGraph C).ConnectedComponent) (a : S)
    (ha : S.toSimpleGraph.degree a = 1) :
    ∃! b : Fin C.v, C.graph.Adj a.1.1 b ∧ b ∈ branchVertices C.graph := by
  have hpositive : 0 < S.toSimpleGraph.degree a := by omega
  obtain ⟨y, hay⟩ := (S.toSimpleGraph.degree_pos_iff_exists_adj a).mp hpositive
  have hcore : C.graph.Adj y.1.1 a.1.1 := hay.symm
  have hdegree : C.graph.degree a.1.1 = 2 :=
    core_degree_eq_two_of_mem_degreeTwo C a.1
  let b := otherNeighbor C.graph hcore hdegree
  have hab : C.graph.Adj a.1.1 b := otherNeighbor_adjacent C.graph hcore hdegree
  have hby : b ≠ y.1.1 := otherNeighbor_ne_prev C.graph hcore hdegree
  have hbbranch : b ∈ branchVertices C.graph := by
    by_contra hnot
    let bD : degreeTwoVertices C := ⟨b, hnot⟩
    have hD : (degreeTwoGraph C).Adj a.1 bD := hab
    have hbS : bD ∈ S.supp := S.mem_supp_of_adj_mem_supp a.2 hD
    have hSa : S.toSimpleGraph.Adj a ⟨bD, hbS⟩ := hD
    have hcard : (S.toSimpleGraph.neighborFinset a).card = 1 := by
      simpa using! ha
    obtain ⟨only, hone⟩ := Finset.card_eq_one.mp hcard
    have hy : y = only := by
      have hy' : y ∈ S.toSimpleGraph.neighborFinset a := by simpa using! hay
      rw [hone] at hy'
      simpa using! hy'
    have hb : (⟨bD, hbS⟩ : S) = only := by
      have hb' : (⟨bD, hbS⟩ : S) ∈ S.toSimpleGraph.neighborFinset a := by
        simpa using! hSa
      rw [hone] at hb'
      simpa using! hb'
    exact hby (congrArg (fun x : S => x.1.1) (hb.trans hy.symm))
  refine ⟨b, ⟨hab, hbbranch⟩, ?_⟩
  intro z hz
  have hzy : z ≠ y.1.1 := by
    intro h
    exact y.1.2 (h ▸ hz.2)
  exact eq_otherNeighbor C.graph hcore hdegree hz.1 hzy

/-- A degree-two component, with its precise internal path and both external
attachments. The external branch endpoints are allowed to coincide. -/
structure ComponentPath {k r : ℕ} {G : Erdos745.WrapUp.Graph k}
    (C : ConnectedCoreIn G r)
    (S : (degreeTwoGraph C).ConnectedComponent) where
  first : S
  last : S
  walk : S.toSimpleGraph.Walk first last
  hamiltonian : walk.IsHamiltonian
  edge_exact : ∀ x y : S,
    S.toSimpleGraph.Adj x y ↔ s(x, y) ∈ walk.edges
  first_branch : Fin C.v
  last_branch : Fin C.v
  first_adj : C.graph.Adj first.1.1 first_branch
  last_adj : C.graph.Adj last.1.1 last_branch
  first_is_branch : first_branch ∈ branchVertices C.graph
  last_is_branch : last_branch ∈ branchVertices C.graph
  singleton_distinct : Fintype.card S = 1 → first_branch ≠ last_branch

/-- Each component admits an exact oriented path, including a singleton
component, which has two different external branch neighbours. -/
noncomputable def exists_componentPath {k r : ℕ} {G : Erdos745.WrapUp.Graph k}
    (C : ConnectedCoreIn G r) (hbranch : (branchVertices C.graph).Nonempty)
    (S : (degreeTwoGraph C).ConnectedComponent) : ComponentPath C S := by
  by_cases hlarge : 1 < Fintype.card S
  · let endpoints := component_endpoint_pair C hbranch S hlarge
    let a := Classical.choose endpoints
    let b := Classical.choose (Classical.choose_spec endpoints)
    have ⟨hab, ha, hb, hinterior⟩ :=
      Classical.choose_spec (Classical.choose_spec endpoints)
    let path := tree_path_between_leaves
      S.toSimpleGraph (degreeTwoComponent_isTree C hbranch S)
      a b hab ha hb hinterior
    let p := Classical.choose path
    have ⟨hp, hedges⟩ := Classical.choose_spec path
    let aBranch := Classical.choose (endpoint_unique_branch_neighbor C S a ha)
    have ⟨⟨haadj, haBranch⟩, _⟩ :=
      Classical.choose_spec (endpoint_unique_branch_neighbor C S a ha)
    let bBranch := Classical.choose (endpoint_unique_branch_neighbor C S b hb)
    have ⟨⟨hbadj, hbBranch⟩, _⟩ :=
      Classical.choose_spec (endpoint_unique_branch_neighbor C S b hb)
    exact ⟨a, b, p, hp, hedges, aBranch, bBranch,
      haadj, hbadj, haBranch, hbBranch, by intro h; omega⟩
  · let representative := Classical.choose S.nonempty_supp
    have hrepresentative := Classical.choose_spec S.nonempty_supp
    let start : S := ⟨representative, hrepresentative⟩
    have hpositive : 0 < Fintype.card S := Fintype.card_pos_iff.mpr ⟨start⟩
    have hsingle : Fintype.card S = 1 := by omega
    let one := Fintype.card_eq_one_iff.mp hsingle
    let only := Classical.choose one
    have honly := Classical.choose_spec one
    let branches := singleton_two_branch_neighbors C S hsingle only
    let a := Classical.choose branches
    let b := Classical.choose (Classical.choose_spec branches)
    have ⟨hab, ha, hb, haBranch, hbBranch⟩ :=
      Classical.choose_spec (Classical.choose_spec branches)
    refine ⟨only, only, .nil, ?_, ?_, a, b,
      ha, hb, haBranch, hbBranch, ?_⟩
    · intro x
      rw [honly x]
      simp [only]
    · intro x y
      rw [honly x, honly y]
      simp
    · intro _
      exact hab

end Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_ComponentPath


/-!
# Exact unlabelled suppression paths

Attach the two branch incidences to every degree-two component and include
each direct branch edge once. The resulting trails partition core edges and
internal vertices as multisets. Their number is the branch count plus excess.
-/

open scoped BigOperators Sym2
noncomputable section

namespace Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_PathAssembly

open Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_CoreConnected
open Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_PathPartition
open Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_ComponentPath

attribute [local instance] Classical.propDecidable

private theorem neighbor_ncard_eq_degree {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (x : V) : (H.neighborSet x).ncard = H.degree x := by
  rw [Set.ncard_eq_toFinset_card' (H.neighborSet x), ← H.neighborFinset_def]
  exact H.card_neighborFinset_eq_degree x

/-- A trail with simple interior is locally saturated at a degree-two
interior vertex, whether or not its two endpoints coincide. -/
private theorem saturated_internal {V : Type*} [Fintype V] [DecidableEq V]
    {H : SimpleGraph V} {a b x : V} (w : H.Walk a b)
    (ht : w.IsTrail) (hn : ¬ w.Nil) (htail : w.support.tail.Nodup)
    (hp : a ≠ b → w.IsPath) (hx : x ∈ w.support)
    (hxa : x ≠ a) (hxb : x ≠ b) (hdeg : H.degree x = 2) :
    w.toSubgraph.neighborSet x = H.neighborSet x := by
  have hcard : (w.toSubgraph.neighborSet x).ncard = 2 := by
    by_cases hab : a = b
    · subst b
      have hc : w.IsCycle := ⟨⟨ht, fun h => hn (h ▸ SimpleGraph.Walk.Nil.nil)⟩, htail⟩
      exact hc.ncard_neighborSet_toSubgraph_eq_two hx
    · have hpath := hp hab
      obtain ⟨i, hi, hib⟩ := w.mem_support_iff_exists_getVert.mp hx
      have hi0 : i ≠ 0 := by
        intro h
        subst i
        exact hxa (by simpa using! hi.symm)
      have hil : i < w.length := by
        have hne : i ≠ w.length := by
          intro h
          subst i
          exact hxb (by simpa using! hi.symm)
        omega
      rw [← hi]
      exact hpath.ncard_neighborSet_toSubgraph_internal_eq_two hi0 hil
  apply Set.eq_of_subset_of_ncard_le (w.toSubgraph.neighborSet_subset x)
  rw [neighbor_ncard_eq_degree H x, hdeg, hcard]

variable {k r : ℕ} {G : Erdos745.WrapUp.Graph k}
variable {C : ConnectedCoreIn G r}

end Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_PathAssembly

namespace Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_ComponentPath.ComponentPath

open Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_CoreConnected
open Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_PathPartition
open Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_PathAssembly

attribute [local instance] Classical.propDecidable

variable {k r : ℕ} {G : Erdos745.WrapUp.Graph k}
variable {C : ConnectedCoreIn G r}
variable {S : (degreeTwoGraph C).ConnectedComponent} (P : ComponentPath C S)

/-- Inclusion of one induced component into its original core. -/
def inclusion (_P : ComponentPath C S) : S.toSimpleGraph →g C.graph where
  toFun x := x.1.1
  map_rel' h := h

theorem inclusion_injective : Function.Injective P.inclusion := by
  intro x y h
  exact Subtype.ext (Subtype.ext h)

/-- The internal path regarded as a path in the core. -/
def corePath : C.graph.Walk P.first.1.1 P.last.1.1 :=
  P.walk.map P.inclusion

theorem corePath_isPath : P.corePath.IsPath :=
  SimpleGraph.Walk.map_isPath_of_injective P.inclusion_injective P.hamiltonian.isPath

theorem mem_corePath_support (x : Fin C.v) :
    x ∈ P.corePath.support ↔ ∃ z : S, z.1.1 = x := by
  have hs : P.corePath.support = P.walk.support.map (fun z : S => z.1.1) :=
    SimpleGraph.Walk.support_map P.inclusion P.walk
  rw [hs]
  simp only [List.mem_map]
  constructor
  · rintro ⟨z, _, hz⟩
    exact ⟨z, hz⟩
  · rintro ⟨z, hz⟩
    exact ⟨z, P.hamiltonian.mem_support z, hz⟩

theorem corePath_nonbranch {x : Fin C.v} (hx : x ∈ P.corePath.support) :
    x ∉ branchVertices C.graph := by
  obtain ⟨z, rfl⟩ := (P.mem_corePath_support x).mp hx
  exact z.1.2

theorem card_eq_one_of_first_eq_last (h : P.first = P.last) :
    Fintype.card S = 1 := by
  have hl : P.walk.length = 0 :=
    (P.hamiltonian.isPath.getVert_eq_start_iff (Nat.le_refl _)).mp (by simpa using! h.symm)
  have hc := P.hamiltonian.length_support
  rw [P.walk.length_support, hl] at hc
  omega

/-- The genuine branch-to-branch walk attached to this component. -/
def attached : C.graph.Walk P.first_branch P.last_branch :=
  .cons P.first_adj.symm (P.corePath.concat P.last_adj)

theorem attached_support :
    P.attached.support = P.first_branch :: (P.corePath.support ++ [P.last_branch]) := by
  simp [attached, List.concat_eq_append]

theorem attached_internal :
    walkInternal P.attached = P.corePath.support := by
  simp [walkInternal, P.attached_support]

theorem attached_internal_nodup : (walkInternal P.attached).Nodup := by
  rw [P.attached_internal]
  exact P.corePath_isPath.support_nodup

theorem attached_positive : 0 < P.attached.length := by
  simp [attached]

theorem boundary_edges_ne :
    s(P.first_branch, P.first.1.1) ≠ s(P.last.1.1, P.last_branch) := by
  intro he
  rcases Sym2.eq_iff.mp he with ⟨h, _⟩ | ⟨hab, hfl⟩
  · exact P.last.1.2 (h ▸ P.first_is_branch)
  · have hfl' : P.first = P.last := Subtype.ext (Subtype.ext hfl)
    exact P.singleton_distinct (P.card_eq_one_of_first_eq_last hfl') hab

theorem attached_trail : P.attached.IsTrail := by
  have hb : P.last_branch ∉ P.corePath.support :=
    fun h => P.corePath_nonbranch h P.last_is_branch
  have htail := P.corePath_isPath.concat hb P.last_adj
  apply htail.isTrail.cons P.first_adj.symm
  simp only [SimpleGraph.Walk.edges_concat, List.concat_eq_append, List.mem_append, List.mem_singleton, not_or]
  constructor
  · intro he
    exact P.corePath_nonbranch
      (P.corePath.fst_mem_support_of_mem_edges he) P.first_is_branch
  · exact P.boundary_edges_ne

theorem attached_isPath (h : P.first_branch ≠ P.last_branch) :
    P.attached.IsPath := by
  apply SimpleGraph.Walk.IsPath.cons
    (P.corePath_isPath.concat
      (fun hm => P.corePath_nonbranch hm P.last_is_branch) P.last_adj)
  simp only [SimpleGraph.Walk.support_concat, List.concat_eq_append, List.mem_append, List.mem_singleton, not_or]
  exact ⟨fun hm => P.corePath_nonbranch hm P.first_is_branch, h⟩

theorem attached_tail_nodup : P.attached.support.tail.Nodup := by
  rw [P.attached_support]
  simpa only [List.tail_cons, ← List.concat_eq_append] using!
    (List.nodup_concat P.corePath.support P.last_branch).mpr
      ⟨fun hm => P.corePath_nonbranch hm P.last_is_branch,
        P.corePath_isPath.support_nodup⟩

theorem attached_internal_length :
    (walkInternal P.attached).length = Fintype.card S := by
  rw [P.attached_internal]
  have hs : P.corePath.support = P.walk.support.map (fun z : S => z.1.1) :=
    SimpleGraph.Walk.support_map P.inclusion P.walk
  rw [hs, List.length_map]
  exact P.hamiltonian.length_support

theorem attached_length :
    P.attached.length = Fintype.card S + 1 := by
  have h := P.hamiltonian.length_support
  rw [P.walk.length_support] at h
  simp only [attached, SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_concat,
    corePath]
  have hm : P.corePath.length = P.walk.length :=
    SimpleGraph.Walk.length_map P.inclusion P.walk
  change P.corePath.length + 1 + 1 = Fintype.card S + 1
  omega

theorem attached_loop_internal_two (h : P.first_branch = P.last_branch) :
    2 ≤ (walkInternal P.attached).length := by
  rw [P.attached_internal_length]
  have hpos : 0 < Fintype.card S := Fintype.card_pos_iff.mpr ⟨P.first⟩
  have hne : Fintype.card S ≠ 1 := fun hc => P.singleton_distinct hc h
  omega

theorem mem_attached_support_of_nonbranch {x : Fin C.v}
    (hx : x ∉ branchVertices C.graph) (hm : x ∈ P.attached.support) :
    ∃ z : S, z.1.1 = x := by
  rw [P.attached_support] at hm
  simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hm
  rcases hm with h | h | h
  · exact (hx (h ▸ P.first_is_branch)).elim
  · exact (P.mem_corePath_support x).mp h
  · exact (hx (h ▸ P.last_is_branch)).elim

/-- Every core edge at an internal vertex is used by its attached path. -/
theorem attached_contains_adj (x : S) {y : Fin C.v}
    (hxy : C.graph.Adj x.1.1 y) : s(x.1.1, y) ∈ P.attached.edges := by
  have hx : x.1.1 ∈ P.attached.support := by
    rw [P.attached_support]
    exact List.mem_cons_of_mem _ (List.mem_append_left _ ((P.mem_corePath_support _).mpr ⟨x, rfl⟩))
  have hxa : x.1.1 ≠ P.first_branch := by
    intro h
    exact x.1.2 (h ▸ P.first_is_branch)
  have hxb : x.1.1 ≠ P.last_branch := by
    intro h
    exact x.1.2 (h ▸ P.last_is_branch)
  have heq := saturated_internal P.attached P.attached_trail
    (SimpleGraph.Walk.not_nil_iff_lt_length.mpr P.attached_positive)
    P.attached_tail_nodup P.attached_isPath hx hxa hxb
    (core_degree_eq_two_of_mem_degreeTwo C x.1)
  apply P.attached.adj_toSubgraph_iff_mem_edges.mp
  change y ∈ P.attached.toSubgraph.neighborSet x.1.1
  rw [heq]
  exact hxy

/-- Every used edge has an endpoint in the originating component. -/
theorem attached_edge_has_internal {x y : Fin C.v}
    (he : s(x, y) ∈ P.attached.edges) :
    (∃ z : S, z.1.1 = x) ∨ (∃ z : S, z.1.1 = y) := by
  simp only [attached, SimpleGraph.Walk.edges_cons,
    SimpleGraph.Walk.edges_concat, List.mem_cons, List.concat_eq_append, List.mem_append, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · rcases Sym2.eq_iff.mp he with ⟨_, h⟩ | ⟨h, _⟩
    · exact Or.inr ⟨P.first, h.symm⟩
    · exact Or.inl ⟨P.first, h.symm⟩
  · exact Or.inl ((P.mem_corePath_support x).mp
      (P.corePath.fst_mem_support_of_mem_edges he))
  · rcases Sym2.eq_iff.mp he with ⟨h, _⟩ | ⟨_, h⟩
    · exact Or.inl ⟨P.last, h.symm⟩
    · exact Or.inr ⟨P.last, h.symm⟩

end Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_ComponentPath.ComponentPath

namespace Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_PathAssembly

open Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_CoreConnected
open Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_PathPartition
open Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_ComponentPath

attribute [local instance] Classical.propDecidable

variable {k r : ℕ} {G : Erdos745.WrapUp.Graph k}
variable {C : ConnectedCoreIn G r}

/-- One occurrence for each degree-two component, and one for each direct
branch edge, ordered by the original finite vertex labels. -/
def DirectEdge (C : ConnectedCoreIn G r) :=
  {p : Fin C.v × Fin C.v // p.1 < p.2 ∧ C.graph.Adj p.1 p.2 ∧
    p.1 ∈ branchVertices C.graph ∧ p.2 ∈ branchVertices C.graph}

def PathSlot (C : ConnectedCoreIn G r) :=
  (degreeTwoGraph C).ConnectedComponent ⊕ DirectEdge C

instance : Fintype (DirectEdge C) := by unfold DirectEdge; exact Fintype.ofFinite _
instance : Fintype (PathSlot C) := by unfold PathSlot; exact Fintype.ofFinite _

/-- An actual oriented path occurrence; endpoints may agree. -/
structure BranchWalk (C : ConnectedCoreIn G r) where
  first : Fin C.v
  last : Fin C.v
  first_branch : first ∈ branchVertices C.graph
  last_branch : last ∈ branchVertices C.graph
  walk : C.graph.Walk first last

def slotWalk (C : ConnectedCoreIn G r)
    (hbranch : (branchVertices C.graph).Nonempty) : PathSlot C → BranchWalk C
  | Sum.inl S =>
    let P := exists_componentPath C hbranch S
    ⟨P.first_branch, P.last_branch, P.first_is_branch, P.last_is_branch, P.attached⟩
  | Sum.inr e => ⟨e.1.1, e.1.2, e.2.2.2.1, e.2.2.2.2, e.2.2.1.toWalk⟩

variable (C) (hbranch : (branchVertices C.graph).Nonempty)

theorem slotWalk_trail (t : PathSlot C) : (slotWalk C hbranch t).walk.IsTrail := by
  cases t with
  | inl S => exact (exists_componentPath C hbranch S).attached_trail
  | inr e => exact (SimpleGraph.Walk.IsPath.of_adj e.2.2.1).isTrail

theorem slotWalk_positive (t : PathSlot C) : 0 < (slotWalk C hbranch t).walk.length := by
  cases t with
  | inl S => exact (exists_componentPath C hbranch S).attached_positive
  | inr e => simp [slotWalk]

theorem slotWalk_internal_nodup (t : PathSlot C) :
    (walkInternal (slotWalk C hbranch t).walk).Nodup := by
  cases t with
  | inl S => exact (exists_componentPath C hbranch S).attached_internal_nodup
  | inr e => simp [slotWalk, walkInternal, SimpleGraph.Adj.toWalk]

theorem slotWalk_internal_nonbranch (t : PathSlot C) {x : Fin C.v}
    (hx : x ∈ walkInternal (slotWalk C hbranch t).walk) :
    x ∉ branchVertices C.graph := by
  cases t with
  | inl S =>
    let P := exists_componentPath C hbranch S
    exact P.corePath_nonbranch (P.attached_internal ▸ hx)
  | inr e => simp [slotWalk, walkInternal, SimpleGraph.Adj.toWalk] at hx

theorem slotWalk_internal_degree_two (t : PathSlot C) {x : Fin C.v}
    (hx : x ∈ walkInternal (slotWalk C hbranch t).walk) :
    C.graph.degree x = 2 :=
  core_degree_eq_two_of_mem_degreeTwo C
    ⟨x, slotWalk_internal_nonbranch C hbranch t hx⟩

theorem slotWalk_loop_internal_two (t : PathSlot C)
    (h : (slotWalk C hbranch t).first = (slotWalk C hbranch t).last) :
    2 ≤ (walkInternal (slotWalk C hbranch t).walk).length := by
  cases t with
  | inl S => exact (exists_componentPath C hbranch S).attached_loop_internal_two h
  | inr e => exact ((ne_of_lt e.2.1) h).elim

theorem slotWalk_length (t : PathSlot C) :
    (slotWalk C hbranch t).walk.length =
      (walkInternal (slotWalk C hbranch t).walk).length + 1 := by
  cases t with
  | inl S =>
    let P := exists_componentPath C hbranch S
    exact P.attached_length.trans (congrArg (· + 1) P.attached_internal_length.symm)
  | inr e => simp [slotWalk, walkInternal, SimpleGraph.Adj.toWalk]

private theorem component_eq_of_vertex
    {S T : (degreeTwoGraph C).ConnectedComponent}
    (x : S) (y : T) (h : x.1.1 = y.1.1) : S = T := by
  have hxy : x.1 = y.1 := Subtype.ext h
  exact SimpleGraph.ConnectedComponent.eq_of_common_vertex x.2 (hxy ▸ y.2)

/-- Internal vertices have exactly one occurrence, their induced component. -/
theorem existsUnique_internal {x : Fin C.v} (hx : x ∉ branchVertices C.graph) :
    ∃! t : PathSlot C, x ∈ walkInternal (slotWalk C hbranch t).walk := by
  let xD : degreeTwoVertices C := ⟨x, hx⟩
  let S := (degreeTwoGraph C).connectedComponentMk xD
  let xS : S := ⟨xD, rfl⟩
  refine ⟨Sum.inl S, ?_, ?_⟩
  · let P := exists_componentPath C hbranch S
    change x ∈ walkInternal P.attached
    rw [P.attached_internal]
    exact (P.mem_corePath_support x).mpr ⟨xS, rfl⟩
  · intro t ht
    cases t with
    | inl T =>
      let P := exists_componentPath C hbranch T
      change x ∈ walkInternal P.attached at ht
      rw [P.attached_internal] at ht
      obtain ⟨y, hy⟩ := (P.mem_corePath_support x).mp ht
      exact congrArg Sum.inl (component_eq_of_vertex C y xS hy)
    | inr e => simp [slotWalk, walkInternal, SimpleGraph.Adj.toWalk] at ht

private theorem component_slot_of_edge {x y : Fin C.v}
    (hx : x ∉ branchVertices C.graph) {t : PathSlot C}
    (he : s(x, y) ∈ (slotWalk C hbranch t).walk.edges) :
    t = Sum.inl ((degreeTwoGraph C).connectedComponentMk ⟨x, hx⟩) := by
  cases t with
  | inl S =>
    let P := exists_componentPath C hbranch S
    obtain ⟨z, hz⟩ := P.mem_attached_support_of_nonbranch hx
      (P.attached.fst_mem_support_of_mem_edges he)
    apply congrArg Sum.inl
    exact component_eq_of_vertex C z ⟨⟨x, hx⟩, rfl⟩ hz
  | inr e =>
    have heq : s(x, y) = s(e.1.1, e.1.2) := by simpa [slotWalk, SimpleGraph.Adj.toWalk] using! he
    rcases Sym2.eq_iff.mp heq with ⟨h, _⟩ | ⟨h, _⟩
    · exact (hx (h ▸ e.2.2.2.1)).elim
    · exact (hx (h ▸ e.2.2.2.2)).elim

private theorem existsUnique_edge_nonbranch {x y : Fin C.v}
    (hxy : C.graph.Adj x y) (hx : x ∉ branchVertices C.graph) :
    ∃! t : PathSlot C, s(x, y) ∈ (slotWalk C hbranch t).walk.edges := by
  let S := (degreeTwoGraph C).connectedComponentMk ⟨x, hx⟩
  refine ⟨Sum.inl S, ?_, fun t ht => component_slot_of_edge C hbranch hx ht⟩
  exact (exists_componentPath C hbranch S).attached_contains_adj ⟨⟨x, hx⟩, rfl⟩ hxy

private theorem existsUnique_edge_branch_lt {x y : Fin C.v}
    (hxy : C.graph.Adj x y) (hx : x ∈ branchVertices C.graph)
    (hy : y ∈ branchVertices C.graph) (hlt : x < y) :
    ∃! t : PathSlot C, s(x, y) ∈ (slotWalk C hbranch t).walk.edges := by
  let e : DirectEdge C := ⟨(x, y), hlt, hxy, hx, hy⟩
  refine ⟨Sum.inr e, ?_, ?_⟩
  · simp [slotWalk, e, SimpleGraph.Adj.toWalk]
  · intro t ht
    cases t with
    | inl S =>
      rcases (exists_componentPath C hbranch S).attached_edge_has_internal ht with
        ⟨z, hz⟩ | ⟨z, hz⟩
      · exact (z.1.2 (hz ▸ hx)).elim
      · exact (z.1.2 (hz ▸ hy)).elim
    | inr f =>
      have heq : s(x, y) = s(f.1.1, f.1.2) := by
        simpa [slotWalk, SimpleGraph.Adj.toWalk] using! ht
      apply congrArg Sum.inr
      apply Subtype.ext
      rcases Sym2.eq_iff.mp heq with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · exact Prod.ext h₁.symm h₂.symm
      · have hf := f.2.1
        omega

/-- Every core edge belongs to exactly one attached or direct path. -/
theorem existsUnique_edge {x y : Fin C.v} (hxy : C.graph.Adj x y) :
    ∃! t : PathSlot C, s(x, y) ∈ (slotWalk C hbranch t).walk.edges := by
  by_cases hx : x ∈ branchVertices C.graph
  · by_cases hy : y ∈ branchVertices C.graph
    · rcases lt_or_gt_of_ne hxy.ne with hlt | hlt
      · exact existsUnique_edge_branch_lt C hbranch hxy hx hy hlt
      · simpa only [Sym2.eq_swap] using!
          existsUnique_edge_branch_lt C hbranch hxy.symm hy hx hlt
    · simpa only [Sym2.eq_swap] using!
        existsUnique_edge_nonbranch C hbranch hxy.symm hy
  · exact existsUnique_edge_nonbranch C hbranch hxy hx

/-- Convert uniqueness and list simplicity to a literal multiset partition. -/
private theorem sum_lists_eq_finset {ι α : Type*} [Fintype ι] [DecidableEq α]
    (L : ι → List α) (F : Finset α) (hn : ∀ i, (L i).Nodup)
    (hmem : ∀ i a, a ∈ L i → a ∈ F)
    (huniq : ∀ a ∈ F, ∃! i, a ∈ L i) :
    (∑ i, (L i : Multiset α)) = F.1 := by
  apply Multiset.ext.mpr
  intro a
  rw [Multiset.count_sum']
  simp only [Multiset.coe_count]
  by_cases ha : a ∈ F
  · obtain ⟨i, hi, hu⟩ := huniq a ha
    rw [Finset.sum_eq_single i]
    · rw [List.count_eq_one_of_mem (hn i) hi]
      exact (Multiset.count_eq_one_of_mem F.nodup ha).symm
    · intro j _ hji
      exact List.count_eq_zero.mpr (fun hj => hji (hu j hj))
    · simp
  · have hz : ∀ i, List.count a (L i) = 0 :=
      fun i => List.count_eq_zero.mpr (fun hi => ha (hmem i a hi))
    simp [hz, Multiset.count_eq_zero.mpr ha]

/-- Exact edge coverage, with every edge used once. -/
theorem edge_partition :
    (∑ t : PathSlot C, ((slotWalk C hbranch t).walk.edges :
      Multiset (Sym2 (Fin C.v)))) = C.graph.edgeFinset.1 := by
  apply sum_lists_eq_finset
  · exact fun t => (slotWalk_trail C hbranch t).edges_nodup
  · intro t e he
    induction e using Sym2.ind with
    | _ x y =>
      exact C.graph.mem_edgeFinset.mpr ((slotWalk C hbranch t).walk.adj_of_mem_edges he)
  · intro e he
    induction e using Sym2.ind with
    | _ x y => exact existsUnique_edge C hbranch (C.graph.mem_edgeFinset.mp he)

/-- Exact internal-vertex coverage, including singleton components. -/
theorem internal_partition :
    (∑ t : PathSlot C, (walkInternal (slotWalk C hbranch t).walk :
      Multiset (Fin C.v))) = (Finset.univ \ branchVertices C.graph).1 := by
  apply sum_lists_eq_finset
  · exact slotWalk_internal_nodup C hbranch
  · intro t x hx
    simpa using! slotWalk_internal_nonbranch C hbranch t hx
  · intro x hx
    exact existsUnique_internal C hbranch (by simpa using! hx)

include hbranch in
/-- The number of unlabelled path occurrences is branch count plus excess. -/
theorem card_pathSlot :
    Fintype.card (PathSlot C) = (branchVertices C.graph).card + r := by
  have he := congrArg Multiset.card (edge_partition C hbranch)
  have hi := congrArg Multiset.card (internal_partition C hbranch)
  simp only [Multiset.card_sum, Multiset.coe_card, SimpleGraph.Walk.length_edges] at he
  simp only [Multiset.card_sum, Multiset.coe_card] at hi
  have he' : (∑ t : PathSlot C, (slotWalk C hbranch t).walk.length) = C.v + r := by
    change (∑ t : PathSlot C, (slotWalk C hbranch t).walk.length) =
      C.graph.edgeFinset.card at he
    exact he.trans C.edge_card
  have hi' : (∑ t : PathSlot C, (walkInternal (slotWalk C hbranch t).walk).length) =
      C.v - (branchVertices C.graph).card := by
    change (∑ t : PathSlot C, (walkInternal (slotWalk C hbranch t).walk).length) =
      (Finset.univ \ branchVertices C.graph).card at hi
    simpa only [Finset.card_sdiff_of_subset (Finset.subset_univ _),
      Finset.card_univ, Fintype.card_fin] using! hi
  have hsum : (∑ t : PathSlot C, (slotWalk C hbranch t).walk.length) =
      (∑ t : PathSlot C, (walkInternal (slotWalk C hbranch t).walk).length) +
        Fintype.card (PathSlot C) := by
    calc
      _ = ∑ t : PathSlot C, ((walkInternal (slotWalk C hbranch t).walk).length + 1) :=
        Finset.sum_congr rfl (fun t _ => slotWalk_length C hbranch t)
      _ = _ := by rw [Finset.sum_add_distrib]; simp
  have hb : (branchVertices C.graph).card ≤ C.v := by
    simpa using! Finset.card_le_card (Finset.subset_univ (branchVertices C.graph))
  omega

end Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_PathAssembly


/-!
# The finite kernel obtained by suppressing the assembled paths

Branch incidences are counted before labelling, with two incidences for a
closed path. Retraction of each interior to its first branch transfers core
connectedness. Sorting endpoints reverses walks when necessary, preserving
both exact multiset partitions.
-/

open scoped BigOperators Sym2

noncomputable section

namespace Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_KernelAssembly

open Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_CoreConnected
open Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_PathPartition
open Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_PathAssembly
open Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_ComponentPath
open Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_EdgeLabelled
open Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_Mass
open Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_Expansion

attribute [local instance] Classical.propDecidable

private theorem support_decomposition {V : Type*} {H : SimpleGraph V} {a b : V}
    (w : H.Walk a b) (hp : 0 < w.length) :
    w.support = a :: (walkInternal w ++ [b]) := by
  cases w with
  | nil => simp at hp
  | cons h w =>
    change a :: w.support = a :: (w.support.dropLast ++ [b])
    rw [w.support_eq_concat]
    simp

variable {k r : ℕ} {G : Erdos745.WrapUp.Graph k}
variable (C : ConnectedCoreIn G r) (hbranch : (branchVertices C.graph).Nonempty)

/-- At a branch, a path contributes exactly its endpoint incidences. -/
theorem slot_branch_incidence (t : PathSlot C) {x : Fin C.v}
    (hx : x ∈ branchVertices C.graph) :
    ((slotWalk C hbranch t).walk.edges.countP (fun e => decide (x ∈ e))) =
      (if (slotWalk C hbranch t).first = x then 1 else 0) +
      (if (slotWalk C hbranch t).last = x then 1 else 0) := by
  cases t with
  | inl S =>
    let P := exists_componentPath C hbranch S
    have hfirst : x ≠ P.first.1.1 := fun h => P.first.1.2 (h ▸ hx)
    have hlast : x ≠ P.last.1.1 := fun h => P.last.1.2 (h ▸ hx)
    have hz : P.corePath.edges.countP (fun e => decide (x ∈ e)) = 0 := by
      apply List.countP_eq_zero.mpr
      intro e he hm
      have hxm : x ∈ e := of_decide_eq_true hm
      induction e using Sym2.ind with
      | _ y z =>
        rcases Sym2.mem_iff.mp hxm with rfl | rfl
        · exact P.corePath_nonbranch (P.corePath.fst_mem_support_of_mem_edges he) hx
        · exact P.corePath_nonbranch (P.corePath.snd_mem_support_of_mem_edges he) hx
    change P.attached.edges.countP _ =
      (if P.first_branch = x then 1 else 0) + (if P.last_branch = x then 1 else 0)
    simp only [ComponentPath.attached, SimpleGraph.Walk.edges_cons,
      SimpleGraph.Walk.edges_concat, List.concat_eq_append, List.countP_cons,
      List.countP_append, List.countP_nil, hz, Sym2.mem_iff,
      hfirst, hlast, or_false, false_or, decide_eq_true_eq, Nat.zero_add]
    simp only [eq_comm, Nat.add_comm]
  | inr e =>
    have hne := ne_of_lt e.2.1
    by_cases h₁ : e.1.1 = x <;> by_cases h₂ : e.1.2 = x <;>
      simp_all [slotWalk, SimpleGraph.Adj.toWalk, Sym2.mem_iff, eq_comm]

/-- Suppression preserves the degree of every branch, including loop ends. -/
theorem branch_degree_eq_endpoint_sum {x : Fin C.v}
    (hx : x ∈ branchVertices C.graph) :
    C.graph.degree x = ∑ t : PathSlot C,
      ((if (slotWalk C hbranch t).first = x then 1 else 0) +
       (if (slotWalk C hbranch t).last = x then 1 else 0)) := by
  let F := Multiset.countPAddMonoidHom (fun e : Sym2 (Fin C.v) => x ∈ e)
  have he := congrArg F (edge_partition C hbranch)
  rw [map_sum] at he
  have hright : F C.graph.edgeFinset.1 = C.graph.degree x := by
    change Multiset.countP (fun e => x ∈ e) C.graph.edgeFinset.1 = _
    rw [Multiset.countP_eq_card_filter]
    change (C.graph.edgeFinset.filter (fun e => x ∈ e)).card = _
    rw [← C.graph.incidenceFinset_eq_filter, C.graph.card_incidenceFinset_eq_degree]
  rw [hright] at he
  rw [← he]
  apply Finset.sum_congr rfl
  intro t _
  exact slot_branch_incidence C hbranch t hx

/-- The actual number of branch vertices lies in the allowed kernel range. -/
def branchSize : KernelSize r :=
  ⟨(branchVertices C.graph).card, Finset.mem_Icc.mpr
    ⟨Finset.card_pos.mpr hbranch,
      card_branchVertices_le C.graph C.edge_card C.min_degree⟩⟩

def branchEquiv : Fin (branchSize C hbranch).1 ≃ ↥(branchVertices C.graph) :=
  (branchVertices C.graph).equivFin.symm

def branchEmbedding : Fin (branchSize C hbranch).1 ↪ Fin C.v :=
  (branchEquiv C hbranch).toEmbedding.trans (Function.Embedding.subtype _)

@[simp] theorem branchEmbedding_apply (i : Fin (branchSize C hbranch).1) :
    branchEmbedding C hbranch i = (branchEquiv C hbranch i).1 := rfl

theorem branchEmbedding_image :
    Finset.univ.image (branchEmbedding C hbranch) = branchVertices C.graph := by
  ext x
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, rfl⟩
    exact (branchEquiv C hbranch i).2
  · intro hx
    exact ⟨(branchEquiv C hbranch).symm ⟨x, hx⟩,
      congrArg Subtype.val ((branchEquiv C hbranch).apply_symm_apply ⟨x, hx⟩)⟩

def slotEquiv : Fin ((branchSize C hbranch).1 + r) ≃ PathSlot C :=
  (Fintype.equivFinOfCardEq (card_pathSlot C hbranch)).symm

def firstLabel (t : PathSlot C) : Fin (branchSize C hbranch).1 :=
  (branchEquiv C hbranch).symm
    ⟨(slotWalk C hbranch t).first, (slotWalk C hbranch t).first_branch⟩

def lastLabel (t : PathSlot C) : Fin (branchSize C hbranch).1 :=
  (branchEquiv C hbranch).symm
    ⟨(slotWalk C hbranch t).last, (slotWalk C hbranch t).last_branch⟩

@[simp] theorem branch_firstLabel (t : PathSlot C) :
    branchEmbedding C hbranch (firstLabel C hbranch t) = (slotWalk C hbranch t).first :=
  congrArg Subtype.val ((branchEquiv C hbranch).apply_symm_apply _)

@[simp] theorem branch_lastLabel (t : PathSlot C) :
    branchEmbedding C hbranch (lastLabel C hbranch t) = (slotWalk C hbranch t).last :=
  congrArg Subtype.val ((branchEquiv C hbranch).apply_symm_apply _)

/-- Relabel endpoints without changing the walk. -/
def labelledWalk (t : PathSlot C) :
    C.graph.Walk (branchEmbedding C hbranch (firstLabel C hbranch t))
      (branchEmbedding C hbranch (lastLabel C hbranch t)) :=
  (slotWalk C hbranch t).walk.copy (branch_firstLabel C hbranch t).symm
    (branch_lastLabel C hbranch t).symm

/-- Sort the two branch labels while retaining this occurrence's identity. -/
def sortedEdge (t : PathSlot C) : KernelIndex (branchSize C hbranch).1 :=
  if h : firstLabel C hbranch t ≤ lastLabel C hbranch t then
    ⟨(firstLabel C hbranch t, lastLabel C hbranch t), h⟩
  else ⟨(lastLabel C hbranch t, firstLabel C hbranch t), le_of_not_ge h⟩

def orientedWalk (t : PathSlot C) :
    C.graph.Walk (branchEmbedding C hbranch (sortedEdge C hbranch t).1.1)
      (branchEmbedding C hbranch (sortedEdge C hbranch t).1.2) :=
  if h : firstLabel C hbranch t ≤ lastLabel C hbranch t then
    (labelledWalk C hbranch t).copy
      (by simp only [sortedEdge, dif_pos h]) (by simp only [sortedEdge, dif_pos h])
  else (labelledWalk C hbranch t).reverse.copy
      (by simp only [sortedEdge, dif_neg h]) (by simp only [sortedEdge, dif_neg h])

theorem orientedWalk_edges (t : PathSlot C) :
    ((orientedWalk C hbranch t).edges : Multiset (Sym2 (Fin C.v))) =
      (slotWalk C hbranch t).walk.edges := by
  unfold orientedWalk
  split_ifs <;> simp [labelledWalk]

theorem orientedWalk_internal (t : PathSlot C) :
    (walkInternal (orientedWalk C hbranch t) : Multiset (Fin C.v)) =
      walkInternal (slotWalk C hbranch t).walk := by
  unfold orientedWalk
  split_ifs <;> simp [labelledWalk, walkInternal, List.tail_dropLast]

theorem orientedWalk_length (t : PathSlot C) :
    (orientedWalk C hbranch t).length = (slotWalk C hbranch t).walk.length := by
  unfold orientedWalk
  split_ifs <;> simp [labelledWalk]

theorem orientedWalk_trail (t : PathSlot C) : (orientedWalk C hbranch t).IsTrail := by
  have he := orientedWalk_edges C hbranch t
  rw [SimpleGraph.Walk.isTrail_def]
  change Multiset.Nodup ((orientedWalk C hbranch t).edges : Multiset (Sym2 (Fin C.v)))
  rw [he]
  exact (slotWalk_trail C hbranch t).edges_nodup

theorem sortedEdge_incidence (i : Fin (branchSize C hbranch).1) (t : PathSlot C) :
    incidence i (sortedEdge C hbranch t) =
      (if (slotWalk C hbranch t).first = branchEmbedding C hbranch i then 1 else 0) +
      (if (slotWalk C hbranch t).last = branchEmbedding C hbranch i then 1 else 0) := by
  have hf : firstLabel C hbranch t = i ↔
      (slotWalk C hbranch t).first = branchEmbedding C hbranch i := by
    rw [← branch_firstLabel C hbranch t]
    exact (branchEmbedding C hbranch).injective.eq_iff.symm
  have hl : lastLabel C hbranch t = i ↔
      (slotWalk C hbranch t).last = branchEmbedding C hbranch i := by
    rw [← branch_lastLabel C hbranch t]
    exact (branchEmbedding C hbranch).injective.eq_iff.symm
  by_cases h : firstLabel C hbranch t ≤ lastLabel C hbranch t
  · simp only [sortedEdge, dif_pos h, incidence, hf, hl]
  · simp only [sortedEdge, dif_neg h, incidence, hf, hl, Nat.add_comm]

def kernelEdges (t : Fin ((branchSize C hbranch).1 + r)) :
    KernelIndex (branchSize C hbranch).1 :=
  sortedEdge C hbranch (slotEquiv C hbranch t)

/-- Kernel degree equals core degree under the branch embedding. -/
theorem kernel_degree (i : Fin (branchSize C hbranch).1) :
    (∑ t, incidence i (kernelEdges C hbranch t)) =
      C.graph.degree (branchEmbedding C hbranch i) := by
  unfold kernelEdges
  rw [(slotEquiv C hbranch).sum_comp (fun t => incidence i (sortedEdge C hbranch t))]
  simp_rw [sortedEdge_incidence]
  exact (branch_degree_eq_endpoint_sum C hbranch (branchEquiv C hbranch i).2).symm

/-- Contract every interior to the first endpoint of its unique path. -/
def retract (x : Fin C.v) : Fin (branchSize C hbranch).1 :=
  if hx : x ∈ branchVertices C.graph then (branchEquiv C hbranch).symm ⟨x, hx⟩
  else firstLabel C hbranch (Classical.choose (existsUnique_internal C hbranch hx))

@[simp] theorem retract_branch (i : Fin (branchSize C hbranch).1) :
    retract C hbranch (branchEmbedding C hbranch i) = i := by
  have hi : branchEmbedding C hbranch i ∈ branchVertices C.graph :=
    (branchEquiv C hbranch i).2
  rw [retract, dif_pos hi]
  exact (branchEquiv C hbranch).symm_apply_apply i

theorem retract_first (t : PathSlot C) :
    retract C hbranch (slotWalk C hbranch t).first = firstLabel C hbranch t := by
  rw [← branch_firstLabel C hbranch t, retract_branch]

theorem retract_last (t : PathSlot C) :
    retract C hbranch (slotWalk C hbranch t).last = lastLabel C hbranch t := by
  rw [← branch_lastLabel C hbranch t, retract_branch]

theorem retract_internal (t : PathSlot C) {x : Fin C.v}
    (hx : x ∈ walkInternal (slotWalk C hbranch t).walk) :
    retract C hbranch x = firstLabel C hbranch t := by
  have hn := slotWalk_internal_nonbranch C hbranch t hx
  rw [retract, dif_neg hn]
  have hu := (Classical.choose_spec (existsUnique_internal C hbranch hn)).2 t hx
  rw [← hu]

theorem retract_support (t : PathSlot C) {x : Fin C.v}
    (hx : x ∈ (slotWalk C hbranch t).walk.support) :
    retract C hbranch x = firstLabel C hbranch t ∨
      retract C hbranch x = lastLabel C hbranch t := by
  rw [support_decomposition _ (slotWalk_positive C hbranch t)] at hx
  simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | hx | rfl
  · exact Or.inl (retract_first C hbranch t)
  · exact Or.inl (retract_internal C hbranch t hx)
  · exact Or.inr (retract_last C hbranch t)

private theorem endpoints_reachable (t : PathSlot C)
    {i j : Fin (branchSize C hbranch).1}
    (hi : i = firstLabel C hbranch t ∨ i = lastLabel C hbranch t)
    (hj : j = firstLabel C hbranch t ∨ j = lastLabel C hbranch t) :
    Relation.ReflTransGen (occurrenceAdj (kernelEdges C hbranch)) i j := by
  by_cases hij : i = j
  · subst j
    exact .refl
  · apply Relation.ReflTransGen.single
    refine ⟨hij, (slotEquiv C hbranch).symm t, ?_⟩
    simp only [kernelEdges, Equiv.apply_symm_apply]
    unfold sortedEdge
    split_ifs <;> rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;>
      simp_all

private theorem adjacent_retract_reachable {x y : Fin C.v} (hxy : C.graph.Adj x y) :
    Relation.ReflTransGen (occurrenceAdj (kernelEdges C hbranch))
      (retract C hbranch x) (retract C hbranch y) := by
  obtain ⟨t, ht, _⟩ := existsUnique_edge C hbranch hxy
  exact endpoints_reachable C hbranch t
    (retract_support C hbranch t ((slotWalk C hbranch t).walk.fst_mem_support_of_mem_edges ht))
    (retract_support C hbranch t ((slotWalk C hbranch t).walk.snd_mem_support_of_mem_edges ht))

/-- Core connectedness survives suppression of all the interiors. -/
theorem kernel_connected (i j : Fin (branchSize C hbranch).1) :
    Relation.ReflTransGen (occurrenceAdj (kernelEdges C hbranch)) i j := by
  have hw : ∀ {x y : Fin C.v} (w : C.graph.Walk x y),
      Relation.ReflTransGen (occurrenceAdj (kernelEdges C hbranch))
        (retract C hbranch x) (retract C hbranch y) := by
    intro x y w
    induction w with
    | nil => exact .refl
    | cons h w ih => exact (adjacent_retract_reachable C hbranch h).trans ih
  obtain ⟨w⟩ := C.connected.preconnected
    (branchEmbedding C hbranch i) (branchEmbedding C hbranch j)
  simpa only [retract_branch] using! hw w

/-- Labelled occurrences with exact degrees and connected underlying graph. -/
def occurrenceKernel : OccurrenceKernel (branchSize C hbranch).1 r where
  edge := kernelEdges C hbranch
  connected := kernel_connected C hbranch
  minDegree i := by
    rw [kernel_degree]
    exact mem_branchVertices.mp (branchEquiv C hbranch i).2

/-- The degree-two component construction supplies every field of the exact
maximal-path partition, without any suppression premise. -/
def maximalPathPartition : MaximalPathPartition C where
  v := branchSize C hbranch
  branch := branchEmbedding C hbranch
  branch_image := branchEmbedding_image C hbranch
  kernel := occurrenceKernel C hbranch
  walk t := orientedWalk C hbranch (slotEquiv C hbranch t)
  trail t := orientedWalk_trail C hbranch _
  positive t := by
    exact (orientedWalk_length C hbranch (slotEquiv C hbranch t)).symm ▸
      slotWalk_positive C hbranch (slotEquiv C hbranch t)
  internal_degree_two t x hx := by
    have hm := orientedWalk_internal C hbranch (slotEquiv C hbranch t)
    have hx' : x ∈ walkInternal (slotWalk C hbranch (slotEquiv C hbranch t)).walk := by
      change x ∈ (walkInternal (slotWalk C hbranch (slotEquiv C hbranch t)).walk : Multiset _)
      rw [← hm]
      exact hx
    exact slotWalk_internal_degree_two C hbranch _ hx'
  edge_partition := by
    calc
      _ = ∑ t : Fin ((branchSize C hbranch).1 + r),
          ((slotWalk C hbranch (slotEquiv C hbranch t)).walk.edges : Multiset (Sym2 (Fin C.v))) :=
        Finset.sum_congr rfl (fun t _ => orientedWalk_edges C hbranch _)
      _ = _ := ((slotEquiv C hbranch).sum_comp
        (fun t => ((slotWalk C hbranch t).walk.edges : Multiset (Sym2 (Fin C.v))))).trans
          (edge_partition C hbranch)
  internal_partition := by
    calc
      _ = ∑ t : Fin ((branchSize C hbranch).1 + r),
          (walkInternal (slotWalk C hbranch (slotEquiv C hbranch t)).walk : Multiset (Fin C.v)) :=
        Finset.sum_congr rfl (fun t _ => orientedWalk_internal C hbranch _)
      _ = _ := ((slotEquiv C hbranch).sum_comp
        (fun t => (walkInternal (slotWalk C hbranch t).walk : Multiset (Fin C.v)))).trans
          (internal_partition C hbranch)
  loop_internal_two t he := by
    have hend : (slotWalk C hbranch (slotEquiv C hbranch t)).first =
        (slotWalk C hbranch (slotEquiv C hbranch t)).last := by
      change (sortedEdge C hbranch (slotEquiv C hbranch t)).1.1 =
        (sortedEdge C hbranch (slotEquiv C hbranch t)).1.2 at he
      have hl : firstLabel C hbranch (slotEquiv C hbranch t) =
          lastLabel C hbranch (slotEquiv C hbranch t) := by
        unfold sortedEdge at he
        split_ifs at he
        · exact he
        · exact he.symm
      have hb := congrArg (branchEmbedding C hbranch) hl
      simpa only [branch_firstLabel, branch_lastLabel] using! hb
    have hlen := congrArg Multiset.card
      (orientedWalk_internal C hbranch (slotEquiv C hbranch t))
    simp only [Multiset.coe_card] at hlen
    exact hlen.symm ▸ slotWalk_loop_internal_two C hbranch _ hend

/-- Every positive-excess connected graph has an actual suppressed-path
partition of its extracted core. -/
theorem positiveExcessGraph_has_maximalPathPartition (hr : 0 < r)
    (hG : G ∈ positiveExcessGraphs k r) :
    ∃ C : ConnectedCoreIn G r, Nonempty (MaximalPathPartition C) := by
  obtain ⟨C, hb, _⟩ := positiveExcessGraph_has_branch_core hr hG
  exact ⟨C, ⟨maximalPathPartition C hb⟩⟩

end Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_KernelAssembly
