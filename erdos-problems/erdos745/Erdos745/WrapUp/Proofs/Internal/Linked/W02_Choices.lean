module

public import Erdos745.WrapUp.Proofs.Internal.Linked.W02_Paths
public import Erdos745.WrapUp.Proofs.Internal.Linked.W02_DecodeEncode

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local simp] Pi.div_def Pi.mul_def Pi.add_def Pi.sub_def Pi.neg_def Pi.inv_def Function.comp_def Pi.pow_def Pi.smul_def Real.rpow_eq_pow

@[expose] public section


/-!
# Exact presentations of a maximal-path partition

The occurrence order chosen by the finite decoder is matched to the labelled
paths without identifying parallel occurrences. Branches followed by all path
interiors enumerate the core once. This order encodes the rooted forest, and
the decoded path graph is exactly the embedded core.
-/

open scoped BigOperators Sym2
noncomputable section

namespace Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_Presentation

open Erdos745.WrapUp
open Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_CoreConnected
open Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_CoreForest
open Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_PathPartition
open Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_KernelAssembly
open Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_EdgeLabelled
open Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_Expansion
open Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_Occurrences
open Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_Decode
open Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_Encode

attribute [local instance] Classical.propDecidable

/-- Matching two enumerations preserves occurrences, including repetitions. -/
def matchingPermutation {α : Type*} [DecidableEq α] {n : ℕ}
    (f g : Fin n → α) (h : (List.ofFn f : Multiset α) = List.ofFn g) :
    Equiv.Perm (Fin n) :=
  let hp := Multiset.coe_eq_coe.mp h
  let e : Fin (List.ofFn f).length ≃ Fin (List.ofFn g).length :=
    ⟨hp.idxBij, hp.symm.idxBij, hp.idxBij_rightInverse_idxBij_symm,
      hp.idxBij_leftInverse_idxBij_symm⟩
  ((finCongr (List.length_ofFn (f := f))).symm.trans e).trans
    (finCongr (List.length_ofFn (f := g)))

theorem matchingPermutation_apply {α : Type*} [DecidableEq α] {n : ℕ}
    (f g : Fin n → α) (h : (List.ofFn f : Multiset α) = List.ofFn g)
    (i : Fin n) : g (matchingPermutation f g h i) = f i := by
  have hi := (Multiset.coe_eq_coe.mp h).getElem_idxBij_eq_getElem
    (Fin.cast (List.length_ofFn (f := f)).symm i)
  simpa only [List.getElem_ofFn] using! hi

/-- Flattening finite lists agrees with the exact multiset sum. -/
theorem coe_flatten_ofFn {α : Type*} {n : ℕ} (f : Fin n → List α) :
    ((List.ofFn f).flatten : Multiset α) = ∑ i, (f i : Multiset α) := by
  rw [← Multiset.coe_join]
  simp [Multiset.join, List.map_ofFn, List.sum_ofFn, Function.comp_def]

/-- A length vector recovers its own concatenated blocks, including empties. -/
theorem splitBy_lengths_flatten {α : Type*} (blocks : List (List α)) :
    splitBy (blocks.map List.length) blocks.flatten = blocks := by
  induction blocks with
  | nil => rfl
  | cons b bs ih => simp [splitBy, ih]

private theorem support_decomposition {V : Type*} {H : SimpleGraph V} {a b : V}
    (w : H.Walk a b) (hp : 0 < w.length) :
    w.support = a :: (walkInternal w ++ [b]) := by
  cases w with
  | nil => simp at hp
  | cons h w =>
    change a :: w.support = a :: (w.support.dropLast ++ [b])
    rw [w.support_eq_concat]
    simp

variable {k r : ℕ} {G : Graph k} {C : ConnectedCoreIn G r}

section Partition

variable (P : MaximalPathPartition C)

private theorem occurrence_multiset :
    (List.ofFn (kernelEdgeAt P.kernelChoice.1) :
      Multiset (W02_KERNEL_Mass.KernelIndex P.v.1)) = List.ofFn P.kernel.edge := by
  rw [ofFn_kernelEdgeAt]
  exact P.kernel.ordered_edges_eq_occurrences

/-- Decoder slot to original path label. -/
def occurrenceOrder : Equiv.Perm (Fin (P.v.1 + r)) :=
  matchingPermutation (kernelEdgeAt P.kernelChoice.1) P.kernel.edge (occurrence_multiset P)

theorem occurrenceOrder_edge (t : Fin (P.v.1 + r)) :
    P.kernel.edge ((occurrenceOrder P) t) = kernelEdgeAt P.kernelChoice.1 t :=
  matchingPermutation_apply _ _ _ t

/-- Internal core vertices in the decoder's occurrence order. -/
def internalBlock (t : Fin (P.v.1 + r)) : List (Fin C.v) :=
  walkInternal (P.walk ((occurrenceOrder P) t))

theorem internalBlock_partition :
    (∑ t, ((internalBlock P) t : Multiset (Fin C.v))) =
      (Finset.univ \ branchVertices C.graph).val := by
  change (∑ t, (walkInternal (P.walk ((occurrenceOrder P) t)) :
    Multiset (Fin C.v))) = _
  rw [Equiv.sum_comp (occurrenceOrder P)
    (fun t => (walkInternal (P.walk t) : Multiset (Fin C.v)))]
  exact P.internal_partition

/-- Branch labels first, then the concatenated internal path lists. -/
def coreRootList : List (Fin C.v) :=
  List.ofFn P.branch ++ (List.ofFn (internalBlock P)).flatten

theorem coreRootList_multiset :
    ((coreRootList P) : Multiset (Fin C.v)) = Finset.univ.val := by
  have hb : (List.ofFn P.branch : Multiset (Fin C.v)) =
      (branchVertices C.graph).val := by
    let s : Finset (Fin C.v) := ⟨List.ofFn P.branch,
      List.nodup_ofFn.mpr P.branch.injective⟩
    have hs : s = branchVertices C.graph := by
      rw [← P.branch_image]
      ext x
      simp [s]
    exact congrArg Finset.val hs
  change (List.ofFn P.branch : Multiset (Fin C.v)) +
    ((List.ofFn (internalBlock P)).flatten : Multiset (Fin C.v)) = _
  rw [hb, coe_flatten_ofFn, (internalBlock_partition P)]
  change ((branchVertices C.graph).disjUnion
    (Finset.univ \ branchVertices C.graph) Finset.disjoint_sdiff).val = _
  rw [Finset.disjUnion_eq_union, Finset.union_sdiff_of_subset (Finset.subset_univ _)]

theorem coreRootList_length : (coreRootList P).length = C.v := by
  have h := congrArg Multiset.card (coreRootList_multiset P)
  simpa using! h

theorem coreRootList_nodup : (coreRootList P).Nodup := by
  change Multiset.Nodup ((coreRootList P) : Multiset (Fin C.v))
  rw [(coreRootList_multiset P)]
  exact Finset.univ.nodup

/-- The concatenated root list is an actual permutation of the core. -/
def coreOrder : Equiv.Perm (Fin C.v) :=
  (finCongr (coreRootList_length P)).symm.trans
    ((coreRootList_nodup P).getEquivOfForallMemList (coreRootList P) (by
      intro x
      change x ∈ ((coreRootList P) : Multiset (Fin C.v))
      rw [(coreRootList_multiset P)]
      exact Finset.mem_univ x))

/-- Ambient labels of the ordered core roots. -/
def roots : Fin C.v ↪ Fin k := (coreOrder P).toEmbedding.trans C.labels

theorem roots_ofFn : List.ofFn (roots P) = (coreRootList P).map C.labels := by
  apply List.ext_get
  · simp [(coreRootList_length P)]
  · intro i hi hj
    simp [roots, coreOrder]

theorem roots_image : Finset.univ.image (roots P) = coreLabels C := by
  ext x
  simp only [Finset.mem_image, Finset.mem_univ, true_and, coreLabels]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨(coreOrder P) i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨(coreOrder P).symm i, by simp [roots]⟩

theorem branch_le_core : P.v.1 ≤ C.v := by
  simpa using! Fintype.card_le_of_embedding P.branch

/-- The number of forest roots is the full core size. -/
def treeCount : TreeCount k P.v.1 :=
  ⟨C.v, Finset.mem_Icc.mpr ⟨(branch_le_core P),
    by simpa using! Fintype.card_le_of_embedding C.labels⟩⟩

theorem roots_branch (i : Fin P.v.1) :
    (roots P) (Fin.castLE (branch_le_core P) i) = C.labels (P.branch i) := by
  have hi : i.val < (coreRootList P).length := by
    rw [coreRootList_length P]
    exact lt_of_lt_of_le i.isLt (branch_le_core P)
  change C.labels ((coreRootList P)[i.val]'hi) = _
  congr 1
  simp only [coreRootList]
  rw [List.getElem_append_left (by simp)]
  simp

/-- Semantic lengths and ordered roots attached to the partition. -/
def presentation
    (hforest : ∀ S ∈ components (coreComplement C),
      isTree (coreComplement C) S ∧ (S ∩ coreLabels C).card = 1) :
    ExpansionPresentation k r P.v (treeCount P) where
  H := P.kernelChoice
  lengths := fun t => ((internalBlock P) t).length
  sum_lengths := by
    change (∑ t, (walkInternal (P.walk ((occurrenceOrder P) t))).length) = _
    rw [Equiv.sum_comp (occurrenceOrder P) (fun t => (walkInternal (P.walk t)).length)]
    exact P.sum_internal_lengths
  roots := (roots P)
  forest := coreComplement C
  forest_spec := by
    change ∀ S ∈ components (coreComplement C),
      isTree (coreComplement C) S ∧ (S ∩ Finset.univ.image (roots P)).card = 1
    rw [roots_image P]
    exact hforest

variable (hforest : ∀ S ∈ components (coreComplement C),
  isTree (coreComplement C) S ∧ (S ∩ coreLabels C).card = 1)

theorem presentation_internalBlocks :
    codeInternalBlocks ((presentation P) hforest).code =
      List.ofFn (fun t => ((internalBlock P) t).map C.labels) := by
  rw [ExpansionPresentation.codeInternalBlocks_code]
  change splitBy (List.ofFn (fun t => ((internalBlock P) t).length))
    ((List.ofFn (roots P)).drop P.v.1) = _
  rw [(roots_ofFn P)]
  have hempty : (List.ofFn (fun i => C.labels (P.branch i))).drop P.v.1 = [] := by
    apply List.drop_eq_nil_of_le
    simp
  have h := splitBy_lengths_flatten
    (List.ofFn (fun t => ((internalBlock P) t).map C.labels))
  simpa [coreRootList, List.map_ofFn, List.map_flatten, List.drop_append,
    Function.comp_def, hempty] using! h

theorem presentation_kernelLabel (i : Fin P.v.1) :
    kernelVertexLabel ((presentation P) hforest).code i = C.labels (P.branch i) := by
  rw [ExpansionPresentation.kernelVertexLabel_code]
  exact (roots_branch P) i

/-- Each decoded occurrence is literally its original walk support. -/
theorem presentation_occurrenceVertices (t : Fin (P.v.1 + r)) :
    occurrenceVertices ((presentation P) hforest).code t =
      (P.walk ((occurrenceOrder P) t)).support.map C.labels := by
  unfold occurrenceVertices
  simp only [List.get_eq_getElem, presentation_internalBlocks P hforest,
    List.getElem_ofFn]
  change kernelVertexLabel ((presentation P) hforest).code
      (kernelEdgeAt P.kernelChoice.1 t).1.1 ::
    (((internalBlock P) t).map C.labels ++
      [kernelVertexLabel ((presentation P) hforest).code
        (kernelEdgeAt P.kernelChoice.1 t).1.2]) = _
  rw [(presentation_kernelLabel P), (presentation_kernelLabel P),
    ← (occurrenceOrder_edge P) t,
    support_decomposition _ (P.positive ((occurrenceOrder P) t))]
  simp [internalBlock]

end Partition

private theorem edgeBetween_some_iff {k : ℕ} (a b : Fin k) (e : Edge k) :
    edgeBetween? a b = some e ↔ s(a, b) = s(e.1.1, e.1.2) := by
  by_cases hab : a < b
  · simp only [edgeBetween?, dif_pos hab, Option.some.injEq,
      Subtype.ext_iff, Prod.ext_iff, Sym2.eq_iff]
    constructor
    · exact Or.inl
    · rintro (h | h)
      · exact h
      · have hba : b < a := by simpa [h.1, h.2] using! e.2
        exact False.elim (lt_asymm hab hba)
  · by_cases hba : b < a
    · simp only [edgeBetween?, dif_neg hab, dif_pos hba, Option.some.injEq,
        Subtype.ext_iff, Prod.ext_iff, Sym2.eq_iff]
      constructor
      · rintro ⟨h₁, h₂⟩; exact Or.inr ⟨h₂, h₁⟩
      · rintro (h | h)
        · have hab' : a < b := by simpa [h.1, h.2] using! e.2
          exact False.elim (hab hab')
        · exact ⟨h.2, h.1⟩
    · have he : a = b := le_antisymm (le_of_not_gt hba) (le_of_not_gt hab)
      simp only [edgeBetween?, dif_neg hab, dif_neg hba, Sym2.eq_iff]
      constructor
      · intro h; cases h
      · rintro (h | h) <;> have := e.2 <;> simp_all

private theorem mem_pathEdges_iff {k : ℕ} (xs : List (Fin k)) (e : Edge k) :
    e ∈ pathEdges xs ↔
      s(e.1.1, e.1.2) ∈ List.zipWith (fun a b => s(a, b)) xs xs.tail := by
  simp only [pathEdges, List.mem_toFinset, List.mem_filterMap]
  rw [← List.map_uncurry_zip_eq_zipWith]
  simp only [List.mem_map]
  constructor
  · rintro ⟨⟨a, b⟩, hmem, he⟩
    exact ⟨(a, b), hmem, (edgeBetween_some_iff a b e).1 he⟩
  · rintro ⟨⟨a, b⟩, hmem, he⟩
    exact ⟨(a, b), hmem, (edgeBetween_some_iff a b e).2 he⟩

/-- The finite decoder's path edges agree with the usual walk edges. -/
theorem mem_pathEdges_walk {V : Type*} {H : SimpleGraph V} {a b : V}
    (w : H.Walk a b) {k : ℕ} (labels : V → Fin k) (e : Edge k) :
    e ∈ pathEdges (w.support.map labels) ↔
      s(e.1.1, e.1.2) ∈ w.edges.map (Sym2.map labels) := by
  rw [mem_pathEdges_iff, SimpleGraph.Walk.edges_eq_zipWith_support]
  simp only [← List.map_tail, List.zipWith_map, List.map_zipWith, Sym2.map_mk]

private theorem edge_mem_iff_adj {k : ℕ} (F : Graph k) (e : Edge k) :
    e ∈ F ↔ (W01_ENUM_Trees.simpleGraph F).Adj e.1.1 e.1.2 := by
  constructor
  · intro he; exact ⟨e, he, Or.inl ⟨rfl, rfl⟩⟩
  · rintro ⟨f, hf, h | h⟩
    · have hfe : f = e := Subtype.ext (Prod.ext h.1 h.2)
      simpa [hfe] using! hf
    · have hback : e.1.2 < e.1.1 := by
        rw [← h.1, ← h.2]
        exact f.2
      exact False.elim (lt_asymm e.2 hback)

section Partition
variable (P : MaximalPathPartition C)
variable (hforest : ∀ S ∈ components (coreComplement C),
  isTree (coreComplement C) S ∧ (S ∩ coreLabels C).card = 1)

/-- Decoding the maximal paths gives exactly the embedded core edges. -/
theorem presentation_kernelPathGraph :
    kernelPathGraph ((presentation P) hforest).code = embeddedCoreEdges C := by
  ext e
  rw [edge_mem_iff_adj (embeddedCoreEdges C), simpleGraph_embeddedCoreEdges]
  change e ∈ kernelPathGraph ((presentation P) hforest).code ↔
    s(e.1.1, e.1.2) ∈ (C.graph.map C.labels).edgeSet
  rw [SimpleGraph.edgeSet_map]
  simp only [kernelPathGraph, Finset.mem_biUnion, Finset.mem_univ, true_and,
    (presentation_occurrenceVertices P) hforest, mem_pathEdges_walk, List.mem_map,
    Set.mem_image]
  constructor
  · rintro ⟨t, q, hq, he⟩
    exact ⟨q, (P.walk ((occurrenceOrder P) t)).edges_subset_edgeSet hq, he⟩
  · rintro ⟨q, hq, he⟩
    have hq' : q ∈ (C.graph.edgeFinset.val : Multiset (Sym2 (Fin C.v))) :=
      SimpleGraph.mem_edgeFinset.mpr hq
    rw [← P.edge_partition, Multiset.mem_sum] at hq'
    obtain ⟨t, _, ht⟩ := hq'
    refine ⟨(occurrenceOrder P).symm t, q, ?_, he⟩
    rw [Equiv.apply_symm_apply]
    exact ht

/-- Exact decoder identity, including the forest decoration. -/
theorem presentation_decode :
    decodeExpansionCode ((presentation P) hforest).code = G := by
  rw [ExpansionPresentation.decode_code, (presentation_kernelPathGraph P)]
  change (G \ embeddedCoreEdges C) ∪ embeddedCoreEdges C = G
  exact Finset.sdiff_union_of_subset (embeddedCoreEdges_subset C)

end Partition

/- Every positive-excess graph has a concrete exact semantic expansion
presentation, with no remaining pruning or decoder premise. -/
end Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_Presentation


/-!
# Freeness of the path data used in a kernel presentation

The two multiset partitions of a maximal-path partition make both core edges
and internal vertices exclusive to one occurrence. Consequently the ordered
endpoint pair and internal list identify a path occurrence. A closed path has
at least two distinct internal vertices, so reversing it changes that list.
These are the graph-theoretic freeness facts needed when the kernel's parallel
occurrences and loop orientations are varied.
-/

open scoped BigOperators Sym2

noncomputable section

namespace Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_ChoiceFreeness

open Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_PathPartition
open Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_CoreConnected

attribute [local instance] Classical.propDecidable

/-- In a nodup sum of finite multisets, two summands sharing an element have
the same index. This keeps the exact multiset hypotheses visible instead of
silently weakening them to set coverage. -/
private theorem index_eq_of_shared {ι α : Type*} [Fintype ι]
    [DecidableEq ι] [DecidableEq α] (f : ι → Multiset α)
    (hn : (∑ i, f i).Nodup) {i j : ι} {a : α}
    (hi : a ∈ f i) (hj : a ∈ f j) : i = j := by
  by_contra hij
  have hcount : (∑ x : ι, Multiset.count a (f x)) ≤ 1 := by
    have h := (Multiset.nodup_iff_count_le_one.mp hn) a
    change (Multiset.countAddMonoidHom a) (∑ x : ι, f x) ≤ 1 at h
    rw [map_sum] at h
    exact h
  have htwo : Multiset.count a (f i) + Multiset.count a (f j) ≤
      ∑ x : ι, Multiset.count a (f x) := by
    calc
      _ = ∑ x ∈ ({i, j} : Finset ι), Multiset.count a (f x) := by
        simp [hij]
      _ ≤ ∑ x : ι, Multiset.count a (f x) :=
        Finset.sum_le_sum_of_subset (by simp)
  have hci : 0 < Multiset.count a (f i) := Multiset.count_pos.mpr hi
  have hcj : 0 < Multiset.count a (f j) := Multiset.count_pos.mpr hj
  omega

/-- The global internal-vertex partition is nodup. -/
private theorem internal_sum_nodup {k r : ℕ} {G : Erdos745.WrapUp.Graph k}
    {C : ConnectedCoreIn G r} (P : MaximalPathPartition C) :
    (∑ t : Fin (P.v.1 + r),
      (walkInternal (P.walk t) : Multiset (Fin C.v))).Nodup := by
  rw [P.internal_partition]
  exact (Finset.univ \ branchVertices C.graph).nodup

/-- The global core-edge partition is nodup. -/
private theorem edge_sum_nodup {k r : ℕ} {G : Erdos745.WrapUp.Graph k}
    {C : ConnectedCoreIn G r} (P : MaximalPathPartition C) :
    (∑ t : Fin (P.v.1 + r),
      ((P.walk t).edges : Multiset (Sym2 (Fin C.v)))).Nodup := by
  rw [P.edge_partition]
  exact C.graph.edgeFinset.nodup

variable {k r : ℕ} {G : Erdos745.WrapUp.Graph k}
variable {C : ConnectedCoreIn G r} (P : MaximalPathPartition C)

/-- Every internal vertex determines its unique suppressed path occurrence. -/
theorem path_eq_of_shared_internal (t u : Fin (P.v.1 + r)) (x : Fin C.v)
    (ht : x ∈ walkInternal (P.walk t))
    (hu : x ∈ walkInternal (P.walk u)) : t = u := by
  apply index_eq_of_shared
    (fun s => (walkInternal (P.walk s) : Multiset (Fin C.v)))
    (internal_sum_nodup P)
  · exact ht
  · exact hu

/-- Every core edge determines its unique suppressed path occurrence. -/
theorem path_eq_of_shared_edge (t u : Fin (P.v.1 + r))
    (e : Sym2 (Fin C.v)) (ht : e ∈ (P.walk t).edges)
    (hu : e ∈ (P.walk u).edges) : t = u := by
  apply index_eq_of_shared
    (fun s => ((P.walk s).edges : Multiset (Sym2 (Fin C.v))))
    (edge_sum_nodup P)
  · exact ht
  · exact hu

/-- Each individual path has no repeated internal vertex. -/
theorem internal_nodup (t : Fin (P.v.1 + r)) :
    (walkInternal (P.walk t)).Nodup := by
  change Multiset.Nodup (walkInternal (P.walk t) : Multiset (Fin C.v))
  apply Multiset.nodup_of_le
    (Finset.single_le_sum (s := Finset.univ)
      (f := fun s : Fin (P.v.1 + r) =>
        (walkInternal (P.walk s) : Multiset (Fin C.v)))
      (by simp) (Finset.mem_univ t))
  exact internal_sum_nodup P

/-- A positive walk with no internal vertices is exactly one edge. -/
private theorem edges_of_empty_internal {V : Type*} {H : SimpleGraph V}
    {a b : V} (w : H.Walk a b) (hp : 0 < w.length)
    (he : walkInternal w = []) : w.edges = [s(a, b)] := by
  have hs : w.support = [a, b] := by
    cases w with
    | nil => simp at hp
    | cons h w =>
      change a :: w.support = [a, b]
      have hconcat := w.support_eq_concat
      have hd : w.support.dropLast = [] := by
        simpa only [walkInternal, List.tail_cons] using! he
      rw [hconcat, hd]
      simp
  rw [w.edges_eq_zipWith_support, hs]
  simp

/-- The sorted endpoint occurrence together with its internal list identifies
the original path, including the unique possible direct edge in a parallel
class. -/
theorem path_signature_injective : Function.Injective
    (fun t : Fin (P.v.1 + r) =>
      (P.kernel.edge t, walkInternal (P.walk t))) := by
  intro t u h
  have hend : P.kernel.edge t = P.kernel.edge u := congrArg Prod.fst h
  have hblock : walkInternal (P.walk t) = walkInternal (P.walk u) :=
    congrArg Prod.snd h
  by_cases hempty : walkInternal (P.walk t) = []
  · have hempty' : walkInternal (P.walk u) = [] := by
      rw [← hblock]
      exact hempty
    let e : Sym2 (Fin C.v) :=
      s(P.branch (P.kernel.edge t).1.1, P.branch (P.kernel.edge t).1.2)
    have ht : e ∈ (P.walk t).edges := by
      rw [edges_of_empty_internal (P.walk t) (P.positive t) hempty]
      simp [e]
    have hu : e ∈ (P.walk u).edges := by
      rw [edges_of_empty_internal (P.walk u) (P.positive u) hempty']
      simp [e, hend]
    exact path_eq_of_shared_edge P t u e ht hu
  · obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ hempty
    exact path_eq_of_shared_internal P t u x hx (hblock ▸ hx)

/-- Reversing a walk reverses precisely its internal list. -/
theorem walkInternal_reverse {V : Type*} {H : SimpleGraph V}
    {a b : V} (w : H.Walk a b) :
    walkInternal w.reverse = (walkInternal w).reverse := by
  simp only [walkInternal, w.support_reverse, List.tail_reverse,
    List.dropLast_reverse, List.tail_dropLast]

/-- A list of at least two distinct elements cannot equal its reversal. -/
private theorem nodup_ne_reverse {α : Type*} (xs : List α)
    (hn : xs.Nodup) (hlen : 2 ≤ xs.length) : xs ≠ xs.reverse := by
  intro heq
  cases xs with
  | nil => simp at hlen
  | cons x ys =>
    cases ys with
    | nil => simp at hlen
    | cons y zs =>
      have hxnot : x ∉ y :: zs := (List.nodup_cons.mp hn).1
      have hlast' : (x :: y :: zs).getLast (by simp) = x := by
        have hh := congrArg List.head? heq
        rw [List.head?_reverse,
          List.getLast?_eq_some_getLast (l := x :: y :: zs) (by simp)] at hh
        exact (Option.some.inj hh).symm
      rw [List.getLast_cons (by simp)] at hlast'
      exact hxnot (hlast' ▸ List.getLast_mem (l := y :: zs) (by simp))

/-- A suppressed loop has a distinguishable orientation in its ordered
internal list. -/
theorem loop_internal_reverse_ne (t : Fin (P.v.1 + r))
    (hloop : (P.kernel.edge t).1.1 = (P.kernel.edge t).1.2) :
    walkInternal (P.walk t) ≠ (walkInternal (P.walk t)).reverse :=
  nodup_ne_reverse _ (internal_nodup P t) (P.loop_internal_two t hloop)

end Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_ChoiceFreeness


/-!
# Reordering and orienting suppressed paths

An exact maximal-path partition remains exact when occurrences inside a
parallel class are reordered and closed paths are independently reversed.
This module transports all path-partition fields, then reuses the semantic
presentation and decoder inverse for the resulting arrangement.
-/

open scoped BigOperators Sym2
noncomputable section

namespace Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_ChoiceArrangement

open Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_PathPartition
open Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_CoreConnected
open Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_CoreForest
open Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_Presentation
open Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_Encode
open Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_Mass

attribute [local instance] Classical.propDecidable

variable {k r : ℕ} {G : Erdos745.WrapUp.Graph k}
variable {C : ConnectedCoreIn G r} (P : MaximalPathPartition C)

/-- Reverse one loop when selected. A nonloop has its original orientation. -/
def flippedWalk (t : Fin (P.v.1 + r)) (b : Bool) :
    C.graph.Walk (P.branch (P.kernel.edge t).1.1)
      (P.branch (P.kernel.edge t).1.2) :=
  if h : (P.kernel.edge t).1.1 = (P.kernel.edge t).1.2 then
    if b then
      (P.walk t).reverse.copy (congrArg P.branch h.symm) (congrArg P.branch h)
    else P.walk t
  else P.walk t

theorem flippedWalk_edges (t : Fin (P.v.1 + r)) (b : Bool) :
    ((flippedWalk P t b).edges : Multiset (Sym2 (Fin C.v))) =
      (P.walk t).edges := by
  unfold flippedWalk
  split_ifs <;> simp [SimpleGraph.Walk.edges_copy,
    SimpleGraph.Walk.edges_reverse]

theorem flippedWalk_internal (t : Fin (P.v.1 + r)) (b : Bool) :
    (walkInternal (flippedWalk P t b) : Multiset (Fin C.v)) =
      walkInternal (P.walk t) := by
  unfold flippedWalk
  split_ifs with h hb
  · simp only [walkInternal, SimpleGraph.Walk.support_copy]
    change ((walkInternal ((P.walk t).reverse) : List (Fin C.v)) :
      Multiset (Fin C.v)) = walkInternal (P.walk t)
    rw [W02_KERNEL_ChoiceFreeness.walkInternal_reverse]
    exact Multiset.coe_reverse _
  · rfl
  · rfl

/-- The ordered block records the orientation of a closed path. -/
theorem flippedWalk_internalList (t : Fin (P.v.1 + r)) (b : Bool) :
    walkInternal (flippedWalk P t b) =
      if (P.kernel.edge t).1.1 = (P.kernel.edge t).1.2 then
        if b then (walkInternal (P.walk t)).reverse else walkInternal (P.walk t)
      else walkInternal (P.walk t) := by
  by_cases h : (P.kernel.edge t).1.1 = (P.kernel.edge t).1.2
  · cases b with
    | false => simp [flippedWalk, h]
    | true =>
      simp only [flippedWalk, dif_pos h, if_pos h, if_true]
      rw [show walkInternal ((P.walk t).reverse.copy
          (congrArg P.branch h.symm) (congrArg P.branch h)) =
          walkInternal ((P.walk t).reverse) by simp [walkInternal]]
      exact W02_KERNEL_ChoiceFreeness.walkInternal_reverse (P.walk t)
  · simp [flippedWalk, h]

theorem flippedWalk_length (t : Fin (P.v.1 + r)) (b : Bool) :
    (flippedWalk P t b).length = (P.walk t).length := by
  unfold flippedWalk
  split_ifs <;> simp

def arrangedWalk (q : Equiv.Perm (Fin (P.v.1 + r)))
    (hq : ∀ t, P.kernel.edge (q t) = P.kernel.edge t)
    (b : Fin (P.v.1 + r) → Bool) (t : Fin (P.v.1 + r)) :
    C.graph.Walk (P.branch (P.kernel.edge t).1.1)
      (P.branch (P.kernel.edge t).1.2) :=
  (flippedWalk P (q t) (b t)).copy
    (congrArg (fun p => P.branch p.1.1) (hq t))
    (congrArg (fun p => P.branch p.1.2) (hq t))

theorem arrangedWalk_edges (q : Equiv.Perm (Fin (P.v.1 + r)))
    (hq : ∀ t, P.kernel.edge (q t) = P.kernel.edge t)
    (b : Fin (P.v.1 + r) → Bool) (t : Fin (P.v.1 + r)) :
    ((arrangedWalk P q hq b t).edges : Multiset (Sym2 (Fin C.v))) =
      (P.walk (q t)).edges := by
  rw [arrangedWalk, SimpleGraph.Walk.edges_copy, flippedWalk_edges]

theorem arrangedWalk_internal (q : Equiv.Perm (Fin (P.v.1 + r)))
    (hq : ∀ t, P.kernel.edge (q t) = P.kernel.edge t)
    (b : Fin (P.v.1 + r) → Bool) (t : Fin (P.v.1 + r)) :
    (walkInternal (arrangedWalk P q hq b t) : Multiset (Fin C.v)) =
      walkInternal (P.walk (q t)) := by
  rw [arrangedWalk]
  simp only [walkInternal, SimpleGraph.Walk.support_copy]
  exact flippedWalk_internal P (q t) (b t)

/-- The ordered block in a new slot is the old block, optionally reversed. -/
theorem arrangedWalk_internalList (q : Equiv.Perm (Fin (P.v.1 + r)))
    (hq : ∀ t, P.kernel.edge (q t) = P.kernel.edge t)
    (b : Fin (P.v.1 + r) → Bool) (t : Fin (P.v.1 + r)) :
    walkInternal (arrangedWalk P q hq b t) =
      if (P.kernel.edge (q t)).1.1 = (P.kernel.edge (q t)).1.2 then
        if b t then (walkInternal (P.walk (q t))).reverse
        else walkInternal (P.walk (q t))
      else walkInternal (P.walk (q t)) := by
  rw [arrangedWalk]
  simp only [walkInternal, SimpleGraph.Walk.support_copy]
  exact flippedWalk_internalList P (q t) (b t)

theorem arrangedWalk_length (q : Equiv.Perm (Fin (P.v.1 + r)))
    (hq : ∀ t, P.kernel.edge (q t) = P.kernel.edge t)
    (b : Fin (P.v.1 + r) → Bool) (t : Fin (P.v.1 + r)) :
    (arrangedWalk P q hq b t).length = (P.walk (q t)).length := by
  rw [arrangedWalk, SimpleGraph.Walk.length_copy, flippedWalk_length]

theorem arrangedWalk_trail (q : Equiv.Perm (Fin (P.v.1 + r)))
    (hq : ∀ t, P.kernel.edge (q t) = P.kernel.edge t)
    (b : Fin (P.v.1 + r) → Bool) (t : Fin (P.v.1 + r)) :
    (arrangedWalk P q hq b t).IsTrail := by
  rw [SimpleGraph.Walk.isTrail_def]
  change Multiset.Nodup
    ((arrangedWalk P q hq b t).edges : Multiset (Sym2 (Fin C.v)))
  rw [arrangedWalk_edges]
  exact (P.trail (q t)).edges_nodup

/-- All exact path-partition invariants survive an arrangement. -/
def arrangedPartition (q : Equiv.Perm (Fin (P.v.1 + r)))
    (hq : ∀ t, P.kernel.edge (q t) = P.kernel.edge t)
    (b : Fin (P.v.1 + r) → Bool) : MaximalPathPartition C where
  v := P.v
  branch := P.branch
  branch_image := P.branch_image
  kernel := P.kernel
  walk := arrangedWalk P q hq b
  trail := arrangedWalk_trail P q hq b
  positive t := by
    rw [arrangedWalk_length]
    exact P.positive (q t)
  internal_degree_two t x hx := by
    have hm := arrangedWalk_internal P q hq b t
    have hx' : x ∈ walkInternal (P.walk (q t)) := by
      change x ∈ (walkInternal (P.walk (q t)) : Multiset _)
      rw [← hm]
      exact hx
    exact P.internal_degree_two (q t) x hx'
  edge_partition := by
    calc
      (∑ t : Fin (P.v.1 + r),
        ((arrangedWalk P q hq b t).edges : Multiset (Sym2 (Fin C.v)))) =
          ∑ t : Fin (P.v.1 + r),
            ((P.walk (q t)).edges : Multiset (Sym2 (Fin C.v))) :=
        Finset.sum_congr rfl (fun t _ => arrangedWalk_edges P q hq b t)
      _ = ∑ t : Fin (P.v.1 + r),
            ((P.walk t).edges : Multiset (Sym2 (Fin C.v))) :=
        Equiv.sum_comp q (fun t : Fin (P.v.1 + r) =>
          ((P.walk t).edges : Multiset (Sym2 (Fin C.v))))
      _ = C.graph.edgeFinset.1 := P.edge_partition
  internal_partition := by
    calc
      (∑ t : Fin (P.v.1 + r),
        (walkInternal (arrangedWalk P q hq b t) : Multiset (Fin C.v))) =
          ∑ t : Fin (P.v.1 + r),
            (walkInternal (P.walk (q t)) : Multiset (Fin C.v)) :=
        Finset.sum_congr rfl (fun t _ => arrangedWalk_internal P q hq b t)
      _ = ∑ t : Fin (P.v.1 + r),
            (walkInternal (P.walk t) : Multiset (Fin C.v)) :=
        Equiv.sum_comp q (fun t : Fin (P.v.1 + r) =>
          (walkInternal (P.walk t) : Multiset (Fin C.v)))
      _ = (Finset.univ \ branchVertices C.graph).1 := P.internal_partition
  loop_internal_two t ht := by
    have ht' : (P.kernel.edge (q t)).1.1 =
        (P.kernel.edge (q t)).1.2 := by rw [hq t]; exact ht
    have hm := congrArg Multiset.card (arrangedWalk_internal P q hq b t)
    simp only [Multiset.coe_card] at hm
    exact hm.symm ▸ P.loop_internal_two (q t) ht'

variable (hforest : ∀ S ∈ components (coreComplement C),
  isTree (coreComplement C) S ∧ (S ∩ coreLabels C).card = 1)

/-- A full semantic expansion presentation of an arranged partition. -/
def arrangedPresentation (q : Equiv.Perm (Fin (P.v.1 + r)))
    (hq : ∀ t, P.kernel.edge (q t) = P.kernel.edge t)
    (b : Fin (P.v.1 + r) → Bool) :
    ExpansionPresentation k r P.v (treeCount P) :=
  presentation (arrangedPartition P q hq b) hforest

/-- Every arranged code decodes back to the original graph. -/
theorem arrangedPresentation_decode (q : Equiv.Perm (Fin (P.v.1 + r)))
    (hq : ∀ t, P.kernel.edge (q t) = P.kernel.edge t)
    (b : Fin (P.v.1 + r) → Bool) :
    Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_Decode.decodeExpansionCode
      ((arrangedPresentation P hforest q hq b).code) = G :=
  presentation_decode (arrangedPartition P q hq b) hforest

/-- The array and therefore the compensated kernel weight are unchanged. -/
theorem arrangedPresentation_kernelWeight
    (q : Equiv.Perm (Fin (P.v.1 + r)))
    (hq : ∀ t, P.kernel.edge (q t) = P.kernel.edge t)
    (b : Fin (P.v.1 + r) → Bool) :
    kernelWeight (arrangedPresentation P hforest q hq b).H.1 =
      kernelWeight P.kernel.choice.1 := by
  rfl

/- The ordered internal block is exactly the selected oriented path. -/
end Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_ChoiceArrangement


/-!
# Canonical finite indices for parallel occurrences and loops

The symmetric-power kernel has one sorted decoder slot for every edge
occurrence.  Each endpoint fiber has its exact multiplicity, so its factorial
permutation acts faithfully on the slots.  Similarly the loop slots have
cardinality `loopCount`.  These finite actions are transported to the native
path partition, where the existing arrangement construction supplies exact
presentations.
-/

open scoped BigOperators Sym2
noncomputable section

namespace Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_ChoiceIndexing

open Erdos745.WrapUp
open Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_Mass
open Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_Occurrences
open Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_Suppression
open Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_PathPartition
open Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_Presentation
open Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_ChoiceArrangement
open Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_CoreConnected
open Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_CoreForest
open Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_Encode

attribute [local instance] Classical.propDecidable

variable {v r : ℕ} (H : KernelArray v r)

/-- Decoder slots carrying one prescribed unordered endpoint pair. -/
abbrev SlotFiber (p : KernelIndex v) :=
  {t : Fin (v + r) // kernelEdgeAt H t = p}

theorem slotFiber_card (p : KernelIndex v) :
    Fintype.card (SlotFiber H p) = multiplicity H p := by
  classical
  rw [Fintype.card_subtype]
  have hc := Fin.card_filter_univ_eq_vector_get_eq_count p
    (List.Vector.ofFn (kernelEdgeAt H))
  have hc' : (Finset.univ.filter (fun t : Fin (v + r) => kernelEdgeAt H t = p)).card =
      @List.count (KernelIndex v) (instBEqOfDecidableEq) p (orderedKernelEdges H) := by
    simpa only [List.Vector.get_ofFn, List.Vector.toList_ofFn,
      ofFn_kernelEdgeAt] using! hc
  rw [hc']
  change @List.count (KernelIndex v) (instBEqOfDecidableEq) p
    (orderedKernelEdges H) = H.1.count p
  rw [← Multiset.coe_count, coe_orderedKernelEdges]
  rfl

/-- The standard `Fin m` of a parallel class is exactly its decoder fiber. -/
def slotFiberEquiv (p : KernelIndex v) :
    Fin (multiplicity H p) ≃ SlotFiber H p :=
  (finCongr (slotFiber_card H p).symm).trans
    (Fintype.equivFin (SlotFiber H p)).symm

/-- The endpoint and the position within its fiber determine a slot. -/
def slotSigmaEquiv :
    Fin (v + r) ≃ (Σ p : KernelIndex v, SlotFiber H p) where
  toFun t := ⟨kernelEdgeAt H t, ⟨t, rfl⟩⟩
  invFun s := s.2.1
  left_inv _ := rfl
  right_inv := by
    rintro ⟨p, ⟨t, ht⟩⟩
    cases ht
    rfl

/-- Apply every parallel-class permutation in its own endpoint fiber. -/
def fiberAction
    (σ : (p : KernelIndex v) → Equiv.Perm (Fin (multiplicity H p))) :
    (Σ p : KernelIndex v, SlotFiber H p) ≃
      (Σ p : KernelIndex v, SlotFiber H p) :=
  Equiv.sigmaCongrRight fun p =>
    ((slotFiberEquiv H p).symm.trans (σ p)).trans (slotFiberEquiv H p)

/-- The factorial choices act as an endpoint-preserving slot permutation. -/
def slotPerm
    (σ : (p : KernelIndex v) → Equiv.Perm (Fin (multiplicity H p))) :
    Equiv.Perm (Fin (v + r)) :=
  ((slotSigmaEquiv H).trans (fiberAction H σ)).trans (slotSigmaEquiv H).symm

theorem slotPerm_edge
    (σ : (p : KernelIndex v) → Equiv.Perm (Fin (multiplicity H p)))
    (t : Fin (v + r)) :
    kernelEdgeAt H (slotPerm H σ t) = kernelEdgeAt H t := by
  simpa [slotPerm, slotSigmaEquiv, fiberAction] using!
    ((slotFiberEquiv H (kernelEdgeAt H t))
      ((σ (kernelEdgeAt H t))
        ((slotFiberEquiv H (kernelEdgeAt H t)).symm ⟨t, rfl⟩))).2

/-- No nontrivial family of fiber permutations fixes every decoder slot. -/
theorem slotPerm_faithful : Function.Injective (slotPerm H) := by
  intro σ τ heq
  funext p
  apply Equiv.ext
  intro i
  let s : Σ q : KernelIndex v, SlotFiber H q :=
    ⟨p, slotFiberEquiv H p i⟩
  have hs := congrArg
    (fun q : Equiv.Perm (Fin (v + r)) =>
      (slotSigmaEquiv H) (q ((slotSigmaEquiv H).symm s))) heq
  have ha : fiberAction H σ s = fiberAction H τ s := by
    simpa only [slotPerm, Equiv.trans_apply, Equiv.apply_symm_apply,
      Equiv.symm_apply_apply] using! hs
  have hb : (slotFiberEquiv H p) (σ p i) =
      (slotFiberEquiv H p) (τ p i) := by
    have hh := (Sigma.mk.inj (show
      (⟨p, (slotFiberEquiv H p) (σ p i)⟩ :
        Σ q : KernelIndex v, SlotFiber H q) =
      ⟨p, (slotFiberEquiv H p) (τ p i)⟩ by
        simpa [s, fiberAction] using! ha)).2
    exact eq_of_heq hh
  exact (slotFiberEquiv H p).injective hb

/-- A pair type whose members are exactly the diagonal kernel indices. -/
abbrev LoopPair (v : ℕ) :=
  {p : KernelIndex v // p.1.1 = p.1.2}

/-- Decoder slots whose paths are closed. -/
abbrev LoopSlot :=
  {t : Fin (v + r) // (kernelEdgeAt H t).1.1 = (kernelEdgeAt H t).1.2}

/-- Splitting a loop slot by its diagonal endpoint pair. -/
def loopSigmaEquiv :
    LoopSlot H ≃ (Σ p : LoopPair v, SlotFiber H p.1) where
  toFun t := ⟨⟨kernelEdgeAt H t.1, t.2⟩, ⟨t.1, rfl⟩⟩
  invFun s := ⟨s.2.1, by rw [s.2.2]; exact s.1.2⟩
  left_inv t := by apply Subtype.ext; rfl
  right_inv := by
    rintro ⟨⟨p, hp⟩, ⟨t, ht⟩⟩
    cases ht
    rfl

/-- The loop bits have exactly one coordinate for each loop occurrence. -/
theorem loopSlot_card : Fintype.card (LoopSlot H) = loopCount H := by
  classical
  calc
    Fintype.card (LoopSlot H) =
        Fintype.card (Σ p : LoopPair v, SlotFiber H p.1) :=
      Fintype.card_congr (loopSigmaEquiv H)
    _ = ∑ p : LoopPair v, multiplicity H p.1 := by
      rw [Fintype.card_sigma]
      simp_rw [slotFiber_card H]
    _ = loopCount H := by
      unfold loopCount
      rw [← Finset.sum_subtype
        (Finset.univ.filter (fun p : KernelIndex v => p.1.1 = p.1.2))
        (by simp) (fun p : KernelIndex v => multiplicity H p)]
      simp only [Finset.sum_filter]

def loopSlotEquiv : Fin (loopCount H) ≃ LoopSlot H :=
  (finCongr (loopSlot_card H).symm).trans
    (Fintype.equivFin (LoopSlot H)).symm

/-- A loop bit is assigned to its unique canonical loop slot. -/
def loopBits (β : Fin (loopCount H) → Bool) (t : Fin (v + r)) : Bool :=
  if ht : (kernelEdgeAt H t).1.1 = (kernelEdgeAt H t).1.2 then
    β ((loopSlotEquiv H).symm ⟨t, ht⟩)
  else false

theorem loopBits_apply (β : Fin (loopCount H) → Bool)
    (i : Fin (loopCount H)) :
    loopBits H β (loopSlotEquiv H i).1 = β i := by
  simp [loopBits, (loopSlotEquiv H i).2]

variable {k : ℕ} {G : Graph k} {C : ConnectedCoreIn G r}
variable (P : MaximalPathPartition C)

abbrev baseArray : KernelArray P.v.1 r := P.kernelChoice.1

/-- Transport the canonical fiber action to the paths' original labels. -/
def nativeSlotPerm
    (σ : (p : KernelIndex P.v.1) →
      Equiv.Perm (Fin (multiplicity (baseArray P) p))) :
    Equiv.Perm (Fin (P.v.1 + r)) :=
  (((occurrenceOrder P).symm.trans (slotPerm (baseArray P) σ)).trans
    (occurrenceOrder P))

theorem nativeSlotPerm_apply_order
    (σ : (p : KernelIndex P.v.1) →
      Equiv.Perm (Fin (multiplicity (baseArray P) p)))
    (t : Fin (P.v.1 + r)) :
    nativeSlotPerm P σ (occurrenceOrder P t) =
      occurrenceOrder P (slotPerm (baseArray P) σ t) := by
  simp [nativeSlotPerm]

theorem nativeSlotPerm_edge
    (σ : (p : KernelIndex P.v.1) →
      Equiv.Perm (Fin (multiplicity (baseArray P) p)))
    (t : Fin (P.v.1 + r)) :
    P.kernel.edge (nativeSlotPerm P σ t) = P.kernel.edge t := by
  have h := occurrenceOrder_edge P ((occurrenceOrder P).symm t)
  have h' := occurrenceOrder_edge P
    (slotPerm (baseArray P) σ ((occurrenceOrder P).symm t))
  calc
    P.kernel.edge (nativeSlotPerm P σ t) =
        kernelEdgeAt (baseArray P)
          (slotPerm (baseArray P) σ ((occurrenceOrder P).symm t)) := by
      simpa [nativeSlotPerm] using! h'
    _ = kernelEdgeAt (baseArray P) ((occurrenceOrder P).symm t) :=
      slotPerm_edge (baseArray P) σ _
    _ = P.kernel.edge t := by simpa using! h.symm

/-- Transport a loop bit from the canonical decoder slot to a native path. -/
def nativeLoopBits (β : Fin (loopCount (baseArray P)) → Bool)
    (u : Fin (P.v.1 + r)) : Bool :=
  loopBits (baseArray P) β ((occurrenceOrder P).symm u)

theorem nativeLoopBits_apply_order
    (β : Fin (loopCount (baseArray P)) → Bool)
    (t : Fin (P.v.1 + r)) :
    nativeLoopBits P β (occurrenceOrder P t) = loopBits (baseArray P) β t := by
  simp [nativeLoopBits]

/- The exact path partition selected by all fixed-label finite choices. -/
variable (hforest : ∀ S ∈ components (coreComplement C),
  isTree (coreComplement C) S ∧ (S ∩ coreLabels C).card = 1)

/- Present the same graph after every fixed-label occurrence and loop choice. -/
end Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_ChoiceIndexing


/-!
# Branch relabelling of exact kernel presentations

A branch permutation changes both the triangular kernel array and the
orientation of a path whose newly sorted endpoints occur in the opposite
order.  This file transports the occurrence kernel and its exact path
partition together.  The existing presentation theorem then supplies the
decoder inverse for every relabelled branch order.
-/

open scoped BigOperators Sym2
noncomputable section

namespace Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_ChoiceRelabel

open Erdos745.WrapUp
open Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_Mass
open Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_Occurrences
open Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_EdgeLabelled
open Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_PathPartition
open Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_CoreConnected
open Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_CoreForest
open Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_Presentation
open Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_Encode
open Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_ChoiceFreeness
open Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_ChoiceIndexing

attribute [local instance] Classical.propDecidable

variable {v r : ℕ}

/-- The action of a vertex permutation on unordered endpoint pairs. -/
def sym2Relabel (π : Equiv.Perm (Fin v)) : Equiv.Perm (Sym2 (Fin v)) where
  toFun := Sym2.map π.symm
  invFun := Sym2.map π
  left_inv := by
    intro x
    induction x using Sym2.ind with
    | _ a b => simp
  right_inv := by
    intro x
    induction x using Sym2.ind with
    | _ a b => simp

/-- New branch labels are mapped back to the original labels by `π`.
The symmetric pair is sorted again after this change of labels. -/
def indexRelabel (π : Equiv.Perm (Fin v)) : Equiv.Perm (KernelIndex v) :=
  Sym2.sortEquiv.symm.trans (sym2Relabel π) |>.trans Sym2.sortEquiv

theorem indexRelabel_sym2 (π : Equiv.Perm (Fin v)) (p : KernelIndex v) :
    Sym2.sortEquiv.symm (indexRelabel π p) =
      s(π.symm p.1.1, π.symm p.1.2) := by
  simp [indexRelabel, sym2Relabel, Sym2.sortEquiv_symm_apply]

theorem indexRelabel_apply (π : Equiv.Perm (Fin v)) (p : KernelIndex v) :
    indexRelabel π p =
      if h : π.symm p.1.1 ≤ π.symm p.1.2 then
        ⟨(π.symm p.1.1, π.symm p.1.2), h⟩
      else ⟨(π.symm p.1.2, π.symm p.1.1), le_of_not_ge h⟩ := by
  apply Sym2.sortEquiv.symm.injective
  rw [indexRelabel_sym2]
  by_cases h : π.symm p.1.1 ≤ π.symm p.1.2
  · simp [h, Sym2.sortEquiv_symm_apply]
  · simp [h, Sym2.sortEquiv_symm_apply, Sym2.eq_swap]

theorem indexRelabel_loop (π : Equiv.Perm (Fin v)) (p : KernelIndex v) :
    (indexRelabel π p).1.1 = (indexRelabel π p).1.2 ↔
      p.1.1 = p.1.2 := by
  rw [indexRelabel_apply]
  split_ifs <;> simp [π.symm.injective.eq_iff, eq_comm]

theorem incidence_indexRelabel (π : Equiv.Perm (Fin v))
    (i : Fin v) (p : KernelIndex v) :
    incidence i (indexRelabel π p) = incidence (π i) p := by
  simp only [indexRelabel_apply]
  split_ifs <;>
    simp [incidence, Equiv.apply_eq_iff_eq_symm_apply, Nat.add_comm]

theorem occurrenceAdj_indexRelabel (π : Equiv.Perm (Fin v))
    (edge : Fin (v + r) → KernelIndex v) (i j : Fin v) :
    occurrenceAdj (fun t => indexRelabel π (edge t)) i j ↔
      occurrenceAdj edge (π i) (π j) := by
  unfold occurrenceAdj
  constructor
  · rintro ⟨hij, t, ht⟩
    refine ⟨π.injective.ne hij, t, ?_⟩
    change (indexRelabel π (edge t)).1.1 = i ∧
      (indexRelabel π (edge t)).1.2 = j ∨
      (indexRelabel π (edge t)).1.1 = j ∧
      (indexRelabel π (edge t)).1.2 = i at ht
    rw [indexRelabel_apply] at ht
    by_cases h : π.symm (edge t).1.1 ≤ π.symm (edge t).1.2
    · simp only [dif_pos h] at ht
      rcases ht with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · exact Or.inl ⟨by simpa using! congrArg π ha, by simpa using congrArg π hb⟩
      · exact Or.inr ⟨by simpa using! congrArg π ha, by simpa using congrArg π hb⟩
    · simp only [dif_neg h] at ht
      rcases ht with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · exact Or.inr ⟨by simpa using! congrArg π hb, by simpa using congrArg π ha⟩
      · exact Or.inl ⟨by simpa using! congrArg π hb, by simpa using congrArg π ha⟩
  · rintro ⟨hij, t, ht⟩
    refine ⟨fun h => hij (congrArg π h), t, ?_⟩
    change (indexRelabel π (edge t)).1.1 = i ∧
      (indexRelabel π (edge t)).1.2 = j ∨
      (indexRelabel π (edge t)).1.1 = j ∧
      (indexRelabel π (edge t)).1.2 = i
    rw [indexRelabel_apply]
    by_cases h : π.symm (edge t).1.1 ≤ π.symm (edge t).1.2
    · simp only [dif_pos h]
      rcases ht with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · exact Or.inl ⟨by simpa using! congrArg π.symm ha,
          by simpa using! congrArg π.symm hb⟩
      · exact Or.inr ⟨by simpa using! congrArg π.symm ha,
          by simpa using! congrArg π.symm hb⟩
    · simp only [dif_neg h]
      rcases ht with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · exact Or.inr ⟨by simpa using! congrArg π.symm hb,
          by simpa using! congrArg π.symm ha⟩
      · exact Or.inl ⟨by simpa using! congrArg π.symm hb,
          by simpa using! congrArg π.symm ha⟩

/-- Relabelling every occurrence preserves connectivity and minimum degree. -/
def relabelKernel (K : OccurrenceKernel v r)
    (π : Equiv.Perm (Fin v)) : OccurrenceKernel v r where
  edge := fun t => indexRelabel π (K.edge t)
  connected := by
    intro i j
    have h := Relation.ReflTransGen.lift π.symm
      (fun a b hab =>
        (occurrenceAdj_indexRelabel π K.edge (π.symm a) (π.symm b)).2
          (by simpa using! hab)) (π i) (π j) (K.connected (π i) (π j))
    simpa [Function.onFun] using! h
  minDegree := by
    intro i
    simpa only [incidence_indexRelabel] using! K.minDegree (π i)

theorem relabelKernel_array (K : OccurrenceKernel v r)
    (π : Equiv.Perm (Fin v)) :
    (relabelKernel K π).array = Sym.map (indexRelabel π) K.array := by
  apply Subtype.ext
  simp [OccurrenceKernel.array, relabelKernel, arrayOfOccurrences,
    List.map_ofFn, Function.comp_def]

theorem multiplicity_relabelKernel (K : OccurrenceKernel v r)
    (π : Equiv.Perm (Fin v)) (p : KernelIndex v) :
    multiplicity (relabelKernel K π).array (indexRelabel π p) =
      multiplicity K.array p := by
  rw [relabelKernel_array]
  change (Sym.map (indexRelabel π) K.array).1.count (indexRelabel π p) =
    K.array.1.count p
  simpa only [Sym.coe_map] using!
    (Multiset.count_map_eq_count' (indexRelabel π) K.array.1
      (indexRelabel π).injective p)

theorem kernelWeight_relabelKernel (K : OccurrenceKernel v r)
    (π : Equiv.Perm (Fin v)) :
    kernelWeight (relabelKernel K π).array = kernelWeight K.array := by
  classical
  rw [kernelWeight_eq_compensation, kernelWeight_eq_compensation]
  symm
  apply Finset.prod_equiv (indexRelabel π) (by simp)
  intro p hp
  rw [multiplicity_relabelKernel]
  simp only [indexRelabel_loop]

variable {k : ℕ} {G : Graph k} {C : ConnectedCoreIn G r}
variable (P : MaximalPathPartition C)

/-- A relabelled branch index selects the old branch `π i`. -/
def relabelBranch (π : Equiv.Perm (Fin P.v.1)) : Fin P.v.1 ↪ Fin C.v :=
  π.toEmbedding.trans P.branch

theorem relabelBranch_image (π : Equiv.Perm (Fin P.v.1)) :
    Finset.univ.image (relabelBranch P π) = branchVertices C.graph := by
  rw [← P.branch_image]
  ext x
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨π i, rfl⟩
  · rintro ⟨i, hi⟩
    exact ⟨π.symm i, by simpa [relabelBranch] using! hi⟩

/-- The path with old sorted endpoints is reversed exactly when its new
endpoint labels have the opposite sorted order. -/
def relabelWalk (π : Equiv.Perm (Fin P.v.1))
    (t : Fin (P.v.1 + r)) :
    C.graph.Walk
      (relabelBranch P π ((indexRelabel π (P.kernel.edge t)).1.1))
      (relabelBranch P π ((indexRelabel π (P.kernel.edge t)).1.2)) :=
  if h : π.symm (P.kernel.edge t).1.1 ≤ π.symm (P.kernel.edge t).1.2 then
    (P.walk t).copy
      (by simp [relabelBranch, indexRelabel_apply, h])
      (by simp [relabelBranch, indexRelabel_apply, h])
  else
    (P.walk t).reverse.copy
      (by simp [relabelBranch, indexRelabel_apply, h])
      (by simp [relabelBranch, indexRelabel_apply, h])

theorem relabelWalk_edges (π : Equiv.Perm (Fin P.v.1))
    (t : Fin (P.v.1 + r)) :
    ((relabelWalk P π t).edges : Multiset (Sym2 (Fin C.v))) =
      (P.walk t).edges := by
  unfold relabelWalk
  split_ifs <;> simp [SimpleGraph.Walk.edges_copy, SimpleGraph.Walk.edges_reverse]

theorem relabelWalk_internal (π : Equiv.Perm (Fin P.v.1))
    (t : Fin (P.v.1 + r)) :
    (walkInternal (relabelWalk P π t) : Multiset (Fin C.v)) =
      walkInternal (P.walk t) := by
  unfold relabelWalk
  split_ifs
  · simp only [walkInternal, SimpleGraph.Walk.support_copy]
  · simp only [walkInternal, SimpleGraph.Walk.support_copy]
    change ((walkInternal ((P.walk t).reverse) : List (Fin C.v)) :
      Multiset (Fin C.v)) = walkInternal (P.walk t)
    rw [walkInternal_reverse]
    exact Multiset.coe_reverse _

theorem relabelWalk_length (π : Equiv.Perm (Fin P.v.1))
    (t : Fin (P.v.1 + r)) :
    (relabelWalk P π t).length = (P.walk t).length := by
  unfold relabelWalk
  split_ifs <;> simp

theorem relabelWalk_trail (π : Equiv.Perm (Fin P.v.1))
    (t : Fin (P.v.1 + r)) :
    (relabelWalk P π t).IsTrail := by
  rw [SimpleGraph.Walk.isTrail_def]
  change Multiset.Nodup
    ((relabelWalk P π t).edges : Multiset (Sym2 (Fin C.v)))
  rw [relabelWalk_edges]
  exact (P.trail t).edges_nodup

/-- Relabelling branches preserves every exact path-partition invariant. -/
def relabelPartition (π : Equiv.Perm (Fin P.v.1)) :
    MaximalPathPartition C where
  v := P.v
  branch := relabelBranch P π
  branch_image := relabelBranch_image P π
  kernel := relabelKernel P.kernel π
  walk := relabelWalk P π
  trail := relabelWalk_trail P π
  positive t := by
    change 0 < (relabelWalk P π t).length
    rw [relabelWalk_length]
    exact P.positive t
  internal_degree_two t x hx := by
    have h := relabelWalk_internal P π t
    apply P.internal_degree_two t x
    change x ∈ (walkInternal (P.walk t) : Multiset _)
    rw [← h]
    exact hx
  edge_partition := by
    change (∑ t : Fin (P.v.1 + r),
      ((relabelWalk P π t).edges : Multiset (Sym2 (Fin C.v)))) =
        C.graph.edgeFinset.1
    simp_rw [relabelWalk_edges]
    exact P.edge_partition
  internal_partition := by
    change (∑ t : Fin (P.v.1 + r),
      (walkInternal (relabelWalk P π t) : Multiset (Fin C.v))) =
        (Finset.univ \ branchVertices C.graph).1
    simp_rw [relabelWalk_internal]
    exact P.internal_partition
  loop_internal_two t ht := by
    have ht' : (P.kernel.edge t).1.1 = (P.kernel.edge t).1.2 :=
      (indexRelabel_loop π (P.kernel.edge t)).1 ht
    have h := congrArg Multiset.card (relabelWalk_internal P π t)
    simp only [Multiset.coe_card] at h
    exact h.symm ▸ P.loop_internal_two t ht'

theorem relabelPartition_kernelWeight
    (π : Equiv.Perm (Fin P.v.1)) :
    kernelWeight (relabelPartition P π).kernelChoice.1 =
      kernelWeight P.kernelChoice.1 :=
  kernelWeight_relabelKernel P.kernel π

variable (hforest : ∀ S ∈ components (coreComplement C),
  isTree (coreComplement C) S ∧ (S ∩ coreLabels C).card = 1)

/- Every branch relabelling has an exact semantic presentation. -/
end Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_ChoiceRelabel


/-!
# The complete free family of exact kernel presentations

Branch labels, parallel occurrences, and loop orientations act on one fixed
maximal-path partition.  The native occurrence labels survive a branch
relabelling, so the parallel action and loop bits can be applied to that
relabelled partition without choosing a second matching of decoder slots.
The ordered roots and lengths recover all three choices.
-/

open scoped BigOperators Sym2
noncomputable section

namespace Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_ChoiceFamily

open Erdos745.WrapUp
open Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_Mass
open Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_Occurrences
open Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_Expansion
open Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_Suppression
open Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_CoreConnected
open Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_CoreForest
open Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_PathPartition
open Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_Presentation
open Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_ChoiceFreeness
open Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_ChoiceArrangement
open Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_ChoiceIndexing
open Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_ChoiceRelabel
open Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_Encode
open Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_KernelAssembly

attribute [local instance] Classical.propDecidable

variable {k r : ℕ} {G : Graph k} {C : ConnectedCoreIn G r}

/-- The endpoint pair and internal multiset identify one native path. -/
theorem path_eq_of_internal_multiset (P : MaximalPathPartition C)
    (t u : Fin (P.v.1 + r))
    (hedge : P.kernel.edge t = P.kernel.edge u)
    (hblock : (walkInternal (P.walk t) : Multiset (Fin C.v)) =
      (walkInternal (P.walk u) : Multiset (Fin C.v))) : t = u := by
  by_cases he : walkInternal (P.walk t) = []
  · have hu : walkInternal (P.walk u) = [] := by
      apply (Multiset.coe_eq_zero _).mp
      rw [← hblock, he]
      rfl
    apply path_signature_injective P
    exact Prod.ext hedge (by change walkInternal (P.walk t) = walkInternal (P.walk u); exact he.trans hu.symm)
  · obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ he
    apply path_eq_of_shared_internal P t u x hx
    have hx' : x ∈ (walkInternal (P.walk u) : Multiset (Fin C.v)) := by
      rw [← hblock]
      exact hx
    exact hx'

/-- Equality of semantic lengths and roots gives literal equality of all
ordered path blocks in two arrangements of the same partition. -/
theorem arranged_blocks_eq_of_data (P : MaximalPathPartition C)
    (hforest : ∀ S ∈ components (coreComplement C),
      isTree (coreComplement C) S ∧ (S ∩ coreLabels C).card = 1)
    (q₁ q₂ : Equiv.Perm (Fin (P.v.1 + r)))
    (hq₁ : ∀ t, P.kernel.edge (q₁ t) = P.kernel.edge t)
    (hq₂ : ∀ t, P.kernel.edge (q₂ t) = P.kernel.edge t)
    (b₁ b₂ : Fin (P.v.1 + r) → Bool)
    (hdata : ((arrangedPresentation P hforest q₁ hq₁ b₁).lengths,
        (arrangedPresentation P hforest q₁ hq₁ b₁).roots) =
      ((arrangedPresentation P hforest q₂ hq₂ b₂).lengths,
        (arrangedPresentation P hforest q₂ hq₂ b₂).roots)) :
    ∀ t, internalBlock (arrangedPartition P q₁ hq₁ b₁) t =
      internalBlock (arrangedPartition P q₂ hq₂ b₂) t := by
  have hcode :
      Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_Decode.codeInternalBlocks
          (arrangedPresentation P hforest q₁ hq₁ b₁).code =
        Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_Decode.codeInternalBlocks
          (arrangedPresentation P hforest q₂ hq₂ b₂).code := by
    have hlen := congrArg Prod.fst hdata
    have hroots := congrArg Prod.snd hdata
    change (arrangedPresentation P hforest q₁ hq₁ b₁).lengths =
      (arrangedPresentation P hforest q₂ hq₂ b₂).lengths at hlen
    change (arrangedPresentation P hforest q₁ hq₁ b₁).roots =
      (arrangedPresentation P hforest q₂ hq₂ b₂).roots at hroots
    rw [ExpansionPresentation.codeInternalBlocks_code,
      ExpansionPresentation.codeInternalBlocks_code, hlen, hroots]
  change Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_Decode.codeInternalBlocks
      (presentation (arrangedPartition P q₁ hq₁ b₁) hforest).code =
    Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_Decode.codeInternalBlocks
      (presentation (arrangedPartition P q₂ hq₂ b₂) hforest).code at hcode
  rw [presentation_internalBlocks, presentation_internalBlocks] at hcode
  have hfun := List.ofFn_injective hcode
  intro t
  exact (List.map_injective_iff.mpr C.labels.injective) (congrFun hfun t)

/-- The observable data first recovers the parallel-occurrence permutation,
then every loop orientation bit. -/
theorem arranged_data_faithful (P : MaximalPathPartition C)
    (hforest : ∀ S ∈ components (coreComplement C),
      isTree (coreComplement C) S ∧ (S ∩ coreLabels C).card = 1)
    (q₁ q₂ : Equiv.Perm (Fin (P.v.1 + r)))
    (hq₁ : ∀ t, P.kernel.edge (q₁ t) = P.kernel.edge t)
    (hq₂ : ∀ t, P.kernel.edge (q₂ t) = P.kernel.edge t)
    (b₁ b₂ : Fin (P.v.1 + r) → Bool)
    (hdata : ((arrangedPresentation P hforest q₁ hq₁ b₁).lengths,
        (arrangedPresentation P hforest q₁ hq₁ b₁).roots) =
      ((arrangedPresentation P hforest q₂ hq₂ b₂).lengths,
        (arrangedPresentation P hforest q₂ hq₂ b₂).roots)) :
    q₁ = q₂ ∧ ∀ u, (P.kernel.edge u).1.1 = (P.kernel.edge u).1.2 →
      b₁ u = b₂ u := by
  have hblocks := arranged_blocks_eq_of_data P hforest q₁ q₂ hq₁ hq₂ b₁ b₂ hdata
  have horder₁ : occurrenceOrder (arrangedPartition P q₁ hq₁ b₁) =
      occurrenceOrder P := rfl
  have horder₂ : occurrenceOrder (arrangedPartition P q₂ hq₂ b₂) =
      occurrenceOrder P := rfl
  have hblocks' (t : Fin (P.v.1 + r)) :
      walkInternal (arrangedWalk P q₁ hq₁ b₁ (occurrenceOrder P t)) =
        walkInternal (arrangedWalk P q₂ hq₂ b₂ (occurrenceOrder P t)) := by
    have hb := hblocks t
    change walkInternal
        ((arrangedPartition P q₁ hq₁ b₁).walk
          (occurrenceOrder (arrangedPartition P q₁ hq₁ b₁) t)) =
      walkInternal
        ((arrangedPartition P q₂ hq₂ b₂).walk
          (occurrenceOrder (arrangedPartition P q₂ hq₂ b₂) t)) at hb
    rw [horder₁, horder₂] at hb
    exact hb
  have hq : q₁ = q₂ := by
    apply Equiv.ext
    intro u
    obtain ⟨t, rfl⟩ := (occurrenceOrder P).surjective u
    have hm := congrArg (fun xs : List (Fin C.v) =>
      (xs : Multiset (Fin C.v))) (hblocks' t)
    have hm' : (walkInternal (P.walk (q₁ (occurrenceOrder P t))) :
        Multiset (Fin C.v)) =
        (walkInternal (P.walk (q₂ (occurrenceOrder P t))) :
          Multiset (Fin C.v)) := by
      change (walkInternal (arrangedWalk P q₁ hq₁ b₁
          (occurrenceOrder P t)) : Multiset (Fin C.v)) =
        (walkInternal (arrangedWalk P q₂ hq₂ b₂
          (occurrenceOrder P t)) : Multiset (Fin C.v)) at hm
      rw [arrangedWalk_internal, arrangedWalk_internal] at hm
      exact hm
    exact path_eq_of_internal_multiset P
      (q₁ (occurrenceOrder P t)) (q₂ (occurrenceOrder P t))
      ((hq₁ _).trans (hq₂ _).symm) hm'
  refine ⟨hq, ?_⟩
  intro u hloop
  obtain ⟨t, rfl⟩ := (occurrenceOrder P).surjective u
  subst q₂
  have hb' := hblocks' t
  rw [arrangedWalk_internalList, arrangedWalk_internalList] at hb'
  have hloop' : (P.kernel.edge (q₁ (occurrenceOrder P t))).1.1 =
      (P.kernel.edge (q₁ (occurrenceOrder P t))).1.2 := by
    rw [hq₁ (occurrenceOrder P t)]
    exact hloop
  simp only [if_pos hloop'] at hb'
  have hne := loop_internal_reverse_ne P (q₁ (occurrenceOrder P t)) hloop'
  cases hb₁ : b₁ (occurrenceOrder P t) <;>
    cases hb₂ : b₂ (occurrenceOrder P t)
  · rfl
  · have hh : walkInternal (P.walk (q₁ (occurrenceOrder P t))) =
        (walkInternal (P.walk (q₁ (occurrenceOrder P t)))).reverse := by
      simpa [hb₁, hb₂] using! hb'
    exact False.elim (hne hh)
  · have hh : walkInternal (P.walk (q₁ (occurrenceOrder P t))) =
        (walkInternal (P.walk (q₁ (occurrenceOrder P t)))).reverse := by
      simpa [hb₁, hb₂] using! hb'.symm
    exact False.elim (hne hh)
  · rfl

variable (P : MaximalPathPartition C)

/-- Relabelling the branch endpoints preserves the native parallel action. -/
theorem relabel_nativeSlotPerm_edge (π : Equiv.Perm (Fin P.v.1))
    (σ : (p : KernelIndex P.v.1) →
      Equiv.Perm (Fin (multiplicity (baseArray P) p)))
    (u : Fin (P.v.1 + r)) :
    (relabelPartition P π).kernel.edge (nativeSlotPerm P σ u) =
      (relabelPartition P π).kernel.edge u := by
  exact congrArg (indexRelabel π) (nativeSlotPerm_edge P σ u)

/-- A complete choice acts on the relabelled native partition. -/
def choicePartition (π : Equiv.Perm (Fin P.v.1))
    (β : Fin (loopCount (baseArray P)) → Bool)
    (σ : (p : KernelIndex P.v.1) →
      Equiv.Perm (Fin (multiplicity (baseArray P) p))) :
    MaximalPathPartition C :=
  arrangedPartition (relabelPartition P π) (nativeSlotPerm P σ)
    (relabel_nativeSlotPerm_edge P π σ) (nativeLoopBits P β)

variable (hforest : ∀ S ∈ components (coreComplement C),
  isTree (coreComplement C) S ∧ (S ∩ coreLabels C).card = 1)

/-- Exact expansion presentation for all three finite choices. -/
def choicePresentation (s : SymmetryChoices (baseArray P)) :
    ExpansionPresentation k r P.v (treeCount P) :=
  arrangedPresentation (relabelPartition P s.1) hforest
    (nativeSlotPerm P s.2.2)
    (relabel_nativeSlotPerm_edge P s.1 s.2.2)
    (nativeLoopBits P s.2.1)

theorem choicePresentation_decode (s : SymmetryChoices (baseArray P)) :
    Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_Decode.decodeExpansionCode
      (choicePresentation P hforest s).code = G :=
  arrangedPresentation_decode (relabelPartition P s.1) hforest _ _ _

theorem choicePresentation_kernelWeight
    (s : SymmetryChoices (baseArray P)) :
    kernelWeight (choicePresentation P hforest s).H.1 =
      kernelWeight (baseArray P) := by
  exact (arrangedPresentation_kernelWeight
    (relabelPartition P s.1) hforest _ _ _).trans
      (relabelPartition_kernelWeight P s.1)

/-- The first `v` roots display the chosen branch permutation. -/
theorem choicePresentation_branchRoot
    (s : SymmetryChoices (baseArray P)) (i : Fin P.v.1) :
    (choicePresentation P hforest s).roots
      (Fin.castLE (branch_le_core P) i) = C.labels (P.branch (s.1 i)) := by
  exact roots_branch (choicePartition P s.1 s.2.1 s.2.2) i

/-- The action of the factorial parallel choices on native paths is faithful. -/
theorem nativeSlotPerm_faithful :
    Function.Injective (nativeSlotPerm P) := by
  intro σ τ h
  apply slotPerm_faithful (baseArray P)
  apply Equiv.ext
  intro t
  have ht := congrArg
    (fun q : Equiv.Perm (Fin (P.v.1 + r)) => q (occurrenceOrder P t)) h
  change nativeSlotPerm P σ (occurrenceOrder P t) =
    nativeSlotPerm P τ (occurrenceOrder P t) at ht
  rw [nativeSlotPerm_apply_order, nativeSlotPerm_apply_order] at ht
  exact (occurrenceOrder P).injective ht

/-- Canonical loop bits remain faithful after transport to native slots. -/
theorem nativeLoopBits_eq_of_relabelled_loops
    (π : Equiv.Perm (Fin P.v.1))
    (β γ : Fin (loopCount (baseArray P)) → Bool)
    (h : ∀ u, ((relabelPartition P π).kernel.edge u).1.1 =
      ((relabelPartition P π).kernel.edge u).1.2 →
      nativeLoopBits P β u = nativeLoopBits P γ u) : β = γ := by
  funext i
  let t := (loopSlotEquiv (baseArray P) i).1
  let u := occurrenceOrder P t
  have ht : (kernelEdgeAt (baseArray P) t).1.1 =
      (kernelEdgeAt (baseArray P) t).1.2 :=
    (loopSlotEquiv (baseArray P) i).2
  have hu : (P.kernel.edge u).1.1 = (P.kernel.edge u).1.2 := by
    rw [occurrenceOrder_edge P]
    exact ht
  have hnew : ((relabelPartition P π).kernel.edge u).1.1 =
      ((relabelPartition P π).kernel.edge u).1.2 :=
    (indexRelabel_loop π (P.kernel.edge u)).2 hu
  have hb := h u hnew
  change nativeLoopBits P β (occurrenceOrder P t) =
    nativeLoopBits P γ (occurrenceOrder P t) at hb
  rw [nativeLoopBits_apply_order, nativeLoopBits_apply_order] at hb
  change loopBits (baseArray P) β (loopSlotEquiv (baseArray P) i).1 =
    loopBits (baseArray P) γ (loopSlotEquiv (baseArray P) i).1 at hb
  simpa only [loopBits_apply] using! hb

/-- The joint length/root observable recovers branch labels, all parallel
occurrences, and all independent loop orientations. -/
theorem choicePresentation_data_injective : Function.Injective
    (fun s : SymmetryChoices (baseArray P) =>
      ((choicePresentation P hforest s).lengths,
        (choicePresentation P hforest s).roots)) := by
  intro s t hdata
  change ((choicePresentation P hforest s).lengths,
      (choicePresentation P hforest s).roots) =
    ((choicePresentation P hforest t).lengths,
      (choicePresentation P hforest t).roots) at hdata
  have hπ : s.1 = t.1 := by
    apply Equiv.ext
    intro i
    have hi := congrArg
      (fun f : Fin C.v ↪ Fin k => f (Fin.castLE (branch_le_core P) i))
      (congrArg Prod.snd hdata)
    change (choicePresentation P hforest s).roots
        (Fin.castLE (branch_le_core P) i) =
      (choicePresentation P hforest t).roots
        (Fin.castLE (branch_le_core P) i) at hi
    rw [choicePresentation_branchRoot, choicePresentation_branchRoot] at hi
    exact P.branch.injective (C.labels.injective hi)
  rcases s with ⟨π, β, σ⟩
  rcases t with ⟨ρ, γ, τ⟩
  dsimp at hπ
  subst ρ
  have hdata' :
      ((arrangedPresentation (relabelPartition P π) hforest
          (nativeSlotPerm P σ) (relabel_nativeSlotPerm_edge P π σ)
          (nativeLoopBits P β)).lengths,
        (arrangedPresentation (relabelPartition P π) hforest
          (nativeSlotPerm P σ) (relabel_nativeSlotPerm_edge P π σ)
          (nativeLoopBits P β)).roots) =
      ((arrangedPresentation (relabelPartition P π) hforest
          (nativeSlotPerm P τ) (relabel_nativeSlotPerm_edge P π τ)
          (nativeLoopBits P γ)).lengths,
        (arrangedPresentation (relabelPartition P π) hforest
          (nativeSlotPerm P τ) (relabel_nativeSlotPerm_edge P π τ)
          (nativeLoopBits P γ)).roots) := by
    simpa only [choicePresentation] using! hdata
  obtain ⟨hq, hb⟩ := arranged_data_faithful (relabelPartition P π) hforest
    (nativeSlotPerm P σ) (nativeSlotPerm P τ)
    (relabel_nativeSlotPerm_edge P π σ)
    (relabel_nativeSlotPerm_edge P π τ)
    (nativeLoopBits P β) (nativeLoopBits P γ) hdata'
  have hσ : σ = τ := nativeSlotPerm_faithful P hq
  have hβ : β = γ := nativeLoopBits_eq_of_relabelled_loops P π β γ hb
  cases hσ
  cases hβ
  rfl

/-- Every positive-excess connected graph carries its complete free family. -/
theorem positiveExcessGraph_has_choicePresentationFamily {k r : ℕ}
    {G : Graph k} (hr : 0 < r)
    (hG : G ∈ positiveExcessGraphs k r) :
    Nonempty (ChoicePresentationFamily k r G) := by
  obtain ⟨C, ⟨P⟩⟩ := positiveExcessGraph_has_maximalPathPartition hr hG
  change G ∈ (fixedGraphs k (k + r)).filter
    (fun H => 0 < k ∧ ∀ u v : Fin k, reach H u v) at hG
  have hf := Finset.mem_filter.mp hG
  have hcard : G.card = k + r := (Finset.mem_filter.mp hf.1).2
  have hforest := coreComplement_isRootedForest C hf.2.2 hcard
  exact ⟨{
    v := P.v
    H := P.kernelChoice
    j := treeCount P
    presentation := choicePresentation P hforest
    data_injective := choicePresentation_data_injective P hforest
    decode_eq := choicePresentation_decode P hforest
    kernelWeight_eq := choicePresentation_kernelWeight P hforest
  }⟩

theorem choicePresentationFamilyStatement : ChoicePresentationFamilyStatement := by
  intro k r _hk hr G hG
  exact positiveExcessGraph_has_choicePresentationFamily hr hG

end Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_ChoiceFamily
