module

public import Erdos745.WrapUp.Proofs.Internal.Linked.W02_ExpansionCore
public import Mathlib.Data.Fintype.CardEmbedding
public import Mathlib.Logic.Equiv.Fintype
public import Mathlib.Data.Multiset.Fintype

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local simp] Pi.div_def Pi.mul_def Pi.add_def Pi.sub_def Pi.neg_def Pi.inv_def Function.comp_def Pi.pow_def Pi.smul_def Real.rpow_eq_pow

@[expose] public section


/-!
# Semantic ordered rooted forests for the kernel expansion

The integer `tau k j` is represented semantically by an ordered embedding of
the `j` roots into `Fin k`, together with a forest rooted at the canonical
`j`-element root set.  A later relabelling step transports the canonical
forest to the selected ordered roots.
-/

noncomputable section

namespace Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_Forest

open Erdos745.WrapUp
open Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_Expansion

private noncomputable def rootedForestsAt (k : ℕ) (roots : Finset (Fin k)) :
    Finset (Graph k) := by
  classical
  exact (allGraphs k).filter (fun G => ∀ S ∈ components G,
    isTree G S ∧ (S ∩ roots).card = 1)

/-- Forests on `Fin k` having exactly one root from `roots` in each component. -/
abbrev RootedForestAt (k : ℕ) (roots : Finset (Fin k)) :=
  ↥(rootedForestsAt k roots)

/-- Forests rooted at the canonical first `j` labels. -/
abbrev CanonicalRootedForest (k j : ℕ) :=
  RootedForestAt k (canonicalRoots k j)

/-- A semantic ordered-root presentation: the embedding selects and orders
the roots; the second factor is the canonical representative to be relabelled. -/
abbrev OrderedRootedForest (k j : ℕ) :=
  (Fin j ↪ Fin k) × CanonicalRootedForest k j

theorem card_canonicalRootedForest (k j : ℕ) :
    Fintype.card (CanonicalRootedForest k j) =
      rootedForestCount k (canonicalRoots k j) := by
  rw [Fintype.card_coe]
  rfl

private theorem card_rootEmbeddings (k j : ℕ) :
    Fintype.card (Fin j ↪ Fin k) = falling k j := by
  rw [Fintype.card_embedding_eq]
  simp [falling, Nat.descFactorial_eq_prod_range]

/-- The semantic presentation has exactly the coefficient `tau k j`. -/
theorem card_orderedRootedForest (k j : ℕ) :
    Fintype.card (OrderedRootedForest k j) = tau k j := by
  rw [Fintype.card_prod, card_rootEmbeddings, card_canonicalRootedForest]
  rfl

/-- Interpret the existing finite coefficient index as an ordered rooted
forest presentation. -/
noncomputable def finTauEquivOrderedRootedForest (k j : ℕ) :
    Fin (tau k j) ≃ OrderedRootedForest k j :=
  Fintype.equivOfCardEq (by
    rw [Fintype.card_fin, card_orderedRootedForest])

/-- The ordered roots selected by a coefficient index. -/
noncomputable def selectedRoots (k j : ℕ) (code : Fin (tau k j)) :
    Fin j ↪ Fin k :=
  (finTauEquivOrderedRootedForest k j code).1

/-- The canonical rooted forest selected by a coefficient index. -/
noncomputable def selectedCanonicalForest (k j : ℕ)
    (code : Fin (tau k j)) : CanonicalRootedForest k j :=
  (finTauEquivOrderedRootedForest k j code).2

/- Membership facts carried by the selected canonical forest. -/
end Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_Forest


/-!
# Label transport for semantic kernel-expansion data

This module extends an ordered root embedding to a permutation of all vertex
labels and transports the canonical rooted forest through that permutation.
Edges are normalized back to the increasing-pair representation used by
`Erdos745.WrapUp.Edge`.
-/

noncomputable section

namespace Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_Relabel

open Erdos745.WrapUp
open Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_Expansion
open Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_Forest

private theorem rootEmbedding_card_le {k j : ℕ} (roots : Fin j ↪ Fin k) :
    j ≤ k := by
  simpa using! Fintype.card_le_of_embedding roots

/-- The canonical first-`j` root set is equivalent to `Fin j`. -/
def canonicalRootEquiv (k j : ℕ) (hjk : j ≤ k) :
    {x : Fin k // x ∈ canonicalRoots k j} ≃ Fin j where
  toFun x := ⟨x.1.1, by
    have hx := Finset.mem_filter.mp x.2
    exact hx.2⟩
  invFun i := ⟨Fin.castLE hjk i, by
    simp [canonicalRoots, Fin.castLE]⟩
  left_inv x := by
    apply Subtype.ext
    rfl
  right_inv i := by
    apply Fin.ext
    rfl

private noncomputable def rootSubtypeEquiv {k j : ℕ} (roots : Fin j ↪ Fin k) :
    {x : Fin k // x ∈ canonicalRoots k j} ≃
      {x : Fin k // x ∈ Set.range roots} :=
  (canonicalRootEquiv k j (rootEmbedding_card_le roots)).trans roots.toEquivRange

/-- A permutation extending the selected ordered-root embedding. -/
noncomputable def rootPermutation {k j : ℕ} (roots : Fin j ↪ Fin k) :
    Equiv.Perm (Fin k) := by
  classical
  exact Equiv.extendSubtype (rootSubtypeEquiv roots)

/-- The extension agrees with the selected embedding on every canonical root. -/
theorem rootPermutation_apply_castLE {k j : ℕ} (roots : Fin j ↪ Fin k)
    (i : Fin j) :
    rootPermutation roots (Fin.castLE (rootEmbedding_card_le roots) i) = roots i := by
  classical
  let x : Fin k := Fin.castLE (rootEmbedding_card_le roots) i
  have hx : x ∈ canonicalRoots k j := by
    simp [x, canonicalRoots, Fin.castLE]
  have h := Equiv.extendSubtype_apply_of_mem (rootSubtypeEquiv roots) x hx
  simpa [rootPermutation, rootSubtypeEquiv, canonicalRootEquiv, x] using! h

/-- Relabel one simple edge and normalize its endpoint order. -/
def relabelEdge {k : ℕ} (p : Equiv.Perm (Fin k)) (e : Edge k) : Edge k := by
  let a := p e.1.1
  let b := p e.1.2
  by_cases hab : a < b
  · exact ⟨(a, b), hab⟩
  · have hne : a ≠ b := by
      intro h
      have := p.injective h
      exact (ne_of_lt e.2) this
    exact ⟨(b, a), lt_of_le_of_ne (le_of_not_gt hab) hne.symm⟩

/-- Relabel every edge of a graph.  Finite image automatically removes no
edge because a permutation is injective; the explicit cardinal proof is kept
for the later compensation boundary. -/
def relabelGraph {k : ℕ} (p : Equiv.Perm (Fin k)) (G : Graph k) : Graph k :=
  G.image (relabelEdge p)

/-- The canonical forest selected by a coefficient index, transported to its
selected ordered roots. -/
noncomputable def selectedForestGraph (k j : ℕ) (code : Fin (tau k j)) :
    Graph k :=
  relabelGraph (rootPermutation (selectedRoots k j code))
    (selectedCanonicalForest k j code).1

end Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_Relabel


/-!
# Canonically ordered kernel-edge occurrences

A kernel is stored as a symmetric-power multiset.  Path expansion instead
needs one ordered slot for each of its `v+r` edge occurrences.  Sorting the
finite index type supplies those slots without changing multiplicities.
-/

noncomputable section

namespace Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_Occurrences

open Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_Mass

/-- A fixed ordered list of kernel-edge occurrences. -/
def orderedKernelEdges {v r : ℕ} (H : KernelArray v r) : List (KernelIndex v) :=
  (H : Multiset (KernelIndex v)).toList

/-- Sorting preserves the underlying kernel multiset. -/
theorem coe_orderedKernelEdges {v r : ℕ} (H : KernelArray v r) :
    (orderedKernelEdges H : Multiset (KernelIndex v)) =
      (H : Multiset (KernelIndex v)) := by
  exact Multiset.coe_toList _

/-- There is one ordered slot for each of the `v+r` kernel edges. -/
theorem length_orderedKernelEdges {v r : ℕ} (H : KernelArray v r) :
    (orderedKernelEdges H).length = v + r := by
  rw [orderedKernelEdges, Multiset.length_toList]
  exact Sym.card_coe

/-- The kernel edge in an ordered occurrence slot. -/
def kernelEdgeAt {v r : ℕ} (H : KernelArray v r) (i : Fin (v + r)) :
    KernelIndex v :=
  (orderedKernelEdges H).get
    (Fin.cast (length_orderedKernelEdges H).symm i)

/-- Rebuilding the occurrence list from its indexed accessor is exact. -/
theorem ofFn_kernelEdgeAt {v r : ℕ} (H : KernelArray v r) :
    List.ofFn (kernelEdgeAt H) = orderedKernelEdges H := by
  apply List.ext_get
  · simp [length_orderedKernelEdges]
  · intro n hn₁ hn₂
    simp [kernelEdgeAt]

end Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_Occurrences
