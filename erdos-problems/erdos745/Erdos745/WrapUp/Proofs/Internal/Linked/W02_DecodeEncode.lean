module

public import Erdos745.WrapUp.Proofs.Internal.Linked.W02_Relabel
public import Erdos745.WrapUp.Proofs.Internal.Linked.W02_CoreForest
public import Erdos745.WrapUp.Proofs.Internal.Linked.W02_Paths

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local simp] Pi.div_def Pi.mul_def Pi.add_def Pi.sub_def Pi.neg_def Pi.inv_def Function.comp_def Pi.pow_def Pi.smul_def Real.rpow_eq_pow

@[expose] public section


/-!
# Total decoding of finite kernel-expansion codes

All finite majorant codes receive a graph value.  Invalid decorations are
allowed: self-pairs are discarded and repeated edges are deduplicated by the
target `Finset`.  The later fibre theorem restricts to the valid decorations
arising from suppression of a simple connected graph.
-/

noncomputable section

namespace Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_Decode

open Erdos745.WrapUp
open Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_Expansion
open Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_Composition
open Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_Forest
open Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_Relabel
open Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_Occurrences

/-- Split a list successively by a list of requested block lengths. -/
def splitBy {α : Type*} : List ℕ → List α → List (List α)
  | [], _ => []
  | n :: ns, xs => xs.take n :: splitBy ns (xs.drop n)

@[simp]
theorem length_splitBy {α : Type*} (ns : List ℕ) (xs : List α) :
    (splitBy ns xs).length = ns.length := by
  induction ns generalizing xs with
  | nil => rfl
  | cons n ns ih => simp [splitBy, ih]

def edgeBetween? {k : ℕ} (a b : Fin k) : Option (Edge k) := by
  by_cases hab : a < b
  · exact some ⟨(a, b), hab⟩
  · by_cases hba : b < a
    · exact some ⟨(b, a), hba⟩
    · exact none

/-- The simple edges traversed by consecutive vertices of a path or closed
walk. -/
def pathEdges {k : ℕ} (vertices : List (Fin k)) : Graph k :=
  ((vertices.zip vertices.tail).filterMap
    (fun ab => edgeBetween? ab.1 ab.2)).toFinset

/-- Weak-composition lengths attached to the ordered kernel occurrences. -/
noncomputable def codeLengths {k r : ℕ} (c : ExpansionCode k r) :
    Fin (c.1.1 + r) → ℕ :=
  let v := c.1.1
  let j := c.2.2.1.1
  let hv : 0 < v := (Finset.mem_Icc.mp c.1.2).1
  let hvj : v ≤ j := (Finset.mem_Icc.mp c.2.2.1.2).1
  expansionParts v r j hv hvj c.2.2.2.1

/-- Ordered labels which are not the first `v` kernel roots. -/
noncomputable def nonkernelLabels {k r : ℕ} (c : ExpansionCode k r) :
    List (Fin k) :=
  let v := c.1.1
  let j := c.2.2.1.1
  let roots := selectedRoots k j c.2.2.2.2
  (List.ofFn roots).drop v

/-- The ordered internal labels assigned to each kernel-edge occurrence. -/
noncomputable def codeInternalBlocks {k r : ℕ} (c : ExpansionCode k r) :
    List (List (Fin k)) :=
  splitBy (List.ofFn (codeLengths c)) (nonkernelLabels c)

theorem length_codeInternalBlocks {k r : ℕ} (c : ExpansionCode k r) :
    (codeInternalBlocks c).length = c.1.1 + r := by
  simp [codeInternalBlocks, length_splitBy]

/-- Label of a kernel vertex among the first `v` ordered roots. -/
noncomputable def kernelVertexLabel {k r : ℕ} (c : ExpansionCode k r)
    (i : Fin c.1.1) : Fin k :=
  let v := c.1.1
  let j := c.2.2.1.1
  let hvj : v ≤ j := (Finset.mem_Icc.mp c.2.2.1.2).1
  selectedRoots k j c.2.2.2.2 (Fin.castLE hvj i)

/-- Vertex list of one expanded kernel-edge occurrence. -/
noncomputable def occurrenceVertices {k r : ℕ} (c : ExpansionCode k r)
    (t : Fin (c.1.1 + r)) : List (Fin k) :=
  let H := c.2.1.1
  let edge := kernelEdgeAt H t
  let internal := (codeInternalBlocks c).get
    (Fin.cast (length_codeInternalBlocks c).symm t)
  kernelVertexLabel c edge.1.1 ::
    (internal ++ [kernelVertexLabel c edge.1.2])

/-- Simple graph made from all expanded kernel paths. -/
noncomputable def kernelPathGraph {k r : ℕ} (c : ExpansionCode k r) : Graph k :=
  Finset.univ.biUnion fun t : Fin (c.1.1 + r) =>
    pathEdges (occurrenceVertices c t)

/-- Total decoder for every finite expansion code. -/
noncomputable def decodeExpansionCode {k r : ℕ} (c : ExpansionCode k r) : Graph k :=
  selectedForestGraph k c.2.2.1.1 c.2.2.2.2 ∪ kernelPathGraph c

end Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_Decode


/-!
# Inverting the semantic rooted-forest coefficient

The core-complement theorem produces a rooted forest on the actual core
labels.  This module transports it through the permutation used by the
existing semantic `tau` decoder and takes the inverse of
`finTauEquivOrderedRootedForest`.  The result is an actual coefficient code,
not merely a cardinality assertion.
-/

open scoped Sym2

noncomputable section

namespace Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_ForestInverse

open Erdos745.WrapUp
open Erdos745.WrapUp.Proofs.Internal.W01_ENUM_Trees
open Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_Expansion
open Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_Forest
open Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_Relabel
open Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_CoreConnected
open Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_CoreForest

attribute [local instance] Classical.propDecidable

private def edgeSym2 {k : ℕ} (e : Edge k) : Sym2 (Fin k) :=
  s(e.1.1, e.1.2)

private theorem edgeSym2_injective {k : ℕ} :
    Function.Injective (@edgeSym2 k) := by
  intro e f hef
  apply Subtype.ext
  apply Prod.ext
  · rcases Sym2.eq_iff.mp hef with h | h
    · exact h.1
    · have hlt : f.1.2 < f.1.1 := by
        calc
          f.1.2 = e.1.1 := h.1.symm
          _ < e.1.2 := e.2
          _ = f.1.1 := h.2
      exact False.elim (lt_asymm f.2 hlt)
  · rcases Sym2.eq_iff.mp hef with h | h
    · exact h.2
    · have hlt : f.1.2 < f.1.1 := by
        calc
          f.1.2 = e.1.1 := h.1.symm
          _ < e.1.2 := e.2
          _ = f.1.1 := h.2
      exact False.elim (lt_asymm f.2 hlt)

private theorem edgeSym2_relabel {k : ℕ} (p : Equiv.Perm (Fin k))
    (e : Edge k) :
    edgeSym2 (relabelEdge p e) = p.toEmbedding.sym2Map (edgeSym2 e) := by
  by_cases h : p e.1.1 < p e.1.2
  · simp [relabelEdge, h, edgeSym2, Function.Embedding.sym2Map_apply]
  · simp [relabelEdge, h, edgeSym2, Function.Embedding.sym2Map_apply,
      Sym2.eq_swap]

theorem relabelEdge_injective {k : ℕ} (p : Equiv.Perm (Fin k)) :
    Function.Injective (relabelEdge p) := by
  intro e f h
  apply edgeSym2_injective
  apply p.toEmbedding.sym2Map.injective
  simpa [edgeSym2_relabel] using! congrArg edgeSym2 h

theorem card_relabelGraph {k : ℕ} (p : Equiv.Perm (Fin k)) (G : Graph k) :
    (relabelGraph p G).card = G.card := by
  unfold relabelGraph
  exact Finset.card_image_of_injective G (relabelEdge_injective p)

private theorem relabelEdge_endpoints {k : ℕ} (p : Equiv.Perm (Fin k))
    (e : Edge k) :
    ((relabelEdge p e).1.1 = p e.1.1 ∧
        (relabelEdge p e).1.2 = p e.1.2) ∨
      ((relabelEdge p e).1.1 = p e.1.2 ∧
        (relabelEdge p e).1.2 = p e.1.1) := by
  by_cases h : p e.1.1 < p e.1.2
  · simp [relabelEdge, h]
  · simp [relabelEdge, h]

private theorem reflTransGen_map {A B : Type*} {R : A → A → Prop}
    {S : B → B → Prop} (f : A → B)
    (hf : ∀ a b, R a b → S (f a) (f b)) {a b : A} :
    Relation.ReflTransGen R a b → Relation.ReflTransGen S (f a) (f b) := by
  intro h
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail hab hbc ih => exact ih.tail (hf _ _ hbc)

theorem adj_relabelGraph_iff {k : ℕ} (p : Equiv.Perm (Fin k))
    (G : Graph k) (x y : Fin k) :
    adj (relabelGraph p G) (p x) (p y) ↔ adj G x y := by
  constructor
  · rintro ⟨e', he', hends'⟩
    rw [relabelGraph, Finset.mem_image] at he'
    rcases he' with ⟨e, he, rfl⟩
    have hends := relabelEdge_endpoints p e
    refine ⟨e, he, ?_⟩
    rcases hends with h | h <;> rcases hends' with h' | h'
    all_goals
      apply Or.elim (em (e.1.1 = x))
      · intro hx
        left
        constructor
        · exact hx
        · apply p.injective
          aesop
      · intro hx
        right
        constructor <;> apply p.injective <;> aesop
  · rintro ⟨e, he, hends⟩
    refine ⟨relabelEdge p e, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨e, he, rfl⟩
    · have hp := relabelEdge_endpoints p e
      rcases hends with h | h <;> rcases hp with hp | hp
      all_goals aesop

private theorem reach_relabelGraph_iff {k : ℕ} (p : Equiv.Perm (Fin k))
    (G : Graph k) (x y : Fin k) :
    reach (relabelGraph p G) (p x) (p y) ↔ reach G x y := by
  change Relation.ReflTransGen (adj (relabelGraph p G)) (p x) (p y) ↔
    Relation.ReflTransGen (adj G) x y
  constructor
  · intro h
    have hmap : ∀ a b : Fin k,
        adj (relabelGraph p G) a b → adj G (p.symm a) (p.symm b) := by
      intro a b hab
      simpa using! (adj_relabelGraph_iff p G (p.symm a) (p.symm b)).mp
        (by simpa using! hab)
    have := reflTransGen_map p.symm hmap h
    simpa using! this
  · intro h
    have hmap : ∀ a b : Fin k, adj G a b →
        adj (relabelGraph p G) (p a) (p b) := by
      intro a b hab
      exact (adj_relabelGraph_iff p G a b).2 hab
    exact reflTransGen_map p hmap h

private theorem mem_componentOf_iff {k : ℕ} {G : Graph k}
    {x y : Fin k} : y ∈ componentOf G x ↔ reach G x y := by
  simp [componentOf]

theorem componentOf_relabelGraph {k : ℕ} (p : Equiv.Perm (Fin k))
    (G : Graph k) (x : Fin k) :
    componentOf (relabelGraph p G) (p x) =
      (componentOf G x).image p := by
  ext z
  let y := p.symm z
  have hzy : p y = z := by simp [y]
  constructor
  · intro hz
    apply Finset.mem_image.mpr
    refine ⟨y, ?_, hzy⟩
    apply mem_componentOf_iff.mpr
    apply (reach_relabelGraph_iff p G x y).mp
    simpa [hzy] using! mem_componentOf_iff.mp hz
  · intro hz
    rcases Finset.mem_image.mp hz with ⟨y', hy', hyz⟩
    rw [← hyz]
    apply mem_componentOf_iff.mpr
    exact (reach_relabelGraph_iff p G x y').2
      (mem_componentOf_iff.mp hy')

private theorem relabelGraph_filter_inside {k : ℕ}
    (p : Equiv.Perm (Fin k)) (G : Graph k) (S : Finset (Fin k)) :
    relabelGraph p (G.filter fun e => e.1.1 ∈ S ∧ e.1.2 ∈ S) =
      (relabelGraph p G).filter fun e =>
        e.1.1 ∈ S.image p ∧ e.1.2 ∈ S.image p := by
  ext e'
  constructor
  · intro he'
    rw [relabelGraph, Finset.mem_image] at he'
    rcases he' with ⟨e, he, rfl⟩
    have hmem := Finset.mem_filter.mp he
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_image.mpr ⟨e, hmem.1, rfl⟩, ?_⟩
    have hp := relabelEdge_endpoints p e
    rcases hp with hp | hp
    · exact ⟨Finset.mem_image.mpr ⟨e.1.1, hmem.2.1, hp.1.symm⟩,
        Finset.mem_image.mpr ⟨e.1.2, hmem.2.2, hp.2.symm⟩⟩
    · exact ⟨Finset.mem_image.mpr ⟨e.1.2, hmem.2.2, hp.1.symm⟩,
        Finset.mem_image.mpr ⟨e.1.1, hmem.2.1, hp.2.symm⟩⟩
  · intro he'
    have hmem := Finset.mem_filter.mp he'
    rw [relabelGraph, Finset.mem_image] at hmem
    rcases hmem.1 with ⟨e, he, rfl⟩
    rw [relabelGraph, Finset.mem_image]
    refine ⟨e, Finset.mem_filter.mpr ⟨he, ?_⟩, rfl⟩
    have hp := relabelEdge_endpoints p e
    rcases hp with hp | hp
    · constructor
      · rcases Finset.mem_image.mp hmem.2.1 with ⟨a, ha, hae⟩
        have := p.injective (hae.trans hp.1)
        simpa [this] using! ha
      · rcases Finset.mem_image.mp hmem.2.2 with ⟨a, ha, hae⟩
        have := p.injective (hae.trans hp.2)
        simpa [this] using! ha
    · constructor
      · rcases Finset.mem_image.mp hmem.2.2 with ⟨a, ha, hae⟩
        have := p.injective (hae.trans hp.2)
        simpa [this] using! ha
      · rcases Finset.mem_image.mp hmem.2.1 with ⟨a, ha, hae⟩
        have := p.injective (hae.trans hp.1)
        simpa [this] using! ha

theorem edgesInside_relabelGraph {k : ℕ} (p : Equiv.Perm (Fin k))
    (G : Graph k) (S : Finset (Fin k)) :
    edgesInside (relabelGraph p G) (S.image p) = edgesInside G S := by
  unfold edgesInside
  rw [← relabelGraph_filter_inside]
  exact card_relabelGraph p _

theorem relabelGraph_symm {k : ℕ} (p : Equiv.Perm (Fin k))
    (G : Graph k) :
    relabelGraph p (relabelGraph p.symm G) = G := by
  ext e
  constructor
  · intro he
    rw [relabelGraph, Finset.mem_image] at he
    rcases he with ⟨e', he', rfl⟩
    rw [relabelGraph, Finset.mem_image] at he'
    rcases he' with ⟨e, he, rfl⟩
    have heq : relabelEdge p (relabelEdge p.symm e) = e := by
      apply edgeSym2_injective
      rw [edgeSym2_relabel, edgeSym2_relabel]
      induction edgeSym2 e using Sym2.inductionOn with
      | _ a b => simp [Function.Embedding.sym2Map_apply]
    simpa [heq] using! he
  · intro he
    rw [relabelGraph, Finset.mem_image]
    refine ⟨relabelEdge p.symm e, ?_, ?_⟩
    · rw [relabelGraph, Finset.mem_image]
      exact ⟨e, he, rfl⟩
    · apply edgeSym2_injective
      rw [edgeSym2_relabel, edgeSym2_relabel]
      induction edgeSym2 e using Sym2.inductionOn with
      | _ a b => simp [Function.Embedding.sym2Map_apply]

private theorem image_rootPermutation_canonicalRoots {k j : ℕ}
    (roots : Fin j ↪ Fin k) :
    (canonicalRoots k j).image (rootPermutation roots) =
      Finset.univ.image roots := by
  have hjk : j ≤ k := by
    simpa using! Fintype.card_le_of_embedding roots
  ext x
  constructor
  · intro hx
    rcases Finset.mem_image.mp hx with ⟨y, hy, rfl⟩
    have hylt : y.1 < j := (Finset.mem_filter.mp hy).2
    let i : Fin j := ⟨y.1, hylt⟩
    have hycast : Fin.castLE hjk i = y := by
      apply Fin.ext
      rfl
    have hp : rootPermutation roots (Fin.castLE hjk i) = roots i := by
      simpa using! rootPermutation_apply_castLE roots i
    apply Finset.mem_image.mpr
    refine ⟨i, Finset.mem_univ i, ?_⟩
    rw [← hp, hycast]
  · intro hx
    rcases Finset.mem_image.mp hx with ⟨i, -, rfl⟩
    apply Finset.mem_image.mpr
    refine ⟨Fin.castLE hjk i, ?_, ?_⟩
    simp [canonicalRoots, Fin.castLE]
    simpa using! rootPermutation_apply_castLE roots i

private theorem card_inter_image {k : ℕ} (p : Equiv.Perm (Fin k))
    (S T : Finset (Fin k)) :
    ((S.image p) ∩ (T.image p)).card = (S ∩ T).card := by
  rw [← Finset.image_inter S T p.injective]
  exact Finset.card_image_of_injective _ p.injective

/-- A rooted forest on an arbitrary ordered root embedding has an actual
coefficient code whose selected roots and relabelled forest are exactly the
given data. -/
theorem exists_forestCode {k j : ℕ} (roots : Fin j ↪ Fin k)
    (F : Graph k)
    (hF : ∀ S ∈ components F,
      isTree F S ∧ (S ∩ (Finset.univ.image roots)).card = 1) :
    ∃ code : Fin (tau k j),
      selectedRoots k j code = roots ∧
      selectedForestGraph k j code = F := by
  let p := rootPermutation roots
  let F₀ := relabelGraph p.symm F
  have hF₀ : ∀ S ∈ components F₀,
      isTree F₀ S ∧ (S ∩ canonicalRoots k j).card = 1 := by
    intro S hS
    simp only [components, Finset.mem_image] at hS
    rcases hS with ⟨x, -, rfl⟩
    let T := componentOf F (p x)
    have hT : T ∈ components F := by simp [T, components]
    have hspec := hF T hT
    have hFrelabel : F = relabelGraph p F₀ := by
      symm
      exact relabelGraph_symm p F
    have hcomp : T = (componentOf F₀ x).image p := by
      change componentOf F (p x) = (componentOf F₀ x).image p
      rw [hFrelabel]
      exact componentOf_relabelGraph p F₀ x
    constructor
    · refine ⟨by simp [components], ?_⟩
      have hedge := edgesInside_relabelGraph p F₀ (componentOf F₀ x)
      rw [← hcomp, ← hFrelabel] at hedge
      have hcard : T.card = (componentOf F₀ x).card := by
        rw [hcomp]
        exact Finset.card_image_of_injective _ p.injective
      have htreecard := hspec.1.2
      omega
    · have hroots := image_rootPermutation_canonicalRoots roots
      have hinter := card_inter_image p (componentOf F₀ x)
        (canonicalRoots k j)
      rw [hroots, ← hcomp] at hinter
      omega
  let forest₀ : CanonicalRootedForest k j := ⟨F₀, by
    change F₀ ∈ (allGraphs k).filter (fun G => ∀ S ∈ components G,
      isTree G S ∧ (S ∩ canonicalRoots k j).card = 1)
    exact Finset.mem_filter.mpr ⟨by simp [allGraphs], hF₀⟩⟩
  let presentation : OrderedRootedForest k j := (roots, forest₀)
  let code := (finTauEquivOrderedRootedForest k j).symm presentation
  refine ⟨code, ?_, ?_⟩
  · simp [code, presentation, selectedRoots]
  · have hcode := (finTauEquivOrderedRootedForest k j).apply_symm_apply presentation
    have hroots : (finTauEquivOrderedRootedForest k j code).1 = roots := by
      simpa [code, presentation] using! congrArg Prod.fst hcode
    have hforest : (finTauEquivOrderedRootedForest k j code).2.1 = F₀ := by
      simpa [code, presentation, forest₀] using!
        congrArg (fun q => q.2.1) hcode
    simp only [selectedForestGraph, selectedCanonicalForest, selectedRoots]
    rw [hroots, hforest]
    exact relabelGraph_symm p F

/- The rooted forest supplied by the exact-excess core theorem is therefore
represented by a concrete `tau k v` index with the core labels first. -/
end Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_ForestInverse


/-!
# Suppression orbits and the compensated decoder

This module is the durable semantic boundary for forward suppression.  A
certificate records the finite orbit of labelled/oriented/parallel-ordered
representations of one connected graph.  The orbit is tied to the concrete
total decoder from `W02_KERNEL_Decode`; its total compensation is at least
one.  A family of such certificates therefore constructs the exact
`PruningSuppressionEncoding` consumed by the finite double-counting theorem.
-/

open scoped BigOperators

noncomputable section

namespace Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_Suppression

open Erdos745.WrapUp
open Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_Expansion
open Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_Decode
open Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_Mass

/-- A finite orbit of valid inverse kernel-expansion representations of `G`.
The orbit may be a proper subset of the full fibre; invalid majorant codes and
additional valid codes are harmless because all weights are nonnegative. -/
structure SuppressionOrbit (k r : ℕ) (G : Graph k) where
  representations : Finset (ExpansionCode k r)
  decode_eq : ∀ c ∈ representations, decodeExpansionCode c = G
  compensated_mass :
    1 ≤ ∑ c ∈ representations, expansionCodeWeight c

/-- Exact remaining combinatorial construction: every positive-excess
connected graph has a compensated suppression orbit for the concrete decoder. -/
def SuppressionOrbitStatement : Prop :=
  ∀ k r : ℕ, 0 < k → 0 < r →
    ∀ G ∈ positiveExcessGraphs k r, Nonempty (SuppressionOrbit k r G)

/-- The integer symmetry denominator cancelled by one labelled kernel orbit:
kernel-vertex relabellings, loop orientations, and permutations of every
parallel-edge family. -/
def symmetryDenominator {v r : ℕ} (H : KernelArray v r) : ℕ :=
  v.factorial * 2 ^ loopCount H *
    ∏ p : KernelIndex v, (multiplicity H p).factorial

private theorem sum_loop_exponents {v r : ℕ} (H : KernelArray v r) :
    ∑ p : KernelIndex v,
      (if p.1.1 = p.1.2 then multiplicity H p else 0) = loopCount H := by
  rfl

/-- Literal cancellation of the kernel weight and the `1/v!` quotient by the
full finite representation symmetry denominator. -/
theorem kernelWeight_div_factorial_eq_inv_symmetryDenominator
    {v r : ℕ} (H : KernelArray v r) :
    kernelWeight H / (v.factorial : ℝ) =
      ((symmetryDenominator H : ℕ) : ℝ)⁻¹ := by
  classical
  rw [kernelWeight_eq_compensation]
  unfold symmetryDenominator
  push_cast
  simp only [mul_inv_rev, Finset.prod_mul_distrib,
    Finset.prod_inv_distrib, Finset.prod_pow_eq_pow_sum,
    sum_loop_exponents]
  ring

/-- A concrete finite symmetry family above one graph.  The family need not
be the whole decoder fibre.  It records exactly the facts delivered by the
path/forest inverse construction: all codes decode to `G`, all have the same
kernel compensation weight, and their cardinality is the full symmetry
denominator. -/
structure SymmetryOrbit (k r : ℕ) (G : Graph k) where
  v : KernelSize r
  H : KernelChoice v.1 r
  representations : Finset (ExpansionCode k r)
  decode_eq : ∀ c ∈ representations, decodeExpansionCode c = G
  weight_eq : ∀ c ∈ representations,
    expansionCodeWeight c = kernelWeight H.1 / (v.1.factorial : ℝ)
  card_representations : representations.card = symmetryDenominator H.1

/-- The three independent choices in a full presentation orbit: a labelling
of kernel vertices, one reversal bit for every loop occurrence, and a
permutation of each parallel-edge family. -/
abbrev SymmetryChoices {v r : ℕ} (H : KernelArray v r) :=
  Equiv.Perm (Fin v) ×
    ((Fin (loopCount H) → Bool) ×
      ((p : KernelIndex v) → Equiv.Perm (Fin (multiplicity H p))))

/-- Literal cardinality of the decomposed symmetry-choice type. -/
theorem card_symmetryChoices {v r : ℕ} (H : KernelArray v r) :
    Fintype.card (SymmetryChoices H) = symmetryDenominator H := by
  classical
  simp [SymmetryChoices, symmetryDenominator, Fintype.card_perm,
    Fintype.card_pi, mul_assoc]

/-- Canonical finite indexing of all relabelling/orientation/parallel-order
choices by the exact compensation denominator. -/
noncomputable def finEquivSymmetryChoices {v r : ℕ} (H : KernelArray v r) :
    Fin (symmetryDenominator H) ≃ SymmetryChoices H :=
  (finCongr (card_symmetryChoices H).symm).trans (Fintype.equivFin _).symm

/-- A family indexed by the decomposed symmetry choices.  The suppression
recursion constructs this form directly; conversion to a denominator index
is purely finite enumeration. -/
structure ChoiceSymmetryFamily (k r : ℕ) (G : Graph k) where
  v : KernelSize r
  H : KernelChoice v.1 r
  code : SymmetryChoices H.1 → ExpansionCode k r
  code_injective : Function.Injective code
  decode_eq : ∀ s, decodeExpansionCode (code s) = G
  weight_eq : ∀ s,
    expansionCodeWeight (code s) = kernelWeight H.1 / (v.1.factorial : ℝ)

/-- An injectively indexed full symmetry family.  This is the convenient
output type for the suppression construction: the index records all kernel
vertex relabellings, loop orientations, and permutations inside parallel-edge
families.  Injectivity is exactly the freeness assertion for those choices. -/
structure IndexedSymmetryFamily (k r : ℕ) (G : Graph k) where
  v : KernelSize r
  H : KernelChoice v.1 r
  code : Fin (symmetryDenominator H.1) → ExpansionCode k r
  code_injective : Function.Injective code
  decode_eq : ∀ i, decodeExpansionCode (code i) = G
  weight_eq : ∀ i,
    expansionCodeWeight (code i) = kernelWeight H.1 / (v.1.factorial : ℝ)

/-- Enumerate the decomposed symmetry choices by the exact denominator. -/
noncomputable def ChoiceSymmetryFamily.toIndexed {k r : ℕ} {G : Graph k}
    (F : ChoiceSymmetryFamily k r G) : IndexedSymmetryFamily k r G where
  v := F.v
  H := F.H
  code := F.code ∘ finEquivSymmetryChoices F.H.1
  code_injective := F.code_injective.comp (finEquivSymmetryChoices F.H.1).injective
  decode_eq := fun i => F.decode_eq (finEquivSymmetryChoices F.H.1 i)
  weight_eq := fun i => F.weight_eq (finEquivSymmetryChoices F.H.1 i)

namespace IndexedSymmetryFamily

/-- The finite decoder fibre contributed by an indexed symmetry family. -/
noncomputable def representations {k r : ℕ} {G : Graph k}
    (F : IndexedSymmetryFamily k r G) : Finset (ExpansionCode k r) :=
  Finset.univ.image F.code

theorem mem_representations_iff {k r : ℕ} {G : Graph k}
    (F : IndexedSymmetryFamily k r G) (c : ExpansionCode k r) :
    c ∈ F.representations ↔ ∃ i, F.code i = c := by
  classical
  simp [representations]

/-- Every member of the indexed family decodes to the original graph. -/
theorem decode_eq_of_mem {k r : ℕ} {G : Graph k}
    (F : IndexedSymmetryFamily k r G) (c : ExpansionCode k r)
    (hc : c ∈ F.representations) :
    decodeExpansionCode c = G := by
  obtain ⟨i, rfl⟩ := (F.mem_representations_iff c).mp hc
  exact F.decode_eq i

/-- Every indexed representation has the common compensated kernel weight. -/
theorem weight_eq_of_mem {k r : ℕ} {G : Graph k}
    (F : IndexedSymmetryFamily k r G) (c : ExpansionCode k r)
    (hc : c ∈ F.representations) :
    expansionCodeWeight c = kernelWeight F.H.1 / (F.v.1.factorial : ℝ) := by
  obtain ⟨i, rfl⟩ := (F.mem_representations_iff c).mp hc
  exact F.weight_eq i

/-- Freeness turns the symmetry index into the literal denominator-sized
decoder fibre required by `SymmetryOrbit`. -/
theorem card_representations {k r : ℕ} {G : Graph k}
    (F : IndexedSymmetryFamily k r G) :
    F.representations.card = symmetryDenominator F.H.1 := by
  classical
  rw [representations, Finset.card_image_of_injective _ F.code_injective]
  simp

/-- Package an injectively indexed family as the exact finite symmetry orbit
consumed by the compensation theorem. -/
noncomputable def toSymmetryOrbit {k r : ℕ} {G : Graph k}
    (F : IndexedSymmetryFamily k r G) : SymmetryOrbit k r G where
  v := F.v
  H := F.H
  representations := F.representations
  decode_eq := F.decode_eq_of_mem
  weight_eq := F.weight_eq_of_mem
  card_representations := F.card_representations

end IndexedSymmetryFamily

/-- Exact mass one for a full labelled/oriented/parallel-ordered symmetry
orbit.  This is the compensation calculation in equation (6), isolated from
the graph-theoretic path construction. -/
theorem SymmetryOrbit.mass_one {k r : ℕ} {G : Graph k}
    (O : SymmetryOrbit k r G) :
    ∑ c ∈ O.representations, expansionCodeWeight c = 1 := by
  calc
    ∑ c ∈ O.representations, expansionCodeWeight c =
        ∑ _c ∈ O.representations,
          kernelWeight O.H.1 / (O.v.1.factorial : ℝ) := by
      apply Finset.sum_congr rfl
      intro c hc
      exact O.weight_eq c hc
    _ = (O.representations.card : ℝ) *
        (kernelWeight O.H.1 / (O.v.1.factorial : ℝ)) := by simp
    _ = (symmetryDenominator O.H.1 : ℝ) *
        ((symmetryDenominator O.H.1 : ℕ) : ℝ)⁻¹ := by
      rw [O.card_representations,
        kernelWeight_div_factorial_eq_inv_symmetryDenominator]
    _ = 1 := by
      have hpos : 0 < symmetryDenominator O.H.1 := by
        unfold symmetryDenominator
        positivity
      exact mul_inv_cancel₀ (by positivity)

/-- Forgetting the uniform symmetry presentation yields the compensated
decoder orbit consumed by the finite double-counting theorem. -/
def SymmetryOrbit.toSuppressionOrbit {k r : ℕ} {G : Graph k}
    (O : SymmetryOrbit k r G) : SuppressionOrbit k r G where
  representations := O.representations
  decode_eq := O.decode_eq
  compensated_mass := by rw [O.mass_one]

/-- Strong construction boundary for the remaining suppression proof. -/
def SymmetryOrbitStatement : Prop :=
  ∀ k r : ℕ, 0 < k → 0 < r →
    ∀ G ∈ positiveExcessGraphs k r, Nonempty (SymmetryOrbit k r G)

/-- Construction-facing form of `SymmetryOrbitStatement`.  The remaining
graph-theoretic suppression recursion may expose all symmetry choices through
a finite index; the lemmas above perform the exact finite enumeration. -/
def IndexedSymmetryFamilyStatement : Prop :=
  ∀ k r : ℕ, 0 < k → 0 < r →
    ∀ G ∈ positiveExcessGraphs k r,
      Nonempty (IndexedSymmetryFamily k r G)

/-- Suppression-facing statement with the three symmetry factors kept
separate. -/
def ChoiceSymmetryFamilyStatement : Prop :=
  ∀ k r : ℕ, 0 < k → 0 < r →
    ∀ G ∈ positiveExcessGraphs k r,
      Nonempty (ChoiceSymmetryFamily k r G)

theorem indexedSymmetryFamilyStatement_of_choices
    (h : ChoiceSymmetryFamilyStatement) : IndexedSymmetryFamilyStatement := by
  intro k r hk hr G hG
  obtain ⟨F⟩ := h k r hk hr G hG
  exact ⟨F.toIndexed⟩

/-- An indexed free symmetry construction supplies the public orbit
interface, including the exact denominator cardinality. -/
theorem symmetryOrbitStatement_of_indexed
    (h : IndexedSymmetryFamilyStatement) : SymmetryOrbitStatement := by
  intro k r hk hr G hG
  obtain ⟨F⟩ := h k r hk hr G hG
  exact ⟨F.toSymmetryOrbit⟩

/-- A free family over the literal relabelling/orientation/parallel-order
choice type supplies the exact symmetry-orbit statement. -/
theorem symmetryOrbitStatement_of_choices
    (h : ChoiceSymmetryFamilyStatement) : SymmetryOrbitStatement :=
  symmetryOrbitStatement_of_indexed
    (indexedSymmetryFamilyStatement_of_choices h)

/-- A complete symmetry-orbit construction supplies the existing semantic
suppression-orbit interface without any additional counting premise. -/
theorem suppressionOrbitStatement_of_symmetry
    (h : SymmetryOrbitStatement) : SuppressionOrbitStatement := by
  intro k r hk hr G hG
  obtain ⟨O⟩ := h k r hk hr G hG
  exact ⟨O.toSuppressionOrbit⟩

private noncomputable def chosenOrbit (h : SuppressionOrbitStatement)
    {k r : ℕ} (hk : 0 < k) (hr : 0 < r) (G : Graph k)
    (hG : G ∈ positiveExcessGraphs k r) : SuppressionOrbit k r G :=
  Classical.choice (h k r hk hr G hG)

/-- The concrete decoder and the certified orbits satisfy the quantitative
interface used by `connectedCount_le_expansionMajorant`. -/
noncomputable def pruningSuppressionEncoding_of_orbits
    (h : SuppressionOrbitStatement) (k r : ℕ) (hk : 0 < k) (hr : 0 < r) :
    PruningSuppressionEncoding k r where
  decode := decodeExpansionCode
  compensated_fiber_covers := by
    intro G hG
    let cert := chosenOrbit h hk hr G hG
    calc
      1 ≤ ∑ c ∈ cert.representations, expansionCodeWeight c :=
        cert.compensated_mass
      _ = ∑ c ∈ cert.representations,
          if decodeExpansionCode c = G then expansionCodeWeight c else 0 := by
        apply Finset.sum_congr rfl
        intro c hc
        simp [cert.decode_eq c hc]
      _ ≤ ∑ c : ExpansionCode k r,
          if decodeExpansionCode c = G then expansionCodeWeight c else 0 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        intro c hc hnot
        split_ifs
        · exact expansionCodeWeight_nonneg c
        · exact le_rfl

/-- Orbit construction implies the original W02 pruning/suppression
statement, with no further premise hidden in the assembly layer. -/
theorem connectedCount_le_expansionMajorant_of_orbits
    (h : SuppressionOrbitStatement) {k r : ℕ} (hk : 0 < k) (hr : 0 < r) :
    (connectedCount k (k + r) : ℝ) ≤ expansionMajorant k r := by
  exact connectedCount_le_expansionMajorant
    (pruningSuppressionEncoding_of_orbits h k r hk hr)

end Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_Suppression


/-!
# Semantic construction of kernel-expansion codes

The finite majorant stores compositions and ordered rooted forests as bare
`Fin` indices.  Forward suppression, however, naturally produces their
semantic data.  This module is the one-way construction boundary between
those representations.  It chooses both indices simultaneously, records the
exact decoder normal form, and exposes the ordered root list as an injective
observable of the resulting code.
-/

open scoped BigOperators

noncomputable section

namespace Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_Encode

open Erdos745.WrapUp
open Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_Composition
open Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_Decode
open Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_Expansion
open Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_Forest
open Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_ForestInverse
open Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_Mass
open Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_Occurrences
open Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_Relabel
open Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_Suppression

/-- Semantic data from which one exact finite expansion code is reconstructed.
The kernel size and number of forest roots are parameters so a whole symmetry
family can share them definitionally while its labelled kernel varies. -/
structure ExpansionPresentation (k r : ℕ) (v : KernelSize r)
    (j : TreeCount k v.1) where
  H : KernelChoice v.1 r
  lengths : Fin (v.1 + r) → ℕ
  sum_lengths : ∑ t, lengths t = j.1 - v.1
  roots : Fin j.1 ↪ Fin k
  forest : Graph k
  forest_spec : ∀ S ∈ components forest,
    isTree forest S ∧ (S ∩ Finset.univ.image roots).card = 1

namespace ExpansionPresentation

private theorem v_pos {k r : ℕ} {v : KernelSize r}
    {j : TreeCount k v.1} (_P : ExpansionPresentation k r v j) : 0 < v.1 :=
  (Finset.mem_Icc.mp v.2).1

private theorem v_le_j {k r : ℕ} {v : KernelSize r}
    {j : TreeCount k v.1} (_P : ExpansionPresentation k r v j) : v.1 ≤ j.1 :=
  (Finset.mem_Icc.mp j.2).1

/-- The exact stars-and-bars index selected by the semantic path lengths. -/
noncomputable def lengthCode {k r : ℕ} {v : KernelSize r}
    {j : TreeCount k v.1} (P : ExpansionPresentation k r v j) :
    Fin ((v.1 + r + j.1 - v.1 - 1).choose (v.1 + r - 1)) :=
  Classical.choose (exists_expansionParts_code v.1 r j.1 P.v_pos P.v_le_j
    P.lengths P.sum_lengths)

theorem expansionParts_lengthCode {k r : ℕ} {v : KernelSize r}
    {j : TreeCount k v.1} (P : ExpansionPresentation k r v j) :
    expansionParts v.1 r j.1 P.v_pos P.v_le_j P.lengthCode = P.lengths :=
  Classical.choose_spec (exists_expansionParts_code v.1 r j.1 P.v_pos P.v_le_j
    P.lengths P.sum_lengths)

/-- The exact ordered-rooted-forest index selected by the semantic forest. -/
noncomputable def forestCode {k r : ℕ} {v : KernelSize r}
    {j : TreeCount k v.1} (P : ExpansionPresentation k r v j) : Fin (tau k j.1) :=
  Classical.choose (exists_forestCode P.roots P.forest P.forest_spec)

theorem selectedRoots_forestCode {k r : ℕ} {v : KernelSize r}
    {j : TreeCount k v.1} (P : ExpansionPresentation k r v j) :
    selectedRoots k j.1 P.forestCode = P.roots :=
  (Classical.choose_spec (exists_forestCode P.roots P.forest P.forest_spec)).1

theorem selectedForestGraph_forestCode {k r : ℕ} {v : KernelSize r}
    {j : TreeCount k v.1} (P : ExpansionPresentation k r v j) :
    selectedForestGraph k j.1 P.forestCode = P.forest :=
  (Classical.choose_spec (exists_forestCode P.roots P.forest P.forest_spec)).2

/-- The concrete `ExpansionCode` represented by the semantic data. -/
noncomputable def code {k r : ℕ} {v : KernelSize r}
    {j : TreeCount k v.1} (P : ExpansionPresentation k r v j) :
    ExpansionCode k r :=
  ⟨v, P.H, j, P.lengthCode, P.forestCode⟩

@[simp] theorem code_v {k r : ℕ} {v : KernelSize r}
    {j : TreeCount k v.1} (P : ExpansionPresentation k r v j) : P.code.1 = v := rfl

@[simp] theorem code_H {k r : ℕ} {v : KernelSize r}
    {j : TreeCount k v.1} (P : ExpansionPresentation k r v j) : P.code.2.1 = P.H := rfl

@[simp] theorem code_j {k r : ℕ} {v : KernelSize r}
    {j : TreeCount k v.1} (P : ExpansionPresentation k r v j) : P.code.2.2.1 = j := rfl

theorem codeLengths_code {k r : ℕ} {v : KernelSize r}
    {j : TreeCount k v.1} (P : ExpansionPresentation k r v j) :
    codeLengths P.code = P.lengths := by
  unfold codeLengths
  change expansionParts v.1 r j.1
    (Finset.mem_Icc.mp v.2).1 (Finset.mem_Icc.mp j.2).1 P.lengthCode = P.lengths
  exact P.expansionParts_lengthCode

theorem nonkernelLabels_code {k r : ℕ} {v : KernelSize r}
    {j : TreeCount k v.1} (P : ExpansionPresentation k r v j) :
    nonkernelLabels P.code = (List.ofFn P.roots).drop v.1 := by
  change (List.ofFn (selectedRoots k j.1 P.forestCode)).drop v.1 = _
  rw [P.selectedRoots_forestCode]

/-- The semantic internal blocks are read back literally by the decoder. -/
theorem codeInternalBlocks_code {k r : ℕ} {v : KernelSize r}
    {j : TreeCount k v.1} (P : ExpansionPresentation k r v j) :
    codeInternalBlocks P.code =
      splitBy (List.ofFn P.lengths) ((List.ofFn P.roots).drop v.1) := by
  unfold codeInternalBlocks
  rw [P.codeLengths_code, P.nonkernelLabels_code]

/-- The first `v` selected roots are the labels of the kernel vertices. -/
theorem kernelVertexLabel_code {k r : ℕ} {v : KernelSize r}
    {j : TreeCount k v.1} (P : ExpansionPresentation k r v j)
    (i : Fin v.1) :
    kernelVertexLabel P.code i = P.roots (Fin.castLE P.v_le_j i) := by
  change (selectedRoots k j.1 P.forestCode)
    (Fin.castLE (Finset.mem_Icc.mp j.2).1 i) = _
  rw [P.selectedRoots_forestCode]

/-- The decoder sees the selected semantic forest without any loss. -/
theorem decode_code {k r : ℕ} {v : KernelSize r}
    {j : TreeCount k v.1} (P : ExpansionPresentation k r v j) :
    decodeExpansionCode P.code = P.forest ∪ kernelPathGraph P.code := by
  change selectedForestGraph k j.1 P.forestCode ∪ kernelPathGraph P.code = _
  rw [P.selectedForestGraph_forestCode]

/-- The compensated weight of a constructed code depends only on its selected
kernel, exactly as required by the orbit interface. -/
theorem expansionCodeWeight_code {k r : ℕ} {v : KernelSize r}
    {j : TreeCount k v.1} (P : ExpansionPresentation k r v j) :
    expansionCodeWeight P.code = kernelWeight P.H.1 / (v.1.factorial : ℝ) := by
  rfl

end ExpansionPresentation

/-- Path lengths, viewed as an ordinary list.  This is a uniform observable
on expansion codes even though the function domain depends on the selected
kernel size. -/
noncomputable def codeLengthList {k r : ℕ} (c : ExpansionCode k r) : List ℕ :=
  List.ofFn (codeLengths c)

theorem codeLengthList_code {k r : ℕ} {v : KernelSize r}
    {j : TreeCount k v.1} (P : ExpansionPresentation k r v j) :
    codeLengthList P.code = List.ofFn P.lengths := by
  change List.ofFn (codeLengths P.code) = _
  rw [P.codeLengths_code]

/-- Ordered roots, viewed as an ordinary list.  Unlike the dependent root
embedding itself, this is a uniform observable on every expansion code. -/
noncomputable def codeRootList {k r : ℕ} (c : ExpansionCode k r) : List (Fin k) :=
  List.ofFn (selectedRoots k c.2.2.1.1 c.2.2.2.2)

theorem codeRootList_code {k r : ℕ} {v : KernelSize r}
    {j : TreeCount k v.1} (P : ExpansionPresentation k r v j) :
    codeRootList P.code = List.ofFn P.roots := by
  change List.ofFn (selectedRoots k j.1 P.forestCode) = _
  rw [P.selectedRoots_forestCode]

/-- Semantic presentation of the entire free symmetry family.  Freeness is
recorded by the pair consisting of the ordered path lengths and ordered core
roots.  Both observables are needed: permuting a direct branch edge (whose
internal block is empty) past a parallel nonempty path changes the length
vector but not the concatenated root list.  All finite-index choices, decoder
facts, and compensation weights are discharged by the generic construction. -/
structure ChoicePresentationFamily (k r : ℕ) (G : Graph k) where
  v : KernelSize r
  H : KernelChoice v.1 r
  j : TreeCount k v.1
  presentation : SymmetryChoices H.1 → ExpansionPresentation k r v j
  data_injective : Function.Injective
    (fun s => ((presentation s).lengths, (presentation s).roots))
  decode_eq : ∀ s, decodeExpansionCode (presentation s).code = G
  kernelWeight_eq : ∀ s, kernelWeight (presentation s).H.1 = kernelWeight H.1

namespace ChoicePresentationFamily

/-- The length vector together with the root-list observable proves freeness
of the constructed codes. -/
theorem code_injective {k r : ℕ} {G : Graph k}
    (F : ChoicePresentationFamily k r G) :
    Function.Injective (fun s => (F.presentation s).code) := by
  intro a b hab
  apply F.data_injective
  have hlengths := congrArg codeLengthList hab
  have hroots := congrArg codeRootList hab
  have hlengthList : List.ofFn (F.presentation a).lengths =
      List.ofFn (F.presentation b).lengths := by
    simpa only [codeLengthList_code] using! hlengths
  have hlengths' : (F.presentation a).lengths =
      (F.presentation b).lengths := List.ofFn_injective hlengthList
  have hlist : List.ofFn (F.presentation a).roots =
      List.ofFn (F.presentation b).roots := by
    simpa only [codeRootList_code] using! hroots
  have hfun : (F.presentation a).roots.toFun =
      (F.presentation b).roots.toFun := List.ofFn_injective hlist
  exact Prod.ext hlengths' (Function.Embedding.ext (congrFun hfun))

/-- Package semantic path/forest presentations as the exact choice-indexed
symmetry family consumed by the compensated orbit theorem. -/
noncomputable def toChoiceSymmetryFamily {k r : ℕ} {G : Graph k}
    (F : ChoicePresentationFamily k r G) : ChoiceSymmetryFamily k r G where
  v := F.v
  H := F.H
  code := fun s => (F.presentation s).code
  code_injective := F.code_injective
  decode_eq := F.decode_eq
  weight_eq := by
    intro s
    rw [(F.presentation s).expansionCodeWeight_code, F.kernelWeight_eq s]

end ChoicePresentationFamily

/-- Construction statement at the semantic maximal-path boundary. -/
def ChoicePresentationFamilyStatement : Prop :=
  ∀ k r : ℕ, 0 < k → 0 < r →
    ∀ G ∈ positiveExcessGraphs k r,
      Nonempty (ChoicePresentationFamily k r G)

theorem choiceSymmetryFamilyStatement_of_presentations
    (h : ChoicePresentationFamilyStatement) : ChoiceSymmetryFamilyStatement := by
  intro k r hk hr G hG
  obtain ⟨F⟩ := h k r hk hr G hG
  exact ⟨F.toChoiceSymmetryFamily⟩

end Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_Encode
