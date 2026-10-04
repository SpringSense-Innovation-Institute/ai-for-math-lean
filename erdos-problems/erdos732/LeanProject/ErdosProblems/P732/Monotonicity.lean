module

public import LeanProject.ErdosProblems.P732.Construction

@[expose] public section

noncomputable section

namespace ErdosProblems
namespace P732

/-!
Monotonicity helpers for enlarging the ground set of a block-compatible
sequence.

Given a design on `n` points and `N ≥ n`, the old blocks are embedded into
`α ⊕ Fin (N - n)` and every pair not wholly contained in the old copy of `α`
is appended as a 2-block.
-/

def extendList (n N : ℕ) (xs : List ℕ) : List ℕ :=
  xs ++ List.replicate (Nat.choose N 2 - Nat.choose n 2) 2

@[simp] theorem extendList_length (n N : ℕ) (xs : List ℕ) :
    (extendList n N xs).length =
      xs.length + (Nat.choose N 2 - Nat.choose n 2) := by
  simp [extendList]

theorem extendList_get_left {n N : ℕ} {xs : List ℕ}
    (i : Fin (extendList n N xs).length) (hi : i.1 < xs.length) :
    (extendList n N xs).get i = xs.get ⟨i.1, hi⟩ := by
  rw [List.get_eq_getElem, List.get_eq_getElem]
  exact List.getElem_append_left hi

theorem extendList_get_right {n N : ℕ} {xs : List ℕ}
    (i : Fin (extendList n N xs).length) (hi : xs.length ≤ i.1) :
    (extendList n N xs).get i = 2 := by
  have hlen :
      i.1 < xs.length + (Nat.choose N 2 - Nat.choose n 2) := by
    simpa [extendList] using i.2
  have hright : i.1 - xs.length < Nat.choose N 2 - Nat.choose n 2 := by
    omega
  rw [List.get_eq_getElem]
  simp only [extendList]
  rw [List.getElem_append_right hi]
  exact List.getElem_replicate (by simpa using hright)

theorem extendList_take_left (n N : ℕ) (xs : List ℕ) :
    (extendList n N xs).take xs.length = xs := by
  simp [extendList]

theorem extendList_injective (n N : ℕ) :
    Function.Injective (extendList n N) := by
  intro xs ys h
  have hlen : ys.length = xs.length := by
    have hcongr := congrArg List.length h
    simp [extendList] at hcongr
    omega
  have htake := congrArg (fun zs : List ℕ => zs.take xs.length) h
  have hright : (extendList n N ys).take xs.length = ys := by
    rw [← hlen]
    exact extendList_take_left n N ys
  exact (extendList_take_left n N xs).symm.trans (htake.trans hright)

def oldPointSet {α : Type} [Fintype α] [DecidableEq α] (r : ℕ) :
    Finset (α ⊕ Fin r) :=
  (Finset.univ : Finset α).image Sum.inl

@[simp] private theorem mem_oldPointSet {α : Type} [Fintype α] [DecidableEq α]
    {r : ℕ} {x : α ⊕ Fin r} :
    x ∈ oldPointSet (α := α) r ↔ ∃ a : α, Sum.inl a = x := by
  simp [oldPointSet]

private theorem oldPointSet_card {α : Type} [Fintype α] [DecidableEq α] (r : ℕ) :
    (oldPointSet (α := α) r).card = Fintype.card α := by
  calc
    ((Finset.univ : Finset α).image (Sum.inl : α → α ⊕ Fin r)).card =
        (Finset.univ : Finset α).card :=
      Finset.card_image_of_injective _ Sum.inl_injective
    _ = Fintype.card α := Finset.card_univ

def newPairs {α : Type} [Fintype α] [DecidableEq α] (r : ℕ) :
    Finset (Finset (α ⊕ Fin r)) :=
  (Finset.univ : Finset (α ⊕ Fin r)).powersetCard 2 \
    (oldPointSet (α := α) r).powersetCard 2

theorem newPairs_card {α : Type} [Fintype α] [DecidableEq α]
    {n N : ℕ} (hN : n ≤ N) (hcard : Fintype.card α = n) :
    (newPairs (α := α) (N - n)).card =
      Nat.choose N 2 - Nat.choose n 2 := by
  have hsubset :
      (oldPointSet (α := α) (N - n)).powersetCard 2 ⊆
        (Finset.univ : Finset (α ⊕ Fin (N - n))).powersetCard 2 := by
    intro p hp
    exact Finset.mem_powersetCard.2
      ⟨Finset.subset_univ p, (Finset.mem_powersetCard.1 hp).2⟩
  rw [newPairs, Finset.card_sdiff_of_subset hsubset]
  rw [Finset.card_powersetCard, Finset.card_powersetCard]
  rw [Finset.card_univ, oldPointSet_card]
  have hsum : Fintype.card (α ⊕ Fin (N - n)) = N := by
    rw [Fintype.card_sum, Fintype.card_fin, hcard]
    omega
  rw [hsum, hcard]

def NewPairIndex {α : Type} [Fintype α] [DecidableEq α]
    (n N : ℕ) : Type :=
  {p : Finset (α ⊕ Fin (N - n)) // p ∈ newPairs (α := α) (N - n)}

instance {α : Type} [Fintype α] [DecidableEq α]
    (n N : ℕ) : Fintype (NewPairIndex (α := α) n N) := by
  unfold NewPairIndex
  infer_instance

theorem newPairIndex_card {α : Type} [Fintype α] [DecidableEq α]
    {n N : ℕ} (hN : n ≤ N) (hcard : Fintype.card α = n) :
    Fintype.card (NewPairIndex (α := α) n N) =
      Nat.choose N 2 - Nat.choose n 2 := by
  change Fintype.card {p : Finset (α ⊕ Fin (N - n)) //
      p ∈ newPairs (α := α) (N - n)} =
    Nat.choose N 2 - Nat.choose n 2
  exact (Fintype.card_coe _).trans (newPairs_card hN hcard)

def newPairEquiv {α : Type} [Fintype α] [DecidableEq α]
    {n N : ℕ} (hN : n ≤ N) (hcard : Fintype.card α = n) :
    NewPairIndex (α := α) n N ≃ Fin (Nat.choose N 2 - Nat.choose n 2) :=
  Fintype.equivFinOfCardEq (newPairIndex_card hN hcard)

theorem newPairIndex_ext {α : Type} [Fintype α] [DecidableEq α]
    {n N : ℕ} {x y : NewPairIndex (α := α) n N}
    (h : x.1 = y.1) : x = y := by
  cases x with
  | mk xv hx =>
      cases y with
      | mk yv hy =>
          dsimp at h
          subst yv
          rfl

def oldPointEmbedding (α : Type) (r : ℕ) : α ↪ α ⊕ Fin r :=
  Function.Embedding.inl

def extendLeftIndex (n N : ℕ) (xs : List ℕ) (i : Fin xs.length) :
    Fin (extendList n N xs).length :=
  Fin.cast (extendList_length n N xs).symm
    (Fin.castAdd (Nat.choose N 2 - Nat.choose n 2) i)

def extendRightIndex (n N : ℕ) (xs : List ℕ)
    (i : Fin (Nat.choose N 2 - Nat.choose n 2)) :
    Fin (extendList n N xs).length :=
  Fin.cast (extendList_length n N xs).symm
    (Fin.natAdd xs.length i)

theorem extendIndex_cases {n N : ℕ} {xs : List ℕ}
    {P : Fin (extendList n N xs).length → Prop}
    (hleft : ∀ i : Fin xs.length, P (extendLeftIndex n N xs i))
    (hright : ∀ i : Fin (Nat.choose N 2 - Nat.choose n 2),
      P (extendRightIndex n N xs i))
    (i : Fin (extendList n N xs).length) : P i := by
  change P (Fin.cast (extendList_length n N xs).symm
    (Fin.cast (extendList_length n N xs) i))
  induction Fin.cast (extendList_length n N xs) i using Fin.addCases with
  | left j =>
      simpa [extendLeftIndex] using hleft j
  | right j =>
      simpa [extendRightIndex] using hright j

def extendedBlock {α : Type} [Fintype α] [DecidableEq α]
    {n N : ℕ} (hN : n ≤ N) (hcard : Fintype.card α = n)
    {xs : List ℕ} (D : PairwiseBalancedDesign α xs.length)
    (i : Fin (extendList n N xs).length) : Finset (α ⊕ Fin (N - n)) :=
  Fin.addCases
    (fun j : Fin xs.length =>
      (D.block j).map (oldPointEmbedding α (N - n)))
    (fun j : Fin (Nat.choose N 2 - Nat.choose n 2) =>
      ((newPairEquiv hN hcard).symm j).1)
    (Fin.cast (extendList_length n N xs) i)

@[simp] theorem extendedBlock_left {α : Type} [Fintype α] [DecidableEq α]
    {n N : ℕ} (hN : n ≤ N) (hcard : Fintype.card α = n)
    {xs : List ℕ} (D : PairwiseBalancedDesign α xs.length)
    (i : Fin xs.length) :
    extendedBlock hN hcard D (extendLeftIndex n N xs i) =
      (D.block i).map (oldPointEmbedding α (N - n)) := by
  simp [extendedBlock, extendLeftIndex]

@[simp] theorem extendedBlock_right {α : Type} [Fintype α] [DecidableEq α]
    {n N : ℕ} (hN : n ≤ N) (hcard : Fintype.card α = n)
    {xs : List ℕ} (D : PairwiseBalancedDesign α xs.length)
    (i : Fin (Nat.choose N 2 - Nat.choose n 2)) :
    extendedBlock hN hcard D (extendRightIndex n N xs i) =
      ((newPairEquiv hN hcard).symm i).1 := by
  simp [extendedBlock, extendRightIndex]

theorem extendedBlock_card {α : Type} [Fintype α] [DecidableEq α]
    {n N : ℕ} (hN : n ≤ N) (hcard : Fintype.card α = n)
    {xs : List ℕ} (D : PairwiseBalancedDesign α xs.length)
    (hblock : ∀ i : Fin xs.length, (D.block i).card = xs.get i)
    (i : Fin (extendList n N xs).length) :
    (extendedBlock hN hcard D i).card = (extendList n N xs).get i := by
  refine extendIndex_cases (n := n) (N := N) (xs := xs)
    (P := fun i => (extendedBlock hN hcard D i).card =
      (extendList n N xs).get i) ?_ ?_ i
  · intro j
    rw [extendedBlock_left]
    have hget :
        (extendList n N xs).get (extendLeftIndex n N xs j) = xs.get j := by
      exact extendList_get_left (extendLeftIndex n N xs j) (by
        simp [extendLeftIndex, extendList, Fin.cast])
    rw [hget]
    simp [oldPointEmbedding, hblock j]
  · intro j
    rw [extendedBlock_right]
    have hget :
        (extendList n N xs).get (extendRightIndex n N xs j) = 2 := by
      exact extendList_get_right (extendRightIndex n N xs j) (by
        simp [extendRightIndex, extendList, Fin.cast])
    rw [hget]
    have hmem := (Finset.mem_sdiff.1 ((newPairEquiv hN hcard).symm j).2).1
    exact (Finset.mem_powersetCard.1 hmem).2

private theorem pair_mem_newPairs_of_not_both_old {α : Type} [Fintype α]
    [DecidableEq α] {r : ℕ} {a b : α ⊕ Fin r} (hab : a ≠ b)
    (hnot : ¬ (a ∈ oldPointSet (α := α) r ∧ b ∈ oldPointSet (α := α) r)) :
    ({a, b} : Finset (α ⊕ Fin r)) ∈ newPairs (α := α) r := by
  refine Finset.mem_sdiff.2 ⟨?_, ?_⟩
  · exact Finset.mem_powersetCard.2
      ⟨Finset.subset_univ _, Finset.card_pair hab⟩
  · intro hp
    have hsub := (Finset.mem_powersetCard.1 hp).1
    exact hnot ⟨hsub (by simp), hsub (by simp)⟩

theorem extendedBlock_pair_unique {α : Type} [Fintype α] [DecidableEq α]
    {n N : ℕ} (hN : n ≤ N) (hcard : Fintype.card α = n)
    {xs : List ℕ} (D : PairwiseBalancedDesign α xs.length) :
    ∀ ⦃a b : α ⊕ Fin (N - n)⦄, a ≠ b →
      ∃! i : Fin (extendList n N xs).length,
        a ∈ extendedBlock hN hcard D i ∧
          b ∈ extendedBlock hN hcard D i := by
  classical
  intro a b hab
  by_cases hold : a ∈ oldPointSet (α := α) (N - n) ∧
      b ∈ oldPointSet (α := α) (N - n)
  · rcases mem_oldPointSet.mp hold.1 with ⟨a0, ha0⟩
    rcases mem_oldPointSet.mp hold.2 with ⟨b0, hb0⟩
    subst a
    subst b
    have hab0 : a0 ≠ b0 := by
      intro h
      exact hab (by simp [h])
    rcases D.pair_unique hab0 with ⟨j, hj, huniq⟩
    refine ExistsUnique.intro (extendLeftIndex n N xs j) ?_ ?_
    · rw [extendedBlock_left]
      constructor
      · exact Finset.mem_map.2 ⟨a0, hj.1, rfl⟩
      · exact Finset.mem_map.2 ⟨b0, hj.2, rfl⟩
    · intro i hi
      refine extendIndex_cases (n := n) (N := N) (xs := xs)
        (P := fun i =>
          Sum.inl a0 ∈ extendedBlock hN hcard D i ∧
            Sum.inl b0 ∈ extendedBlock hN hcard D i →
              i = extendLeftIndex n N xs j) ?_ ?_ i hi
      · intro k hk
        rw [extendedBlock_left] at hk
        have hk' : a0 ∈ D.block k ∧ b0 ∈ D.block k := by
          constructor
          · rcases Finset.mem_map.1 hk.1 with ⟨x, hx, hxeq⟩
            simpa [oldPointEmbedding] using (Function.Embedding.inl.injective hxeq.symm ▸ hx)
          · rcases Finset.mem_map.1 hk.2 with ⟨x, hx, hxeq⟩
            simpa [oldPointEmbedding] using (Function.Embedding.inl.injective hxeq.symm ▸ hx)
        rw [huniq k hk']
      · intro k hk
        rw [extendedBlock_right] at hk
        have hpair :
            ((newPairEquiv hN hcard).symm k).1 =
              ({Sum.inl a0, Sum.inl b0} : Finset (α ⊕ Fin (N - n))) := by
          apply finset_eq_pair_of_card_two_of_mem
          · exact (Finset.mem_powersetCard.1
              (Finset.mem_sdiff.1 ((newPairEquiv hN hcard).symm k).2).1).2
          · exact hk.1
          · exact hk.2
          · exact hab
        have hnew_not_old :=
          (Finset.mem_sdiff.1 ((newPairEquiv hN hcard).symm k).2).2
        have hmem_old :
            ((newPairEquiv hN hcard).symm k).1 ∈
              (oldPointSet (α := α) (N - n)).powersetCard 2 := by
          rw [hpair]
          exact Finset.mem_powersetCard.2
            ⟨by
                intro x hx
                simp only [Finset.mem_insert, Finset.mem_singleton] at hx
                rcases hx with rfl | rfl
                · exact (mem_oldPointSet.2 ⟨a0, rfl⟩)
                · exact (mem_oldPointSet.2 ⟨b0, rfl⟩),
              Finset.card_pair hab⟩
        exact (hnew_not_old hmem_old).elim
  · have hnew : ({a, b} : Finset (α ⊕ Fin (N - n))) ∈
        newPairs (α := α) (N - n) :=
      pair_mem_newPairs_of_not_both_old hab hold
    let p : NewPairIndex (α := α) n N := ⟨{a, b}, hnew⟩
    let k : Fin (Nat.choose N 2 - Nat.choose n 2) := newPairEquiv hN hcard p
    refine ExistsUnique.intro (extendRightIndex n N xs k) ?_ ?_
    · have hk : (newPairEquiv hN hcard).symm k = p := by
        exact Equiv.symm_apply_apply (newPairEquiv hN hcard) p
      rw [extendedBlock_right]
      rw [hk]
      simp [p]
    · intro i hi
      refine extendIndex_cases (n := n) (N := N) (xs := xs)
        (P := fun i =>
          a ∈ extendedBlock hN hcard D i ∧ b ∈ extendedBlock hN hcard D i →
            i = extendRightIndex n N xs k) ?_ ?_ i hi
      · intro j hj
        rw [extendedBlock_left] at hj
        have haold : a ∈ oldPointSet (α := α) (N - n) := by
          rcases Finset.mem_map.1 hj.1 with ⟨x, _hx, rfl⟩
          exact mem_oldPointSet.2 ⟨x, rfl⟩
        have hbold : b ∈ oldPointSet (α := α) (N - n) := by
          rcases Finset.mem_map.1 hj.2 with ⟨x, _hx, rfl⟩
          exact mem_oldPointSet.2 ⟨x, rfl⟩
        exact (hold ⟨haold, hbold⟩).elim
      · intro j hj
        rw [extendedBlock_right] at hj
        have hpair :
            ((newPairEquiv hN hcard).symm j).1 =
              ({a, b} : Finset (α ⊕ Fin (N - n))) := by
          apply finset_eq_pair_of_card_two_of_mem
          · exact (Finset.mem_powersetCard.1
              (Finset.mem_sdiff.1 ((newPairEquiv hN hcard).symm j).2).1).2
          · exact hj.1
          · exact hj.2
          · exact hab
        have hjp : (newPairEquiv hN hcard).symm j = p :=
          newPairIndex_ext hpair
        have hjk : j = k := by
          apply (newPairEquiv hN hcard).symm.injective
          simpa [k] using hjp
        rw [hjk]

def extendedDesign {α : Type} [Fintype α] [DecidableEq α]
    {n N : ℕ} (hN : n ≤ N) (hcard : Fintype.card α = n)
    {xs : List ℕ} (D : PairwiseBalancedDesign α xs.length)
    (hblocks : ∀ i : Fin xs.length, (D.block i).card = xs.get i) :
    PairwiseBalancedDesign (α ⊕ Fin (N - n)) (extendList n N xs).length where
  block := extendedBlock hN hcard D
  block_card_ge_two := by
    intro i
    rw [extendedBlock_card hN hcard D hblocks i]
    by_cases hi : i.1 < xs.length
    · rw [extendList_get_left i hi]
      rw [← hblocks ⟨i.1, hi⟩]
      exact D.block_card_ge_two ⟨i.1, hi⟩
    · rw [extendList_get_right i (Nat.le_of_not_gt hi)]
  pair_unique := extendedBlock_pair_unique hN hcard D

theorem BlockCompatible.extend {n N : ℕ} (hN : n ≤ N)
    {xs : List ℕ} (hxs : BlockCompatible n xs) :
    BlockCompatible N (extendList n N xs) := by
  rcases hxs with ⟨α, instF, instD, hcard, D, hblocks⟩
  letI : Fintype α := instF
  letI : DecidableEq α := instD
  refine ⟨α ⊕ Fin (N - n), inferInstance, inferInstance, ?_, ?_⟩
  · rw [Fintype.card_sum, Fintype.card_fin, hcard]
    omega
  · exact ⟨extendedDesign hN hcard D hblocks, fun i =>
      extendedBlock_card hN hcard D hblocks i⟩

theorem ErdosSequence.extend {n N : ℕ} (hN : n ≤ N) (hN2 : 2 ≤ N)
    {xs : List ℕ} (hxs : ErdosSequence n xs) :
    ErdosSequence N (extendList n N xs) := by
  constructor
  · intro i j hij
    by_cases hi : i.1 < xs.length
    · by_cases hj : j.1 < xs.length
      · rw [extendList_get_left i hi, extendList_get_left j hj]
        exact hxs.1 ⟨i.1, hi⟩ ⟨j.1, hj⟩ hij
      · rw [extendList_get_left i hi, extendList_get_right j (Nat.le_of_not_gt hj)]
        exact (hxs.2 ⟨i.1, hi⟩).1
    · have hjright : xs.length ≤ j.1 := le_trans (Nat.le_of_not_gt hi) hij
      rw [extendList_get_right i (Nat.le_of_not_gt hi), extendList_get_right j hjright]
  · intro i
    by_cases hi : i.1 < xs.length
    · rw [extendList_get_left i hi]
      exact ⟨(hxs.2 ⟨i.1, hi⟩).1, (hxs.2 ⟨i.1, hi⟩).2.trans hN⟩
    · rw [extendList_get_right i (Nat.le_of_not_gt hi)]
      exact ⟨by omega, hN2⟩

theorem BlockCompatibleSequence.extend {n N : ℕ} (hN : n ≤ N) (hN2 : 2 ≤ N)
    {xs : List ℕ} (hxs : BlockCompatibleSequence n xs) :
    BlockCompatibleSequence N (extendList n N xs) :=
  ⟨hxs.1.extend hN hN2, hxs.2.extend hN⟩

theorem blockCompatibleSequence_ncard_mono {n N : ℕ} (hN : n ≤ N) (hN2 : 2 ≤ N) :
    Set.ncard {xs : List ℕ | BlockCompatibleSequence n xs}
      ≤ Set.ncard {xs : List ℕ | BlockCompatibleSequence N xs} := by
  exact Set.ncard_le_ncard_of_injOn (extendList n N)
    (fun xs hxs => BlockCompatibleSequence.extend hN hN2 hxs)
    (fun _ _ _ _ h => extendList_injective n N h)
    (ht := blockCompatibleSequence_finite N)

end P732
end ErdosProblems
