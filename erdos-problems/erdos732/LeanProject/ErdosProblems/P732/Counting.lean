module

public import LeanProject.ErdosProblems.P732.Construction

@[expose] public section

noncomputable section
open scoped BigOperators

namespace ErdosProblems
namespace P732

/-! Counting admissible heads is separated from the geometric construction. -/

private abbrev headAlphabet (q : ℕ) : Type :=
  Set.Icc 3 (q + 1)

private def headLength (q : ℕ) : ℕ :=
  q ^ 2 + q + 1

private theorem nonincreasing_iff_sortedGE {ys : List ℕ} :
    Nonincreasing ys ↔ ys.SortedGE := by
  exact (List.sortedGE_iff_antitone_get (l := ys)).symm

private def admissibleHeadToSym (q : ℕ)
    (ys : {ys : List ℕ // AdmissibleHead q ys}) :
    Sym (headAlphabet q) (headLength q) :=
  Sym.mk
    ((ys.1.attach.map fun x : {x // x ∈ ys.1} =>
      (⟨x.1, by
        rcases List.mem_iff_get.mp x.2 with ⟨i, hi⟩
        have hb := ys.2.bounds i
        rw [hi] at hb
        exact hb⟩ : headAlphabet q)) : Multiset _)
    (by simp [headLength, ys.2.length_eq])

private def admissibleHeadOfSym (q : ℕ)
    (s : Sym (headAlphabet q) (headLength q)) :
    {ys : List ℕ // AdmissibleHead q ys} where
  val := (s.1.map (fun x : headAlphabet q => (x : ℕ))).sort (· ≥ ·)
  property := by
    constructor
    · simpa [headLength] using s.prop
    constructor
    · have hpair :
          ((s.1.map (fun x : headAlphabet q => (x : ℕ))).sort (· ≥ ·)).Pairwise (· ≥ ·) :=
        Multiset.pairwise_sort _ _
      exact nonincreasing_iff_sortedGE.2 hpair.sortedGE
    · intro i
      have hmem :
          ((s.1.map (fun x : headAlphabet q => (x : ℕ))).sort (· ≥ ·)).get i ∈
            (s.1.map (fun x : headAlphabet q => (x : ℕ))).sort (· ≥ ·) :=
        List.get_mem _ _
      have hmem' :
          ((s.1.map (fun x : headAlphabet q => (x : ℕ))).sort (· ≥ ·)).get i ∈
            s.1.map (fun x : headAlphabet q => (x : ℕ)) := by
        simpa using (Multiset.mem_sort (r := fun a b : ℕ => a ≥ b)).1 hmem
      rcases Multiset.mem_map.1 hmem' with ⟨x, _hx, hx⟩
      simpa [hx] using x.2

private def admissibleHeadEquivSym (q : ℕ) :
    {ys : List ℕ // AdmissibleHead q ys} ≃ Sym (headAlphabet q) (headLength q) where
  toFun := admissibleHeadToSym q
  invFun := admissibleHeadOfSym q
  left_inv := by
    intro ys
    apply Subtype.ext
    apply List.Perm.eq_of_sortedGE
    · have hpair :
          ((((admissibleHeadToSym q ys).1.map fun x : headAlphabet q => (x : ℕ))).sort
              (· ≥ ·)).Pairwise (· ≥ ·) :=
        Multiset.pairwise_sort _ _
      exact hpair.sortedGE
    · exact nonincreasing_iff_sortedGE.1 ys.2.nonincreasing
    · simpa [admissibleHeadOfSym, admissibleHeadToSym, Sym.mk] using
        (List.mergeSort_perm ys.1 (fun x y : ℕ => x ≥ y))
  right_inv := by
    intro s
    apply Sym.ext
    apply Multiset.map_injective (f := fun x : headAlphabet q => (x : ℕ)) Subtype.val_injective
    simp [admissibleHeadOfSym, admissibleHeadToSym]

theorem admissibleHead_ncard (q : ℕ) (hq : 2 ≤ q) :
    Set.ncard {ys : List ℕ | AdmissibleHead q ys}
      = Nat.choose ((q ^ 2 + q + 1) + q - 2) (q - 2) := by
  let α := headAlphabet q
  have hset :
      Set.ncard {ys : List ℕ | AdmissibleHead q ys} =
        Nat.card {ys : List ℕ // AdmissibleHead q ys} := by
    rw [← Set.ncard_univ]
    exact Set.ncard_congr' (Equiv.Set.univ {ys : List ℕ | AdmissibleHead q ys}).symm
  have hchooseHead :
      Nat.choose (Fintype.card α + headLength q - 1) (headLength q) =
        Nat.choose ((q ^ 2 + q + 1) + q - 2) (headLength q) := by
    have hcardα : Fintype.card α = q - 1 := by
      simp [α, headAlphabet]
    have htop :
        Fintype.card α + headLength q - 1 = (q ^ 2 + q + 1) + q - 2 := by
      rw [hcardα]
      unfold headLength
      omega
    rw [htop]
  have hchooseSymm :
      Nat.choose ((q ^ 2 + q + 1) + q - 2) (headLength q) =
        Nat.choose ((q ^ 2 + q + 1) + q - 2) (q - 2) := by
    have hsum :
        (q ^ 2 + q + 1) + q - 2 = headLength q + (q - 2) := by
      unfold headLength
      omega
    exact Nat.choose_symm_of_eq_add hsum
  rw [hset]
  calc
    Nat.card {ys : List ℕ // AdmissibleHead q ys}
        = Nat.card (Sym α (headLength q)) :=
          Nat.card_congr (admissibleHeadEquivSym q)
    _ = Fintype.card (Sym α (headLength q)) := by
          rw [Nat.card_eq_fintype_card]
    _ = Nat.choose (Fintype.card α + headLength q - 1) (headLength q) := by
          rw [Sym.card_sym_eq_choose]
    _ = Nat.choose ((q ^ 2 + q + 1) + q - 2) (headLength q) := by
          exact hchooseHead
    _ = Nat.choose ((q ^ 2 + q + 1) + q - 2) (q - 2) := by
          exact hchooseSymm

end P732
end ErdosProblems
