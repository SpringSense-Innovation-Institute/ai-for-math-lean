module

public import LeanProject.ErdosProblems.P732.ProjectivePlane

@[expose] public section

noncomputable section
open scoped BigOperators

namespace ErdosProblems
namespace P732

/-!
This file isolates the constructive part of Theorem 2.3:
the admissible head, Alon's augmented list, and the design-existence theorem.
-/

def twoBlockCount (q : ℕ) (ys : List ℕ) : ℕ :=
  ∑ i : Fin ys.length,
    (Nat.choose (q + 1) 2 - Nat.choose (ys.get i) 2)

def AlonList (q : ℕ) (ys : List ℕ) : List ℕ :=
  ys ++ List.replicate (twoBlockCount q ys) 2

def AdmissibleHead (q : ℕ) (ys : List ℕ) : Prop :=
  ys.length = q ^ 2 + q + 1 ∧
    Nonincreasing ys ∧
      ∀ i : Fin ys.length, 3 ≤ ys.get i ∧ ys.get i ≤ q + 1

@[simp] theorem alonList_length (q : ℕ) (ys : List ℕ) :
    (AlonList q ys).length = ys.length + twoBlockCount q ys := by
  simp [AlonList]

theorem AdmissibleHead.length_eq {q : ℕ} {ys : List ℕ}
    (hys : AdmissibleHead q ys) :
    ys.length = q ^ 2 + q + 1 :=
  hys.1

theorem AdmissibleHead.nonincreasing {q : ℕ} {ys : List ℕ}
    (hys : AdmissibleHead q ys) :
    Nonincreasing ys :=
  hys.2.1

theorem AdmissibleHead.bounds {q : ℕ} {ys : List ℕ}
    (hys : AdmissibleHead q ys) (i : Fin ys.length) :
    3 ≤ ys.get i ∧ ys.get i ≤ q + 1 :=
  hys.2.2 i

theorem alonList_get_left {q : ℕ} {ys : List ℕ}
    (i : Fin (AlonList q ys).length) (hi : i.1 < ys.length) :
    (AlonList q ys).get i = ys.get ⟨i.1, hi⟩ := by
  rw [List.get_eq_getElem, List.get_eq_getElem]
  exact List.getElem_append_left hi

theorem alonList_get_right {q : ℕ} {ys : List ℕ}
    (i : Fin (AlonList q ys).length) (hi : ys.length ≤ i.1) :
    (AlonList q ys).get i = 2 := by
  have hlen : i.1 < ys.length + twoBlockCount q ys := by
    simpa [AlonList] using i.2
  have hright : i.1 - ys.length < twoBlockCount q ys := by
    omega
  rw [List.get_eq_getElem]
  simp only [AlonList]
  rw [List.getElem_append_right hi]
  exact List.getElem_replicate (by simpa using hright)

theorem AdmissibleHead.two_le_order {q : ℕ} {ys : List ℕ}
    (hys : AdmissibleHead q ys) :
    2 ≤ q ^ 2 + q + 1 := by
  have hlen : 0 < ys.length := by
    rw [hys.length_eq]
    omega
  let i : Fin ys.length := ⟨0, hlen⟩
  have hbound := hys.bounds i
  omega

noncomputable def chosenLineSubset {q : ℕ} (π : ProjectivePlane q)
    {ys : List ℕ} (hys : AdmissibleHead q ys)
    (i : Fin ys.length) : Finset π.Point :=
  Classical.choose <|
    Finset.exists_subset_card_eq
      (s := π.line (Fin.cast hys.length_eq i))
      (n := ys.get i) <| by
        rw [π.line_card]
        exact (hys.bounds i).2

theorem chosenLineSubset_subset {q : ℕ} (π : ProjectivePlane q)
    {ys : List ℕ} (hys : AdmissibleHead q ys)
    (i : Fin ys.length) :
    chosenLineSubset π hys i ⊆ π.line (Fin.cast hys.length_eq i) := by
  unfold chosenLineSubset
  exact (Classical.choose_spec <|
    Finset.exists_subset_card_eq
      (s := π.line (Fin.cast hys.length_eq i))
      (n := ys.get i) <| by
        rw [π.line_card]
        exact (hys.bounds i).2).1

theorem chosenLineSubset_card {q : ℕ} (π : ProjectivePlane q)
    {ys : List ℕ} (hys : AdmissibleHead q ys)
    (i : Fin ys.length) :
    (chosenLineSubset π hys i).card = ys.get i := by
  unfold chosenLineSubset
  exact (Classical.choose_spec <|
    Finset.exists_subset_card_eq
      (s := π.line (Fin.cast hys.length_eq i))
      (n := ys.get i) <| by
        rw [π.line_card]
        exact (hys.bounds i).2).2

def missingPairs {q : ℕ} (π : ProjectivePlane q)
    {ys : List ℕ} (hys : AdmissibleHead q ys)
    (i : Fin ys.length) : Finset (Finset π.Point) :=
  (π.line (Fin.cast hys.length_eq i)).powersetCard 2 \
    (chosenLineSubset π hys i).powersetCard 2

theorem missingPairs_card {q : ℕ} (π : ProjectivePlane q)
    {ys : List ℕ} (hys : AdmissibleHead q ys)
    (i : Fin ys.length) :
    (missingPairs π hys i).card =
      Nat.choose (q + 1) 2 - Nat.choose (ys.get i) 2 := by
  have hsubset :
      (chosenLineSubset π hys i).powersetCard 2 ⊆
        (π.line (Fin.cast hys.length_eq i)).powersetCard 2 := by
    intro p hp
    exact Finset.mem_powersetCard.2
      ⟨(Finset.mem_powersetCard.1 hp).1.trans (chosenLineSubset_subset π hys i),
        (Finset.mem_powersetCard.1 hp).2⟩
  rw [missingPairs, Finset.card_sdiff_of_subset hsubset]
  rw [Finset.card_powersetCard, Finset.card_powersetCard,
    π.line_card, chosenLineSubset_card]

def MissingPairIndex {q : ℕ} (π : ProjectivePlane q)
    {ys : List ℕ} (hys : AdmissibleHead q ys) : Type :=
  Σ i : Fin ys.length, {p : Finset π.Point // p ∈ missingPairs π hys i}

instance {q : ℕ} (π : ProjectivePlane q)
    {ys : List ℕ} (hys : AdmissibleHead q ys) :
    Fintype (MissingPairIndex π hys) := by
  unfold MissingPairIndex
  infer_instance

theorem missingPairIndex_card {q : ℕ} (π : ProjectivePlane q)
    {ys : List ℕ} (hys : AdmissibleHead q ys) :
    Fintype.card (MissingPairIndex π hys) = twoBlockCount q ys := by
  change Fintype.card
      (Σ i : Fin ys.length, {p : Finset π.Point // p ∈ missingPairs π hys i}) =
    twoBlockCount q ys
  calc
    Fintype.card
        (Σ i : Fin ys.length, {p : Finset π.Point // p ∈ missingPairs π hys i})
        = ∑ i : Fin ys.length,
            Fintype.card {p : Finset π.Point // p ∈ missingPairs π hys i} := by
          exact Fintype.card_sigma
    _ = twoBlockCount q ys := by
      rw [twoBlockCount]
      apply Finset.sum_congr rfl
      intro i _
      exact (Fintype.card_coe (missingPairs π hys i)).trans (missingPairs_card π hys i)

noncomputable def missingPairEquiv {q : ℕ} (π : ProjectivePlane q)
    {ys : List ℕ} (hys : AdmissibleHead q ys) :
    MissingPairIndex π hys ≃ Fin (twoBlockCount q ys) :=
  Fintype.equivFinOfCardEq (missingPairIndex_card π hys)

def alonLeftIndex (q : ℕ) (ys : List ℕ) (i : Fin ys.length) :
    Fin (AlonList q ys).length :=
  Fin.cast (alonList_length q ys).symm
    (Fin.castAdd (twoBlockCount q ys) i)

def alonRightIndex (q : ℕ) (ys : List ℕ)
    (i : Fin (twoBlockCount q ys)) :
    Fin (AlonList q ys).length :=
  Fin.cast (alonList_length q ys).symm
    (Fin.natAdd ys.length i)

noncomputable def constructionBlock {q : ℕ} (π : ProjectivePlane q)
    {ys : List ℕ} (hys : AdmissibleHead q ys)
    (i : Fin (AlonList q ys).length) : Finset π.Point :=
  Fin.addCases
    (fun j : Fin ys.length => chosenLineSubset π hys j)
    (fun j : Fin (twoBlockCount q ys) => ((missingPairEquiv π hys).symm j).2.1)
    (Fin.cast (alonList_length q ys) i)

noncomputable def constructionLineIndex {q : ℕ} (π : ProjectivePlane q)
    {ys : List ℕ} (hys : AdmissibleHead q ys)
    (i : Fin (AlonList q ys).length) : Fin (q ^ 2 + q + 1) :=
  Fin.addCases
    (fun j : Fin ys.length => Fin.cast hys.length_eq j)
    (fun j : Fin (twoBlockCount q ys) =>
      Fin.cast hys.length_eq ((missingPairEquiv π hys).symm j).1)
    (Fin.cast (alonList_length q ys) i)

@[simp] theorem constructionBlock_left {q : ℕ} (π : ProjectivePlane q)
    {ys : List ℕ} (hys : AdmissibleHead q ys)
    (i : Fin ys.length) :
    constructionBlock π hys (alonLeftIndex q ys i) =
      chosenLineSubset π hys i := by
  simp [constructionBlock, alonLeftIndex]

@[simp] theorem constructionBlock_right {q : ℕ} (π : ProjectivePlane q)
    {ys : List ℕ} (hys : AdmissibleHead q ys)
    (i : Fin (twoBlockCount q ys)) :
    constructionBlock π hys (alonRightIndex q ys i) =
      ((missingPairEquiv π hys).symm i).2.1 := by
  simp [constructionBlock, alonRightIndex]

@[simp] theorem constructionLineIndex_left {q : ℕ} (π : ProjectivePlane q)
    {ys : List ℕ} (hys : AdmissibleHead q ys)
    (i : Fin ys.length) :
    constructionLineIndex π hys (alonLeftIndex q ys i) =
      Fin.cast hys.length_eq i := by
  simp [constructionLineIndex, alonLeftIndex]

@[simp] theorem constructionLineIndex_right {q : ℕ} (π : ProjectivePlane q)
    {ys : List ℕ} (hys : AdmissibleHead q ys)
    (i : Fin (twoBlockCount q ys)) :
    constructionLineIndex π hys (alonRightIndex q ys i) =
      Fin.cast hys.length_eq ((missingPairEquiv π hys).symm i).1 := by
  simp [constructionLineIndex, alonRightIndex]

theorem constructionBlock_subset_line {q : ℕ} (π : ProjectivePlane q)
    {ys : List ℕ} (hys : AdmissibleHead q ys)
    (i : Fin (AlonList q ys).length) :
    constructionBlock π hys i ⊆ π.line (constructionLineIndex π hys i) := by
  by_cases hi : i.1 < ys.length
  · have hidx : i = alonLeftIndex q ys ⟨i.1, hi⟩ := by
      ext
      simp [alonLeftIndex, AlonList, Fin.cast, List.get_eq_getElem]
    rw [hidx, constructionBlock_left, constructionLineIndex_left]
    exact chosenLineSubset_subset π hys ⟨i.1, hi⟩
  · let j : Fin (twoBlockCount q ys) := ⟨i.1 - ys.length, by
      have hlen : i.1 < ys.length + twoBlockCount q ys := by
        simpa [alonList_length] using i.2
      omega⟩
    have hidx : i = alonRightIndex q ys j := by
      ext
      simp [alonRightIndex, AlonList, Fin.cast, j]
      omega
    rw [hidx, constructionBlock_right, constructionLineIndex_right]
    exact (Finset.mem_powersetCard.1 (Finset.mem_sdiff.1
      ((missingPairEquiv π hys).symm j).2.2).1).1

theorem finset_eq_pair_of_card_two_of_mem {α : Type} [DecidableEq α]
    {s : Finset α} {a b : α} (hs : s.card = 2)
    (ha : a ∈ s) (hb : b ∈ s) (hab : a ≠ b) :
    s = {a, b} := by
  have hsubset : ({a, b} : Finset α) ⊆ s := by
    intro x hx
    rw [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact ha
    · exact hb
  exact (Finset.eq_of_subset_of_card_le hsubset (by
    rw [hs, Finset.card_pair hab])).symm

theorem constructionLineIndex_unique_of_pair_mem {q : ℕ} (π : ProjectivePlane q)
    {ys : List ℕ} (hys : AdmissibleHead q ys)
    {a b : π.Point} (hab : a ≠ b)
    {lineIdx : Fin (q ^ 2 + q + 1)}
    (hline : a ∈ π.line lineIdx ∧ b ∈ π.line lineIdx)
    {i : Fin (AlonList q ys).length}
    (hi : a ∈ constructionBlock π hys i ∧ b ∈ constructionBlock π hys i) :
    constructionLineIndex π hys i = lineIdx := by
  rcases π.pair_unique_line hab with ⟨_, _, huniq⟩
  exact (huniq (constructionLineIndex π hys i)
    ⟨constructionBlock_subset_line π hys i hi.1,
      constructionBlock_subset_line π hys i hi.2⟩).trans
    (huniq lineIdx hline).symm

@[simp] theorem alonList_get_leftIndex {q : ℕ} {ys : List ℕ}
    (i : Fin ys.length) :
    (AlonList q ys).get (alonLeftIndex q ys i) = ys.get i := by
  simp [alonLeftIndex, AlonList, Fin.cast, List.get_eq_getElem]

@[simp] theorem alonList_get_rightIndex {q : ℕ} {ys : List ℕ}
    (i : Fin (twoBlockCount q ys)) :
    (AlonList q ys).get (alonRightIndex q ys i) = 2 := by
  simp [alonRightIndex, AlonList, Fin.cast, List.get_eq_getElem]

theorem constructionBlock_card {q : ℕ} (π : ProjectivePlane q)
    {ys : List ℕ} (hys : AdmissibleHead q ys)
    (i : Fin (AlonList q ys).length) :
    (constructionBlock π hys i).card = (AlonList q ys).get i := by
  by_cases hi : i.1 < ys.length
  · have hidx : i = alonLeftIndex q ys ⟨i.1, hi⟩ := by
      ext
      simp [alonLeftIndex, AlonList, Fin.cast, List.get_eq_getElem]
    rw [hidx, constructionBlock_left, alonList_get_leftIndex]
    exact chosenLineSubset_card π hys ⟨i.1, hi⟩
  · have hi' : ys.length ≤ i.1 := Nat.le_of_not_gt hi
    let j : Fin (twoBlockCount q ys) := ⟨i.1 - ys.length, by
      have hlen : i.1 < ys.length + twoBlockCount q ys := by
        simpa [alonList_length] using i.2
      omega⟩
    have hidx : i = alonRightIndex q ys j := by
      ext
      simp [alonRightIndex, AlonList, Fin.cast, j]
      omega
    rw [hidx, constructionBlock_right, alonList_get_rightIndex]
    have hmem := ((missingPairEquiv π hys).symm j).2.2
    exact (Finset.mem_powersetCard.1 (Finset.mem_sdiff.1 hmem).1).2

theorem pair_subset_iff {α : Type} [DecidableEq α]
    {a b : α} {s : Finset α} :
    ({a, b} : Finset α) ⊆ s ↔ a ∈ s ∧ b ∈ s := by
  constructor
  · intro h
    exact ⟨h (by simp), h (by simp)⟩
  · intro h x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact h.1
    · exact h.2

theorem missingPairIndex_ext {q : ℕ} (π : ProjectivePlane q)
    {ys : List ℕ} (hys : AdmissibleHead q ys)
    {x y : MissingPairIndex π hys}
    (hfst : x.1 = y.1) (hsnd : x.2.1 = y.2.1) :
    x = y := by
  cases x with
  | mk xi xp =>
      cases y with
      | mk yi yp =>
          dsimp at hfst hsnd
          subst yi
          cases xp with
          | mk xv hxv =>
              cases yp with
              | mk yv hyv =>
                  dsimp at hsnd
                  subst yv
                  rfl

theorem eq_alonLeftIndex_of_cast_eq {q : ℕ} {ys : List ℕ}
    {i : Fin (AlonList q ys).length} {j : Fin ys.length}
    (h : Fin.cast (alonList_length q ys) i =
      Fin.castAdd (twoBlockCount q ys) j) :
    i = alonLeftIndex q ys j := by
  have h' := congrArg (Fin.cast (alonList_length q ys).symm) h
  simpa [alonLeftIndex] using h'

theorem eq_alonRightIndex_of_cast_eq {q : ℕ} {ys : List ℕ}
    {i : Fin (AlonList q ys).length} {j : Fin (twoBlockCount q ys)}
    (h : Fin.cast (alonList_length q ys) i =
      Fin.natAdd ys.length j) :
    i = alonRightIndex q ys j := by
  have h' := congrArg (Fin.cast (alonList_length q ys).symm) h
  simpa [alonRightIndex] using h'

theorem constructionIndex_cases {q : ℕ} {ys : List ℕ}
    {P : Fin (AlonList q ys).length → Prop}
    (hleft : ∀ i : Fin ys.length, P (alonLeftIndex q ys i))
    (hright : ∀ i : Fin (twoBlockCount q ys), P (alonRightIndex q ys i))
    (i : Fin (AlonList q ys).length) : P i := by
  change P (Fin.cast (alonList_length q ys).symm
    (Fin.cast (alonList_length q ys) i))
  induction Fin.cast (alonList_length q ys) i using Fin.addCases with
  | left j =>
      simpa [alonLeftIndex] using hleft j
  | right j =>
      simpa [alonRightIndex] using hright j

def headIndexOfLine {q : ℕ} {ys : List ℕ}
    (hys : AdmissibleHead q ys) (i : Fin (q ^ 2 + q + 1)) :
    Fin ys.length :=
  Fin.cast hys.length_eq.symm i

@[simp] theorem headIndexOfLine_cast {q : ℕ} {ys : List ℕ}
    (hys : AdmissibleHead q ys) (i : Fin (q ^ 2 + q + 1)) :
    Fin.cast hys.length_eq (headIndexOfLine hys i) = i := by
  simp [headIndexOfLine]

theorem eq_headIndexOfLine_of_cast_eq {q : ℕ} {ys : List ℕ}
    (hys : AdmissibleHead q ys) {i : Fin ys.length}
    {j : Fin (q ^ 2 + q + 1)}
    (h : Fin.cast hys.length_eq i = j) :
    i = headIndexOfLine hys j := by
  have h' := congrArg (Fin.cast hys.length_eq.symm) h
  simpa [headIndexOfLine] using h'

theorem constructionBlock_unique_left {q : ℕ} (π : ProjectivePlane q)
    {ys : List ℕ} (hys : AdmissibleHead q ys)
    {a b : π.Point} (hab : a ≠ b)
    {lineIdx : Fin (q ^ 2 + q + 1)}
    (hline : a ∈ π.line lineIdx ∧ b ∈ π.line lineIdx)
    (hchosen :
      ({a, b} : Finset π.Point) ⊆
        chosenLineSubset π hys (headIndexOfLine hys lineIdx))
    {i : Fin (AlonList q ys).length}
    (hi : a ∈ constructionBlock π hys i ∧ b ∈ constructionBlock π hys i) :
    i = alonLeftIndex q ys (headIndexOfLine hys lineIdx) := by
  refine constructionIndex_cases (q := q) (ys := ys)
    (P := fun i =>
      a ∈ constructionBlock π hys i ∧ b ∈ constructionBlock π hys i →
        i = alonLeftIndex q ys (headIndexOfLine hys lineIdx))
    ?_ ?_ i hi
  · intro j hleft
    have hlinej :
        Fin.cast hys.length_eq j = lineIdx :=
      by
        have h := constructionLineIndex_unique_of_pair_mem π hys hab hline
          (i := alonLeftIndex q ys j) hleft
        simpa [constructionLineIndex_left] using h
    have hj : j = headIndexOfLine hys lineIdx :=
      eq_headIndexOfLine_of_cast_eq hys hlinej
    rw [hj]
  · intro j hright
    have hlinej :
        Fin.cast hys.length_eq ((missingPairEquiv π hys).symm j).1 = lineIdx :=
      by
        have h := constructionLineIndex_unique_of_pair_mem π hys hab hline
          (i := alonRightIndex q ys j) hright
        simpa [constructionLineIndex_right] using h
    have hright_pair :
        a ∈ ((missingPairEquiv π hys).symm j).2.1 ∧
          b ∈ ((missingPairEquiv π hys).symm j).2.1 := by
      simpa [constructionBlock_right] using hright
    have hj :
        ((missingPairEquiv π hys).symm j).1 = headIndexOfLine hys lineIdx :=
      eq_headIndexOfLine_of_cast_eq hys hlinej
    have hpair :
        ((missingPairEquiv π hys).symm j).2.1 = ({a, b} : Finset π.Point) := by
      apply finset_eq_pair_of_card_two_of_mem
      · exact (Finset.mem_powersetCard.1 (Finset.mem_sdiff.1
          ((missingPairEquiv π hys).symm j).2.2).1).2
      · exact hright_pair.1
      · exact hright_pair.2
      · exact hab
    have hnot :
        ((missingPairEquiv π hys).symm j).2.1 ∉
          (chosenLineSubset π hys ((missingPairEquiv π hys).symm j).1).powersetCard 2 :=
      (Finset.mem_sdiff.1 ((missingPairEquiv π hys).symm j).2.2).2
    have hmemChosen :
        ((missingPairEquiv π hys).symm j).2.1 ∈
          (chosenLineSubset π hys ((missingPairEquiv π hys).symm j).1).powersetCard 2 := by
      rw [hpair, hj]
      exact Finset.mem_powersetCard.2
        ⟨hchosen, Finset.card_pair hab⟩
    exact (hnot hmemChosen).elim

theorem constructionBlock_unique_right {q : ℕ} (π : ProjectivePlane q)
    {ys : List ℕ} (hys : AdmissibleHead q ys)
    {a b : π.Point} (hab : a ≠ b)
    {lineIdx : Fin (q ^ 2 + q + 1)}
    (hline : a ∈ π.line lineIdx ∧ b ∈ π.line lineIdx)
    (hnotChosen :
      ¬ ({a, b} : Finset π.Point) ⊆
        chosenLineSubset π hys (headIndexOfLine hys lineIdx))
    (mp : MissingPairIndex π hys)
    (hmp_fst : mp.1 = headIndexOfLine hys lineIdx)
    (hmp_pair : mp.2.1 = ({a, b} : Finset π.Point))
    {i : Fin (AlonList q ys).length}
    (hi : a ∈ constructionBlock π hys i ∧ b ∈ constructionBlock π hys i) :
    i = alonRightIndex q ys (missingPairEquiv π hys mp) := by
  refine constructionIndex_cases (q := q) (ys := ys)
    (P := fun i =>
      a ∈ constructionBlock π hys i ∧ b ∈ constructionBlock π hys i →
        i = alonRightIndex q ys (missingPairEquiv π hys mp))
    ?_ ?_ i hi
  · intro j hleft
    have hlinej :
        Fin.cast hys.length_eq j = lineIdx :=
      by
        have h := constructionLineIndex_unique_of_pair_mem π hys hab hline
          (i := alonLeftIndex q ys j) hleft
        simpa [constructionLineIndex_left] using h
    have hleft_pair :
        a ∈ chosenLineSubset π hys j ∧ b ∈ chosenLineSubset π hys j := by
      simpa [constructionBlock_left] using hleft
    have hj : j = headIndexOfLine hys lineIdx :=
      eq_headIndexOfLine_of_cast_eq hys hlinej
    have hsubset :
        ({a, b} : Finset π.Point) ⊆
          chosenLineSubset π hys (headIndexOfLine hys lineIdx) := by
      rw [← hj]
      exact pair_subset_iff.2 hleft_pair
    exact (hnotChosen hsubset).elim
  · intro j hright
    have hlinej :
        Fin.cast hys.length_eq ((missingPairEquiv π hys).symm j).1 = lineIdx :=
      by
        have h := constructionLineIndex_unique_of_pair_mem π hys hab hline
          (i := alonRightIndex q ys j) hright
        simpa [constructionLineIndex_right] using h
    have hright_pair :
        a ∈ ((missingPairEquiv π hys).symm j).2.1 ∧
          b ∈ ((missingPairEquiv π hys).symm j).2.1 := by
      simpa [constructionBlock_right] using hright
    have hj :
        ((missingPairEquiv π hys).symm j).1 = headIndexOfLine hys lineIdx :=
      eq_headIndexOfLine_of_cast_eq hys hlinej
    have hpair :
        ((missingPairEquiv π hys).symm j).2.1 = ({a, b} : Finset π.Point) := by
      apply finset_eq_pair_of_card_two_of_mem
      · exact (Finset.mem_powersetCard.1 (Finset.mem_sdiff.1
          ((missingPairEquiv π hys).symm j).2.2).1).2
      · exact hright_pair.1
      · exact hright_pair.2
      · exact hab
    have hmp_eq : (missingPairEquiv π hys).symm j = mp := by
      apply missingPairIndex_ext π hys
      · rw [hj, hmp_fst]
      · rw [hpair, hmp_pair]
    have hj_eq : j = missingPairEquiv π hys mp := by
      rw [← hmp_eq]
      simp
    rw [hj_eq]

theorem alonList_is_sequence
    (q : ℕ) (ys : List ℕ) (hys : AdmissibleHead q ys) :
    ErdosSequence (q ^ 2 + q + 1) (AlonList q ys) := by
  constructor
  · intro i j hij
    by_cases hi : i.1 < ys.length
    · by_cases hj : j.1 < ys.length
      · rw [alonList_get_left i hi, alonList_get_left j hj]
        exact hys.nonincreasing ⟨i.1, hi⟩ ⟨j.1, hj⟩ hij
      · rw [alonList_get_left i hi, alonList_get_right j (Nat.le_of_not_gt hj)]
        have hbound := hys.bounds ⟨i.1, hi⟩
        omega
    · rw [alonList_get_right i (Nat.le_of_not_gt hi),
        alonList_get_right j (le_trans (Nat.le_of_not_gt hi) hij)]
  · intro i
    by_cases hi : i.1 < ys.length
    · rw [alonList_get_left i hi]
      have hbound := hys.bounds ⟨i.1, hi⟩
      have hq : 2 ≤ q ^ 2 + q + 1 := hys.two_le_order
      omega
    · rw [alonList_get_right i (Nat.le_of_not_gt hi)]
      exact ⟨by omega, hys.two_le_order⟩

theorem alon_blockCompatible_of_admissible
    (q : ℕ) (π : ProjectivePlane q) (ys : List ℕ)
    (hys : AdmissibleHead q ys) :
    BlockCompatible (q ^ 2 + q + 1) (AlonList q ys) := by
  refine ⟨π.Point, inferInstance, inferInstance, ?_, ?_⟩
  · exact π.card_points
  · refine ⟨
      { block := constructionBlock π hys
        block_card_ge_two := ?_
        pair_unique := ?_ }, ?_⟩
    · intro i
      rw [constructionBlock_card π hys i]
      exact (alonList_is_sequence q ys hys).2 i |>.1
    · intro a b hab
      classical
      rcases π.pair_unique_line hab with ⟨lineIdx, hline, _hline_unique⟩
      let headIdx : Fin ys.length := headIndexOfLine hys lineIdx
      have hline_head : Fin.cast hys.length_eq headIdx = lineIdx := by
        simp [headIdx]
      let pair : Finset π.Point := {a, b}
      have hpair_card : pair.card = 2 := by
        simp [pair, Finset.card_pair hab]
      by_cases hchosen :
          a ∈ chosenLineSubset π hys headIdx ∧
            b ∈ chosenLineSubset π hys headIdx
      · let witness : Fin (AlonList q ys).length :=
          alonLeftIndex q ys headIdx
        refine ExistsUnique.intro witness ?_ ?_
        · simpa [witness] using hchosen
        · intro candidate hcandidate
          have hsubset : pair ⊆ chosenLineSubset π hys (headIndexOfLine hys lineIdx) :=
            pair_subset_iff.2 hchosen
          simpa [witness] using
            constructionBlock_unique_left π hys hab hline hsubset hcandidate
      · have hpair_line :
            pair ∈ (π.line (Fin.cast hys.length_eq headIdx)).powersetCard 2 := by
          exact Finset.mem_powersetCard.2
            ⟨by
                rw [hline_head]
                exact pair_subset_iff.2 hline,
              hpair_card⟩
        have hpair_not_chosen :
            pair ∉ (chosenLineSubset π hys headIdx).powersetCard 2 := by
          intro hp
          exact hchosen (pair_subset_iff.1 (Finset.mem_powersetCard.1 hp).1)
        have hmissing : pair ∈ missingPairs π hys headIdx := by
          exact Finset.mem_sdiff.2 ⟨hpair_line, hpair_not_chosen⟩
        let missingIdx : MissingPairIndex π hys :=
          ⟨headIdx, ⟨pair, hmissing⟩⟩
        let witness : Fin (AlonList q ys).length :=
          alonRightIndex q ys ((missingPairEquiv π hys) missingIdx)
        refine ExistsUnique.intro witness ?_ ?_
        · have hmissing_apply :
              (missingPairEquiv π hys).symm
                ((missingPairEquiv π hys) missingIdx) = missingIdx := by
            exact Equiv.symm_apply_apply (missingPairEquiv π hys) missingIdx
          rw [constructionBlock_right, hmissing_apply]
          simp [missingIdx, pair]
        · intro candidate hcandidate
          have hnotSubset :
              ¬ pair ⊆ chosenLineSubset π hys (headIndexOfLine hys lineIdx) := by
            intro hsub
            exact hchosen (pair_subset_iff.1 (by simpa [pair, headIdx] using hsub))
          have hmp_fst : missingIdx.1 = headIndexOfLine hys lineIdx := by
            simp [missingIdx, headIdx]
          have hmp_pair : missingIdx.2.1 = pair := by
            simp [missingIdx]
          simpa [witness] using
            constructionBlock_unique_right π hys hab hline hnotSubset missingIdx
              hmp_fst hmp_pair hcandidate
    · intro i
      exact constructionBlock_card π hys i

theorem theorem_2_3
    (q : ℕ) (π : ProjectivePlane q) (ys : List ℕ)
    (hys : AdmissibleHead q ys) :
    BlockCompatibleSequence (q ^ 2 + q + 1) (AlonList q ys) := by
  constructor
  · exact alonList_is_sequence q ys hys
  · exact alon_blockCompatible_of_admissible q π ys hys

end P732
end ErdosProblems
