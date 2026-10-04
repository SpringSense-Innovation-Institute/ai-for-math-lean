module

public import Mathlib

@[expose] public section

noncomputable section

namespace ErdosProblems
namespace P732

/-! Basic definitions for block-compatible sequences in Erdős problem #732. -/

structure PairwiseBalancedDesign (α : Type) [Fintype α] [DecidableEq α]
    (m : ℕ) where
  block : Fin m → Finset α
  block_card_ge_two : ∀ i : Fin m, 2 ≤ (block i).card
  pair_unique :
    ∀ ⦃a b : α⦄, a ≠ b →
      ∃! i : Fin m, a ∈ block i ∧ b ∈ block i

def BlockCompatible (n : ℕ) (xs : List ℕ) : Prop :=
  ∃ (α : Type) (instF : Fintype α) (instD : DecidableEq α),
    letI : Fintype α := instF
    letI : DecidableEq α := instD
    Fintype.card α = n ∧
      ∃ D : PairwiseBalancedDesign α xs.length,
        ∀ i : Fin xs.length, (D.block i).card = xs.get i

def Nonincreasing (xs : List ℕ) : Prop :=
  ∀ i j : Fin xs.length, i ≤ j → xs.get i ≥ xs.get j

def ErdosSequence (n : ℕ) (xs : List ℕ) : Prop :=
  Nonincreasing xs ∧
    ∀ i : Fin xs.length, 2 ≤ xs.get i ∧ xs.get i ≤ n

def BlockCompatibleSequence (n : ℕ) (xs : List ℕ) : Prop :=
  ErdosSequence n xs ∧ BlockCompatible n xs

private theorem PairwiseBalancedDesign.exists_pair_in_block
    {α : Type} [Fintype α] [DecidableEq α] {m : ℕ}
    (D : PairwiseBalancedDesign α m) (i : Fin m) :
    ∃ p : α × α, p.1 ∈ D.block i ∧ p.2 ∈ D.block i ∧ p.1 ≠ p.2 := by
  have h : 1 < (D.block i).card := by
    have htwo := D.block_card_ge_two i
    exact htwo
  rcases Finset.one_lt_card.1 h with ⟨a, ha, b, hb, hab⟩
  exact ⟨(a, b), ha, hb, hab⟩

theorem PairwiseBalancedDesign.length_le_card_sq
    {α : Type} [Fintype α] [DecidableEq α] {m : ℕ}
    (D : PairwiseBalancedDesign α m) :
    m ≤ Fintype.card α * Fintype.card α := by
  classical
  let chosenPair (i : Fin m) : α × α :=
    Classical.choose (D.exists_pair_in_block i)
  have chosenPair_spec (i : Fin m) :
      (chosenPair i).1 ∈ D.block i ∧
        (chosenPair i).2 ∈ D.block i ∧
        (chosenPair i).1 ≠ (chosenPair i).2 := by
    dsimp [chosenPair]
    exact Classical.choose_spec (D.exists_pair_in_block i)
  have hinj : Function.Injective chosenPair := by
    intro i j hij
    have hi := chosenPair_spec i
    have hj := chosenPair_spec j
    have hfirst : (chosenPair i).1 = (chosenPair j).1 := congrArg Prod.fst hij
    have hsecond : (chosenPair i).2 = (chosenPair j).2 := congrArg Prod.snd hij
    rcases D.pair_unique hi.2.2 with ⟨k, _hk, huniq⟩
    have hik : i = k := huniq i ⟨hi.1, hi.2.1⟩
    have hjk : j = k := huniq j ⟨by simpa [hfirst] using hj.1,
      by simpa [hsecond] using hj.2.1⟩
    exact hik.trans hjk.symm
  have hcard := Fintype.card_le_of_injective chosenPair hinj
  simpa using hcard

theorem BlockCompatible.length_le_sq {n : ℕ} {xs : List ℕ}
    (h : BlockCompatible n xs) :
    xs.length ≤ n * n := by
  rcases h with ⟨α, instF, instD, hcard, D, _hblocks⟩
  letI : Fintype α := instF
  letI : DecidableEq α := instD
  simpa [hcard] using D.length_le_card_sq

private theorem finite_list_nat_length_le_entries_le (n L : ℕ) :
    {xs : List ℕ | xs.length ≤ L ∧ ∀ i : Fin xs.length, xs.get i ≤ n}.Finite := by
  classical
  let f : (Σ k : Fin (L + 1), List.Vector (Fin (n + 1)) k.1) → List ℕ :=
    fun t => t.2.toList.map (fun x : Fin (n + 1) => x.1)
  refine (Set.finite_range f).subset ?_
  intro xs hxs
  rcases hxs with ⟨hlen, hle⟩
  let ys : List (Fin (n + 1)) :=
    xs.attach.map fun x =>
      ⟨x.1, Nat.lt_succ_iff.mpr (by
        rcases List.mem_iff_get.mp x.2 with ⟨i, hi⟩
        have hb := hle i
        rw [hi] at hb
        exact hb)⟩
  refine ⟨⟨⟨xs.length, by omega⟩, ⟨ys, by simp [ys]⟩⟩, ?_⟩
  simp [f, ys]

theorem blockCompatibleSequence_finite (n : ℕ) :
    {xs : List ℕ | BlockCompatibleSequence n xs}.Finite := by
  refine (finite_list_nat_length_le_entries_le n (n * n)).subset ?_
  intro xs hxs
  exact ⟨hxs.2.length_le_sq, fun i => (hxs.1.2 i).2⟩

end P732
end ErdosProblems
