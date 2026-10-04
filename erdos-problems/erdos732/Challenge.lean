module

public import Mathlib

@[expose] public section

/-!
Erdős problem 732: an absolute exponential lower bound on the number of
nonincreasing block-size lists realized by pairwise balanced designs.
Every pair of distinct points belongs to exactly one block; blocks have size
at least two. Lists, rather than labeled designs, are counted.
-/

noncomputable section
open scoped Filter

namespace ErdosProblems.P732

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

end ErdosProblems.P732

/-- Alon's affirmative answer to Problem 1.2 (Erdős 732), with natural logarithm. -/
theorem ErdosProblems.P732.Palomar.erdos732_yes :
    ∃ c : ℝ, 0 < c ∧
      ∀ᶠ n : ℕ in Filter.atTop,
        Real.exp (c * Real.sqrt (n : ℝ) * Real.log (n : ℝ))
          ≤ (Set.ncard {xs : List ℕ | ErdosProblems.P732.BlockCompatibleSequence n xs} : ℝ) := by
  sorry
