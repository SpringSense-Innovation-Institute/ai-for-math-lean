module

public import Mathlib

@[expose] public section

/-!
# Negative resolution of Erdős problem 448

For a positive integer n, tau is its divisor count and tauPlus counts the
occupied dyadic intervals [2^k, 2^(k+1)). Only k >= 0 can be occupied by a
positive integer divisor. The finite range includes every occupied interval.
Natural density counts positive integers below x and divides by x; changing
the endpoint or including zero does not change the limiting density.
The claim refuted below uses a strict inequality for every positive epsilon.

Source: Erdős–Tenenbaum, Sur la structure de la suite des diviseurs d'un entier,
selected pages 18–19 and 22–32; see docs/selected-source-pages.md.
-/

namespace Erdos448.Stage4

open Filter Finset Set
open scoped BigOperators Topology

noncomputable section

abbrev PosNat := {n : ℕ // 0 < n}

def divisorSet (n : PosNat) : Finset ℕ := n.1.divisors

def tau (n : PosNat) : ℕ := (divisorSet n).card

def OccupiesBin (n : PosNat) (theta : ℝ) (k : ℕ) : Prop :=
  ∃ d ∈ divisorSet n,
    theta ^ k ≤ (d : ℝ) ∧ (d : ℝ) < theta ^ (k + 1)

def occupiedBins (n : PosNat) (theta : ℝ) : Finset ℕ :=
  by
    classical
    exact if 1 < theta then
      (Finset.range (Nat.ceil (Real.log n.1 / Real.log theta) + 1)).filter
        fun k => OccupiesBin n theta k
    else ∅

def tauPlus (n : PosNat) (theta : ℝ) : ℕ :=
  (occupiedBins n theta).card

def prefixCount (A : Set ℕ) (x : ℕ) : ℕ :=
  by
    classical
    exact ((Finset.range x).filter fun n => 0 < n ∧ n ∈ A).card

def prefixDensity (A : Set ℕ) (x : ℕ) : ℝ :=
  (prefixCount A x : ℝ) / x

def HasNaturalDensity (A : Set ℕ) (delta : ℝ) : Prop :=
  Tendsto (prefixDensity A) atTop (nhds delta)

def strictEvent (epsilon : ℝ) : Set ℕ :=
  {n | if hn : 0 < n then
      (tauPlus ⟨n, hn⟩ 2 : ℝ) < epsilon * tau ⟨n, hn⟩
    else False}

def OriginalClaim : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon → HasNaturalDensity (strictEvent epsilon) 1

def NegativeAnswer : Prop := ¬ OriginalClaim

end
end Erdos448.Stage4

/-- The strict small-divisor-ratio assertion does not hold for every epsilon. -/
theorem Erdos448.negativeAnswer : Erdos448.Stage4.NegativeAnswer := by
  sorry
