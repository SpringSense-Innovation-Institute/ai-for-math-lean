module

import all Mathlib.Basic.Real.Basic
public import Mathlib

public section

set_option backward.isDefEq.respectTransparency false

/-!
Lean-facing representation surface for the S3 authority of Erdos Problem 448.

This file deliberately contains definitions and specification interfaces only.
It introduces no theorem axiom and proves no S3 proposition.  S7 tasks construct
the theorem terms; cross-task use is through local parameters until S8 links the
real providers.
-/

namespace Erdos448.Stage4

open Filter Finset Set
open scoped BigOperators Topology

noncomputable section

/-- Positive natural numbers are the default integer domain in the S3 authority. -/
@[expose] abbrev PosNat := {n : ℕ // 0 < n}

/-- D-001: positive divisors, represented by `Nat.divisors`. -/
@[expose] def divisorSet (n : PosNat) : Finset ℕ := n.1.divisors

/-- D-001: divisor count. -/
@[expose] def tau (n : PosNat) : ℕ := (divisorSet n).card

/-- D-002: `P⁻(n) ≥ s`, written without an artificial infinity value at `n = 1`. -/
@[expose] def IsRough (n : ℕ) (s : ℝ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ n → s ≤ p

/-- D-002: the roughness indicator, total on all inputs and used on the S3 domain `s ≥ 2`. -/
@[expose] def roughIndicator (n : ℕ) (s : ℝ) : ℕ :=
  by
    classical
    exact if IsRough n s then 1 else 0

/-- D-002: rough-divisor count. -/
@[expose] def roughTau (n : PosNat) (s : ℝ) : ℕ :=
  ∑ d ∈ divisorSet n, roughIndicator d s

/-- D-003: truncated prime-factor count with multiplicity and strict cutoff. -/
@[expose] def omegaBelow (n : PosNat) (u : ℝ) : ℕ :=
  ∑ p ∈ n.1.primeFactors, if (p : ℝ) < u then n.1.factorization p else 0

/-- D-004: the exact half-open multiplicative-bin predicate. -/
@[expose] def OccupiesBin (n : PosNat) (theta : ℝ) (k : ℕ) : Prop :=
  ∃ d ∈ divisorSet n,
    theta ^ k ≤ (d : ℝ) ∧ (d : ℝ) < theta ^ (k + 1)

/-- D-004: a finite representation of the occupied bins.

On the intended domain `theta > 1`, an occupied index is at most
`ceil (log n / log theta)`.  Outside that domain the S3 definition has no
contract, so the total Lean value is the empty finset.
-/
@[expose] def occupiedBins (n : PosNat) (theta : ℝ) : Finset ℕ :=
  by
    classical
    exact if 1 < theta then
      (Finset.range (Nat.ceil (Real.log n.1 / Real.log theta) + 1)).filter
        fun k => OccupiesBin n theta k
    else ∅

/-- D-004: occupied-bin count. -/
@[expose] def tauPlus (n : PosNat) (theta : ℝ) : ℕ :=
  (occupiedBins n theta).card

/-- D-005: ordered, unequal, strict close-pair relation. -/
@[expose] def Close (theta : ℝ) (d d' : PosNat) : Prop :=
  d ≠ d' ∧ 1 / theta < (d'.1 : ℝ) / d.1 ∧ (d'.1 : ℝ) / d.1 < theta

/-- D-006: count positive integers in `[1,x)` satisfying `A`. -/
@[expose] def prefixCount (A : Set ℕ) (x : ℕ) : ℕ :=
  by
    classical
    exact ((Finset.range x).filter fun n => 0 < n ∧ n ∈ A).card

/-- D-006: normalized positive-integer prefix count.  Division at `x=0` is
total in Lean; all asymptotic contracts use the `atTop` tail. -/
@[expose] def prefixDensity (A : Set ℕ) (x : ℕ) : ℝ :=
  (prefixCount A x : ℝ) / x

/-- Natural density, used to formalize "for almost all positive integers". -/
@[expose] def HasNaturalDensity (A : Set ℕ) (delta : ℝ) : Prop :=
  Tendsto (prefixDensity A) atTop (nhds delta)

/-- The inequality characterization of `limsup ≤ c` needed by the audited proof. -/
@[expose] def UpperDensityAtMost (A : Set ℕ) (c : ℝ) : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon →
    ∀ᶠ x : ℕ in atTop, prefixDensity A x ≤ c + epsilon

/-- The exact consequence used at P-120: upper density is strictly below one. -/
@[expose] def UpperDensityLtOne (A : Set ℕ) : Prop :=
  ∃ c : ℝ, c < 1 ∧ UpperDensityAtMost A c

/-- D-006: safe logarithm. -/
@[expose] def safeLog (t : ℝ) : ℝ := max 1 (Real.log t)

/-- D-022: the non-strict event used by Theorem 1. -/
@[expose] def densityEvent (alpha : ℝ) : Set ℕ :=
  {n | if hn : 0 < n then
      (tauPlus ⟨n, hn⟩ 2 : ℝ) ≤ alpha * tau ⟨n, hn⟩
    else False}

/-- P-120/FT-448-NEG-017: the strict event in the literal problem. -/
@[expose] def strictEvent (epsilon : ℝ) : Set ℕ :=
  {n | if hn : 0 < n then
      (tauPlus ⟨n, hn⟩ 2 : ℝ) < epsilon * tau ⟨n, hn⟩
    else False}

/-- The user-facing universal almost-all assertion, with the positive epsilon
domain and strict inequality preserved. -/
@[expose] def OriginalClaim : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon → HasNaturalDensity (strictEvent epsilon) 1

/-- FT-448-NEG-017: literal negative answer. -/
@[expose] def NegativeAnswer : Prop := ¬ OriginalClaim

/-- P-117's witness-bearing interface.  The constant is selected after
`delta` and before every `alpha`. -/
structure InteriorDensityBound (delta : ℝ) where
  constant : ℝ
  constant_pos : 0 < constant
  bound : ∀ alpha : ℝ, 0 < alpha → alpha ≤ 1 →
    UpperDensityAtMost (densityEvent alpha) (constant * alpha ^ (1 - delta))

/-- P-120's shared witness interface; S8 must use this same epsilon in the
strict event and in the instantiation that refutes `OriginalClaim`. -/
structure CounterexampleWitness where
  epsilon : ℝ
  epsilon_pos : 0 < epsilon
  strict_event_small : UpperDensityLtOne (strictEvent epsilon)

/-- Frozen witness interface for contracts whose existential data must remain
identical across task boundaries. -/
structure WitnessWithSpec (α : Type*) (Spec : α → Prop) where
  witness : α
  specification : Spec witness

/-- Frozen two-sided positive comparison constants, selected before their
uniform variables. -/
structure PositiveComparison where
  lower : ℝ
  upper : ℝ
  lower_pos : 0 < lower
  upper_pos : 0 < upper

/-- Provider classifications fixed by S4. -/
inductive ProviderClass
  | project
  | mathMinerFoundation
  | mathlib
  | externalLean
  | newFoundationRequired
  | authorizedTrustBoundary
  deriving DecidableEq, Repr

end

end Erdos448.Stage4
