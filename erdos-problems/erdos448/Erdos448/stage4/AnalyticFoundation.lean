module

import all Mathlib.Basic.Real.Basic
public import Erdos448.stage4.RootObjects

public section

set_option backward.isDefEq.respectTransparency false

/-!
Witness-bearing interfaces for the closed analytic estimates used by the
P-053, P-068, and P-069 contracts.

These structures do not assert any theorem.  They expose the exact constants
and uniform bound families that a separate foundation proof must construct.
-/

namespace Erdos448.Stage4.Contracts

open Finset
open scoped BigOperators

noncomputable section

/-- P-053 is closed mathematics whose Lean proof belongs to a new foundation task. -/
@[expose] def P053ProviderClassification : ProviderClass := .newFoundationRequired

/-- P-068 is closed mathematics whose Lean proof belongs to a new foundation task. -/
@[expose] def P068ProviderClassification : ProviderClass := .newFoundationRequired

/-- P-069 is closed mathematics whose Lean proof belongs to a new foundation task. -/
@[expose] def P069ProviderClassification : ProviderClass := .newFoundationRequired

@[expose] def safeLogHalfSum (z : ℝ) : ℝ :=
  ∑ m ∈ positiveNatsBelow z, (safeLog m).rpow (-1 / 2)

/-- Foundation provider for the endpoint-safe logarithmic partial sum.
The absolute constant is selected before the uniform endpoint `M`. -/
structure P053FoundationProvider where
  Cps : ℝ
  Cps_pos : 0 < Cps
  bound : ∀ M : ℝ, 0 < M →
    safeLogHalfSum M ≤ Cps * M * (safeLog (2 * M)).rpow (-1 / 2)

/-- Foundation provider for the absolute `A` beta-convolution estimate.
The absolute constant is selected before every parameter package and endpoint. -/
structure P068FoundationProvider where
  CA : ℝ
  CA_pos : 0 < CA
  bound : ∀ q : WeightParameters, ∀ x : ℝ,
    q.theta ^ (2 * q.k - 1) < x →
      convolutionA q x ≤
        CA * (x / q.theta ^ (2 * q.k)) *
          (q.k : ℝ).rpow ((q.y - 1) / 2)

/-- Both distinct middle-convolution subjects share the same absolute witness
and the same explicit `1 / y` loss. -/
structure P069MiddleConvolutionBounds (Cmc : ℝ) : Prop where
  sharp : ∀ q : WeightParameters, ∀ x : ℝ,
    q.theta ^ (2 * q.k - 1) < x →
      convolutionBSharp q x ≤
        (Cmc / q.y) * (x / q.theta ^ (2 * q.k)) *
          (safeLog (2 * x * q.theta ^ (1 - (2 : ℤ) * q.k))).rpow
            ((q.y - 1) / 2)
  enlarged : ∀ q : WeightParameters, ∀ x : ℝ,
    q.theta ^ (2 * q.k - 1) < x →
      convolutionBEnlarged q x ≤
        (Cmc / q.y) * (x / q.theta ^ (2 * q.k)) *
          (safeLog (2 * x * q.theta ^ (1 - (2 : ℤ) * q.k))).rpow
            ((q.y - 1) / 2)

/-- Foundation provider for both exact R3 middle-convolution estimates.
One absolute constant controls both subjects without identifying them. -/
structure P069FoundationProvider where
  Cmc : ℝ
  Cmc_pos : 0 < Cmc
  bounds : P069MiddleConvolutionBounds Cmc

end

end Erdos448.Stage4.Contracts
