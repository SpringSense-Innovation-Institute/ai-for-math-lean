module

import all Mathlib.Basic.Real.Basic
public import Erdos448.stage4.contracts.GroupB
public import Erdos448.stage4.contracts.GroupC

public section

set_option backward.isDefEq.respectTransparency false

/-! Exact endpoint-indexed families for the scoped 448 wrap-up.
No existence, positivity, summability, or comparison theorem is asserted here.
All such facts are construction obligations discharged in CURRENT.md W2--W5
and formalized by ROOT01/ROOT06/ROOT09. In particular, `y` belongs to the
family index; it is not selected before a purported y-uniform constant. -/
namespace Erdos448.Stage4.WrapupFamilies
open Erdos448.Stage4 Erdos448.Stage4.Contracts
noncomputable section
local instance (p : Prop) : Decidable p := Classical.propDecidable p

structure RegularIndex where
  parameters : WeightParameters
  member : WeightMember
  regular : parameters.sigma ≤ parameters.theta ^ parameters.k
  z : ℝ
  z_ge_two : 2 ≤ z

@[expose] def regularEuler (q : RegularIndex) (p : ℕ) : ℝ :=
  localEulerFactor (selectedWeight q.parameters q.member)
    (modifierWeight q.parameters) p

@[expose] def regularMidCoefficient (q : RegularIndex) : ℝ := q.parameters.y / 2

@[expose] def regularHighCoefficient (_q : RegularIndex) : ℝ := 1 / 2

@[expose] def regularMidFactor (q : RegularIndex) (p : ℕ) : ℝ :=
  if q.parameters.sigma ≤ (p : ℝ) ∧
      (p : ℝ) < min q.z (q.parameters.theta ^ q.parameters.k) then
    regularEuler q p
  else 1 + q.parameters.y / (2 * (p : ℝ))

@[expose] def regularHighFactor (q : RegularIndex) (p : ℕ) : ℝ :=
  if q.parameters.theta ^ q.parameters.k ≤ (p : ℝ) ∧ (p : ℝ) < q.z then
    regularEuler q p
  else 1 + 1 / (2 * (p : ℝ))

structure TransitionIndex where
  parameters : TransitionParameters
  member : WeightMember
  z : ℝ
  z_ge_sigma : parameters.sigma ≤ z

@[expose] def transitionCoefficient (_q : TransitionIndex) : ℝ := 1 / 2

@[expose] def transitionFactor (q : TransitionIndex) (p : ℕ) : ℝ :=
  if q.parameters.sigma ≤ (p : ℝ) ∧ (p : ℝ) < q.z then
    localEulerFactor (selectedWeight q.parameters.toWeightParameters q.member)
      (modifierWeight q.parameters.toWeightParameters) p
  else 1 + 1 / (2 * (p : ℝ))

/-- Every parameter is an explicit projection of the same already-supplied W. -/
@[expose] def commonEta (W : CommonWeightWitnesses) : ℝ := min W.cStar 1

@[expose] def commonError (W : CommonWeightWitnesses) : ℝ := W.CStar + 2 * W.LambdaStar

@[expose] def commonLambdaSeq (W : CommonWeightWitnesses) : ℕ → ℝ :=
  fun _ => W.LambdaStar

end
end Erdos448.Stage4.WrapupFamilies
