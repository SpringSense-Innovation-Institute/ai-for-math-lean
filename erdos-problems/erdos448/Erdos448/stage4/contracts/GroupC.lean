module

import all Mathlib.Basic.Real.Basic
public import Erdos448.stage4.AnalyticFoundation

public section

set_option backward.isDefEq.respectTransparency false

/-!
Lean-facing contracts for the regular, transition, and empty-bin portions of
Proposition 3 (S3 P-060--P-089).

Mathematical authority: `Erdos448/stage3/canonical/CURRENT.md`, SHA-256
`1974e1237d99cb34aca984ee81273a55676e70fdc4f047080e79d579a42aacda`.

These are proposition aliases and construction-payload specifications only.
They contain no theorem implementation.  In particular, constants quantified
after `theta` and before a `WeightParameters` value are uniform in
`y`, `k`, `sigma`, `x`, and every finite-sum index.
-/

namespace Erdos448.Stage4.Contracts

open Finset Set
open scoped BigOperators NNReal

noncomputable section

/-! Exact shared scalar subjects.  The strict `w4` window is the canonical
`w4WindowSum` supplied by `RootObjects`. -/

/-- The three-term brace common to P-074, P-087, and P-089. -/
@[expose] def proposition3Braces (q : WeightParameters) (x : ℝ) : ℝ :=
  (q.k : ℝ).rpow ((q.y - 1) / 2) +
    (safeLog (2 * x * q.theta ^ (1 - (2 : ℤ) * q.k))).rpow ((q.y - 1) / 2) +
    (Real.log q.sigma).rpow (q.y / 2) /
      (safeLog (2 * x * q.theta ^ (1 - (2 : ℤ) * q.k))).rpow (1 / 2)

/-- The Proposition-3 envelope without its leading constant or the regular
branch's explicit `1 / y`. -/
@[expose] def proposition3Envelope (q : WeightParameters) (x : ℝ) : ℝ :=
  x * (Real.log q.sigma).rpow (-q.y) *
    (q.k : ℝ).rpow ((q.y - 3) / 2) * proposition3Braces q x

@[expose] def upperAssemblyEnvelope (q : WeightParameters) (x : ℝ) : ℝ :=
  x * (Real.log q.sigma).rpow (-q.y) *
    (q.k : ℝ).rpow ((q.y - 3) / 2) *
    (q.k : ℝ).rpow ((q.y - 1) / 2)

@[expose] def middleAssemblyEnvelope (q : WeightParameters) (x : ℝ) : ℝ :=
  x * (Real.log q.sigma).rpow (-q.y) *
    (q.k : ℝ).rpow ((q.y - 3) / 2) *
    (safeLog (2 * x * q.theta ^ (1 - (2 : ℤ) * q.k))).rpow ((q.y - 1) / 2)

@[expose] def terminalAssemblyEnvelope (q : WeightParameters) (x : ℝ) : ℝ :=
  x * (Real.log q.sigma).rpow (-q.y) *
    (q.k : ℝ).rpow ((q.y - 3) / 2) *
    ((Real.log q.sigma).rpow (q.y / 2) /
      (safeLog (2 * x * q.theta ^ (1 - (2 : ℤ) * q.k))).rpow (1 / 2))

/-! P-060--P-074: regular branch. -/

/-- P-060: exact regular smoothing, with a theta-only constant. -/
@[expose] def P060Statement : Prop :=
  ∀ theta : ℝ, 2 ≤ theta → ∃ CregSm : ℝ, 0 < CregSm ∧
    ∀ q : WeightParameters, q.theta = theta →
      q.sigma ≤ q.theta ^ q.k → ∀ x : ℝ,
        q.theta ^ (2 * q.k - 1) < x →
          proposition3Subject q x ≤ CregSm * smoothedRegular .whole q x

/-- P-061: the exact upper/middle/terminal partition. -/
@[expose] def P061Statement : Prop :=
  ∀ q : WeightParameters, q.sigma ≤ q.theta ^ q.k → ∀ x : ℝ,
    q.theta ^ (2 * q.k - 1) < x →
      smoothedRegular .whole q x =
        smoothedRegular .upper q x + smoothedRegular .middle q x +
          smoothedRegular .terminal q x

/-- P-062: upper-regime substitution, in the forward `U^up → M^up`
direction. -/
@[expose] def P062Statement : Prop :=
  ∀ theta : ℝ, 2 ≤ theta → ∃ Cup : ℝ, 0 < Cup ∧
    ∀ q : WeightParameters, q.theta = theta →
      q.sigma ≤ q.theta ^ q.k → ∀ x : ℝ,
        q.theta ^ (2 * q.k - 1) < x →
          smoothedRegular .upper q x ≤ Cup * substitutedRegular .upper q x

/-- P-063: upper window/weight transport, `M^up → R^A`. -/
@[expose] def P063Statement : Prop :=
  ∀ theta : ℝ, 2 ≤ theta → ∃ CA : ℝ, 0 < CA ∧
    ∀ q : WeightParameters, q.theta = theta →
      q.sigma ≤ q.theta ^ q.k → ∀ x : ℝ,
        q.theta ^ (2 * q.k - 1) < x →
          substitutedRegular .upper q x ≤ CA * regularA q x

/-- P-064: middle-regime substitution, `U^mid → M^mid`. -/
@[expose] def P064Statement : Prop :=
  ∀ theta : ℝ, 2 ≤ theta → ∃ Cmid : ℝ, 0 < Cmid ∧
    ∀ q : WeightParameters, q.theta = theta →
      q.sigma ≤ q.theta ^ q.k → ∀ x : ℝ,
        q.theta ^ (2 * q.k - 1) < x →
          smoothedRegular .middle q x ≤ Cmid * substitutedRegular .middle q x

/-- P-065: middle transport lands in the separately named enlarged subject,
never in `convolutionBSharp`. -/
@[expose] def P065Statement : Prop :=
  ∀ theta : ℝ, 2 ≤ theta → ∃ CB : ℝ, 0 < CB ∧
    ∀ q : WeightParameters, q.theta = theta →
      q.sigma ≤ q.theta ^ q.k → ∀ x : ℝ,
        q.theta ^ (2 * q.k - 1) < x →
          substitutedRegular .middle q x ≤ CB * regularB q x

/-- P-066: terminal substitution has no comparison constant. -/
@[expose] def P066Statement : Prop :=
  ∀ q : WeightParameters, q.sigma ≤ q.theta ^ q.k → ∀ x : ℝ,
    q.theta ^ (2 * q.k - 1) < x →
      smoothedRegular .terminal q x ≤ substitutedRegular .terminal q x

/-- P-067: terminal window/weight transport, `M^term → R^C`. -/
@[expose] def P067Statement : Prop :=
  ∀ theta : ℝ, 2 ≤ theta → ∃ CC : ℝ, 0 < CC ∧
    ∀ q : WeightParameters, q.theta = theta →
      q.sigma ≤ q.theta ^ q.k → ∀ x : ℝ,
        q.theta ^ (2 * q.k - 1) < x →
          substitutedRegular .terminal q x ≤ CC * regularC q x

/-- P-068: the absolute A-convolution bound. -/
@[expose] def P068Statement : Prop :=
  Nonempty P068FoundationProvider

/-- P-069: one absolute constant controls both the sharp and enlarged
middle convolutions without identifying them. -/
@[expose] def P069Statement : Prop :=
  Nonempty P069FoundationProvider

/-- The part of P-051G needed to keep P-070's three local witnesses literally
common across the complete D-015 family. -/
structure P070WeightTypeSpec
    (w : ArithmeticWeight) (c C Lambda : ℝ) : Prop where
  nonnegative_multiplicative : NonnegativeMultiplicativeWeight w
  normalized : w 1 = 1
  prime_power_error : ∀ p : ℕ, p.Prime → ∀ i : ℕ, 1 ≤ i →
    |w (p ^ i) - 1 / (i + 1 : ℝ)| ≤ C * (p : ℝ).rpow (-c)
  prime_power_bounds : ∀ p : ℕ, p.Prime → ∀ i : ℕ, 1 ≤ i →
    0 ≤ w (p ^ i) ∧ w (p ^ i) ≤ Lambda

structure P070CommonWeightWitnesses where
  cStar : ℝ
  CStar : ℝ
  LambdaStar : ℝ
  cStar_pos : 0 < cStar
  CStar_pos : 0 < CStar
  LambdaStar_pos : 0 < LambdaStar
  a0_type : P070WeightTypeSpec a0Weight cStar CStar LambdaStar
  w1_type : P070WeightTypeSpec w1Weight cStar CStar LambdaStar
  w2_type : ∀ q : WeightParameters,
    P070WeightTypeSpec (w2Weight q) cStar CStar LambdaStar
  w3_type : ∀ q : WeightParameters,
    P070WeightTypeSpec (w3Weight q) cStar CStar LambdaStar
  w4_type : ∀ q : WeightParameters,
    P070WeightTypeSpec (w4Weight q) cStar CStar LambdaStar

/-- P-070's common witnesses.  `Cfam` is shared by every weight family;
`p070C4` is formed from that very witness only after `theta` is fixed. -/
structure P070FamilyWitness where
  /-- The exact P-051G witness triple reused here, not a fresh copy. -/
  common : P070CommonWeightWitnesses
  Cfam : ℝ
  Cfam_pos : 0 < Cfam
  c4_positive : ∀ theta : ℝ, ∀ htheta : 2 ≤ theta,
    0 < p070C4
      { Cfam := Cfam, Cfam_pos := Cfam_pos,
        theta := theta, theta_ge_two := htheta }
  family_mean : ∀ q : WeightParameters, ∀ Z : ℝ, 2 ≤ Z →
    (∑ r ∈ positiveNatsBelow Z, w4Weight q r) ≤
      Cfam * Z * (Real.log Z).rpow (-1 / 2)
  window : ∀ q : WeightParameters,
    w4WindowSum q ≤
      p070C4
          { Cfam := Cfam, Cfam_pos := Cfam_pos,
            theta := q.theta, theta_ge_two := q.theta_ge_two } *
        q.theta ^ q.k * (q.k : ℝ).rpow (-1 / 2)

/-- P-070: all common witnesses are chosen before every family parameter
and endpoint. -/
@[expose] def P070Statement : Prop := Nonempty P070FamilyWitness

/-- P-071: regular upper-branch assembly. -/
@[expose] def P071Statement : Prop :=
  ∀ theta : ℝ, 2 ≤ theta → ∃ CAasm : ℝ, 0 < CAasm ∧
    ∀ q : WeightParameters, q.theta = theta →
      q.sigma ≤ q.theta ^ q.k → ∀ x : ℝ,
        q.theta ^ (2 * q.k - 1) < x →
          regularA q x ≤ CAasm * upperAssemblyEnvelope q x

/-- P-072: regular middle assembly retains the explicit sharp `1 / y`. -/
@[expose] def P072Statement : Prop :=
  ∀ theta : ℝ, 2 ≤ theta → ∃ CBasm : ℝ, 0 < CBasm ∧
    ∀ q : WeightParameters, q.theta = theta →
      q.sigma ≤ q.theta ^ q.k → ∀ x : ℝ,
        q.theta ^ (2 * q.k - 1) < x →
          regularB q x ≤ (CBasm / q.y) * middleAssemblyEnvelope q x

/-- P-073: regular terminal-branch assembly. -/
@[expose] def P073Statement : Prop :=
  ∀ theta : ℝ, 2 ≤ theta → ∃ CCasm : ℝ, 0 < CCasm ∧
    ∀ q : WeightParameters, q.theta = theta →
      q.sigma ≤ q.theta ^ q.k → ∀ x : ℝ,
        q.theta ^ (2 * q.k - 1) < x →
          regularC q x ≤ CCasm * terminalAssemblyEnvelope q x

/-- P-074: completed regular envelope, with its theta-only numerator and
subsequent `1 / y` factor kept separate. -/
@[expose] def P074Statement : Prop :=
  ∀ theta : ℝ, 2 ≤ theta → ∃ Creg : ℝ, 0 < Creg ∧
    ∀ q : WeightParameters, q.theta = theta →
      q.sigma ≤ q.theta ^ q.k → ∀ x : ℝ,
        q.theta ^ (2 * q.k - 1) < x →
          proposition3Subject q x ≤ (Creg / q.y) * proposition3Envelope q x

/-! P-075--P-087: transition branch. -/

/-- P-075: exact transition smoothing. -/
@[expose] def P075Statement : Prop :=
  ∀ theta : ℝ, 2 ≤ theta → ∃ CtrSm : ℝ, 0 < CtrSm ∧
    ∀ q : TransitionParameters, q.theta = theta → ∀ x : ℝ,
      q.theta ^ (2 * q.k - 1) < x →
        proposition3Subject q.toWeightParameters x ≤
          CtrSm * transitionSmoothed q x

/-- P-076: exact high/low transition partition. -/
@[expose] def P076Statement : Prop :=
  ∀ q : TransitionParameters, ∀ x : ℝ,
    q.theta ^ (2 * q.k - 1) < x →
      transitionSmoothed q x =
        transitionRestricted .high q x + transitionRestricted .low q x

/-- The P-077 family index includes the active endpoint `z`; it is not
specialized to `x / (m*d*d')` until the termwise consumer instantiation. -/
structure P077EndpointIndex where
  parameters : TransitionParameters
  z : ℝ
  z_ge_sigma : parameters.sigma ≤ z

@[expose] def p077EulerFactor (q : P077EndpointIndex) (p : ℕ) : ℝ :=
  ∑' j : ℕ,
    w1Weight (p ^ j) * modifierWeight q.parameters.toWeightParameters (p ^ j) /
      (p : ℝ) ^ j

/-- `L^{tr,0}_{q,p}` from the endpoint-indexed P-077 payload. -/
@[expose] def p077LowerEulerFamily (q : P077EndpointIndex) (p : ℕ) : ℝ :=
  if 2 ≤ p ∧ (p : ℝ) < q.parameters.sigma then p077EulerFactor q p else 1

/-- `L^{tr,hi}_{q,p}` from the endpoint-indexed P-077 payload. -/
@[expose] def p077HighEulerFamily (q : P077EndpointIndex) (p : ℕ) : ℝ :=
  if q.parameters.sigma ≤ (p : ℝ) ∧ (p : ℝ) < q.z then
    p077EulerFactor q p
  else 1 + 1 / (2 * (p : ℝ))

/-- Well-posedness/specification surface for the two global P-077 factor
families.  Positivity and convergence remain explicit construction payload. -/
structure P077EndpointFamilySpec : Prop where
  summable : ∀ q : P077EndpointIndex, ∀ p : ℕ, Nat.Prime p →
    Summable fun j : ℕ =>
      w1Weight (p ^ j) * modifierWeight q.parameters.toWeightParameters (p ^ j) /
        (p : ℝ) ^ j
  lower_positive : ∀ q : P077EndpointIndex, ∀ p : ℕ,
    Nat.Prime p → 0 < p077LowerEulerFamily q p
  high_positive : ∀ q : P077EndpointIndex, ∀ p : ℕ,
    Nat.Prime p → 0 < p077HighEulerFamily q p

/-- P-077: high substitution in the exact forward direction
`V^≥ → H̃`, uniform over the endpoint-indexed family above. -/
@[expose] def P077Statement : Prop :=
  ∀ theta : ℝ, 2 ≤ theta → ∃ CtrHigh : ℝ, 0 < CtrHigh ∧
    ∀ q : TransitionParameters, q.theta = theta → ∀ x : ℝ,
      q.theta ^ (2 * q.k - 1) < x →
        transitionRestricted .high q x ≤
          CtrHigh * transitionSubstituted .high q x

/-- P-078: `H̃ → H`, with no comparison constant. -/
@[expose] def P078Statement : Prop :=
  ∀ q : TransitionParameters, ∀ x : ℝ,
    q.theta ^ (2 * q.k - 1) < x →
      transitionSubstituted .high q x ≤ transitionTransported .high q x

/-- P-079: `V^< → L̃`, with no comparison constant. -/
@[expose] def P079Statement : Prop :=
  ∀ q : TransitionParameters, ∀ x : ℝ,
    q.theta ^ (2 * q.k - 1) < x →
      transitionRestricted .low q x ≤ transitionSubstituted .low q x

/-- P-080: `L̃ → L`, with no comparison constant. -/
@[expose] def P080Statement : Prop :=
  ∀ q : TransitionParameters, ∀ x : ℝ,
    q.theta ^ (2 * q.k - 1) < x →
      transitionSubstituted .low q x ≤ transitionTransported .low q x

/-- The y-independent parameter domain of P-081. -/
structure P081ScaleParameters where
  theta : ℝ
  theta_ge_two : 2 ≤ theta
  k : ℕ
  k_pos : 1 ≤ k
  sigma : ℝ
  sigma_gt_bin : theta ^ k < sigma
  sigma_lt_next_bin : sigma < theta ^ (k + 1)

/-- P-081's exact strict log endpoints together with a single pair of
theta-dependent comparison constants, fixed before `k` and `sigma`. -/
structure P081ScaleWitness (theta : ℝ) where
  comparison : PositiveComparison
  strict_log_bounds : ∀ q : P081ScaleParameters, q.theta = theta →
    (q.k : ℝ) * Real.log q.theta < Real.log q.sigma ∧
      Real.log q.sigma < (q.k + 1 : ℕ) * Real.log q.theta
  asymptotic_bounds : ∀ q : P081ScaleParameters, q.theta = theta →
    comparison.lower * q.k ≤ Real.log q.sigma ∧
      Real.log q.sigma ≤ comparison.upper * q.k

/-- P-081: exact scale comparison with theta-only witnesses. -/
@[expose] def P081Statement : Prop :=
  ∀ theta : ℝ, 2 ≤ theta → Nonempty (P081ScaleWitness theta)

/-- P-082: high convolution transport. -/
@[expose] def P082Statement : Prop :=
  ∀ theta : ℝ, 2 ≤ theta → ∃ CtrH : ℝ, 0 < CtrH ∧
    ∀ q : TransitionParameters, q.theta = theta → ∀ x : ℝ,
      q.theta ^ (2 * q.k - 1) < x →
        transitionTransported .high q x ≤
          CtrH * (Real.log q.sigma).rpow (-1 / 2) *
            (x / q.theta ^ (2 * q.k)) * transitionOuter q

/-- P-083: low convolution transport. -/
@[expose] def P083Statement : Prop :=
  ∀ theta : ℝ, 2 ≤ theta → ∃ CtrL : ℝ, 0 < CtrL ∧
    ∀ q : TransitionParameters, q.theta = theta → ∀ x : ℝ,
      q.theta ^ (2 * q.k - 1) < x →
        transitionTransported .low q x ≤
          CtrL * (x / q.theta ^ (2 * q.k)) *
            (safeLog (2 * x * q.theta ^ (1 - (2 : ℤ) * q.k))).rpow (-1 / 2) *
              transitionOuter q

/-- P-084: transition outer shifted mean using the same D-015 `w4` family
and the exact strict P-070 window. -/
@[expose] def P084Statement : Prop :=
  ∀ theta : ℝ, 2 ≤ theta → ∃ CtrOut : ℝ, 0 < CtrOut ∧
    ∀ q : TransitionParameters, q.theta = theta →
      transitionOuter q ≤
        CtrOut * q.theta ^ q.k * (Real.log q.sigma).rpow (-1) *
          w4WindowSum q.toWeightParameters

/-- P-085: transition high assembly. -/
@[expose] def P085Statement : Prop :=
  ∀ theta : ℝ, 2 ≤ theta → ∃ CtrA : ℝ, 0 < CtrA ∧
    ∀ q : TransitionParameters, q.theta = theta → ∀ x : ℝ,
      q.theta ^ (2 * q.k - 1) < x →
        transitionTransported .high q x ≤
          CtrA * upperAssemblyEnvelope q.toWeightParameters x

/-- P-086: transition low assembly. -/
@[expose] def P086Statement : Prop :=
  ∀ theta : ℝ, 2 ≤ theta → ∃ CtrC : ℝ, 0 < CtrC ∧
    ∀ q : TransitionParameters, q.theta = theta → ∀ x : ℝ,
      q.theta ^ (2 * q.k - 1) < x →
        transitionTransported .low q x ≤
          CtrC * terminalAssemblyEnvelope q.toWeightParameters x

/-- P-087: completed transition envelope. -/
@[expose] def P087Statement : Prop :=
  ∀ theta : ℝ, 2 ≤ theta → ∃ Ctr : ℝ, 0 < Ctr ∧
    ∀ q : TransitionParameters, q.theta = theta → ∀ x : ℝ,
      q.theta ^ (2 * q.k - 1) < x →
        proposition3Subject q.toWeightParameters x ≤
          Ctr * proposition3Envelope q.toWeightParameters x

/-! P-088--P-089: empty branch and Proposition 3. -/

/-- P-088: the weak empty-bin endpoint `theta^(k+1) ≤ sigma` gives an
exact zero subject. -/
@[expose] def P088Statement : Prop :=
  ∀ q : WeightParameters, ∀ x : ℝ, 0 < x →
    q.theta ^ (q.k + 1) ≤ q.sigma → proposition3Subject q x = 0

/-- P-089: Proposition 3, with `C3(theta)` fixed before y and with the
explicit `1 / y` preserved outside that constant. -/
@[expose] def P089Statement : Prop :=
  ∀ theta : ℝ, 2 ≤ theta → ∃ C3 : ℝ, 0 < C3 ∧
    ∀ q : WeightParameters, q.theta = theta → ∀ x : ℝ,
      q.theta ^ (2 * q.k - 1) < x →
        proposition3Subject q x ≤ (C3 / q.y) * proposition3Envelope q x

end

end Erdos448.Stage4.Contracts
