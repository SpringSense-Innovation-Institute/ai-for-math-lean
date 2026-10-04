module

import all Mathlib.Basic.Real.Basic
public import Erdos448.stage4.Interfaces

public section

set_option backward.isDefEq.respectTransparency false

/-!
Construction-facing representations of the root objects in S3 D-001--D-022
and the scoped definition P070-C4.

Mathematical authority: `Erdos448/stage3/canonical/CURRENT.md`, SHA-256
`1974e1237d99cb34aca984ee81273a55676e70fdc4f047080e79d579a42aacda`.

The formulas below are total Lean functions.  Every restriction under which
S3 defines or uses them, and every well-posedness obligation hidden by total
division or `tsum`, is retained in an adjacent domain/specification type.
This file contains no theorem declaration or proof implementation.
-/

namespace Erdos448.Stage4

open Filter Finset Set
open scoped BigOperators Topology NNReal

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

@[expose] abbrev ArithmeticWeight := ℕ → ℝ

@[expose] def NonnegativeWeight (w : ArithmeticWeight) : Prop :=
  ∀ n : ℕ, 0 < n → 0 ≤ w n

@[expose] def MultiplicativeWeight (w : ArithmeticWeight) : Prop :=
  w 1 = 1 ∧ ∀ a b : ℕ, 0 < a → 0 < b → Nat.Coprime a b →
    w (a * b) = w a * w b

structure NonnegativeMultiplicativeWeight (w : ArithmeticWeight) : Prop where
  nonnegative : NonnegativeWeight w
  multiplicative : MultiplicativeWeight w

@[expose] def positiveNatsBelow (x : ℝ) : Finset ℕ :=
  (Finset.range (Nat.ceil x)).filter fun n => 0 < n ∧ (n : ℝ) < x

@[expose] def positiveNatsUpTo (N : ℕ) : Finset ℕ :=
  (Finset.range (N + 1)).filter fun n => 0 < n

@[expose] def strictPrimeRange (x : ℝ) : Finset ℕ :=
  (positiveNatsBelow x).filter Nat.Prime

@[expose] def tauRaw (n : ℕ) : ℕ :=
  if hn : 0 < n then tau ⟨n, hn⟩ else 0

@[expose] def omegaBelowRaw (n : ℕ) (u : ℝ) : ℕ :=
  if hn : 0 < n then omegaBelow ⟨n, hn⟩ u else 0

/-! D-001--D-006: specification surfaces for the definitions in Interfaces. -/

structure DivisorCountSpec (n : PosNat) : Prop where
  divisor_membership : ∀ d : ℕ, d ∈ divisorSet n ↔ 0 < d ∧ d ∣ n.1
  count_positive : 0 < tau n

structure RoughCountDomain where
  n : PosNat
  s : ℝ
  s_ge_two : 2 ≤ s

structure RoughCountSpec (q : RoughCountDomain) : Prop where
  one_is_rough : IsRough 1 q.s
  indicator_zero_or_one : ∀ d : ℕ,
    roughIndicator d q.s = 0 ∨ roughIndicator d q.s = 1
  denominator_positive : 0 < roughTau q.n q.s

structure OmegaDomain where
  n : PosNat
  u : ℝ
  u_pos : 0 < u

structure OccupiedBinDomain where
  n : PosNat
  theta : ℝ
  theta_gt_one : 1 < theta

structure OccupiedBinSpec (q : OccupiedBinDomain) : Prop where
  exact_support : ∀ k : ℕ,
    k ∈ occupiedBins q.n q.theta ↔ OccupiesBin q.n q.theta k
  count_positive : 0 < tauPlus q.n q.theta

structure CloseDomain where
  d : PosNat
  d' : PosNat
  theta : ℝ
  theta_gt_one : 1 < theta

@[expose] def upperDensity (A : Set ℕ) : ℝ :=
  Filter.limsup (prefixDensity A) atTop

@[expose] def lowerDensity (A : Set ℕ) : ℝ :=
  Filter.liminf (prefixDensity A) atTop

@[expose] def roughDensity (theta : ℝ) : ℝ :=
  ∏ p ∈ strictPrimeRange theta, (1 - 1 / (p : ℝ))

structure DensityDomain where
  A : Set ℕ
  positive_members : ∀ n : ℕ, n ∈ A → 0 < n
  t : ℝ
  t_pos : 0 < t
  theta : ℝ
  theta_ge_two : 2 ≤ theta

structure DensitySpec (q : DensityDomain) : Prop where
  upper_mem : upperDensity q.A ∈ Set.Icc (0 : ℝ) 1
  lower_mem : lowerDensity q.A ∈ Set.Icc (0 : ℝ) 1
  safeLog_ge_one : 1 ≤ safeLog q.t
  roughDensity_pos : 0 < roughDensity q.theta

@[expose] def LowerDensityAtLeast (A : Set ℕ) (c : ℝ) : Prop :=
  c ≤ lowerDensity A

/-! D-007: ambient good-divisor predicate and indicator. -/

structure GoodParameters where
  epsilonInt : ℝ
  epsilonInt_pos : 0 < epsilonInt
  epsilonInt_le_tenth : epsilonInt ≤ 1 / 10
  xi : ℝ
  xi_gt_one : 1 < xi
  sigma : ℝ
  sigma_ge_two : 2 ≤ sigma

@[expose] def goodU0 (q : GoodParameters) : ℝ :=
  Real.exp (Real.log q.xi * Real.log q.sigma)

@[expose] def Good (q : GoodParameters) (n d : PosNat) : Prop :=
  ∀ u : ℝ, goodU0 q ≤ u → u < n.1 →
    |(omegaBelow d u : ℝ) -
        (1 / 2) * Real.log (Real.log u / Real.log q.sigma)| ≤
      q.epsilonInt * Real.log (Real.log u / Real.log q.sigma)

@[expose] def goodIndicator (q : GoodParameters) (n d : ℕ) : ℕ :=
  if hn : 0 < n then
    if hd : 0 < d then if Good q ⟨n, hn⟩ ⟨d, hd⟩ then 1 else 0
    else 0
  else 0

structure GoodDivisorDomain (q : GoodParameters) where
  n : PosNat
  d : PosNat
  divides : d.1 ∣ n.1
  beyond_exceptional_range : goodU0 q < n.1

/-! D-008: exact divisor moment and its intended-domain obligations. -/

structure MomentParameters where
  y : ℝ
  y_pos : 0 < y
  y_lt_two : y < 2
  theta : ℝ
  theta_ge_two : 2 ≤ theta
  sigma : ℝ
  sigma_ge_theta : theta ≤ sigma
  u : ℝ
  u_gt_sigma : sigma < u

@[expose] def moment (q : MomentParameters) (n : PosNat) : ℝ :=
  (roughIndicator n.1 q.theta : ℝ) / roughTau n q.sigma *
    ∑ d ∈ divisorSet n,
      q.y.rpow (omegaBelowRaw d q.u : ℝ) * (roughIndicator d q.sigma : ℝ)

structure MomentSpec (q : MomentParameters) (n : PosNat) : Prop where
  denominator_positive : 0 < roughTau n q.sigma
  nonnegative : 0 ≤ moment q n

/-! D-009: grid, terminal event, GridBound, and ThresholdSpec. -/

structure GridParameters where
  epsilonInt : ℝ
  epsilonInt_pos : 0 < epsilonInt
  epsilonInt_le_tenth : epsilonInt ≤ 1 / 10
  Cgrid : ℝ
  Cgrid_pos : 0 < Cgrid

@[expose] def gridU0 (xi sigma : ℝ) : ℝ :=
  Real.exp (Real.log xi * Real.log sigma)

@[expose] def gridPoint (xi sigma : ℝ) (j : ℕ) : ℝ :=
  Real.exp (Real.exp (j : ℝ) * Real.log sigma * Real.log xi)

@[expose] def lambdaDeviation (sigma : ℝ) (d : PosNat) (u : ℝ) : ℝ :=
  ((omegaBelow d u : ℝ) -
      (1 / 2) * Real.log (Real.log u / Real.log sigma)) /
    Real.log (Real.log u / Real.log sigma)

@[expose] def TerminalGridEvent
    (epsilonInt xi sigma x : ℝ) (d : PosNat) : Prop :=
  (∃ j : ℕ, gridPoint xi sigma j < x ∧
      (0.98 * epsilonInt < lambdaDeviation sigma d (gridPoint xi sigma j) ∨
        lambdaDeviation sigma d (gridPoint xi sigma j) < -0.98 * epsilonInt)) ∨
    0.98 * epsilonInt < lambdaDeviation sigma d x

@[expose] def terminalGridCount
    (epsilonInt xi sigma x : ℝ) (n : PosNat) : ℕ :=
  ((divisorSet n).filter fun d =>
    roughIndicator d sigma = 1 ∧
      if hd : 0 < d then TerminalGridEvent epsilonInt xi sigma x ⟨d, hd⟩
      else False).card

@[expose] def gridExceptionalMass
    (epsilonInt xi sigma theta x : ℝ) : ℝ :=
  ∑ n ∈ positiveNatsBelow x,
    if hn : 0 < n then
      (roughIndicator n theta : ℝ) / roughTau ⟨n, hn⟩ sigma *
        terminalGridCount epsilonInt xi sigma x ⟨n, hn⟩
    else 0

@[expose] def GridBound (q : GridParameters) : Prop :=
  ∀ xi sigma theta x : ℝ,
    Real.exp 1 < xi → 2 ≤ theta → theta ≤ sigma → gridU0 xi sigma < x →
      gridExceptionalMass q.epsilonInt xi sigma theta x ≤
        q.Cgrid * x * roughDensity theta *
          (Real.log xi).rpow (-0.901 * q.epsilonInt ^ 2)

@[expose] def ThresholdSpec (q : GridParameters) (Xi0 : ℝ) : Prop :=
  1 < Xi0 ∧ ∀ xi : ℝ, Xi0 ≤ xi →
    Real.exp 1 < xi ∧
      1 / Real.log (Real.log xi) ≤ 0.01 * q.epsilonInt ∧
      10 * q.Cgrid * (Real.log xi).rpow (-0.901 * q.epsilonInt ^ 2) ≤
        (Real.log xi).rpow (-0.9 * q.epsilonInt ^ 2)

/-! D-010--D-012: Lemma-4 set, occupied good bins, and close-pair mean. -/

structure Lemma4Parameters extends GoodParameters where
  theta : ℝ
  theta_ge_two : 2 ≤ theta
  sigma_ge_theta : theta ≤ sigma

@[expose] def lemma4GoodDivisorMass
    (q : Lemma4Parameters) (n : PosNat) : ℕ :=
  ∑ d ∈ divisorSet n,
    roughIndicator d q.sigma * goodIndicator q.toGoodParameters n.1 d

@[expose] def L4Spec (q : Lemma4Parameters) (A : Set ℕ) : Prop :=
  (∀ n : ℕ, n ∈ A → 0 < n ∧ roughIndicator n q.theta = 1) ∧
  LowerDensityAtLeast A
    ((1 - (Real.log q.xi).rpow (-(9 / 10) * q.epsilonInt ^ 2)) *
      roughDensity q.theta) ∧
  ∀ n : ℕ, n ∈ A → ∀ hn : 0 < n,
    (9 / 10 : ℝ) * roughTau ⟨n, hn⟩ q.sigma ≤
      lemma4GoodDivisorMass q ⟨n, hn⟩

@[expose] def occupiedGoodBinCount
    (q : Lemma4Parameters) (n : PosNat) (k : ℕ) : ℕ :=
  ((divisorSet n).filter fun d : ℕ =>
    q.theta ^ k ≤ (d : ℝ) ∧ (d : ℝ) < q.theta ^ (k + 1) ∧
      roughIndicator d q.sigma = 1 ∧ goodIndicator q.toGoodParameters n.1 d = 1).card

@[expose] def occupiedGoodBins
    (q : Lemma4Parameters) (n : PosNat) : Finset ℕ :=
  (occupiedBins n q.theta).filter fun k => 0 < occupiedGoodBinCount q n k

@[expose] def occupiedGoodBinCard (q : Lemma4Parameters) (n : PosNat) : ℕ :=
  (occupiedGoodBins q n).card

/-- The canonical increasing enumeration, rather than an existentially chosen
enumeration whose identity could change across consumers. -/
@[expose] def occupiedGoodBinIndex
    (q : Lemma4Parameters) (n : PosNat)
    (i : Fin (occupiedGoodBinCard q n)) : ℕ :=
  ((occupiedGoodBins q n).orderIsoOfFin rfl i).1

structure GoodBinEnumeration
    (q : Lemma4Parameters) (n : PosNat) where
  index : Fin (occupiedGoodBinCard q n) → ℕ
  exactIdentity : index = occupiedGoodBinIndex q n
  strictlyIncreasing : StrictMono index
  exactRange : ∀ k : ℕ,
    k ∈ occupiedGoodBins q n ↔ ∃ i, index i = k

@[expose] def closePairSum (q : Lemma4Parameters) (n : PosNat) : ℝ :=
  ∑ d ∈ divisorSet n, ∑ d' ∈ divisorSet n,
    if hd : 0 < d then
      if hd' : 0 < d' then
        if Close q.theta ⟨d, hd⟩ ⟨d', hd'⟩ then
          (roughIndicator d q.sigma : ℝ) *
            goodIndicator q.toGoodParameters n.1 d
        else 0
      else 0
    else 0

@[expose] def normalizedClosePair (q : Lemma4Parameters) (n : PosNat) : ℝ :=
  (roughIndicator n.1 q.theta : ℝ) * closePairSum q n / tau n

structure ClosePairSpec (q : Lemma4Parameters) (n : PosNat) : Prop where
  denominator_positive : 0 < tau n
  nonnegative : 0 ≤ normalizedClosePair q n

/-! D-013: typed finite half-open `f_k^#`. -/

structure SharpParameters where
  y : ℝ
  y_pos : 0 < y
  y_lt_one : y < 1
  k : ℕ
  theta : ℝ
  theta_ge_two : 2 ≤ theta
  sigma : ℝ
  sigma_ge_theta : theta ≤ sigma

@[expose] def fkSharp (q : SharpParameters) (n : PosNat) : ℝ :=
  (1 / tau n : ℝ) *
    ∑ d ∈ positiveNatsUpTo n.1, ∑ d' ∈ positiveNatsUpTo n.1,
      ∑ t ∈ positiveNatsUpTo n.1,
        if hd : 0 < d then
          if hd' : 0 < d' then
            if d * d' * t ∣ n.1 ∧
                q.theta ^ q.k ≤ (d : ℝ) ∧ (d : ℝ) < q.theta ^ (q.k + 1) ∧
                Close q.theta ⟨d, hd⟩ ⟨d', hd'⟩ then
              (roughIndicator d q.sigma : ℝ) *
                q.y.rpow (omegaBelowRaw (d * t) (q.theta ^ q.k) : ℝ) *
                roughIndicator t q.sigma
            else 0
          else 0
        else 0

structure SharpSpec (q : SharpParameters) (n : PosNat) : Prop where
  tau_positive : 0 < tau n
  nonnegative : 0 ≤ fkSharp q n

/-! D-014: type-tau-inverse weights and the two shift operators. -/

@[expose] def TauInvType (w : ArithmeticWeight) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧
    ∀ p : ℕ, Nat.Prime p → ∀ i : ℕ, 1 ≤ i →
      |w (p ^ i) - 1 / (i + 1 : ℕ)| ≤ C * (p : ℝ) ^ (-c)

@[expose] def shiftNumerator (a b : ArithmeticWeight) (p i : ℕ) : ℝ :=
  ∑' j : ℕ,
    a (p ^ (i + j)) * b (p ^ j) * (1 + j * Real.log p) / (p : ℝ) ^ j

@[expose] def shiftDenominator (a b : ArithmeticWeight) (p : ℕ) : ℝ :=
  ∑' j : ℕ, a (p ^ j) * b (p ^ j) / (p : ℝ) ^ j

structure ShiftLocalBounds (a b : ArithmeticWeight) where
  cA : ℝ
  cA_pos : 0 < cA
  CA : ℝ
  CA_pos : 0 < CA
  LambdaA : ℝ
  LambdaA_pos : 0 < LambdaA
  a_one : a 1 = 1
  a_type : ∀ p : ℕ, Nat.Prime p → ∀ i : ℕ, 1 ≤ i →
    |a (p ^ i) - 1 / (i + 1 : ℕ)| ≤ CA * (p : ℝ) ^ (-cA)
  a_prime_power_bound : ∀ p : ℕ, Nat.Prime p → ∀ i : ℕ, 1 ≤ i →
    0 ≤ a (p ^ i) ∧ a (p ^ i) ≤ LambdaA
  b_one : b 1 = 1
  b_prime_power_bound : ∀ p : ℕ, Nat.Prime p → ∀ j : ℕ,
    0 ≤ b (p ^ j) ∧ b (p ^ j) ≤ 1

structure ShiftAdmissible (a b : ArithmeticWeight) : Prop where
  a_nonnegative_multiplicative : NonnegativeMultiplicativeWeight a
  b_nonnegative_multiplicative : NonnegativeMultiplicativeWeight b
  local_bounds : Nonempty (ShiftLocalBounds a b)
  numerator_summable : ∀ p : ℕ, Nat.Prime p → ∀ i : ℕ, 1 ≤ i →
    Summable fun j : ℕ =>
      a (p ^ (i + j)) * b (p ^ j) * (1 + j * Real.log p) / (p : ℝ) ^ j
  denominator_summable : ∀ p : ℕ, Nat.Prime p →
    Summable fun j : ℕ => a (p ^ j) * b (p ^ j) / (p : ℝ) ^ j
  denominator_positive : ∀ p : ℕ, Nat.Prime p → 0 < shiftDenominator a b p

@[expose] def localShift (a b : ArithmeticWeight) (p i : ℕ) : ℝ :=
  shiftNumerator a b p i / shiftDenominator a b p

@[expose] def multiplicativeExtension (factorValue : ℕ → ℕ → ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 0
  else ∏ p ∈ n.primeFactors, factorValue p (n.factorization p)

@[expose] def shift (a b : ArithmeticWeight) : ArithmeticWeight :=
  multiplicativeExtension (localShift a b)

@[expose] def maxShift (a b : ArithmeticWeight) : ArithmeticWeight :=
  multiplicativeExtension fun p i => max (localShift a b p i) (a (p ^ i))

structure ShiftSpecification (a b : ArithmeticWeight) : Prop where
  admissible : ShiftAdmissible a b
  shift_nonnegative_multiplicative : NonnegativeMultiplicativeWeight (shift a b)
  maxShift_nonnegative_multiplicative : NonnegativeMultiplicativeWeight (maxShift a b)
  shift_prime_power : ∀ p : ℕ, Nat.Prime p → ∀ i : ℕ, 1 ≤ i →
    shift a b (p ^ i) = localShift a b p i
  maxShift_prime_power : ∀ p : ℕ, Nat.Prime p → ∀ i : ℕ, 1 ≤ i →
    maxShift a b (p ^ i) = max (localShift a b p i) (a (p ^ i))

/-! D-015: the deterministic six-function weight chain and its payload. -/

structure WeightParameters where
  theta : ℝ
  theta_ge_two : 2 ≤ theta
  y : ℝ
  y_pos : 0 < y
  y_lt_one : y < 1
  k : ℕ
  k_pos : 1 ≤ k
  sigma : ℝ
  sigma_ge_theta : theta ≤ sigma

@[expose] def a0Weight : ArithmeticWeight := fun n =>
  if hn : 0 < n then 1 / tau ⟨n, hn⟩ else 0

@[expose] def oneWeight : ArithmeticWeight := fun _ => 1

@[expose] def w1Weight : ArithmeticWeight := maxShift a0Weight oneWeight

@[expose] def modifierWeight (q : WeightParameters) : ArithmeticWeight := fun t =>
  if 0 < t then
    q.y.rpow (omegaBelowRaw t (q.theta ^ q.k) : ℝ) * roughIndicator t q.sigma
  else 0

@[expose] def w2Weight (q : WeightParameters) : ArithmeticWeight :=
  maxShift w1Weight (modifierWeight q)

@[expose] def w3Weight (q : WeightParameters) : ArithmeticWeight :=
  multiplicativeExtension fun p i =>
    max (w1Weight (p ^ i)) (w2Weight q (p ^ i))

@[expose] def w4Weight (q : WeightParameters) : ArithmeticWeight :=
  maxShift (w3Weight q) (modifierWeight q)

@[expose] def w4PrefixSum (q : WeightParameters) (Z : ℝ) : ℝ :=
  ∑ r ∈ positiveNatsBelow Z, w4Weight q r

@[expose] def w4WindowSum (q : WeightParameters) : ℝ :=
  ∑ r ∈ positiveNatsBelow (q.theta ^ (q.k + 2)),
    if q.theta ^ (q.k - 1) < (r : ℝ) then w4Weight q r else 0

structure WeightChainSpecification (q : WeightParameters) : Prop where
  a0_type : TauInvType a0Weight
  w1_shift_spec : ShiftSpecification a0Weight oneWeight
  modifier_nonnegative_multiplicative :
    NonnegativeMultiplicativeWeight (modifierWeight q)
  modifier_one : modifierWeight q 1 = 1
  w2_shift_spec : ShiftSpecification w1Weight (modifierWeight q)
  w3_nonnegative_multiplicative : NonnegativeMultiplicativeWeight (w3Weight q)
  w3_prime_power : ∀ p : ℕ, Nat.Prime p → ∀ i : ℕ, 1 ≤ i →
    w3Weight q (p ^ i) = max (w1Weight (p ^ i)) (w2Weight q (p ^ i))
  w4_shift_spec : ShiftSpecification (w3Weight q) (modifierWeight q)

/-! Shared exact finite subjects for D-016--D-021e. -/

@[expose] def shiftedMean (q : WeightParameters) (z : ℝ) (Ksh : PosNat) : ℝ :=
  ∑ t ∈ positiveNatsBelow z,
    modifierWeight q t * w1Weight (t * Ksh.1)

structure ShiftedMeanDomain (q : WeightParameters) where
  z : ℝ
  z_pos : 0 < z
  Ksh : PosNat

@[expose] def lowerBinIndex (sigma theta : ℝ) : ℕ :=
  max 1 (Nat.ceil ((1 / 2) * Real.log sigma / Real.log theta))

@[expose] def proposition3Subject (q : WeightParameters) (x : ℝ) : ℝ :=
  ∑ n ∈ positiveNatsBelow x,
    if hn : 0 < n then
      fkSharp
        { y := q.y, y_pos := q.y_pos, y_lt_one := q.y_lt_one,
          k := q.k, theta := q.theta, theta_ge_two := q.theta_ge_two,
          sigma := q.sigma, sigma_ge_theta := q.sigma_ge_theta }
        ⟨n, hn⟩
    else 0

@[expose] def outerPairSum (q : WeightParameters) (weight : ArithmeticWeight) : ℝ :=
  ∑ d ∈ positiveNatsBelow (q.theta ^ (q.k + 1)),
    ∑ d' ∈ positiveNatsBelow (q.theta ^ (q.k + 2)),
      if hd : 0 < d then
        if hd' : 0 < d' then
          if q.theta ^ q.k ≤ (d : ℝ) ∧
              Close q.theta ⟨d, hd⟩ ⟨d', hd'⟩ then
            (roughIndicator d q.sigma : ℝ) *
              q.y.rpow (omegaBelowRaw d (q.theta ^ q.k) : ℝ) * weight (d * d')
          else 0
        else 0
      else 0

@[expose] def regularOuter (q : WeightParameters) : ℝ :=
  outerPairSum q (w3Weight q)

@[expose] def convolutionA (q : WeightParameters) (x : ℝ) : ℝ :=
  x / q.theta ^ (2 * q.k) * (q.k : ℝ).rpow ((q.y - 1) / 2) *
    ∑ m ∈ positiveNatsBelow (x * q.theta ^ (1 - (3 : ℤ) * q.k)),
      (safeLog m).rpow (-1 / 2) / m *
        (safeLog (x * q.theta ^ (1 - (2 : ℤ) * q.k) / m)).rpow (-1 / 2)

@[expose] def convolutionBSharp (q : WeightParameters) (x : ℝ) : ℝ :=
  x / q.theta ^ (2 * q.k) *
    ∑ m ∈ positiveNatsBelow (x * q.theta ^ (1 - (2 : ℤ) * q.k)),
      if x * q.theta ^ (1 - (3 : ℤ) * q.k) ≤ m then
        (safeLog m).rpow (-1 / 2) / m *
          (safeLog (x * q.theta ^ (1 - (2 : ℤ) * q.k) / m)).rpow (q.y / 2 - 1)
      else 0

@[expose] def convolutionBEnlarged (q : WeightParameters) (x : ℝ) : ℝ :=
  x / q.theta ^ (2 * q.k) *
    ∑ m ∈ positiveNatsBelow (x * q.theta ^ (1 - (2 : ℤ) * q.k)),
      if x * q.theta ^ (-((3 : ℤ) * q.k) - 3) < m then
        (safeLog m).rpow (-1 / 2) / m *
          (safeLog (x * q.theta ^ (1 - (2 : ℤ) * q.k) / m)).rpow (q.y / 2 - 1)
      else 0

@[expose] def convolutionC (q : WeightParameters) (x : ℝ) : ℝ :=
  x / q.theta ^ (2 * q.k) * (Real.log q.sigma).rpow (q.y / 2) *
    (safeLog (2 * x * q.theta ^ (1 - (2 : ℤ) * q.k))).rpow (-1 / 2)

@[expose] def regularA (q : WeightParameters) (x : ℝ) : ℝ :=
  (Real.log q.sigma).rpow (-q.y / 2) * regularOuter q * convolutionA q x

@[expose] def regularB (q : WeightParameters) (x : ℝ) : ℝ :=
  (Real.log q.sigma).rpow (-q.y / 2) * regularOuter q *
    convolutionBEnlarged q x

@[expose] def regularC (q : WeightParameters) (x : ℝ) : ℝ :=
  (Real.log q.sigma).rpow (-q.y / 2) * regularOuter q * convolutionC q x

structure RegularSubjectDomain (q : WeightParameters) (x : ℝ) : Prop where
  x_pos : 0 < x
  chain : WeightChainSpecification q
  subjects_nonnegative :
    0 ≤ regularOuter q ∧ 0 ≤ convolutionA q x ∧
    0 ≤ convolutionBSharp q x ∧ 0 ≤ convolutionBEnlarged q x ∧
    0 ≤ convolutionC q x

inductive RegularPartition
  | whole | upper | middle | terminal
  deriving DecidableEq

@[expose] def zValue (x : ℝ) (m d d' : ℕ) : ℝ :=
  x / (m * d * d' : ℕ)

@[expose] def partitionAccepts
    (part : RegularPartition) (q : WeightParameters) (z : ℝ) : Prop :=
  match part with
  | .whole => True
  | .upper => q.theta ^ q.k ≤ z
  | .middle => q.sigma ≤ z ∧ z < q.theta ^ q.k
  | .terminal => z < q.sigma

@[expose] def smoothedRegular
    (part : RegularPartition) (q : WeightParameters) (x : ℝ) : ℝ :=
  ∑ d ∈ positiveNatsBelow (q.theta ^ (q.k + 1)),
    ∑ d' ∈ positiveNatsBelow (q.theta ^ (q.k + 2)),
      if hd : 0 < d then
        if hd' : 0 < d' then
          if q.theta ^ q.k ≤ (d : ℝ) ∧ Close q.theta ⟨d, hd⟩ ⟨d', hd'⟩ then
            (roughIndicator d q.sigma : ℝ) *
              q.y.rpow (omegaBelowRaw d (q.theta ^ q.k) : ℝ) *
              ∑ m ∈ positiveNatsBelow (x / (d * d' : ℕ)),
                if partitionAccepts part q (zValue x m d d') then
                  (safeLog m).rpow (-1 / 2) *
                    shiftedMean q (zValue x m d d') ⟨d * d', Nat.mul_pos hd hd'⟩
                else 0
          else 0
        else 0
      else 0

structure RegularSmoothedDomain (q : WeightParameters) (x : ℝ) : Prop where
  sigma_le_bin_top : q.sigma ≤ q.theta ^ q.k
  x_gt_lower_edge : q.theta ^ (2 * q.k - 1) < x
  chain : WeightChainSpecification q

inductive RegularSubstitution
  | upper | middle | terminal
  deriving DecidableEq

@[expose] def substitutedRegular
    (part : RegularSubstitution) (q : WeightParameters) (x : ℝ) : ℝ :=
  ∑ d ∈ positiveNatsBelow (q.theta ^ (q.k + 1)),
    ∑ d' ∈ positiveNatsBelow (q.theta ^ (q.k + 2)),
      if hd : 0 < d then
        if hd' : 0 < d' then
          if q.theta ^ q.k ≤ (d : ℝ) ∧ Close q.theta ⟨d, hd⟩ ⟨d', hd'⟩ then
            (roughIndicator d q.sigma : ℝ) *
              q.y.rpow (omegaBelowRaw d (q.theta ^ q.k) : ℝ) *
              match part with
              | .upper =>
                  (Real.log q.sigma).rpow (-q.y / 2) *
                    (q.k : ℝ).rpow ((q.y - 1) / 2) * w2Weight q (d * d') *
                    ∑ m ∈ positiveNatsBelow (x / (d * d' : ℕ)),
                      if q.theta ^ q.k ≤ zValue x m d d' then
                        (safeLog m).rpow (-1 / 2) * zValue x m d d' *
                          (safeLog (zValue x m d d')).rpow (-1 / 2)
                      else 0
              | .middle =>
                  (Real.log q.sigma).rpow (-q.y / 2) * w2Weight q (d * d') *
                    ∑ m ∈ positiveNatsBelow (x / (d * d' : ℕ)),
                      if q.sigma ≤ zValue x m d d' ∧
                          zValue x m d d' < q.theta ^ q.k then
                        (safeLog m).rpow (-1 / 2) * zValue x m d d' *
                          (safeLog (zValue x m d d')).rpow (q.y / 2 - 1)
                      else 0
              | .terminal =>
                  w1Weight (d * d') *
                    ∑ m ∈ positiveNatsBelow (x / (d * d' : ℕ)),
                      if zValue x m d d' < q.sigma then
                        (safeLog m).rpow (-1 / 2)
                      else 0
          else 0
        else 0
      else 0

structure TransitionParameters extends WeightParameters where
  sigma_gt_bin : theta ^ k < sigma
  sigma_lt_next_bin : sigma < theta ^ (k + 1)

@[expose] def transitionSmoothed (q : TransitionParameters) (x : ℝ) : ℝ :=
  smoothedRegular .whole q.toWeightParameters x

inductive TransitionRestriction
  | high | low
  deriving DecidableEq

@[expose] def transitionRestricted
    (part : TransitionRestriction) (q : TransitionParameters) (x : ℝ) : ℝ :=
  ∑ d ∈ positiveNatsBelow (q.theta ^ (q.k + 1)),
    ∑ d' ∈ positiveNatsBelow (q.theta ^ (q.k + 2)),
      if hd : 0 < d then
        if hd' : 0 < d' then
          if q.theta ^ q.k ≤ (d : ℝ) ∧ Close q.theta ⟨d, hd⟩ ⟨d', hd'⟩ then
            (roughIndicator d q.sigma : ℝ) *
              q.y.rpow (omegaBelowRaw d (q.theta ^ q.k) : ℝ) *
              ∑ m ∈ positiveNatsBelow (x / (d * d' : ℕ)),
                if (match part with
                    | .high => q.sigma ≤ zValue x m d d'
                    | .low => zValue x m d d' < q.sigma) then
                  (safeLog m).rpow (-1 / 2) *
                    shiftedMean q.toWeightParameters (zValue x m d d')
                      ⟨d * d', Nat.mul_pos hd hd'⟩
                else 0
          else 0
        else 0
      else 0

@[expose] def transitionSubstituted
    (part : TransitionRestriction) (q : TransitionParameters) (x : ℝ) : ℝ :=
  ∑ d ∈ positiveNatsBelow (q.theta ^ (q.k + 1)),
    ∑ d' ∈ positiveNatsBelow (q.theta ^ (q.k + 2)),
      if hd : 0 < d then
        if hd' : 0 < d' then
          if q.theta ^ q.k ≤ (d : ℝ) ∧ Close q.theta ⟨d, hd⟩ ⟨d', hd'⟩ then
            (roughIndicator d q.sigma : ℝ) *
              q.y.rpow (omegaBelowRaw d (q.theta ^ q.k) : ℝ) *
              match part with
              | .high =>
                  (Real.log q.sigma).rpow (-1 / 2) * w2Weight q.toWeightParameters (d * d') *
                    ∑ m ∈ positiveNatsBelow (x / (d * d' : ℕ)),
                      if q.sigma ≤ zValue x m d d' then
                        (safeLog m).rpow (-1 / 2) * zValue x m d d' *
                          (safeLog (zValue x m d d')).rpow (-1 / 2)
                      else 0
              | .low =>
                  w1Weight (d * d') *
                    ∑ m ∈ positiveNatsBelow (x / (d * d' : ℕ)),
                      if zValue x m d d' < q.sigma then
                        (safeLog m).rpow (-1 / 2)
                      else 0
          else 0
        else 0
      else 0

@[expose] def transitionTransported
    (part : TransitionRestriction) (q : TransitionParameters) (x : ℝ) : ℝ :=
  ∑ d ∈ positiveNatsBelow (q.theta ^ (q.k + 1)),
    ∑ d' ∈ positiveNatsBelow (q.theta ^ (q.k + 2)),
      if hd : 0 < d then
        if hd' : 0 < d' then
          if q.theta ^ q.k ≤ (d : ℝ) ∧ Close q.theta ⟨d, hd⟩ ⟨d', hd'⟩ then
            (roughIndicator d q.sigma : ℝ) *
              q.y.rpow (omegaBelowRaw d (q.theta ^ q.k) : ℝ) *
              w3Weight q.toWeightParameters (d * d') *
              match part with
              | .high =>
                  (Real.log q.sigma).rpow (-1 / 2) *
                    ∑ m ∈ positiveNatsBelow (x / (d * d' : ℕ)),
                      if q.sigma ≤ zValue x m d d' then
                        (safeLog m).rpow (-1 / 2) * zValue x m d d' *
                          (safeLog (zValue x m d d')).rpow (-1 / 2)
                      else 0
              | .low =>
                  ∑ m ∈ positiveNatsBelow (x / (d * d' : ℕ)),
                    if zValue x m d d' < q.sigma then
                      (safeLog m).rpow (-1 / 2)
                    else 0
          else 0
        else 0
      else 0

@[expose] def transitionOuter (q : TransitionParameters) : ℝ :=
  outerPairSum q.toWeightParameters (w3Weight q.toWeightParameters)

structure TransitionSubjectDomain
    (q : TransitionParameters) (x : ℝ) : Prop where
  x_gt_lower_edge : q.theta ^ (2 * q.k - 1) < x
  chain : WeightChainSpecification q.toWeightParameters
  high_low_exhaustive : ∀ z : ℝ, q.sigma ≤ z ∨ z < q.sigma

/-! D-022: moving cutoff and the non-strict target event. -/

structure MovingCutoffDomain where
  theta : ℝ
  theta_ge_two : 2 ≤ theta
  x : ℝ
  x_pos : 0 < x

@[expose] def movingCutoffReal (q : MovingCutoffDomain) : ℝ :=
  (1 / 2) * (1 + Real.log q.x / Real.log q.theta)

@[expose] def movingCutoff (q : MovingCutoffDomain) : ℤ :=
  Int.ceil (movingCutoffReal q) - 1

structure DensityEventDomain where
  alpha : ℝ
  alpha_nonnegative : 0 ≤ alpha
  alpha_le_one : alpha ≤ 1

@[expose] def targetDensityEvent (q : DensityEventDomain) : Set ℕ :=
  densityEvent q.alpha

/-! Scoped P070-C4.  `Cfam` is selected first and remains part of the input. -/

structure P070C4Parameters where
  Cfam : ℝ
  Cfam_pos : 0 < Cfam
  theta : ℝ
  theta_ge_two : 2 ≤ theta

@[expose] def p070C4 (q : P070C4Parameters) : ℝ :=
  q.Cfam * q.theta ^ 2 / Real.sqrt (Real.log q.theta)

structure P070C4Spec (q : P070C4Parameters) : Prop where
  positive : 0 < p070C4 q

end

end Erdos448.Stage4
