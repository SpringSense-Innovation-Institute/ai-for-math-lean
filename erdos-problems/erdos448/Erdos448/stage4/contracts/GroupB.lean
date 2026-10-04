module

import all Mathlib.Basic.Real.Basic
public import Erdos448.stage4.AnalyticFoundation
public import Erdos448.stage4.RootObjects

public section

set_option backward.isDefEq.respectTransparency false

/-!
S4 proposition contracts for the root-module group B cone.

Mathematical authority: `Erdos448/stage3/canonical/CURRENT.md`, SHA-256
`1974e1237d99cb34aca984ee81273a55676e70fdc4f047080e79d579a42aacda`.

These are proposition aliases and witness/specification records only.  In
particular, the records expose finite reindexing, summability, positivity,
prime-power specifications, and common-witness identity rather than relying
on Lean's total division, `tsum`, or multiplicative extension silently.
-/

namespace Erdos448.Stage4.Contracts

open Finset Set
open scoped BigOperators NNReal

noncomputable section

local instance instDecidableEqPosNat : DecidableEq PosNat := Classical.decEq _
local instance instPropDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-! ## Common exact specification records for P-051 -/

/-- Type-`tau^{-1}` data with the local bound carried by the same witnesses. -/
structure WeightTypeSpec
    (w : ArithmeticWeight) (c C Lambda : ℝ) : Prop where
  c_pos : 0 < c
  C_pos : 0 < C
  Lambda_pos : 0 < Lambda
  nonnegative_multiplicative : NonnegativeMultiplicativeWeight w
  normalized : w 1 = 1
  prime_power : ∀ p : ℕ, p.Prime → ∀ i : ℕ, 1 ≤ i →
    |w (p ^ i) - 1 / (i + 1 : ℕ)| ≤ C * (p : ℝ).rpow (-c)
  prime_power_bounds : ∀ p : ℕ, p.Prime → ∀ i : ℕ, 1 ≤ i →
    0 ≤ w (p ^ i) ∧ w (p ^ i) ≤ Lambda

/-- The literal full-domain modifier conditions, including exponent zero. -/
structure ModifierSpec (b : ArithmeticWeight) : Prop where
  nonnegative_multiplicative : NonnegativeMultiplicativeWeight b
  normalized : b 1 = 1
  prime_power_bounds : ∀ p : ℕ, p.Prime → ∀ j : ℕ,
    0 ≤ b (p ^ j) ∧ b (p ^ j) ≤ 1

/-- Local Euler factor.  Summability is never inferred from the total `tsum`. -/
@[expose] def localEulerFactor (w b : ArithmeticWeight) (p : ℕ) : ℝ :=
  ∑' j : ℕ, w (p ^ j) * b (p ^ j) / (p : ℝ) ^ j

structure EulerFactorDomain (w b : ArithmeticWeight) (p : ℕ) : Prop where
  prime : p.Prime
  modifier : ModifierSpec b
  summable : Summable fun j : ℕ => w (p ^ j) * b (p ^ j) / (p : ℝ) ^ j
  positive : 0 < localEulerFactor w b p

/-- Exact deterministic chain data, with witnesses chosen before every family member. -/
structure WeightChainSpec where
  c1 : ℝ
  C1 : ℝ
  Lambda1 : ℝ
  c1_pos : 0 < c1
  C1_pos : 0 < C1
  Lambda1_pos : 0 < Lambda1
  w1_type : WeightTypeSpec w1Weight c1 C1 Lambda1
  w1_shift : ShiftSpecification a0Weight oneWeight
  w1_dom_a0 : ∀ K : ℕ, 0 < K → a0Weight K ≤ w1Weight K
  w1_dom_shift : ∀ K : ℕ, 0 < K → shift a0Weight oneWeight K ≤ w1Weight K
  c2 : ℝ
  C2 : ℝ
  Lambda2 : ℝ
  c2_pos : 0 < c2
  C2_pos : 0 < C2
  Lambda2_pos : 0 < Lambda2
  w2_type : ∀ q : WeightParameters, WeightTypeSpec (w2Weight q) c2 C2 Lambda2
  w2_shift : ∀ q : WeightParameters,
    ShiftSpecification w1Weight (modifierWeight q)
  w2_dom_w1 : ∀ q : WeightParameters, ∀ K : ℕ, 0 < K →
    w1Weight K ≤ w2Weight q K
  w2_dom_shift : ∀ q : WeightParameters, ∀ K : ℕ, 0 < K →
    shift w1Weight (modifierWeight q) K ≤ w2Weight q K
  c3 : ℝ
  C3 : ℝ
  Lambda3 : ℝ
  c3_pos : 0 < c3
  C3_pos : 0 < C3
  Lambda3_pos : 0 < Lambda3
  w3_type : ∀ q : WeightParameters, WeightTypeSpec (w3Weight q) c3 C3 Lambda3
  w3_prime_power : ∀ q : WeightParameters, ∀ p : ℕ, p.Prime →
    ∀ i : ℕ, 1 ≤ i →
      w3Weight q (p ^ i) = max (w1Weight (p ^ i)) (w2Weight q (p ^ i))
  w3_dom_w1 : ∀ q : WeightParameters, ∀ K : ℕ, 0 < K →
    w1Weight K ≤ w3Weight q K
  w3_dom_w2 : ∀ q : WeightParameters, ∀ K : ℕ, 0 < K →
    w2Weight q K ≤ w3Weight q K
  c4 : ℝ
  C4 : ℝ
  Lambda4 : ℝ
  c4_pos : 0 < c4
  C4_pos : 0 < C4
  Lambda4_pos : 0 < Lambda4
  w4_type : ∀ q : WeightParameters, WeightTypeSpec (w4Weight q) c4 C4 Lambda4
  w4_shift : ∀ q : WeightParameters,
    ShiftSpecification (w3Weight q) (modifierWeight q)
  w4_dom_w3 : ∀ q : WeightParameters, ∀ K : ℕ, 0 < K →
    w3Weight q K ≤ w4Weight q K
  w4_dom_shift : ∀ q : WeightParameters, ∀ K : ℕ, 0 < K →
    shift (w3Weight q) (modifierWeight q) K ≤ w4Weight q K
  modifier : ∀ q : WeightParameters, ModifierSpec (modifierWeight q)

inductive WeightMember
  | a0 | w1 | w2 | w3 | w4
  deriving DecidableEq

@[expose] def selectedWeight (q : WeightParameters) : WeightMember → ArithmeticWeight
  | .a0 => a0Weight
  | .w1 => w1Weight
  | .w2 => w2Weight q
  | .w3 => w3Weight q
  | .w4 => w4Weight q

/-- P-051G's one triple is shared literally by all five exact weights. -/
structure CommonWeightWitnesses where
  cStar : ℝ
  CStar : ℝ
  LambdaStar : ℝ
  cStar_pos : 0 < cStar
  CStar_pos : 0 < CStar
  LambdaStar_pos : 0 < LambdaStar
  LambdaStar_lower : 1 + CStar * (2 : ℝ).rpow (-cStar) ≤ LambdaStar
  weight_type : ∀ q : WeightParameters, ∀ member : WeightMember,
    WeightTypeSpec (selectedWeight q member) cStar CStar LambdaStar
  modifier : ∀ q : WeightParameters, ModifierSpec (modifierWeight q)
  w1_dom_a0 : ∀ K : ℕ, 0 < K → a0Weight K ≤ w1Weight K
  w2_dom_w1 : ∀ q : WeightParameters, ∀ K : ℕ, 0 < K →
    w1Weight K ≤ w2Weight q K
  w3_dom_w1 : ∀ q : WeightParameters, ∀ K : ℕ, 0 < K →
    w1Weight K ≤ w3Weight q K
  w3_dom_w2 : ∀ q : WeightParameters, ∀ K : ℕ, 0 < K →
    w2Weight q K ≤ w3Weight q K
  w4_dom_w3 : ∀ q : WeightParameters, ∀ K : ℕ, 0 < K →
    w3Weight q K ≤ w4Weight q K

/-! ## P-001C and Propositions 1--2 -/

@[expose] def P001CStatement : Prop :=
  ∀ Ksh : PosNat, ∀ z : ℝ, 0 < z → z < 2 →
    (∑ m ∈ positiveNatsBelow z, a0Weight (m * Ksh.1)) ≤
      w1Weight Ksh.1 *
        ∑ m ∈ positiveNatsBelow z, (safeLog m).rpow (-1 / 2)

@[expose] def P030Statement : Prop :=
  ∀ theta : ℝ, 1 < theta → ∀ k : ℕ, ∀ d d' : PosNat,
    d ≠ d' → theta ^ k ≤ (d.1 : ℝ) → (d.1 : ℝ) < theta ^ (k + 1) →
    theta ^ k ≤ (d'.1 : ℝ) → (d'.1 : ℝ) < theta ^ (k + 1) →
      Close theta d d'

structure P031Payload
    (q : Lemma4Parameters) (n : PosNat)
    (enumeration : GoodBinEnumeration q n) : Prop where
  exact_card : occupiedGoodBinCard q n = (occupiedGoodBins q n).card
  exact_order : StrictMono enumeration.index
  exact_range : ∀ k : ℕ,
    k ∈ occupiedGoodBins q n ↔ ∃ i, enumeration.index i = k
  mass_identity :
    (∑ i : Fin (occupiedGoodBinCard q n),
      occupiedGoodBinCount q n (enumeration.index i)) = lemma4GoodDivisorMass q n
  occupied_bound : occupiedGoodBinCard q n ≤ tauPlus n q.theta

structure P031Witness (q : Lemma4Parameters) (n : PosNat) where
  enumeration : GoodBinEnumeration q n
  payload : P031Payload q n enumeration

@[expose] def P031Statement : Prop :=
  ∀ q : Lemma4Parameters, ∀ A : Set ℕ, L4Spec q A →
    ∀ n : PosNat, n.1 ∈ A → Nonempty (P031Witness q n)

structure P032Payload
    (q : Lemma4Parameters) (n : PosNat)
    (enumeration : GoodBinEnumeration q n) : Prop where
  ordered_pair_bound :
    (∑ i : Fin (occupiedGoodBinCard q n),
      (occupiedGoodBinCount q n (enumeration.index i) : ℝ) *
        ((occupiedGoodBinCount q n (enumeration.index i) : ℝ) - 1)) ≤
      closePairSum q n
  mass_lower :
    (9 / 10 : ℝ) * roughTau n q.sigma ≤
      ∑ i : Fin (occupiedGoodBinCard q n),
        (occupiedGoodBinCount q n (enumeration.index i) : ℝ)
  mass_upper :
    (∑ i : Fin (occupiedGoodBinCard q n),
      (occupiedGoodBinCount q n (enumeration.index i) : ℝ)) ≤
        roughTau n q.sigma

structure P032Witness (q : Lemma4Parameters) (n : PosNat) where
  enumeration : GoodBinEnumeration q n
  payload : P032Payload q n enumeration

@[expose] def P032Statement : Prop :=
  ∀ q : Lemma4Parameters, ∀ A : Set ℕ, L4Spec q A →
    ∀ n : PosNat, n.1 ∈ A → Nonempty (P032Witness q n)

@[expose] def P033Statement : Prop :=
  ∀ r : ℕ, 1 ≤ r → ∀ nu : Fin r → ℝ,
    (∀ i, 0 ≤ nu i) →
      (∑ i, nu i) ^ 2 ≤ (r : ℝ) * ∑ i, (nu i) ^ 2

structure P034Payload (q : Lemma4Parameters) (n : PosNat) : Prop where
  rough_count_positive : 0 < roughTau n q.sigma
  occupied_count_positive : 0 < tauPlus n q.theta
  bound :
    (4 / 5 : ℝ) * ((roughTau n q.sigma : ℝ) / tauPlus n q.theta) ≤
      1 + closePairSum q n / roughTau n q.sigma

@[expose] def P034Statement : Prop :=
  ∀ q : Lemma4Parameters, ∀ A : Set ℕ, L4Spec q A →
    ∀ n : PosNat, n.1 ∈ A → P034Payload q n

@[expose] def GcdReindexRelation
    (n D D' d d' t : PosNat) (theta : ℝ) : Prop :=
  D.1 ∣ n.1 ∧ D'.1 ∣ n.1 ∧ Close theta D D' ∧
    t.1 = Nat.gcd D.1 D'.1 ∧ D.1 = d.1 * t.1 ∧ D'.1 = d'.1 * t.1 ∧
    Nat.Coprime d.1 d'.1 ∧ d.1 * d'.1 * t.1 ∣ n.1 ∧ Close theta d d'

structure GcdReindexPayload
    (n D D' : PosNat) (theta : ℝ) where
  t : PosNat
  d : PosNat
  dPrime : PosNat
  exact_relation : GcdReindexRelation n D D' d dPrime t theta
  forward_unique : ∃! triple : PosNat × PosNat × PosNat,
    GcdReindexRelation n D D' triple.1 triple.2.1 triple.2.2 theta
  inverse_unique : ∀ e e' u : PosNat,
    Nat.Coprime e.1 e'.1 → e.1 * e'.1 * u.1 ∣ n.1 → Close theta e e' →
      ∃! pair : PosNat × PosNat,
        pair.1.1 = e.1 * u.1 ∧ pair.2.1 = e'.1 * u.1 ∧
          GcdReindexRelation n pair.1 pair.2 e e' u theta
  weight_identity : ∀ W : ArithmeticWeight, W D.1 = W (d.1 * t.1)

@[expose] def P040Statement : Prop :=
  ∀ n D D' : PosNat, ∀ theta : ℝ, 1 < theta →
    D.1 ∣ n.1 → D'.1 ∣ n.1 → Close theta D D' →
      Nonempty (GcdReindexPayload n D D' theta)

structure P041Payload
    (q : Lemma4Parameters) (d : PosNat) where
  d_gt_one : 1 < d.1
  rough : roughIndicator d.1 q.sigma = 1
  d_ge_sigma : q.sigma ≤ d.1
  k : ℕ
  k_half_open : q.theta ^ k ≤ (d.1 : ℝ) ∧ (d.1 : ℝ) < q.theta ^ (k + 1)
  k_unique : ∀ j : ℕ,
    q.theta ^ j ≤ (d.1 : ℝ) → (d.1 : ℝ) < q.theta ^ (j + 1) → j = k
  floor_lower : Int.floor (Real.log q.sigma / Real.log q.theta) ≤ (k : ℤ)
  half_lower : (1 / 2 : ℝ) * Real.log q.sigma / Real.log q.theta ≤ k

@[expose] def P041Statement : Prop :=
  ∀ q : Lemma4Parameters, ∀ n D D' t d d' : PosNat,
    D.1 ∣ n.1 → D'.1 ∣ n.1 → Close q.theta D D' →
    t.1 = Nat.gcd D.1 D'.1 → D.1 = d.1 * t.1 → D'.1 = d'.1 * t.1 →
    roughIndicator n.1 q.theta = 1 → roughIndicator (d.1 * t.1) q.sigma = 1 →
      Nonempty (P041Payload q d)

@[expose] def goodPowerMajorant
    (q : Lemma4Parameters) (y : ℝ) (k : ℕ) (m : PosNat) : ℝ :=
  (2 * k * Real.log q.xi * Real.log q.theta / Real.log q.sigma).rpow
      (-(1 / 2 + q.epsilonInt) * Real.log y) *
    y.rpow (omegaBelow m (q.theta ^ k) : ℝ)

@[expose] def P042Statement : Prop :=
  ∀ q : Lemma4Parameters, ∀ y : ℝ, 0 < y → y < 1 →
    ∀ n m : PosNat, goodU0 q.toGoodParameters < n.1 → m.1 ∣ n.1 →
    ∀ k : ℕ, 1 ≤ k → Good q.toGoodParameters n m →
      (Real.log q.sigma / Real.log q.theta) * Real.log q.xi ≤ k →
      q.theta ^ k ≤ (m.1 : ℝ) →
        1 ≤ goodPowerMajorant q y k m

@[expose] def P043Statement : Prop :=
  ∀ q : Lemma4Parameters, ∀ y : ℝ, 0 < y → y < 1 →
    ∀ n m : PosNat, goodU0 q.toGoodParameters < n.1 → m.1 ∣ n.1 →
    ∀ k : ℕ, 1 ≤ k → Good q.toGoodParameters n m →
      (1 / 2 : ℝ) * Real.log q.sigma / Real.log q.theta ≤ k →
      (k : ℝ) < (Real.log q.sigma / Real.log q.theta) * Real.log q.xi →
        1 ≤ goodPowerMajorant q y k m

@[expose] def sharpParametersOf
    (q : Lemma4Parameters) (y : ℝ) (hy0 : 0 < y) (hy1 : y < 1) (k : ℕ) :
    SharpParameters :=
  { y := y, y_pos := hy0, y_lt_one := hy1, k := k,
    theta := q.theta, theta_ge_two := q.theta_ge_two,
    sigma := q.sigma, sigma_ge_theta := q.sigma_ge_theta }

structure P044Payload
    (q : Lemma4Parameters) (y : ℝ) (hy0 : 0 < y) (hy1 : y < 1)
    (n : PosNat) : Prop where
  majorant_summable : Summable fun k : ℕ =>
    if lowerBinIndex q.sigma q.theta ≤ k then
      (k : ℝ).rpow (-(1 / 2 + q.epsilonInt) * Real.log y) *
        fkSharp (sharpParametersOf q y hy0 hy1 k) n
    else 0
  bound : normalizedClosePair q n ≤
    (2 * Real.log q.xi * Real.log q.theta / Real.log q.sigma).rpow
        (-(1 / 2 + q.epsilonInt) * Real.log y) *
      ∑' k : ℕ, if lowerBinIndex q.sigma q.theta ≤ k then
        (k : ℝ).rpow (-(1 / 2 + q.epsilonInt) * Real.log y) *
          fkSharp (sharpParametersOf q y hy0 hy1 k) n
        else 0

@[expose] def P044Statement : Prop :=
  ∀ q : Lemma4Parameters, ∀ y : ℝ, ∀ hy0 : 0 < y, ∀ hy1 : y < 1,
    ∀ n : PosNat, goodU0 q.toGoodParameters < n.1 → P044Payload q y hy0 hy1 n

/-! ## Proposition 3 common infrastructure -/

@[expose] def fourVariableInversion (q : WeightParameters) (x : ℝ) : ℝ :=
  ∑ d ∈ positiveNatsBelow (q.theta ^ (q.k + 1)),
    ∑ d' ∈ positiveNatsBelow (q.theta ^ (q.k + 2)),
      if hd : 0 < d then
        if hd' : 0 < d' then
          if q.theta ^ q.k ≤ (d : ℝ) ∧ Close q.theta ⟨d, hd⟩ ⟨d', hd'⟩ then
            ∑ t ∈ positiveNatsBelow (x / (d * d' : ℕ)),
              (roughIndicator (d * t) q.sigma : ℝ) *
                q.y.rpow (omegaBelowRaw (d * t) (q.theta ^ q.k) : ℝ) *
                ∑ m ∈ positiveNatsBelow (x / (t * d * d' : ℕ)),
                  a0Weight (m * t * d * d')
          else 0
        else 0
      else 0

@[expose] def P050Statement : Prop :=
  ∀ q : WeightParameters, ∀ x : ℝ, q.theta ^ (2 * q.k - 1) < x →
    proposition3Subject q x = fourVariableInversion q x

@[expose] def P051AStatement : Prop :=
  WeightTypeSpec a0Weight 1 1 1 ∧
    (∀ p : ℕ, p.Prime → ∀ i : ℕ, 1 ≤ i →
      a0Weight (p ^ i) = 1 / (i + 1 : ℕ))

structure P051BDenominatorSpec
    (a b : ArithmeticWeight) (Lambdaa : ℝ) (p : ℕ) : Prop where
  summable : Summable fun j : ℕ => a (p ^ j) * b (p ^ j) / (p : ℝ) ^ j
  lower : 1 ≤ shiftDenominator a b p
  upper_geometric : shiftDenominator a b p ≤ 1 + Lambdaa / ((p : ℝ) - 1)
  upper_prime : 1 + Lambdaa / ((p : ℝ) - 1) ≤ 1 + 2 * Lambdaa / p

@[expose] def P051BStatement : Prop :=
  ∀ a : ArithmeticWeight, ∀ ca Ca Lambdaa : ℝ,
    WeightTypeSpec a ca Ca Lambdaa → ∀ b : ArithmeticWeight, ModifierSpec b →
      ∀ p : ℕ, p.Prime →
        P051BDenominatorSpec a b Lambdaa p

@[expose] def P051CStatement : Prop :=
  ∀ a : ArithmeticWeight, ∀ ca Ca Lambdaa : ℝ,
    WeightTypeSpec a ca Ca Lambdaa →
      ∃ csh Csh Lambdash : ℝ,
        csh = min ca (1 / 2) ∧ 0 < csh ∧ 0 < Csh ∧ 0 < Lambdash ∧
        ∀ b : ArithmeticWeight, ModifierSpec b →
          ShiftSpecification a b ∧ WeightTypeSpec (shift a b) csh Csh Lambdash

@[expose] def P051DStatement : Prop :=
  ∀ a b : ArithmeticWeight, ∀ ca Ca Lambdaa csh Csh Lambdash : ℝ,
    WeightTypeSpec a ca Ca Lambdaa → ModifierSpec b →
    ShiftSpecification a b → WeightTypeSpec (shift a b) csh Csh Lambdash →
      WeightTypeSpec (maxShift a b) (min ca csh) (max Ca Csh) (max Lambdaa Lambdash) ∧
      ∀ K : ℕ, 0 < K →
        shift a b K ≤ maxShift a b K ∧ a K ≤ maxShift a b K

@[expose] def P051EStatement : Prop :=
  ∀ a1 a2 : ArithmeticWeight, ∀ c C Lambda : ℝ,
    WeightTypeSpec a1 c C Lambda → WeightTypeSpec a2 c C Lambda →
      WeightTypeSpec
        (multiplicativeExtension fun p i => max (a1 (p ^ i)) (a2 (p ^ i)))
        c C Lambda ∧
      (∀ p : ℕ, p.Prime → ∀ i : ℕ, 1 ≤ i →
        multiplicativeExtension (fun p i => max (a1 (p ^ i)) (a2 (p ^ i))) (p ^ i) =
          max (a1 (p ^ i)) (a2 (p ^ i))) ∧
      ∀ K : ℕ, 0 < K →
        a1 K ≤ multiplicativeExtension (fun p i => max (a1 (p ^ i)) (a2 (p ^ i))) K ∧
        a2 K ≤ multiplicativeExtension (fun p i => max (a1 (p ^ i)) (a2 (p ^ i))) K

@[expose] def P051VStatement : Prop :=
  ∀ q : WeightParameters, ModifierSpec (modifierWeight q)

@[expose] def P051F1Statement : Prop :=
  ∃ c1 C1 Lambda1 : ℝ,
    WeightTypeSpec w1Weight c1 C1 Lambda1 ∧
    ShiftSpecification a0Weight oneWeight ∧
    ∀ K : ℕ, 0 < K →
      a0Weight K ≤ w1Weight K ∧ shift a0Weight oneWeight K ≤ w1Weight K

@[expose] def P051F2Statement : Prop :=
  ∀ c1 C1 Lambda1 : ℝ, WeightTypeSpec w1Weight c1 C1 Lambda1 →
    ∃ c2 C2 Lambda2 : ℝ, 0 < c2 ∧ 0 < C2 ∧ 0 < Lambda2 ∧
      ∀ q : WeightParameters,
        ModifierSpec (modifierWeight q) ∧
        ShiftSpecification w1Weight (modifierWeight q) ∧
        WeightTypeSpec (w2Weight q) c2 C2 Lambda2 ∧
        ∀ K : ℕ, 0 < K →
          w1Weight K ≤ w2Weight q K ∧
          shift w1Weight (modifierWeight q) K ≤ w2Weight q K

@[expose] def P051F3Statement : Prop :=
  ∀ c C Lambda : ℝ,
    WeightTypeSpec w1Weight c C Lambda →
    (∀ q : WeightParameters, WeightTypeSpec (w2Weight q) c C Lambda) →
      ∀ q : WeightParameters,
        WeightTypeSpec (w3Weight q) c C Lambda ∧
        (∀ p : ℕ, p.Prime → ∀ i : ℕ, 1 ≤ i →
          w3Weight q (p ^ i) = max (w1Weight (p ^ i)) (w2Weight q (p ^ i))) ∧
        ∀ K : ℕ, 0 < K →
          w1Weight K ≤ w3Weight q K ∧ w2Weight q K ≤ w3Weight q K

@[expose] def P051F4Statement : Prop :=
  ∀ c3 C3 Lambda3 : ℝ,
    (∀ q : WeightParameters, WeightTypeSpec (w3Weight q) c3 C3 Lambda3) →
      ∃ c4 C4 Lambda4 : ℝ, 0 < c4 ∧ 0 < C4 ∧ 0 < Lambda4 ∧
      ∀ q : WeightParameters,
        ShiftSpecification (w3Weight q) (modifierWeight q) ∧
        WeightTypeSpec (w4Weight q) c4 C4 Lambda4 ∧
        ∀ K : ℕ, 0 < K →
          w3Weight q K ≤ w4Weight q K ∧
          shift (w3Weight q) (modifierWeight q) K ≤ w4Weight q K

@[expose] def P051GStatement : Prop := Nonempty CommonWeightWitnesses

structure P051HEulerSpec
    (W : CommonWeightWitnesses) (q : WeightParameters) (member : WeightMember)
    (b : ArithmeticWeight) (p : ℕ) : Prop where
  domain : EulerFactorDomain (selectedWeight q member) b p
  tail_bound :
    |localEulerFactor (selectedWeight q member) b p -
        (1 + selectedWeight q member p * b p / p)| ≤
      2 * W.LambdaStar * (p : ℝ).rpow (-2)
  tail_to_eta :
    2 * W.LambdaStar * (p : ℝ).rpow (-2) ≤
      2 * W.LambdaStar * (p : ℝ).rpow (-1 - min W.cStar 1)
  replaced_main_term :
    |localEulerFactor (selectedWeight q member) b p - (1 + b p / (2 * p))| ≤
      (W.CStar + 2 * W.LambdaStar) *
        (p : ℝ).rpow (-1 - min W.cStar 1)

@[expose] def P051HStatement : Prop :=
  ∀ W : CommonWeightWitnesses, ∀ q : WeightParameters, ∀ member : WeightMember,
    ∀ b : ArithmeticWeight, ModifierSpec b → ∀ p : ℕ, p.Prime →
      P051HEulerSpec W q member b p

/-! ## Smoothing, endpoint adapters, and regular means -/

@[expose] def reciprocalDivisorSum (z : ℝ) (Ksh : PosNat) : ℝ :=
  ∑ m ∈ positiveNatsBelow z, a0Weight (m * Ksh.1)

@[expose] def P052Statement : Prop :=
  ∀ theta : ℝ, 2 ≤ theta → ∃ Csm : ℝ, 0 < Csm ∧
    ∀ q : WeightParameters, q.theta = theta → ∀ Ksh : PosNat, ∀ z : ℝ, 0 < z →
      reciprocalDivisorSum z Ksh ≤ Csm * w1Weight Ksh.1 * safeLogHalfSum z

@[expose] def P053Statement : Prop := Nonempty P053FoundationProvider

structure P054Payload (theta : ℝ) (k : ℕ) (d d' : PosNat) : Prop where
  product_lower : theta ^ (2 * k - 1) < (d.1 * d'.1 : ℕ)
  product_upper : (d.1 * d'.1 : ℕ) < theta ^ (2 * k + 3)
  second_lower : theta ^ (k - 1) < d'.1
  second_upper : (d'.1 : ℝ) < theta ^ (k + 2)

@[expose] def P054Statement : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∀ theta : ℝ, 1 < theta → ∀ d d' : PosNat,
    theta ^ k ≤ (d.1 : ℝ) → (d.1 : ℝ) < theta ^ (k + 1) →
    Close theta d d' → P054Payload theta k d d'

@[expose] def intervalSum (g : ArithmeticWeight) (lower upper : ℝ) : ℝ :=
  ∑ d ∈ positiveNatsBelow upper, if lower ≤ d then g d else 0

structure P054APayload
    (g : ArithmeticWeight) (k : ℕ) (theta sigma : ℝ) : Prop where
  regular_to_initial : intervalSum g (theta ^ k) (theta ^ (k + 1)) ≤
    ∑ d ∈ positiveNatsBelow (theta ^ (k + 1)), g d
  transition_to_initial : intervalSum g sigma (theta ^ (k + 1)) ≤
    ∑ d ∈ positiveNatsBelow (theta ^ (k + 1)), g d

@[expose] def P054AStatement : Prop :=
  ∀ g : ArithmeticWeight, NonnegativeWeight g → ∀ k : ℕ, 1 ≤ k →
    ∀ theta : ℝ, 2 ≤ theta → ∀ sigma : ℝ, 0 < sigma →
      P054APayload g k theta sigma

@[expose] def P055Statement : Prop :=
  ∀ theta : ℝ, 2 ≤ theta → ∃ Cup : ℝ, 0 < Cup ∧
    ∀ q : WeightParameters, q.theta = theta → ∀ Ksh : PosNat, ∀ z : ℝ,
      q.theta ^ q.k ≤ z → q.sigma ≤ q.theta ^ q.k →
        shiftedMean q z Ksh ≤ Cup * z * w2Weight q Ksh.1 *
          (Real.log q.sigma).rpow (-q.y / 2) *
          (q.k : ℝ).rpow ((q.y - 1) / 2) * (safeLog z).rpow (-1 / 2)

@[expose] def P056Statement : Prop :=
  ∀ theta : ℝ, 2 ≤ theta → ∃ Cmid : ℝ, 0 < Cmid ∧
    ∀ q : WeightParameters, q.theta = theta → ∀ Ksh : PosNat, ∀ z : ℝ, 0 < z →
      q.sigma ≤ z → z < q.theta ^ q.k →
        shiftedMean q z Ksh ≤ Cmid * z * w2Weight q Ksh.1 *
          (Real.log q.sigma).rpow (-q.y / 2) * (safeLog z).rpow (q.y / 2 - 1)

@[expose] def P057Statement : Prop :=
  ∀ q : WeightParameters, ∀ Ksh : PosNat, ∀ z : ℝ, 0 < z → z < q.sigma →
    shiftedMean q z Ksh ≤ w1Weight Ksh.1

@[expose] def P058Statement : Prop :=
  ∀ theta : ℝ, 2 ≤ theta → ∃ Cout : ℝ, 0 < Cout ∧
    ∀ q : WeightParameters, q.theta = theta → q.sigma ≤ q.theta ^ q.k →
      regularOuter q ≤ Cout * q.theta ^ q.k *
        (Real.log q.sigma).rpow (-q.y / 2) *
        (q.k : ℝ).rpow (q.y / 2 - 1) * w4WindowSum q

@[expose] def familyPartialSum {Q : Type*} (w : Q → ArithmeticWeight) (q : Q) (Z : ℝ) : ℝ :=
  ∑ r ∈ positiveNatsBelow Z, w q r

@[expose] def P059Statement : Prop :=
  ∀ (Q : Type*) (w : Q → ArithmeticWeight), Nonempty Q →
    ∀ cw Cw LambdaW : ℝ,
      0 < cw → 0 < Cw → 0 < LambdaW →
      (∀ q : Q, WeightTypeSpec (w q) cw Cw LambdaW) →
        ∃ Cmean : ℝ, 0 < Cmean ∧ ∀ q : Q, ∀ Z : ℝ, 2 ≤ Z →
          familyPartialSum w q Z ≤ Cmean * Z * (Real.log Z).rpow (-1 / 2)

end

end Erdos448.Stage4.Contracts

/-! ## Binder-faithful lowering interfaces: late P-051F2 closure -/

@[expose] abbrev Erdos448.Stage4.Typed.I_D_LATE_P051F2_W
    (_theta _y : ℝ) (_k : ℕ) (_sigma : ℝ) :=
  ℝ × ℝ × ℝ

@[expose] def Erdos448.Stage4.Typed.I_D_LATE_P051F2_EXISTS
    (theta y : ℝ) (k : ℕ) (sigma : ℝ) : Prop :=
  ∃ (htheta : 2 ≤ theta) (hyPos : 0 < y) (hyLt : y < 1)
    (hk : 1 ≤ k) (hsigma : theta ≤ sigma),
    ∃ c2 C2 Lambda2 : ℝ,
      let q : Erdos448.Stage4.WeightParameters :=
        { theta := theta, theta_ge_two := htheta,
          y := y, y_pos := hyPos, y_lt_one := hyLt,
          k := k, k_pos := hk,
          sigma := sigma, sigma_ge_theta := hsigma }
      Erdos448.Stage4.Contracts.WeightTypeSpec
          (Erdos448.Stage4.w2Weight q) c2 C2 Lambda2 ∧
        (∀ K : ℕ, 0 < K →
          Erdos448.Stage4.w1Weight K ≤ Erdos448.Stage4.w2Weight q K) ∧
        ∀ K : ℕ, 0 < K →
          Erdos448.Stage4.shift Erdos448.Stage4.w1Weight
              (Erdos448.Stage4.modifierWeight q) K ≤
            Erdos448.Stage4.w2Weight q K

@[expose] def Erdos448.Stage4.Typed.I_A_LATE_P051F2_EXISTS : Prop :=
  ∀ theta y : ℝ, ∀ k : ℕ, ∀ sigma : ℝ,
    2 ≤ theta → 0 < y → y < 1 → 1 ≤ k → theta ≤ sigma →
      Erdos448.Stage4.Typed.I_D_LATE_P051F2_EXISTS theta y k sigma

@[expose] abbrev Erdos448.Stage4.Typed.I_D_LATE_P051F3_W
    (_theta _y : ℝ) (_k : ℕ) (_sigma : ℝ) :=
  ℝ × ℝ × ℝ

@[expose] def Erdos448.Stage4.Typed.I_D_LATE_P051F3_EXISTS
    (theta y : ℝ) (k : ℕ) (sigma : ℝ) : Prop :=
  ∃ (htheta : 2 ≤ theta) (hyPos : 0 < y) (hyLt : y < 1)
    (hk : 1 ≤ k) (hsigma : theta ≤ sigma),
    ∃ c3 C3 Lambda3 : ℝ,
      let q : Erdos448.Stage4.WeightParameters :=
        { theta := theta, theta_ge_two := htheta,
          y := y, y_pos := hyPos, y_lt_one := hyLt,
          k := k, k_pos := hk,
          sigma := sigma, sigma_ge_theta := hsigma }
      Erdos448.Stage4.Contracts.WeightTypeSpec
          (Erdos448.Stage4.w3Weight q) c3 C3 Lambda3 ∧
        (∀ K : ℕ, 0 < K →
          Erdos448.Stage4.w1Weight K ≤ Erdos448.Stage4.w3Weight q K) ∧
        ∀ K : ℕ, 0 < K →
          Erdos448.Stage4.w2Weight q K ≤ Erdos448.Stage4.w3Weight q K

@[expose] def Erdos448.Stage4.Typed.I_A_LATE_P051F3_EXISTS : Prop :=
  ∀ theta y : ℝ, ∀ k : ℕ, ∀ sigma : ℝ,
    2 ≤ theta → 0 < y → y < 1 → 1 ≤ k → theta ≤ sigma →
      Erdos448.Stage4.Typed.I_D_LATE_P051F3_EXISTS theta y k sigma

@[expose] def Erdos448.Stage4.Typed.I_D_LATE_P051F4_EXISTS
    (theta y : ℝ) (k : ℕ) (sigma : ℝ) : Prop :=
  ∃ (htheta : 2 ≤ theta) (hyPos : 0 < y) (hyLt : y < 1)
    (hk : 1 ≤ k) (hsigma : theta ≤ sigma),
    ∃ c4 C4 Lambda4 : ℝ,
      let q : Erdos448.Stage4.WeightParameters :=
        { theta := theta, theta_ge_two := htheta,
          y := y, y_pos := hyPos, y_lt_one := hyLt,
          k := k, k_pos := hk,
          sigma := sigma, sigma_ge_theta := hsigma }
      Erdos448.Stage4.Contracts.WeightTypeSpec
          (Erdos448.Stage4.w4Weight q) c4 C4 Lambda4 ∧
        (∀ K : ℕ, 0 < K →
          Erdos448.Stage4.w3Weight q K ≤ Erdos448.Stage4.w4Weight q K) ∧
        ∀ K : ℕ, 0 < K →
          Erdos448.Stage4.shift (Erdos448.Stage4.w3Weight q)
              (Erdos448.Stage4.modifierWeight q) K ≤
            Erdos448.Stage4.w4Weight q K

@[expose] def Erdos448.Stage4.Typed.I_A_LATE_P051F4_EXISTS : Prop :=
  ∀ theta y : ℝ, ∀ k : ℕ, ∀ sigma : ℝ,
    2 ≤ theta → 0 < y → y < 1 → 1 ≤ k → theta ≤ sigma →
      Erdos448.Stage4.Typed.I_D_LATE_P051F4_EXISTS theta y k sigma

@[expose] abbrev Erdos448.Stage4.Typed.I_D_LATE_P051G_W
    (_theta _y : ℝ) (_k : ℕ) (_sigma : ℝ) :=
  ℝ × ℝ × ℝ

@[expose] def Erdos448.Stage4.Typed.I_D_LATE_P051G_EXISTS
    (theta y : ℝ) (k : ℕ) (sigma : ℝ) : Prop :=
  ∃ (htheta : 2 ≤ theta) (hyPos : 0 < y) (hyLt : y < 1)
    (hk : 1 ≤ k) (hsigma : theta ≤ sigma),
    ∃ cStar CStar LambdaStar : ℝ,
      let q : Erdos448.Stage4.WeightParameters :=
        { theta := theta, theta_ge_two := htheta,
          y := y, y_pos := hyPos, y_lt_one := hyLt,
          k := k, k_pos := hk,
          sigma := sigma, sigma_ge_theta := hsigma }
      Erdos448.Stage4.Contracts.WeightTypeSpec
          Erdos448.Stage4.a0Weight cStar CStar LambdaStar ∧
        Erdos448.Stage4.Contracts.WeightTypeSpec
          Erdos448.Stage4.w1Weight cStar CStar LambdaStar ∧
        Erdos448.Stage4.Contracts.WeightTypeSpec
          (Erdos448.Stage4.w2Weight q) cStar CStar LambdaStar ∧
        Erdos448.Stage4.Contracts.WeightTypeSpec
          (Erdos448.Stage4.w3Weight q) cStar CStar LambdaStar ∧
        Erdos448.Stage4.Contracts.WeightTypeSpec
          (Erdos448.Stage4.w4Weight q) cStar CStar LambdaStar ∧
        1 + CStar * (2 : ℝ).rpow (-cStar) ≤ LambdaStar ∧
        Erdos448.Stage4.Contracts.ModifierSpec
          (Erdos448.Stage4.modifierWeight q) ∧
        (∀ K : ℕ, 0 < K →
          Erdos448.Stage4.a0Weight K ≤ Erdos448.Stage4.w1Weight K) ∧
        (∀ K : ℕ, 0 < K →
          Erdos448.Stage4.w1Weight K ≤ Erdos448.Stage4.w2Weight q K) ∧
        (∀ K : ℕ, 0 < K →
          Erdos448.Stage4.w1Weight K ≤ Erdos448.Stage4.w3Weight q K) ∧
        (∀ K : ℕ, 0 < K →
          Erdos448.Stage4.w2Weight q K ≤ Erdos448.Stage4.w3Weight q K) ∧
        ∀ K : ℕ, 0 < K →
          Erdos448.Stage4.w3Weight q K ≤ Erdos448.Stage4.w4Weight q K

@[expose] def Erdos448.Stage4.Typed.I_A_LATE_P051G_EXISTS : Prop :=
  ∀ theta y : ℝ, ∀ k : ℕ, ∀ sigma : ℝ,
    2 ≤ theta → 0 < y → y < 1 → 1 ≤ k → theta ≤ sigma →
      Erdos448.Stage4.Typed.I_D_LATE_P051G_EXISTS theta y k sigma

@[expose] def Erdos448.Stage4.Typed.I_D_S7A_SELECTED_WEIGHT
    (theta y : ℝ) (k : ℕ) (sigma : ℝ)
    (w : Erdos448.Stage4.ArithmeticWeight) : Prop :=
  ∃ (htheta : 2 ≤ theta) (hyPos : 0 < y) (hyLt : y < 1)
    (hk : 1 ≤ k) (hsigma : theta ≤ sigma),
    ∃ member : Erdos448.Stage4.Contracts.WeightMember,
      let q : Erdos448.Stage4.WeightParameters :=
        { theta := theta, theta_ge_two := htheta,
          y := y, y_pos := hyPos, y_lt_one := hyLt,
          k := k, k_pos := hk,
          sigma := sigma, sigma_ge_theta := hsigma }
      w = Erdos448.Stage4.Contracts.selectedWeight q member

@[expose] abbrev Erdos448.Stage4.Typed.I_D_S7A_MODIFIER :=
  Erdos448.Stage4.Contracts.ModifierSpec

@[expose] def Erdos448.Stage4.Typed.I_D_S7A_PRIME (p : ℕ) : Prop :=
  p.Prime

@[expose] def Erdos448.Stage4.Typed.I_D_LATE_P051H_EXISTS
    (_theta _y : ℝ) (_k : ℕ) (_sigma : ℝ)
    (w b : Erdos448.Stage4.ArithmeticWeight) (p : ℕ) : Prop :=
  ∃ cStar CStar LambdaStar : ℝ,
    0 < min cStar 1 ∧
      0 < CStar + 2 * LambdaStar ∧
      |Erdos448.Stage4.Contracts.localEulerFactor w b p -
          (1 + w p * b p / p)| ≤
        2 * LambdaStar * (p : ℝ).rpow (-2) ∧
      2 * LambdaStar * (p : ℝ).rpow (-2) ≤
        2 * LambdaStar * (p : ℝ).rpow (-1 - min cStar 1) ∧
      |Erdos448.Stage4.Contracts.localEulerFactor w b p -
          (1 + b p / (2 * p))| ≤
        (CStar + 2 * LambdaStar) *
          (p : ℝ).rpow (-1 - min cStar 1)

@[expose] def Erdos448.Stage4.Typed.I_A_LATE_P051H_EXISTS : Prop :=
  ∀ theta y : ℝ, ∀ k : ℕ, ∀ sigma : ℝ,
    ∀ w b : Erdos448.Stage4.ArithmeticWeight, ∀ p : ℕ,
      2 ≤ theta → 0 < y → y < 1 → 1 ≤ k → theta ≤ sigma →
      Erdos448.Stage4.Typed.I_D_S7A_SELECTED_WEIGHT theta y k sigma w →
      Erdos448.Stage4.Typed.I_D_S7A_MODIFIER b →
      Erdos448.Stage4.Typed.I_D_S7A_PRIME p →
      Erdos448.Stage4.Typed.I_D_LATE_P051H_EXISTS
        theta y k sigma w b p

@[expose] def Erdos448.Stage4.Typed.I_D_S7_P051V_DOMAIN
    (theta y : ℝ) (k : ℕ) (sigma : ℝ) : Prop :=
  2 ≤ theta ∧ 0 < y ∧ y < 1 ∧ 1 ≤ k ∧ theta ≤ sigma

@[expose] def Erdos448.Stage4.Typed.I_D_S7B_P052_DOMAIN
    (theta y : ℝ) (k : ℕ) (sigma : ℝ) (Ksh : ℕ) (z : ℝ) : Prop :=
  Erdos448.Stage4.Typed.I_D_S7_P051V_DOMAIN theta y k sigma ∧
    0 < Ksh ∧ 0 < z

@[expose] abbrev Erdos448.Stage4.Typed.I_D_S7B_P052_W (_theta : ℝ) := ℝ

@[expose] def Erdos448.Stage4.Typed.I_D_S7B_P052_RESULT
    (_theta _y : ℝ) (_k : ℕ) (_sigma : ℝ)
    (Ksh : ℕ) (z Csm : ℝ) : Prop :=
  ∃ hKsh : 0 < Ksh,
    Erdos448.Stage4.Contracts.reciprocalDivisorSum z ⟨Ksh, hKsh⟩ ≤
      Csm * Erdos448.Stage4.w1Weight Ksh *
        Erdos448.Stage4.Contracts.safeLogHalfSum z

@[expose] def Erdos448.Stage4.Typed.I_D_LATE_P052_EXISTS
    (theta y : ℝ) (k : ℕ) (sigma : ℝ) (Ksh : ℕ) (z : ℝ) : Prop :=
  ∃ Csm : ℝ, 0 < Csm ∧
    Erdos448.Stage4.Typed.I_D_S7B_P052_RESULT
      theta y k sigma Ksh z Csm

@[expose] def Erdos448.Stage4.Typed.I_A_LATE_P052_EXISTS : Prop :=
  ∀ theta y : ℝ, ∀ k : ℕ, ∀ sigma : ℝ, ∀ Ksh : ℕ, ∀ z : ℝ,
    Erdos448.Stage4.Typed.I_D_S7B_P052_DOMAIN
        theta y k sigma Ksh z →
      Erdos448.Stage4.Typed.I_D_S7_P051V_DOMAIN theta y k sigma →
      Erdos448.Stage4.Typed.I_D_LATE_P052_EXISTS
        theta y k sigma Ksh z

@[expose] def Erdos448.Stage4.Typed.I_D_S7B_P053_DOMAIN (M : ℝ) : Prop :=
  0 < M

@[expose] abbrev Erdos448.Stage4.Typed.I_D_S7B_P053_W := ℝ

@[expose] def Erdos448.Stage4.Typed.I_D_S7B_P053_RESULT
    (M Cps : ℝ) : Prop :=
  0 < Cps ∧
    Erdos448.Stage4.Contracts.safeLogHalfSum M ≤
      Cps * M * (Erdos448.Stage4.safeLog (2 * M)).rpow (-1 / 2)

@[expose] def Erdos448.Stage4.Typed.I_D_LATE_P053_EXISTS (M : ℝ) : Prop :=
  ∃ Cps : ℝ,
    Erdos448.Stage4.Typed.I_D_S7B_P053_RESULT M Cps

@[expose] def Erdos448.Stage4.Typed.I_A_LATE_P053_EXISTS : Prop :=
  ∀ M : ℝ, Erdos448.Stage4.Typed.I_D_S7B_P053_DOMAIN M →
    Erdos448.Stage4.Typed.I_D_LATE_P053_EXISTS M

@[expose] def Erdos448.Stage4.Typed.I_D_S7B_P055_DOMAIN
    (theta y : ℝ) (k : ℕ) (sigma : ℝ) (Ksh : ℕ) (z : ℝ) : Prop :=
  Erdos448.Stage4.Typed.I_D_S7_P051V_DOMAIN theta y k sigma ∧
    0 < Ksh ∧ 0 < z ∧ theta ^ k ≤ z ∧ sigma ≤ theta ^ k

@[expose] abbrev Erdos448.Stage4.Typed.I_D_S7B_P055_W (_theta : ℝ) := ℝ

@[expose] def Erdos448.Stage4.Typed.I_D_S7B_P055_RESULT
    (theta y : ℝ) (k : ℕ) (sigma : ℝ)
    (Ksh : ℕ) (z Cup : ℝ) : Prop :=
  ∃ (htheta : 2 ≤ theta) (hyPos : 0 < y) (hyLt : y < 1)
    (hk : 1 ≤ k) (hsigma : theta ≤ sigma) (hKsh : 0 < Ksh),
    let q : Erdos448.Stage4.WeightParameters :=
      { theta := theta, theta_ge_two := htheta,
        y := y, y_pos := hyPos, y_lt_one := hyLt,
        k := k, k_pos := hk,
        sigma := sigma, sigma_ge_theta := hsigma }
    Erdos448.Stage4.shiftedMean q z ⟨Ksh, hKsh⟩ ≤
      Cup * z * Erdos448.Stage4.w2Weight q Ksh *
        (Real.log sigma).rpow (-y / 2) *
        (k : ℝ).rpow ((y - 1) / 2) *
        (Erdos448.Stage4.safeLog z).rpow (-1 / 2)

@[expose] def Erdos448.Stage4.Typed.I_D_LATE_P055_EXISTS
    (theta y : ℝ) (k : ℕ) (sigma : ℝ) (Ksh : ℕ) (z : ℝ) : Prop :=
  ∃ Cup : ℝ, 0 < Cup ∧
    Erdos448.Stage4.Typed.I_D_S7B_P055_RESULT
      theta y k sigma Ksh z Cup

@[expose] def Erdos448.Stage4.Typed.I_A_LATE_P055_EXISTS : Prop :=
  ∀ theta y : ℝ, ∀ k : ℕ, ∀ sigma : ℝ, ∀ Ksh : ℕ, ∀ z : ℝ,
    Erdos448.Stage4.Typed.I_D_S7B_P055_DOMAIN
        theta y k sigma Ksh z →
      Erdos448.Stage4.Typed.I_D_S7_P051V_DOMAIN theta y k sigma →
      Erdos448.Stage4.Typed.I_D_LATE_P055_EXISTS
        theta y k sigma Ksh z

@[expose] def Erdos448.Stage4.Typed.I_D_S7B_P056_DOMAIN
    (theta y : ℝ) (k : ℕ) (sigma : ℝ) (Ksh : ℕ) (z : ℝ) : Prop :=
  Erdos448.Stage4.Typed.I_D_S7_P051V_DOMAIN theta y k sigma ∧
    0 < Ksh ∧ 0 < z ∧ sigma ≤ z ∧ z < theta ^ k

@[expose] abbrev Erdos448.Stage4.Typed.I_D_S7B_P056_W (_theta : ℝ) := ℝ

@[expose] def Erdos448.Stage4.Typed.I_D_S7B_P056_RESULT
    (theta y : ℝ) (k : ℕ) (sigma : ℝ)
    (Ksh : ℕ) (z Cmid : ℝ) : Prop :=
  ∃ (htheta : 2 ≤ theta) (hyPos : 0 < y) (hyLt : y < 1)
    (hk : 1 ≤ k) (hsigma : theta ≤ sigma) (hKsh : 0 < Ksh),
    let q : Erdos448.Stage4.WeightParameters :=
      { theta := theta, theta_ge_two := htheta,
        y := y, y_pos := hyPos, y_lt_one := hyLt,
        k := k, k_pos := hk,
        sigma := sigma, sigma_ge_theta := hsigma }
    Erdos448.Stage4.shiftedMean q z ⟨Ksh, hKsh⟩ ≤
      Cmid * z * Erdos448.Stage4.w2Weight q Ksh *
        (Real.log sigma).rpow (-y / 2) *
        (Erdos448.Stage4.safeLog z).rpow (y / 2 - 1)

@[expose] def Erdos448.Stage4.Typed.I_D_LATE_P056_EXISTS
    (theta y : ℝ) (k : ℕ) (sigma : ℝ) (Ksh : ℕ) (z : ℝ) : Prop :=
  ∃ Cmid : ℝ, 0 < Cmid ∧
    Erdos448.Stage4.Typed.I_D_S7B_P056_RESULT
      theta y k sigma Ksh z Cmid

@[expose] def Erdos448.Stage4.Typed.I_A_LATE_P056_EXISTS : Prop :=
  ∀ theta y : ℝ, ∀ k : ℕ, ∀ sigma : ℝ, ∀ Ksh : ℕ, ∀ z : ℝ,
    Erdos448.Stage4.Typed.I_D_S7B_P056_DOMAIN
        theta y k sigma Ksh z →
      Erdos448.Stage4.Typed.I_D_S7_P051V_DOMAIN theta y k sigma →
      Erdos448.Stage4.Typed.I_D_LATE_P056_EXISTS
        theta y k sigma Ksh z

@[expose] def Erdos448.Stage4.Typed.I_D_S7B_P058_DOMAIN
    (theta y : ℝ) (k : ℕ) (sigma x : ℝ) : Prop :=
  Erdos448.Stage4.Typed.I_D_S7_P051V_DOMAIN theta y k sigma ∧
    sigma ≤ theta ^ k ∧ theta ^ (2 * k - 1) < x

@[expose] abbrev Erdos448.Stage4.Typed.I_D_S7B_P058_W (_theta : ℝ) := ℝ

@[expose] def Erdos448.Stage4.Typed.I_D_S7B_P058_RESULT
    (theta y : ℝ) (k : ℕ) (sigma _x Cout : ℝ) : Prop :=
  ∃ (htheta : 2 ≤ theta) (hyPos : 0 < y) (hyLt : y < 1)
    (hk : 1 ≤ k) (hsigma : theta ≤ sigma),
    let q : Erdos448.Stage4.WeightParameters :=
      { theta := theta, theta_ge_two := htheta,
        y := y, y_pos := hyPos, y_lt_one := hyLt,
        k := k, k_pos := hk,
        sigma := sigma, sigma_ge_theta := hsigma }
    Erdos448.Stage4.regularOuter q ≤
      Cout * theta ^ k * (Real.log sigma).rpow (-y / 2) *
        (k : ℝ).rpow (y / 2 - 1) * Erdos448.Stage4.w4WindowSum q

@[expose] def Erdos448.Stage4.Typed.I_D_LATE_P058_EXISTS
    (theta y : ℝ) (k : ℕ) (sigma x : ℝ) : Prop :=
  ∃ Cout : ℝ, 0 < Cout ∧
    Erdos448.Stage4.Typed.I_D_S7B_P058_RESULT
      theta y k sigma x Cout

@[expose] def Erdos448.Stage4.Typed.I_A_LATE_P058_EXISTS : Prop :=
  ∀ theta y : ℝ, ∀ k : ℕ, ∀ sigma x : ℝ,
    Erdos448.Stage4.Typed.I_D_S7B_P058_DOMAIN theta y k sigma x →
      Erdos448.Stage4.Typed.I_D_S7_P051V_DOMAIN theta y k sigma →
      Erdos448.Stage4.Typed.I_D_LATE_P058_EXISTS theta y k sigma x

@[expose] def Erdos448.Stage4.Typed.I_D_S7B_P059_DOMAIN
    (Q : Type*) (wFamily : Q → Erdos448.Stage4.ArithmeticWeight)
    (cw CwErr LambdaW : ℝ) (_q : Q) (Z : ℝ) : Prop :=
  Nonempty Q ∧ 0 < cw ∧ 0 < CwErr ∧ 0 < LambdaW ∧
    (∀ q : Q, Erdos448.Stage4.Contracts.WeightTypeSpec
      (wFamily q) cw CwErr LambdaW) ∧ 2 ≤ Z

@[expose] abbrev Erdos448.Stage4.Typed.I_D_S7B_P059_W
    (_Q : Type*) (_wFamily : _Q → Erdos448.Stage4.ArithmeticWeight)
    (_cw _CwErr _LambdaW : ℝ) := ℝ

@[expose] def Erdos448.Stage4.Typed.I_D_S7B_P059_RESULT
    (Q : Type*) (wFamily : Q → Erdos448.Stage4.ArithmeticWeight)
    (_cw _CwErr _LambdaW : ℝ) (q : Q) (Z Cmean : ℝ) : Prop :=
  0 < Cmean ∧
    Erdos448.Stage4.Contracts.familyPartialSum wFamily q Z ≤
      Cmean * Z * (Real.log Z).rpow (-1 / 2)

@[expose] def Erdos448.Stage4.Typed.I_D_S7B_P059_LAMBDA
    (LambdaW : ℝ) : ℝ := max 1 LambdaW

@[expose] def Erdos448.Stage4.Typed.I_D_S7B_P059_ETA (cw : ℝ) : ℝ :=
  min cw 1

@[expose] def Erdos448.Stage4.Typed.I_D_S7B_P059_CERR
    (CwErr LambdaW : ℝ) : ℝ := CwErr + 2 * LambdaW

@[expose] noncomputable def Erdos448.Stage4.Typed.I_D_S7B_P059_L
    (Q : Type*) (wFamily : Q → Erdos448.Stage4.ArithmeticWeight)
    (q : Q) : ℕ → ℝ := fun p =>
  ∑' j : ℕ, wFamily q (p ^ j) / (p : ℝ) ^ j

@[expose] noncomputable def Erdos448.Stage4.Typed.I_D_S7B_P059_COEFF
    (Q : Type*) : Q → ℝ := fun _ => 1 / 2

@[expose] noncomputable def Erdos448.Stage4.Typed.I_D_S7B_P059_LOCAL
    (Q : Type*) (wFamily : Q → Erdos448.Stage4.ArithmeticWeight) :
    Q → ℕ → ℝ := fun q p =>
  ∑' j : ℕ, wFamily q (p ^ j) / (p : ℝ) ^ j

@[expose] def Erdos448.Stage4.Typed.I_D_LATE_P059_EXISTS
    (Q : Type*) (wFamily : Q → Erdos448.Stage4.ArithmeticWeight)
    (cw CwErr LambdaW : ℝ) (q : Q) (Z : ℝ) : Prop :=
  ∃ Cmean : ℝ,
    Erdos448.Stage4.Typed.I_D_S7B_P059_RESULT
      Q wFamily cw CwErr LambdaW q Z Cmean

@[expose] def Erdos448.Stage4.Typed.I_A_LATE_P059_EXISTS : Prop :=
  ∀ (Q : Type*) (wFamily : Q → Erdos448.Stage4.ArithmeticWeight),
    ∀ cw CwErr LambdaW : ℝ, ∀ q : Q, ∀ Z : ℝ,
      Erdos448.Stage4.Typed.I_D_S7B_P059_DOMAIN
          Q wFamily cw CwErr LambdaW q Z →
        Erdos448.Stage4.Typed.I_D_LATE_P059_EXISTS
          Q wFamily cw CwErr LambdaW q Z
