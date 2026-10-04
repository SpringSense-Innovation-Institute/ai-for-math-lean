module

import all Mathlib.Basic.Real.Basic
public import Erdos448.stage4.RootObjects

public section

set_option backward.isDefEq.respectTransparency false

/-!
Lean proposition aliases for S3 P-090--P-102, P-110--P-120, and
FT-448-NEG-017.  Mathematical authority is the matching headings of
`Erdos448/stage3/canonical/CURRENT.md`, SHA-256
`1974e1237d99cb34aca984ee81273a55676e70fdc4f047080e79d579a42aacda`.

This file contains representation contracts only: no theorem declarations,
axioms, or proof implementations.  Sequential structure fields deliberately
preserve the S3 witness and constant-selection order.
-/

namespace Erdos448.Stage4.Contracts

open Filter Finset Set
open scoped BigOperators Topology

noncomputable section

@[expose] def cutoffDomain (theta x : ℝ) (htheta : 2 ≤ theta) (hx : 0 < x) :
    MovingCutoffDomain :=
  { theta := theta, theta_ge_two := htheta, x := x, x_pos := hx }

@[expose] def p4Lemma4Parameters
    (theta epsilonInt sigma xi : ℝ) (htheta : 2 ≤ theta)
    (he0 : 0 < epsilonInt) (he1 : epsilonInt ≤ 1 / 10)
    (hsigma : theta ≤ sigma) (hxi : 1 < xi) : Lemma4Parameters :=
  { epsilonInt := epsilonInt, epsilonInt_pos := he0,
    epsilonInt_le_tenth := he1, xi := xi, xi_gt_one := hxi,
    sigma := sigma, sigma_ge_two := htheta.trans hsigma,
    theta := theta, theta_ge_two := htheta, sigma_ge_theta := hsigma }

@[expose] def p4Mean
    (theta epsilonInt sigma xi x : ℝ) (htheta : 2 ≤ theta)
    (he0 : 0 < epsilonInt) (he1 : epsilonInt ≤ 1 / 10)
    (hsigma : theta ≤ sigma) (hxi : 1 < xi) : ℝ :=
  let q := p4Lemma4Parameters theta epsilonInt sigma xi htheta he0 he1 hsigma hxi
  ∑ n ∈ positiveNatsBelow x,
    if hn : 0 < n then normalizedClosePair q ⟨n, hn⟩ else 0

/-! P-090: finite support and the moving-cutoff consequence. -/

structure P090Witness (q : SharpParameters) (n : PosNat) where
  d : PosNat
  d' : PosNat
  t : PosNat
  product_dvd : d.1 * d'.1 * t.1 ∣ n.1
  bin_lower : q.theta ^ q.k ≤ (d.1 : ℝ)
  bin_upper : (d.1 : ℝ) < q.theta ^ (q.k + 1)
  close : Close q.theta d d'
  summand_pos :
    0 < (roughIndicator d.1 q.sigma : ℝ) *
      q.y.rpow (omegaBelowRaw (d.1 * t.1) (q.theta ^ q.k) : ℝ) *
      roughIndicator t.1 q.sigma
  product_lower : q.theta ^ (2 * q.k - 1) < (d.1 * d'.1 : ℕ)
  product_le_triple : d.1 * d'.1 ≤ d.1 * d'.1 * t.1
  triple_le_n : d.1 * d'.1 * t.1 ≤ n.1
  cutoff_consequence : ∀ x : ℝ, (n.1 : ℝ) < x → q.theta ^ (2 * q.k - 1) < x

@[expose] def P090Statement : Prop :=
  ∀ q : SharpParameters, 1 ≤ q.k → ∀ n : PosNat,
    0 < fkSharp q n → Nonempty (P090Witness q n)

/-! P-091: exact real/integer moving cutoff. -/

@[expose] def P091Statement : Prop :=
  ∀ theta : ℝ, ∀ htheta : 2 ≤ theta, ∀ x : ℝ, ∀ hx : 0 < x, ∀ k : ℤ,
    let q := cutoffDomain theta x htheta hx
    (theta ^ (2 * k - 1) < x ↔ (k : ℝ) < movingCutoffReal q) ∧
      (movingCutoff q : ℝ) < movingCutoffReal q ∧
      movingCutoffReal q ≤ (movingCutoff q : ℝ) + 1 ∧
      ((k : ℝ) < movingCutoffReal q → k ≤ movingCutoff q)

/-! P-092: exact finite restriction of the Proposition-2 majorant. -/

structure P092Parameters where
  epsilonInt : ℝ
  epsilonInt_pos : 0 < epsilonInt
  epsilonInt_le_tenth : epsilonInt ≤ 1 / 10
  xi : ℝ
  xi_gt_one : 1 < xi
  sigma : ℝ
  theta : ℝ
  theta_ge_two : 2 ≤ theta
  sigma_ge_theta : theta ≤ sigma
  y : ℝ
  y_pos : 0 < y
  y_lt_one : y < 1
  x : ℝ
  x_gt_U0 : Real.exp (Real.log xi * Real.log sigma) < x

@[expose] def P092APow (q : P092Parameters) : ℝ :=
  -(1 / 2 + q.epsilonInt) * Real.log q.y

@[expose] def p092Cutoff (q : P092Parameters) : ℤ :=
  movingCutoff
    (cutoffDomain q.theta q.x q.theta_ge_two
      (Real.exp_pos _ |>.trans q.x_gt_U0))

@[expose] def p092Sharp (q : P092Parameters) (k : ℕ) : SharpParameters :=
  { y := q.y, y_pos := q.y_pos, y_lt_one := q.y_lt_one, k := k,
    theta := q.theta, theta_ge_two := q.theta_ge_two,
    sigma := q.sigma, sigma_ge_theta := q.sigma_ge_theta }

@[expose] def P092LeftSum (q : P092Parameters) : ℝ :=
  let l4 := p4Lemma4Parameters q.theta q.epsilonInt q.sigma q.xi
    q.theta_ge_two q.epsilonInt_pos q.epsilonInt_le_tenth
    q.sigma_ge_theta q.xi_gt_one
  ∑ n ∈ positiveNatsBelow q.x,
    if hn : 0 < n then
      if Real.exp (Real.log q.xi * Real.log q.sigma) < n then
        normalizedClosePair l4 ⟨n, hn⟩
      else 0
    else 0

@[expose] def P092KSum (q : P092Parameters) : ℝ :=
  ∑ k ∈ Finset.Icc (lowerBinIndex q.sigma q.theta) (p092Cutoff q).toNat,
    (k : ℝ).rpow (P092APow q) *
      (∑ n ∈ positiveNatsBelow q.x,
        if hn : 0 < n then fkSharp (p092Sharp q k) ⟨n, hn⟩ else 0)

@[expose] def P092Statement : Prop :=
  ∀ q : P092Parameters,
    P092LeftSum q ≤
      (2 * Real.log q.xi * Real.log q.theta / Real.log q.sigma).rpow
        (P092APow q) * P092KSum q ∧
    ((p092Cutoff q : ℤ) < (lowerBinIndex q.sigma q.theta : ℤ) →
      P092KSum q = 0 ∧ P092LeftSum q = 0)

/-! P-093--P-095: endpoint comparison and both reversed negative powers. -/

structure P093Witness (theta : ℝ) (htheta : 2 ≤ theta) where
  cLower : ℝ
  cUpper : ℝ
  cLower_pos : 0 < cLower
  cUpper_pos : 0 < cUpper
  specification : ∀ x : ℝ, ∀ hx : 0 < x, ∀ k : ℤ,
    let q := cutoffDomain theta x htheta hx
    k ≤ movingCutoff q →
      Real.log (2 * x * theta ^ (1 - 2 * k)) =
          Real.log 2 + 2 * (movingCutoffReal q - k) * Real.log theta ∧
        (movingCutoff q : ℝ) - k < movingCutoffReal q - k ∧
        movingCutoffReal q - k ≤ (movingCutoff q : ℝ) - k + 1 ∧
        cLower * ((movingCutoff q - k + 1 : ℤ) : ℝ) ≤
          safeLog (2 * x * theta ^ (1 - 2 * k)) ∧
        safeLog (2 * x * theta ^ (1 - 2 * k)) ≤
          cUpper * ((movingCutoff q - k + 1 : ℤ) : ℝ)

@[expose] def P093Statement : Prop :=
  ∀ theta : ℝ, ∀ htheta : 2 ≤ theta, Nonempty (P093Witness theta htheta)

structure P094Witness (theta : ℝ) (htheta : 2 ≤ theta) where
  endpoint : P093Witness theta htheta
  specification : ∀ y : ℝ, 0 < y → y < 1 →
    ∀ x : ℝ, ∀ hx : 0 < x, ∀ k : ℤ,
      let q := cutoffDomain theta x htheta hx
      k ≤ movingCutoff q →
        endpoint.cUpper.rpow ((y - 1) / 2) *
              (((movingCutoff q - k + 1 : ℤ) : ℝ).rpow ((y - 1) / 2)) ≤
            (safeLog (2 * x * theta ^ (1 - 2 * k))).rpow ((y - 1) / 2) ∧
          (safeLog (2 * x * theta ^ (1 - 2 * k))).rpow ((y - 1) / 2) ≤
            endpoint.cLower.rpow ((y - 1) / 2) *
              (((movingCutoff q - k + 1 : ℤ) : ℝ).rpow ((y - 1) / 2))

@[expose] def P094Statement : Prop :=
  ∀ theta : ℝ, ∀ htheta : 2 ≤ theta, Nonempty (P094Witness theta htheta)

structure P095Witness (theta : ℝ) (htheta : 2 ≤ theta) where
  endpoint : P093Witness theta htheta
  specification : ∀ x : ℝ, ∀ hx : 0 < x, ∀ k : ℤ,
    let q := cutoffDomain theta x htheta hx
    k ≤ movingCutoff q →
      endpoint.cUpper.rpow (-1 / 2) *
            (((movingCutoff q - k + 1 : ℤ) : ℝ).rpow (-1 / 2)) ≤
          (safeLog (2 * x * theta ^ (1 - 2 * k))).rpow (-1 / 2) ∧
        (safeLog (2 * x * theta ^ (1 - 2 * k))).rpow (-1 / 2) ≤
          endpoint.cLower.rpow (-1 / 2) *
            (((movingCutoff q - k + 1 : ℤ) : ℝ).rpow (-1 / 2))

@[expose] def P095Statement : Prop :=
  ∀ theta : ℝ, ∀ htheta : 2 ≤ theta, Nonempty (P095Witness theta htheta)

/-! P-096--P-101: exponent normalization and fixed-parameter little-o. -/

@[expose] def P096Statement : Prop :=
  ∀ y epsilonInt : ℝ, 0 < y → y < 1 → 0 < epsilonInt →
    epsilonInt < -(1 - y + (1 / 2) * Real.log y) / Real.log y →
      0 < -(1 / 2 + epsilonInt) * Real.log y ∧
      -(1 / 2 + epsilonInt) * Real.log y < 1 - y

@[expose] def P097Statement : Prop :=
  ∀ y aPow : ℝ, 0 < y → y < 1 → 0 < aPow → aPow < 1 - y →
    ∀ K0 : ℕ, 1 ≤ K0 →
      (∑' k : ℕ, if K0 ≤ k then (k : ℝ).rpow (y - 2 + aPow) else 0) ≤
          (1 + 1 / (1 - y - aPow)) * (K0 : ℝ).rpow (y - 1 + aPow) ∧
      ∀ sigma theta : ℝ, 2 ≤ theta → theta ≤ sigma →
        K0 = lowerBinIndex sigma theta →
          (1 / 2) * (Real.log sigma / Real.log theta) ≤ K0 ∧
          (K0 : ℝ) ≤ (3 / 2) * (Real.log sigma / Real.log theta)

@[expose] def movingPowerSum (K0 N : ℕ) (r s : ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc K0 N,
    (k : ℝ).rpow r * ((N - k + 1 : ℕ) : ℝ).rpow s

@[expose] def P098Statement : Prop :=
  ∀ K0 : ℕ, 1 ≤ K0 → ∀ y aPow : ℝ,
    0 < y → y < 1 → 0 < aPow → aPow < 1 - y →
      (fun N : ℕ => movingPowerSum K0 N ((y - 3) / 2 + aPow) ((y - 1) / 2))
        =o[atTop] (fun _ : ℕ => (1 : ℝ))

@[expose] def P099Statement : Prop :=
  ∀ K0 : ℕ, 1 ≤ K0 → ∀ y aPow : ℝ,
    0 < y → y < 1 → 0 < aPow → aPow < 1 - y →
      (fun N : ℕ => movingPowerSum K0 N ((y - 3) / 2 + aPow) (-1 / 2))
        =o[atTop] (fun _ : ℕ => (1 : ℝ))

@[expose] def actualMovingLogSum
    (theta sigma y aPow exponent x : ℝ) (htheta : 2 ≤ theta) : ℝ :=
  if hx : 0 < x then
    let q := cutoffDomain theta x htheta hx
    ∑ k ∈ Finset.Icc (lowerBinIndex sigma theta) (movingCutoff q).toNat,
      (k : ℝ).rpow ((y - 3) / 2 + aPow) *
        (safeLog (2 * x * theta ^ (1 - (2 : ℤ) * k))).rpow exponent
  else 0

@[expose] def P100Statement : Prop :=
  ∀ theta sigma : ℝ, ∀ htheta : 2 ≤ theta, theta ≤ sigma →
    ∀ y aPow : ℝ, 0 < y → y < 1 → 0 < aPow → aPow < 1 - y →
      (fun x : ℝ => actualMovingLogSum theta sigma y aPow ((y - 1) / 2) x htheta)
        =o[atTop] (fun _ : ℝ => (1 : ℝ))

@[expose] def P101Statement : Prop :=
  ∀ theta sigma : ℝ, ∀ htheta : 2 ≤ theta, theta ≤ sigma →
    ∀ y aPow : ℝ, 0 < y → y < 1 → 0 < aPow → aPow < 1 - y →
      (fun x : ℝ => actualMovingLogSum theta sigma y aPow (-1 / 2) x htheta)
        =o[atTop] (fun _ : ℝ => (1 : ℝ))

/-! P-102: the main coefficient precedes sigma/xi; the little-o witness follows them. -/

structure P102Parameters where
  theta : ℝ
  theta_ge_two : 2 ≤ theta
  y : ℝ
  y_pos : 0 < y
  y_lt_one : y < 1
  epsilonInt : ℝ
  epsilonInt_pos : 0 < epsilonInt
  epsilonInt_le_tenth : epsilonInt ≤ 1 / 10
  admissible :
    epsilonInt < -(1 - y + (1 / 2) * Real.log y) / Real.log y

@[expose] def P102APow (q : P102Parameters) : ℝ :=
  -(1 / 2 + q.epsilonInt) * Real.log q.y

structure P102RemainderSpec
    (q : P102Parameters) (coefficient sigma xi : ℝ)
    (hsigma : q.theta ≤ sigma) (hxi : 1 < xi) where
  remainder : ℝ → ℝ
  littleO : remainder =o[atTop] (fun x : ℝ => x)
  eventual_bound : ∀ᶠ x : ℝ in atTop,
    p4Mean q.theta q.epsilonInt sigma xi x q.theta_ge_two
        q.epsilonInt_pos q.epsilonInt_le_tenth hsigma hxi ≤
      coefficient * x * (Real.log xi).rpow (P102APow q) *
          (Real.log sigma).rpow (-1) + remainder x

structure P102Witness (q : P102Parameters) where
  coefficient : ℝ
  coefficient_pos : 0 < coefficient
  fixed_parameter_remainder : ∀ sigma : ℝ, ∀ hsigma : q.theta ≤ sigma,
    ∀ xi : ℝ, ∀ hxi : 1 < xi,
      P102RemainderSpec q coefficient sigma xi hsigma hxi

@[expose] def P102Statement : Prop :=
  ∀ q : P102Parameters, Nonempty (P102Witness q)

/-! P-110--P-112: specialization, pointwise lower bound, and density bound. -/

@[expose] def tauPlusAtTwo (n : PosNat) : ℕ := tauPlus n 2

@[expose] def P110Statement : Prop :=
  ∀ n : PosNat,
    roughIndicator n.1 2 = 1 ∧ roughTau n 2 = tau n ∧
      tauPlus n 2 = tauPlusAtTwo n ∧ roughDensity 2 = 1

@[expose] def twoLemma4Parameters
    (epsilonInt xi : ℝ) (he0 : 0 < epsilonInt)
    (he1 : epsilonInt ≤ 1 / 10) (hxi : 1 < xi) : Lemma4Parameters :=
  { epsilonInt := epsilonInt, epsilonInt_pos := he0,
    epsilonInt_le_tenth := he1, xi := xi, xi_gt_one := hxi,
    sigma := 2, sigma_ge_two := le_rfl, theta := 2,
    theta_ge_two := le_rfl, sigma_ge_theta := le_rfl }

@[expose] def P111Statement : Prop :=
  ∀ epsilonInt xi : ℝ, ∀ he0 : 0 < epsilonInt,
    ∀ he1 : epsilonInt ≤ 1 / 10, ∀ hxi : 1 < xi,
    ∀ A : Set ℕ,
      L4Spec (twoLemma4Parameters epsilonInt xi he0 he1 hxi) A →
      ∀ n : PosNat, n.1 ∈ A → ∀ alpha : ℝ,
        0 < alpha → alpha ≤ 2 / 5 →
        (tauPlusAtTwo n : ℝ) ≤ alpha * tau n →
          4 / (5 * alpha) - 1 ≤
              normalizedClosePair
                (twoLemma4Parameters epsilonInt xi he0 he1 hxi) n ∧
            2 / (5 * alpha) ≤ 4 / (5 * alpha) - 1

structure P112Parameters where
  epsilonInt : ℝ
  epsilonInt_pos : 0 < epsilonInt
  epsilonInt_le_tenth : epsilonInt ≤ 1 / 10
  y : ℝ
  y_pos : 0 < y
  y_lt_one : y < 1
  admissible :
    epsilonInt < -(1 - y + (1 / 2) * Real.log y) / Real.log y

@[expose] def P112ABal (q : P112Parameters) : ℝ :=
  -(1 / 2 + q.epsilonInt) * Real.log q.y

@[expose] def P112BBal (q : P112Parameters) : ℝ :=
  (9 / 10) * q.epsilonInt ^ 2

structure P112Witness (q : P112Parameters) where
  Cgrid : ℝ
  Cgrid_pos : 0 < Cgrid
  Xi0 : ℝ
  Xi0_gt_one : 1 < Xi0
  CP4 : ℝ
  CP4_pos : 0 < CP4
  Cden : ℝ
  Cden_pos : 0 < Cden
  density_bound : ∀ xi : ℝ, Xi0 ≤ xi → ∀ alpha : ℝ,
    0 < alpha → alpha ≤ 2 / 5 →
      UpperDensityAtMost (densityEvent alpha)
        (Cden * (alpha * (Real.log xi).rpow (P112ABal q) +
          (Real.log xi).rpow (-P112BBal q)))

@[expose] def P112Statement : Prop :=
  ∀ q : P112Parameters, Nonempty (P112Witness q)

/-! P-113--P-117: parameter selection, balance, and uniform interior result. -/

structure P113Witness (delta : ℝ) where
  y : ℝ
  y_pos : 0 < y
  y_lt_one : y < 1
  admissible :
    1 / 10 < -(1 - y + (1 / 2) * Real.log y) / Real.log y
  exponent_loss : 0.009 / (0.009 - 0.6 * Real.log y) ≥ 1 - delta

@[expose] def P113Statement : Prop :=
  ∀ delta : ℝ, 0 < delta → delta < 1 → Nonempty (P113Witness delta)

@[expose] def P114Statement : Prop :=
  ∀ y alpha : ℝ, 0 < y → y < 1 → 0 < alpha → alpha < 1 →
    let aBal := -0.6 * Real.log y
    let bBal := 0.009
    let L := alpha.rpow (-1 / (aBal + bBal))
    let xi := Real.exp L
    0 < aBal ∧ 0 < bBal ∧ 0 < L ∧ Real.log xi = L ∧
      alpha * L.rpow aBal = L.rpow (-bBal) ∧
      L.rpow (-bBal) = alpha.rpow (bBal / (aBal + bBal)) ∧
      bBal / (aBal + bBal) = 0.009 / (0.009 - 0.6 * Real.log y)

structure P115Witness (delta : ℝ) (selected : P113Witness delta) where
  Cgrid : ℝ
  Cgrid_pos : 0 < Cgrid
  Xi0 : ℝ
  Xi0_gt_one : 1 < Xi0
  CP4 : ℝ
  CP4_pos : 0 < CP4
  Cden : ℝ
  Cden_pos : 0 < Cden
  alpha0 : ℝ
  alpha0_pos : 0 < alpha0
  alpha0_le_two_fifths : alpha0 ≤ 2 / 5
  Csmall : ℝ
  Csmall_pos : 0 < Csmall
  small_alpha_bound : ∀ alpha : ℝ, 0 < alpha → alpha < alpha0 →
    let aBal := -0.6 * Real.log selected.y
    let bBal := 0.009
    let L := alpha.rpow (-1 / (aBal + bBal))
    let xi := Real.exp L
    Xi0 ≤ xi ∧
      UpperDensityAtMost (densityEvent alpha) (Csmall * alpha.rpow (1 - delta))

@[expose] def P115Statement : Prop :=
  ∀ delta : ℝ, 0 < delta → delta < 1 →
    ∀ selected : P113Witness delta, Nonempty (P115Witness delta selected)

@[expose] def P116Statement : Prop :=
  ∀ delta alpha0 alpha : ℝ,
    0 < delta → delta < 1 → 0 < alpha0 → alpha0 ≤ 1 →
    alpha0 ≤ alpha → alpha ≤ 1 →
      UpperDensityAtMost (densityEvent alpha) 1 ∧
      1 ≤ alpha0.rpow (-(1 - delta)) * alpha.rpow (1 - delta)

@[expose] def P117Statement : Prop :=
  ∀ delta : ℝ, 0 < delta → delta < 1 → Nonempty (InteriorDensityBound delta)

/-! P-118--P-120: endpoints and the strict counterevent. -/

@[expose] def P118Statement : Prop :=
  (∀ n : PosNat, 1 ≤ tauPlusAtTwo n) ∧
    densityEvent 0 = ∅ ∧ UpperDensityAtMost (densityEvent 0) 0

@[expose] def P119Statement : Prop :=
  ∀ delta alpha : ℝ, 1 ≤ delta → 0 < alpha → alpha ≤ 1 →
    UpperDensityAtMost (densityEvent alpha) 1 ∧ 1 ≤ alpha.rpow (1 - delta)

structure P120Witness where
  delta : ℝ
  delta_pos : 0 < delta
  delta_lt_one : delta < 1
  Cdelta : ℝ
  Cdelta_pos : 0 < Cdelta
  counterexample : CounterexampleWitness
  alpha_lt_cutoff :
    counterexample.epsilon < min 1 (Cdelta.rpow (-1 / (1 - delta)))

@[expose] def P120Statement : Prop := Nonempty P120Witness

/-! The exact final assertion and its parametric S8 linking contract. -/

@[expose] def FT448NEG017Statement : Prop := NegativeAnswer

@[expose] def FT448NEG017ParametricContract : Prop :=
  P120Statement → NegativeAnswer

end

end Erdos448.Stage4.Contracts

/-! ## Binder-faithful lowering interfaces: P-090 finite support -/

@[expose] def Erdos448.Stage4.Typed.I_S_P_090
    (theta y : ℝ) (k : ℕ) (sigma : ℝ) (n d d' t : ℕ) : Prop :=
  ∀ (htheta : 2 ≤ theta) (hyPos : 0 < y) (hyLt : y < 1)
    (hk : 1 ≤ k) (hsigma : theta ≤ sigma) (hn : 0 < n),
    let q : Erdos448.Stage4.SharpParameters :=
      { y := y, y_pos := hyPos, y_lt_one := hyLt,
        k := k, theta := theta, theta_ge_two := htheta,
        sigma := sigma, sigma_ge_theta := hsigma }
    0 < Erdos448.Stage4.fkSharp q ⟨n, hn⟩ →
      ∃ (hd : 0 < d) (hd' : 0 < d') (ht : 0 < t),
        d * d' * t ∣ n ∧
          theta ^ k ≤ (d : ℝ) ∧ (d : ℝ) < theta ^ (k + 1) ∧
          Erdos448.Stage4.Close theta ⟨d, hd⟩ ⟨d', hd'⟩ ∧
          0 < (Erdos448.Stage4.roughIndicator d sigma : ℝ) *
            y.rpow (Erdos448.Stage4.omegaBelowRaw (d * t) (theta ^ k) : ℝ) *
            Erdos448.Stage4.roughIndicator t sigma ∧
          theta ^ (2 * k - 1) < (d * d' : ℕ) ∧
          d * d' ≤ d * d' * t ∧ d * d' * t ≤ n ∧
          ∀ x : ℝ, (n : ℝ) < x → theta ^ (2 * k - 1) < x

@[expose] def Erdos448.Stage4.Typed.I_D_LATE_P090_EXISTS
    (theta y : ℝ) (k : ℕ) (sigma : ℝ) (n : ℕ) : Prop :=
  ∃ d d' t : ℕ,
    Erdos448.Stage4.Typed.I_S_P_090 theta y k sigma n d d' t

@[expose] def Erdos448.Stage4.Typed.I_A_LATE_P090_EXISTS : Prop :=
  ∀ theta y : ℝ, ∀ k : ℕ, ∀ sigma : ℝ, ∀ n : ℕ,
    Erdos448.Stage4.Typed.I_D_LATE_P090_EXISTS theta y k sigma n
