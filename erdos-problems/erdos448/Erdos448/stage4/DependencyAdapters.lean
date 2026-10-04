module

import all Mathlib.Basic.Real.Basic
public import Erdos448.dependencies.«DP-MEAN».stage4.Design
public import Erdos448.dependencies.«DP-MERTENS».stage4.DP_Mertens_Design
public import Erdos448.stage4.contracts.GroupA

public section

set_option backward.isDefEq.respectTransparency false

/-!
Parent-owned representation adapter between the accepted DP-MEAN target and
the parent `EXT-001` contract.

The two targets use distinct namespaces, structures, and strict-cutoff
definitions.  This module records the exact equalities/equivalences that an
adapter proof must certify and exposes the final target conversion without
asserting it.
-/

namespace Erdos448.Stage4.DependencyAdapters

open Erdos448.Stage4
open Erdos448.Stage4.Contracts

noncomputable section

/-- A certified adapter must account for every representation boundary before
converting `DPMean.T001Statement` into the parent `EXT001Statement`. -/
structure DPMeanEXT001Adapter : Prop where
  parameter_range_iff : ∀ lambda1 lambda2 : ℝ,
    MeanParameterRange lambda1 lambda2 ↔
      Erdos448.DPMean.ParameterRange lambda1 lambda2
  nonnegative_multiplicative_iff : ∀ h : ArithmeticWeight,
    NonnegativeMultiplicativeWeight h ↔
      Erdos448.DPMean.NonnegativeMultiplicative h
  prime_power_geometric_bound_iff :
    ∀ h : ArithmeticWeight, ∀ lambda1 lambda2 : ℝ,
      PrimePowerGeometricBound h lambda1 lambda2 ↔
        Erdos448.DPMean.PrimePowerGeometricBound h lambda1 lambda2
  strict_nat_domain_eq : ∀ X : ℝ,
    Erdos448.DPMean.strictNatDomain X = positiveNatsBelow X
  strict_prime_domain_eq : ∀ X : ℝ,
    Erdos448.DPMean.strictPrimeDomain X = strictPrimeRange X
  strict_mean_eq : ∀ h : ArithmeticWeight, ∀ X : ℝ,
    Erdos448.DPMean.strictMean h X = strictMean h X
  strict_euler_product_eq : ∀ h : ArithmeticWeight, ∀ X : ℝ,
    Erdos448.DPMean.strictEulerProduct h X = strictEulerProduct h X
  adapt : Erdos448.DPMean.T001Statement → EXT001Statement

/-- Exact S7/S8 adapter target.  A proof supplies both the representation
agreement and the target conversion; the DP-MEAN theorem alone is not silently
identified with the parent theorem. -/
@[expose] def DPMeanEXT001AdapterStatement : Prop :=
  DPMeanEXT001Adapter

/-! A direct representation adapter for the accepted dependency output. -/
theorem strictNatDomain_eq_positiveNatsBelow (X : ℝ) :
    Erdos448.DPMean.strictNatDomain X = positiveNatsBelow X := by
  ext n
  simp only [Erdos448.DPMean.strictNatDomain, positiveNatsBelow,
    Finset.mem_filter, Finset.mem_range]
  by_cases hn : 0 < n
  · simp only [hn, true_and]
    constructor
    · rintro ⟨h, _⟩; exact ⟨h, Nat.lt_ceil.mp h⟩
    · rintro ⟨h, _⟩; exact ⟨h, trivial⟩
  · simp [hn]

theorem strictPrimeDomain_eq_strictPrimeRange (X : ℝ) :
    Erdos448.DPMean.strictPrimeDomain X = strictPrimeRange X := by
  simp only [Erdos448.DPMean.strictPrimeDomain, strictPrimeRange]
  rw [strictNatDomain_eq_positiveNatsBelow]

theorem dp_nonnegative_multiplicative_to_parent
    (h : Erdos448.DPMean.ArithmeticFunction)
    (hh : Erdos448.DPMean.NonnegativeMultiplicative h) :
    NonnegativeMultiplicativeWeight h := by
  exact { nonnegative := hh.nonnegative
          multiplicative := hh.multiplicative }

theorem dp_parameter_to_parent {lambda1 lambda2 : ℝ}
    (hr : Erdos448.DPMean.ParameterRange lambda1 lambda2) :
    MeanParameterRange lambda1 lambda2 := by
  exact { lambda1_nonnegative := hr.lambda1_nonnegative
          lambda2_nonnegative := hr.lambda2_nonnegative
          lambda2_lt_two := hr.lambda2_lt_two }

theorem dp_geom_to_parent {h : Erdos448.DPMean.ArithmeticFunction}
    {lambda1 lambda2 : ℝ}
    (hg : Erdos448.DPMean.PrimePowerGeometricBound h lambda1 lambda2) :
    PrimePowerGeometricBound h lambda1 lambda2 := hg

theorem adaptDPMeanT001 (hT : Erdos448.DPMean.T001Statement) :
    EXT001Statement := by
  intro lambda1 lambda2 hr
  have hrc : Erdos448.DPMean.ParameterRange lambda1 lambda2 :=
    { lambda1_nonnegative := hr.lambda1_nonnegative
      lambda2_nonnegative := hr.lambda2_nonnegative
      lambda2_lt_two := hr.lambda2_lt_two }
  rcases hT lambda1 lambda2 hrc with ⟨provider⟩
  refine ⟨{ constant := provider.C
            constant_pos := provider.C_positive
            local_series_summable := ?_
            bound := ?_ }⟩
  · intro h hg p hp
    exact provider.local_series_summable h hg p hp
  · intro h hnm hg X hX
    have childnm : Erdos448.DPMean.NonnegativeMultiplicative h :=
      { nonnegative := hnm.nonnegative
        multiplicative := hnm.multiplicative }
    have childgeom : Erdos448.DPMean.PrimePowerGeometricBound h lambda1 lambda2 := hg
    have hb := provider.bound h childnm childgeom X hX
    have hmean : Erdos448.DPMean.strictMean h X = strictMean h X := by
      unfold Erdos448.DPMean.strictMean strictMean
      rw [strictNatDomain_eq_positiveNatsBelow]
    have hprod : Erdos448.DPMean.strictEulerProduct h X = strictEulerProduct h X := by
      unfold Erdos448.DPMean.strictEulerProduct strictEulerProduct
      rw [strictPrimeDomain_eq_strictPrimeRange]
      rfl
    unfold Erdos448.DPMean.MeanBoundAt at hb
    rw [hmean, hprod] at hb
    exact hb

/-! The Mertens dependency uses equivalent finite-set definitions in its own
namespace.  These lemmas make the parent representation boundary explicit. -/

theorem mertens_primesLT_eq_strictPrimeRange (x : ℝ) :
    Erdos448.DPMertens.primesLT x = strictPrimeRange x := by
  ext p
  simp only [Erdos448.DPMertens.primesLT, strictPrimeRange,
    positiveNatsBelow, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hpceil, hp⟩
    exact ⟨⟨hpceil, hp.pos, Nat.lt_ceil.mp hpceil⟩, hp⟩
  · rintro ⟨⟨hpceil, -, -⟩, hp⟩
    exact ⟨hpceil, hp⟩

theorem mertens_primesIco_eq_parent (A B : ℝ) :
    Erdos448.DPMertens.primesIco A B =
      (strictPrimeRange B).filter (fun p : ℕ => A ≤ (p : ℝ)) := by
  ext p
  simp only [Erdos448.DPMertens.primesIco, strictPrimeRange,
    positiveNatsBelow, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hpceil, hp, hA⟩
    exact ⟨⟨⟨hpceil, hp.pos, Nat.lt_ceil.mp hpceil⟩, hp⟩, hA⟩
  · rintro ⟨⟨⟨hpceil, -, -⟩, hp⟩, hA⟩
    exact ⟨hpceil, hp, hA⟩

theorem mertensFactor_eq_primeFactor (p : ℕ) :
    Erdos448.DPMertens.primeFactor p = mertensFactor p := by
  simp [Erdos448.DPMertens.primeFactor, mertensFactor, one_div]

theorem mertensStrictProduct_eq_qLT (x : ℝ) :
    Erdos448.DPMertens.qLT x = mertensStrictProduct x := by
  unfold Erdos448.DPMertens.qLT mertensStrictProduct
  rw [mertens_primesLT_eq_strictPrimeRange]
  apply Finset.prod_congr rfl
  intro p _
  exact mertensFactor_eq_primeFactor p

theorem mertensIntervalProduct_eq_parent (A B : ℝ) :
    Erdos448.DPMertens.intervalProduct A B =
      primeIntervalProduct mertensFactor A B := by
  unfold Erdos448.DPMertens.intervalProduct primeIntervalProduct
  rw [mertens_primesIco_eq_parent]
  simp only [Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro p _
  by_cases hA : A ≤ (p : ℝ)
  · simp [hA, mertensFactor_eq_primeFactor]
  · simp [hA]

theorem adaptDPMertensEXT002 (hT : Erdos448.DPMertens.EXT002Contract) :
    EXT002Statement := by
  rcases hT with ⟨hasymptotic, hinterval⟩
  rcases hinterval with ⟨X, cMinus, cPlus, hX, hcMinus, hcPlus, hbounds⟩
  refine ⟨{
    strict_asymptotic := ?_
    X_M := X
    c_M_minus := cMinus
    c_M_plus := cPlus
    X_M_ge_two := hX
    c_M_minus_pos := hcMinus
    c_M_plus_pos := hcPlus
    interval_comparison := ?_ }⟩
  · simpa [Erdos448.DPMertens.StrictMertensAsymptotic,
      Erdos448.DPMertens.AtTopEquivalent, StrictMertensAsymptotic] using
      (show Asymptotics.IsEquivalent Filter.atTop mertensStrictProduct
          mertensMainTerm from by
        have hq : Erdos448.DPMertens.qLT = mertensStrictProduct :=
          funext mertensStrictProduct_eq_qLT
        have hm : Erdos448.DPMertens.mertensMain = mertensMainTerm := rfl
        rw [← hq, ← hm]
        exact hasymptotic)
  · intro A B hA hAB
    simpa [mertensIntervalProduct_eq_parent] using hbounds A B hA hAB

end

end Erdos448.Stage4.DependencyAdapters
