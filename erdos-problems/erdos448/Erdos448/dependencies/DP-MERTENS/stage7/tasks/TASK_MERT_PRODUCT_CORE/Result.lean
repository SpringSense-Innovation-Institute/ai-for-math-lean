module

import all Mathlib.Basic.Real.Basic
public import Erdos448.dependencies.«DP-MERTENS».stage6.FrozenTaskContracts

public section

set_option backward.isDefEq.respectTransparency false

open Filter Finset
open scoped BigOperators Topology

namespace Erdos448.DPMertens.Tasks.MertProductCore

noncomputable section

open Erdos448.DPMertens
open Erdos448.DPMertens.Lowering
open Asymptotics

/-- P-MERT-03--05, constructed parametrically from the fixed child and
correction witnesses. -/
@[expose] def weakProduct (corr : CorrectionOutput) (child : SumAssemblyOutput corr.H) :
    WeakProductOutput corr child := by
  have factor_pos : ∀ (x : ℝ) (p : ℕ), p ∈ primesLE x → 0 < primeFactor p := by
    intro x p hp
    have hp_prime : p.Prime := (Finset.mem_filter.mp hp).2
    have hp_one : (1 : ℝ) < p := by
      exact_mod_cast hp_prime.one_lt
    exact sub_pos.mpr (inv_lt_one_of_one_lt₀ hp_one)

  have finite_log : FiniteProductLogContract := by
    intro x _hx
    rw [qLE, Real.log_prod (fun p hp ↦ (factor_pos x p hp).ne')]
    calc
      (∑ p ∈ primesLE x, Real.log (primeFactor p)) =
          ∑ p ∈ primesLE x, (-((p : ℝ)⁻¹) - correction p) := by
            apply Finset.sum_congr rfl
            intro p _hp
            simp only [correction, primeFactor]
            ring
      _ = -(∑ p ∈ primesLE x, (p : ℝ)⁻¹) -
          ∑ p ∈ primesLE x, correction p := by
            rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib]
      _ = -reciprocalPrimeSum x - correctionLE x := rfl

  let E : ℝ → ℝ := fun x ↦ (child.data.H - correctionLE x) - child.data.R x
  let CE : ℝ := child.data.CR + 2
  let XE : ℝ := max child.data.XR 2

  have log_cancellation : ∀ x : ℝ, 2 ≤ x →
      Real.log (qLE x) =
        -Real.log (Real.log x) - Real.eulerMascheroniConstant + E x := by
    intro x hx
    rw [finite_log x hx, child.data.real_formula x hx, child.data.B_identity]
    simp only [E]
    ring

  have E_rate : ReciprocalLogRate E CE XE := by
    refine ⟨?_, ?_, ?_⟩
    · dsimp [CE]
      linarith [child.data.remainder_rate.1]
    · dsimp [XE]
      exact le_max_right _ _
    · intro x hxXE
      have hxR : child.data.XR ≤ x := le_trans (le_max_left _ _) hxXE
      have hx2 : 2 ≤ x := le_trans (le_max_right _ _) hxXE
      have hxpos : 0 < x := by linarith
      have hlogpos : 0 < Real.log x := Real.log_pos (by linarith)
      have hxsubpos : 0 < x - 1 := by linarith
      have htail := corr.tail x hx2
      rw [← child.same_H] at htail
      have htail_log : child.data.H - correctionLE x ≤ 2 / Real.log x := by
        calc
          child.data.H - correctionLE x ≤ 2 / (x - 1) := htail.2
          _ ≤ 2 / Real.log x := by
            apply (div_le_div_iff₀ hxsubpos hlogpos).2
            nlinarith [Real.log_le_sub_one_of_pos hxpos]
      have htail_abs : |child.data.H - correctionLE x| ≤ 2 / Real.log x := by
        rw [abs_of_nonneg htail.1]
        exact htail_log
      have hR := child.data.remainder_rate.2.2 x hxR
      calc
        |E x| = |(child.data.H - correctionLE x) - child.data.R x| := rfl
        _ ≤ |child.data.H - correctionLE x| + |child.data.R x| := abs_sub _ _
        _ ≤ 2 / Real.log x + child.data.CR / Real.log x :=
          add_le_add htail_abs hR
        _ = CE / Real.log x := by
          dsimp [CE]
          ring

  have E_tendsto : Tendsto E atTop (nhds 0) := by
    have hcorr : Tendsto correctionLE atTop (nhds child.data.H) := by
      simpa [child.same_H] using corr.convergence.2.2
    have htail : Tendsto (fun x : ℝ ↦ child.data.H - correctionLE x) atTop (nhds 0) := by
      convert tendsto_const_nhds.sub hcorr using 1 <;> simp
    simpa only [E, sub_zero] using htail.sub child.data.remainder_tendsto

  have exact_exponential : ∀ x : ℝ, 2 ≤ x →
      qLE x = mertensMain x * Real.exp (E x) := by
    intro x hx
    have hxlog : 0 < Real.log x := Real.log_pos (by linarith)
    have hq : 0 < qLE x := by
      rw [qLE]
      exact Finset.prod_pos fun p hp ↦ factor_pos x p hp
    calc
      qLE x = Real.exp (Real.log (qLE x)) := (Real.exp_log hq).symm
      _ = Real.exp
          (-Real.log (Real.log x) - Real.eulerMascheroniConstant + E x) := by
            rw [log_cancellation x hx]
      _ = mertensMain x * Real.exp (E x) := by
            rw [show -Real.log (Real.log x) - Real.eulerMascheroniConstant + E x =
                -Real.log (Real.log x) + (-Real.eulerMascheroniConstant) + E x by ring,
              Real.exp_add, Real.exp_add, Real.exp_neg,
              Real.exp_log hxlog]
            simp only [mertensMain, div_eq_mul_inv]
            ring

  let relativeError : ℝ → ℝ := fun x ↦ Real.exp (E x) - 1
  let CRelative : ℝ := 2 * CE
  let XRelative : ℝ := max XE (Real.exp CE)

  have exact_relative : ∀ x : ℝ, 2 ≤ x →
      qLE x = mertensMain x * (1 + relativeError x) := by
    intro x hx
    rw [exact_exponential x hx]
    simp only [relativeError]
    ring

  have relative_rate : ReciprocalLogRate relativeError CRelative XRelative := by
    refine ⟨?_, ?_, ?_⟩
    · dsimp [CRelative]
      exact mul_pos (by norm_num) E_rate.1
    · exact le_trans E_rate.2.1 (le_max_left _ _)
    · intro x hxX
      have hxXE : XE ≤ x := le_trans (le_max_left _ _) hxX
      have hexpCE : Real.exp CE ≤ x := le_trans (le_max_right _ _) hxX
      have hx2 : 2 ≤ x := le_trans E_rate.2.1 hxXE
      have hxpos : 0 < x := by linarith
      have hlogpos : 0 < Real.log x := Real.log_pos (by linarith)
      have hCElog : CE ≤ Real.log x :=
        (Real.le_log_iff_exp_le hxpos).2 hexpCE
      have hEone : |E x| ≤ 1 := by
        calc
          |E x| ≤ CE / Real.log x := E_rate.2.2 x hxXE
          _ ≤ 1 := (div_le_one hlogpos).2 hCElog
      calc
        |relativeError x| = |Real.exp (E x) - 1| := rfl
        _ ≤ 2 * |E x| := Real.abs_exp_sub_one_le hEone
        _ ≤ 2 * (CE / Real.log x) :=
          mul_le_mul_of_nonneg_left (E_rate.2.2 x hxXE) (by norm_num)
        _ = CRelative / Real.log x := by
          dsimp [CRelative]
          ring

  have asymptotic : AtTopEquivalent qLE mertensMain := by
    have hexp_tendsto : Tendsto (fun x : ℝ ↦ Real.exp (E x)) atTop (nhds 1) := by
      simpa [Function.comp_def] using Filter.Tendsto.comp Real.continuous_exp.continuousAt E_tendsto
    rw [AtTopEquivalent, isEquivalent_iff_exists_eq_mul]
    refine ⟨fun x : ℝ ↦ Real.exp (E x), hexp_tendsto, ?_⟩
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
    simpa [mul_comm] using exact_exponential x hx

  exact
    { finite_log := finite_log
      E := E
      CE := CE
      XE := XE
      E_definition := by intro x _hx; rfl
      log_cancellation := log_cancellation
      E_rate := E_rate
      E_tendsto := E_tendsto
      relativeError := relativeError
      CRelative := CRelative
      XRelative := XRelative
      relativeError_definition := by intro x _hx; rfl
      exact_exponential := exact_exponential
      exact_relative := exact_relative
      relative_rate := relative_rate
      asymptotic := asymptotic }

/-- Exact frozen task target, retaining the supplied correction witness and
transporting the assembly data along uniqueness of its correction sum. -/
@[expose] def result : TASK_MERT_PRODUCT_CORE_Target := by
  intro hChild hCorrection
  have same_H : hChild.assembly.data.H = hCorrection.H :=
    hChild.assembly.data.correction_hasSum.unique hCorrection.convergence.2.1
  let child : SumAssemblyOutput hCorrection.H :=
    { data := hChild.assembly.data
      same_H := same_H }
  exact
    { corr := hCorrection
      child := child
      weak := weakProduct hCorrection child }

end

end Erdos448.DPMertens.Tasks.MertProductCore

#print axioms Erdos448.DPMertens.Tasks.MertProductCore.result
