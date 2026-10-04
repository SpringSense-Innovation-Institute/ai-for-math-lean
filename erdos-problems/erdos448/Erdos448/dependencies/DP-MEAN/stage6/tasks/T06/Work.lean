module

import all Mathlib.Basic.Real.Basic
public import Erdos448.dependencies.«DP-MEAN».stage6.shared.TaskInterfaces

public section

set_option backward.isDefEq.respectTransparency false

namespace Erdos448.DPMean.TaskT06

@[expose] abbrev PublicTarget : Prop := Erdos448.DPMean.S6.T06Target

open Erdos448.DPMean

noncomputable section

lemma higherPowerTerm_nonneg
    {lambda2 : ℝ} (hlambda2 : 0 ≤ lambda2) (p r : ℕ) :
    0 ≤ higherPowerTerm lambda2 p r := by
  unfold higherPowerTerm
  split_ifs with hpr
  · have hp_one : (1 : ℝ) ≤ p := by exact_mod_cast hpr.1.one_le
    exact mul_nonneg
      (mul_nonneg (Nat.cast_nonneg r) (Real.log_nonneg hp_one))
      (pow_nonneg (div_nonneg hlambda2 (Nat.cast_nonneg p)) r)
  · exact le_rfl

lemma higherPowerConstant_nonneg
    {lambda1 lambda2 : ℝ} (range : ParameterRange lambda1 lambda2) :
    0 ≤ higherPowerConstant lambda1 lambda2 := by
  unfold higherPowerConstant
  exact mul_nonneg range.lambda1_nonnegative
    (tsum_nonneg (fun p => tsum_nonneg
      (higherPowerTerm_nonneg range.lambda2_nonnegative p)))

lemma summand_le_majorant
    {h : ArithmeticFunction} {lambda1 lambda2 x : ℝ}
    (hgeom : PrimePowerGeometricBound h lambda1 lambda2)
    (range : ParameterRange lambda1 lambda2) (hx : 1 ≤ x)
    {m p r : ℕ} (hm : 0 < m) (hp : Nat.Prime p) :
    (if 2 ≤ r ∧ (((p ^ r : ℕ) : ℝ) ≤ x / (m : ℝ)) then
        h (p ^ r) * Real.log (((p ^ r : ℕ) : ℝ))
      else 0) ≤
      (x / (m : ℝ) * lambda1) * higherPowerTerm lambda2 p r := by
  split_ifs with hpr
  · rcases hpr with ⟨hr, hpower⟩
    have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have hm_pos : (0 : ℝ) < m := by exact_mod_cast hm
    have hpow_pos : 0 < (p : ℝ) ^ r := pow_pos hp_pos r
    have hlog_nonneg : 0 ≤ Real.log (p : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hp.one_le)
    have hweight_nonneg : 0 ≤ (r : ℝ) * Real.log (p : ℝ) :=
      mul_nonneg (Nat.cast_nonneg r) hlog_nonneg
    have hbase_nonneg :
        0 ≤ lambda1 * lambda2 ^ r * ((r : ℝ) * Real.log (p : ℝ)) :=
      mul_nonneg
        (mul_nonneg range.lambda1_nonnegative
          (pow_nonneg range.lambda2_nonnegative r)) hweight_nonneg
    have hratio : 1 ≤ (x / (m : ℝ)) / (p : ℝ) ^ r := by
      apply (le_div_iff₀ hpow_pos).2
      simpa only [one_mul, Nat.cast_pow] using hpower
    calc
      h (p ^ r) * Real.log (((p ^ r : ℕ) : ℝ))
          = h (p ^ r) * ((r : ℝ) * Real.log (p : ℝ)) := by
              rw [Nat.cast_pow, Real.log_pow]
      _ ≤ (lambda1 * lambda2 ^ r) *
          ((r : ℝ) * Real.log (p : ℝ)) :=
            mul_le_mul_of_nonneg_right (hgeom p hp r).2 hweight_nonneg
      _ ≤ ((x / (m : ℝ)) / (p : ℝ) ^ r) *
          (lambda1 * lambda2 ^ r * ((r : ℝ) * Real.log (p : ℝ))) := by
            nlinarith [mul_nonneg (sub_nonneg.mpr hratio) hbase_nonneg]
      _ = (x / (m : ℝ) * lambda1) * higherPowerTerm lambda2 p r := by
            rw [higherPowerTerm, if_pos ⟨hp, hr⟩, div_pow]
            ring
  · exact mul_nonneg
      (mul_nonneg (div_nonneg (by linarith) (Nat.cast_nonneg m))
        range.lambda1_nonnegative)
      (higherPowerTerm_nonneg range.lambda2_nonnegative p r)

lemma primePowerSum_le
    (hP002 : P002Statement)
    {h : ArithmeticFunction} {lambda1 lambda2 x : ℝ}
    (hgeom : PrimePowerGeometricBound h lambda1 lambda2)
    (range : ParameterRange lambda1 lambda2) (hx : 1 ≤ x)
    {m : ℕ} (hm : 0 < m) :
    (∑ p ∈ inclusivePrimeDomain x,
      ∑ r ∈ inclusiveNatDomain x,
        if 2 ≤ r ∧ (((p ^ r : ℕ) : ℝ) ≤ x / (m : ℝ)) then
          h (p ^ r) * Real.log (((p ^ r : ℕ) : ℝ))
        else 0) ≤
      (x / (m : ℝ)) * higherPowerConstant lambda1 lambda2 := by
  let payload := hP002 lambda1 lambda2 range
  have coeff_nonneg : 0 ≤ x / (m : ℝ) * lambda1 :=
    mul_nonneg (div_nonneg (by linarith) (Nat.cast_nonneg m))
      range.lambda1_nonnegative
  have each_prime : ∀ p ∈ inclusivePrimeDomain x,
      (∑ r ∈ inclusiveNatDomain x,
        if 2 ≤ r ∧ (((p ^ r : ℕ) : ℝ) ≤ x / (m : ℝ)) then
          h (p ^ r) * Real.log (((p ^ r : ℕ) : ℝ))
        else 0) ≤
      (x / (m : ℝ) * lambda1) *
        ∑' r : ℕ, higherPowerTerm lambda2 p r := by
    intro p hp_mem
    have hp : Nat.Prime p := (Finset.mem_filter.1 hp_mem).2
    calc
      (∑ r ∈ inclusiveNatDomain x,
        if 2 ≤ r ∧ (((p ^ r : ℕ) : ℝ) ≤ x / (m : ℝ)) then
          h (p ^ r) * Real.log (((p ^ r : ℕ) : ℝ))
        else 0) ≤
          ∑ r ∈ inclusiveNatDomain x,
            (x / (m : ℝ) * lambda1) * higherPowerTerm lambda2 p r := by
              gcongr with r hr
              exact summand_le_majorant hgeom range hx hm hp
      _ = (x / (m : ℝ) * lambda1) *
          ∑ r ∈ inclusiveNatDomain x, higherPowerTerm lambda2 p r := by
            rw [Finset.mul_sum]
      _ ≤ (x / (m : ℝ) * lambda1) *
          ∑' r : ℕ, higherPowerTerm lambda2 p r := by
            gcongr
            exact (payload.local_summable p hp).sum_le_tsum
              (inclusiveNatDomain x)
              (fun r _ => higherPowerTerm_nonneg range.lambda2_nonnegative p r)
  calc
    (∑ p ∈ inclusivePrimeDomain x,
      ∑ r ∈ inclusiveNatDomain x,
        if 2 ≤ r ∧ (((p ^ r : ℕ) : ℝ) ≤ x / (m : ℝ)) then
          h (p ^ r) * Real.log (((p ^ r : ℕ) : ℝ))
        else 0) ≤
        ∑ p ∈ inclusivePrimeDomain x,
          (x / (m : ℝ) * lambda1) *
            ∑' r : ℕ, higherPowerTerm lambda2 p r := by
              exact Finset.sum_le_sum fun p hp => each_prime p hp
    _ = (x / (m : ℝ) * lambda1) *
        ∑ p ∈ inclusivePrimeDomain x,
          ∑' r : ℕ, higherPowerTerm lambda2 p r := by
            rw [Finset.mul_sum]
    _ ≤ (x / (m : ℝ) * lambda1) *
        ∑' p : ℕ, ∑' r : ℕ, higherPowerTerm lambda2 p r := by
          gcongr
          exact payload.outer_summable.sum_le_tsum
            (inclusivePrimeDomain x)
            (fun p _ => tsum_nonneg
              (higherPowerTerm_nonneg range.lambda2_nonnegative p))
    _ = (x / (m : ℝ)) * higherPowerConstant lambda1 lambda2 := by
          unfold higherPowerConstant
          ring

lemma smallDomain_subset
    {x : ℝ} (hx : 1 ≤ x) :
    inclusiveNatDomain (x / 4) ⊆ inclusiveNatDomain x := by
  intro m hm
  rcases Finset.mem_filter.1 hm with ⟨hm_range, hm_pos⟩
  apply Finset.mem_filter.2
  refine ⟨?_, hm_pos⟩
  rw [Finset.mem_range, Nat.lt_succ_iff] at hm_range ⊢
  have hx4_nonneg : 0 ≤ x / 4 := by positivity
  have hm_le : (m : ℝ) ≤ x / 4 :=
    (Nat.le_floor_iff hx4_nonneg).mp hm_range
  apply Nat.le_floor
  linarith

theorem publicTarget : PublicTarget := by
  intro hP002 h lambda1 lambda2 x hnonneg hgeom range hx
  have x_nonneg : 0 ≤ x := by linarith
  have B_nonneg : 0 ≤ higherPowerConstant lambda1 lambda2 :=
    higherPowerConstant_nonneg range
  have partial_reciprocal :
      (∑ m ∈ inclusiveNatDomain (x / 4), h m / (m : ℝ)) ≤
        reciprocalMean h x := by
    unfold reciprocalMean
    apply Finset.sum_le_sum_of_subset_of_nonneg (smallDomain_subset hx)
    intro m hm _
    exact div_nonneg (hnonneg m (Finset.mem_filter.1 hm).2)
      (Nat.cast_nonneg m)
  unfold higherPowerContribution
  calc
    (∑ m ∈ inclusiveNatDomain (x / 4),
      h m * ∑ p ∈ inclusivePrimeDomain x,
        ∑ r ∈ inclusiveNatDomain x,
          if 2 ≤ r ∧ (((p ^ r : ℕ) : ℝ) ≤ x / (m : ℝ)) then
            h (p ^ r) * Real.log (((p ^ r : ℕ) : ℝ))
          else 0) ≤
        ∑ m ∈ inclusiveNatDomain (x / 4),
          h m * ((x / (m : ℝ)) * higherPowerConstant lambda1 lambda2) := by
            gcongr with m hm
            · exact hnonneg m (Finset.mem_filter.1 hm).2
            · exact primePowerSum_le hP002 hgeom range hx
                (Finset.mem_filter.1 hm).2
    _ = higherPowerConstant lambda1 lambda2 * x *
        ∑ m ∈ inclusiveNatDomain (x / 4), h m / (m : ℝ) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro m hm
          ring
    _ ≤ higherPowerConstant lambda1 lambda2 * x * reciprocalMean h x := by
          exact mul_le_mul_of_nonneg_left partial_reciprocal
            (mul_nonneg B_nonneg x_nonneg)

end

end Erdos448.DPMean.TaskT06
