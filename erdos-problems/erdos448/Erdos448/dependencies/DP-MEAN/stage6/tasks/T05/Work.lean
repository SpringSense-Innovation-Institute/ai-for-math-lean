module

import all Mathlib.Basic.Real.Basic
public import Erdos448.dependencies.«DP-MEAN».stage6.shared.TaskInterfaces

public section

set_option backward.isDefEq.respectTransparency false

namespace Erdos448.DPMean.TaskT05

@[expose] abbrev PublicTarget : Prop := Erdos448.DPMean.S6.T05Target

theorem mem_inclusiveNatDomain_iff
    {x : ℝ} (hx : 0 ≤ x) {n : ℕ} :
    n ∈ inclusiveNatDomain x ↔ 0 < n ∧ (n : ℝ) ≤ x := by
  constructor
  · intro hn
    rw [inclusiveNatDomain, Finset.mem_filter] at hn
    refine ⟨hn.2, ?_⟩
    rw [Finset.mem_range] at hn
    apply (Nat.le_floor_iff hx).1
    omega
  · rintro ⟨hnpos, hnx⟩
    rw [inclusiveNatDomain, Finset.mem_filter, Finset.mem_range]
    refine ⟨?_, hnpos⟩
    have hfloor : n ≤ Nat.floor x := Nat.le_floor hnx
    omega

theorem constructed : PublicTarget := by
  intro hP003 h lambda1 lambda2 x hh hgeom hrange hx
  have hx0 : 0 ≤ x := by linarith
  have hxhalf0 : 0 ≤ x / 2 := by positivity
  have hA0 : 0 ≤ firstPowerConstant lambda1 lambda2 := by
    have hcheb : 0 ≤ chebyshevConstant := by
      dsimp [chebyshevConstant]
      positivity
    exact mul_nonneg
      (mul_nonneg hcheb hrange.lambda1_nonnegative)
      hrange.lambda2_nonnegative
  have hAx0 : 0 ≤ firstPowerConstant lambda1 lambda2 * x :=
    mul_nonneg hA0 hx0
  have hpointwise : ∀ m ∈ inclusiveNatDomain (x / 2),
      h m * ∑ p ∈ inclusivePrimeDomain (x / (m : ℝ)),
          h p * Real.log (p : ℝ) ≤
        (firstPowerConstant lambda1 lambda2 * x) * (h m / (m : ℝ)) := by
    intro m hm
    have hm_data := (mem_inclusiveNatDomain_iff hxhalf0).1 hm
    have hmpos_nat : 0 < m := hm_data.1
    have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hmpos_nat
    have hm_le : (m : ℝ) ≤ x / 2 := hm_data.2
    have hy : 2 ≤ x / (m : ℝ) := by
      rw [le_div_iff₀ hmpos]
      linarith
    have hprime := hP003 h lambda1 lambda2 (x / (m : ℝ))
      hh hgeom hrange hy
    calc
      h m * ∑ p ∈ inclusivePrimeDomain (x / (m : ℝ)),
          h p * Real.log (p : ℝ) ≤
          h m * (firstPowerConstant lambda1 lambda2 * (x / (m : ℝ))) :=
        mul_le_mul_of_nonneg_left hprime (hh m hmpos_nat)
      _ = (firstPowerConstant lambda1 lambda2 * x) * (h m / (m : ℝ)) := by
        field_simp
        <;> ring
  have hdomain : inclusiveNatDomain (x / 2) ⊆ inclusiveNatDomain x := by
    intro m hm
    rw [mem_inclusiveNatDomain_iff hx0]
    have hm_data := (mem_inclusiveNatDomain_iff hxhalf0).1 hm
    exact ⟨hm_data.1, hm_data.2.trans (by linarith)⟩
  have hreciprocal :
      (∑ m ∈ inclusiveNatDomain (x / 2), h m / (m : ℝ)) ≤
        reciprocalMean h x := by
    unfold reciprocalMean
    apply Finset.sum_le_sum_of_subset_of_nonneg hdomain
    intro m hm _hm_small
    have hmpos := (mem_inclusiveNatDomain_iff hx0).1 hm |>.1
    exact div_nonneg (hh m hmpos) (Nat.cast_nonneg m)
  unfold firstPowerContribution
  calc
    (∑ m ∈ inclusiveNatDomain (x / 2),
        h m * ∑ p ∈ inclusivePrimeDomain (x / (m : ℝ)),
          h p * Real.log (p : ℝ)) ≤
        ∑ m ∈ inclusiveNatDomain (x / 2),
          (firstPowerConstant lambda1 lambda2 * x) * (h m / (m : ℝ)) :=
      Finset.sum_le_sum hpointwise
    _ = (firstPowerConstant lambda1 lambda2 * x) *
        ∑ m ∈ inclusiveNatDomain (x / 2), h m / (m : ℝ) := by
      rw [Finset.mul_sum]
    _ ≤ (firstPowerConstant lambda1 lambda2 * x) * reciprocalMean h x :=
      mul_le_mul_of_nonneg_left hreciprocal hAx0
    _ = firstPowerConstant lambda1 lambda2 * x * reciprocalMean h x := rfl

end Erdos448.DPMean.TaskT05
