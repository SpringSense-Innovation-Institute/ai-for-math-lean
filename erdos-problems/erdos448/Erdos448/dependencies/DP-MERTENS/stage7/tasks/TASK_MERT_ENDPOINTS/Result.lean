module

import all Mathlib.Basic.Real.Basic
public import Erdos448.dependencies.«DP-MERTENS».stage6.FrozenTaskContracts

public section

set_option backward.isDefEq.respectTransparency false

open Filter Finset
open scoped BigOperators Topology

namespace Erdos448.DPMertens.Tasks.MertEndpoints

noncomputable section

open Erdos448.DPMertens
open Erdos448.DPMertens.Lowering

lemma mem_primesLE_iff (x : ℝ) (p : ℕ) :
    p ∈ primesLE x ↔ p.Prime ∧ (p : ℝ) ≤ x := by
  simp only [primesLE, Finset.mem_filter, Finset.mem_range, Nat.lt_add_one_iff]
  constructor
  · rintro ⟨hpFloor, hp⟩
    exact ⟨hp, (Nat.le_floor_iff' hp.ne_zero).mp hpFloor⟩
  · rintro ⟨hp, hpx⟩
    exact ⟨(Nat.le_floor_iff' hp.ne_zero).mpr hpx, hp⟩

lemma mem_primesLT_iff (x : ℝ) (p : ℕ) :
    p ∈ primesLT x ↔ p.Prime ∧ (p : ℝ) < x := by
  simp only [primesLT, Finset.mem_filter, Finset.mem_range, Nat.lt_ceil]
  tauto

lemma mem_primesIco_iff (A B : ℝ) (p : ℕ) :
    p ∈ primesIco A B ↔ p.Prime ∧ A ≤ (p : ℝ) ∧ (p : ℝ) < B := by
  simp only [primesIco, Finset.mem_filter, Finset.mem_range, Nat.lt_ceil]
  tauto

lemma primeFactor_pos {p : ℕ} (hp : p.Prime) : 0 < primeFactor p := by
  rw [primeFactor]
  exact sub_pos.mpr <| (inv_lt_one₀ (by exact_mod_cast hp.pos)).2
    (by exact_mod_cast hp.one_lt)

lemma qLT_pos (x : ℝ) : 0 < qLT x := by
  apply Finset.prod_pos
  intro p hp
  exact primeFactor_pos (mem_primesLT_iff x p |>.mp hp).1

lemma endpoint_eq_one_or_denominator (x : ℝ) :
    endpointFactor x = 1 ∨ endpointFactor x = 1 - x⁻¹ := by
  classical
  by_cases h : ∃ p : ℕ, p ∈ primesLE x ∧ (p : ℝ) = x
  · obtain ⟨p, hpMem, hpx⟩ := h
    right
    have hfilter :
        (primesLE x).filter (fun q : ℕ ↦ (q : ℝ) = x) = {p} := by
      ext q
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨hqMem, hqx⟩
        have hcast : (q : ℝ) = (p : ℝ) := hqx.trans hpx.symm
        exact_mod_cast hcast
      · rintro rfl
        exact ⟨hpMem, hpx⟩
    simp [endpointFactor, hfilter, primeFactor, hpx]
  · left
    have hfilter :
        (primesLE x).filter (fun p : ℕ ↦ (p : ℝ) = x) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro p hp
      exact h ⟨p, Finset.mem_filter.mp hp⟩
    simp [endpointFactor, hfilter]

lemma weak_strict_product (x : ℝ) :
    qLE x = qLT x * endpointFactor x := by
  classical
  have hstrict :
      primesLT x = (primesLE x).filter (fun p : ℕ ↦ (p : ℝ) < x) := by
    ext p
    simp only [mem_primesLT_iff, Finset.mem_filter, mem_primesLE_iff]
    constructor
    · rintro ⟨hp, hpx⟩
      exact ⟨⟨hp, hpx.le⟩, hpx⟩
    · rintro ⟨⟨hp, _⟩, hpx⟩
      exact ⟨hp, hpx⟩
  have hend :
      (primesLE x).filter (fun p : ℕ ↦ (p : ℝ) = x) =
        (primesLE x).filter (fun p : ℕ ↦ ¬ (p : ℝ) < x) := by
    ext p
    simp only [Finset.mem_filter, mem_primesLE_iff]
    constructor
    · rintro ⟨hp, hpx⟩
      exact ⟨hp, by linarith⟩
    · rintro ⟨hp, hnlt⟩
      exact ⟨hp, le_antisymm hp.2 (le_of_not_gt hnlt)⟩
  rw [qLE, qLT, endpointFactor, hstrict, hend]
  exact (Finset.prod_filter_mul_prod_filter_not
    (primesLE x) (fun p : ℕ ↦ (p : ℝ) < x) primeFactor).symm

lemma endpoint_properties (x : ℝ) (hx : 2 ≤ x) :
    0 < endpointFactor x ∧
      1 ≤ (endpointFactor x)⁻¹ ∧
      (endpointFactor x)⁻¹ ≤ (1 - x⁻¹)⁻¹ := by
  have hxpos : 0 < x := by linarith
  have hinv_nonneg : 0 ≤ x⁻¹ := inv_nonneg.mpr hxpos.le
  have hden_pos : 0 < 1 - x⁻¹ := by
    exact sub_pos.mpr <| (inv_lt_one₀ hxpos).2 (by linarith)
  have hden_le : 1 - x⁻¹ ≤ 1 := sub_le_self 1 hinv_nonneg
  rcases endpoint_eq_one_or_denominator x with hOne | hDen
  · simp only [hOne, inv_one]
    exact ⟨zero_lt_one, le_rfl, (one_le_inv₀ hden_pos).2 hden_le⟩
  · simp only [hDen]
    exact ⟨hden_pos, (one_le_inv₀ hden_pos).2 hden_le, le_rfl⟩

lemma endpoint_inverse_tendsto :
    Tendsto (fun x : ℝ ↦ (endpointFactor x)⁻¹) atTop (𝓝 1) := by
  letI : ContinuousInv₀ ℝ := NormedDivisionRing.to_continuousInv₀
  have hUpper : Tendsto (fun x : ℝ ↦ (1 - x⁻¹)⁻¹) atTop (𝓝 1) := by
    have hInv : Tendsto (fun x : ℝ ↦ x⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero
    have hDen : Tendsto (fun x : ℝ ↦ 1 - x⁻¹) atTop (𝓝 1) := by
      simpa using (tendsto_const_nhds.sub hInv :
        Tendsto (fun x : ℝ ↦ 1 - x⁻¹) atTop (𝓝 (1 - 0)))
    simpa using hDen.inv₀ one_ne_zero
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hUpper
  · filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
    exact (endpoint_properties x hx).2.1
  · filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
    exact (endpoint_properties x hx).2.2

lemma interval_first_quotient (A B : ℝ) (hAB : A < B) :
    intervalProduct A B = qLT B / qLT A := by
  classical
  have hlow :
      primesLT A = (primesLT B).filter (fun p : ℕ ↦ (p : ℝ) < A) := by
    ext p
    simp only [mem_primesLT_iff, Finset.mem_filter]
    constructor
    · rintro ⟨hp, hpA⟩
      exact ⟨⟨hp, hpA.trans hAB⟩, hpA⟩
    · rintro ⟨⟨hp, _⟩, hpA⟩
      exact ⟨hp, hpA⟩
  have hinterval :
      primesIco A B =
        (primesLT B).filter (fun p : ℕ ↦ ¬ (p : ℝ) < A) := by
    ext p
    simp only [mem_primesIco_iff, Finset.mem_filter, mem_primesLT_iff]
    constructor
    · rintro ⟨hp, hAp, hpB⟩
      exact ⟨⟨hp, hpB⟩, not_lt.mpr hAp⟩
    · rintro ⟨⟨hp, hpB⟩, hnlt⟩
      exact ⟨hp, le_of_not_gt hnlt, hpB⟩
  have hprod : qLT A * intervalProduct A B = qLT B := by
    rw [qLT, intervalProduct, hlow, hinterval]
    exact Finset.prod_filter_mul_prod_filter_not
      (primesLT B) (fun p : ℕ ↦ (p : ℝ) < A) primeFactor
  apply (eq_div_iff (qLT_pos A).ne').2
  simpa [mul_comm] using hprod

lemma interval_second_quotient (A B : ℝ) (hA2 : 2 ≤ A) (hAB : A < B) :
    intervalProduct A B =
      qLE B * endpointFactor A / (qLE A * endpointFactor B) := by
  have hFirst := interval_first_quotient A B hAB
  have hA := weak_strict_product A
  have hB := weak_strict_product B
  have hqA : qLT A ≠ 0 := (qLT_pos A).ne'
  have hqB : qLT B ≠ 0 := (qLT_pos B).ne'
  have hB2 : 2 ≤ B := hA2.trans hAB.le
  have heA : endpointFactor A ≠ 0 := (endpoint_properties A hA2).1.ne'
  have heB : endpointFactor B ≠ 0 := (endpoint_properties B hB2).1.ne'
  rw [hFirst, hA, hB]
  field_simp [hqA, hqB, heA, heB]

theorem result : TASK_MERT_ENDPOINTS_Target := by
  refine ⟨?_, ?_⟩
  · refine ⟨?_, endpoint_inverse_tendsto⟩
    intro x hx
    have hp := endpoint_properties x hx
    exact ⟨hp.1, weak_strict_product x, hp.2.1, hp.2.2⟩
  · intro A B hA2 hAB
    refine ⟨interval_first_quotient A B hAB, ?_⟩
    exact interval_second_quotient A B hA2 hAB

end

end Erdos448.DPMertens.Tasks.MertEndpoints

#print axioms Erdos448.DPMertens.Tasks.MertEndpoints.result
