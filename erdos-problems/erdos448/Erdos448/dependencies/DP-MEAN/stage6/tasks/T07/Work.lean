module

import all Mathlib.Basic.Real.Basic
public import Erdos448.dependencies.«DP-MEAN».stage6.shared.TaskInterfaces

public section

set_option backward.isDefEq.respectTransparency false

namespace Erdos448.DPMean.TaskT07

@[expose] abbrev PublicTarget : Prop := Erdos448.DPMean.S6.T07Target

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

theorem mem_inclusivePrimeDomain_iff
    {x : ℝ} (hx : 0 ≤ x) {p : ℕ} :
    p ∈ inclusivePrimeDomain x ↔ Nat.Prime p ∧ (p : ℝ) ≤ x := by
  rw [inclusivePrimeDomain, Finset.mem_filter,
    mem_inclusiveNatDomain_iff hx]
  constructor
  · rintro ⟨⟨_, hp⟩, hprime⟩
    exact ⟨hprime, hp⟩
  · rintro ⟨hprime, hp⟩
    exact ⟨⟨hprime.pos, hp⟩, hprime⟩

@[expose] noncomputable def rawTerm (h : ArithmeticFunction) (p r m : ℕ) : ℝ :=
  h (p ^ r) * h m * Real.log ((p ^ r : ℕ) : ℝ)

theorem rawTerm_nonneg
    {h : ArithmeticFunction} (hh : Nonnegative h)
    {p r m : ℕ} (hp : Nat.Prime p) (hr : 0 < r) (hm : 0 < m) :
    0 ≤ rawTerm h p r m := by
  have hpow : 0 < p ^ r := pow_pos hp.pos r
  have hone : (1 : ℝ) ≤ ((p ^ r : ℕ) : ℝ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hpow))
  exact mul_nonneg (mul_nonneg (hh _ hpow) (hh _ hm))
    (Real.log_nonneg hone)

theorem first_raw_eq
    {h : ArithmeticFunction} {x : ℝ} (hx : 2 ≤ x) :
    (∑ p ∈ inclusivePrimeDomain x,
      ∑ r ∈ inclusiveNatDomain x,
        ∑ m ∈ inclusiveNatDomain x,
          if r = 1 ∧ ((((p ^ r) * m : ℕ) : ℝ) ≤ x) then
            rawTerm h p r m else 0) = firstPowerContribution h x := by
  classical
  have hx0 : 0 ≤ x := by linarith
  have hxhalf0 : 0 ≤ x / 2 := by positivity
  have hone : 1 ∈ inclusiveNatDomain x :=
    (mem_inclusiveNatDomain_iff hx0).2 ⟨by omega, by norm_num; linarith⟩
  have hMsub : inclusiveNatDomain (x / 2) ⊆ inclusiveNatDomain x := by
    intro m hm
    have hm' := (mem_inclusiveNatDomain_iff hxhalf0).1 hm
    exact (mem_inclusiveNatDomain_iff hx0).2
      ⟨hm'.1, hm'.2.trans (by linarith)⟩
  calc
    (∑ p ∈ inclusivePrimeDomain x,
      ∑ r ∈ inclusiveNatDomain x,
        ∑ m ∈ inclusiveNatDomain x,
          if r = 1 ∧ ((((p ^ r) * m : ℕ) : ℝ) ≤ x) then
            rawTerm h p r m else 0) =
        ∑ p ∈ inclusivePrimeDomain x,
          ∑ m ∈ inclusiveNatDomain x,
            if (((p * m : ℕ) : ℝ) ≤ x) then
              h p * h m * Real.log (p : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.sum_eq_single 1]
      · simp [rawTerm]
      · intro r hr hrne
        simp [hrne]
      · exact fun hnot ↦ (hnot hone).elim
    _ = ∑ m ∈ inclusiveNatDomain x,
          ∑ p ∈ inclusivePrimeDomain x,
            if (((p * m : ℕ) : ℝ) ≤ x) then
              h p * h m * Real.log (p : ℝ) else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ m ∈ inclusiveNatDomain (x / 2),
          ∑ p ∈ inclusivePrimeDomain x,
            if (((p * m : ℕ) : ℝ) ≤ x) then
              h p * h m * Real.log (p : ℝ) else 0 := by
      symm
      apply Finset.sum_subset hMsub
      intro m hmx hmnot
      apply Finset.sum_eq_zero
      intro p hp
      have hpprime := (mem_inclusivePrimeDomain_iff hx0).1 hp |>.1
      simp only [ite_eq_right_iff]
      intro hpm
      exfalso
      apply hmnot
      apply (mem_inclusiveNatDomain_iff hxhalf0).2
      have hmpos := (mem_inclusiveNatDomain_iff hx0).1 hmx |>.1
      refine ⟨hmpos, ?_⟩
      have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpprime.two_le
      norm_num at hpm ⊢
      nlinarith
    _ = ∑ m ∈ inclusiveNatDomain (x / 2),
          h m * ∑ p ∈ inclusivePrimeDomain (x / (m : ℝ)),
            h p * Real.log (p : ℝ) := by
      apply Finset.sum_congr rfl
      intro m hm
      have hmdata := (mem_inclusiveNatDomain_iff hxhalf0).1 hm
      have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hmdata.1
      have hquot0 : 0 ≤ x / (m : ℝ) := div_nonneg hx0 hmpos.le
      have hPsub : inclusivePrimeDomain (x / (m : ℝ)) ⊆
          inclusivePrimeDomain x := by
        intro p hp
        have hpdata := (mem_inclusivePrimeDomain_iff hquot0).1 hp
        apply (mem_inclusivePrimeDomain_iff hx0).2
        refine ⟨hpdata.1, hpdata.2.trans ?_⟩
        exact div_le_self hx0 (by exact_mod_cast hmdata.1)
      calc
        (∑ p ∈ inclusivePrimeDomain x,
            if (((p * m : ℕ) : ℝ) ≤ x) then
              h p * h m * Real.log (p : ℝ) else 0) =
            ∑ p ∈ inclusivePrimeDomain (x / (m : ℝ)),
              if (((p * m : ℕ) : ℝ) ≤ x) then
                h p * h m * Real.log (p : ℝ) else 0 := by
          symm
          apply Finset.sum_subset hPsub
          intro p hpx hpnot
          simp only [ite_eq_right_iff]
          intro hpm
          exfalso
          apply hpnot
          apply (mem_inclusivePrimeDomain_iff hquot0).2
          refine ⟨(mem_inclusivePrimeDomain_iff hx0).1 hpx |>.1, ?_⟩
          apply (le_div_iff₀ hmpos).2
          norm_num at hpm ⊢
          simpa [Nat.cast_mul] using hpm
        _ = h m * ∑ p ∈ inclusivePrimeDomain (x / (m : ℝ)),
              h p * Real.log (p : ℝ) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro p hp
          have hpdata := (mem_inclusivePrimeDomain_iff hquot0).1 hp
          have hpm : (((p * m : ℕ) : ℝ) ≤ x) := by
            norm_num
            exact (le_div_iff₀ hmpos).1 hpdata.2
          rw [if_pos (by simpa [Nat.cast_mul] using hpm)]
          ring
    _ = firstPowerContribution h x := rfl

theorem higher_raw_eq
    {h : ArithmeticFunction} {x : ℝ} (hx : 2 ≤ x) :
    (∑ p ∈ inclusivePrimeDomain x,
      ∑ r ∈ inclusiveNatDomain x,
        ∑ m ∈ inclusiveNatDomain x,
          if 2 ≤ r ∧ ((((p ^ r) * m : ℕ) : ℝ) ≤ x) then
            rawTerm h p r m else 0) = higherPowerContribution h x := by
  classical
  have hx0 : 0 ≤ x := by linarith
  have hxfourth0 : 0 ≤ x / 4 := by positivity
  have hMsub : inclusiveNatDomain (x / 4) ⊆ inclusiveNatDomain x := by
    intro m hm
    have hm' := (mem_inclusiveNatDomain_iff hxfourth0).1 hm
    exact (mem_inclusiveNatDomain_iff hx0).2
      ⟨hm'.1, hm'.2.trans (by linarith)⟩
  calc
    (∑ p ∈ inclusivePrimeDomain x,
      ∑ r ∈ inclusiveNatDomain x,
        ∑ m ∈ inclusiveNatDomain x,
          if 2 ≤ r ∧ ((((p ^ r) * m : ℕ) : ℝ) ≤ x) then
            rawTerm h p r m else 0) =
        ∑ p ∈ inclusivePrimeDomain x,
          ∑ m ∈ inclusiveNatDomain x,
            ∑ r ∈ inclusiveNatDomain x,
              if 2 ≤ r ∧ ((((p ^ r) * m : ℕ) : ℝ) ≤ x) then
                rawTerm h p r m else 0 := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.sum_comm]
    _ = ∑ m ∈ inclusiveNatDomain x,
          ∑ p ∈ inclusivePrimeDomain x,
            ∑ r ∈ inclusiveNatDomain x,
              if 2 ≤ r ∧ ((((p ^ r) * m : ℕ) : ℝ) ≤ x) then
                rawTerm h p r m else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ m ∈ inclusiveNatDomain (x / 4),
          ∑ p ∈ inclusivePrimeDomain x,
            ∑ r ∈ inclusiveNatDomain x,
              if 2 ≤ r ∧ ((((p ^ r) * m : ℕ) : ℝ) ≤ x) then
                rawTerm h p r m else 0 := by
      symm
      apply Finset.sum_subset hMsub
      intro m hmx hmnot
      apply Finset.sum_eq_zero
      intro p hp
      apply Finset.sum_eq_zero
      intro r hr
      simp only [Nat.cast_mul, Nat.cast_pow]
      by_cases hcond : 2 ≤ r ∧ (p : ℝ) ^ r * (m : ℝ) ≤ x
      · exfalso
        apply hmnot
        apply (mem_inclusiveNatDomain_iff hxfourth0).2
        have hmpos := (mem_inclusiveNatDomain_iff hx0).1 hmx |>.1
        refine ⟨hmpos, ?_⟩
        have hpprime := (mem_inclusivePrimeDomain_iff hx0).1 hp |>.1
        have hpow4 : 4 ≤ p ^ r := by
          calc
            4 = 2 ^ 2 := by norm_num
            _ ≤ p ^ 2 := Nat.pow_le_pow_left hpprime.two_le 2
            _ ≤ p ^ r := Nat.pow_le_pow_right hpprime.pos hcond.1
        have hpow4real : (4 : ℝ) ≤ ((p ^ r : ℕ) : ℝ) := by
          exact_mod_cast hpow4
        have h4m : (4 : ℝ) * (m : ℝ) ≤
            ((p ^ r : ℕ) : ℝ) * (m : ℝ) :=
          mul_le_mul_of_nonneg_right hpow4real (by positivity)
        have hmx4 : (m : ℝ) * 4 ≤ x := by
          calc
            (m : ℝ) * 4 = 4 * (m : ℝ) := by ring
            _ ≤ ((p ^ r : ℕ) : ℝ) * (m : ℝ) := h4m
            _ = (p : ℝ) ^ r * (m : ℝ) := by norm_num
            _ ≤ x := hcond.2
        exact (le_div_iff₀ (by norm_num : (0 : ℝ) < 4)).2 hmx4
      · exact if_neg hcond
    _ = ∑ m ∈ inclusiveNatDomain (x / 4),
          h m * ∑ p ∈ inclusivePrimeDomain x,
            ∑ r ∈ inclusiveNatDomain x,
              if 2 ≤ r ∧ (((p ^ r : ℕ) : ℝ) ≤ x / (m : ℝ)) then
                h (p ^ r) * Real.log ((p ^ r : ℕ) : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro m hm
      have hmdata := (mem_inclusiveNatDomain_iff hxfourth0).1 hm
      have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hmdata.1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      have hiff : (p : ℝ) ^ r * (m : ℝ) ≤ x ↔
          (p : ℝ) ^ r ≤ x / (m : ℝ) := by
        rw [le_div_iff₀ hmpos]
      simp only [Nat.cast_mul, Nat.cast_pow]
      by_cases h2 : 2 ≤ r
      · by_cases hright : ((p : ℝ) ^ r ≤ x / (m : ℝ))
        · rw [if_pos ⟨h2, hiff.mpr hright⟩, if_pos ⟨h2, hright⟩]
          simp [rawTerm, Nat.cast_pow]
          ring
        · rw [if_neg (fun hc ↦ hright (hiff.mp hc.2)),
              if_neg (fun hc ↦ hright hc.2)]
          simp
      · rw [if_neg (fun hc ↦ h2 hc.1), if_neg (fun hc ↦ h2 hc.1)]
        simp
    _ = higherPowerContribution h x := rfl

theorem p009_checkpoint
    (hP006 : P006Statement) (hP007 : P007Statement)
    (hP008 : P008Statement) : P009Statement := by
  intro h lambda1 lambda2 x hass hx
  let hh : Nonnegative h := hass.h_nonnegative_multiplicative.nonnegative
  have hx1 : 1 ≤ x := by linarith
  have hx0 : 0 ≤ x := by linarith
  have hreindex := (hP006 h hass.h_nonnegative_multiplicative x hx1).exact_identity
  have hfirst := hP007 h lambda1 lambda2 x hh
    hass.prime_power_geometric_bound hass.parameter_range hx
  have hhigher := hP008 h lambda1 lambda2 x hh
    hass.prime_power_geometric_bound hass.parameter_range hx1
  have hraw : primePowerCoprimeSum h x ≤
      firstPowerContribution h x + higherPowerContribution h x := by
    unfold primePowerCoprimeSum
    calc
      (∑ p ∈ inclusivePrimeDomain x,
        ∑ r ∈ inclusiveNatDomain x,
          ∑ m ∈ inclusiveNatDomain x,
            if Nat.Coprime p m ∧ ((((p ^ r) * m : ℕ) : ℝ) ≤ x) then
              rawTerm h p r m else 0) ≤
          ∑ p ∈ inclusivePrimeDomain x,
            ∑ r ∈ inclusiveNatDomain x,
              ∑ m ∈ inclusiveNatDomain x,
                ((if r = 1 ∧ ((((p ^ r) * m : ℕ) : ℝ) ≤ x) then
                    rawTerm h p r m else 0) +
                 (if 2 ≤ r ∧ ((((p ^ r) * m : ℕ) : ℝ) ≤ x) then
                    rawTerm h p r m else 0)) := by
        apply Finset.sum_le_sum
        intro p hp
        apply Finset.sum_le_sum
        intro r hr
        apply Finset.sum_le_sum
        intro m hm
        have hpprime := (mem_inclusivePrimeDomain_iff hx0).1 hp |>.1
        have hrpos := (mem_inclusiveNatDomain_iff hx0).1 hr |>.1
        have hmpos := (mem_inclusiveNatDomain_iff hx0).1 hm |>.1
        have hterm0 := rawTerm_nonneg hh hpprime hrpos hmpos
        simp only [Nat.cast_mul, Nat.cast_pow]
        by_cases hc : Nat.Coprime p m ∧
            (p : ℝ) ^ r * (m : ℝ) ≤ x
        · rcases eq_or_lt_of_le (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hrpos)) with hr1 | hr2
          · have hre : r = 1 := hr1.symm
            have hn2 : ¬ 2 ≤ r := by omega
            rw [if_pos hc, if_pos ⟨hre, hc.2⟩,
              if_neg (fun h2 ↦ hn2 h2.1)]
            simp
          · have h2r : 2 ≤ r := by omega
            have hrne : r ≠ 1 := by omega
            rw [if_pos hc, if_neg (fun h1 ↦ hrne h1.1),
              if_pos ⟨h2r, hc.2⟩]
            linarith
        · simp only [if_neg hc]
          positivity
      _ = (∑ p ∈ inclusivePrimeDomain x,
              ∑ r ∈ inclusiveNatDomain x,
                ∑ m ∈ inclusiveNatDomain x,
                  if r = 1 ∧ ((((p ^ r) * m : ℕ) : ℝ) ≤ x) then
                    rawTerm h p r m else 0) +
            (∑ p ∈ inclusivePrimeDomain x,
              ∑ r ∈ inclusiveNatDomain x,
                ∑ m ∈ inclusiveNatDomain x,
                  if 2 ≤ r ∧ ((((p ^ r) * m : ℕ) : ℝ) ≤ x) then
                    rawTerm h p r m else 0) := by
        simp only [Finset.sum_add_distrib]
      _ = firstPowerContribution h x + higherPowerContribution h x := by
        rw [first_raw_eq hx, higher_raw_eq hx]
  calc
    weightedLogMean h x = primePowerCoprimeSum h x := hreindex
    _ ≤ firstPowerContribution h x + higherPowerContribution h x := hraw
    _ ≤ firstPowerConstant lambda1 lambda2 * x * reciprocalMean h x +
        higherPowerConstant lambda1 lambda2 * x * reciprocalMean h x :=
      add_le_add hfirst hhigher
    _ = (firstPowerConstant lambda1 lambda2 +
          higherPowerConstant lambda1 lambda2) * x * reciprocalMean h x := by ring

theorem constructed : PublicTarget := by
  intro hP006 hP007 hP008 _hSmoothing hP004 hP005
  let hP009 : P009Statement := p009_checkpoint hP006 hP007 hP008
  refine ⟨hP009, ?_⟩
  intro h lambda1 lambda2 x hass hx
  let hh : Nonnegative h := hass.h_nonnegative_multiplicative.nonnegative
  have hx1 : 1 ≤ x := by linarith
  have hlogpos : 0 < Real.log x := Real.log_pos (by linarith)
  have hweighted := hP009 h lambda1 lambda2 x hass hx
  have hintegral := (hP004 h hh x hx1).integral_only
  have hidentity := hP005 h hh x hx1
  have hproduct : inclusiveMean h x * Real.log x ≤
      (firstPowerConstant lambda1 lambda2 +
          higherPowerConstant lambda1 lambda2) * x * reciprocalMean h x +
        x * reciprocalMean h x := by
    rw [hidentity]
    exact add_le_add hweighted hintegral
  calc
    inclusiveMean h x =
        (inclusiveMean h x * Real.log x) / Real.log x := by
      field_simp
    _ ≤ ((firstPowerConstant lambda1 lambda2 +
          higherPowerConstant lambda1 lambda2) * x * reciprocalMean h x +
        x * reciprocalMean h x) / Real.log x :=
      div_le_div_of_nonneg_right hproduct hlogpos.le
    _ = (firstPowerConstant lambda1 lambda2 +
          higherPowerConstant lambda1 lambda2 + 1) *
        (x / Real.log x) * reciprocalMean h x := by
      field_simp

end Erdos448.DPMean.TaskT07
