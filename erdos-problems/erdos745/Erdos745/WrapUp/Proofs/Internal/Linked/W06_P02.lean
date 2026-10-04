module

public import Erdos745.WrapUp.Contracts

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local simp] Pi.div_def Pi.mul_def Pi.add_def Pi.sub_def Pi.neg_def Pi.inv_def Function.comp_def Pi.pow_def Pi.smul_def Real.rpow_eq_pow

@[expose] public section


namespace Erdos745.WrapUp.Proofs.W06_POISSON

noncomputable section

open Erdos745.WrapUp
open Filter
open scoped Topology

/-- The Stirling correction in a form whose convergence is directly exposed by
Mathlib's `Stirling.stirlingSeq`.  For positive component orders this is the
factor multiplying the standard `k ^ (-5/2) * exp (-a*k)` tree tail. -/
def cayleyStirlingRatio (k : ℕ) : ℝ :=
  Real.sqrt Real.pi / Stirling.stirlingSeq k

lemma cayleyStirlingRatio_tendsto_one :
    Tendsto cayleyStirlingRatio atTop (nhds 1) := by
  have hsqrt : Real.sqrt Real.pi ≠ 0 := by positivity
  have hconst : Tendsto (fun _ : ℕ ↦ Real.sqrt Real.pi) atTop
      (nhds (Real.sqrt Real.pi)) := tendsto_const_nhds
  change Tendsto (fun k => Real.sqrt Real.pi / Stirling.stirlingSeq k) atTop (nhds 1)
  simpa [hsqrt] using!
    hconst.div Stirling.tendsto_stirlingSeq_sqrt_pi hsqrt

lemma cayleyStirlingRatio_bddAbove :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, cayleyStirlingRatio k ≤ C := by
  obtain ⟨C, hC⟩ := cayleyStirlingRatio_tendsto_one.bddAbove_range
  refine ⟨max C 1, by positivity, ?_⟩
  intro k
  exact (hC ⟨k, rfl⟩).trans (le_max_left _ _)

def cayleyKernel (k : ℕ) : ℝ :=
  (cayley k : ℝ) / (k.factorial : ℝ) * Real.exp (-(k : ℝ))

lemma degreeExp_pow_eq_rateExp (lam : ℝ) (k : ℕ) (hlam : 0 < lam) :
    (lam * Real.exp (-lam)) ^ k =
      Real.exp (-(k : ℝ)) * Real.exp (-rate lam * (k : ℝ)) := by
  have hbase : lam * Real.exp (-lam) = Real.exp (Real.log lam - lam) := by
    calc
      lam * Real.exp (-lam) = Real.exp (Real.log lam) * Real.exp (-lam) := by
        rw [Real.exp_log hlam]
      _ = Real.exp (Real.log lam + -lam) := by rw [Real.exp_add]
      _ = Real.exp (Real.log lam - lam) := rfl
  rw [hbase, ← Real.exp_nat_mul, ← Real.exp_add]
  congr 1
  simp only [rate]
  ring

lemma treeLeading_eq_cayleyKernel (n M k : ℕ) (hk : 0 < k)
    (hlam : 0 < degreeAt n M) :
    treeLeading n M k =
      (n : ℝ) / degreeAt n M * cayleyKernel k *
        Real.exp (-rate (degreeAt n M) * (k : ℝ)) := by
  rw [treeLeading, if_neg hk.ne']
  rw [degreeExp_pow_eq_rateExp (degreeAt n M) k hlam]
  simp only [cayleyKernel]
  ring

lemma cayley_eq_pow_sub_two (k : ℕ) (hk : 0 < k) :
    cayley k = k ^ (k - 2) := by
  by_cases hk1 : k = 1
  · subst k
    simp [cayley]
  · simp [cayley, hk.ne', hk1]

lemma sqrt_pi_mul_sqrt_two_mul (x : ℝ) :
    Real.sqrt Real.pi * Real.sqrt (2 * x) =
      Real.sqrt (2 * Real.pi) * Real.sqrt x := by
  rw [← Real.sqrt_mul (Real.pi_nonneg),
    ← Real.sqrt_mul (by positivity : 0 ≤ 2 * Real.pi)]
  congr 1
  ring

lemma sqrt_mul_pow_mul_rpow (k : ℕ) (hk : 2 ≤ k) :
    Real.sqrt (k : ℝ) * ((k : ℝ) / Real.exp 1) ^ k *
        (k : ℝ) ^ (-(5 / 2) : ℝ) =
      ((k : ℝ) ^ (k - 2)) * Real.exp (-(k : ℝ)) := by
  have hkpos : 0 < (k : ℝ) := by positivity
  have hpow : Real.sqrt (k : ℝ) * (k : ℝ) ^ k *
        (k : ℝ) ^ (-(5 / 2) : ℝ) =
      (k : ℝ) ^ (k - 2) := by
    calc
      Real.sqrt (k : ℝ) * (k : ℝ) ^ k *
          (k : ℝ) ^ (-(5 / 2) : ℝ) =
          (k : ℝ) ^ (1 / 2 : ℝ) *
            (k : ℝ) ^ (k : ℝ) *
              (k : ℝ) ^ (-(5 / 2) : ℝ) := by
                rw [Real.sqrt_eq_rpow, Real.rpow_natCast]
      _ = (k : ℝ) ^ ((1 / 2 : ℝ) + (k : ℝ)) *
            (k : ℝ) ^ (-(5 / 2) : ℝ) := by
              exact congrArg
                (fun z ↦ z * (k : ℝ) ^ (-(5 / 2) : ℝ))
                (Real.rpow_add hkpos (1 / 2 : ℝ) (k : ℝ)).symm
      _ = (k : ℝ) ^
            (((1 / 2 : ℝ) + (k : ℝ)) + (-(5 / 2) : ℝ)) := by
              exact (Real.rpow_add hkpos
                ((1 / 2 : ℝ) + (k : ℝ)) (-(5 / 2) : ℝ)).symm
      _ = (k : ℝ) ^ (k - 2) := by
        have hexp : (1 / 2 : ℝ) + (k : ℝ) + (-(5 / 2) : ℝ) =
            ((k - 2 : ℕ) : ℝ) := by
          rw [Nat.cast_sub hk]
          push_cast
          ring
        rw [hexp]
        simp only [Real.rpow_natCast]
  rw [div_pow, ← Real.exp_nat_mul]
  norm_num only [mul_one]
  rw [div_eq_mul_inv, ← Real.exp_neg]
  calc
    Real.sqrt (k : ℝ) * ((k : ℝ) ^ k * Real.exp (-(k : ℝ))) *
        (k : ℝ) ^ (-(5 / 2) : ℝ) =
        (Real.sqrt (k : ℝ) * (k : ℝ) ^ k *
          (k : ℝ) ^ (-(5 / 2) : ℝ)) * Real.exp (-(k : ℝ)) := by
            ring
    _ = ((k : ℝ) ^ (k - 2)) * Real.exp (-(k : ℝ)) := by rw [hpow]

lemma cayleyKernel_eq_stirling (k : ℕ) (hk : 0 < k) :
    cayleyKernel k =
      cayleyStirlingRatio k / Real.sqrt (2 * Real.pi) *
        (k : ℝ) ^ (-(5 / 2) : ℝ) := by
  by_cases hk1 : k = 1
  · subst k
    simp only [cayleyKernel, cayleyStirlingRatio, Stirling.stirlingSeq_one,
      cayley, Nat.factorial_one, Nat.cast_one, Real.exp_neg]
    have hsqrt : Real.sqrt (2 * Real.pi) ≠ 0 := by positivity
    have hsqrtTwo : Real.sqrt (2 : ℝ) ≠ 0 := by positivity
    field_simp
    simpa using! (sqrt_pi_mul_sqrt_two_mul 1).symm
  · have hk2 : 2 ≤ k := by omega
    have hkpos : 0 < (k : ℝ) := by positivity
    have hfact : (k.factorial : ℝ) ≠ 0 := by positivity
    have hsqrt : Real.sqrt (2 * Real.pi) ≠ 0 := by positivity
    have hstirlingDenom :
        Real.sqrt (2 * (k : ℝ)) * ((k : ℝ) / Real.exp 1) ^ k ≠ 0 := by
      positivity
    rw [cayleyKernel, cayleyStirlingRatio, Stirling.stirlingSeq,
      cayley_eq_pow_sub_two k hk]
    push_cast
    rw [div_div]
    field_simp
    rw [show (k : ℝ) * 2 = 2 * (k : ℝ) by ring]
    rw [sqrt_pi_mul_sqrt_two_mul (k : ℝ)]
    have hp := sqrt_mul_pow_mul_rpow k hk2
    calc
      (k : ℝ) ^ (k - 2) * Real.exp (-(k : ℝ)) * Real.sqrt (2 * Real.pi) =
          Real.sqrt (2 * Real.pi) *
            ((k : ℝ) ^ (k - 2) * Real.exp (-(k : ℝ))) := by ring
      _ = Real.sqrt (2 * Real.pi) *
          (Real.sqrt (k : ℝ) * ((k : ℝ) / Real.exp 1) ^ k *
            (k : ℝ) ^ (-(5 / 2) : ℝ)) := by rw [hp]
      _ = Real.sqrt (2 * Real.pi) * Real.sqrt (k : ℝ) *
          ((k : ℝ) / Real.exp 1) ^ k *
            (k : ℝ) ^ (-(5 / 2) : ℝ) := by ring

def weightedTreeTail (a : ℝ) (h : ℕ) : ℝ :=
  ∑' k : ℕ, if h ≤ k ∧ 0 < k then
    cayleyStirlingRatio k * (k : ℝ) ^ (-(5 / 2) : ℝ) *
      Real.exp (-a * (k : ℝ))
  else 0

def treeLeadingTail (n M h : ℕ) : ℝ :=
  ∑' k : ℕ, if h ≤ k ∧ 0 < k then treeLeading n M k else 0

lemma treeLeadingTail_eq_weightedTreeTail (n M h : ℕ)
    (hlam : 0 < degreeAt n M) :
    treeLeadingTail n M h =
      (n : ℝ) / (degreeAt n M * Real.sqrt (2 * Real.pi)) *
        weightedTreeTail (rate (degreeAt n M)) h := by
  rw [treeLeadingTail, weightedTreeTail, ← tsum_mul_left]
  apply tsum_congr
  intro k
  by_cases hk : h ≤ k ∧ 0 < k
  · simp only [if_pos hk]
    rw [treeLeading_eq_cayleyKernel n M k hk.2 hlam,
      cayleyKernel_eq_stirling k hk.2]
    ring
  · simp [hk]

lemma cayleyStirlingRatio_pos (k : ℕ) (hk : 0 < k) :
    0 < cayleyStirlingRatio k := by
  have hk0 : k ≠ 0 := hk.ne'
  have hsqrt : 0 < Real.sqrt Real.pi := by positivity
  have hstirling : 0 < Stirling.stirlingSeq k :=
    lt_of_lt_of_le hsqrt (Stirling.sqrt_pi_le_stirlingSeq hk0)
  exact div_pos hsqrt hstirling

lemma treeTail_summable (a : ℝ) (h : ℕ) (ha : 0 < a) :
    Summable (fun k : ℕ ↦ if h ≤ k ∧ 0 < k then
      (k : ℝ) ^ (-(5 / 2) : ℝ) * Real.exp (-a * (k : ℝ)) else 0) := by
  have hratio : ‖Real.exp (-a)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_lt_one_iff]
    linarith
  have hgeom : Summable (fun k : ℕ ↦ Real.exp (-a) ^ k) :=
    summable_geometric_of_norm_lt_one hratio
  have hnonneg : ∀ k : ℕ, 0 ≤ (if h ≤ k ∧ 0 < k then
      (k : ℝ) ^ (-(5 / 2) : ℝ) * Real.exp (-a * (k : ℝ)) else 0) := by
    intro k
    split_ifs
    · positivity
    · exact le_rfl
  have hle : ∀ k : ℕ, (if h ≤ k ∧ 0 < k then
      (k : ℝ) ^ (-(5 / 2) : ℝ) * Real.exp (-a * (k : ℝ)) else 0) ≤
        Real.exp (-a) ^ k := by
    intro k
    by_cases hk : h ≤ k ∧ 0 < k
    · rw [if_pos hk]
      have hkOne : (1 : ℝ) ≤ k := by exact_mod_cast hk.2
      have hrpow : (k : ℝ) ^ (-(5 / 2) : ℝ) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hkOne (by norm_num)
      calc
        (k : ℝ) ^ (-(5 / 2) : ℝ) * Real.exp (-a * (k : ℝ)) ≤
            1 * Real.exp (-a * (k : ℝ)) :=
          mul_le_mul_of_nonneg_right hrpow (Real.exp_nonneg _)
        _ = Real.exp (-a) ^ k := by
          calc
            1 * Real.exp (-a * (k : ℝ)) = Real.exp (-a * (k : ℝ)) := one_mul _
            _ = Real.exp ((k : ℝ) * (-a)) := by
              congr 1
              ring_nf
            _ = Real.exp (-a) ^ k := Real.exp_nat_mul (-a) k
    · simp only [if_neg hk]
      positivity
  exact Summable.of_nonneg_of_le hnonneg hle hgeom

lemma treeTail_pos (a : ℝ) (h : ℕ) (ha : 0 < a) :
    0 < treeTail a h := by
  let k0 := max h 1
  have hk0h : h ≤ k0 := le_max_left _ _
  have hk0pos : 0 < k0 := lt_of_lt_of_le Nat.zero_lt_one (le_max_right _ _)
  have hs := treeTail_summable a h ha
  rw [treeTail]
  simp_rw [Real.rpow_eq_pow]
  have hexp : (-5 / 2 : ℝ) = (-(5 / 2) : ℝ) := by ring
  rw [hexp]
  have hnonneg : ∀ k : ℕ, 0 ≤ (if h ≤ k ∧ 0 < k then
      (k : ℝ) ^ (-(5 / 2) : ℝ) * Real.exp (-a * (k : ℝ)) else 0) := by
    intro k
    split_ifs
    · positivity
    · exact le_rfl
  have hpos : 0 < (if h ≤ k0 ∧ 0 < k0 then
      (k0 : ℝ) ^ (-(5 / 2) : ℝ) * Real.exp (-a * (k0 : ℝ)) else 0) := by
    rw [if_pos ⟨hk0h, hk0pos⟩]
    positivity
  exact hs.tsum_pos hnonneg k0 hpos

lemma weightedTreeTail_summable (a : ℝ) (h : ℕ) (ha : 0 < a) :
    Summable (fun k : ℕ ↦ if h ≤ k ∧ 0 < k then
      cayleyStirlingRatio k * (k : ℝ) ^ (-(5 / 2) : ℝ) *
        Real.exp (-a * (k : ℝ)) else 0) := by
  obtain ⟨C, hCpos, hC⟩ := cayleyStirlingRatio_bddAbove
  have hs := (treeTail_summable a h ha).mul_left C
  have hnonneg : ∀ k : ℕ, 0 ≤ (if h ≤ k ∧ 0 < k then
      cayleyStirlingRatio k * (k : ℝ) ^ (-(5 / 2) : ℝ) *
        Real.exp (-a * (k : ℝ)) else 0) := by
    intro k
    by_cases hk : h ≤ k ∧ 0 < k
    · rw [if_pos hk]
      exact mul_nonneg
        (mul_nonneg (cayleyStirlingRatio_pos k hk.2).le (by positivity))
        (Real.exp_nonneg _)
    · simp [hk]
  have hle : ∀ k : ℕ, (if h ≤ k ∧ 0 < k then
      cayleyStirlingRatio k * (k : ℝ) ^ (-(5 / 2) : ℝ) *
        Real.exp (-a * (k : ℝ)) else 0) ≤
      C * (if h ≤ k ∧ 0 < k then
        (k : ℝ) ^ (-(5 / 2) : ℝ) * Real.exp (-a * (k : ℝ)) else 0) := by
    intro k
    by_cases hk : h ≤ k ∧ 0 < k
    · simp only [if_pos hk]
      have hbase : 0 ≤ (k : ℝ) ^ (-(5 / 2) : ℝ) *
          Real.exp (-a * (k : ℝ)) := by positivity
      simpa [mul_assoc] using! mul_le_mul_of_nonneg_right (hC k) hbase
    · simp [hk]
  exact Summable.of_nonneg_of_le hnonneg hle hs

lemma weightedTreeTail_div_treeTail_tendsto_one
    (aa : RealSeq) (hs : NatSeq)
    (ha : ∀ᶠ n in atTop, 0 < aa n)
    (hh : Tendsto hs atTop atTop) :
    Tendsto (fun n ↦ weightedTreeTail (aa n) (hs n) / treeTail (aa n) (hs n))
      atTop (nhds 1) := by
  have hexp : (-5 / 2 : ℝ) = (-(5 / 2) : ℝ) := by ring
  rw [tendsto_order]
  constructor
  · intro x hx
    let c : ℝ := (x + 1) / 2
    have hxc : x < c := by dsimp [c]; linarith
    have hc1 : c < 1 := by dsimp [c]; linarith
    have hrho : ∀ᶠ k in atTop, c < cayleyStirlingRatio k :=
      (tendsto_order.1 cayleyStirlingRatio_tendsto_one).1 c hc1
    obtain ⟨N, hN⟩ := eventually_atTop.1 hrho
    have hhs : ∀ᶠ n in atTop, N ≤ hs n := (tendsto_atTop.1 hh) N
    filter_upwards [ha, hhs] with n han hhn
    have htpos : 0 < treeTail (aa n) (hs n) := treeTail_pos _ _ han
    have hsBase := treeTail_summable (aa n) (hs n) han
    have hsWeight := weightedTreeTail_summable (aa n) (hs n) han
    have hle : c * treeTail (aa n) (hs n) ≤
        weightedTreeTail (aa n) (hs n) := by
      rw [treeTail, weightedTreeTail]
      simp_rw [Real.rpow_eq_pow]
      rw [hexp]
      rw [← tsum_mul_left]
      apply Summable.tsum_le_tsum
      · intro k
        by_cases hk : hs n ≤ k ∧ 0 < k
        · simp only [if_pos hk]
          have hbase : 0 ≤ (k : ℝ) ^ (-(5 / 2) : ℝ) *
              Real.exp (-aa n * (k : ℝ)) := by positivity
          simpa [mul_assoc] using!
            mul_le_mul_of_nonneg_right (hN k (hhn.trans hk.1)).le hbase
        · simp [hk]
      · exact hsBase.mul_left c
      · exact hsWeight
    calc
      x < c := hxc
      _ = c * treeTail (aa n) (hs n) / treeTail (aa n) (hs n) := by
        field_simp
      _ ≤ weightedTreeTail (aa n) (hs n) / treeTail (aa n) (hs n) :=
        (div_le_div_iff_of_pos_right htpos).2 hle
  · intro x hx
    let c : ℝ := (x + 1) / 2
    have h1c : 1 < c := by dsimp [c]; linarith
    have hcx : c < x := by dsimp [c]; linarith
    have hrho : ∀ᶠ k in atTop, cayleyStirlingRatio k < c :=
      (tendsto_order.1 cayleyStirlingRatio_tendsto_one).2 c h1c
    obtain ⟨N, hN⟩ := eventually_atTop.1 hrho
    have hhs : ∀ᶠ n in atTop, N ≤ hs n := (tendsto_atTop.1 hh) N
    filter_upwards [ha, hhs] with n han hhn
    have htpos : 0 < treeTail (aa n) (hs n) := treeTail_pos _ _ han
    have hsBase := treeTail_summable (aa n) (hs n) han
    have hsWeight := weightedTreeTail_summable (aa n) (hs n) han
    have hle : weightedTreeTail (aa n) (hs n) ≤
        c * treeTail (aa n) (hs n) := by
      rw [treeTail, weightedTreeTail]
      simp_rw [Real.rpow_eq_pow]
      rw [hexp]
      rw [← tsum_mul_left]
      apply Summable.tsum_le_tsum
      · intro k
        by_cases hk : hs n ≤ k ∧ 0 < k
        · simp only [if_pos hk]
          have hbase : 0 ≤ (k : ℝ) ^ (-(5 / 2) : ℝ) *
              Real.exp (-aa n * (k : ℝ)) := by positivity
          simpa [mul_assoc] using!
            mul_le_mul_of_nonneg_right (hN k (hhn.trans hk.1)).le hbase
        · simp [hk]
      · exact hsWeight
      · exact hsBase.mul_left c
    calc
      weightedTreeTail (aa n) (hs n) / treeTail (aa n) (hs n) ≤
          c * treeTail (aa n) (hs n) / treeTail (aa n) (hs n) :=
        (div_le_div_iff_of_pos_right htpos).2 hle
      _ = c := by field_simp
      _ < x := hcx

def normalizedTailSeries (a : ℝ) (h : ℕ) : ℝ :=
  ∑' s : ℕ, (1 + (s : ℝ) / h) ^ (-(5 / 2) : ℝ) *
    Real.exp (-a * (s : ℝ))

lemma treeTail_eq_leading_mul_normalizedTailSeries
    (a : ℝ) (h : ℕ) (ha : 0 < a) (hh : 0 < h) :
    treeTail a h =
      (h : ℝ) ^ (-(5 / 2) : ℝ) * Real.exp (-a * (h : ℝ)) *
        normalizedTailSeries a h := by
  let f : ℕ → ℝ := fun k ↦ if h ≤ k ∧ 0 < k then
    (k : ℝ) ^ (-(5 / 2) : ℝ) * Real.exp (-a * (k : ℝ)) else 0
  have hsum : Summable f := treeTail_summable a h ha
  have hsplit := hsum.sum_add_tsum_nat_add h
  have hprefix : ∑ k ∈ Finset.range h, f k = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    have hklt : k < h := Finset.mem_range.1 hk
    have hkh : ¬ h ≤ k := by omega
    simp [f, hkh]
  have hshift : (∑' k : ℕ, f k) = ∑' s : ℕ, f (s + h) := by
    rw [hprefix, zero_add] at hsplit
    exact hsplit.symm
  rw [treeTail]
  simp_rw [Real.rpow_eq_pow]
  have hneg : (-5 / 2 : ℝ) = (-(5 / 2) : ℝ) := by ring
  rw [hneg]
  change (∑' k : ℕ, f k) = _
  rw [hshift, normalizedTailSeries, ← tsum_mul_left]
  apply tsum_congr
  intro s
  have hle : h ≤ s + h := by omega
  have hpos : 0 < s + h := by omega
  rw [show f (s + h) =
      ((s + h : ℕ) : ℝ) ^ (-(5 / 2) : ℝ) *
        Real.exp (-a * ((s + h : ℕ) : ℝ)) by simp [f, hle, hpos]]
  have hhreal : (0 : ℝ) < h := by exact_mod_cast hh
  have hcast : ((s + h : ℕ) : ℝ) =
      (h : ℝ) * (1 + (s : ℝ) / h) := by
    push_cast
    field_simp
    ring
  rw [hcast, Real.mul_rpow hhreal.le (by positivity)]
  have hexp : -a * ((h : ℝ) * (1 + (s : ℝ) / h)) =
      -a * (h : ℝ) + -a * (s : ℝ) := by
    field_simp
    ring
  rw [hexp, Real.exp_add]
  ring

lemma normalizedTailSeries_tendsto
    (aa : RealSeq) (hs : NatSeq) (a : ℝ) (ha : 0 < a)
    (haa : Tendsto aa atTop (nhds a))
    (hhs : Tendsto hs atTop atTop) :
    Tendsto (fun n ↦ normalizedTailSeries (aa n) (hs n)) atTop
      (nhds ((1 - Real.exp (-a))⁻¹)) := by
  let f : ℕ → ℕ → ℝ := fun n s ↦
    (1 + (s : ℝ) / hs n) ^ (-(5 / 2) : ℝ) *
      Real.exp (-aa n * (s : ℝ))
  let g : ℕ → ℝ := fun s ↦ Real.exp (-a * (s : ℝ))
  let bound : ℕ → ℝ := fun s ↦ Real.exp (-(a / 2)) ^ s
  have hratio : ‖Real.exp (-(a / 2))‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_lt_one_iff]
    linarith
  have hbound : Summable bound := by
    exact summable_geometric_of_norm_lt_one hratio
  have hpoint : ∀ s : ℕ, Tendsto (fun n ↦ f n s) atTop (nhds (g s)) := by
    intro s
    have hdiv : Tendsto (fun n ↦ (s : ℝ) / (hs n : ℝ)) atTop (nhds 0) :=
      (tendsto_const_div_atTop_nhds_zero_nat (s : ℝ)).comp hhs
    have hone : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (nhds 1) :=
      tendsto_const_nhds
    have hbase : Tendsto (fun n ↦ 1 + (s : ℝ) / (hs n : ℝ)) atTop
        (nhds 1) := by simpa using! hone.add hdiv
    have hrpow : Tendsto
        (fun n ↦ (1 + (s : ℝ) / (hs n : ℝ)) ^ (-(5 / 2) : ℝ))
        atTop (nhds 1) := by
      simpa using! hbase.rpow_const (Or.inl one_ne_zero)
    have hexpArg : Tendsto (fun n ↦ -aa n * (s : ℝ)) atTop
        (nhds (-a * (s : ℝ))) := by
      simpa using! (haa.neg.mul_const (s : ℝ))
    have hexp : Tendsto (fun n ↦ Real.exp (-aa n * (s : ℝ))) atTop
        (nhds (Real.exp (-a * (s : ℝ)))) := by
      exact Real.continuous_exp.continuousAt.tendsto.comp hexpArg
    simpa [f, g] using! hrpow.mul hexp
  have haaLower : ∀ᶠ n in atTop, a / 2 ≤ aa n := by
    have haHalf : a / 2 < a := by linarith
    exact ((tendsto_order.1 haa).1 (a / 2) haHalf).mono fun _ h ↦ h.le
  have hdom : ∀ᶠ n in atTop, ∀ s : ℕ, ‖f n s‖ ≤ bound s := by
    filter_upwards [haaLower] with n hn
    intro s
    have hbaseOne : (1 : ℝ) ≤ 1 + (s : ℝ) / (hs n : ℝ) := by
      have hdivNonneg : 0 ≤ (s : ℝ) / (hs n : ℝ) :=
        div_nonneg (by positivity) (by positivity)
      linarith
    have hrpowNonneg : 0 ≤
        (1 + (s : ℝ) / (hs n : ℝ)) ^ (-(5 / 2) : ℝ) := by positivity
    have hrpowLe :
        (1 + (s : ℝ) / (hs n : ℝ)) ^ (-(5 / 2) : ℝ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hbaseOne (by norm_num)
    have hexpLe : Real.exp (-aa n * (s : ℝ)) ≤
        Real.exp (-(a / 2) * (s : ℝ)) := by
      apply Real.exp_le_exp.mpr
      have hsnonneg : (0 : ℝ) ≤ s := by positivity
      nlinarith
    have htermNonneg : 0 ≤ f n s := by
      dsimp [f]
      positivity
    rw [Real.norm_eq_abs, abs_of_nonneg htermNonneg]
    calc
      f n s ≤ Real.exp (-aa n * (s : ℝ)) := by
        dsimp [f]
        simpa using! mul_le_of_le_one_left (Real.exp_nonneg _) hrpowLe
      _ ≤ Real.exp (-(a / 2) * (s : ℝ)) := hexpLe
      _ = bound s := by
        dsimp [bound]
        rw [← Real.exp_nat_mul]
        congr 1
        ring
  have htsum : Tendsto (fun n ↦ ∑' s : ℕ, f n s) atTop
      (nhds (∑' s : ℕ, g s)) :=
    tendsto_tsum_of_dominated_convergence hbound hpoint hdom
  have hgeo : (∑' s : ℕ, g s) = (1 - Real.exp (-a))⁻¹ := by
    have hnorm : ‖Real.exp (-a)‖ < 1 := by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_lt_one_iff]
      linarith
    rw [show (∑' s : ℕ, g s) = ∑' s : ℕ, Real.exp (-a) ^ s by
      apply tsum_congr
      intro s
      dsimp [g]
      rw [← Real.exp_nat_mul]
      congr 1
      ring]
    exact tsum_geometric_of_norm_lt_one hnorm
  rw [← hgeo]
  simpa [normalizedTailSeries, f] using! htsum

lemma treeTail_varying_positive_rate
    (aa : RealSeq) (hs : NatSeq) (a : ℝ) (ha : 0 < a)
    (haa : Tendsto aa atTop (nhds a))
    (hhs : Tendsto hs atTop atTop) :
    Tendsto (fun n ↦ treeTail (aa n) (hs n) /
      ((hs n : ℝ) ^ (-(5 / 2) : ℝ) *
        Real.exp (-aa n * (hs n : ℝ)) / (1 - Real.exp (-aa n))))
      atTop (nhds 1) := by
  have haEventually : ∀ᶠ n in atTop, 0 < aa n :=
    (tendsto_order.1 haa).1 0 ha
  have hhEventually : ∀ᶠ n in atTop, 0 < hs n := by
    have hOne : ∀ᶠ n in atTop, 1 ≤ hs n := (tendsto_atTop.1 hhs) 1
    exact hOne.mono fun _ hn ↦ lt_of_lt_of_le Nat.zero_lt_one hn
  have hnegExp : Tendsto (fun n ↦ Real.exp (-aa n)) atTop
      (nhds (Real.exp (-a))) := by
    have hneg : Tendsto (fun n ↦ -aa n) atTop (nhds (-a)) := haa.neg
    exact Real.continuous_exp.continuousAt.tendsto.comp hneg
  have hpref : Tendsto (fun n ↦ 1 - Real.exp (-aa n)) atTop
      (nhds (1 - Real.exp (-a))) := by
    have hone : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (nhds 1) :=
      tendsto_const_nhds
    exact hone.sub hnegExp
  have hseries := normalizedTailSeries_tendsto aa hs a ha haa hhs
  have hprod : Tendsto
      (fun n ↦ (1 - Real.exp (-aa n)) * normalizedTailSeries (aa n) (hs n))
      atTop (nhds 1) := by
    have hmul := hpref.mul hseries
    have hne : 1 - Real.exp (-a) ≠ 0 := by
      have : Real.exp (-a) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
      linarith
    convert hmul using 1
    field_simp
  apply hprod.congr'
  filter_upwards [haEventually, hhEventually] with n han hhn
  rw [treeTail_eq_leading_mul_normalizedTailSeries (aa n) (hs n) han hhn]
  have hpow : (hs n : ℝ) ^ (-(5 / 2) : ℝ) ≠ 0 := by positivity
  have hexp : Real.exp (-aa n * (hs n : ℝ)) ≠ 0 := Real.exp_ne_zero _
  have hprefne : 1 - Real.exp (-aa n) ≠ 0 := by
    have : Real.exp (-aa n) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    linarith
  field_simp

end

end Erdos745.WrapUp.Proofs.W06_POISSON


namespace Erdos745.WrapUp.Proofs.W06_POISSON

noncomputable section

open Erdos745.WrapUp
open Filter
open scoped BigOperators Topology

def inRectangle {n q : ℕ} (h H : ℕ) (ks : Fin q → Fin (n + 1)) : Prop :=
  ∀ i, h ≤ (ks i).val ∧ (ks i).val ≤ H

def rectangleTupleSum (n M q h H : ℕ) : ℝ :=
  by
    classical
    exact ∑ ks : Fin q → Fin (n + 1),
      if inRectangle h H ks then tupleMoment n M q (fun i ↦ (ks i).val) else 0

def rectangleLeadingSum (n M q h H : ℕ) : ℝ :=
  by
    classical
    exact ∑ ks : Fin q → Fin (n + 1),
      if inRectangle h H ks then tupleLeading n M q (fun i ↦ (ks i).val) else 0

def truncatedTreeLeadingSum (n M h H : ℕ) : ℝ :=
  by
    classical
    exact ∑ k : Fin (n + 1),
      if h ≤ k.val ∧ k.val ≤ H then treeLeading n M k.val else 0

lemma rectangleLeadingSum_eq_pow (n M q h H : ℕ) :
    rectangleLeadingSum n M q h H =
      truncatedTreeLeadingSum n M h H ^ q := by
  classical
  rw [rectangleLeadingSum, truncatedTreeLeadingSum, Fintype.sum_pow]
  apply Finset.sum_congr rfl
  intro ks _
  simp only [tupleLeading]
  by_cases hrect : inRectangle h H ks
  · rw [if_pos hrect]
    apply Finset.prod_congr rfl
    intro i _
    rw [if_pos (hrect i)]
  · rw [if_neg hrect]
    rw [inRectangle] at hrect
    push_neg at hrect
    obtain ⟨i, hi⟩ := hrect
    symm
    apply (Finset.prod_eq_zero (Finset.mem_univ i))
    rw [if_neg (by
      intro hboth
      exact (not_le_of_gt (hi hboth.1)) hboth.2)]

lemma exp_neg_mul_le_of_abs_log_div_le
    {x y eta : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hlog : |Real.log (x / y)| ≤ eta) :
    Real.exp (-eta) * y ≤ x := by
  have hLower : -eta ≤ Real.log (x / y) := (abs_le.1 hlog).1
  have hExp := Real.exp_le_exp.mpr hLower
  have hdiv : 0 < x / y := div_pos hx hy
  calc
    Real.exp (-eta) * y ≤ Real.exp (Real.log (x / y)) * y :=
      mul_le_mul_of_nonneg_right hExp hy.le
    _ = x := by rw [Real.exp_log hdiv]; field_simp

lemma le_exp_mul_of_abs_log_div_le
    {x y eta : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hlog : |Real.log (x / y)| ≤ eta) :
    x ≤ Real.exp eta * y := by
  have hUpper : Real.log (x / y) ≤ eta := (abs_le.1 hlog).2
  have hExp := Real.exp_le_exp.mpr hUpper
  have hdiv : 0 < x / y := div_pos hx hy
  calc
    x = Real.exp (Real.log (x / y)) * y := by
      rw [Real.exp_log hdiv]
      field_simp
    _ ≤ Real.exp eta * y := mul_le_mul_of_nonneg_right hExp hy.le

lemma tupleLeading_pos_of_coordinates
    (n M q : ℕ) (ks : Fin q → ℕ)
    (hn : 0 < n) (hdegree : 0 < degreeAt n M)
    (hks : ∀ i, 0 < ks i) :
    0 < tupleLeading n M q ks := by
  rw [tupleLeading]
  apply Finset.prod_pos
  intro i _
  simp only [treeLeading, if_neg (hks i).ne']
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hcayley : 0 < (cayley (ks i) : ℝ) := by
    rw [cayley_eq_pow_sub_two (ks i) (hks i)]
    exact_mod_cast Nat.pow_pos (hks i)
  have hfact : 0 < ((ks i).factorial : ℝ) := by positivity
  have hbase : 0 < degreeAt n M * Real.exp (-degreeAt n M) :=
    mul_pos hdegree (Real.exp_pos _)
  positivity

lemma rectangleTupleSum_sandwich
    (n M q h H : ℕ) (eta : ℝ)
    (hn : 0 < n) (hdegree : 0 < degreeAt n M) (hh : 0 < h)
    (hLocal : ∀ ks : Fin q → Fin (n + 1), inRectangle h H ks →
      0 < tupleMoment n M q (fun i ↦ (ks i).val) ∧
      |Real.log (tupleMoment n M q (fun i ↦ (ks i).val) /
        tupleLeading n M q (fun i ↦ (ks i).val))| ≤ eta) :
    Real.exp (-eta) * rectangleLeadingSum n M q h H ≤
      rectangleTupleSum n M q h H ∧
    rectangleTupleSum n M q h H ≤
      Real.exp eta * rectangleLeadingSum n M q h H := by
  classical
  constructor
  · rw [rectangleLeadingSum, rectangleTupleSum, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro ks _
    by_cases hrect : inRectangle h H ks
    · simp only [if_pos hrect]
      have hks : ∀ i, 0 < (ks i).val := fun i ↦ lt_of_lt_of_le hh (hrect i).1
      exact exp_neg_mul_le_of_abs_log_div_le
        (hLocal ks hrect).1
        (tupleLeading_pos_of_coordinates n M q (fun i ↦ (ks i).val)
          hn hdegree hks)
        (hLocal ks hrect).2
    · simp [hrect]
  · rw [rectangleLeadingSum, rectangleTupleSum, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro ks _
    by_cases hrect : inRectangle h H ks
    · simp only [if_pos hrect]
      have hks : ∀ i, 0 < (ks i).val := fun i ↦ lt_of_lt_of_le hh (hrect i).1
      exact le_exp_mul_of_abs_log_div_le
        (hLocal ks hrect).1
        (tupleLeading_pos_of_coordinates n M q (fun i ↦ (ks i).val)
          hn hdegree hks)
        (hLocal ks hrect).2
    · simp [hrect]

end

end Erdos745.WrapUp.Proofs.W06_POISSON


namespace Erdos745.WrapUp.Proofs.W06_POISSON

noncomputable section

open Erdos745.WrapUp
open Filter
open scoped Topology

lemma tendsto_rate_of_tendsto
    {u : RealSeq} {lam : ℝ} (hlam : 0 < lam)
    (hu : Tendsto u atTop (nhds lam)) :
    Tendsto (fun n ↦ rate (u n)) atTop (nhds (rate lam)) := by
  have hone : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (nhds 1) :=
    tendsto_const_nhds
  simpa [rate] using! (hu.sub hone).sub (hu.log hlam.ne')

lemma eventually_pos_ne_one_of_tendsto
    {u : RealSeq} {lam : ℝ} (hlam : 0 < lam) (hlam1 : lam ≠ 1)
    (hu : Tendsto u atTop (nhds lam)) :
    ∀ᶠ n in atTop, 0 < u n ∧ u n ≠ 1 := by
  have hpos : ∀ᶠ n in atTop, 0 < u n :=
    (tendsto_order.1 hu).1 0 hlam
  rcases lt_or_gt_of_ne hlam1 with hlt | hgt
  · let c : ℝ := (lam + 1) / 2
    have hlamc : lam < c := by dsimp [c]; linarith
    have hc1 : c < 1 := by dsimp [c]; linarith
    have hupper : ∀ᶠ n in atTop, u n < c :=
      (tendsto_order.1 hu).2 c hlamc
    filter_upwards [hpos, hupper] with n hn hc
    exact ⟨hn, ne_of_lt (hc.trans hc1)⟩
  · let c : ℝ := (lam + 1) / 2
    have h1c : 1 < c := by dsimp [c]; linarith
    have hclam : c < lam := by dsimp [c]; linarith
    have hlower : ∀ᶠ n in atTop, c < u n :=
      (tendsto_order.1 hu).1 c hclam
    filter_upwards [hpos, hlower] with n hn hc
    exact ⟨hn, ne_of_gt (h1c.trans hc)⟩

lemma weightedTreeTail_varying_positive_rate
    (aa : RealSeq) (hs : NatSeq) (a : ℝ) (ha : 0 < a)
    (haa : Tendsto aa atTop (nhds a))
    (hhs : Tendsto hs atTop atTop) :
    Tendsto (fun n ↦ weightedTreeTail (aa n) (hs n) /
      ((hs n : ℝ) ^ (-(5 / 2) : ℝ) *
        Real.exp (-aa n * (hs n : ℝ)) / (1 - Real.exp (-aa n))))
      atTop (nhds 1) := by
  have haEventually : ∀ᶠ n in atTop, 0 < aa n :=
    ((tendsto_order.1 haa).1 0 ha).mono fun _ h ↦ h
  have hRatio := weightedTreeTail_div_treeTail_tendsto_one aa hs haEventually hhs
  have hTail := treeTail_varying_positive_rate aa hs a ha haa hhs
  have hMul := hRatio.mul hTail
  have hMul' : Tendsto
      (fun n ↦ weightedTreeTail (aa n) (hs n) / treeTail (aa n) (hs n) *
        (treeTail (aa n) (hs n) /
          ((hs n : ℝ) ^ (-(5 / 2) : ℝ) *
            Real.exp (-aa n * (hs n : ℝ)) / (1 - Real.exp (-aa n)))))
      atTop (nhds 1) := by simpa using! hMul
  apply hMul'.congr'
  filter_upwards [haEventually] with n han
  have ht : treeTail (aa n) (hs n) ≠ 0 := (treeTail_pos _ _ han).ne'
  field_simp

lemma tendsto_rate_along_strictMono
    (M ns : NatSeq) (lam : ℝ) (hlam : 0 < lam)
    (hdegree : Tendsto (degree M) atTop (nhds lam))
    (hns : StrictMono ns) :
    Tendsto (fun j ↦ rate (degree M (ns j))) atTop (nhds (rate lam)) := by
  have hsub : Tendsto (fun j ↦ degree M (ns j)) atTop (nhds lam) :=
    hdegree.comp hns.tendsto_atTop
  exact tendsto_rate_of_tendsto hlam hsub

lemma treeLeadingTail_varying_positive_rate
    (hRate : RateStatement) (M ns hs : NatSeq) (lam : ℝ)
    (hlam : 0 < lam) (hlam1 : lam ≠ 1)
    (hdegree : Tendsto (degree M) atTop (nhds lam))
    (hns : StrictMono ns)
    (hhs : Tendsto hs atTop atTop) :
    Tendsto (fun j ↦ treeLeadingTail (ns j) (M (ns j)) (hs j) /
      ((ns j : ℝ) /
        (degree M (ns j) * Real.sqrt (2 * Real.pi)) *
        ((hs j : ℝ) ^ (-(5 / 2) : ℝ) *
          Real.exp (-rate (degree M (ns j)) * (hs j : ℝ)) /
            (1 - Real.exp (-rate (degree M (ns j)))))))
      atTop (nhds 1) := by
  let dd : RealSeq := fun j ↦ degree M (ns j)
  let aa : RealSeq := fun j ↦ rate (dd j)
  have hdd : Tendsto dd atTop (nhds lam) := by
    exact hdegree.comp hns.tendsto_atTop
  have haa : Tendsto aa atTop (nhds (rate lam)) := by
    exact tendsto_rate_of_tendsto hlam hdd
  have hrate : 0 < rate lam := hRate.1 lam hlam hlam1
  have hweighted := weightedTreeTail_varying_positive_rate aa hs (rate lam)
    hrate haa hhs
  have hddGood := eventually_pos_ne_one_of_tendsto hlam hlam1 hdd
  have hnsPos : ∀ᶠ j in atTop, 0 < ns j := by
    have hOne : ∀ᶠ j in atTop, 1 ≤ ns j := (tendsto_atTop.1 hns.tendsto_atTop) 1
    exact hOne.mono fun _ h ↦ lt_of_lt_of_le Nat.zero_lt_one h
  apply hweighted.congr'
  filter_upwards [hddGood, hnsPos] with j hd hj
  have hlead := treeLeadingTail_eq_weightedTreeTail
    (ns j) (M (ns j)) (hs j) hd.1
  have hvertex : (ns j : ℝ) ≠ 0 := by positivity
  have hdegreeNe : dd j ≠ 0 := hd.1.ne'
  have hsqrt : Real.sqrt (2 * Real.pi) ≠ 0 := by positivity
  have hdegEq : degreeAt (ns j) (M (ns j)) = degree M (ns j) := rfl
  rw [hdegEq] at hlead
  rw [hlead]
  dsimp [dd, aa]
  dsimp [dd] at hdegreeNe
  field_simp

lemma fixedDensity_threshold_asymptotics
    (hRate : RateStatement) (M ns h : NatSeq) (lam ell : ℝ)
    (hlam : 0 < lam) (hlam1 : lam ≠ 1)
    (hdegree : Tendsto (degree M) atTop (nhds lam))
    (hns : StrictMono ns)
    (hoffset : Tendsto (fun j ↦ (h j : ℝ) - center M (ns j))
      atTop (nhds ell)) :
    Tendsto (fun j ↦ (h j : ℝ) / Real.log (ns j : ℝ)) atTop
        (nhds (1 / rate lam)) ∧
      Tendsto h atTop atTop := by
  let NN : RealSeq := fun j ↦ (ns j : ℝ)
  let LL : RealSeq := fun j ↦ Real.log (NN j)
  let dd : RealSeq := fun j ↦ degree M (ns j)
  let aa : RealSeq := fun j ↦ rate (dd j)
  let uu : RealSeq := fun j ↦ (h j : ℝ) - center M (ns j)
  have hNN : Tendsto NN atTop atTop := by
    exact tendsto_natCast_atTop_atTop.comp hns.tendsto_atTop
  have hLL : Tendsto LL atTop atTop := by
    exact Real.tendsto_log_atTop.comp hNN
  have hdd : Tendsto dd atTop (nhds lam) := by
    exact hdegree.comp hns.tendsto_atTop
  have haa : Tendsto aa atTop (nhds (rate lam)) :=
    tendsto_rate_of_tendsto hlam hdd
  have hrate : 0 < rate lam := hRate.1 lam hlam hlam1
  have hloglogDiv : Tendsto (fun j ↦ Real.log (LL j) / LL j) atTop (nhds 0) := by
    exact (Real.isLittleO_log_id_atTop.comp_tendsto hLL).tendsto_div_nhds_zero
  have hnumRatio : Tendsto
      (fun j ↦ (LL j - (5 / 2 : ℝ) * Real.log (LL j)) / LL j)
      atTop (nhds 1) := by
    have hc : Tendsto (fun _ : ℕ ↦ (5 / 2 : ℝ)) atTop (nhds (5 / 2 : ℝ)) :=
      tendsto_const_nhds
    have hscaled := hc.mul hloglogDiv
    have hone : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (nhds 1) :=
      tendsto_const_nhds
    have hsub := hone.sub hscaled
    have hsub' : Tendsto
        (fun j ↦ 1 - (5 / 2 : ℝ) * (Real.log (LL j) / LL j))
        atTop (nhds 1) := by simpa using! hsub
    have hLLne : ∀ᶠ j in atTop, LL j ≠ 0 := by
      have hpos : ∀ᶠ j in atTop, 0 < LL j := (tendsto_atTop.1 hLL) 1 |>.mono
        fun _ hj ↦ lt_of_lt_of_le zero_lt_one hj
      exact hpos.mono fun _ hj ↦ hj.ne'
    apply hsub'.congr'
    filter_upwards [hLLne] with j hj
    field_simp
  have hcenterRatio : Tendsto
      (fun j ↦ center M (ns j) / LL j) atTop (nhds (1 / rate lam)) := by
    have hdiv := hnumRatio.div haa hrate.ne'
    have hgood : ∀ᶠ j in atTop, aa j ≠ 0 ∧ LL j ≠ 0 := by
      have haaPos : ∀ᶠ j in atTop, 0 < aa j :=
        ((tendsto_order.1 haa).1 0 hrate).mono fun _ hj ↦ hj
      have hLLPos : ∀ᶠ j in atTop, 0 < LL j := by
        have hOne : ∀ᶠ j in atTop, 1 ≤ LL j := (tendsto_atTop.1 hLL) 1
        exact hOne.mono fun _ hj ↦ lt_of_lt_of_le zero_lt_one hj
      filter_upwards [haaPos, hLLPos] with j haj hLj
      exact ⟨haj.ne', hLj.ne'⟩
    apply hdiv.congr'
    filter_upwards [hgood] with j hj
    dsimp [aa, dd, LL, NN]
    rw [center]
    field_simp
  have huu : Tendsto uu atTop (nhds ell) := by
    simpa [uu] using! hoffset
  have huuDiv : Tendsto (fun j ↦ uu j / LL j) atTop (nhds 0) :=
    huu.div_atTop hLL
  have hratio : Tendsto (fun j ↦ (h j : ℝ) / LL j) atTop
      (nhds (1 / rate lam)) := by
    have hadd := hcenterRatio.add huuDiv
    have hadd' : Tendsto (fun j ↦ center M (ns j) / LL j + uu j / LL j)
        atTop (nhds (1 / rate lam)) := by simpa using! hadd
    have hLLne : ∀ᶠ j in atTop, LL j ≠ 0 := by
      have hOne : ∀ᶠ j in atTop, 1 ≤ LL j := (tendsto_atTop.1 hLL) 1
      exact hOne.mono fun _ hj ↦ (lt_of_lt_of_le zero_lt_one hj).ne'
    apply hadd'.congr'
    filter_upwards [hLLne] with j hj
    dsimp [uu]
    field_simp
    ring
  have hcastTop : Tendsto (fun j ↦ (h j : ℝ)) atTop atTop := by
    have hprod : Tendsto (fun j ↦ LL j * ((h j : ℝ) / LL j)) atTop atTop :=
      hLL.atTop_mul_pos (one_div_pos.mpr hrate) hratio
    have hLLne : ∀ᶠ j in atTop, LL j ≠ 0 := by
      have hOne : ∀ᶠ j in atTop, 1 ≤ LL j := (tendsto_atTop.1 hLL) 1
      exact hOne.mono fun _ hj ↦ (lt_of_lt_of_le zero_lt_one hj).ne'
    apply hprod.congr'
    filter_upwards [hLLne] with j hj
    field_simp
  constructor
  · simpa [LL, NN] using! hratio
  · exact tendsto_natCast_atTop_iff.mp hcastTop

def fixedDensityLeadingNormalization
    (M ns h : NatSeq) (j : ℕ) : ℝ :=
  (ns j : ℝ) / (degree M (ns j) * Real.sqrt (2 * Real.pi)) *
    ((h j : ℝ) ^ (-(5 / 2) : ℝ) *
      Real.exp (-rate (degree M (ns j)) * (h j : ℝ)) /
        (1 - Real.exp (-rate (degree M (ns j)))))

lemma fixedDensityLeadingNormalization_tendsto
    (hRate : RateStatement) (M ns h : NatSeq) (lam ell : ℝ)
    (hlam : 0 < lam) (hlam1 : lam ≠ 1)
    (hdegree : Tendsto (degree M) atTop (nhds lam))
    (hns : StrictMono ns)
    (hoffset : Tendsto (fun j ↦ (h j : ℝ) - center M (ns j))
      atTop (nhds ell)) :
    Tendsto (fixedDensityLeadingNormalization M ns h) atTop
      (nhds (latticeRate lam ell)) := by
  let NN : RealSeq := fun j ↦ (ns j : ℝ)
  let LL : RealSeq := fun j ↦ Real.log (NN j)
  let dd : RealSeq := fun j ↦ degree M (ns j)
  let aa : RealSeq := fun j ↦ rate (dd j)
  let uu : RealSeq := fun j ↦ (h j : ℝ) - center M (ns j)
  have hNN : Tendsto NN atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hns.tendsto_atTop
  have hLL : Tendsto LL atTop atTop := Real.tendsto_log_atTop.comp hNN
  have hdd : Tendsto dd atTop (nhds lam) := hdegree.comp hns.tendsto_atTop
  have haa : Tendsto aa atTop (nhds (rate lam)) := tendsto_rate_of_tendsto hlam hdd
  have hrate : 0 < rate lam := hRate.1 lam hlam hlam1
  have hthreshold := fixedDensity_threshold_asymptotics hRate M ns h lam ell
    hlam hlam1 hdegree hns hoffset
  have hhOverL : Tendsto (fun j ↦ (h j : ℝ) / LL j) atTop
      (nhds (1 / rate lam)) := by
    simpa [LL, NN] using! hthreshold.1
  have hLOverH : Tendsto (fun j ↦ LL j / (h j : ℝ)) atTop
      (nhds (rate lam)) := by
    have hone' : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (nhds 1) :=
      tendsto_const_nhds
    have hinv := hone'.div hhOverL (by positivity : (1 / rate lam : ℝ) ≠ 0)
    have hinv' : Tendsto ((fun _ : ℕ ↦ (1 : ℝ)) /
        fun j ↦ (h j : ℝ) / LL j) atTop (nhds (rate lam)) := by
      convert hinv using 1
      field_simp [hrate.ne']
    have hhPos : ∀ᶠ j in atTop, 0 < h j := by
      have hOne : ∀ᶠ j in atTop, 1 ≤ h j := (tendsto_atTop.1 hthreshold.2) 1
      exact hOne.mono fun _ hj ↦ lt_of_lt_of_le Nat.zero_lt_one hj
    have hLLPos : ∀ᶠ j in atTop, 0 < LL j := by
      have hOne : ∀ᶠ j in atTop, 1 ≤ LL j := (tendsto_atTop.1 hLL) 1
      exact hOne.mono fun _ hj ↦ lt_of_lt_of_le zero_lt_one hj
    apply hinv'.congr'
    filter_upwards [hhPos, hLLPos] with j hhj hLj
    have hhreal : (0 : ℝ) < h j := by exact_mod_cast hhj
    change 1 / ((h j : ℝ) / LL j) = LL j / (h j : ℝ)
    field_simp [hLj.ne', hhreal.ne']
  have hpow : Tendsto (fun j ↦ (LL j / (h j : ℝ)) ^ (5 / 2 : ℝ)) atTop
      (nhds ((rate lam) ^ (5 / 2 : ℝ))) :=
    hLOverH.rpow_const (Or.inl hrate.ne')
  have huu : Tendsto uu atTop (nhds ell) := by simpa [uu] using! hoffset
  have hexpArg : Tendsto (fun j ↦ -aa j * uu j) atTop
      (nhds (-rate lam * ell)) := by
    exact haa.neg.mul huu
  have hexp : Tendsto (fun j ↦ Real.exp (-aa j * uu j)) atTop
      (nhds (Real.exp (-rate lam * ell))) :=
    Real.continuous_exp.continuousAt.tendsto.comp hexpArg
  have hdenExp : Tendsto (fun j ↦ Real.exp (-aa j)) atTop
      (nhds (Real.exp (-rate lam))) :=
    Real.continuous_exp.continuousAt.tendsto.comp haa.neg
  have hone : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (nhds 1) :=
    tendsto_const_nhds
  have hden : Tendsto (fun j ↦ 1 - Real.exp (-aa j)) atTop
      (nhds (1 - Real.exp (-rate lam))) := hone.sub hdenExp
  have hdenNe : 1 - Real.exp (-rate lam) ≠ 0 := by
    have : Real.exp (-rate lam) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    linarith
  have hsqrtNe : Real.sqrt (2 * Real.pi) ≠ 0 := by positivity
  have hlimit : Tendsto
      (fun j ↦ 1 / (dd j * Real.sqrt (2 * Real.pi)) *
        (LL j / (h j : ℝ)) ^ (5 / 2 : ℝ) *
          Real.exp (-aa j * uu j) / (1 - Real.exp (-aa j)))
      atTop (nhds (latticeRate lam ell)) := by
    have hconst : Tendsto (fun _ : ℕ ↦ Real.sqrt (2 * Real.pi)) atTop
        (nhds (Real.sqrt (2 * Real.pi))) := tendsto_const_nhds
    have hpref := hone.div (hdd.mul hconst) (mul_ne_zero hlam.ne' hsqrtNe)
    have hall := ((hpref.mul hpow).mul hexp).div hden hdenNe
    have htarget : 1 / (lam * Real.sqrt (2 * Real.pi)) *
        (rate lam) ^ (5 / 2 : ℝ) * Real.exp (-rate lam * ell) /
          (1 - Real.exp (-rate lam)) = latticeRate lam ell := by
      rw [latticeRate]
      rw [Real.rpow_eq_pow]
      field_simp [hlam.ne', hsqrtNe, hdenNe]
    rw [← htarget]
    apply hall.congr'
    exact Filter.Eventually.of_forall fun j ↦ by
      dsimp
  apply hlimit.congr'
  have haaPos : ∀ᶠ j in atTop, 0 < aa j :=
    ((tendsto_order.1 haa).1 0 hrate).mono fun _ hj ↦ hj
  have hLLPos : ∀ᶠ j in atTop, 0 < LL j := by
    have hOne : ∀ᶠ j in atTop, 1 ≤ LL j := (tendsto_atTop.1 hLL) 1
    exact hOne.mono fun _ hj ↦ lt_of_lt_of_le zero_lt_one hj
  have hhPos : ∀ᶠ j in atTop, 0 < h j := by
    have hOne : ∀ᶠ j in atTop, 1 ≤ h j := (tendsto_atTop.1 hthreshold.2) 1
    exact hOne.mono fun _ hj ↦ lt_of_lt_of_le Nat.zero_lt_one hj
  have hddPos : ∀ᶠ j in atTop, 0 < dd j :=
    (eventually_pos_ne_one_of_tendsto hlam hlam1 hdd).mono fun _ hj ↦ hj.1
  filter_upwards [haaPos, hLLPos, hhPos, hddPos] with j haj hLj hhj hdj
  have hNpos : 0 < NN j := by
    dsimp [NN]
    by_contra hnot
    have hzreal : (ns j : ℝ) = 0 :=
      le_antisymm (not_lt.1 hnot) (by positivity)
    have hz : ns j = 0 := by exact_mod_cast hzreal
    dsimp [dd, degree] at hdj
    simp [hz] at hdj
  have hcenterEq : aa j * center M (ns j) =
      LL j - (5 / 2 : ℝ) * Real.log (LL j) := by
    dsimp [aa, dd] at haj
    dsimp [aa, dd, LL, NN]
    rw [center]
    field_simp [haj.ne']
  have hExpArg : -aa j * (h j : ℝ) =
      -LL j + (5 / 2 : ℝ) * Real.log (LL j) - aa j * uu j := by
    dsimp [uu]
    nlinarith
  have hNexp : Real.exp (LL j) = NN j := by
    dsimp [LL]
    rw [Real.exp_log]
    exact hNpos
  have hLrpow : Real.exp ((5 / 2 : ℝ) * Real.log (LL j)) =
      (LL j) ^ (5 / 2 : ℝ) := by
    rw [Real.rpow_def_of_pos hLj]
    congr 1
    ring
  dsimp [fixedDensityLeadingNormalization, NN, dd, aa]
  rw [hExpArg]
  rw [show -LL j + (5 / 2 : ℝ) * Real.log (LL j) - aa j * uu j =
      -LL j + ((5 / 2 : ℝ) * Real.log (LL j)) + (-aa j * uu j) by ring]
  rw [Real.exp_add, Real.exp_add]
  rw [Real.exp_neg (LL j), hNexp, hLrpow]
  dsimp [NN, aa, dd]
  have hNne : NN j ≠ 0 := hNpos.ne'
  have hLne : LL j ≠ 0 := hLj.ne'
  have hhreal : (0 : ℝ) < h j := by exact_mod_cast hhj
  dsimp [dd] at hdj
  have hdenpos : 0 < 1 - Real.exp (-rate (degree M (ns j))) := by
    have hexplt : Real.exp (-rate (degree M (ns j))) < 1 :=
      Real.exp_lt_one_iff.mpr (by
        dsimp [aa, dd] at haj
        linarith)
    linarith
  rw [Real.div_rpow hLj.le hhreal.le]
  rw [Real.rpow_neg hhreal.le]
  field_simp [hdj.ne', hNpos.ne', hdenpos.ne']
  exact (mul_inv_cancel₀ hNpos.ne').symm

lemma fixedDensity_treeLeadingTail_tendsto
    (hRate : RateStatement) (M ns h : NatSeq) (lam ell : ℝ)
    (hlam : 0 < lam) (hlam1 : lam ≠ 1)
    (hdegree : Tendsto (degree M) atTop (nhds lam))
    (hns : StrictMono ns)
    (hoffset : Tendsto (fun j ↦ (h j : ℝ) - center M (ns j))
      atTop (nhds ell)) :
    Tendsto (fun j ↦ treeLeadingTail (ns j) (M (ns j)) (h j)) atTop
      (nhds (latticeRate lam ell)) := by
  have hthreshold := fixedDensity_threshold_asymptotics hRate M ns h lam ell
    hlam hlam1 hdegree hns hoffset
  have hratio := treeLeadingTail_varying_positive_rate hRate M ns h lam
    hlam hlam1 hdegree hns hthreshold.2
  have hnorm := fixedDensityLeadingNormalization_tendsto hRate M ns h lam ell
    hlam hlam1 hdegree hns hoffset
  have hmul := hratio.mul hnorm
  have hnormPos : ∀ᶠ j in atTop, 0 < fixedDensityLeadingNormalization M ns h j := by
    have hrate : 0 < rate lam := hRate.1 lam hlam hlam1
    have haa := tendsto_rate_along_strictMono M ns lam hlam hdegree hns
    have haaPos : ∀ᶠ j in atTop, 0 < rate (degree M (ns j)) :=
      ((tendsto_order.1 haa).1 0 hrate).mono fun _ hj ↦ hj
    have hdegreeSub : Tendsto (fun j ↦ degree M (ns j)) atTop (nhds lam) :=
      hdegree.comp hns.tendsto_atTop
    have hdPos : ∀ᶠ j in atTop, 0 < degree M (ns j) :=
      ((tendsto_order.1 hdegreeSub).1 0 hlam).mono fun _ hj ↦ hj
    have hhPos : ∀ᶠ j in atTop, 0 < h j := by
      have hOne : ∀ᶠ j in atTop, 1 ≤ h j := (tendsto_atTop.1 hthreshold.2) 1
      exact hOne.mono fun _ hj ↦ lt_of_lt_of_le Nat.zero_lt_one hj
    have hnPos : ∀ᶠ j in atTop, 0 < ns j := by
      have hOne : ∀ᶠ j in atTop, 1 ≤ ns j := (tendsto_atTop.1 hns.tendsto_atTop) 1
      exact hOne.mono fun _ hj ↦ lt_of_lt_of_le Nat.zero_lt_one hj
    filter_upwards [haaPos, hdPos, hhPos, hnPos] with j haj hdj hhj hnj
    rw [fixedDensityLeadingNormalization]
    have : Real.exp (-rate (degree M (ns j))) < 1 :=
      Real.exp_lt_one_iff.mpr (by linarith)
    have hdenpos : 0 < 1 - Real.exp (-rate (degree M (ns j))) := by linarith
    have hhreal : (0 : ℝ) < h j := by exact_mod_cast hhj
    have hnreal : (0 : ℝ) < ns j := by exact_mod_cast hnj
    have hrpowpos : 0 < (h j : ℝ) ^ (-(5 / 2) : ℝ) :=
      Real.rpow_pos_of_pos hhreal _
    positivity
  have hmul' : Tendsto
      (fun j ↦ treeLeadingTail (ns j) (M (ns j)) (h j) /
        fixedDensityLeadingNormalization M ns h j *
          fixedDensityLeadingNormalization M ns h j)
      atTop (nhds (latticeRate lam ell)) := by
    simpa [fixedDensityLeadingNormalization] using! hmul
  apply hmul'.congr'
  filter_upwards [hnormPos] with j hj
  exact div_mul_cancel₀ _ hj.ne'

end

end Erdos745.WrapUp.Proofs.W06_POISSON


namespace Erdos745.WrapUp.Proofs.W06_POISSON

noncomputable section

open Erdos745.WrapUp
open Filter
open scoped BigOperators Topology

def logCutoff (D : ℝ) (n : ℕ) : ℕ :=
  ⌈D * Real.log (n : ℝ)⌉₊

def factorialTupleSum (n M q h : ℕ) : ℝ :=
  by
    classical
    exact ∑ ks : Fin q → Fin (n + 1),
      if ∀ i, h ≤ (ks i).val then
        tupleMoment n M q (fun i ↦ (ks i).val)
      else 0

def outsideRectangleTupleSum (n M q h H : ℕ) : ℝ :=
  by
    classical
    exact ∑ ks : Fin q → Fin (n + 1),
      if (∀ i, h ≤ (ks i).val) ∧ (∃ i, H < (ks i).val) then
        tupleMoment n M q (fun i ↦ (ks i).val)
      else 0

lemma factorialMoment_treeCountGE_internal
    (hEnum : FiniteEnumerationStatement)
    (n M q h : ℕ) (hcap : M ≤ capacity n) (hh : 0 < h) :
    expectM n M (fun G ↦ (falling (treeCountGE G h) q : ℝ)) =
      factorialTupleSum n M q h := by
  rw [factorialTupleSum]
  rw [hEnum.2.2.2.2.2.2.1 n M q h hcap hh]
  apply Finset.sum_congr rfl
  intro ks _
  split
  · rw [hEnum.2.2.2.2.2.1 n M q (fun i ↦ (ks i).val) hcap]
  · rfl

lemma tupleMoment_nonneg (n M q : ℕ) (ks : Fin q → ℕ) :
    0 ≤ tupleMoment n M q ks := by
  rw [tupleMoment, expectM]
  exact div_nonneg (Finset.sum_nonneg fun _ _ ↦ by positivity) (by positivity)

lemma treeLeading_nonneg (n M k : ℕ) (hdegree : 0 < degreeAt n M) :
    0 ≤ treeLeading n M k := by
  rw [treeLeading]
  split_ifs
  · exact le_rfl
  · have hbase : 0 < degreeAt n M * Real.exp (-degreeAt n M) :=
      mul_pos hdegree (Real.exp_pos _)
    positivity

lemma treeLeadingTail_summable (n M h : ℕ)
    (hdegree : 0 < degreeAt n M) (hrate : 0 < rate (degreeAt n M)) :
    Summable (fun k : ℕ ↦ if h ≤ k ∧ 0 < k then treeLeading n M k else 0) := by
  let c : ℝ := (n : ℝ) / (degreeAt n M * Real.sqrt (2 * Real.pi))
  have hs := (weightedTreeTail_summable (rate (degreeAt n M)) h hrate).mul_left c
  apply hs.congr
  intro k
  by_cases hk : h ≤ k ∧ 0 < k
  · simp only [if_pos hk]
    rw [treeLeading_eq_cayleyKernel n M k hk.2 hdegree,
      cayleyKernel_eq_stirling k hk.2]
    dsimp [c]
    ring
  · simp [hk]

lemma treeLeadingTail_nonneg (n M h : ℕ) (hdegree : 0 < degreeAt n M)
    (hrate : 0 < rate (degreeAt n M)) :
    0 ≤ treeLeadingTail n M h := by
  rw [treeLeadingTail]
  exact tsum_nonneg
    (fun k ↦ by split_ifs <;> [exact treeLeading_nonneg n M k hdegree; exact le_rfl])

lemma treeLeadingTail_mono (n M h H : ℕ) (hhH : h ≤ H)
    (hdegree : 0 < degreeAt n M) (hrate : 0 < rate (degreeAt n M)) :
    treeLeadingTail n M H ≤ treeLeadingTail n M h := by
  rw [treeLeadingTail, treeLeadingTail]
  apply Summable.tsum_le_tsum
  · intro k
    by_cases hk : H ≤ k ∧ 0 < k
    · rw [if_pos hk, if_pos ⟨hhH.trans hk.1, hk.2⟩]
    · rw [if_neg hk]
      by_cases hh : h ≤ k ∧ 0 < k
      · rw [if_pos hh]
        exact treeLeading_nonneg n M k hdegree
      · rw [if_neg hh]
  · exact treeLeadingTail_summable n M H hdegree hrate
  · exact treeLeadingTail_summable n M h hdegree hrate

lemma truncatedTreeLeadingSum_eq_tail_sub
    (n M h H : ℕ) (hhH : h ≤ H) (hHn : H ≤ n)
    (hdegree : 0 < degreeAt n M) (hrate : 0 < rate (degreeAt n M)) :
    truncatedTreeLeadingSum n M h H =
      treeLeadingTail n M h - treeLeadingTail n M (H + 1) := by
  let f : ℕ → ℝ := fun k ↦ if h ≤ k ∧ 0 < k then treeLeading n M k else 0
  let g : ℕ → ℝ := fun k ↦ if H + 1 ≤ k ∧ 0 < k then treeLeading n M k else 0
  have hf : Summable f := treeLeadingTail_summable n M h hdegree hrate
  have hg : Summable g := treeLeadingTail_summable n M (H + 1) hdegree hrate
  have hsupp : Function.support (fun k ↦ f k - g k) ⊆
      (Finset.Icc h H : Set ℕ) := by
    intro k hk
    simp only [Function.mem_support] at hk
    simp only [Finset.coe_Icc, Set.mem_Icc]
    by_contra hnot
    push_neg at hnot
    by_cases hkh : h ≤ k
    · have hHk : H < k := hnot hkh
      have hkH : H + 1 ≤ k := by omega
      have hkpos : 0 < k := by omega
      have hfEq : f k = treeLeading n M k := by
        change (if h ≤ k ∧ 0 < k then treeLeading n M k else 0) = _
        rw [if_pos ⟨hkh, hkpos⟩]
      have hgEq : g k = treeLeading n M k := by
        change (if H + 1 ≤ k ∧ 0 < k then treeLeading n M k else 0) = _
        rw [if_pos ⟨hkH, hkpos⟩]
      exact hk (by rw [hfEq, hgEq, sub_self])
    · have hfEq : f k = 0 := by
        change (if h ≤ k ∧ 0 < k then treeLeading n M k else 0) = 0
        rw [if_neg]
        exact fun hx ↦ hkh hx.1
      have hnotH : ¬H + 1 ≤ k := by omega
      have hgEq : g k = 0 := by
        change (if H + 1 ≤ k ∧ 0 < k then treeLeading n M k else 0) = 0
        rw [if_neg]
        exact fun hx ↦ hnotH hx.1
      exact hk (by rw [hfEq, hgEq, sub_self])
  have hdiff : (∑' k : ℕ, (f k - g k)) =
      treeLeadingTail n M h - treeLeadingTail n M (H + 1) := by
    rw [hf.tsum_sub hg]
    rfl
  have hfinite : (∑' k : ℕ, (f k - g k)) =
      ∑ k ∈ Finset.Icc h H, treeLeading n M k := by
    rw [tsum_eq_sum' hsupp]
    apply Finset.sum_congr rfl
    intro k hk
    have hbounds := Finset.mem_Icc.1 hk
    have hnotUpper : ¬ H + 1 ≤ k := by omega
    by_cases hk0 : k = 0
    · subst k
      simp [f, g, treeLeading]
    · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
      have hfEq : f k = treeLeading n M k := by
        change (if h ≤ k ∧ 0 < k then treeLeading n M k else 0) = _
        rw [if_pos ⟨hbounds.1, hkpos⟩]
      have hgEq : g k = 0 := by
        change (if H + 1 ≤ k ∧ 0 < k then treeLeading n M k else 0) = 0
        rw [if_neg]
        exact fun hx ↦ hnotUpper hx.1
      rw [hfEq, hgEq, sub_zero]
  rw [← hdiff, hfinite]
  rw [truncatedTreeLeadingSum]
  have hfin := Fin.sum_univ_eq_sum_range
    (fun k ↦ if h ≤ k ∧ k ≤ H then treeLeading n M k else 0) (n + 1)
  rw [hfin]
  rw [← Finset.sum_filter]
  congr 1
  ext k
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
  omega

lemma logCutoff_tendsto_atTop
    (ns : NatSeq) (hns : Tendsto ns atTop atTop) (D : ℝ) (hD : 0 < D) :
    Tendsto (fun j ↦ logCutoff D (ns j)) atTop atTop := by
  have hcast : Tendsto (fun j ↦ (ns j : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hns
  have hlog : Tendsto (fun j ↦ Real.log (ns j : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp hcast
  have hmul : Tendsto (fun j ↦ D * Real.log (ns j : ℝ)) atTop atTop :=
    hlog.const_mul_atTop hD
  exact tendsto_nat_ceil_atTop.comp hmul

lemma logCutoff_le_vertices_eventually
    (ns : NatSeq) (hns : Tendsto ns atTop atTop) (D : ℝ) (hD : 0 < D) :
    ∀ᶠ j in atTop, logCutoff D (ns j) ≤ ns j := by
  let NN : RealSeq := fun j ↦ (ns j : ℝ)
  have hNN : Tendsto NN atTop atTop := tendsto_natCast_atTop_atTop.comp hns
  have hlogDiv : Tendsto (fun j ↦ Real.log (NN j) / NN j) atTop (nhds 0) := by
    have h := Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
    have hc := h.comp hNN
    simpa [NN] using! hc
  have honeDiv : Tendsto (fun j ↦ 1 / NN j) atTop (nhds 0) := by
    simpa [NN] using! (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).comp hns
  have hratio : Tendsto (fun j ↦ (D * Real.log (NN j) + 1) / NN j)
      atTop (nhds 0) := by
    have hscaled : Tendsto (fun j ↦ D * (Real.log (NN j) / NN j))
        atTop (nhds 0) := by simpa using! hlogDiv.const_mul D
    have hadd := hscaled.add honeDiv
    have hadd' : Tendsto
        (fun j ↦ D * (Real.log (NN j) / NN j) + 1 / NN j)
        atTop (nhds 0) := by simpa using! hadd
    apply hadd'.congr'
    filter_upwards with j
    ring
  have hlt : ∀ᶠ j in atTop, (D * Real.log (NN j) + 1) / NN j < 1 :=
    (tendsto_order.1 hratio).2 1 zero_lt_one
  have hNNpos : ∀ᶠ j in atTop, 0 < NN j := by
    have hOne : ∀ᶠ j in atTop, 1 ≤ ns j := (tendsto_atTop.1 hns) 1
    exact hOne.mono fun j hj ↦ by dsimp [NN]; exact_mod_cast (Nat.zero_lt_one.trans_le hj)
  have hlognonneg : ∀ᶠ j in atTop, 0 ≤ Real.log (NN j) := by
    have hOne : ∀ᶠ j in atTop, 1 ≤ NN j := (tendsto_atTop.1 hNN) 1
    exact hOne.mono fun j hj ↦ Real.log_nonneg hj
  filter_upwards [hlt, hNNpos, hlognonneg] with j hj hn hlog
  have hceil : (logCutoff D (ns j) : ℝ) < D * Real.log (NN j) + 1 := by
    exact Nat.ceil_lt_add_one (mul_nonneg hD.le hlog)
  have hbound : D * Real.log (NN j) + 1 < NN j := by
    exact (div_lt_one hn).1 hj
  have hcastLe : (logCutoff D (ns j) : ℝ) < (ns j : ℝ) := by
    simpa [NN] using! hceil.trans hbound
  exact Nat.le_of_lt (by exact_mod_cast hcastLe)

lemma fixedDensity_threshold_le_logCutoff_eventually
    (hRate : RateStatement) (M ns h : NatSeq) (lam ell D : ℝ)
    (hlam : 0 < lam) (hlam1 : lam ≠ 1)
    (hdegree : Tendsto (degree M) atTop (nhds lam))
    (hns : StrictMono ns)
    (hoffset : Tendsto (fun j ↦ (h j : ℝ) - center M (ns j)) atTop (nhds ell))
    (hD : 1 / rate lam < D) :
    ∀ᶠ j in atTop, h j ≤ logCutoff D (ns j) := by
  have hthreshold := fixedDensity_threshold_asymptotics hRate M ns h lam ell
    hlam hlam1 hdegree hns hoffset
  have hratio := hthreshold.1
  have hlt : ∀ᶠ j in atTop,
      (h j : ℝ) / Real.log (ns j : ℝ) < D :=
    (tendsto_order.1 hratio).2 D hD
  have hlogpos : ∀ᶠ j in atTop, 0 < Real.log (ns j : ℝ) := by
    have hlog : Tendsto (fun j ↦ Real.log (ns j : ℝ)) atTop atTop :=
      Real.tendsto_log_atTop.comp
        (tendsto_natCast_atTop_atTop.comp hns.tendsto_atTop)
    exact (tendsto_atTop.1 hlog) 1 |>.mono fun _ hj ↦ zero_lt_one.trans_le hj
  filter_upwards [hlt, hlogpos] with j hj hLj
  have hreal : (h j : ℝ) < D * Real.log (ns j : ℝ) := by
    rw [div_lt_iff₀ hLj] at hj
    simpa [mul_comm] using! hj
  have hceil := Nat.le_ceil (D * Real.log (ns j : ℝ))
  exact_mod_cast hreal.le.trans hceil

lemma logCutoff_treeLeadingTail_tendsto_zero
    (hRate : RateStatement) (M ns : NatSeq) (lam D : ℝ)
    (hlam : 0 < lam) (hlam1 : lam ≠ 1)
    (hdegree : Tendsto (degree M) atTop (nhds lam))
    (hns : StrictMono ns)
    (hD : 2 / rate lam < D) :
    Tendsto (fun j ↦ treeLeadingTail (ns j) (M (ns j))
      (logCutoff D (ns j))) atTop (nhds 0) := by
  let NN : RealSeq := fun j ↦ (ns j : ℝ)
  let dd : RealSeq := fun j ↦ degree M (ns j)
  let aa : RealSeq := fun j ↦ rate (dd j)
  let HH : NatSeq := fun j ↦ logCutoff D (ns j)
  have hnsTop : Tendsto ns atTop atTop := hns.tendsto_atTop
  have hNN : Tendsto NN atTop atTop := tendsto_natCast_atTop_atTop.comp hnsTop
  have hLL : Tendsto (fun j ↦ Real.log (NN j)) atTop atTop :=
    Real.tendsto_log_atTop.comp hNN
  have hdd : Tendsto dd atTop (nhds lam) := hdegree.comp hnsTop
  have haa : Tendsto aa atTop (nhds (rate lam)) := tendsto_rate_of_tendsto hlam hdd
  have ha : 0 < rate lam := hRate.1 lam hlam hlam1
  have hDpos : 0 < D := lt_trans (by positivity : 0 < 2 / rate lam) hD
  have hHH : Tendsto HH atTop atTop := logCutoff_tendsto_atTop ns hnsTop D hDpos
  have hHHcast : Tendsto (fun j ↦ (HH j : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hHH
  have haaLower : ∀ᶠ j in atTop, rate lam / 2 ≤ aa j := by
    exact ((tendsto_order.1 haa).1 (rate lam / 2) (by linarith)).mono
      fun _ hj ↦ hj.le
  have hNNpos : ∀ᶠ j in atTop, 0 < NN j := by
    have hOne : ∀ᶠ j in atTop, 1 ≤ ns j := (tendsto_atTop.1 hnsTop) 1
    exact hOne.mono fun j hj ↦ by dsimp [NN]; exact_mod_cast (Nat.zero_lt_one.trans_le hj)
  have hlogpos : ∀ᶠ j in atTop, 0 < Real.log (NN j) :=
    ((tendsto_atTop.1 hLL) 1).mono fun _ hj ↦ zero_lt_one.trans_le hj
  let c : ℝ := rate lam / 2 * D
  have hc : 1 < c := by
    dsimp [c]
    have := hD
    rw [div_lt_iff₀ ha] at this
    nlinarith
  have hupperArg : ∀ᶠ j in atTop,
      Real.log (NN j) - aa j * (HH j : ℝ) ≤
        (1 - c) * Real.log (NN j) := by
    filter_upwards [haaLower, hlogpos] with j haj hLj
    have hceil : D * Real.log (NN j) ≤ (HH j : ℝ) := by
      exact Nat.le_ceil (D * Real.log (NN j))
    have hprod : rate lam / 2 * (D * Real.log (NN j)) ≤
        aa j * (HH j : ℝ) := by
      exact mul_le_mul haj hceil (mul_nonneg hDpos.le hLj.le) (by linarith)
    dsimp [c]
    nlinarith
  have hupperZero : Tendsto (fun j ↦ Real.exp ((1 - c) * Real.log (NN j)))
      atTop (nhds 0) := by
    have hbot := hLL.const_mul_atTop_of_neg (by linarith : 1 - c < 0)
    exact Real.tendsto_exp_atBot.comp hbot
  have hNexp : Tendsto (fun j ↦ NN j * Real.exp (-aa j * (HH j : ℝ)))
      atTop (nhds 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupperZero
    · exact Filter.Eventually.of_forall fun j ↦ by positivity
    · filter_upwards [hupperArg, hNNpos] with j hj hn
      calc
        NN j * Real.exp (-aa j * (HH j : ℝ)) =
            Real.exp (Real.log (NN j) - aa j * (HH j : ℝ)) := by
              rw [sub_eq_add_neg, Real.exp_add, Real.exp_log hn]
              congr 2 <;> ring
        _ ≤ Real.exp ((1 - c) * Real.log (NN j)) := Real.exp_le_exp.mpr hj
  have hpow : Tendsto (fun j ↦ (HH j : ℝ) ^ (-(5 / 2) : ℝ)) atTop
      (nhds 0) := by
    exact (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 5 / 2)).comp hHHcast
  have hdenExp : Tendsto (fun j ↦ Real.exp (-aa j)) atTop
      (nhds (Real.exp (-rate lam))) :=
    Real.continuous_exp.continuousAt.tendsto.comp haa.neg
  have hden : Tendsto (fun j ↦ 1 - Real.exp (-aa j)) atTop
      (nhds (1 - Real.exp (-rate lam))) := tendsto_const_nhds.sub hdenExp
  have hdenNe : 1 - Real.exp (-rate lam) ≠ 0 := by
    have : Real.exp (-rate lam) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    linarith
  have hsqrtNe : Real.sqrt (2 * Real.pi) ≠ 0 := by positivity
  have hpref : Tendsto
      (fun j ↦ (1 / (dd j * Real.sqrt (2 * Real.pi))) *
        (HH j : ℝ) ^ (-(5 / 2) : ℝ) / (1 - Real.exp (-aa j)))
      atTop (nhds 0) := by
    have hsqrt : Tendsto (fun _ : ℕ ↦ Real.sqrt (2 * Real.pi)) atTop
        (nhds (Real.sqrt (2 * Real.pi))) := tendsto_const_nhds
    have hone : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (nhds 1) :=
      tendsto_const_nhds
    have hleft := (hone.div (hdd.mul hsqrt)
      (mul_ne_zero hlam.ne' hsqrtNe)).mul hpow
    simpa using! hleft.div hden hdenNe
  have hnorm : Tendsto (fixedDensityLeadingNormalization M ns HH) atTop
      (nhds 0) := by
    have hmul := hpref.mul hNexp
    have hmul' := hmul
    simp only [mul_zero] at hmul'
    apply hmul'.congr'
    filter_upwards with j
    dsimp [fixedDensityLeadingNormalization, HH, NN, dd, aa]
    ring
  have hratio := treeLeadingTail_varying_positive_rate hRate M ns HH lam
    hlam hlam1 hdegree hns hHH
  have hmul := hratio.mul hnorm
  have hmul' := hmul
  simp only [one_mul] at hmul'
  apply hmul'.congr'
  have hnormPos : ∀ᶠ j in atTop, 0 < fixedDensityLeadingNormalization M ns HH j := by
    have hgood := eventually_pos_ne_one_of_tendsto hlam hlam1 hdd
    have haaPos : ∀ᶠ j in atTop, 0 < aa j :=
      ((tendsto_order.1 haa).1 0 ha).mono fun _ hj ↦ hj
    have hHpos : ∀ᶠ j in atTop, 0 < HH j := by
      have hOne : ∀ᶠ j in atTop, 1 ≤ HH j := (tendsto_atTop.1 hHH) 1
      exact hOne.mono fun _ hj ↦ Nat.zero_lt_one.trans_le hj
    filter_upwards [hgood, haaPos, hHpos, hNNpos] with j hd haj hHj hNj
    rw [fixedDensityLeadingNormalization]
    have hdenpos : 0 < 1 - Real.exp (-aa j) := by
      have : Real.exp (-aa j) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
      linarith
    have hHreal : (0 : ℝ) < HH j := by exact_mod_cast hHj
    dsimp [NN, dd, aa] at *
    exact mul_pos
      (div_pos hNj (mul_pos hd.1 (by positivity)))
      (div_pos (mul_pos (Real.rpow_pos_of_pos hHreal _) (Real.exp_pos _)) hdenpos)
  filter_upwards [hnormPos] with j hj
  exact div_mul_cancel₀ _ hj.ne'

lemma factorialTupleSum_eq_rectangle_add_outside
    (n M q h H : ℕ) (hhH : h ≤ H) :
    factorialTupleSum n M q h =
      rectangleTupleSum n M q h H + outsideRectangleTupleSum n M q h H := by
  classical
  rw [factorialTupleSum, rectangleTupleSum, outsideRectangleTupleSum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ks _
  by_cases hlow : ∀ i, h ≤ (ks i).val
  · by_cases hhigh : ∀ i, (ks i).val ≤ H
    · have hrect : inRectangle h H ks := fun i ↦ ⟨hlow i, hhigh i⟩
      have hout : ¬∃ i, H < (ks i).val := by push_neg; exact hhigh
      simp [hlow, hrect, hout]
    · push_neg at hhigh
      obtain ⟨i, hi⟩ := hhigh
      have hrect : ¬inRectangle h H ks := by
        intro hr
        exact (not_le_of_gt hi) (hr i).2
      rw [if_pos hlow, if_neg hrect, if_pos ⟨hlow, ⟨i, hi⟩⟩, zero_add]
  · have hrect : ¬inRectangle h H ks := by
      intro hr
      exact hlow fun i ↦ (hr i).1
    simp [hlow, hrect]

lemma outsideRectangleTupleSum_nonneg (n M q h H : ℕ) :
    0 ≤ outsideRectangleTupleSum n M q h H := by
  classical
  rw [outsideRectangleTupleSum]
  exact Finset.sum_nonneg fun ks _ ↦ by
    split_ifs
    · exact tupleMoment_nonneg n M q (fun i ↦ (ks i).val)
    · exact le_rfl

lemma outsideRectangleTupleSum_le_tupleTail
    (n M q h H : ℕ) (B D : ℝ)
    (hh : 0 < h) (hBD : B ≤ D) (hlog : 0 ≤ Real.log (n : ℝ))
    (hH : logCutoff D n = H) :
    outsideRectangleTupleSum n M q h H ≤ tupleTail n M q 0 B := by
  classical
  rw [outsideRectangleTupleSum, tupleTail]
  apply Finset.sum_le_sum
  intro ks _
  by_cases hout : (∀ i, h ≤ (ks i).val) ∧ (∃ i, H < (ks i).val)
  · obtain ⟨i, hi⟩ := hout.2
    have hpos : ∀ i, 0 < (ks i).val := fun i ↦ lt_of_lt_of_le hh (hout.1 i)
    have hex : ∃ i, B * Real.log n < ((ks i).val : ℝ) := by
      refine ⟨i, ?_⟩
      have hBDlog : B * Real.log (n : ℝ) ≤ D * Real.log (n : ℝ) :=
        mul_le_mul_of_nonneg_right hBD hlog
      have hceil : D * Real.log (n : ℝ) ≤ (H : ℝ) := by
        rw [← hH]
        exact Nat.le_ceil (D * Real.log (n : ℝ))
      exact lt_of_le_of_lt (hBDlog.trans hceil) (by exact_mod_cast hi)
    simp [hout, hpos, hex]
  · rw [if_neg hout]
    split_ifs
    · exact mul_nonneg (Finset.prod_nonneg fun _ _ ↦ by positivity)
        (tupleMoment_nonneg n M q (fun i ↦ (ks i).val))
    · exact le_rfl

lemma truncatedTreeLeadingSum_fixedDensity_tendsto
    (hRate : RateStatement) (M ns h : NatSeq) (lam ell D : ℝ)
    (hlam : 0 < lam) (hlam1 : lam ≠ 1)
    (hdegree : Tendsto (degree M) atTop (nhds lam))
    (hns : StrictMono ns)
    (hoffset : Tendsto (fun j ↦ (h j : ℝ) - center M (ns j)) atTop (nhds ell))
    (hD : 2 / rate lam < D) :
    Tendsto (fun j ↦ truncatedTreeLeadingSum (ns j) (M (ns j)) (h j)
      (logCutoff D (ns j))) atTop (nhds (latticeRate lam ell)) := by
  have ha : 0 < rate lam := hRate.1 lam hlam hlam1
  have hDpos : 0 < D := lt_trans (by positivity : 0 < 2 / rate lam) hD
  have hDcenter : 1 / rate lam < D := by
    have : 1 / rate lam < 2 / rate lam :=
      (div_lt_div_iff_of_pos_right ha).2 (by norm_num)
    exact this.trans hD
  have hnsTop := hns.tendsto_atTop
  have hleH := fixedDensity_threshold_le_logCutoff_eventually hRate M ns h lam ell D
    hlam hlam1 hdegree hns hoffset hDcenter
  have hHleN := logCutoff_le_vertices_eventually ns hnsTop D hDpos
  have hdd : Tendsto (fun j ↦ degree M (ns j)) atTop (nhds lam) :=
    hdegree.comp hnsTop
  have hgood := eventually_pos_ne_one_of_tendsto hlam hlam1 hdd
  have hratePos : ∀ᶠ j in atTop, 0 < rate (degree M (ns j)) :=
    hgood.mono fun j hj ↦ hRate.1 _ hj.1 hj.2
  have hfull := fixedDensity_treeLeadingTail_tendsto hRate M ns h lam ell
    hlam hlam1 hdegree hns hoffset
  have hcut := logCutoff_treeLeadingTail_tendsto_zero hRate M ns lam D
    hlam hlam1 hdegree hns hD
  have hcutSucc : Tendsto (fun j ↦ treeLeadingTail (ns j) (M (ns j))
      (logCutoff D (ns j) + 1)) atTop (nhds 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hcut
    · filter_upwards [hgood, hratePos] with j hdj haj
      exact treeLeadingTail_nonneg _ _ _ hdj.1 haj
    · filter_upwards [hgood, hratePos] with j hdj haj
      exact treeLeadingTail_mono _ _ _ _ (Nat.le_add_right _ _) hdj.1 haj
  have hsub := hfull.sub hcutSucc
  have hsub' := hsub
  simp only [sub_zero] at hsub'
  apply hsub'.congr'
  filter_upwards [hleH, hHleN, hgood, hratePos] with j hhj hHj hdj haj
  exact (truncatedTreeLeadingSum_eq_tail_sub _ _ _ _ hhj hHj hdj.1 haj).symm

lemma latticeRate_pos (hRate : RateStatement) (lam ell : ℝ)
    (hlam : 0 < lam) (hlam1 : lam ≠ 1) :
    0 < latticeRate lam ell := by
  have ha : 0 < rate lam := hRate.1 lam hlam hlam1
  have hden : 0 < 1 - Real.exp (-rate lam) := by
    have : Real.exp (-rate lam) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    linarith
  rw [latticeRate]
  exact div_pos
    (mul_pos (Real.rpow_pos_of_pos ha _) (Real.exp_pos _))
    (mul_pos (mul_pos hlam (by positivity)) hden)

lemma fixedDensity_factorialMoments
    (hEnum : FiniteEnumerationStatement) (hRate : RateStatement)
    (hTuple : TupleEstimatesStatement)
    (M ns h : NatSeq) (lam ell : ℝ)
    (hM : admissible M) (hlam : 0 < lam) (hlam1 : lam ≠ 1)
    (hdegree : Tendsto (degree M) atTop (nhds lam))
    (hns : StrictMono ns)
    (hoffset : Tendsto (fun j ↦ (h j : ℝ) - center M (ns j)) atTop (nhds ell)) :
    ∀ q : ℕ, 0 < q → Tendsto
      (fun j ↦ expectM (ns j) (M (ns j))
        (fun G ↦ (falling (treeCountGE G (h j)) q : ℝ)))
      atTop (nhds ((latticeRate lam ell) ^ q)) := by
  intro q hq
  let lo : ℝ := lam / 2
  let hi : ℝ := lam + 1
  let delta : ℝ := |lam - 1| / 2
  have hlo : 0 < lo := by dsimp [lo]; positivity
  have hlohi : lo ≤ hi := by dsimp [lo, hi]; linarith
  have hdelta : 0 < delta := by
    dsimp [delta]
    exact div_pos (abs_pos.mpr (sub_ne_zero.mpr hlam1)) (by norm_num)
  obtain ⟨Btail, hBtail, nTail, hTail⟩ :=
    hTuple.2.2.2 lo hi delta 1 q 0 hlo hlohi hdelta zero_lt_one hq
  have ha : 0 < rate lam := hRate.1 lam hlam hlam1
  let D : ℝ := max Btail (4 / rate lam)
  have hDB : Btail ≤ D := le_max_left _ _
  have hDfour : 4 / rate lam ≤ D := le_max_right _ _
  have hD : 2 / rate lam < D := by
    have : 2 / rate lam < 4 / rate lam :=
      (div_lt_div_iff_of_pos_right ha).2 (by norm_num)
    exact this.trans_le hDfour
  have hDpos : 0 < D := lt_of_lt_of_le (by positivity : 0 < 4 / rate lam) hDfour
  let Blocal : ℝ := (q : ℝ) * (D + 1)
  have hBlocal : 0 < Blocal := by
    dsimp [Blocal]
    positivity
  obtain ⟨Clocal, hClocal, nLocal, hLocal⟩ :=
    hTuple.2.2.1 lo hi Blocal q hlo hlohi hBlocal hq
  let eta : NatSeq → ℝ := fun _ ↦ 0
  let err : RealSeq := fun j ↦
    Clocal * (Blocal * Real.log (ns j : ℝ)) ^ 2 / (ns j : ℝ)
  have hnsTop : Tendsto ns atTop atTop := hns.tendsto_atTop
  have hNN : Tendsto (fun j ↦ (ns j : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hnsTop
  have herr : Tendsto err atTop (nhds 0) := by
    have hbase := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero).comp hNN
    have hbase' : Tendsto (fun j ↦ Real.log (ns j : ℝ) ^ 2 / (ns j : ℝ))
        atTop (nhds 0) := by simpa using! hbase
    have hscaled : Tendsto
      (fun j ↦ (Clocal * Blocal ^ 2) *
        (Real.log (ns j : ℝ) ^ 2 / (ns j : ℝ))) atTop (nhds 0) := by
      simpa using! hbase'.const_mul (Clocal * Blocal ^ 2)
    apply hscaled.congr'
    filter_upwards with j
    dsimp [err]
    ring
  have hdegreeSub : Tendsto (fun j ↦ degree M (ns j)) atTop (nhds lam) :=
    hdegree.comp hnsTop
  have hdegreeLo : ∀ᶠ j in atTop, lo ≤ degree M (ns j) := by
    exact ((tendsto_order.1 hdegreeSub).1 lo (by dsimp [lo]; linarith)).mono
      fun _ hj ↦ hj.le
  have hdegreeHi : ∀ᶠ j in atTop, degree M (ns j) ≤ hi := by
    exact ((tendsto_order.1 hdegreeSub).2 hi (by dsimp [hi]; linarith)).mono
      fun _ hj ↦ hj.le
  have habs : Tendsto (fun j ↦ |degree M (ns j) - 1|) atTop
      (nhds |lam - 1|) := hdegreeSub.sub_const 1 |>.abs
  have hdegreeDelta : ∀ᶠ j in atTop, delta ≤ |degree M (ns j) - 1| := by
    exact ((tendsto_order.1 habs).1 delta (by
      dsimp [delta]
      have hp : 0 < |lam - 1| := abs_pos.mpr (sub_ne_zero.mpr hlam1)
      linarith)).mono fun _ hj ↦ hj.le
  have hcap : ∀ᶠ j in atTop, M (ns j) ≤ capacity (ns j) := hnsTop.eventually hM
  have hnTail : ∀ᶠ j in atTop, nTail ≤ ns j := (tendsto_atTop.1 hnsTop) nTail
  have hnLocal : ∀ᶠ j in atTop, nLocal ≤ ns j := (tendsto_atTop.1 hnsTop) nLocal
  have hlogOne : ∀ᶠ j in atTop, 1 ≤ Real.log (ns j : ℝ) := by
    have hlog := Real.tendsto_log_atTop.comp hNN
    exact (tendsto_atTop.1 hlog) 1
  have hhTop := (fixedDensity_threshold_asymptotics hRate M ns h lam ell
    hlam hlam1 hdegree hns hoffset).2
  have hhpos : ∀ᶠ j in atTop, 0 < h j := by
    have hOne := (tendsto_atTop.1 hhTop) 1
    exact hOne.mono fun _ hj ↦ Nat.zero_lt_one.trans_le hj
  have hHleN := logCutoff_le_vertices_eventually ns hnsTop D hDpos
  have hhH := fixedDensity_threshold_le_logCutoff_eventually hRate M ns h lam ell D
    hlam hlam1 hdegree hns hoffset (by
      have : 1 / rate lam < 2 / rate lam :=
        (div_lt_div_iff_of_pos_right ha).2 (by norm_num)
      exact this.trans hD)
  have htrunc := truncatedTreeLeadingSum_fixedDensity_tendsto hRate M ns h
    lam ell D hlam hlam1 hdegree hns hoffset hD
  have hrectLeading : Tendsto
      (fun j ↦ rectangleLeadingSum (ns j) (M (ns j)) q (h j)
        (logCutoff D (ns j))) atTop (nhds ((latticeRate lam ell) ^ q)) := by
    have hp := htrunc.pow q
    apply hp.congr'
    filter_upwards with j
    exact (rectangleLeadingSum_eq_pow _ _ _ _ _).symm
  have hrect : Tendsto
      (fun j ↦ rectangleTupleSum (ns j) (M (ns j)) q (h j)
        (logCutoff D (ns j))) atTop (nhds ((latticeRate lam ell) ^ q)) := by
    have hlower' := (Real.continuous_exp.continuousAt.tendsto.comp herr.neg).mul hrectLeading
    have hupper' := (Real.continuous_exp.continuousAt.tendsto.comp herr).mul hrectLeading
    have hlower : Tendsto
        (fun j ↦ Real.exp (-err j) * rectangleLeadingSum (ns j) (M (ns j)) q
          (h j) (logCutoff D (ns j))) atTop (nhds ((latticeRate lam ell) ^ q)) := by
      simpa using! hlower'
    have hupper : Tendsto
        (fun j ↦ Real.exp (err j) * rectangleLeadingSum (ns j) (M (ns j)) q
          (h j) (logCutoff D (ns j))) atTop (nhds ((latticeRate lam ell) ^ q)) := by
      simpa using! hupper'
    have hgoodDegree := eventually_pos_ne_one_of_tendsto hlam hlam1 hdegreeSub
    have hsandwich : ∀ᶠ j in atTop,
        Real.exp (-err j) * rectangleLeadingSum (ns j) (M (ns j)) q (h j)
            (logCutoff D (ns j)) ≤
          rectangleTupleSum (ns j) (M (ns j)) q (h j) (logCutoff D (ns j)) ∧
        rectangleTupleSum (ns j) (M (ns j)) q (h j) (logCutoff D (ns j)) ≤
          Real.exp (err j) * rectangleLeadingSum (ns j) (M (ns j)) q (h j)
            (logCutoff D (ns j)) := by
      filter_upwards [hnLocal, hcap, hdegreeLo, hdegreeHi, hlogOne, hhpos, hHleN,
        hgoodDegree] with j hn hc hlo' hhi' hlog hh hHN hdgood
      have hnpos : 0 < ns j := by
        have hlogpos : 0 < Real.log (ns j : ℝ) := zero_lt_one.trans_le hlog
        have hnreal : (1 : ℝ) < ns j :=
          (Real.log_pos_iff (by positivity : (0 : ℝ) ≤ ns j)).1 hlogpos
        exact_mod_cast (zero_lt_one.trans hnreal)
      have hdegpos : 0 < degreeAt (ns j) (M (ns j)) := by
        change 0 < degree M (ns j)
        exact hdgood.1
      apply rectangleTupleSum_sandwich _ _ _ _ _ (err j) hnpos hdegpos hh
      intro ks hks
      have hcoordPos : ∀ i, 0 < (ks i).val :=
        fun i ↦ lt_of_lt_of_le hh (hks i).1
      have hHcast : (logCutoff D (ns j) : ℝ) <
          D * Real.log (ns j : ℝ) + 1 := by
        exact Nat.ceil_lt_add_one (mul_nonneg hDpos.le (zero_le_one.trans hlog))
      have hHbound : (logCutoff D (ns j) : ℝ) ≤
          (D + 1) * Real.log (ns j : ℝ) := by
        linarith
      have hsum : (∑ i, ((ks i).val : ℝ)) ≤
          Blocal * Real.log (ns j : ℝ) := by
        calc
          (∑ i, ((ks i).val : ℝ)) ≤ ∑ _i : Fin q, (logCutoff D (ns j) : ℝ) :=
            Finset.sum_le_sum fun i _ ↦ by exact_mod_cast (hks i).2
          _ = (q : ℝ) * (logCutoff D (ns j) : ℝ) := by simp
          _ ≤ (q : ℝ) * ((D + 1) * Real.log (ns j : ℝ)) :=
            mul_le_mul_of_nonneg_left hHbound (by positivity)
          _ = Blocal * Real.log (ns j : ℝ) := by dsimp [Blocal]; ring
      have hloc := hLocal (ns j) (M (ns j)) (fun i ↦ (ks i).val)
        hn hc hlo' hhi' hcoordPos hsum
      refine ⟨hloc.1, hloc.2.trans ?_⟩
      have hsumNonneg : 0 ≤ ∑ i, ((ks i).val : ℝ) := by positivity
      have hBLogNonneg : 0 ≤ Blocal * Real.log (ns j : ℝ) := by positivity
      have hsquare := (sq_le_sq₀ hsumNonneg hBLogNonneg).2 hsum
      have hdiv := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hsquare hClocal.le) (by positivity : 0 ≤ (ns j : ℝ))
      simpa [err] using! hdiv
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper
      (hsandwich.mono fun _ hj ↦ hj.1) (hsandwich.mono fun _ hj ↦ hj.2)
  have houtUpper : Tendsto (fun j ↦ Real.rpow (ns j : ℝ) (-1)) atTop (nhds 0) := by
    exact (tendsto_rpow_neg_atTop zero_lt_one).comp hNN
  have hout : Tendsto
      (fun j ↦ outsideRectangleTupleSum (ns j) (M (ns j)) q (h j)
        (logCutoff D (ns j))) atTop (nhds 0) := by
    have hbounds : ∀ᶠ j in atTop,
        0 ≤ outsideRectangleTupleSum (ns j) (M (ns j)) q (h j)
            (logCutoff D (ns j)) ∧
        outsideRectangleTupleSum (ns j) (M (ns j)) q (h j)
            (logCutoff D (ns j)) ≤ Real.rpow (ns j : ℝ) (-1) := by
      filter_upwards [hnTail, hcap, hdegreeLo, hdegreeHi, hdegreeDelta, hlogOne,
        hhpos] with j hn hc hlo' hhi' hdelta' hlog hh
      refine ⟨outsideRectangleTupleSum_nonneg _ _ _ _ _, ?_⟩
      exact (outsideRectangleTupleSum_le_tupleTail (ns j) (M (ns j)) q (h j)
        (logCutoff D (ns j)) Btail D hh hDB (zero_le_one.trans hlog) rfl).trans
          (hTail (ns j) (M (ns j)) hn hc hlo' hhi' hdelta')
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds houtUpper
      (hbounds.mono fun _ hj ↦ hj.1) (hbounds.mono fun _ hj ↦ hj.2)
  have htotal : Tendsto (fun j ↦ factorialTupleSum (ns j) (M (ns j)) q (h j))
      atTop (nhds ((latticeRate lam ell) ^ q)) := by
    have hadd' := hrect.add hout
    have hadd : Tendsto
        (fun j ↦ rectangleTupleSum (ns j) (M (ns j)) q (h j)
          (logCutoff D (ns j)) + outsideRectangleTupleSum (ns j) (M (ns j)) q
            (h j) (logCutoff D (ns j)))
        atTop (nhds ((latticeRate lam ell) ^ q)) := by simpa using! hadd'
    apply hadd.congr'
    filter_upwards [hhH] with j hj
    exact (factorialTupleSum_eq_rectangle_add_outside _ _ _ _ _ hj).symm
  apply htotal.congr'
  filter_upwards [hcap, hhpos] with j hc hh
  exact (factorialMoment_treeCountGE_internal hEnum (ns j) (M (ns j)) q (h j) hc hh).symm

end

end Erdos745.WrapUp.Proofs.W06_POISSON
