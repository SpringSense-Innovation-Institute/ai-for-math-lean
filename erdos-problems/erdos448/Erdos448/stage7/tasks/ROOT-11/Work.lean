module

import all Mathlib.Basic.Real.Basic
public import Erdos448.stage6.TaskContracts
public import Mathlib.Analysis.SumIntegralComparisons
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.Normed.Group.Tannery

public section

set_option backward.isDefEq.respectTransparency false

namespace Erdos448.Stage7.ROOT11.Work

open Filter Finset
open scoped BigOperators Topology

open Erdos448.Stage4
open Erdos448.Stage4.Contracts
open Erdos448.Stage6.TaskContracts

noncomputable section

theorem p096 : P096Statement := by
  intro y epsilonInt hy0 hy1 he0 heUpper
  have hlog : Real.log y < 0 := Real.log_neg hy0 hy1
  constructor
  · have hhalf : 0 < (1 / 2 : ℝ) + epsilonInt := by positivity
    exact mul_pos_of_neg_of_neg (neg_lt_zero.mpr hhalf) hlog
  · have hmul := (mul_lt_mul_of_neg_right heUpper hlog)
    have hlog_ne : Real.log y ≠ 0 := ne_of_lt hlog
    have hcancel :
        (-(1 - y + (1 / 2) * Real.log y) / Real.log y) * Real.log y =
          -(1 - y + (1 / 2) * Real.log y) := by
      field_simp [hlog_ne]
    rw [hcancel] at hmul
    nlinarith

lemma rpow_tail_bound (a : ℝ) (ha : a < -1) (K : ℕ) (hK : 1 ≤ K) :
    (∑' k : ℕ, if K ≤ k then (k : ℝ).rpow a else 0) ≤
      (1 + 1 / (-a - 1)) * (K : ℝ).rpow (a + 1) := by
  apply Real.tsum_le_of_sum_le
  · intro k
    change 0 ≤ if K ≤ k then (k : ℝ).rpow a else 0
    split_ifs
    · exact Real.rpow_nonneg (Nat.cast_nonneg k) _
    · exact le_rfl
  · intro u
    let M := (insert K u).max' ⟨K, mem_insert_self K u⟩
    have hKM : K ≤ M :=
      Finset.le_max' (insert K u) K (mem_insert_self K u)
    have hMpos : 0 < M := lt_of_lt_of_le (Nat.zero_lt_succ 0) (hK.trans hKM)
    have hfiltered :
        ∑ k ∈ u, (if K ≤ k then (k : ℝ).rpow a else 0) =
          ∑ k ∈ u.filter (K ≤ ·), (k : ℝ).rpow a := by
      rw [Finset.sum_filter]
    rw [hfiltered]
    have hsubset : u.filter (K ≤ ·) ⊆ Icc K M := by
      intro k hk
      have hku : k ∈ u := (mem_filter.mp hk).1
      exact mem_Icc.mpr ⟨(mem_filter.mp hk).2,
        Finset.le_max' (insert K u) k (mem_insert_of_mem hku)⟩
    calc
      ∑ k ∈ u.filter (K ≤ ·), (k : ℝ).rpow a ≤
          ∑ k ∈ Icc K M, (k : ℝ).rpow a := by
        exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
          (fun k _ _ => Real.rpow_nonneg (Nat.cast_nonneg k) _)
      _ = (K : ℝ).rpow a + ∑ k ∈ Ioc K M, (k : ℝ).rpow a := by
        have hset : Icc K M = insert K (Ioc K M) := by
          ext k
          simp only [mem_Icc, mem_insert, mem_Ioc]
          omega
        rw [hset, sum_insert]
        simp
      _ ≤ (K : ℝ).rpow a + ∫ x in (K : ℝ)..(M : ℝ), x.rpow a := by
        have hshift :
            ∑ k ∈ Ioc K M, (k : ℝ).rpow a =
              ∑ i ∈ Ico K M, ((i + 1 : ℕ) : ℝ).rpow a := by
          have hset : Ioc K M = (Ico K M).image (fun i => i + 1) := by
            ext k
            simp only [mem_Ioc, mem_image, mem_Ico]
            constructor
            · intro hk
              refine ⟨k - 1, ⟨?_, ?_⟩, ?_⟩
              · omega
              · omega
              · omega
            · rintro ⟨i, hi, rfl⟩
              omega
          rw [hset, sum_image]
          intro i _ j _ hij
          exact Nat.add_right_cancel hij
        have hcomp : ∑ k ∈ Ioc K M, (k : ℝ).rpow a ≤
            ∫ x in (K : ℝ)..(M : ℝ), x.rpow a := by
          rw [hshift]
          have hanti : AntitoneOn (fun x : ℝ => x.rpow a)
              (Set.Icc (K : ℝ) (M : ℝ)) :=
            (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (by linarith)).mono
            (fun x hx => by
              have : (0 : ℝ) < K := by exact_mod_cast (lt_of_lt_of_le (by omega) hK)
              exact Set.mem_Ioi.mpr (this.trans_le hx.1))
          exact hanti.sum_le_integral_Ico hKM
        simpa [add_comm] using add_le_add_right hcomp ((K : ℝ).rpow a)
      _ ≤ (K : ℝ).rpow a + ∫ x in Set.Ioi (K : ℝ), x.rpow a := by
        have hKpos : (0 : ℝ) < K := by exact_mod_cast (lt_of_lt_of_le (by omega) hK)
        have hMint : (0 : ℝ) < M := by exact_mod_cast hMpos
        have hIK := integrableOn_Ioi_rpow_of_lt ha hKpos
        have hIM := integrableOn_Ioi_rpow_of_lt ha hMint
        have hadd := intervalIntegral.integral_interval_add_Ioi hIK hIM
        have htail : 0 ≤ ∫ x in Set.Ioi (M : ℝ), x ^ a := by
          apply MeasureTheory.setIntegral_nonneg measurableSet_Ioi
          intro x hx
          exact Real.rpow_nonneg (le_of_lt (hMint.trans hx)) _
        have hcomp : ∫ x in (K : ℝ)..(M : ℝ), x ^ a ≤
            ∫ x in Set.Ioi (K : ℝ), x ^ a := by
          calc
            ∫ x in (K : ℝ)..(M : ℝ), x ^ a ≤
                (∫ x in (K : ℝ)..(M : ℝ), x ^ a) +
                  ∫ x in Set.Ioi (M : ℝ), x ^ a := le_add_of_nonneg_right htail
            _ = _ := hadd
        simpa [add_comm] using add_le_add_right hcomp ((K : ℝ).rpow a)
      _ = (K : ℝ).rpow a - (K : ℝ).rpow (a + 1) / (a + 1) := by
        change (K : ℝ).rpow a + ∫ x in Set.Ioi (K : ℝ), x ^ a = _
        rw [integral_Ioi_rpow_of_lt ha (by exact_mod_cast (lt_of_lt_of_le (by omega) hK))]
        simp only [sub_eq_add_neg, div_eq_mul_inv]
        congr 1
        exact neg_mul _ _
      _ ≤ (1 + 1 / (-a - 1)) * (K : ℝ).rpow (a + 1) := by
        have hden : 0 < -a - 1 := by linarith
        have ha1 : a + 1 ≠ 0 := by linarith
        have hpow : (K : ℝ).rpow a ≤ (K : ℝ).rpow (a + 1) :=
          Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hK) (by linarith)
        have hfrac :
            -(K : ℝ).rpow (a + 1) / (a + 1) =
              (K : ℝ).rpow (a + 1) / (-a - 1) := by
          field_simp [ne_of_gt hden, ha1]
          norm_num
          ring
        calc
          (K : ℝ).rpow a - (K : ℝ).rpow (a + 1) / (a + 1) =
              (K : ℝ).rpow a + (K : ℝ).rpow (a + 1) / (-a - 1) := by
            rw [← hfrac]
            ring
          _ ≤
              (K : ℝ).rpow (a + 1) +
                (K : ℝ).rpow (a + 1) / (-a - 1) :=
            by simpa [add_comm] using
              add_le_add_right hpow ((K : ℝ).rpow (a + 1) / (-a - 1))
          _ = (1 + 1 / (-a - 1)) * (K : ℝ).rpow (a + 1) := by ring

theorem p097 : P097Statement := by
  intro y aPow hy0 hy1 ha0 haUpper K0 hK0
  have hexp : y - 2 + aPow < -1 := by linarith
  constructor
  · have htail := rpow_tail_bound (y - 2 + aPow) hexp K0 hK0
    have hden : -(y - 2 + aPow) - 1 = 1 - y - aPow := by ring
    have hpower : y - 2 + aPow + 1 = y - 1 + aPow := by ring
    rw [hden, hpower] at htail
    simpa [one_div, mul_comm, add_comm] using htail
  · intro sigma theta htheta hsigma hK
    subst K0
    have hlogTheta : 0 < Real.log theta := Real.log_pos (by linarith)
    have hlogSigma : 0 < Real.log sigma := Real.log_pos (by linarith)
    have hlogs : Real.log theta ≤ Real.log sigma :=
      Real.log_le_log (by linarith) hsigma
    have hratio : 1 ≤ Real.log sigma / Real.log theta := by
      rw [le_div_iff₀ hlogTheta]
      simpa using hlogs
    constructor
    · unfold lowerBinIndex
      have hceil : (1 / 2 : ℝ) * Real.log sigma / Real.log theta ≤
          (Nat.ceil ((1 / 2 : ℝ) * Real.log sigma / Real.log theta) : ℝ) :=
        Nat.le_ceil _
      have hmax :
          (Nat.ceil ((1 / 2 : ℝ) * Real.log sigma / Real.log theta) : ℝ) ≤
            (max 1 (Nat.ceil ((1 / 2 : ℝ) * Real.log sigma / Real.log theta)) : ℕ) := by
        exact_mod_cast le_max_right 1
          (Nat.ceil ((1 / 2 : ℝ) * Real.log sigma / Real.log theta))
      calc
        (1 / 2 : ℝ) * (Real.log sigma / Real.log theta) =
            (1 / 2 : ℝ) * Real.log sigma / Real.log theta := by ring
        _ ≤ _ := hceil.trans hmax
    · unfold lowerBinIndex
      have hceil : (Nat.ceil ((1 / 2 : ℝ) * Real.log sigma / Real.log theta) : ℝ) <
          (1 / 2 : ℝ) * Real.log sigma / Real.log theta + 1 := by
        apply Nat.ceil_lt_add_one
        positivity
      push_cast
      apply max_le
      · linarith
      · have hceil' :
            (Nat.ceil ((1 / 2 : ℝ) * Real.log sigma / Real.log theta) : ℝ) <
              (1 / 2 : ℝ) * (Real.log sigma / Real.log theta) + 1 := by
            convert hceil using 1 <;> ring
        linarith

@[expose] def movingLeft (K : ℕ) (r s : ℝ) (N k : ℕ) : ℝ :=
  if K ≤ k ∧ k ≤ N ∧ k ≤ N - k + 1 then
    (k : ℝ).rpow r * ((N - k + 1 : ℕ) : ℝ).rpow s
  else 0

@[expose] def movingRight (K : ℕ) (r s : ℝ) (N j : ℕ) : ℝ :=
  let k := N - j + 1
  if 1 ≤ j ∧ K ≤ k ∧ k ≤ N ∧ j < k then
    (k : ℝ).rpow r * (j : ℝ).rpow s
  else 0

lemma movingPowerSum_eq_tsum_split (K N : ℕ) (r s : ℝ) :
    movingPowerSum K N r s =
      (∑' k : ℕ, movingLeft K r s N k) +
        ∑' j : ℕ, movingRight K r s N j := by
  classical
  have hleft :
      (∑' k : ℕ, movingLeft K r s N k) =
        ∑ k ∈ Icc K N, if k ≤ N - k + 1 then
          (k : ℝ).rpow r * ((N - k + 1 : ℕ) : ℝ).rpow s else 0 := by
    rw [tsum_eq_sum (s := Icc K N)]
    · apply Finset.sum_congr rfl
      intro k hk
      simp [movingLeft, (mem_Icc.mp hk).1, (mem_Icc.mp hk).2]
    · intro k hk
      simp only [movingLeft]
      split_ifs with h
      · exact (hk (mem_Icc.mpr ⟨h.1, h.2.1⟩)).elim
      · rfl
  have hright :
      (∑' j : ℕ, movingRight K r s N j) =
        ∑ k ∈ Icc K N, if N - k + 1 < k then
          (k : ℝ).rpow r * ((N - k + 1 : ℕ) : ℝ).rpow s else 0 := by
    rw [tsum_eq_sum (s :=
      (Icc 1 N).filter (fun j => K ≤ N - j + 1 ∧ j < N - j + 1))]
    · have hrhs :
          (∑ k ∈ Icc K N, if N - k + 1 < k then
              (k : ℝ).rpow r * ((N - k + 1 : ℕ) : ℝ).rpow s else 0) =
            ∑ k ∈ (Icc K N).filter (fun k => N - k + 1 < k),
              (k : ℝ).rpow r * ((N - k + 1 : ℕ) : ℝ).rpow s := by
          rw [Finset.sum_filter]
      rw [hrhs]
      symm
      apply Finset.sum_bij (fun k _ => N - k + 1)
      · intro k hk
        have hk' := mem_filter.mp hk
        have hkK := (mem_Icc.mp hk'.1).1
        have hkN := (mem_Icc.mp hk'.1).2
        exact mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega, by omega⟩, ⟨by
          have hinv : N - (N - k + 1) + 1 = k := by omega
          simpa [hinv] using hkK, by omega⟩⟩
      · intro k₁ hk₁ k₂ hk₂ heq
        have h₁ := (mem_Icc.mp (mem_filter.mp hk₁).1).2
        have h₂ := (mem_Icc.mp (mem_filter.mp hk₂).1).2
        omega
      · intro j hj
        have hj' := mem_filter.mp hj
        have hjlo := (mem_Icc.mp hj'.1).1
        have hjhi := (mem_Icc.mp hj'.1).2
        let k := N - j + 1
        have hkK : K ≤ k := by simpa [k] using hj'.2.1
        have hkN : k ≤ N := by dsimp [k]; omega
        have hinv : N - k + 1 = j := by dsimp [k]; omega
        have hk : k ∈ (Icc K N).filter (fun k => N - k + 1 < k) :=
          mem_filter.mpr ⟨mem_Icc.mpr ⟨hkK, hkN⟩, by
            rw [hinv]
            exact hj'.2.2⟩
        exact ⟨k, hk, hinv⟩
      · intro k hk
        have hk' := mem_filter.mp hk
        have hkK := (mem_Icc.mp hk'.1).1
        have hkN := (mem_Icc.mp hk'.1).2
        have hside := hk'.2
        have hinv : N - (N - k + 1) + 1 = k := by omega
        simp [movingRight, hinv, hkK, hkN, hside]
    · intro j hj
      simp only [movingRight]
      split_ifs with h
      · exact (hj (mem_filter.mpr ⟨mem_Icc.mpr ⟨h.1, by omega⟩,
          ⟨h.2.1, h.2.2.2⟩⟩)).elim
      · rfl
  rw [hleft, hright, movingPowerSum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases h : k ≤ N - k + 1
  · simp [h, not_lt_of_ge h]
  · have h' : N - k + 1 < k := lt_of_not_ge h
    simp [h, h']

lemma movingPowerSum_tendsto_zero
    (K : ℕ) (hK : 1 ≤ K) (r s : ℝ)
    (hr : r < 0) (hs : s < 0) (hrs : r + s < -1) :
    Tendsto (fun N => movingPowerSum K N r s) atTop (nhds 0) := by
  have hsum : Summable (fun k : ℕ => (k : ℝ).rpow (r + s)) :=
    Real.summable_nat_rpow.mpr hrs
  have hleft_point (k : ℕ) :
      Tendsto (fun N => movingLeft K r s N k) atTop (nhds 0) := by
    by_cases hk : K ≤ k
    · have hjNat : Tendsto (fun N : ℕ => N - k + 1) atTop atTop :=
        (Filter.tendsto_add_atTop_nat 1).comp (Filter.tendsto_sub_atTop_nat k)
      have hjReal : Tendsto (fun N : ℕ => ((N - k + 1 : ℕ) : ℝ)) atTop atTop :=
        tendsto_natCast_atTop_atTop.comp hjNat
      have hjPow : Tendsto (fun N : ℕ => ((N - k + 1 : ℕ) : ℝ).rpow s)
          atTop (nhds 0) := by
        simpa only [neg_neg, Function.comp_def, Real.rpow_eq_pow] using
          (tendsto_rpow_neg_atTop (neg_pos.mpr hs)).comp hjReal
      have heq : (fun N => movingLeft K r s N k) =ᶠ[atTop]
          (fun N => (k : ℝ).rpow r * ((N - k + 1 : ℕ) : ℝ).rpow s) := by
        filter_upwards [eventually_ge_atTop (2 * k)] with N hN
        simp [movingLeft, hk, show k ≤ N by omega, show k ≤ N - k + 1 by omega]
      simpa using (tendsto_const_nhds.mul hjPow).congr' heq.symm
    · simp [movingLeft, hk]
  have hright_point (j : ℕ) :
      Tendsto (fun N => movingRight K r s N j) atTop (nhds 0) := by
    by_cases hj : 1 ≤ j
    · have hkNat : Tendsto (fun N : ℕ => N - j + 1) atTop atTop :=
        (Filter.tendsto_add_atTop_nat 1).comp (Filter.tendsto_sub_atTop_nat j)
      have hkReal : Tendsto (fun N : ℕ => ((N - j + 1 : ℕ) : ℝ)) atTop atTop :=
        tendsto_natCast_atTop_atTop.comp hkNat
      have hkPow : Tendsto (fun N : ℕ => ((N - j + 1 : ℕ) : ℝ).rpow r)
          atTop (nhds 0) := by
        simpa only [neg_neg, Function.comp_def, Real.rpow_eq_pow] using
          (tendsto_rpow_neg_atTop (neg_pos.mpr hr)).comp hkReal
      have heq : (fun N => movingRight K r s N j) =ᶠ[atTop]
          (fun N => ((N - j + 1 : ℕ) : ℝ).rpow r * (j : ℝ).rpow s) := by
        filter_upwards [eventually_ge_atTop (K + 2 * j)] with N hN
        have hkK : K ≤ N - j + 1 := by omega
        have hkN : N - j + 1 ≤ N := by omega
        have hjk : j < N - j + 1 := by omega
        simp [movingRight, hj, hkK, hkN, hjk]
      simpa using (hkPow.mul_const ((j : ℝ).rpow s)).congr' heq.symm
    · simp [movingRight, hj]
  have hleft_bound : ∀ N k, ‖movingLeft K r s N k‖ ≤ (k : ℝ).rpow (r + s) := by
    intro N k
    simp only [movingLeft]
    split_ifs with h
    · have hkpos : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le (by omega) (hK.trans h.1))
      have hjposNat : 0 < N - k + 1 := by omega
      have hjpos : (0 : ℝ) < ((N - k + 1 : ℕ) : ℝ) := Nat.cast_pos.mpr hjposNat
      rw [Real.norm_eq_abs, abs_mul]
      have habsK : |(k : ℝ).rpow r| = (k : ℝ).rpow r :=
        abs_of_nonneg (Real.rpow_nonneg hkpos.le _)
      have habsJ : |((N - k + 1 : ℕ) : ℝ).rpow s| =
          ((N - k + 1 : ℕ) : ℝ).rpow s :=
        abs_of_nonneg (Real.rpow_nonneg hjpos.le _)
      rw [habsK, habsJ]
      have hcast : (k : ℝ) ≤ ((N - k + 1 : ℕ) : ℝ) := by
        exact_mod_cast h.2.2
      calc
        (k : ℝ).rpow r * ((N - k + 1 : ℕ) : ℝ).rpow s ≤
            (k : ℝ).rpow r * (k : ℝ).rpow s := by
          exact mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_nonpos hkpos hcast hs.le)
            (Real.rpow_nonneg hkpos.le _)
        _ = _ := (Real.rpow_add hkpos r s).symm
    · simpa using Real.rpow_nonneg (Nat.cast_nonneg k) (r + s)
  have hright_bound : ∀ N j, ‖movingRight K r s N j‖ ≤ (j : ℝ).rpow (r + s) := by
    intro N j
    simp only [movingRight]
    split_ifs with h
    · have hjpos : (0 : ℝ) < j := by exact_mod_cast h.1
      have hkposNat : 0 < N - j + 1 := lt_of_lt_of_le (by omega) (hK.trans h.2.1)
      have hkpos : (0 : ℝ) < ((N - j + 1 : ℕ) : ℝ) := Nat.cast_pos.mpr hkposNat
      rw [Real.norm_eq_abs, abs_mul]
      have habsK : |((N - j + 1 : ℕ) : ℝ).rpow r| =
          ((N - j + 1 : ℕ) : ℝ).rpow r :=
        abs_of_nonneg (Real.rpow_nonneg hkpos.le _)
      have habsJ : |(j : ℝ).rpow s| = (j : ℝ).rpow s :=
        abs_of_nonneg (Real.rpow_nonneg hjpos.le _)
      rw [habsK, habsJ]
      have hcast : (j : ℝ) ≤ ((N - j + 1 : ℕ) : ℝ) := by
        exact_mod_cast h.2.2.2.le
      calc
        ((N - j + 1 : ℕ) : ℝ).rpow r * (j : ℝ).rpow s ≤
            (j : ℝ).rpow r * (j : ℝ).rpow s := by
          exact mul_le_mul_of_nonneg_right
            (Real.rpow_le_rpow_of_nonpos hjpos hcast hr.le)
            (Real.rpow_nonneg hjpos.le _)
        _ = _ := (Real.rpow_add hjpos r s).symm
    · simpa using Real.rpow_nonneg (Nat.cast_nonneg j) (r + s)
  have hleft := tendsto_tsum_of_dominated_convergence hsum hleft_point
    (Filter.Eventually.of_forall hleft_bound)
  have hright := tendsto_tsum_of_dominated_convergence hsum hright_point
    (Filter.Eventually.of_forall hright_bound)
  have hadd := hleft.add hright
  simpa [movingPowerSum_eq_tsum_split, tsum_zero] using hadd

theorem p098 : P098Statement := by
  intro K hK y aPow hy0 hy1 ha0 haUpper
  rw [Asymptotics.isLittleO_one_iff]
  apply movingPowerSum_tendsto_zero K hK
  · linarith
  · linarith
  · linarith

theorem p099 : P099Statement := by
  intro K hK y aPow hy0 hy1 ha0 haUpper
  rw [Asymptotics.isLittleO_one_iff]
  apply movingPowerSum_tendsto_zero K hK
  · linarith
  · norm_num
  · linarith

@[expose] def actualMovingLogSumLocal
    (theta sigma y aPow exponent x : ℝ) (htheta : 2 ≤ theta) : ℝ :=
  if hx : 0 < x then
    let q : MovingCutoffDomain :=
      { theta := theta, theta_ge_two := htheta, x := x, x_pos := hx }
    ∑ k ∈ Finset.Icc (lowerBinIndex sigma theta) (movingCutoff q).toNat,
      (k : ℝ).rpow ((y - 3) / 2 + aPow) *
        (safeLog (2 * x * theta ^ (1 - (2 : ℤ) * k))).rpow exponent
  else 0

lemma movingCutoff_cell
    (theta x : ℝ) (htheta : 2 ≤ theta) (hx : 0 < x) :
    let q : MovingCutoffDomain :=
      { theta := theta, theta_ge_two := htheta, x := x, x_pos := hx }
    (movingCutoff q : ℝ) < movingCutoffReal q ∧
      movingCutoffReal q ≤ (movingCutoff q : ℝ) + 1 := by
  intro q
  constructor
  · unfold movingCutoff
    have h := Int.ceil_lt_add_one (movingCutoffReal q)
    push_cast
    linarith
  · unfold movingCutoff
    have h := Int.le_ceil (movingCutoffReal q)
    push_cast
    linarith

lemma endpoint_safeLog_lower
    (theta x : ℝ) (htheta : 2 ≤ theta) (hx : 0 < x) (k : ℕ)
    (hk : k ≤ (movingCutoff
      ({ theta := theta, theta_ge_two := htheta, x := x, x_pos := hx } :
        MovingCutoffDomain)).toNat) :
    min 1 (Real.log theta) *
        (((movingCutoff
          ({ theta := theta, theta_ge_two := htheta, x := x, x_pos := hx } :
            MovingCutoffDomain)).toNat - k + 1 : ℕ) : ℝ) ≤
      safeLog (2 * x * theta ^ (1 - (2 : ℤ) * k)) := by
  let q : MovingCutoffDomain :=
    { theta := theta, theta_ge_two := htheta, x := x, x_pos := hx }
  let N : ℤ := movingCutoff q
  change min 1 (Real.log theta) * (((N.toNat - k + 1 : ℕ) : ℝ)) ≤
    safeLog (2 * x * theta ^ (1 - (2 : ℤ) * k))
  have hlogtheta : 0 < Real.log theta := Real.log_pos (by linarith)
  have hsafe_one : (1 : ℝ) ≤ safeLog (2 * x * theta ^ (1 - (2 : ℤ) * k)) :=
    le_max_left _ _
  by_cases hNnonneg : 0 ≤ N
  · have hNcast : (N.toNat : ℤ) = N := Int.toNat_of_nonneg hNnonneg
    have hNreal : (N.toNat : ℝ) = (N : ℝ) := by exact_mod_cast hNcast
    have hkInt : (k : ℤ) ≤ N := by
      rw [← hNcast]
      exact_mod_cast hk
    have hcell : (N : ℝ) < movingCutoffReal q ∧
        movingCutoffReal q ≤ (N : ℝ) + 1 := by
      simpa [N, q] using movingCutoff_cell theta x htheta hx
    have hlogarg :
        Real.log (2 * x * theta ^ (1 - (2 : ℤ) * k)) =
          Real.log 2 + 2 * (movingCutoffReal q - k) * Real.log theta := by
      have htheta0 : theta ≠ 0 := by linarith
      have hx0 : x ≠ 0 := ne_of_gt hx
      rw [Real.log_mul (mul_ne_zero (by norm_num) hx0) (zpow_ne_zero _ htheta0),
        Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hx0,
        Real.log_zpow theta]
      unfold movingCutoffReal
      simp only [q]
      field_simp [ne_of_gt hlogtheta]
      push_cast
      ring_nf
    have hdelta : (N : ℝ) - k < movingCutoffReal q - k := by
      linarith [hcell.1]
    by_cases hlast : k = N.toNat
    · subst k
      simp only [Nat.sub_self, zero_add, Nat.cast_one, mul_one]
      exact (min_le_left _ _).trans hsafe_one
    · have hgapNat : 1 ≤ N.toNat - k := by omega
      have hgapReal : (1 : ℝ) ≤ (N : ℝ) - k := by
        have : (1 : ℝ) ≤ (N.toNat - k : ℕ) := by exact_mod_cast hgapNat
        rw [Nat.cast_sub hk, hNreal] at this
        exact this
      have hlogLower :
          Real.log theta * (((N.toNat - k + 1 : ℕ) : ℝ)) ≤
            Real.log (2 * x * theta ^ (1 - (2 : ℤ) * k)) := by
        rw [hlogarg]
        have hgapCast : (((N.toNat - k + 1 : ℕ) : ℝ)) =
            (N : ℝ) - k + 1 := by
          push_cast
          rw [Nat.cast_sub hk, hNreal]
        rw [hgapCast]
        have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
        nlinarith
      calc
        min 1 (Real.log theta) * ((N.toNat - k + 1 : ℕ) : ℝ) ≤
            Real.log theta * ((N.toNat - k + 1 : ℕ) : ℝ) := by
          exact mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)
        _ ≤ Real.log (2 * x * theta ^ (1 - (2 : ℤ) * k)) := hlogLower
        _ ≤ safeLog (2 * x * theta ^ (1 - (2 : ℤ) * k)) :=
          le_max_right _ _
  · have htoNat : N.toNat = 0 := Int.toNat_of_nonpos (by omega)
    have hk0 : k = 0 := by rw [htoNat] at hk; omega
    subst k
    simp only [htoNat, Nat.zero_sub, zero_add, Nat.cast_one, mul_one]
    exact (min_le_left _ _).trans hsafe_one

@[expose] def cutoffNatLocal (theta x : ℝ) (htheta : 2 ≤ theta) : ℕ :=
  if hx : 0 < x then
    (movingCutoff
      ({ theta := theta, theta_ge_two := htheta, x := x, x_pos := hx } :
        MovingCutoffDomain)).toNat
  else 0

lemma cutoffNatLocal_tendsto_atTop (theta : ℝ) (htheta : 2 ≤ theta) :
    Tendsto (cutoffNatLocal theta · htheta) atTop atTop := by
  have hlogtheta : 0 < Real.log theta := Real.log_pos (by linarith)
  have hdiv : Tendsto (fun x : ℝ => Real.log x / Real.log theta) atTop atTop :=
    Real.tendsto_log_atTop.atTop_div_const hlogtheta
  have hadd : Tendsto (fun x : ℝ => 1 + Real.log x / Real.log theta) atTop atTop :=
    Filter.tendsto_atTop_add_const_left atTop 1 hdiv
  have hX : Tendsto (fun x : ℝ => (1 / 2 : ℝ) *
      (1 + Real.log x / Real.log theta)) atTop atTop :=
    hadd.const_mul_atTop' (by norm_num)
  apply Filter.tendsto_atTop.mpr
  intro b
  filter_upwards [hX.eventually (eventually_ge_atTop ((b : ℝ) + 2)),
    eventually_ge_atTop (1 : ℝ)] with x hXx hx
  have hxpos : 0 < x := by linarith
  simp only [cutoffNatLocal, dif_pos hxpos]
  let q : MovingCutoffDomain :=
    { theta := theta, theta_ge_two := htheta, x := x, x_pos := hxpos }
  change b ≤ (movingCutoff q).toNat
  have hceil : ((b : ℤ) + 2) ≤ Int.ceil (movingCutoffReal q) := by
    have hXx' : (b : ℝ) + 2 ≤ movingCutoffReal q := by
      simpa [movingCutoffReal, q] using hXx
    have hceilReal : (b : ℝ) + 2 ≤ (Int.ceil (movingCutoffReal q) : ℝ) :=
      hXx'.trans (Int.le_ceil _)
    exact_mod_cast hceilReal
  have hN : (0 : ℤ) ≤ Int.ceil (movingCutoffReal q) - 1 := by omega
  have hcast : ((Int.ceil (movingCutoffReal q) - 1).toNat : ℤ) =
      Int.ceil (movingCutoffReal q) - 1 := Int.toNat_of_nonneg hN
  unfold movingCutoff
  rw [← Int.ofNat_le]
  rw [hcast]
  omega

lemma actualMovingLogSumLocal_nonneg
    (theta sigma y aPow exponent x : ℝ) (htheta : 2 ≤ theta) :
    0 ≤ actualMovingLogSumLocal theta sigma y aPow exponent x htheta := by
  unfold actualMovingLogSumLocal
  split_ifs
  · apply Finset.sum_nonneg
    intro k hk
    exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg k) _)
      (Real.rpow_nonneg (by simp [safeLog]) _)
  · exact le_rfl

lemma actualMovingLogSumLocal_le
    (theta sigma y aPow exponent x : ℝ) (htheta : 2 ≤ theta)
    (hexponent : exponent < 0) :
    actualMovingLogSumLocal theta sigma y aPow exponent x htheta ≤
      (min 1 (Real.log theta)).rpow exponent *
        movingPowerSum (lowerBinIndex sigma theta) (cutoffNatLocal theta x htheta)
          ((y - 3) / 2 + aPow) exponent := by
  unfold actualMovingLogSumLocal cutoffNatLocal
  by_cases hx : 0 < x
  · simp only [dif_pos hx]
    let q : MovingCutoffDomain :=
      { theta := theta, theta_ge_two := htheta, x := x, x_pos := hx }
    change (∑ k ∈ Icc (lowerBinIndex sigma theta) (movingCutoff q).toNat,
        (k : ℝ).rpow ((y - 3) / 2 + aPow) *
          (safeLog (2 * x * theta ^ (1 - (2 : ℤ) * k))).rpow exponent) ≤ _
    rw [movingPowerSum, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k hk
    have hkUpper := (mem_Icc.mp hk).2
    have hcpos : 0 < min 1 (Real.log theta) :=
      lt_min (by norm_num) (Real.log_pos (by linarith))
    have hjpos : (0 : ℝ) < (((movingCutoff q).toNat - k + 1 : ℕ) : ℝ) := by
      exact_mod_cast (by omega : 0 < (movingCutoff q).toNat - k + 1)
    have hlower := endpoint_safeLog_lower theta x htheta hx k hkUpper
    have hbasepos : 0 < min 1 (Real.log theta) *
        (((movingCutoff q).toNat - k + 1 : ℕ) : ℝ) := mul_pos hcpos hjpos
    have hsafe :
        (safeLog (2 * x * theta ^ (1 - (2 : ℤ) * k))).rpow exponent ≤
          (min 1 (Real.log theta) *
            (((movingCutoff q).toNat - k + 1 : ℕ) : ℝ)).rpow exponent :=
      Real.rpow_le_rpow_of_nonpos hbasepos hlower hexponent.le
    calc
      (k : ℝ).rpow ((y - 3) / 2 + aPow) *
          (safeLog (2 * x * theta ^ (1 - (2 : ℤ) * k))).rpow exponent ≤
        (k : ℝ).rpow ((y - 3) / 2 + aPow) *
          (min 1 (Real.log theta) *
            (((movingCutoff q).toNat - k + 1 : ℕ) : ℝ)).rpow exponent := by
        exact mul_le_mul_of_nonneg_left hsafe (Real.rpow_nonneg (Nat.cast_nonneg k) _)
      _ = (min 1 (Real.log theta)).rpow exponent *
          ((k : ℝ).rpow ((y - 3) / 2 + aPow) *
            (((movingCutoff q).toNat - k + 1 : ℕ) : ℝ).rpow exponent) := by
        have hmul :
            (min 1 (Real.log theta) *
                (((movingCutoff q).toNat - k + 1 : ℕ) : ℝ)).rpow exponent =
              (min 1 (Real.log theta)).rpow exponent *
                (((movingCutoff q).toNat - k + 1 : ℕ) : ℝ).rpow exponent :=
          Real.mul_rpow hcpos.le hjpos.le
        rw [hmul]
        ring
  · simp [hx, movingPowerSum, lowerBinIndex]

lemma actualMovingLogSumLocal_tendsto_zero
    (theta sigma y aPow exponent : ℝ) (htheta : 2 ≤ theta)
    (hr : (y - 3) / 2 + aPow < 0) (he : exponent < 0)
    (hre : (y - 3) / 2 + aPow + exponent < -1) :
    Tendsto (fun x => actualMovingLogSumLocal theta sigma y aPow exponent x htheta)
      atTop (nhds 0) := by
  let K := lowerBinIndex sigma theta
  have hK : 1 ≤ K := by
    unfold K lowerBinIndex
    exact le_max_left _ _
  have hmoving : Tendsto
      (fun N => movingPowerSum K N ((y - 3) / 2 + aPow) exponent)
      atTop (nhds 0) := movingPowerSum_tendsto_zero K hK _ _ hr he hre
  have hcutoff := cutoffNatLocal_tendsto_atTop theta htheta
  have hcomposed : Tendsto
      (fun x => movingPowerSum K (cutoffNatLocal theta x htheta)
        ((y - 3) / 2 + aPow) exponent) atTop (nhds 0) :=
    hmoving.comp hcutoff
  have hupper : Tendsto
      (fun x => (min 1 (Real.log theta)).rpow exponent *
        movingPowerSum K (cutoffNatLocal theta x htheta)
          ((y - 3) / 2 + aPow) exponent) atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul hcomposed
  apply squeeze_zero
  · intro x
    exact actualMovingLogSumLocal_nonneg theta sigma y aPow exponent x htheta
  · intro x
    exact actualMovingLogSumLocal_le theta sigma y aPow exponent x htheta he
  · exact hupper

theorem p100 : P100Statement := by
  unfold P100Statement
  intro theta sigma htheta hsigma y aPow hy0 hy1 ha0 haUpper
  rw [Asymptotics.isLittleO_one_iff]
  change Tendsto
    (fun x => actualMovingLogSumLocal theta sigma y aPow ((y - 1) / 2) x htheta)
    atTop (nhds 0)
  apply actualMovingLogSumLocal_tendsto_zero
  · linarith
  · linarith
  · linarith

theorem p101 : P101Statement := by
  unfold P101Statement
  intro theta sigma htheta hsigma y aPow hy0 hy1 ha0 haUpper
  rw [Asymptotics.isLittleO_one_iff]
  change Tendsto
    (fun x => actualMovingLogSumLocal theta sigma y aPow (-1 / 2) x htheta)
    atTop (nhds 0)
  apply actualMovingLogSumLocal_tendsto_zero
  · linarith
  · norm_num
  · linarith

lemma nat_le_movingCutoff_toNat_of_pow_lt
    (theta x : ℝ) (htheta : 2 ≤ theta) (hx : 0 < x)
    (k : ℕ) (hk : 1 ≤ k) (hpow : theta ^ (2 * k - 1) < x) :
    k ≤ (movingCutoff
      ({ theta := theta, theta_ge_two := htheta, x := x, x_pos := hx } :
        MovingCutoffDomain)).toNat := by
  let q : MovingCutoffDomain :=
    { theta := theta, theta_ge_two := htheta, x := x, x_pos := hx }
  have hthetaPos : 0 < theta := by linarith
  have hlogtheta : 0 < Real.log theta := Real.log_pos (by linarith)
  have hlogpow := Real.strictMonoOn_log (pow_pos hthetaPos _) hx hpow
  rw [Real.log_pow] at hlogpow
  have hkX : (k : ℝ) < movingCutoffReal q := by
    unfold movingCutoffReal
    simp only [q]
    have hexp : (((2 * k - 1 : ℕ) : ℝ)) = 2 * (k : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ 2 * k)]
      push_cast
      ring
    rw [hexp] at hlogpow
    have hratio : 2 * (k : ℝ) - 1 < Real.log x / Real.log theta :=
      (lt_div_iff₀ hlogtheta).2 hlogpow
    nlinarith
  have hcell := movingCutoff_cell theta x htheta hx
  have hkInt : (k : ℤ) ≤ movingCutoff q := by
    have : (k : ℝ) < (movingCutoff q : ℝ) + 1 := hkX.trans_le hcell.2
    have hz : (k : ℤ) < movingCutoff q + 1 := by exact_mod_cast this
    omega
  have hNnonneg : (0 : ℤ) ≤ movingCutoff q := (by omega)
  have hcast : ((movingCutoff q).toNat : ℤ) = movingCutoff q :=
    Int.toNat_of_nonneg hNnonneg
  rw [← hcast] at hkInt
  exact_mod_cast hkInt

lemma fkSharp_zero_above_cutoff
    (h054 : P054Statement) (q : SharpParameters) (n : PosNat)
    (x : ℝ) (hx : 0 < x) (hnx : (n.1 : ℝ) < x)
    (hk : 1 ≤ q.k)
    (habove : (movingCutoff
      ({ theta := q.theta, theta_ge_two := q.theta_ge_two, x := x, x_pos := hx } :
        MovingCutoffDomain)).toNat < q.k) :
    fkSharp q n = 0 := by
  classical
  unfold fkSharp
  apply mul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro d hdmem
  apply Finset.sum_eq_zero
  intro d' hd'mem
  apply Finset.sum_eq_zero
  intro t htmem
  by_cases hd : 0 < d
  · simp only [dif_pos hd]
    by_cases hd' : 0 < d'
    · simp only [dif_pos hd']
      by_cases hbase : d * d' * t ∣ n.1 ∧
          q.theta ^ q.k ≤ (d : ℝ) ∧ (d : ℝ) < q.theta ^ (q.k + 1) ∧
          Close q.theta ⟨d, hd⟩ ⟨d', hd'⟩
      · exfalso
        have ht : 0 < t := by
          simpa [positiveNatsUpTo] using (mem_filter.mp htmem).2
        have hp := h054 q.k hk q.theta (by linarith [q.theta_ge_two])
          ⟨d, hd⟩ ⟨d', hd'⟩ hbase.2.1 hbase.2.2.1 hbase.2.2.2
        have htriple : d * d' * t ≤ n.1 := Nat.le_of_dvd n.2 hbase.1
        have hpair : d * d' ≤ d * d' * t := Nat.le_mul_of_pos_right _ ht
        have hsupport : q.theta ^ (2 * q.k - 1) < x := by
          calc
            q.theta ^ (2 * q.k - 1) < (d * d' : ℕ) := hp.product_lower
            _ ≤ (d * d' * t : ℕ) := by exact_mod_cast hpair
            _ ≤ (n.1 : ℝ) := by exact_mod_cast htriple
            _ < x := hnx
        exact (not_lt_of_ge (nat_le_movingCutoff_toNat_of_pow_lt
          q.theta x q.theta_ge_two hx q.k hk hsupport)) habove
      · simp [hbase]
    · simp [hd']
  · simp [hd]

@[expose] def p092L4Local (q : P092Parameters) : Lemma4Parameters :=
  { epsilonInt := q.epsilonInt, epsilonInt_pos := q.epsilonInt_pos,
    epsilonInt_le_tenth := q.epsilonInt_le_tenth,
    xi := q.xi, xi_gt_one := q.xi_gt_one,
    sigma := q.sigma, sigma_ge_two := q.theta_ge_two.trans q.sigma_ge_theta,
    theta := q.theta, theta_ge_two := q.theta_ge_two,
    sigma_ge_theta := q.sigma_ge_theta }

@[expose] def p092SharpLocal (q : P092Parameters) (k : ℕ) : SharpParameters :=
  { y := q.y, y_pos := q.y_pos, y_lt_one := q.y_lt_one, k := k,
    theta := q.theta, theta_ge_two := q.theta_ge_two,
    sigma := q.sigma, sigma_ge_theta := q.sigma_ge_theta }

@[expose] def p092CutoffLocal (q : P092Parameters) : ℤ :=
  movingCutoff
    { theta := q.theta, theta_ge_two := q.theta_ge_two, x := q.x,
      x_pos := (Real.exp_pos _).trans q.x_gt_U0 }

@[expose] def p092LeftLocal (q : P092Parameters) : ℝ :=
  ∑ n ∈ positiveNatsBelow q.x,
    if hn : 0 < n then
      if Real.exp (Real.log q.xi * Real.log q.sigma) < n then
        normalizedClosePair (p092L4Local q) ⟨n, hn⟩
      else 0
    else 0

@[expose] def p092KLocal (q : P092Parameters) : ℝ :=
  ∑ k ∈ Icc (lowerBinIndex q.sigma q.theta) (p092CutoffLocal q).toNat,
    (k : ℝ).rpow (P092APow q) *
      (∑ n ∈ positiveNatsBelow q.x,
        if hn : 0 < n then fkSharp (p092SharpLocal q k) ⟨n, hn⟩ else 0)

lemma fkSharp_nonneg_local (q : SharpParameters) (n : PosNat) :
    0 ≤ fkSharp q n := by
  unfold fkSharp
  apply mul_nonneg
  · positivity
  · apply Finset.sum_nonneg
    intro d hd
    apply Finset.sum_nonneg
    intro d' hd'
    apply Finset.sum_nonneg
    intro t ht
    split_ifs
    · exact mul_nonneg
        (mul_nonneg (by positivity) (Real.rpow_nonneg q.y_pos.le _))
        (by positivity)
    all_goals positivity

lemma normalizedClosePair_nonneg_local
    (q : Lemma4Parameters) (n : PosNat) :
    0 ≤ normalizedClosePair q n := by
  unfold normalizedClosePair closePairSum
  apply div_nonneg
  · apply mul_nonneg
    · positivity
    · apply Finset.sum_nonneg
      intro d hd
      apply Finset.sum_nonneg
      intro d' hd'
      split_ifs <;> positivity
  · positivity

theorem p092 (h044 : P044Statement) (h054 : P054Statement) : P092Statement := by
  intro q
  change p092LeftLocal q ≤
      (2 * Real.log q.xi * Real.log q.theta / Real.log q.sigma).rpow
        (P092APow q) * p092KLocal q ∧
    (p092CutoffLocal q < (lowerBinIndex q.sigma q.theta : ℤ) →
      p092KLocal q = 0 ∧ p092LeftLocal q = 0)
  let K := lowerBinIndex q.sigma q.theta
  let N := (p092CutoffLocal q).toNat
  let C := (2 * Real.log q.xi * Real.log q.theta / Real.log q.sigma).rpow
    (P092APow q)
  let F : ℕ → ℕ → ℝ := fun n k =>
    if hn : 0 < n then
      if K ≤ k then
        (k : ℝ).rpow (P092APow q) * fkSharp (p092SharpLocal q k) ⟨n, hn⟩
      else 0
    else 0
  have hK : 1 ≤ K := by
    dsimp [K]
    unfold lowerBinIndex
    exact le_max_left _ _
  have hx : 0 < q.x := (Real.exp_pos _).trans q.x_gt_U0
  have hFsummable : ∀ n ∈ positiveNatsBelow q.x, Summable (F n) := by
    intro n hnmem
    apply summable_of_ne_finset_zero (s := Icc K N)
    intro k hkout
    simp only [F]
    by_cases hn : 0 < n
    · simp only [dif_pos hn]
      by_cases hkK : K ≤ k
      · simp only [if_pos hkK]
        have hk1 : 1 ≤ k := hK.trans hkK
        have hnx : (n : ℝ) < q.x := (mem_filter.mp hnmem).2.2
        have hkN : N < k := by
          by_contra h
          exact hkout (mem_Icc.mpr ⟨hkK, Nat.le_of_not_gt h⟩)
        rw [fkSharp_zero_above_cutoff h054 (p092SharpLocal q k) ⟨n, hn⟩
          q.x hx hnx hk1]
        · simp
        · simpa [N, p092CutoffLocal, p092SharpLocal] using hkN
      · simp [hkK]
    · simp [hn]
  have hFnonneg : ∀ n k, 0 ≤ F n k := by
    intro n k
    simp only [F]
    split_ifs
    · exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg k) _)
        (fkSharp_nonneg_local _ _)
    all_goals positivity
  have hC : 0 ≤ C := by
    apply Real.rpow_nonneg
    apply div_nonneg
    · exact mul_nonneg
        (mul_nonneg (by positivity) (Real.log_pos q.xi_gt_one).le)
        (Real.log_pos (lt_of_lt_of_le (by norm_num) q.theta_ge_two)).le
    · exact (Real.log_pos
        (lt_of_lt_of_le (by norm_num) (q.theta_ge_two.trans q.sigma_ge_theta))).le
  have hpoint : ∀ n ∈ positiveNatsBelow q.x,
      (if hn : 0 < n then
        if Real.exp (Real.log q.xi * Real.log q.sigma) < n then
          normalizedClosePair (p092L4Local q) ⟨n, hn⟩ else 0 else 0) ≤
        C * ∑' k, F n k := by
    intro n hnmem
    by_cases hn : 0 < n
    · simp only [dif_pos hn]
      by_cases hnU : Real.exp (Real.log q.xi * Real.log q.sigma) < n
      · simp only [if_pos hnU]
        have hp := (h044 (p092L4Local q) q.y q.y_pos q.y_lt_one ⟨n, hn⟩ hnU).bound
        have hFeq : (fun k => F n k) = fun k =>
            if K ≤ k then
              (k : ℝ).rpow (P092APow q) *
                fkSharp (p092SharpLocal q k) ⟨n, hn⟩
            else 0 := by
          funext k
          simp [F, hn]
        rw [hFeq]
        simpa [C, K, P092APow, p092L4Local, p092SharpLocal,
          sharpParametersOf] using hp
      · simp only [if_neg hnU]
        exact mul_nonneg hC (tsum_nonneg (hFnonneg n))
    · simp only [dif_neg hn]
      exact mul_nonneg hC (tsum_nonneg (hFnonneg n))
  have hmain : p092LeftLocal q ≤ C * p092KLocal q := by
    unfold p092LeftLocal
    calc
      _ ≤ ∑ n ∈ positiveNatsBelow q.x, C * ∑' k, F n k :=
        Finset.sum_le_sum hpoint
      _ = C * ∑ n ∈ positiveNatsBelow q.x, ∑' k, F n k := by
        rw [Finset.mul_sum]
      _ = C * ∑' k, ∑ n ∈ positiveNatsBelow q.x, F n k := by
        rw [Summable.tsum_finsetSum hFsummable]
      _ = C * p092KLocal q := by
        congr 1
        unfold p092KLocal
        rw [tsum_eq_sum (s := Icc K N)]
        · apply Finset.sum_congr
          · simp [K, N]
          · intro k hk
            simp only [F]
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro n hnmem
            by_cases hn : 0 < n
            · simp [hn, (mem_Icc.mp hk).1, K, p092SharpLocal]
            · simp [hn]
        · intro k hk
          by_cases hkK : K ≤ k
          · have hkN : N < k := by
              by_contra h
              exact hk (mem_Icc.mpr ⟨hkK, Nat.le_of_not_gt h⟩)
            apply Finset.sum_eq_zero
            intro n hnmem
            simp only [F]
            by_cases hn : 0 < n
            · simp only [dif_pos hn, if_pos hkK]
              have hk1 := hK.trans hkK
              have hnx : (n : ℝ) < q.x := (mem_filter.mp hnmem).2.2
              rw [fkSharp_zero_above_cutoff h054 (p092SharpLocal q k) ⟨n, hn⟩
                q.x hx hnx hk1]
              · simp
              · simpa [N, p092CutoffLocal, p092SharpLocal] using hkN
            · simp [hn]
          · simp [F, hkK]
  refine ⟨?_, ?_⟩
  · simpa [C] using hmain
  · intro hempty
    have hNK : N < K := by
      dsimp [N, K]
      by_cases hcut : 0 ≤ p092CutoffLocal q
      · have hcast : ((p092CutoffLocal q).toNat : ℤ) = p092CutoffLocal q :=
          Int.toNat_of_nonneg hcut
        have hcastLt : ((p092CutoffLocal q).toNat : ℤ) < (K : ℤ) := by
          simpa [K, hcast] using hempty
        exact_mod_cast hcastLt
      · have hcut' : p092CutoffLocal q < 0 := lt_of_not_ge hcut
        have hto : (p092CutoffLocal q).toNat = 0 :=
          Int.toNat_of_nonpos hcut'.le
        rw [hto]
        exact hK
    have hksum : p092KLocal q = 0 := by
      unfold p092KLocal
      simp [show Icc K N = ∅ by ext k; simp; omega, K, N]
    refine ⟨hksum, le_antisymm ?_ ?_⟩
    · rw [hksum, mul_zero] at hmain
      exact hmain
    · unfold p092LeftLocal
      apply Finset.sum_nonneg
      intro n hnmem
      split_ifs
      · exact normalizedClosePair_nonneg_local _ _
      all_goals positivity

theorem result : Erdos448.Stage6.TaskContracts.ROOT11Target := by
  intro h044 h054
  exact {
    p092 := p092 h044 h054
    p096 := p096
    p097 := p097
    p100 := p100
    p101 := p101 }

end

end Erdos448.Stage7.ROOT11.Work
