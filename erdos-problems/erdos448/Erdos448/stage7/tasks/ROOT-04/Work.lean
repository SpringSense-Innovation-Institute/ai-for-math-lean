module

import all Mathlib.Basic.Real.Basic
public import Erdos448.stage7.tasks.«ROOT-04».Pointwise
public import Erdos448.stage7.tasks.«ROOT-04».FiniteSupport
public import Erdos448.stage7.tasks.«ROOT-04».Reindex

public section

set_option backward.isDefEq.respectTransparency false

namespace Erdos448.Stage7.ROOT04.Work

open Erdos448.Stage4
open Erdos448.Stage4.Contracts
open Erdos448.Stage6.TaskContracts
open Erdos448.Stage7.ROOT04.Helpers
open Erdos448.Stage7.ROOT04.Pointwise
open Erdos448.Stage7.ROOT04.FiniteSupport
open Erdos448.Stage7.ROOT04.Reindex
open Finset
open scoped BigOperators

noncomputable section

instance (p : Prop) : Decidable p := Classical.propDecidable p

@[expose] def pairSet (q : Lemma4Parameters) (n : PosNat) : Finset (ℕ × ℕ) :=
  (divisorSet n ×ˢ divisorSet n).filter fun x =>
    if hD : 0 < x.1 then
      if hD' : 0 < x.2 then
        Close q.theta ⟨x.1, hD⟩ ⟨x.2, hD'⟩ ∧
          roughIndicator x.1 q.sigma = 1 ∧
          Good q.toGoodParameters n ⟨x.1, hD⟩
      else False
    else False

lemma mem_pairSet_iff (q : Lemma4Parameters) (n : PosNat) (D D' : ℕ) :
    (D, D') ∈ pairSet q n ↔
      D ∈ divisorSet n ∧ D' ∈ divisorSet n ∧
      ∃ hD : 0 < D, ∃ hD' : 0 < D',
        Close q.theta ⟨D, hD⟩ ⟨D', hD'⟩ ∧
        roughIndicator D q.sigma = 1 ∧
        Good q.toGoodParameters n ⟨D, hD⟩ := by
  simp only [pairSet, Finset.mem_filter, Finset.mem_product]
  by_cases hD : 0 < D <;> by_cases hD' : 0 < D'
  · simp [hD, hD']
    aesop
  · simp [hD, hD']
  · simp [hD]
  · simp [hD]

lemma closePairSum_eq_pair_sum (q : Lemma4Parameters) (n : PosNat) :
    closePairSum q n = ∑ _x ∈ pairSet q n, (1 : ℝ) := by
  classical
  unfold closePairSum pairSet
  simp only [Finset.sum_filter, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro D hDmem
  apply Finset.sum_congr rfl
  intro D' hD'mem
  by_cases hD : 0 < D
  · by_cases hD' : 0 < D'
    · by_cases hc : Close q.theta ⟨D, hD⟩ ⟨D', hD'⟩
      · by_cases hr : roughIndicator D q.sigma = 1
        · by_cases hg : Good q.toGoodParameters n ⟨D, hD⟩
          · simp [hD, hD', hc, hr, hg, goodIndicator, n.2]
          · simp [hD, hD', hc, hr, hg, goodIndicator, n.2]
        · have hr0 : roughIndicator D q.sigma = 0 := by
            classical
            unfold roughIndicator at hr ⊢
            split_ifs at hr ⊢ <;> simp_all
          simp [hD, hD', hc, hr, hr0, goodIndicator]
      · simp [hD, hD', hc]
    · simp [hD, hD']
  · simp [hD]

@[expose] def binOf (q : Lemma4Parameters) (d : ℕ) (hd : 1 ≤ d) : ℕ :=
  Classical.choose (exists_nat_pow_near (show (1 : ℝ) ≤ d by exact_mod_cast hd)
    (lt_of_lt_of_le (by norm_num) q.theta_ge_two))

lemma binOf_spec (q : Lemma4Parameters) (d : ℕ) (hd : 1 ≤ d) :
    q.theta ^ binOf q d hd ≤ (d : ℝ) ∧
      (d : ℝ) < q.theta ^ (binOf q d hd + 1) :=
  Classical.choose_spec (exists_nat_pow_near
    (show (1 : ℝ) ≤ d by exact_mod_cast hd)
    (lt_of_lt_of_le (by norm_num) q.theta_ge_two))

@[expose] def pairBin (q : Lemma4Parameters) (x : ℕ × ℕ) : ℕ :=
  if hd : 1 ≤ x.1 / Nat.gcd x.1 x.2 then
    binOf q (x.1 / Nat.gcd x.1 x.2) hd
  else 0

@[expose] def tripleOf (x : ℕ × ℕ) : ℕ × ℕ × ℕ :=
  (x.1 / Nat.gcd x.1 x.2, x.2 / Nat.gcd x.1 x.2, Nat.gcd x.1 x.2)

lemma pair_data (q : Lemma4Parameters) (n : PosNat)
    (hnrough : roughIndicator n.1 q.theta = 1) {x : ℕ × ℕ}
    (hx : x ∈ pairSet q n) :
    let d := (tripleOf x).1
    let d' := (tripleOf x).2.1
    let t := (tripleOf x).2.2
    0 < x.1 ∧ 0 < x.2 ∧ 0 < d ∧ 0 < d' ∧ 0 < t ∧
      x.1 = d * t ∧ x.2 = d' * t ∧ d * d' * t ∣ n.1 ∧
      roughIndicator d q.sigma = 1 ∧ roughIndicator t q.sigma = 1 ∧
      d ≠ d' ∧ 1 / q.theta < (d' : ℝ) / d ∧ (d' : ℝ) / d < q.theta ∧
      q.sigma ≤ d ∧
      q.theta ^ pairBin q x ≤ (d : ℝ) ∧
      (d : ℝ) < q.theta ^ (pairBin q x + 1) ∧
      lowerBinIndex q.sigma q.theta ≤ pairBin q x := by
  obtain ⟨hxD, hxD', hD, hD', hclose, hrough, hgood⟩ :=
    (mem_pairSet_iff q n x.1 x.2).mp hx
  let D : PosNat := ⟨x.1, hD⟩
  let D' : PosNat := ⟨x.2, hD'⟩
  have hDdvd : D.1 ∣ n.1 := Nat.dvd_of_mem_divisors hxD
  have hD'dvd : D'.1 ∣ n.1 := Nat.dvd_of_mem_divisors hxD'
  obtain ⟨ht, hd, hd', hDt, hD't, hcop, hdiv, hratio⟩ :=
    gcd_reindex n D D' hDdvd hD'dvd hclose
  let t := Nat.gcd x.1 x.2
  let d := x.1 / t
  let d' := x.2 / t
  change 0 < t at ht
  change 0 < d at hd
  change 0 < d' at hd'
  change x.1 = d * t at hDt
  change x.2 = d' * t at hD't
  change d * d' * t ∣ n.1 at hdiv
  change (x.2 : ℝ) / x.1 = (d' : ℝ) / d at hratio
  obtain ⟨hdr, htr, hdgt, hdge⟩ :=
    reduced_rough_and_gt_one q n D D' hnrough hrough hDdvd hD'dvd hclose
  change roughIndicator d q.sigma = 1 at hdr
  change roughIndicator t q.sigma = 1 at htr
  change 1 < d at hdgt
  change q.sigma ≤ d at hdge
  have hredclose : Close q.theta ⟨d, hd⟩ ⟨d', hd'⟩ := by
    refine ⟨?_, ?_, ?_⟩
    · intro heq
      apply hclose.1
      apply Subtype.ext
      simpa [hDt, hD't] using congr_arg (fun z : PosNat => z.1 * t) heq
    · simpa [hratio] using hclose.2.1
    · simpa [hratio] using hclose.2.2
  have hpairBin : pairBin q x = binOf q d (Nat.one_le_of_lt hdgt) := by
    simp [pairBin, d, t, Nat.one_le_of_lt hdgt]
  have hbin := binOf_spec q d (Nat.one_le_of_lt hdgt)
  have hlower := bin_lower q hdge hbin
  rw [← hpairBin] at hbin hlower
  simpa [tripleOf, d, d', t] using
    And.intro hD (And.intro hD' (And.intro hd (And.intro hd' (And.intro ht
      (And.intro hDt (And.intro hD't (And.intro hdiv
        (And.intro hdr (And.intro htr (And.intro hredclose.1
          (And.intro hredclose.2.1 (And.intro hredclose.2.2 (And.intro hdge
            (And.intro hbin.1 (And.intro hbin.2 hlower)))))))))))))))

lemma tripleOf_injective_on (q : Lemma4Parameters) (n : PosNat)
    (hnrough : roughIndicator n.1 q.theta = 1) :
    (pairSet q n : Set (ℕ × ℕ)).InjOn tripleOf := by
  intro x hx z hz heq
  obtain ⟨_, _, hdx, hdx', htx, hx1, hx2, _⟩ := pair_data q n hnrough hx
  obtain ⟨_, _, hdz, hdz', htz, hz1, hz2, _⟩ := pair_data q n hnrough hz
  apply Prod.ext
  · calc
      x.1 = (tripleOf x).1 * (tripleOf x).2.2 := hx1
      _ = (tripleOf z).1 * (tripleOf z).2.2 :=
        congr_arg (fun w : ℕ × ℕ × ℕ => w.1 * w.2.2) heq
      _ = z.1 := hz1.symm
  · calc
      x.2 = (tripleOf x).2.1 * (tripleOf x).2.2 := hx2
      _ = (tripleOf z).2.1 * (tripleOf z).2.2 :=
        congr_arg (fun w : ℕ × ℕ × ℕ => w.2.1 * w.2.2) heq
      _ = z.2 := hz2.symm

lemma lowerBin_half (q : Lemma4Parameters) {k : ℕ}
    (hk : lowerBinIndex q.sigma q.theta ≤ k) :
    (1 / 2 : ℝ) * Real.log q.sigma / Real.log q.theta ≤ k := by
  have hceil : Nat.ceil ((1 / 2 : ℝ) * Real.log q.sigma / Real.log q.theta) ≤ k :=
    (le_max_right _ _).trans hk
  exact (Nat.le_ceil _).trans (by exact_mod_cast hceil)

lemma split_majorant (q : Lemma4Parameters) (y : ℝ) (k : ℕ)
    (m : PosNat) (hk : 1 ≤ k) :
    goodPowerMajorant q y k m =
      (2 * Real.log q.xi * Real.log q.theta / Real.log q.sigma).rpow
          (-(1 / 2 + q.epsilonInt) * Real.log y) *
        (k : ℝ).rpow (-(1 / 2 + q.epsilonInt) * Real.log y) *
          y.rpow (omegaBelow m (q.theta ^ k) : ℝ) := by
  have hli : 0 < Real.log q.xi := Real.log_pos q.xi_gt_one
  have hlt : 0 < Real.log q.theta := Real.log_pos
    (lt_of_lt_of_le (by norm_num) q.theta_ge_two)
  have hls : 0 < Real.log q.sigma := Real.log_pos
    (lt_of_lt_of_le (by norm_num) (q.theta_ge_two.trans q.sigma_ge_theta))
  have hbase : 0 ≤ 2 * Real.log q.xi * Real.log q.theta / Real.log q.sigma := by positivity
  have hk0 : (0 : ℝ) ≤ k := by positivity
  unfold goodPowerMajorant
  change
    (2 * (k : ℝ) * Real.log q.xi * Real.log q.theta / Real.log q.sigma) ^
        (-(1 / 2 + q.epsilonInt) * Real.log y) *
      y ^ (omegaBelow m (q.theta ^ k) : ℝ) =
    (2 * Real.log q.xi * Real.log q.theta / Real.log q.sigma) ^
        (-(1 / 2 + q.epsilonInt) * Real.log y) *
      (k : ℝ) ^ (-(1 / 2 + q.epsilonInt) * Real.log y) *
        y ^ (omegaBelow m (q.theta ^ k) : ℝ)
  have hfactor : (2 * (k : ℝ) * Real.log q.xi * Real.log q.theta / Real.log q.sigma) =
      (2 * Real.log q.xi * Real.log q.theta / Real.log q.sigma) * k := by ring
  rw [hfactor, Real.mul_rpow hbase hk0]

@[expose] def tripleUniverse (n : PosNat) : Finset (ℕ × ℕ × ℕ) :=
  positiveNatsUpTo n.1 ×ˢ (positiveNatsUpTo n.1 ×ˢ positiveNatsUpTo n.1)

@[expose] def sharpTermAt (q : Lemma4Parameters) (y : ℝ)
    (hy0 : 0 < y) (hy1 : y < 1) (n : PosNat) (k : ℕ)
    (z : ℕ × ℕ × ℕ) : ℝ :=
  if hd : 0 < z.1 then
    if hd' : 0 < z.2.1 then
      if z.1 * z.2.1 * z.2.2 ∣ n.1 ∧
          q.theta ^ k ≤ (z.1 : ℝ) ∧ (z.1 : ℝ) < q.theta ^ (k + 1) ∧
          Close q.theta ⟨z.1, hd⟩ ⟨z.2.1, hd'⟩ then
        (roughIndicator z.1 q.sigma : ℝ) *
          y.rpow (omegaBelowRaw (z.1 * z.2.2) (q.theta ^ k) : ℝ) *
          roughIndicator z.2.2 q.sigma
      else 0
    else 0
  else 0

lemma fkSharp_eq_triple_sum (q : Lemma4Parameters) (y : ℝ)
    (hy0 : 0 < y) (hy1 : y < 1) (n : PosNat) (k : ℕ) :
    fkSharp (sharpParametersOf q y hy0 hy1 k) n =
      (1 / tau n : ℝ) * ∑ z ∈ tripleUniverse n, sharpTermAt q y hy0 hy1 n k z := by
  unfold fkSharp tripleUniverse sharpTermAt sharpParametersOf
  simp only [Finset.sum_product]

lemma sharpTermAt_nonneg (q : Lemma4Parameters) (y : ℝ)
    (hy0 : 0 < y) (hy1 : y < 1) (n : PosNat) (k : ℕ)
    (z : ℕ × ℕ × ℕ) : 0 ≤ sharpTermAt q y hy0 hy1 n k z := by
  unfold sharpTermAt
  split_ifs
  · exact mul_nonneg
      (mul_nonneg (roughIndicator_nonneg z.1 q.sigma)
        (Real.rpow_nonneg (le_of_lt hy0) _))
      (roughIndicator_nonneg z.2.2 q.sigma)
  all_goals positivity

lemma triple_mem_universe (q : Lemma4Parameters) (n : PosNat)
    (hnrough : roughIndicator n.1 q.theta = 1) {x : ℕ × ℕ}
    (hx : x ∈ pairSet q n) : tripleOf x ∈ tripleUniverse n := by
  obtain ⟨_, _, hd, hd', ht, hD, hD', hdiv, _⟩ := pair_data q n hnrough hx
  have hdvd : (tripleOf x).1 ∣ n.1 :=
    (dvd_mul_right (tripleOf x).1 ((tripleOf x).2.1 * (tripleOf x).2.2)).trans
      (by simpa [mul_assoc] using hdiv)
  have hd'dvd : (tripleOf x).2.1 ∣ n.1 :=
    (dvd_mul_left (tripleOf x).2.1 ((tripleOf x).1 * (tripleOf x).2.2)).trans
      (by simpa [mul_comm, mul_left_comm, mul_assoc] using hdiv)
  have htdvd : (tripleOf x).2.2 ∣ n.1 :=
    (dvd_mul_left (tripleOf x).2.2 ((tripleOf x).1 * (tripleOf x).2.1)).trans
      (by simpa [mul_comm, mul_left_comm, mul_assoc] using hdiv)
  have hdle := Nat.le_of_dvd n.2 hdvd
  have hd'le := Nat.le_of_dvd n.2 hd'dvd
  have htle := Nat.le_of_dvd n.2 htdvd
  simp [tripleUniverse, positiveNatsUpTo, hd, hd', ht, hdle, hd'le, htle]

lemma pair_pointwise
    (q : Lemma4Parameters) (y : ℝ) (hy0 : 0 < y) (hy1 : y < 1)
    (n : PosNat) (hnU : goodU0 q.toGoodParameters < n.1)
    (hnrough : roughIndicator n.1 q.theta = 1) {x : ℕ × ℕ}
    (hx : x ∈ pairSet q n) :
    1 ≤ goodPowerMajorant q y (pairBin q x)
      ⟨x.1, (pair_data q n hnrough hx).1⟩ := by
  obtain ⟨hD, hD', hd, hd', ht, hDt, hD't, hdiv, hdr, htr,
    hne, hcloseL, hcloseR, hdge, hbinL, hbinR, hlower⟩ := pair_data q n hnrough hx
  obtain ⟨hxmem, hx'mem, hDx, hD'x, hclose, hrough, hgood⟩ :=
    (mem_pairSet_iff q n x.1 x.2).mp hx
  have hDdvd : x.1 ∣ n.1 := Nat.dvd_of_mem_divisors hxmem
  have hk1 : 1 ≤ pairBin q x := (le_max_left _ _).trans hlower
  have hhalf := lowerBin_half q hlower
  have hnroughP : IsRough n.1 q.theta := (roughIndicator_eq_one_iff _ _).mp hnrough
  have hdleD : (tripleOf x).1 ≤ x.1 := by
    rw [hDt]
    exact Nat.le_mul_of_pos_right (tripleOf x).1 ht
  have hpowN : q.theta ^ pairBin q x < n.1 := by
    have hdleD_real : ((tripleOf x).1 : ℝ) ≤ x.1 := by exact_mod_cast hdleD
    have hDlt_real : (x.1 : ℝ) < n.1 := by
      exact_mod_cast close_divisor_lt n ⟨x.1, hD⟩ ⟨x.2, hD'⟩
        (lt_of_lt_of_le (by norm_num) q.theta_ge_two) hnroughP hDdvd
        (Nat.dvd_of_mem_divisors hx'mem) hclose
    exact hbinL.trans_lt (hdleD_real.trans_lt hDlt_real)
  exact pointwise_bound q y hy0 hy1 n ⟨x.1, hD⟩ hnU hgood
    (pairBin q x) hk1 hhalf (hbinL.trans (by exact_mod_cast hdleD)) hpowN

lemma sharpTerm_tripleOf
    (q : Lemma4Parameters) (y : ℝ) (hy0 : 0 < y) (hy1 : y < 1)
    (n : PosNat) (hnrough : roughIndicator n.1 q.theta = 1)
    {x : ℕ × ℕ} (hx : x ∈ pairSet q n) :
    sharpTermAt q y hy0 hy1 n (pairBin q x) (tripleOf x) =
      y.rpow (omegaBelowRaw x.1 (q.theta ^ pairBin q x) : ℝ) := by
  obtain ⟨hD, hD', hd, hd', ht, hDt, hD't, hdiv, hdr, htr,
    hne, hcloseL, hcloseR, hdge, hbinL, hbinR, hlower⟩ := pair_data q n hnrough hx
  unfold sharpTermAt
  simp only [dif_pos hd, dif_pos hd']
  rw [if_pos]
  · rw [hdr, htr]
    norm_num
    congr 2
    exact hDt.symm
  · refine ⟨hdiv, hbinL, hbinR, ?_, hcloseL, hcloseR⟩
    intro heq
    exact hne (congr_arg Subtype.val heq)

lemma triple_sum_le_sharp_sum
    (q : Lemma4Parameters) (y : ℝ) (hy0 : 0 < y) (hy1 : y < 1)
    (n : PosNat) (hnrough : roughIndicator n.1 q.theta = 1) (k : ℕ) :
    ∑ x ∈ (pairSet q n).filter (fun x => pairBin q x = k),
        y.rpow (omegaBelowRaw x.1 (q.theta ^ k) : ℝ) ≤
      ∑ z ∈ tripleUniverse n, sharpTermAt q y hy0 hy1 n k z := by
  let s := (pairSet q n).filter (fun x => pairBin q x = k)
  let img := s.image tripleOf
  calc
    ∑ x ∈ s, y.rpow (omegaBelowRaw x.1 (q.theta ^ k) : ℝ) =
        ∑ z ∈ img, sharpTermAt q y hy0 hy1 n k z := by
      apply Finset.sum_bij (fun x hx => tripleOf x)
      · intro x hx
        exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
      · intro x hx z hz heq
        exact tripleOf_injective_on q n hnrough
          (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hz).1 heq
      · intro z hz
        rcases Finset.mem_image.mp hz with ⟨x, hx, rfl⟩
        exact ⟨x, hx, rfl⟩
      · intro x hx
        have hxpair := (Finset.mem_filter.mp hx).1
        have hxbin := (Finset.mem_filter.mp hx).2
        rw [← hxbin, sharpTerm_tripleOf q y hy0 hy1 n hnrough hxpair]
    _ ≤ ∑ z ∈ tripleUniverse n, sharpTermAt q y hy0 hy1 n k z := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro z hz
        rcases Finset.mem_image.mp hz with ⟨x, hx, rfl⟩
        exact triple_mem_universe q n hnrough (Finset.mem_filter.mp hx).1
      · intro z hzU hzImg
        exact sharpTermAt_nonneg q y hy0 hy1 n k z

lemma fiber_bound
    (q : Lemma4Parameters) (y : ℝ) (hy0 : 0 < y) (hy1 : y < 1)
    (n : PosNat) (hnU : goodU0 q.toGoodParameters < n.1)
    (hnrough : roughIndicator n.1 q.theta = 1) (k : ℕ) :
    ((pairSet q n).filter (fun x => pairBin q x = k)).card ≤
      (2 * Real.log q.xi * Real.log q.theta / Real.log q.sigma).rpow
          (-(1 / 2 + q.epsilonInt) * Real.log y) *
          (k : ℝ).rpow (-(1 / 2 + q.epsilonInt) * Real.log y) *
          ((tau n : ℝ) * fkSharp (sharpParametersOf q y hy0 hy1 k) n) := by
  let s := (pairSet q n).filter (fun x => pairBin q x = k)
  have hA0 : 0 ≤ 2 * Real.log q.xi * Real.log q.theta / Real.log q.sigma := by
    have hxi : 0 < Real.log q.xi := Real.log_pos q.xi_gt_one
    have htheta : 0 < Real.log q.theta := Real.log_pos
      (lt_of_lt_of_le (by norm_num) q.theta_ge_two)
    have hsigma : 0 < Real.log q.sigma := Real.log_pos
      (lt_of_lt_of_le (by norm_num) (q.theta_ge_two.trans q.sigma_ge_theta))
    positivity
  by_cases hs0 : s = ∅
  · simp [s, hs0]
    exact mul_nonneg
      (mul_nonneg (Real.rpow_nonneg hA0 _)
        (Real.rpow_nonneg (Nat.cast_nonneg k) _))
      (mul_nonneg (by positivity) (fkSharp_nonneg _ _))
  have hk1 : 1 ≤ k := by
    obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hs0
    have hxpair := (Finset.mem_filter.mp hx).1
    have hxbin := (Finset.mem_filter.mp hx).2
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hlower⟩ :=
      pair_data q n hnrough hxpair
    exact (le_max_left 1 _).trans (hlower.trans_eq hxbin)
  have hpoint : ∀ x ∈ s,
      (1 : ℝ) ≤
        (2 * Real.log q.xi * Real.log q.theta / Real.log q.sigma).rpow
            (-(1 / 2 + q.epsilonInt) * Real.log y) *
          (k : ℝ).rpow (-(1 / 2 + q.epsilonInt) * Real.log y) *
            y.rpow (omegaBelowRaw x.1 (q.theta ^ k) : ℝ) := by
    intro x hx
    have hxpair := (Finset.mem_filter.mp hx).1
    have hxbin := (Finset.mem_filter.mp hx).2
    have hpos := (pair_data q n hnrough hxpair).1
    have hp := pair_pointwise q y hy0 hy1 n hnU hnrough hxpair
    have hk1x : 1 ≤ pairBin q x := by simpa [hxbin] using hk1
    rw [split_majorant q y (pairBin q x) ⟨x.1, hpos⟩ hk1x] at hp
    simpa [omegaBelowRaw, hpos, hxbin] using hp
  have hsum : (s.card : ℝ) ≤
      ∑ x ∈ s,
        (2 * Real.log q.xi * Real.log q.theta / Real.log q.sigma).rpow
            (-(1 / 2 + q.epsilonInt) * Real.log y) *
          (k : ℝ).rpow (-(1 / 2 + q.epsilonInt) * Real.log y) *
            y.rpow (omegaBelowRaw x.1 (q.theta ^ k) : ℝ) := by
    simpa using Finset.sum_le_sum hpoint
  calc
    (s.card : ℝ) ≤ _ := hsum
    _ = (2 * Real.log q.xi * Real.log q.theta / Real.log q.sigma).rpow
          (-(1 / 2 + q.epsilonInt) * Real.log y) *
        (k : ℝ).rpow (-(1 / 2 + q.epsilonInt) * Real.log y) *
          ∑ x ∈ s, y.rpow (omegaBelowRaw x.1 (q.theta ^ k) : ℝ) := by
      rw [← Finset.mul_sum]
    _ ≤ (2 * Real.log q.xi * Real.log q.theta / Real.log q.sigma).rpow
          (-(1 / 2 + q.epsilonInt) * Real.log y) *
        (k : ℝ).rpow (-(1 / 2 + q.epsilonInt) * Real.log y) *
          (∑ z ∈ tripleUniverse n, sharpTermAt q y hy0 hy1 n k z) := by
      exact mul_le_mul_of_nonneg_left
        (triple_sum_le_sharp_sum q y hy0 hy1 n hnrough k)
        (mul_nonneg (Real.rpow_nonneg hA0 _)
          (Real.rpow_nonneg (Nat.cast_nonneg k) _))
    _ = _ := by
      rw [fkSharp_eq_triple_sum]
      have htau : (0 : ℝ) < tau n := by
        unfold tau divisorSet
        exact_mod_cast Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr n.2.ne'⟩
      field_simp [ne_of_gt htau]

theorem result : Erdos448.Stage6.TaskContracts.ROOT04Target := by
  intro q y hy0 hy1 n hnU
  let T : ℕ → ℝ := fun k =>
    if lowerBinIndex q.sigma q.theta ≤ k then
      (k : ℝ).rpow (-(1 / 2 + q.epsilonInt) * Real.log y) *
        fkSharp (sharpParametersOf q y hy0 hy1 k) n
    else 0
  have hsum : Summable T := majorant_summable q y hy0 hy1 n
  refine ⟨hsum, ?_⟩
  have hT0 : ∀ k, 0 ≤ T k := by
    intro k
    unfold T
    split_ifs
    · exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg k) _) (fkSharp_nonneg _ _)
    · exact le_rfl
  have hA0 : 0 ≤ 2 * Real.log q.xi * Real.log q.theta / Real.log q.sigma := by
    have hxi : 0 < Real.log q.xi := Real.log_pos q.xi_gt_one
    have htheta : 0 < Real.log q.theta := Real.log_pos
      (lt_of_lt_of_le (by norm_num) q.theta_ge_two)
    have hsigma : 0 < Real.log q.sigma := Real.log_pos
      (lt_of_lt_of_le (by norm_num) (q.theta_ge_two.trans q.sigma_ge_theta))
    positivity
  have hApow0 : 0 ≤
      (2 * Real.log q.xi * Real.log q.theta / Real.log q.sigma).rpow
        (-(1 / 2 + q.epsilonInt) * Real.log y) := Real.rpow_nonneg hA0 _
  by_cases hnrough : roughIndicator n.1 q.theta = 1
  · have htauNat : 0 < tau n := by
      unfold tau divisorSet
      exact Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr n.2.ne'⟩
    have htau : (0 : ℝ) < tau n := by exact_mod_cast htauNat
    let bins := (pairSet q n).image (pairBin q)
    have hcard_partition : ((pairSet q n).card : ℝ) =
        ∑ k ∈ bins, (((pairSet q n).filter (fun x => pairBin q x = k)).card : ℝ) := by
      exact_mod_cast Finset.card_eq_sum_card_image (pairBin q) (pairSet q n)
    have hbin_bound : ∀ k ∈ bins,
        (((pairSet q n).filter (fun x => pairBin q x = k)).card : ℝ) ≤
          (2 * Real.log q.xi * Real.log q.theta / Real.log q.sigma).rpow
              (-(1 / 2 + q.epsilonInt) * Real.log y) *
            ((tau n : ℝ) * T k) := by
      intro k hk
      rcases Finset.mem_image.mp hk with ⟨x, hx, rfl⟩
      have hlower := (pair_data q n hnrough hx).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
      have hf := fiber_bound q y hy0 hy1 n hnU hnrough (pairBin q x)
      rw [show T (pairBin q x) =
          (pairBin q x : ℝ).rpow (-(1 / 2 + q.epsilonInt) * Real.log y) *
            fkSharp (sharpParametersOf q y hy0 hy1 (pairBin q x)) n by
        simp [T, hlower]]
      convert hf using 1 <;> ring
    have hfinite : ((pairSet q n).card : ℝ) ≤
        (2 * Real.log q.xi * Real.log q.theta / Real.log q.sigma).rpow
            (-(1 / 2 + q.epsilonInt) * Real.log y) *
          ((tau n : ℝ) * ∑ k ∈ bins, T k) := by
      rw [hcard_partition]
      calc
        ∑ k ∈ bins, (((pairSet q n).filter (fun x => pairBin q x = k)).card : ℝ) ≤
            ∑ k ∈ bins,
              (2 * Real.log q.xi * Real.log q.theta / Real.log q.sigma).rpow
                  (-(1 / 2 + q.epsilonInt) * Real.log y) *
                ((tau n : ℝ) * T k) := Finset.sum_le_sum hbin_bound
        _ = _ := by
          rw [← Finset.mul_sum]
          congr 1
          rw [← Finset.mul_sum]
    have htoTsum : ∑ k ∈ bins, T k ≤ ∑' k, T k :=
      hsum.sum_le_tsum bins (fun k _ => hT0 k)
    have hcard : ((pairSet q n).card : ℝ) ≤
        (2 * Real.log q.xi * Real.log q.theta / Real.log q.sigma).rpow
            (-(1 / 2 + q.epsilonInt) * Real.log y) *
          ((tau n : ℝ) * ∑' k, T k) :=
      hfinite.trans (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left htoTsum (le_of_lt htau)) hApow0)
    unfold normalizedClosePair
    rw [hnrough, closePairSum_eq_pair_sum]
    simp only [Nat.cast_one, one_mul, Finset.sum_const, nsmul_eq_mul, mul_one]
    apply (div_le_iff₀ htau).2
    simpa [T, mul_comm, mul_left_comm, mul_assoc] using hcard
  · have hnzero : roughIndicator n.1 q.theta = 0 := by
      classical
      unfold roughIndicator at hnrough ⊢
      split_ifs at hnrough ⊢ <;> simp_all
    unfold normalizedClosePair
    rw [hnzero]
    simp only [Nat.cast_zero, zero_mul, zero_div]
    exact mul_nonneg hApow0 (tsum_nonneg hT0)

end

end Erdos448.Stage7.ROOT04.Work
