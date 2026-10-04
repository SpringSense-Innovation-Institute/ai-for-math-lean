module

import all Mathlib.Basic.Real.Basic
public import Erdos448.stage6.TaskContracts

public section

set_option backward.isDefEq.respectTransparency false

namespace Erdos448.Stage7.ROOT03.Work

open Finset Set
open scoped BigOperators

open Erdos448.Stage4
open Erdos448.Stage4.Contracts
open Erdos448.Stage6.TaskContracts

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

@[expose] def goodDivisors (q : Lemma4Parameters) (n : PosNat) : Finset ℕ :=
  (divisorSet n).filter fun d =>
    roughIndicator d q.sigma * goodIndicator q.toGoodParameters n.1 d = 1

@[expose] noncomputable def binIndex (q : Lemma4Parameters) (d : ℕ) : ℕ :=
  if hd : 0 < d then
    Classical.choose
      (exists_nat_pow_near (show (1 : ℝ) ≤ d by exact_mod_cast hd)
        (lt_of_lt_of_le (by norm_num) q.theta_ge_two))
  else 0

lemma binIndex_spec (q : Lemma4Parameters) {d : ℕ} (hd : 0 < d) :
    q.theta ^ binIndex q d ≤ (d : ℝ) ∧
      (d : ℝ) < q.theta ^ (binIndex q d + 1) := by
  rw [binIndex, dif_pos hd]
  exact Classical.choose_spec
    (exists_nat_pow_near (show (1 : ℝ) ≤ d by exact_mod_cast hd)
      (lt_of_lt_of_le (by norm_num) q.theta_ge_two))

lemma same_bin_close (q : Lemma4Parameters) {k d d' : ℕ}
    (hd : 0 < d) (hd' : 0 < d') (hne : d ≠ d')
    (hdk : q.theta ^ k ≤ (d : ℝ))
    (hdk' : (d : ℝ) < q.theta ^ (k + 1))
    (hd'k : q.theta ^ k ≤ (d' : ℝ))
    (hd'k' : (d' : ℝ) < q.theta ^ (k + 1)) :
    Close q.theta ⟨d, hd⟩ ⟨d', hd'⟩ := by
  have htheta : 0 < q.theta := lt_of_lt_of_le (by norm_num) q.theta_ge_two
  have hpow : q.theta ^ (k + 1) = q.theta ^ k * q.theta := by
    rw [pow_succ]
  refine ⟨by simpa using hne, ?_, ?_⟩
  · change 1 / q.theta < (d' : ℝ) / (d : ℝ)
    apply (lt_div_iff₀ (show (0 : ℝ) < d by exact_mod_cast hd)).2
    rw [show (1 / q.theta) * (d : ℝ) = (d : ℝ) / q.theta by ring]
    apply (div_lt_iff₀ htheta).2
    rw [hpow] at hdk'
    nlinarith
  · change (d' : ℝ) / (d : ℝ) < q.theta
    rw [div_lt_iff₀ (show (0 : ℝ) < d by exact_mod_cast hd)]
    rw [hpow] at hd'k'
    nlinarith

lemma mem_occupiedBins_of_divisor (q : Lemma4Parameters) (n : PosNat)
    {d : ℕ} (hddiv : d ∈ divisorSet n) :
    binIndex q d ∈ occupiedBins n q.theta := by
  have hd : 0 < d := Nat.pos_of_mem_divisors hddiv
  have htheta : 1 < q.theta := lt_of_lt_of_le (by norm_num) q.theta_ge_two
  have htheta_pos : 0 < q.theta := lt_trans (by norm_num) htheta
  have hlogtheta : 0 < Real.log q.theta := Real.log_pos htheta
  have hdn : d ≤ n.1 := Nat.le_of_dvd n.2 (Nat.dvd_of_mem_divisors hddiv)
  have hspec := binIndex_spec q hd
  have hpow_le_n : q.theta ^ binIndex q d ≤ (n.1 : ℝ) := by
    exact hspec.1.trans (by exact_mod_cast hdn)
  have hnreal : (0 : ℝ) < n.1 := by exact_mod_cast n.2
  have hlog_le : Real.log (q.theta ^ binIndex q d) ≤ Real.log (n.1 : ℝ) :=
    Real.strictMonoOn_log.monotoneOn
      (pow_pos htheta_pos _) hnreal hpow_le_n
  rw [Real.log_pow] at hlog_le
  have hratio : (binIndex q d : ℝ) ≤ Real.log (n.1 : ℝ) / Real.log q.theta := by
    apply (le_div_iff₀ hlogtheta).2
    simpa [mul_comm] using hlog_le
  have hceilReal : (binIndex q d : ℝ) ≤
      (Nat.ceil (Real.log (n.1 : ℝ) / Real.log q.theta) : ℝ) :=
    hratio.trans (Nat.le_ceil _)
  have hceilNat : binIndex q d ≤
      Nat.ceil (Real.log (n.1 : ℝ) / Real.log q.theta) := by
    exact_mod_cast hceilReal
  rw [occupiedBins, if_pos htheta]
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨Nat.lt_succ_of_le hceilNat, ⟨d, hddiv, hspec⟩⟩

@[expose] def usedBins (q : Lemma4Parameters) (n : PosNat) : Finset ℕ :=
  (goodDivisors q n).image (binIndex q)

@[expose] def fiberCard (q : Lemma4Parameters) (n : PosNat) (k : ℕ) : ℕ :=
  ((goodDivisors q n).filter fun d => binIndex q d = k).card

lemma usedBins_card_le (q : Lemma4Parameters) (n : PosNat) :
    (usedBins q n).card ≤ tauPlus n q.theta := by
  rw [tauPlus]
  apply Finset.card_le_card
  intro k hk
  rw [usedBins, Finset.mem_image] at hk
  obtain ⟨d, hdg, rfl⟩ := hk
  exact mem_occupiedBins_of_divisor q n (Finset.mem_filter.mp hdg).1

lemma indicator_product_eq_ite (q : Lemma4Parameters) (n : PosNat) (d : ℕ) :
    roughIndicator d q.sigma * goodIndicator q.toGoodParameters n.1 d =
      if roughIndicator d q.sigma * goodIndicator q.toGoodParameters n.1 d = 1
      then 1 else 0 := by
  have hr : roughIndicator d q.sigma = 0 ∨ roughIndicator d q.sigma = 1 := by
    unfold roughIndicator
    split_ifs <;> simp
  have hg : goodIndicator q.toGoodParameters n.1 d = 0 ∨
      goodIndicator q.toGoodParameters n.1 d = 1 := by
    unfold goodIndicator
    split_ifs <;> simp
  rcases hr with hr | hr <;> rcases hg with hg | hg <;> simp [hr, hg]

lemma mass_eq_good_card (q : Lemma4Parameters) (n : PosNat) :
    lemma4GoodDivisorMass q n = (goodDivisors q n).card := by
  rw [lemma4GoodDivisorMass, goodDivisors]
  calc
    (∑ d ∈ divisorSet n,
        roughIndicator d q.sigma * goodIndicator q.toGoodParameters n.1 d) =
        ∑ d ∈ divisorSet n,
          if roughIndicator d q.sigma * goodIndicator q.toGoodParameters n.1 d = 1
          then 1 else 0 := by
            apply Finset.sum_congr rfl
            intro d _
            exact indicator_product_eq_ite q n d
    _ = ((divisorSet n).filter fun d =>
        roughIndicator d q.sigma * goodIndicator q.toGoodParameters n.1 d = 1).card := by
          simp

lemma mass_le_roughTau (q : Lemma4Parameters) (n : PosNat) :
    lemma4GoodDivisorMass q n ≤ roughTau n q.sigma := by
  rw [lemma4GoodDivisorMass, roughTau]
  apply Finset.sum_le_sum
  intro d _
  unfold roughIndicator goodIndicator
  split_ifs <;> simp

lemma roughTau_pos (q : Lemma4Parameters) (n : PosNat) :
    0 < roughTau n q.sigma := by
  have hone : 1 ∈ divisorSet n := Nat.one_mem_divisors.mpr n.2.ne'
  have hrough : roughIndicator 1 q.sigma = 1 := by
    have h : IsRough 1 q.sigma := by
      intro p hp hpdiv
      have hpone : p = 1 := Nat.dvd_one.mp hpdiv
      subst p
      exact (Nat.not_prime_one hp).elim
    simp [roughIndicator, h]
  rw [roughTau]
  have hle : roughIndicator 1 q.sigma ≤ ∑ d ∈ divisorSet n, roughIndicator d q.sigma := by
    exact Finset.single_le_sum (s := divisorSet n)
      (f := fun d => roughIndicator d q.sigma) (fun d _ => Nat.zero_le _) hone
  omega

lemma tauPlus_pos (q : Lemma4Parameters) (n : PosNat) :
    0 < tauPlus n q.theta := by
  rw [tauPlus, Finset.card_pos]
  refine ⟨0, ?_⟩
  have htheta : 1 < q.theta := lt_of_lt_of_le (by norm_num) q.theta_ge_two
  rw [occupiedBins, if_pos htheta]
  simp only [Finset.mem_filter, Finset.mem_range]
  refine ⟨Nat.succ_pos _, ?_⟩
  refine ⟨1, Nat.one_mem_divisors.mpr n.2.ne', ?_, ?_⟩
  · norm_num
  · simpa using htheta

@[expose] def equalBinPairs (q : Lemma4Parameters) (n : PosNat) : Finset (ℕ × ℕ) :=
  ((goodDivisors q n).product (goodDivisors q n)).filter fun p =>
    binIndex q p.1 = binIndex q p.2

@[expose] def unequalBinPairs (q : Lemma4Parameters) (n : PosNat) : Finset (ℕ × ℕ) :=
  (equalBinPairs q n).filter fun p => p.1 ≠ p.2

lemma equalBinPairs_card_eq (q : Lemma4Parameters) (n : PosNat) :
    (equalBinPairs q n).card =
      ∑ k ∈ usedBins q n, (fiberCard q n k) ^ 2 := by
  have hmap : ((equalBinPairs q n : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)).MapsTo
      (fun p => binIndex q p.1) (usedBins q n : Set ℕ) := by
    intro p hp
    change p ∈ equalBinPairs q n at hp
    rw [equalBinPairs, Finset.mem_filter] at hp
    have hg := Finset.mem_product.mp hp.1
    exact Finset.mem_image.mpr ⟨p.1, hg.1, rfl⟩
  rw [Finset.card_eq_sum_card_fiberwise hmap]
  apply Finset.sum_congr rfl
  intro k hk
  have heq :
      ((equalBinPairs q n).filter fun p => binIndex q p.1 = k) =
        (((goodDivisors q n).filter fun d => binIndex q d = k).product
          ((goodDivisors q n).filter fun d => binIndex q d = k)) := by
    ext p
    simp [equalBinPairs, and_left_comm, and_assoc]
    aesop
  rw [heq]
  simp [fiberCard, pow_two]

lemma diagonal_card_le (q : Lemma4Parameters) (n : PosNat) :
    ((equalBinPairs q n).filter fun p => p.1 = p.2).card ≤
      (goodDivisors q n).card := by
  let diag : Finset (ℕ × ℕ) := (goodDivisors q n).image fun d => (d, d)
  calc
    ((equalBinPairs q n).filter fun p => p.1 = p.2).card ≤ diag.card := by
      apply Finset.card_le_card
      intro p hp
      rw [Finset.mem_filter] at hp
      have hpEq := hp.2
      have hpbase := hp.1
      change p ∈ equalBinPairs q n at hpbase
      rw [show p = (p.1, p.1) by ext <;> simp [hpEq]]
      have hp' := Finset.mem_filter.mp hpbase
      exact Finset.mem_image.mpr ⟨p.1, (Finset.mem_product.mp hp'.1).1, rfl⟩
    _ ≤ (goodDivisors q n).card := Finset.card_image_le

lemma equalBinPairs_card_le (q : Lemma4Parameters) (n : PosNat) :
    (equalBinPairs q n).card ≤
      (unequalBinPairs q n).card + (goodDivisors q n).card := by
  let diagonal := (equalBinPairs q n).filter fun p => p.1 = p.2
  calc
    (equalBinPairs q n).card ≤ (unequalBinPairs q n ∪ diagonal).card := by
      apply Finset.card_le_card
      intro p hp
      by_cases hne : p.1 ≠ p.2
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hp, hne⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hp, not_ne_iff.mp hne⟩)
    _ ≤ (unequalBinPairs q n).card + diagonal.card :=
      Finset.card_union_le _ _
    _ ≤ (unequalBinPairs q n).card + (goodDivisors q n).card := by
      exact Nat.add_le_add_left (diagonal_card_le q n) _

lemma unequal_pairs_le_close_sum (q : Lemma4Parameters) (n : PosNat) :
    ((unequalBinPairs q n).card : ℝ) ≤ closePairSum q n := by
  let term : ℕ × ℕ → ℝ := fun p =>
    if hd : 0 < p.1 then
      if hd' : 0 < p.2 then
        if Close q.theta ⟨p.1, hd⟩ ⟨p.2, hd'⟩ then
          (roughIndicator p.1 q.sigma : ℝ) *
            goodIndicator q.toGoodParameters n.1 p.1
        else 0
      else 0
    else 0
  have hsubset : unequalBinPairs q n ⊆
      (divisorSet n).product (divisorSet n) := by
    intro p hp
    have hp' := Finset.mem_filter.mp hp
    have hpair := Finset.mem_filter.mp hp'.1
    have hg := Finset.mem_product.mp hpair.1
    exact Finset.mem_product.mpr
      ⟨(Finset.mem_filter.mp hg.1).1, (Finset.mem_filter.mp hg.2).1⟩
  have hterm_nonneg : ∀ p ∈ (divisorSet n).product (divisorSet n), 0 ≤ term p := by
    intro p hp
    unfold term
    split_ifs <;> positivity
  calc
    ((unequalBinPairs q n).card : ℝ) =
        ∑ p ∈ unequalBinPairs q n, term p := by
      rw [Finset.card_eq_sum_ones, Nat.cast_sum]
      simp only [Nat.cast_one]
      apply Finset.sum_congr rfl
      intro p hp
      have hp' := Finset.mem_filter.mp hp
      have hpair := Finset.mem_filter.mp hp'.1
      have hg := Finset.mem_product.mp hpair.1
      have hd : 0 < p.1 := Nat.pos_of_mem_divisors (Finset.mem_filter.mp hg.1).1
      have hd' : 0 < p.2 := Nat.pos_of_mem_divisors (Finset.mem_filter.mp hg.2).1
      have hs1 := binIndex_spec q hd
      have hs2 := binIndex_spec q hd'
      have hclose : Close q.theta ⟨p.1, hd⟩ ⟨p.2, hd'⟩ := by
        apply same_bin_close q hd hd' hp'.2 hs1.1 hs1.2
        · simpa [hpair.2] using hs2.1
        · simpa [hpair.2] using hs2.2
      have hgood := (Finset.mem_filter.mp hg.1).2
      dsimp [term]
      rw [dif_pos hd, dif_pos hd', if_pos hclose]
      exact_mod_cast hgood.symm
    _ ≤ ∑ p ∈ (divisorSet n).product (divisorSet n), term p :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun p hp _ => hterm_nonneg p hp)
    _ = closePairSum q n := by
      simp [term, closePairSum, Finset.sum_product]

lemma good_card_energy_bound (q : Lemma4Parameters) (n : PosNat) :
    ((goodDivisors q n).card : ℝ) ^ 2 ≤
      (tauPlus n q.theta : ℝ) *
        (closePairSum q n + (goodDivisors q n).card) := by
  have hcard_sum : (goodDivisors q n).card =
      ∑ k ∈ usedBins q n, fiberCard q n k :=
    Finset.card_eq_sum_card_image (binIndex q) (goodDivisors q n)
  have hcauchy :
      ((∑ k ∈ usedBins q n, (fiberCard q n k : ℝ)) ^ 2) ≤
        ((usedBins q n).card : ℝ) *
          ∑ k ∈ usedBins q n, (fiberCard q n k : ℝ) ^ 2 := by
    simpa using sq_sum_le_card_mul_sum_sq
      (s := usedBins q n) (f := fun k => (fiberCard q n k : ℝ))
  have henergyNat := equalBinPairs_card_le q n
  have henergy : ((equalBinPairs q n).card : ℝ) ≤
      (unequalBinPairs q n).card + (goodDivisors q n).card := by
    exact_mod_cast henergyNat
  have hpair := unequal_pairs_le_close_sum q n
  have hclose_nonneg : 0 ≤ closePairSum q n := by
    rw [closePairSum]
    apply Finset.sum_nonneg
    intro d hd
    apply Finset.sum_nonneg
    intro d' hd'
    split_ifs <;> positivity
  calc
    ((goodDivisors q n).card : ℝ) ^ 2 =
        (∑ k ∈ usedBins q n, (fiberCard q n k : ℝ)) ^ 2 := by
      congr 1
      exact_mod_cast hcard_sum
    _ ≤ ((usedBins q n).card : ℝ) *
        ∑ k ∈ usedBins q n, (fiberCard q n k : ℝ) ^ 2 := hcauchy
    _ = ((usedBins q n).card : ℝ) * (equalBinPairs q n).card := by
      rw [equalBinPairs_card_eq]
      norm_cast
    _ ≤ (tauPlus n q.theta : ℝ) *
        (closePairSum q n + (goodDivisors q n).card) := by
      apply mul_le_mul
      · exact_mod_cast usedBins_card_le q n
      · exact henergy.trans (by
          simpa [add_comm] using
            (add_le_add_right hpair ((goodDivisors q n).card : ℝ)))
      · positivity
      · positivity

theorem p034 : P034Statement := by
  intro q A hA n hn
  have hroughNat : 0 < roughTau n q.sigma := roughTau_pos q n
  have hoccupiedNat : 0 < tauPlus n q.theta := tauPlus_pos q n
  refine ⟨hroughNat, hoccupiedNat, ?_⟩
  have hmass := hA.2.2 n.1 hn n.2
  have hmassCardNat := mass_eq_good_card q n
  have hmassLower : (9 / 10 : ℝ) * roughTau n q.sigma ≤
      ((goodDivisors q n).card : ℝ) := by
    simpa [hmassCardNat] using hmass
  have hmassUpperNat := mass_le_roughTau q n
  have hmassUpper : ((goodDivisors q n).card : ℝ) ≤ roughTau n q.sigma := by
    rw [← mass_eq_good_card q n]
    exact_mod_cast hmassUpperNat
  have henergy := good_card_energy_bound q n
  have hrough : (0 : ℝ) < roughTau n q.sigma := by exact_mod_cast hroughNat
  have hoccupied : (0 : ℝ) < tauPlus n q.theta := by exact_mod_cast hoccupiedNat
  have hcore :
      (4 / 5 : ℝ) * (roughTau n q.sigma : ℝ) ^ 2 ≤
        (tauPlus n q.theta : ℝ) *
          (closePairSum q n + roughTau n q.sigma) := by
    calc
      (4 / 5 : ℝ) * (roughTau n q.sigma : ℝ) ^ 2 ≤
          ((9 / 10 : ℝ) * roughTau n q.sigma) ^ 2 := by nlinarith [sq_nonneg (roughTau n q.sigma : ℝ)]
      _ ≤ ((goodDivisors q n).card : ℝ) ^ 2 := by nlinarith
      _ ≤ (tauPlus n q.theta : ℝ) *
          (closePairSum q n + (goodDivisors q n).card) := henergy
      _ ≤ (tauPlus n q.theta : ℝ) *
          (closePairSum q n + roughTau n q.sigma) := by
        gcongr
  rw [show (4 / 5 : ℝ) * ((roughTau n q.sigma : ℝ) / tauPlus n q.theta) =
      ((4 / 5 : ℝ) * roughTau n q.sigma) / tauPlus n q.theta by ring]
  rw [show (1 : ℝ) + closePairSum q n / roughTau n q.sigma =
      ((roughTau n q.sigma : ℝ) + closePairSum q n) / roughTau n q.sigma by
        field_simp]
  rw [div_le_div_iff₀ hoccupied hrough]
  simpa [pow_two, mul_add, add_mul, add_comm, mul_comm, mul_left_comm, mul_assoc] using hcore

theorem result : ROOT03Target := by
  exact p034

#check result
#print axioms result

end

end Erdos448.Stage7.ROOT03.Work
