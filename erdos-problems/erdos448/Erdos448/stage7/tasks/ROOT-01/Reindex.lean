module

import all Mathlib.Basic.Real.Basic
public import Erdos448.stage7.tasks.«ROOT-01».Decomposition

public section

set_option backward.isDefEq.respectTransparency false

namespace Erdos448.Stage7.ROOT01

open Erdos448.Stage4
open Erdos448.Stage4.Contracts
open Finset Nat
open scoped BigOperators

noncomputable section

@[expose] def supportedCutoff (Ksh : PosNat) (x : ℝ) : Finset ℕ :=
  (positiveNatsBelow x).filter fun d => d.primeFactors ⊆ Ksh.1.primeFactors

@[expose] def coprimeCutoff (Ksh : PosNat) (x : ℝ) (d : ℕ) : Finset ℕ :=
  (positiveNatsBelow (x / (d : ℝ))).filter fun m => Nat.Coprime m Ksh.1

@[expose] def splitPairs (Ksh : PosNat) (x : ℝ) : Finset (ℕ × ℕ) :=
  ((positiveNatsBelow x).product (positiveNatsBelow x)).filter fun z =>
    z.1.primeFactors ⊆ Ksh.1.primeFactors ∧
      Nat.Coprime z.2 Ksh.1 ∧ (z.2 : ℝ) < x / (z.1 : ℝ)

@[expose] def pairTerm
    (u v : ArithmeticWeight) (Ksh : PosNat) (x : ℝ) (z : ℕ × ℕ) : ℝ :=
  u (Ksh.1 * z.1) * v z.1 *
    (u z.2 * v z.2 * (Real.log (x / (z.1 : ℝ)) + Real.log z.1))

lemma inner_mem_global
    {x : ℝ} (hx : 0 ≤ x) {d m : ℕ} (hd : 0 < d)
    (hm : m ∈ positiveNatsBelow (x / (d : ℝ))) :
    m ∈ positiveNatsBelow x := by
  have hm' := mem_positiveNatsBelow.mp hm
  have hdOne : (1 : ℝ) ≤ d := by exact_mod_cast hd
  apply mem_positiveNatsBelow.mpr
  exact ⟨hm'.1, hm'.2.trans_le (div_le_self hx hdOne)⟩

lemma splitPairs_characterization
    (Ksh : PosNat) {x : ℝ} (hx : 0 ≤ x) (z : ℕ × ℕ) :
    z ∈ splitPairs Ksh x ↔
      z.1 ∈ supportedCutoff Ksh x ∧ z.2 ∈ coprimeCutoff Ksh x z.1 := by
  constructor
  · intro hz
    rcases Finset.mem_filter.mp hz with ⟨hzProd, hzCond⟩
    rcases Finset.mem_product.mp hzProd with ⟨hdX, hmX⟩
    have hzCond' : z.1.primeFactors ⊆ Ksh.1.primeFactors ∧
        Nat.Coprime z.2 Ksh.1 ∧ (z.2 : ℝ) < x / (z.1 : ℝ) :=
      hzCond
    constructor
    · exact Finset.mem_filter.mpr ⟨hdX, by simpa using hzCond'.1⟩
    · exact Finset.mem_filter.mpr
        ⟨mem_positiveNatsBelow.mpr
          ⟨(mem_positiveNatsBelow.mp hmX).1, hzCond'.2.2⟩,
          by simpa using hzCond'.2.1⟩
  · rintro ⟨hdS, hmC⟩
    rcases Finset.mem_filter.mp hdS with ⟨hdX, hdSuppB⟩
    rcases Finset.mem_filter.mp hmC with ⟨hmQ, hmCopB⟩
    have hdSupp : z.1.primeFactors ⊆ Ksh.1.primeFactors := hdSuppB
    have hmCop : Nat.Coprime z.2 Ksh.1 := hmCopB
    have hdPos := (mem_positiveNatsBelow.mp hdX).1
    have hmX : z.2 ∈ positiveNatsBelow x := inner_mem_global hx hdPos hmQ
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨hdX, hmX⟩, ?_⟩
    exact ⟨hdSupp, hmCop, (mem_positiveNatsBelow.mp hmQ).2⟩

lemma pair_product_mem
    (Ksh : PosNat) {x : ℝ} (hx : 0 < x) {z : ℕ × ℕ}
    (hz : z ∈ splitPairs Ksh x) : z.1 * z.2 ∈ positiveNatsBelow x := by
  have hz' := (splitPairs_characterization Ksh hx.le z).mp hz
  have hd := mem_positiveNatsBelow.mp (Finset.mem_filter.mp hz'.1).1
  have hm := mem_positiveNatsBelow.mp (Finset.mem_filter.mp hz'.2).1
  apply mem_positiveNatsBelow.mpr
  refine ⟨Nat.mul_pos hd.1 hm.1, ?_⟩
  have hdR : (0 : ℝ) < z.1 := by exact_mod_cast hd.1
  have hmLt : (z.2 : ℝ) < x / (z.1 : ℝ) := hm.2
  rw [lt_div_iff₀ hdR] at hmLt
  simpa [Nat.cast_mul, mul_comm] using hmLt

lemma split_of_cutoff_mem
    (Ksh : PosNat) {x : ℝ} (hx : 0 < x) {n : ℕ}
    (hnX : n ∈ positiveNatsBelow x) :
    (commonPart Ksh n, awayPart Ksh n) ∈ splitPairs Ksh x := by
  have hn := mem_positiveNatsBelow.mp hnX
  have hd := commonPart_pos Ksh hn.1
  have hm := awayPart_pos Ksh hn.1
  have hmul := commonPart_mul_awayPart Ksh hn.1
  have hdLe : commonPart Ksh n ≤ n := by
    calc
      commonPart Ksh n ≤ commonPart Ksh n * awayPart Ksh n :=
        Nat.le_mul_of_pos_right _ hm
      _ = n := hmul
  have hmLe : awayPart Ksh n ≤ n := by
    calc
      awayPart Ksh n ≤ commonPart Ksh n * awayPart Ksh n :=
        Nat.le_mul_of_pos_left _ hd
      _ = n := hmul
  have hdX : commonPart Ksh n ∈ positiveNatsBelow x :=
    mem_positiveNatsBelow.mpr ⟨hd, (by exact_mod_cast hdLe :
      (commonPart Ksh n : ℝ) ≤ n).trans_lt hn.2⟩
  have hmX : awayPart Ksh n ∈ positiveNatsBelow x :=
    mem_positiveNatsBelow.mpr ⟨hm, (by exact_mod_cast hmLe :
      (awayPart Ksh n : ℝ) ≤ n).trans_lt hn.2⟩
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_product.mpr ⟨hdX, hmX⟩, ?_⟩
  refine ⟨commonPart_primeSupport Ksh hn.1, awayPart_coprime Ksh n, ?_⟩
  have hdR : (0 : ℝ) < commonPart Ksh n := by exact_mod_cast hd
  rw [lt_div_iff₀ hdR]
  have hprodLt : ((commonPart Ksh n * awayPart Ksh n : ℕ) : ℝ) < x := by
    calc
      ((commonPart Ksh n * awayPart Ksh n : ℕ) : ℝ) = (n : ℝ) := by
        exact_mod_cast hmul
      _ < x := hn.2
  simpa [Nat.cast_mul, mul_comm] using hprodLt

lemma pairTerm_identity
    (u v : ArithmeticWeight)
    (hu : NonnegativeMultiplicativeWeight u)
    (hv : NonnegativeMultiplicativeWeight v)
    (Ksh : PosNat) {x : ℝ} (hx : 0 < x) {z : ℕ × ℕ}
    (hz : z ∈ splitPairs Ksh x) :
    u (Ksh.1 * (z.1 * z.2)) * v (z.1 * z.2) * Real.log x =
      pairTerm u v Ksh x z := by
  have hz' := (splitPairs_characterization Ksh hx.le z).mp hz
  have hdX := (Finset.mem_filter.mp hz'.1).1
  have hmQ := (Finset.mem_filter.mp hz'.2).1
  have hd := (mem_positiveNatsBelow.mp hdX).1
  have hm := (mem_positiveNatsBelow.mp hmQ).1
  have hdSupp : HasPrimeSupportIn ⟨z.1, hd⟩ Ksh :=
    (Finset.mem_filter.mp hz'.1).2
  have hmK : Nat.Coprime z.2 Ksh.1 :=
    (Finset.mem_filter.mp hz'.2).2
  have hdm : Nat.Coprime z.1 z.2 :=
    supported_coprime_of_coprime_K Ksh ⟨z.1, hd⟩ ⟨z.2, hm⟩ hdSupp hmK
  have hKdm : Nat.Coprime (Ksh.1 * z.1) z.2 :=
    Nat.Coprime.mul_left hmK.symm hdm
  have hlog : Real.log (x / (z.1 : ℝ)) + Real.log z.1 = Real.log x := by
    rw [Real.log_div (ne_of_gt hx) (by exact_mod_cast (Nat.ne_of_gt hd))]
    ring
  unfold pairTerm
  rw [← Nat.mul_assoc,
    hu.multiplicative.2 _ _ (Nat.mul_pos Ksh.2 hd) hm hKdm,
    hv.multiplicative.2 _ _ hd hm hdm, hlog]
  ring

lemma finite_reindex
    (u v : ArithmeticWeight)
    (hu : NonnegativeMultiplicativeWeight u)
    (hv : NonnegativeMultiplicativeWeight v)
    (Ksh : PosNat) {x : ℝ} (hx : 0 < x) :
    (∑ n ∈ positiveNatsBelow x,
      u (Ksh.1 * n) * v n * Real.log x) =
    ∑ z ∈ splitPairs Ksh x, pairTerm u v Ksh x z := by
  apply Finset.sum_bij'
    (fun n _ => (commonPart Ksh n, awayPart Ksh n))
    (fun z _ => z.1 * z.2)
  · intro n hn
    exact split_of_cutoff_mem Ksh hx hn
  · intro z hz
    exact pair_product_mem Ksh hx hz
  · intro n hn
    exact commonPart_mul_awayPart Ksh (mem_positiveNatsBelow.mp hn).1
  · intro z hz
    have hz' := (splitPairs_characterization Ksh hx.le z).mp hz
    have hdX := (Finset.mem_filter.mp hz'.1).1
    have hmQ := (Finset.mem_filter.mp hz'.2).1
    have hd := (mem_positiveNatsBelow.mp hdX).1
    have hm := (mem_positiveNatsBelow.mp hmQ).1
    have hdSupp : HasPrimeSupportIn ⟨z.1, hd⟩ Ksh :=
      (Finset.mem_filter.mp hz'.1).2
    have hmK : Nat.Coprime z.2 Ksh.1 :=
      (Finset.mem_filter.mp hz'.2).2
    have hsplit := split_unique Ksh (Nat.mul_pos hd hm) hd hm rfl hdSupp hmK
    exact Prod.ext hsplit.1 hsplit.2
  · intro n hn
    have hz := split_of_cutoff_mem Ksh hx hn
    have hmul := commonPart_mul_awayPart Ksh (mem_positiveNatsBelow.mp hn).1
    calc
      u (Ksh.1 * n) * v n * Real.log x =
          u (Ksh.1 * (commonPart Ksh n * awayPart Ksh n)) *
            v (commonPart Ksh n * awayPart Ksh n) * Real.log x := by rw [hmul]
      _ = pairTerm u v Ksh x (commonPart Ksh n, awayPart Ksh n) :=
        pairTerm_identity u v hu hv Ksh hx hz

lemma pair_sum_eq_common_sum
    (u v : ArithmeticWeight) (Ksh : PosNat) {x : ℝ} (hx : 0 < x) :
    (∑ z ∈ splitPairs Ksh x, pairTerm u v Ksh x z) =
      ∑ d ∈ positiveNatsBelow x, commonPrimeTerm u v Ksh x d := by
  let D := positiveNatsBelow x
  let S := supportedCutoff Ksh x
  let T := coprimeCutoff Ksh x
  have hprod :
      (∑ z ∈ splitPairs Ksh x, pairTerm u v Ksh x z) =
        ∑ d ∈ S, ∑ m ∈ T d, pairTerm u v Ksh x (d, m) := by
    apply Finset.sum_finset_product (splitPairs Ksh x) S T
    intro z
    exact splitPairs_characterization Ksh hx.le z
  rw [hprod]
  symm
  change (∑ d ∈ D, commonPrimeTerm u v Ksh x d) = _
  dsimp [S, supportedCutoff]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d hdD
  have hd := (mem_positiveNatsBelow.mp hdD).1
  by_cases hs : d.primeFactors ⊆ Ksh.1.primeFactors
  · rw [if_pos hs]
    unfold commonPrimeTerm
    rw [dif_pos hd, if_pos (show HasPrimeSupportIn ⟨d, hd⟩ Ksh from hs)]
    dsimp [T, coprimeCutoff]
    rw [Finset.sum_filter, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m hm
    by_cases hcop : Nat.Coprime m Ksh.1
    · rw [if_pos hcop, if_pos hcop]
      rfl
    · rw [if_neg hcop, if_neg hcop]
      ring
  · rw [if_neg hs]
    unfold commonPrimeTerm
    rw [dif_pos hd, if_neg (show ¬HasPrimeSupportIn ⟨d, hd⟩ Ksh from hs)]

theorem p001 : P001Statement := by
  intro u v hu hv Ksh x hx hsum
  have hxPos : 0 < x := lt_of_lt_of_le (by norm_num) hx
  unfold shiftedLogMean
  rw [finite_reindex u v hu hv Ksh hxPos,
    pair_sum_eq_common_sum u v Ksh hxPos]
  symm
  apply tsum_eq_sum
  intro d hd
  by_contra hdne
  exact hd (mem_positiveNatsBelow.mpr (exactOuterSupport u v Ksh x d hdne))

end

end Erdos448.Stage7.ROOT01
