module

public import Erdos745.WrapUp.Contracts
public import Erdos745.WrapUp.Proofs.Internal.Linked.W04_Near
public import Erdos745.WrapUp.Proofs.Internal.Linked.W04_Entropy
public import Erdos745.WrapUp.Proofs.Internal.Linked.W06_P02
public import Erdos745.WrapUp.Proofs.Internal.Linked.W04_Finite

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local simp] Pi.div_def Pi.mul_def Pi.add_def Pi.sub_def Pi.neg_def Pi.inv_def Function.comp_def Pi.pow_def Pi.smul_def Real.rpow_eq_pow

@[expose] public section


/-!
The finite summation and polynomial-absorption part of W04's fixed-density
far-tail argument.  The input envelope is the pointwise conclusion of the
conditioned fixed-density estimate in the packet.  This module proves that
such an envelope, uniformly over any predicate on `(n,M)`, yields exactly the
weighted `tupleTail` decay required by the public consumer.
-/
namespace Erdos745.WrapUp.Proofs.Internal.W04_TUPLES_Tails

noncomputable section
open scoped BigOperators

private theorem tupleWeight_le
    (n q power : ℕ) (ks : Fin q → Fin (n + 1)) :
    (∏ i, (((ks i).val : ℝ) ^ power)) ≤
      (n : ℝ) ^ (power * q) := by
  calc
    (∏ i, (((ks i).val : ℝ) ^ power))
        ≤ ∏ _i : Fin q, ((n : ℝ) ^ power) := by
          apply Finset.prod_le_prod₀
          · intro i hi
            positivity
          · intro i hi
            gcongr
            exact_mod_cast (Fin.le_last (ks i))
    _ = ((n : ℝ) ^ power) ^ q := by simp
    _ = (n : ℝ) ^ (power * q) := by rw [← pow_mul]

theorem tupleTail_le_expEnvelope
    (n M q power d : ℕ) (B D c : ℝ)
    (hD : 0 ≤ D) (hc : 0 < c)
    (henv : ∀ ks : Fin q → ℕ, (∀ i, 0 < ks i) →
      tupleMoment n M q ks ≤
        D * (n : ℝ) ^ d *
          Real.exp (-c * ∑ i, (ks i : ℝ))) :
    tupleTail n M q power B ≤
      ((n + 1 : ℕ) : ℝ) ^ q *
        ((n : ℝ) ^ (power * q) *
          (D * (n : ℝ) ^ d *
            Real.exp (-c * (B * Real.log n)))) := by
  unfold tupleTail
  let R : ℝ := (n : ℝ) ^ (power * q) *
    (D * (n : ℝ) ^ d * Real.exp (-c * (B * Real.log n)))
  have hR : 0 ≤ R := by
    dsimp [R]
    positivity
  calc
    (∑ ks : Fin q → Fin (n + 1),
      if (∀ i, 0 < (ks i).val) ∧
          (∃ i, B * Real.log n < ((ks i).val : ℝ)) then
        (∏ i, (((ks i).val : ℝ) ^ power)) *
          tupleMoment n M q (fun i => (ks i).val)
      else 0) ≤ (Finset.univ.card : ℕ) • R := by
        apply Finset.sum_le_card_nsmul
        intro ks hks
        split_ifs with h
        · rcases h.2 with ⟨i, hi⟩
          have hcoord : ((ks i).val : ℝ) ≤
              ∑ j, ((ks j).val : ℝ) := by
            exact Finset.single_le_sum
              (fun j _ => (show 0 ≤ ((ks j).val : ℝ) by positivity))
              (Finset.mem_univ i)
          have hK : B * Real.log n <
              ∑ j, ((ks j).val : ℝ) := lt_of_lt_of_le hi hcoord
          have hexp : Real.exp (-c * ∑ j, ((ks j).val : ℝ)) ≤
              Real.exp (-c * (B * Real.log n)) := by
            apply Real.exp_le_exp.mpr
            nlinarith
          have hm := henv (fun j => (ks j).val) h.1
          dsimp [R]
          calc
            (∏ j, (((ks j).val : ℝ) ^ power)) *
                tupleMoment n M q (fun j => (ks j).val)
                ≤ (∏ j, (((ks j).val : ℝ) ^ power)) *
                  (D * (n : ℝ) ^ d *
                    Real.exp (-c * ∑ j, ((ks j).val : ℝ))) :=
              mul_le_mul_of_nonneg_left hm (by positivity)
            _ ≤ (n : ℝ) ^ (power * q) *
                  (D * (n : ℝ) ^ d *
                    Real.exp (-c * ∑ j, ((ks j).val : ℝ))) := by
              gcongr
              exact tupleWeight_le n q power ks
            _ ≤ (n : ℝ) ^ (power * q) *
                  (D * (n : ℝ) ^ d *
                    Real.exp (-c * (B * Real.log n))) := by
              gcongr
        · exact hR
    _ = ((n + 1 : ℕ) : ℝ) ^ q * R := by
      rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
        Fintype.card_fin]
      norm_num
    _ = _ := rfl

theorem polynomialExp_absorb
    (E : ℕ) (D c A : ℝ) (hc : 0 < c) (hA : 0 < A) :
    ∃ B : ℝ, 0 < B ∧ ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n →
      D * (n : ℝ) ^ E * Real.exp (-c * (B * Real.log n)) ≤
        Real.rpow (n : ℝ) (-A) := by
  let B : ℝ := (A + (E : ℝ) + 1) / c
  have hB : 0 < B := by
    dsimp [B]
    positivity
  obtain ⟨nD, hnD⟩ := exists_nat_ge D
  refine ⟨B, hB, max 1 nD, ?_⟩
  intro n hn
  have hn1 : 1 ≤ n := le_trans (le_max_left _ _) hn
  have hnD' : nD ≤ n := le_trans (le_max_right _ _) hn
  have hnposN : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn1
  have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr hnposN
  have hDle : D ≤ (n : ℝ) := le_trans hnD (by exact_mod_cast hnD')
  have hpoly : D * (n : ℝ) ^ E ≤ (n : ℝ) ^ (E + 1) := by
    rw [pow_succ]
    nlinarith [pow_nonneg (show 0 ≤ (n : ℝ) by positivity) E]
  calc
    D * (n : ℝ) ^ E * Real.exp (-c * (B * Real.log n))
        ≤ (n : ℝ) ^ (E + 1) *
            Real.exp (-c * (B * Real.log n)) := by
          gcongr
    _ = Real.exp (Real.log n * (E + 1 : ℕ)) *
          Real.exp (-c * (B * Real.log n)) := by
          rw [← Real.rpow_natCast]
          rw [Real.rpow_def_of_pos hnpos]
    _ = Real.exp (Real.log n * (-A)) := by
          rw [← Real.exp_add]
          congr 1
          dsimp [B]
          field_simp
          push_cast
          ring
    _ = Real.rpow (n : ℝ) (-A) :=
      (Real.rpow_def_of_pos hnpos (-A)).symm

theorem tupleTail_eventually_of_expEnvelope
    (q power d : ℕ) (D c A : ℝ)
    (hD : 0 ≤ D) (hc : 0 < c) (hA : 0 < A)
    (P : ℕ → ℕ → Prop)
    (henv : ∀ n M : ℕ, P n M → ∀ ks : Fin q → ℕ,
      (∀ i, 0 < ks i) →
      tupleMoment n M q ks ≤
        D * (n : ℝ) ^ d *
          Real.exp (-c * ∑ i, (ks i : ℝ))) :
    ∃ B : ℝ, 0 < B ∧ ∃ n0 : ℕ, ∀ n M : ℕ,
      n0 ≤ n → P n M →
      tupleTail n M q power B ≤ Real.rpow (n : ℝ) (-A) := by
  let E : ℕ := q + power * q + d
  obtain ⟨B, hB, n1, habs⟩ :=
    polynomialExp_absorb E (D * (2 : ℝ) ^ q) c A hc hA
  refine ⟨B, hB, max 1 n1, ?_⟩
  intro n M hn hP
  have hnOne : 1 ≤ n := le_trans (le_max_left _ _) hn
  have hnAbs : n1 ≤ n := le_trans (le_max_right _ _) hn
  have htail := tupleTail_le_expEnvelope n M q power d B D c hD hc
    (henv n M hP)
  calc
    tupleTail n M q power B
        ≤ ((n + 1 : ℕ) : ℝ) ^ q *
          ((n : ℝ) ^ (power * q) *
            (D * (n : ℝ) ^ d *
              Real.exp (-c * (B * Real.log n)))) := htail
    _ ≤ (2 * (n : ℝ)) ^ q *
          ((n : ℝ) ^ (power * q) *
            (D * (n : ℝ) ^ d *
              Real.exp (-c * (B * Real.log n)))) := by
          gcongr
          have hnat : n + 1 ≤ 2 * n := by omega
          exact_mod_cast hnat
    _ = (D * (2 : ℝ) ^ q) * (n : ℝ) ^ E *
          Real.exp (-c * (B * Real.log n)) := by
          dsimp [E]
          simp only [mul_pow, pow_add]
          ring
    _ ≤ Real.rpow (n : ℝ) (-A) := habs n hnAbs

end

end Erdos745.WrapUp.Proofs.Internal.W04_TUPLES_Tails


/-! The signed-entropy global tuple majorant on `K ≤ n/16`. -/
namespace Erdos745.WrapUp.Proofs.Internal.W04_TUPLES_GlobalSmall

noncomputable section
open scoped BigOperators

open W04_TUPLES_Foundation
open W04_TUPLES_Local
open W04_TUPLES_Near
open W04_TUPLES_RateEntropy
open Erdos745.WrapUp.Proofs.W06_POISSON

private theorem tupleLeading_stirling_bound
    (n M q : ℕ) (ks : Fin q → ℕ) (R : ℝ)
    (hR0 : 0 ≤ R)
    (hR : ∀ k : ℕ, cayleyStirlingRatio k ≤ R)
    (hlo : (1 : ℝ) / 2 ≤ degreeAt n M)
    (hpos : ∀ i, 0 < ks i) :
    tupleLeading n M q ks ≤
      (2 * R / Real.sqrt (2 * Real.pi)) ^ q * (n : ℝ) ^ q *
        (∏ i, Real.rpow (ks i : ℝ) (-5 / 2)) *
        Real.exp (-rate (degreeAt n M) * ∑ i, (ks i : ℝ)) := by
  have hlam : 0 < degreeAt n M := lt_of_lt_of_le (by norm_num) hlo
  have hsqrt : 0 < Real.sqrt (2 * Real.pi) := by positivity
  have hnlam : (n : ℝ) / degreeAt n M ≤ 2 * n := by
    apply (div_le_iff₀ hlam).2
    have hn0 : 0 ≤ (n : ℝ) := by positivity
    nlinarith [mul_nonneg hn0 (sub_nonneg.mpr hlo)]
  unfold tupleLeading
  calc
    (∏ i, treeLeading n M (ks i)) ≤
        ∏ i, ((2 * R / Real.sqrt (2 * Real.pi)) * (n : ℝ) *
          Real.rpow (ks i : ℝ) (-5 / 2) *
          Real.exp (-rate (degreeAt n M) * (ks i : ℝ))) := by
      apply Finset.prod_le_prod₀
      · intro i hi
        unfold treeLeading
        rw [if_neg (Nat.ne_of_gt (hpos i))]
        have hc : 0 < cayley (ks i) := cayley_pos (hpos i)
        positivity
      · intro i hi
        rw [treeLeading_eq_cayleyKernel n M (ks i) (hpos i) hlam]
        have hkpos : 0 < (ks i : ℝ) := Nat.cast_pos.mpr (hpos i)
        have hstirling : cayleyKernel (ks i) =
            cayleyStirlingRatio (ks i) / Real.sqrt (2 * Real.pi) *
              Real.rpow (ks i : ℝ) (-5 / 2) := by
          convert cayleyKernel_eq_stirling (ks i) (hpos i) using 1
          change cayleyStirlingRatio (ks i) / Real.sqrt (2 * Real.pi) *
              Real.rpow (ks i : ℝ) (-5 / 2) = _
          norm_num [Real.rpow_def_of_pos hkpos]
        rw [hstirling]
        have hrpos : 0 < cayleyStirlingRatio (ks i) :=
          cayleyStirlingRatio_pos (ks i) (hpos i)
        have hkpow : 0 < Real.rpow (ks i : ℝ) (-5 / 2) :=
          Real.rpow_pos_of_pos (Nat.cast_pos.mpr (hpos i)) _
        have hexp : 0 < Real.exp (-rate (degreeAt n M) * (ks i : ℝ)) :=
          Real.exp_pos _
        have hratio : cayleyStirlingRatio (ks i) / Real.sqrt (2 * Real.pi) ≤
            R / Real.sqrt (2 * Real.pi) := by
          exact div_le_div_of_nonneg_right (hR (ks i)) hsqrt.le
        calc
          (n : ℝ) / degreeAt n M *
                (cayleyStirlingRatio (ks i) / Real.sqrt (2 * Real.pi) *
                  Real.rpow (ks i : ℝ) (-5 / 2)) *
              Real.exp (-rate (degreeAt n M) * (ks i : ℝ)) ≤
            (2 * n) *
                (R / Real.sqrt (2 * Real.pi) *
                  Real.rpow (ks i : ℝ) (-5 / 2)) *
              Real.exp (-rate (degreeAt n M) * (ks i : ℝ)) := by
            gcongr
          _ = (2 * R / Real.sqrt (2 * Real.pi)) * (n : ℝ) *
                Real.rpow (ks i : ℝ) (-5 / 2) *
              Real.exp (-rate (degreeAt n M) * (ks i : ℝ)) := by ring
    _ = (2 * R / Real.sqrt (2 * Real.pi)) ^ q * (n : ℝ) ^ q *
          (∏ i, Real.rpow (ks i : ℝ) (-5 / 2)) *
          Real.exp (-rate (degreeAt n M) * ∑ i, (ks i : ℝ)) := by
      rw [show (∏ i : Fin q,
          ((2 * R / Real.sqrt (2 * Real.pi)) * (n : ℝ) *
            Real.rpow (ks i : ℝ) (-5 / 2) *
            Real.exp (-rate (degreeAt n M) * (ks i : ℝ)))) =
          (∏ _i : Fin q, (2 * R / Real.sqrt (2 * Real.pi)) * (n : ℝ)) *
            (∏ i : Fin q, Real.rpow (ks i : ℝ) (-5 / 2)) *
            (∏ i : Fin q,
              Real.exp (-rate (degreeAt n M) * (ks i : ℝ))) by
        rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]]
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
        mul_pow, ← Real.exp_sum]
      rw [Finset.mul_sum]

set_option maxHeartbeats 800000 in
theorem globalSmallEventually (hF : FiniteEnumerationStatement) (q : ℕ) (hq : 0 < q) :
    ∃ C : ℝ, 0 < C ∧ ∃ n0 : ℕ, ∀ (n M : ℕ) (ks : Fin q → ℕ),
      n0 ≤ n → M ≤ capacity n →
      1 / 2 ≤ degreeAt n M → degreeAt n M ≤ 3 / 2 →
      (∀ i, 0 < ks i) →
      (∑ i, (ks i : ℝ)) ≤ (n : ℝ) / 16 →
      tupleGlobalBound n M q ks C (1 / 64) := by
  obtain ⟨R, hRpos, hR⟩ := cayleyStirlingRatio_bddAbove
  let D : ℝ := 64 * ((q : ℝ) + 1) + 74
  let C₀ : ℝ := 2 * R / Real.sqrt (2 * Real.pi)
  let C : ℝ := C₀ ^ q * Real.exp (D / 16)
  have hC₀ : 0 < C₀ := by
    dsimp [C₀]
    positivity
  have hD : 0 < D := by
    dsimp [D]
    positivity
  have hC : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, 64, ?_⟩
  intro n M ks hn hM hlo hhi hpos hK
  obtain ⟨hJ, hrem⟩ := nearFiniteLogRemainder hF n M q ks hq hn hM hpos hK hlo hhi
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by omega) hn)
  have hlam : 0 < degreeAt n M := lt_of_lt_of_le (by norm_num) hlo
  have hLeadPos : 0 < tupleLeading n M q ks :=
    tupleLeading_pos n M q ks (by omega) hlam hpos
  have hLead := tupleLeading_stirling_bound n M q ks R hRpos.le hR hlo hpos
  let K : ℝ := ∑ i, (ks i : ℝ)
  have hK0 : 0 ≤ K := by dsimp [K]; positivity
  have ht0 : 0 ≤ K / n := div_nonneg hK0 hnpos.le
  have ht : K / n ≤ (1 : ℝ) / 16 := by
    apply (div_le_iff₀ hnpos).2
    convert hK using 1 <;> ring
  have hent := entropyCore_global_upper hlo hhi ht0 ht
  have hscaledEntropy :
      (n : ℝ) * entropyCore (degreeAt n M) (K / n) ≤
        -(((degreeAt n M - 1) ^ 2 * K + K ^ 3 / (n : ℝ) ^ 2) / 64) := by
    have := mul_le_mul_of_nonneg_left hent hnpos.le
    convert this using 1 <;> field_simp [ne_of_gt hnpos] <;> ring
  have hlogUpper :
      Real.log (tupleMoment n M q ks / tupleLeading n M q ks) ≤
        (n : ℝ) * entropyCore (degreeAt n M) (K / n) +
          rate (degreeAt n M) * K + D * K / n := by
    dsimp [D, K]
    linarith [le_abs_self
      (Real.log (tupleMoment n M q ks / tupleLeading n M q ks) -
        ((n : ℝ) * entropyCore (degreeAt n M)
          ((∑ i, (ks i : ℝ)) / n) +
          rate (degreeAt n M) * (∑ i, (ks i : ℝ))))]
  have hDloss : D * K / n ≤ D / 16 := by
    have hKn : K ≤ (n : ℝ) / 16 := by simpa [K] using! hK
    apply (div_le_iff₀ hnpos).2
    have hD0 : 0 ≤ D := hD.le
    nlinarith [mul_le_mul_of_nonneg_left hKn hD0]
  have hratioPos : 0 < tupleMoment n M q ks / tupleLeading n M q ks :=
    div_pos hJ hLeadPos
  have hJexp : tupleMoment n M q ks = tupleLeading n M q ks *
      Real.exp (Real.log (tupleMoment n M q ks / tupleLeading n M q ks)) := by
    rw [Real.exp_log hratioPos]
    field_simp [ne_of_gt hLeadPos]
  have hExp :
      Real.exp (Real.log (tupleMoment n M q ks / tupleLeading n M q ks)) ≤
        Real.exp ((n : ℝ) * entropyCore (degreeAt n M) (K / n) +
          rate (degreeAt n M) * K + D * K / n) :=
    Real.exp_le_exp.mpr hlogUpper
  have hcoreExp :
      Real.exp (-rate (degreeAt n M) * K) *
          Real.exp ((n : ℝ) * entropyCore (degreeAt n M) (K / n) +
            rate (degreeAt n M) * K + D * K / n) ≤
        Real.exp (D / 16) *
          Real.exp (-(1 / 64) *
            ((degreeAt n M - 1) ^ 2 * K + K ^ 3 / (n : ℝ) ^ 2)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith
  unfold tupleGlobalBound
  rw [hJexp]
  have hprod0 : 0 ≤ ∏ i, Real.rpow (ks i : ℝ) (-5 / 2) := by
    apply Finset.prod_nonneg
    intro i hi
    exact (Real.rpow_pos_of_pos (Nat.cast_pos.mpr (hpos i)) _).le
  have hpref0 : 0 ≤ C₀ ^ q * (n : ℝ) ^ q *
      (∏ i, Real.rpow (ks i : ℝ) (-5 / 2)) := by
    exact mul_nonneg (mul_nonneg (pow_nonneg hC₀.le q) (pow_nonneg hnpos.le q)) hprod0
  have hleadRhs0 : 0 ≤
      (C₀ ^ q * (n : ℝ) ^ q *
        (∏ i, Real.rpow (ks i : ℝ) (-5 / 2))) *
          Real.exp (-rate (degreeAt n M) * K) :=
    mul_nonneg hpref0 (Real.exp_pos _).le
  calc
    tupleLeading n M q ks *
        Real.exp (Real.log (tupleMoment n M q ks / tupleLeading n M q ks)) ≤
      (C₀ ^ q * (n : ℝ) ^ q *
          (∏ i, Real.rpow (ks i : ℝ) (-5 / 2)) *
          Real.exp (-rate (degreeAt n M) * K)) *
        Real.exp ((n : ℝ) * entropyCore (degreeAt n M) (K / n) +
          rate (degreeAt n M) * K + D * K / n) := by
      exact mul_le_mul hLead hExp (Real.exp_pos _).le hleadRhs0
    _ ≤ C₀ ^ q * (n : ℝ) ^ q *
          (∏ i, Real.rpow (ks i : ℝ) (-5 / 2)) *
          (Real.exp (D / 16) *
            Real.exp (-(1 / 64) *
              ((degreeAt n M - 1) ^ 2 * K + K ^ 3 / (n : ℝ) ^ 2))) := by
      rw [show
        (C₀ ^ q * (n : ℝ) ^ q *
            (∏ i, Real.rpow (ks i : ℝ) (-5 / 2)) *
            Real.exp (-rate (degreeAt n M) * K)) *
          Real.exp ((n : ℝ) * entropyCore (degreeAt n M) (K / n) +
            rate (degreeAt n M) * K + D * K / n) =
        C₀ ^ q * (n : ℝ) ^ q *
            (∏ i, Real.rpow (ks i : ℝ) (-5 / 2)) *
          (Real.exp (-rate (degreeAt n M) * K) *
            Real.exp ((n : ℝ) * entropyCore (degreeAt n M) (K / n) +
              rate (degreeAt n M) * K + D * K / n)) by ring]
      exact mul_le_mul_of_nonneg_left hcoreExp hpref0
    _ = C * (n : ℝ) ^ q *
          (∏ i, Real.rpow (ks i : ℝ) (-5 / 2)) *
          Real.exp (-(1 / 64) *
            ((degreeAt n M - 1) ^ 2 * K + K ^ 3 / (n : ℝ) ^ 2)) := by
      dsimp [C]
      ring
    _ = C * (n : ℝ) ^ q *
          (∏ i, Real.rpow (ks i : ℝ) (-5 / 2)) *
          Real.exp (-(1 / 64) *
            ((degreeAt n M - 1) ^ 2 * (∑ i, (ks i : ℝ)) +
              (∑ i, (ks i : ℝ)) ^ 3 / (n : ℝ) ^ 2)) := by
      rfl

end

end Erdos745.WrapUp.Proofs.Internal.W04_TUPLES_GlobalSmall


/-! The logarithmic estimate on an arbitrary fixed compact density interval. -/
namespace Erdos745.WrapUp.Proofs.Internal.W04_TUPLES_Compact

noncomputable section
open scoped BigOperators
set_option maxHeartbeats 3000000

open W04_TUPLES_Foundation
open W04_TUPLES_Local
open W04_TUPLES_FiniteBridge
open W04_TUPLES_FiniteBounds

private theorem sparse_correction_compact
    {n K M b N A H : ℝ}
    (hn : 0 < n) (hK0 : 0 ≤ K) (hH : 1 ≤ H)
    (hM1 : 1 ≤ M) (hb1 : 1 ≤ b) (hbM : b ≤ M)
    (hMb0 : 0 ≤ M - b) (hMb : M - b ≤ K)
    (hN0 : 0 < N) (hA0 : 0 < A)
    (hNlower : n ^ 2 / 4 ≤ N) (hAlower : n ^ 2 / 4 ≤ A)
    (hNupper : N ≤ n ^ 2)
    (hNA0 : 0 ≤ N - A) (hNA : N - A ≤ K * n)
    (hMH : M ≤ H * n) :
    |M * (M - 1) / (2 * N) - b * (b - 1) / (2 * A)| ≤
      32 * H ^ 2 * K / n := by
  have hn0 : 0 ≤ n := hn.le
  have hM0 : 0 ≤ M := le_trans (by norm_num) hM1
  have hb0 : 0 ≤ b := le_trans (by norm_num) hb1
  have hMsub0 : 0 ≤ M - 1 := sub_nonneg.mpr hM1
  have hsum0 : 0 ≤ M + b - 1 := by linarith
  have hMsq : M * (M - 1) ≤ H ^ 2 * n ^ 2 := by
    have hMHH : M ^ 2 ≤ (H * n) ^ 2 := by gcongr
    nlinarith [mul_nonneg hM0 hMsub0]
  have hfactor : M * (M - 1) - b * (b - 1) =
      (M - b) * (M + b - 1) := by ring
  have hsum : M + b - 1 ≤ 2 * H * n := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hH) hn0]
  have hfactorBound :
      0 ≤ M * (M - 1) - b * (b - 1) ∧
      M * (M - 1) - b * (b - 1) ≤ 2 * H * K * n := by
    rw [hfactor]
    constructor
    · exact mul_nonneg hMb0 hsum0
    · nlinarith [mul_nonneg (sub_nonneg.mpr hMb) hsum0,
        mul_nonneg hMb0 (sub_nonneg.mpr hsum)]
  have hnum :
      |M * (M - 1) * A - b * (b - 1) * N| ≤
        4 * H ^ 2 * K * n ^ 3 := by
    rw [show M * (M - 1) * A - b * (b - 1) * N =
      -(M * (M - 1) * (N - A)) +
        (M * (M - 1) - b * (b - 1)) * N by ring]
    calc
      _ ≤ |M * (M - 1) * (N - A)| +
          |(M * (M - 1) - b * (b - 1)) * N| := by
            simpa only [abs_neg] using! abs_add_le
              (-(M * (M - 1) * (N - A)))
              ((M * (M - 1) - b * (b - 1)) * N)
      _ ≤ (H ^ 2 * n ^ 2) * (K * n) +
          (2 * H * K * n) * n ^ 2 := by
        rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hM0,
          abs_of_nonneg hMsub0, abs_of_nonneg hNA0,
          abs_of_nonneg hfactorBound.1, abs_of_pos hN0]
        exact add_le_add
          (mul_le_mul hMsq hNA hNA0 (by positivity))
          (mul_le_mul hfactorBound.2 hNupper hN0.le (by positivity))
      _ ≤ 4 * H ^ 2 * K * n ^ 3 := by
        have hcoef : 0 ≤ 3 * H ^ 2 - 2 * H := by
          nlinarith [mul_nonneg (sub_nonneg.mpr hH) (show 0 ≤ H by linarith)]
        nlinarith [mul_nonneg hcoef (show 0 ≤ K * n ^ 3 by positivity)]
  have hden : 0 < 2 * N * A := by positivity
  have hdenLower : n ^ 4 / 8 ≤ 2 * N * A := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hNlower) hA0.le,
      mul_nonneg (by positivity : 0 ≤ n ^ 2 / 4)
        (sub_nonneg.mpr hAlower)]
  rw [show M * (M - 1) / (2 * N) - b * (b - 1) / (2 * A) =
      (M * (M - 1) * A - b * (b - 1) * N) / (2 * N * A) by
        field_simp]
  rw [abs_div, abs_of_pos hden]
  calc
    _ ≤ (4 * H ^ 2 * K * n ^ 3) / (2 * N * A) :=
      div_le_div_of_nonneg_right hnum hden.le
    _ ≤ 32 * H ^ 2 * K / n := by
      apply (div_le_iff₀ hden).2
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hn).2
      have hcoef : 0 ≤ 32 * H ^ 2 * K := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hdenLower hcoef]

private theorem realFinite_compact_remainder
    {n M lam N A K Q r b lo H : ℝ}
    (hr : r = K - Q) (hb : b = M - r)
    (hn8 : 8 ≤ n) (hK0 : 0 ≤ K) (hK1 : 1 ≤ K)
    (hK : K ≤ n / 16) (hKlo : K ≤ lo * n / 16)
    (hQ0 : 0 ≤ Q) (hQK : Q ≤ K)
    (hlo : 0 < lo) (hH : 1 ≤ H)
    (hMlo : lo * n / 2 ≤ M) (hMhi : M ≤ H * n / 2)
    (hM1 : 1 ≤ M) (hb1 : 1 ≤ b)
    (hbLo : lo * n / 4 ≤ b) (hbM : b ≤ M)
    (hQhalf : Q ≤ b / 2)
    (hN0 : 0 < N) (hA0 : 0 < A)
    (hNlower : n ^ 2 / 4 ≤ N) (hAlower : n ^ 2 / 4 ≤ A)
    (hNupper : N ≤ n ^ 2)
    (hNA0 : 0 ≤ N - A) (hNA : N - A ≤ K * n)
    (hn0 : n ≠ 0) (hlam0 : lam ≠ 0)
    (hdegree : 2 * M = lam * n)
    (hlogA : Real.log A = Real.log N + Real.log (1 - K / n) +
      Real.log (1 - K / (n - 1)))
    (hbalance : Real.log n + Real.log M - Real.log N - Real.log lam =
      Real.log (n / (n - 1))) :
    |realTupleFiniteMain n M lam N A K Q r b -
        (n * entropyCore lam (K / n) + rate lam * K)| ≤
      (8 * H + 12 / lo + 6 + 32 * H ^ 2) * K ^ 2 / n := by
  have hn : 0 < n := by linarith
  have hn2 : 2 ≤ n := by linarith
  have hM : 0 < M := lt_of_lt_of_le (by norm_num) hM1
  have hKM : K < M := by
    have : K ≤ n / 16 := hK
    nlinarith [mul_pos hlo hn]
  have hb0 : 0 < b := lt_of_lt_of_le (by norm_num) hb1
  have hMb0 : 0 ≤ M - b := sub_nonneg.mpr hbM
  have hMb : M - b ≤ K := by rw [hb, hr]; linarith
  have hr0 : 0 ≤ r := by rw [hr]; linarith
  have hrK : r ≤ K := by rw [hr]; linarith
  have hMH : M ≤ H * n := by nlinarith [mul_nonneg (sub_nonneg.mpr hH) hn.le]
  rw [realTupleFiniteMain_residual_identity hr hb hn0 hlam0 hdegree hlogA hbalance]
  let t1 := b * (Real.log (1 - K / (n - 1)) - Real.log (1 - K / n))
  let t2 := b * (Real.log (1 - K / M) - Real.log (1 - r / M)) + Q
  let t3 := 2 * Q * Real.log (1 - K / n) - Q * Real.log (1 - K / M)
  let t4 := r * Real.log (n / (n - 1))
  let t5 := M * (M - 1) / (2 * N) - b * (b - 1) / (2 * A)
  have heq :
      b * (Real.log (1 - K / (n - 1)) - Real.log (1 - K / n)) +
        b * (Real.log (1 - K / M) - Real.log (1 - r / M)) +
        2 * Q * Real.log (1 - K / n) - Q * Real.log (1 - K / M) +
        r * Real.log (n / (n - 1)) + Q +
        (M * (M - 1) / (2 * N) - b * (b - 1) / (2 * A)) =
      t1 + t2 + t3 + t4 + t5 := by
    dsimp [t1, t2, t3, t4, t5]
    ring
  rw [heq]
  have ht1 : |t1| ≤ 8 * H * K / n := by
    dsimp [t1]
    rw [abs_mul, abs_of_pos hb0]
    calc
      _ ≤ b * (8 * K / n ^ 2) :=
        mul_le_mul_of_nonneg_left (adjacent_log_difference hn2 hK0 hK) hb0.le
      _ ≤ 8 * H * K / n := by
        field_simp [ne_of_gt hn]
        nlinarith [mul_nonneg (sub_nonneg.mpr (hbM.trans hMH)) hK0]
  have ht2 : |t2| ≤ 8 / lo * Q * K / n := by
    dsimp [t2]
    have hbEq : b = M - K + Q := by rw [hb, hr]; ring
    rw [hbEq, hr]
    have hs := shifted_middle_bound hM hQ0 hKM hQK (by rw [← hbEq]; exact hQhalf)
    apply le_trans hs
    rw [← hbEq]
    have hQsq : Q ^ 2 ≤ Q * K := by nlinarith [mul_nonneg hQ0 (sub_nonneg.mpr hQK)]
    field_simp [ne_of_gt hb0, ne_of_gt hn, ne_of_gt hlo]
    nlinarith [mul_nonneg hQ0 hK0,
      mul_nonneg (sub_nonneg.mpr hQsq) (sub_nonneg.mpr hbLo)]
  have hlogn : |Real.log (1 - K / n)| ≤ 2 * K / n :=
    log_small_ratio_bound hn hK0 (by linarith)
  have hlogM : |Real.log (1 - K / M)| ≤ 2 * K / M :=
    log_small_ratio_bound hM hK0 (by nlinarith [hKlo, hMlo])
  have hMratio : 2 * K / M ≤ 4 / lo * K / n := by
    field_simp [ne_of_gt hM, ne_of_gt hn, ne_of_gt hlo]
    nlinarith [mul_nonneg hK0 (sub_nonneg.mpr hMlo)]
  have ht3 : |t3| ≤ (4 + 4 / lo) * Q * K / n := by
    dsimp [t3]
    calc
      _ ≤ |2 * Q * Real.log (1 - K / n)| +
          |Q * Real.log (1 - K / M)| := abs_sub _ _
      _ = 2 * Q * |Real.log (1 - K / n)| +
          Q * |Real.log (1 - K / M)| := by
            rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hQ0]
            norm_num
      _ ≤ 2 * Q * (2 * K / n) + Q * (4 / lo * K / n) :=
        add_le_add
          (mul_le_mul_of_nonneg_left hlogn (by positivity))
          (mul_le_mul_of_nonneg_left (le_trans hlogM hMratio) hQ0)
      _ = _ := by ring
  have ht4 : |t4| ≤ 2 * K / n := by
    dsimp [t4]
    rw [abs_mul, abs_of_nonneg hr0]
    calc
      _ ≤ r * (2 / n) :=
        mul_le_mul_of_nonneg_left (log_succ_ratio_bound hn2) hr0
      _ ≤ 2 * K / n := by
        calc
          r * (2 / n) ≤ K * (2 / n) :=
            mul_le_mul_of_nonneg_right hrK (by positivity)
          _ = 2 * K / n := by ring
  have ht5 : |t5| ≤ 32 * H ^ 2 * K / n := by
    dsimp [t5]
    exact sparse_correction_compact hn hK0 hH hM1 hb1 hbM hMb0 hMb
      hN0 hA0 hNlower hAlower hNupper hNA0 hNA hMH
  calc
    |t1 + t2 + t3 + t4 + t5| ≤
        |t1| + |t2| + |t3| + |t4| + |t5| := by
      linarith [abs_add_le (t1 + t2 + t3 + t4) t5,
        abs_add_le (t1 + t2 + t3) t4, abs_add_le (t1 + t2) t3,
        abs_add_le t1 t2]
    _ ≤ 8 * H * K / n + 8 / lo * Q * K / n +
        (4 + 4 / lo) * Q * K / n + 2 * K / n +
        32 * H ^ 2 * K / n := by linarith
    _ ≤ (8 * H + 12 / lo + 6 + 32 * H ^ 2) * K ^ 2 / n := by
      have hKsq : K ≤ K ^ 2 := by nlinarith [mul_nonneg hK0 (sub_nonneg.mpr hK1)]
      have hQsq : Q * K ≤ K ^ 2 := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hQK) hK0]
      have hc1 : 0 ≤ 8 * H + 2 + 32 * H ^ 2 := by positivity
      have hc2 : 0 ≤ 4 + 12 / lo := by positivity
      have hs1 := mul_nonneg hc1 (sub_nonneg.mpr hKsq)
      have hs2 := mul_nonneg hc2 (sub_nonneg.mpr hQsq)
      field_simp [ne_of_gt hn, ne_of_gt hlo]
      nlinarith [hs1, hs2]

private theorem entropyCurvature_compact
    {lam t lo H : ℝ}
    (hlo : 0 < lo) (hH : 1 ≤ H) (hlamlo : lo ≤ lam) (hlamH : lam ≤ H)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 4) (htlo : t ≤ lo / 4) :
    |entropyCurvature lam t| ≤ 16 * (H + 2) ^ 2 / lo := by
  have hden1 : 1 / 2 ≤ 1 - t := by linarith
  have hden2 : lo / 2 ≤ lam - 2 * t := by linarith
  have hden : lo / 8 ≤ (1 - t) ^ 2 * (lam - 2 * t) := by
    have hsq : (1 : ℝ) / 4 ≤ (1 - t) ^ 2 := by nlinarith [sq_nonneg (1 - t - 1 / 2)]
    calc
      lo / 8 = (1 / 4) * (lo / 2) := by ring
      _ ≤ (1 - t) ^ 2 * (lam - 2 * t) :=
        mul_le_mul hsq hden2 (by positivity) (by positivity)
  have hden0 : 0 < (1 - t) ^ 2 * (lam - 2 * t) :=
    lt_of_lt_of_le (by positivity) hden
  have hnum : |(2 - lam) * (lam - 1 - t)| ≤ (H + 2) ^ 2 := by
    rw [abs_mul]
    have h1 : |2 - lam| ≤ H + 2 := by rw [abs_le]; constructor <;> linarith
    have h2 : |lam - 1 - t| ≤ H + 2 := by rw [abs_le]; constructor <;> linarith
    nlinarith [mul_nonneg (sub_nonneg.mpr h1) (abs_nonneg (lam - 1 - t)),
      mul_nonneg (abs_nonneg (2 - lam)) (sub_nonneg.mpr h2)]
  unfold entropyCurvature
  rw [abs_div, abs_of_pos hden0]
  apply (div_le_iff₀ hden0).2
  field_simp [ne_of_gt hlo]
  nlinarith [mul_nonneg (sq_nonneg (H + 2)) (sub_nonneg.mpr hden)]

private theorem scaled_entropy_compact
    {n lam K lo H : ℝ}
    (hn : 0 < n) (hlo : 0 < lo) (hH : 1 ≤ H)
    (hlamlo : lo ≤ lam) (hlamH : lam ≤ H)
    (hK0 : 0 ≤ K) (hK1 : K ≤ n / 4) (hKlo : K ≤ lo * n / 4) :
    |n * entropyCore lam (K / n) + rate lam * K| ≤
      (16 * (H + 2) ^ 2 / lo) * K ^ 2 / n := by
  let C : ℝ := 16 * (H + 2) ^ 2 / lo
  have hC0 : 0 ≤ C := by dsimp [C]; positivity
  have ht0 : 0 ≤ K / n := by positivity
  have ht1 : K / n ≤ 1 / 4 := (div_le_iff₀ hn).2 (by linarith)
  have htlo : K / n ≤ lo / 4 := (div_le_iff₀ hn).2 (by linarith)
  have firstDerivative : ∀ x ∈ Set.Icc (0 : ℝ) (K / n),
      HasDerivWithinAt (entropySlope lam) (entropyCurvature lam x)
        (Set.Icc (0 : ℝ) (K / n)) x := by
    intro x hx
    apply (hasDerivAt_entropySlope
      (by linarith [hx.2, ht1]) (by linarith [hx.2, htlo, hlamlo])).hasDerivWithinAt
  have curvatureBound : ∀ x ∈ Set.Ico (0 : ℝ) (K / n),
      ‖entropyCurvature lam x‖ ≤ C := by
    intro x hx
    rw [Real.norm_eq_abs]
    exact entropyCurvature_compact hlo hH hlamlo hlamH hx.1
      (le_trans hx.2.le ht1) (le_trans hx.2.le htlo)
  have slopeBound : ∀ x ∈ Set.Icc (0 : ℝ) (K / n),
      ‖entropySlope lam x - entropySlope lam 0‖ ≤ C * x := by
    intro x hx
    simpa using! norm_image_sub_le_of_norm_deriv_le_segment'
      firstDerivative curvatureBound x hx
  have secondDerivative : ∀ x ∈ Set.Icc (0 : ℝ) (K / n),
      HasDerivWithinAt (fun y => entropyCore lam y + rate lam * y)
        (entropySlope lam x + rate lam) (Set.Icc (0 : ℝ) (K / n)) x := by
    intro x hx
    convert ((hasDerivAt_entropyCore (lt_of_lt_of_le hlo hlamlo)
      (by linarith [hx.2, ht1]) (by linarith [hx.2, htlo, hlamlo])).add
      ((hasDerivAt_id x).const_mul (rate lam))).hasDerivWithinAt using 1
    all_goals simp
  have slopeBound' : ∀ x ∈ Set.Ico (0 : ℝ) (K / n),
      ‖entropySlope lam x + rate lam‖ ≤ C * (K / n) := by
    intro x hx
    rw [← sub_neg_eq_add, ← entropySlope_zero]
    exact le_trans (slopeBound x ⟨hx.1, hx.2.le⟩)
      (mul_le_mul_of_nonneg_left hx.2.le hC0)
  have hmain := norm_image_sub_le_of_norm_deriv_le_segment'
    secondDerivative slopeBound' (K / n) ⟨ht0, le_rfl⟩
  rw [entropyCore_zero] at hmain
  simp only [mul_zero, add_zero, sub_zero, Real.norm_eq_abs] at hmain
  have heq : n * (entropyCore lam (K / n) + rate lam * (K / n)) =
      n * entropyCore lam (K / n) + rate lam * K := by field_simp
  rw [← heq, abs_mul, abs_of_pos hn]
  calc
    n * |entropyCore lam (K / n) + rate lam * (K / n)| ≤
        n * (C * (K / n) * (K / n)) := mul_le_mul_of_nonneg_left hmain hn.le
    _ = C * K ^ 2 / n := by field_simp

set_option maxHeartbeats 12000000 in
theorem compactLocalEventually (hF : FiniteEnumerationStatement) :
    ∀ (lo hi B : ℝ) (q : ℕ), 0 < lo → lo ≤ hi → 0 < B → 0 < q →
    ∃ C : ℝ, 0 < C ∧ ∃ n0 : ℕ, ∀ (n M : ℕ) (ks : Fin q → ℕ),
      n0 ≤ n → M ≤ capacity n → lo ≤ degreeAt n M → degreeAt n M ≤ hi →
      (∀ i, 0 < ks i) → (∑ i, (ks i : ℝ)) ≤ B * Real.log n →
      0 < tupleMoment n M q ks ∧
      |Real.log (tupleMoment n M q ks / tupleLeading n M q ks)| ≤
        C * (∑ i, (ks i : ℝ)) ^ 2 / n := by
  intro lo hi B q hlo hlohi hB hq
  let H : ℝ := max 2 hi
  let T : ℝ := max 64 (max (32 * B / lo) (32 * B)) + 8 * H
  let Cfin : ℝ :=
    (2 + 64 * H ^ 3 + 4 / lo) +
      (8 * H + 12 / lo + 6 + 32 * H ^ 2)
  let Cent : ℝ := 16 * (H + 2) ^ 2 / lo
  let C : ℝ := Cfin + Cent
  obtain ⟨n0, hn0⟩ := exists_nat_ge
    (T ^ 2 + 32 * q / lo + 32 * q + 64)
  have hH : 1 ≤ H := by dsimp [H]; exact le_trans (by norm_num) (le_max_left _ _)
  have hhiH : hi ≤ H := le_max_right _ _
  have hC : 0 < C := by dsimp [C, Cfin, Cent, H]; positivity
  refine ⟨C, hC, n0, ?_⟩
  intro n M ks hn hM hdeglo hdeghi hpos hKlog
  let K : ℕ := ∑ i, ks i
  let A : ℕ := (n - K).choose 2
  let b : ℕ := M + q - K
  let r : ℕ := K - q
  have hnlarge : T ^ 2 + 32 * q / lo + 32 * q + 64 ≤ (n : ℝ) :=
    le_trans hn0 (by exact_mod_cast hn)
  have hn64 : 64 ≤ n := by
    have hrest : 0 ≤ T ^ 2 + 32 * (q : ℝ) / lo + 32 * q := by positivity
    have hnr64 : (64 : ℝ) ≤ n := by linarith only [hnlarge, hrest]
    exact_mod_cast hnr64
  have hn64R : (64 : ℝ) ≤ n := by exact_mod_cast hn64
  have hnr : 0 < (n : ℝ) := by positivity
  have hT0 : 0 ≤ T := by dsimp [T]; positivity
  have h8H : 8 * H ≤ T := by
    dsimp [T]
    have hmax0 : (0 : ℝ) ≤ max 64 (max (32 * B / lo) (32 * B)) :=
      le_trans (by norm_num) (le_max_left _ _)
    linarith
  have hTsq : T ^ 2 ≤ (n : ℝ) := by
    have hrest : 0 ≤ 32 * (q : ℝ) / lo + 32 * q + 64 := by positivity
    linarith only [hnlarge, hrest]
  have hTsqrt : T ≤ Real.sqrt n := (Real.le_sqrt hT0 (by positivity)).2 hTsq
  have hlog := Real.log_natCast_le_rpow_div n (show (0 : ℝ) < 1 / 2 by norm_num)
  rw [show (n : ℝ) ^ (1 / 2 : ℝ) = Real.sqrt n by rw [Real.sqrt_eq_rpow]] at hlog
  have hKsmall : (K : ℝ) ≤ (n : ℝ) / 16 := by
    have hBT : 32 * B ≤ T := by dsimp [T]; linarith [le_max_right (32 * B / lo) (32 * B), le_max_right (64 : ℝ) (max (32 * B / lo) (32 * B))]
    have hsqrt : 32 * B ≤ Real.sqrt n := le_trans hBT hTsqrt
    have hsqsqrt := Real.sq_sqrt (show 0 ≤ (n : ℝ) by positivity)
    have : B * Real.log n ≤ (n : ℝ) / 16 := by
      nlinarith [mul_nonneg hB.le (sub_nonneg.mpr hlog),
        mul_nonneg (Real.sqrt_nonneg n) (sub_nonneg.mpr hsqrt)]
    exact le_trans (by simpa [K] using! hKlog) this
  have hKlo : (K : ℝ) ≤ lo * n / 16 := by
    have hBT : 32 * B / lo ≤ T := by dsimp [T]; linarith [le_max_left (32 * B / lo) (32 * B), le_max_right (64 : ℝ) (max (32 * B / lo) (32 * B))]
    have hsqrt : 32 * B / lo ≤ Real.sqrt n := le_trans hBT hTsqrt
    have hsqsqrt := Real.sq_sqrt (show 0 ≤ (n : ℝ) by positivity)
    have : B * Real.log n ≤ lo * n / 16 := by
      field_simp [ne_of_gt hlo] at hsqrt ⊢
      nlinarith [mul_nonneg hB.le (sub_nonneg.mpr hlog),
        mul_nonneg (Real.sqrt_nonneg n) (sub_nonneg.mpr hsqrt)]
    exact le_trans (by simpa [K] using! hKlog) this
  have hqK : q ≤ K := by
    have hcard := Finset.card_nsmul_le_sum
      (Finset.univ : Finset (Fin q)) ks 1 (by
        intro i hi
        exact Nat.succ_le_iff.mpr (hpos i))
    simpa [K] using! hcard
  have hKn : K ≤ n := by
    have hKnR : (K : ℝ) ≤ n := by linarith only [hKsmall, hnr]
    exact_mod_cast hKnR
  have hMlo : lo * (n : ℝ) / 2 ≤ M := by
    unfold degreeAt at hdeglo
    field_simp at hdeglo
    nlinarith only [hdeglo]
  have hMhi : (M : ℝ) ≤ H * n / 2 := by
    unfold degreeAt at hdeghi
    field_simp at hdeghi
    nlinarith only [hdeghi, mul_nonneg (sub_nonneg.mpr hhiH) hnr.le]
  have hMpos : 0 < M := by
    have : 0 < (M : ℝ) := lt_of_lt_of_le (by positivity) hMlo
    exact_mod_cast this
  have hKM : K ≤ M + q := by
    have hKMreal : (K : ℝ) ≤ (M : ℝ) + q := by
      nlinarith only [hKlo, hMlo, mul_pos hlo hnr,
        (show (0 : ℝ) ≤ q by positivity)]
    exact_mod_cast hKMreal
  have hrM : r ≤ M := by dsimp [r]; omega
  have hbEq : b = M - r := by dsimp [b, r]; omega
  have hbM : b ≤ M := by rw [hbEq]; omega
  have hbLo : lo * (n : ℝ) / 4 ≤ b := by
    rw [show (b : ℝ) = (M : ℝ) - r by rw [hbEq, Nat.cast_sub hrM]]
    have hrK : (r : ℝ) ≤ K := by exact_mod_cast Nat.sub_le K q
    nlinarith only [hrK, hKlo, hMlo, mul_pos hlo hnr]
  have hqHalf : (q : ℝ) ≤ (b : ℝ) / 2 := by
    have hqn : (32 : ℝ) * q / lo ≤ n := by
      have hrest : 0 ≤ T ^ 2 + 32 * (q : ℝ) + 64 := by positivity
      linarith only [hnlarge, hrest]
    have hqn' : (32 : ℝ) * q ≤ lo * n := by
      have := (div_le_iff₀ hlo).1 hqn
      nlinarith only [this]
    nlinarith only [hbLo, hqn', (show (0 : ℝ) ≤ q by positivity)]
  have hNcast : (capacity n : ℝ) = (n : ℝ) * (n - 1) / 2 := by
    unfold capacity
    rw [Nat.cast_choose_two]
  have hNlower : (n : ℝ) ^ 2 / 4 ≤ capacity n := by
    rw [hNcast]
    nlinarith only [hn64R, sq_nonneg ((n : ℝ) - 2)]
  have hNpos : 0 < capacity n := by
    have hNposR : 0 < (capacity n : ℝ) := lt_of_lt_of_le (by positivity) hNlower
    exact_mod_cast hNposR
  have hAcast : (A : ℝ) = ((n : ℝ) - K) * ((n : ℝ) - K - 1) / 2 := by
    dsimp [A]
    rw [Nat.cast_choose_two, Nat.cast_sub hKn]
  have hAlower : (n : ℝ) ^ 2 / 4 ≤ A := by
    rw [hAcast]
    have hx : 15 * (n : ℝ) / 16 ≤ (n : ℝ) - K := by
      linarith only [hKsmall]
    have hy : 7 * (n : ℝ) / 8 ≤ (n : ℝ) - K - 1 := by
      linarith only [hKsmall, hn64R]
    nlinarith only [mul_le_mul hx hy (by positivity)
      (le_trans (by positivity) hx), sq_nonneg (n : ℝ)]
  have hApos : 0 < A := by
    have hAposR : 0 < (A : ℝ) := lt_of_lt_of_le (by positivity) hAlower
    exact_mod_cast hAposR
  have h2K : 2 * (K : ℝ) ≤ n := by linarith only [hKsmall, hnr]
  have h2r : 2 * (r : ℝ) ≤ M := by
    have hrK : (r : ℝ) ≤ K := by exact_mod_cast Nat.sub_le K q
    nlinarith only [hrK, hKlo, hMlo, mul_pos hlo hnr]
  -- Share the threshold consequence and keep arithmetic searches independent
  -- of the growing collection of logarithmic and combinatorial hypotheses.
  have hT1 : 1 ≤ T := by linarith only [h8H, hH]
  have hTn : T ≤ (n : ℝ) := by
    nlinarith only [hTsq, hT1, sq_nonneg (T - 1)]
  have hHn : H ≤ (n : ℝ) / 8 := by linarith only [h8H, hTn]
  have hHnMul := mul_nonneg (sub_nonneg.mpr hHn) hnr.le
  have h2b : 2 * (b : ℝ) ≤ A := by
    have hbN : (b : ℝ) ≤ H * n / 2 := le_trans (by exact_mod_cast hbM) hMhi
    nlinarith only [hbN, hAlower, hHnMul, sq_nonneg (n : ℝ)]
  have h2M : 2 * (M : ℝ) ≤ capacity n := by
    nlinarith only [hMhi, hNlower, hHnMul, sq_nonneg (n : ℝ)]
  have hbA : b ≤ A := by
    have hbAreal : (b : ℝ) ≤ A := by
      linarith only [h2b, (show (0 : ℝ) ≤ b by positivity)]
    exact_mod_cast hbAreal
  have hJ := tupleMoment_pos hF n M q ks hM hpos hKn hKM hbA
  have hlog := tupleLog_to_finiteMain hF n M q ks hM hpos hKn hKM hbA
    (by omega) hMpos hApos hNpos (lt_of_lt_of_le hlo hdeglo) hqK
    (by simpa [K] using! h2K) (by simpa [K, r] using h2r)
    (by simpa [K, A, b] using! h2b) h2M
  have hNupper : (capacity n : ℝ) ≤ (n : ℝ) ^ 2 := by
    rw [hNcast]
    nlinarith only [hnr, sq_nonneg (n : ℝ)]
  have hNA0 : 0 ≤ (capacity n : ℝ) - A := by
    have hAle : A ≤ capacity n := by
      dsimp [A, capacity]
      exact Nat.choose_le_choose 2 (Nat.sub_le n K)
    exact sub_nonneg.mpr (by exact_mod_cast hAle)
  have hNA : (capacity n : ℝ) - A ≤ (K : ℝ) * n := by
    rw [hNcast, hAcast]
    nlinarith only [sq_nonneg (K : ℝ), (show (0 : ℝ) ≤ K by positivity)]
  have hdegree : 2 * (M : ℝ) = degreeAt n M * n := by
    unfold degreeAt
    field_simp
  have hn1pos : (0 : ℝ) < n - 1 := by linarith only [hn64R]
  have hlogA : Real.log (A : ℝ) = Real.log (capacity n : ℝ) +
      Real.log (1 - (K : ℝ) / n) + Real.log (1 - (K : ℝ) / (n - 1)) := by
    have hn1 : (n : ℝ) - 1 ≠ 0 := ne_of_gt hn1pos
    have hAeq : (A : ℝ) = (capacity n : ℝ) * (1 - (K : ℝ) / n) *
        (1 - (K : ℝ) / (n - 1)) := by
      rw [hNcast, hAcast]
      field_simp [hnr.ne', hn1]
      ring
    have hx0 : 1 - (K : ℝ) / n ≠ 0 :=
      ne_of_gt (sub_pos.mpr ((div_lt_one hnr).2 (by linarith only [hKsmall, hnr])))
    have hw0 : 1 - (K : ℝ) / ((n : ℝ) - 1) ≠ 0 :=
      ne_of_gt (sub_pos.mpr ((div_lt_one hn1pos).2
        (by linarith only [hKsmall, hn64R])))
    rw [hAeq, Real.log_mul (mul_ne_zero (ne_of_gt (by exact_mod_cast hNpos)) hx0) hw0,
      Real.log_mul (ne_of_gt (by exact_mod_cast hNpos)) hx0]
  have hbalance : Real.log (n : ℝ) + Real.log (M : ℝ) -
      Real.log (capacity n : ℝ) - Real.log (degreeAt n M) =
      Real.log ((n : ℝ) / (n - 1)) := by
    have hlam0 : degreeAt n M ≠ 0 := ne_of_gt (lt_of_lt_of_le hlo hdeglo)
    have hn1 : (n : ℝ) - 1 ≠ 0 := ne_of_gt hn1pos
    have htwo : (2 : ℝ) ≠ 0 := by norm_num
    have hMform : (M : ℝ) = degreeAt n M * n / 2 := by
      rw [← hdegree]
      ring
    rw [hMform, hNcast]
    rw [Real.log_div (mul_ne_zero hlam0 hnr.ne') htwo,
      Real.log_mul hlam0 hnr.ne']
    rw [Real.log_div (mul_ne_zero hnr.ne' hn1) htwo,
      Real.log_mul hnr.ne' hn1]
    rw [Real.log_div hnr.ne' hn1]
    ring
  have hbpos : 0 < b := by
    have hbposR : (0 : ℝ) < b := lt_of_lt_of_le (by positivity) hbLo
    exact_mod_cast hbposR
  have hfiniteMain := realFinite_compact_remainder
    (n := (n : ℝ)) (M := (M : ℝ)) (lam := degreeAt n M)
    (N := (capacity n : ℝ)) (A := (A : ℝ)) (K := (K : ℝ))
    (Q := (q : ℝ)) (r := (r : ℝ)) (b := (b : ℝ))
    (lo := lo) (H := H)
    (by dsimp [r]; rw [Nat.cast_sub hqK])
    (by rw [hbEq, Nat.cast_sub hrM]) (by exact_mod_cast (show 8 ≤ n by omega))
    (by positivity) (by exact_mod_cast (show 1 ≤ K by omega)) hKsmall hKlo
    (by positivity) (by exact_mod_cast hqK) hlo hH hMlo hMhi
    (by exact_mod_cast (show 1 ≤ M by omega))
    (by exact_mod_cast (show 1 ≤ b by omega))
    hbLo
    (by exact_mod_cast hbM) hqHalf (by exact_mod_cast hNpos)
    (by exact_mod_cast hApos) hNlower hAlower hNupper
    hNA0 hNA hnr.ne' (ne_of_gt (lt_of_lt_of_le hlo hdeglo)) hdegree hlogA hbalance
  rw [← tupleFiniteMain_eq_real n M q K] at hfiniteMain
  have hfactor :
      2 * (K : ℝ) / n + 2 * (b : ℝ) ^ 3 / (A : ℝ) ^ 2 +
          2 * (r : ℝ) / M + 2 * (M : ℝ) ^ 3 / (capacity n : ℝ) ^ 2 ≤
        (2 + 64 * H ^ 3 + 4 / lo) * (K : ℝ) / n := by
    have hbH : (b : ℝ) ≤ H * n := by
      have hbMr : (b : ℝ) ≤ M := by exact_mod_cast hbM
      exact hbMr.trans (by linarith only [hMhi, (show 0 ≤ H * (n : ℝ) by positivity)])
    have hrK : (r : ℝ) ≤ K := by exact_mod_cast Nat.sub_le K q
    have hK1 : 1 ≤ (K : ℝ) := by exact_mod_cast (show 1 ≤ K by omega)
    have hbterm : 2 * (b : ℝ) ^ 3 / (A : ℝ) ^ 2 ≤ 32 * H ^ 3 / n := by
      calc
        _ ≤ 2 * (H * n) ^ 3 / ((n : ℝ) ^ 2 / 4) ^ 2 := by gcongr
        _ = 32 * H ^ 3 / n := by field_simp; ring
    have hMterm : 2 * (M : ℝ) ^ 3 / (capacity n : ℝ) ^ 2 ≤ 32 * H ^ 3 / n := by
      have hMH : (M : ℝ) ≤ H * n := by
        linarith only [hMhi, (show 0 ≤ H * (n : ℝ) by positivity)]
      calc
        _ ≤ 2 * (H * n) ^ 3 / ((n : ℝ) ^ 2 / 4) ^ 2 := by gcongr
        _ = 32 * H ^ 3 / n := by field_simp; ring
    have hrterm : 2 * (r : ℝ) / M ≤ 4 / lo * K / n := by
      field_simp
      nlinarith only [mul_nonneg (show 0 ≤ (r : ℝ) by positivity) (sub_nonneg.mpr hMlo),
        mul_nonneg (sub_nonneg.mpr hrK) (by positivity : 0 ≤ (M : ℝ))]
    have hcoef : 64 * H ^ 3 / (n : ℝ) ≤ 64 * H ^ 3 * K / n := by
      calc
        _ = (64 * H ^ 3 / n) * 1 := by ring
        _ ≤ (64 * H ^ 3 / n) * K :=
          mul_le_mul_of_nonneg_left hK1 (by positivity)
        _ = _ := by ring
    calc
      _ ≤ 2 * (K : ℝ) / n + 32 * H ^ 3 / n + 4 / lo * K / n +
          32 * H ^ 3 / n :=
        add_le_add (add_le_add (add_le_add le_rfl hbterm) hrterm) hMterm
      _ = 2 * (K : ℝ) / n + 64 * H ^ 3 / n + 4 / lo * K / n := by ring
      _ ≤ 2 * (K : ℝ) / n + 64 * H ^ 3 * K / n + 4 / lo * K / n := by
        exact add_le_add (add_le_add le_rfl hcoef) le_rfl
      _ = _ := by ring
  have hrem :
      |Real.log (tupleMoment n M q ks / tupleLeading n M q ks) -
          ((n : ℝ) * entropyCore (degreeAt n M) ((K : ℝ) / n) +
            rate (degreeAt n M) * K)| ≤ Cfin * (K : ℝ) ^ 2 / n := by
    have htri := abs_add_le
      (Real.log (tupleMoment n M q ks / tupleLeading n M q ks) - tupleFiniteMain n M q K)
      (tupleFiniteMain n M q K - ((n : ℝ) * entropyCore (degreeAt n M) ((K : ℝ) / n) +
        rate (degreeAt n M) * K))
    dsimp [Cfin]
    rw [show Real.log (tupleMoment n M q ks / tupleLeading n M q ks) -
        ((n : ℝ) * entropyCore (degreeAt n M) ((K : ℝ) / n) + rate (degreeAt n M) * K) =
      (Real.log (tupleMoment n M q ks / tupleLeading n M q ks) - tupleFiniteMain n M q K) +
      (tupleFiniteMain n M q K - ((n : ℝ) * entropyCore (degreeAt n M) ((K : ℝ) / n) +
        rate (degreeAt n M) * K)) by ring]
    have hfactorSq :
        (2 + 64 * H ^ 3 + 4 / lo) * (K : ℝ) / n ≤
        (2 + 64 * H ^ 3 + 4 / lo) * (K : ℝ) ^ 2 / n := by
      have hK1 : 1 ≤ (K : ℝ) := by exact_mod_cast (show 1 ≤ K by omega)
      have hcoef : 0 ≤ 2 + 64 * H ^ 3 + 4 / lo := by positivity
      have hsq : (K : ℝ) ≤ K ^ 2 := by nlinarith only [hK1]
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hsq hcoef) hnr.le
    calc
      _ ≤ (2 + 64 * H ^ 3 + 4 / lo) * (K : ℝ) ^ 2 / n +
          (8 * H + 12 / lo + 6 + 32 * H ^ 2) * (K : ℝ) ^ 2 / n :=
        le_trans htri (add_le_add (le_trans hlog (le_trans hfactor hfactorSq)) hfiniteMain)
      _ = _ := by ring
  have hent := scaled_entropy_compact (n := (n : ℝ))
    (lam := degreeAt n M) (K := (K : ℝ)) (lo := lo) (H := H)
    hnr hlo hH hdeglo (hdeghi.trans hhiH) (by positivity)
    (le_trans hKsmall (by linarith only [hnr]))
    (le_trans hKlo (by nlinarith only [mul_pos hlo hnr]))
  constructor
  · exact hJ
  · rw [← show (K : ℝ) = ∑ i, (ks i : ℝ) by simp [K]]
    calc
      |Real.log (tupleMoment n M q ks / tupleLeading n M q ks)| ≤
          |Real.log (tupleMoment n M q ks / tupleLeading n M q ks) -
            ((n : ℝ) * entropyCore (degreeAt n M) ((K : ℝ) / n) +
              rate (degreeAt n M) * K)| +
          |(n : ℝ) * entropyCore (degreeAt n M) ((K : ℝ) / n) +
              rate (degreeAt n M) * K| := by
        simpa only [sub_add_cancel] using! abs_add_le
          (Real.log (tupleMoment n M q ks / tupleLeading n M q ks) -
            ((n : ℝ) * entropyCore (degreeAt n M) ((K : ℝ) / n) + rate (degreeAt n M) * K))
          ((n : ℝ) * entropyCore (degreeAt n M) ((K : ℝ) / n) + rate (degreeAt n M) * K)
      _ ≤ Cfin * (K : ℝ) ^ 2 / n + Cent * (K : ℝ) ^ 2 / n := by
        exact add_le_add hrem (by simpa [Cent] using! hent)
      _ = C * (K : ℝ) ^ 2 / n := by
        dsimp [C]
        ring

end

end Erdos745.WrapUp.Proofs.Internal.W04_TUPLES_Compact


/-!
The conditioned independent-edge envelope.  All changes of exponent are kept
as exact natural-number identities before passage to `ℝ`; in particular the
fixed shift `K-q` is never simplified by an asymptotic argument.
-/
namespace Erdos745.WrapUp.Proofs.Internal.W04_TUPLES_IndependentEnvelope

noncomputable section
open scoped BigOperators

open W04_TUPLES_Foundation
open W04_TUPLES_Local
open W04_TUPLES_FiniteBounds
open W04_TUPLES_Conditioning
open W04_TUPLES_IndependentEntropy
open Erdos745.WrapUp.Proofs.W06_POISSON

private theorem capacity_cast {n : ℕ} :
    (capacity n : ℝ) = (n : ℝ) * (n - 1) / 2 := by
  unfold capacity
  rw [Nat.cast_choose_two]

private theorem complement_remainder_cast_identity
    {n K q : ℕ} (hn : 4 ≤ n) (hKn : K ≤ n) (hqK : q ≤ K) :
    ((capacity n - (n - K).choose 2 - (K - q) : ℕ) : ℝ) =
      (K : ℝ) * n - (K : ℝ) * ((K : ℝ) + 3) / 2 + q := by
  have hN : (capacity n : ℝ) = (n : ℝ) * (n - 1) / 2 := capacity_cast
  have hA : (((n - K).choose 2 : ℕ) : ℝ) =
      ((n : ℝ) - K) * ((n : ℝ) - K - 1) / 2 := by
    rw [Nat.cast_choose_two, Nat.cast_sub hKn]
  have hAN : (n - K).choose 2 ≤ capacity n := by
    exact_mod_cast (show (((n - K).choose 2 : ℕ) : ℝ) ≤ capacity n by
      rw [hN, hA]
      have hKr : (K : ℝ) ≤ n := by exact_mod_cast hKn
      nlinarith [mul_nonneg (show 0 ≤ (K : ℝ) by positivity)
        (sub_nonneg.mpr hKr)])
  have hrNA : K - q ≤ capacity n - (n - K).choose 2 := by
    exact_mod_cast (show ((K - q : ℕ) : ℝ) ≤
        (capacity n - (n - K).choose 2 : ℕ) by
      rw [Nat.cast_sub hAN, Nat.cast_sub hqK, hN, hA]
      have hKr : (K : ℝ) ≤ n := by exact_mod_cast hKn
      have hqr : (q : ℝ) ≤ K := by exact_mod_cast hqK
      have hnr : (4 : ℝ) ≤ n := by exact_mod_cast hn
      nlinarith [mul_nonneg (show 0 ≤ (K : ℝ) by positivity)
        (sub_nonneg.mpr hKr)])
  rw [Nat.cast_sub hrNA, Nat.cast_sub hAN, Nat.cast_sub hqK, hN, hA]
  ring

private theorem probability_eq_degree
    {n M : ℕ} (hn : 2 ≤ n) :
    (M : ℝ) / capacity n = degreeAt n M / ((n : ℝ) - 1) := by
  rw [capacity_cast]
  unfold degreeAt
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hn1 : (n : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  field_simp

private theorem complement_exponent_comparison
    {n K q : ℕ} {lam : ℝ}
    (hn : 4 ≤ n) (hKn : K ≤ n) (hqK : q ≤ K)
    (hlam0 : 0 ≤ lam) :
    -(lam / ((n : ℝ) - 1)) *
          (capacity n - (n - K).choose 2 - (K - q) : ℕ) ≤
      -lam * K + lam * (K : ℝ) ^ 2 / (2 * n) + 2 * lam := by
  have hn0 : 0 < (n : ℝ) := by positivity
  have hn1 : 0 < (n : ℝ) - 1 := by
    have : (4 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hKnonneg : 0 ≤ (K : ℝ) := by positivity
  have hKnR : (K : ℝ) ≤ n := by exact_mod_cast hKn
  have hq0 : 0 ≤ (q : ℝ) := by positivity
  have hqKreal : (q : ℝ) ≤ K := by exact_mod_cast hqK
  rw [complement_remainder_cast_identity hn hKn hqK]
  have hden : 0 < 2 * (n : ℝ) * ((n : ℝ) - 1) := by positivity
  have hnum : (n : ℝ) * K + (K : ℝ) ^ 2 - 2 * n * q ≤
      4 * (n : ℝ) * ((n : ℝ) - 1) := by
    have hn4r : (4 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith [mul_nonneg hKnonneg (sub_nonneg.mpr hKnR),
      mul_nonneg hq0 hn0.le]
  rw [show
    -(lam / ((n : ℝ) - 1)) *
        ((K : ℝ) * n - (K : ℝ) * ((K : ℝ) + 3) / 2 + q) =
      (-lam * K + lam * (K : ℝ) ^ 2 / (2 * n)) +
        lam * ((n : ℝ) * K + (K : ℝ) ^ 2 - 2 * n * q) /
          (2 * n * (n - 1)) by field_simp; ring]
  have hfrac : lam * ((n : ℝ) * K + (K : ℝ) ^ 2 - 2 * n * q) /
      (2 * n * (n - 1)) ≤ 2 * lam := by
    apply (div_le_iff₀ hden).2
    nlinarith [mul_nonneg hlam0 (sub_nonneg.mpr hnum)]
  linarith

private theorem succ_ratio_pow_bound
    {n K : ℕ} (hn : 2 ≤ n) (hKn : K ≤ n) :
    ((n : ℝ) / ((n : ℝ) - 1)) ^ K ≤ Real.exp 2 := by
  have hn0 : 0 < (n : ℝ) := by positivity
  have hn1 : 0 < (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hratio : 0 < (n : ℝ) / ((n : ℝ) - 1) := div_pos hn0 hn1
  have hlog := log_succ_ratio_bound (n := (n : ℝ)) (by exact_mod_cast hn)
  have hlogUpper : Real.log ((n : ℝ) / ((n : ℝ) - 1)) ≤ 2 / n :=
    le_trans (le_abs_self _) hlog
  calc
    ((n : ℝ) / ((n : ℝ) - 1)) ^ K =
        Real.exp ((K : ℝ) * Real.log ((n : ℝ) / ((n : ℝ) - 1))) := by
          calc
            ((n : ℝ) / ((n : ℝ) - 1)) ^ K =
                (Real.exp (Real.log ((n : ℝ) / ((n : ℝ) - 1)))) ^ K := by
                  rw [Real.exp_log hratio]
            _ = _ := (Real.exp_nat_mul _ _).symm
    _ ≤ Real.exp ((K : ℝ) * (2 / n)) := by
          apply Real.exp_le_exp.mpr
          exact mul_le_mul_of_nonneg_left hlogUpper (by positivity)
    _ ≤ Real.exp 2 := by
          apply Real.exp_le_exp.mpr
          have hKnR : (K : ℝ) ≤ n := by exact_mod_cast hKn
          field_simp
          nlinarith

private theorem complement_power_bound
    {p : ℝ} {s : ℕ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (1 - p) ^ s ≤ Real.exp (-p * s) := by
  have hbase : 0 ≤ 1 - p := sub_nonneg.mpr hp1
  calc
    (1 - p) ^ s ≤ (Real.exp (-p)) ^ s :=
      pow_le_pow_left₀ hbase (Real.one_sub_le_exp_neg p) s
    _ = Real.exp (-p * s) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring

private theorem tupleFactor_stirling_bound
    (q : ℕ) (ks : Fin q → ℕ) (R : ℝ)
    (hR0 : 0 ≤ R) (hR : ∀ k : ℕ, cayleyStirlingRatio k ≤ R)
    (hpos : ∀ i, 0 < ks i) :
    (∏ i, (cayley (ks i) : ℝ) / ((ks i).factorial : ℝ)) ≤
      (R / Real.sqrt (2 * Real.pi)) ^ q *
        (∏ i, (ks i : ℝ) ^ (-5 / 2 : ℝ)) *
        Real.exp (∑ i, (ks i : ℝ)) := by
  let C : ℝ := R / Real.sqrt (2 * Real.pi)
  have hC0 : 0 ≤ C := by dsimp [C]; positivity
  calc
    (∏ i, (cayley (ks i) : ℝ) / ((ks i).factorial : ℝ)) ≤
        ∏ i, (C * (ks i : ℝ) ^ (-5 / 2 : ℝ) *
          Real.exp (ks i : ℝ)) := by
      apply Finset.prod_le_prod₀
      · intro i hi
        positivity
      · intro i hi
        have hk : 0 < (ks i : ℝ) := Nat.cast_pos.mpr (hpos i)
        have hkernel :
            (cayley (ks i) : ℝ) / ((ks i).factorial : ℝ) =
              cayleyKernel (ks i) * Real.exp (ks i : ℝ) := by
          unfold cayleyKernel
          calc
            (cayley (ks i) : ℝ) / ((ks i).factorial : ℝ) =
                ((cayley (ks i) : ℝ) / ((ks i).factorial : ℝ)) * 1 := by ring
            _ = ((cayley (ks i) : ℝ) / ((ks i).factorial : ℝ)) *
                (Real.exp (-(ks i : ℝ)) * Real.exp (ks i : ℝ)) := by
                  rw [← Real.exp_add]
                  simp
            _ = (((cayley (ks i) : ℝ) / ((ks i).factorial : ℝ)) *
                Real.exp (-(ks i : ℝ))) * Real.exp (ks i : ℝ) := by ring
        rw [hkernel, cayleyKernel_eq_stirling (ks i) (hpos i)]
        rw [show (-(5 / 2) : ℝ) = (-5 / 2 : ℝ) by ring]
        have hr : cayleyStirlingRatio (ks i) / Real.sqrt (2 * Real.pi) ≤ C := by
          dsimp [C]
          exact div_le_div_of_nonneg_right (hR (ks i)) (by positivity)
        have hpow0 : 0 ≤ (ks i : ℝ) ^ (-5 / 2 : ℝ) :=
          (Real.rpow_pos_of_pos hk _).le
        have hexp0 : 0 ≤ Real.exp (ks i : ℝ) := (Real.exp_pos _).le
        change (cayleyStirlingRatio (ks i) / Real.sqrt (2 * Real.pi) *
            (ks i : ℝ) ^ (-5 / 2 : ℝ)) * Real.exp (ks i : ℝ) ≤
          (C * (ks i : ℝ) ^ (-5 / 2 : ℝ)) * Real.exp (ks i : ℝ)
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hr hpow0) hexp0
    _ = C ^ q * (∏ i, (ks i : ℝ) ^ (-5 / 2 : ℝ)) *
          Real.exp (∑ i, (ks i : ℝ)) := by
      rw [show (∏ i : Fin q,
          (C * (ks i : ℝ) ^ (-5 / 2 : ℝ) * Real.exp (ks i : ℝ))) =
        (∏ _i : Fin q, C) *
          (∏ i : Fin q, (ks i : ℝ) ^ (-5 / 2 : ℝ)) *
          (∏ i : Fin q, Real.exp (ks i : ℝ)) by
            rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]]
      simp [← Real.exp_sum]
    _ = _ := rfl

private theorem endpoint_falling_exp_bound
    {n : ℕ} (hn : 2 ≤ n) :
    (falling n n : ℝ) * Real.exp (n : ℝ) ≤
      6 * (n : ℝ) ^ (n + 1) := by
  have hnpos : 0 < n := by omega
  have hfall : falling n n = n.factorial := by
    unfold falling
    rw [← Nat.descFactorial_eq_prod_range, Nat.descFactorial_self]
  rw [hfall, factorial_eq_stirlingSeq hnpos]
  have hseq := stirlingSeq_upper hnpos
  have hseq1 : Stirling.stirlingSeq 1 = Real.exp 1 / Real.sqrt 2 :=
    Stirling.stirlingSeq_one
  have hexp : Real.exp 1 < 3 := Real.exp_one_lt_d9.trans_le (by norm_num)
  have hsqrtLower : 1 ≤ Real.sqrt (2 : ℝ) := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hseq3 : Stirling.stirlingSeq n ≤ 3 := by
    rw [hseq1] at hseq
    calc
      Stirling.stirlingSeq n ≤ Real.exp 1 / Real.sqrt 2 := hseq
      _ ≤ Real.exp 1 := (div_le_self (Real.exp_pos 1).le hsqrtLower)
      _ ≤ 3 := hexp.le
  have hsqrt : Real.sqrt (2 * (n : ℝ)) ≤ 2 * n := by
    have hnonneg : 0 ≤ (2 * (n : ℝ)) := by positivity
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · have hnr : (2 : ℝ) ≤ n := by exact_mod_cast hn
      nlinarith
  have he : ((n : ℝ) / Real.exp 1) ^ n * Real.exp (n : ℝ) =
      (n : ℝ) ^ n := by
    rw [div_pow, ← Real.exp_nat_mul]
    have he1 : Real.exp ((n : ℝ) * 1) = Real.exp 1 ^ n := by
      rw [Real.exp_nat_mul]
    rw [show (n : ℝ) * 1 = n by ring] at he1
    field_simp [Real.exp_ne_zero]
  calc
    Stirling.stirlingSeq n *
          (Real.sqrt (2 * (n : ℝ)) * (((n : ℝ) / Real.exp 1) ^ n)) *
        Real.exp (n : ℝ) ≤
      3 * ((2 * n) * (((n : ℝ) / Real.exp 1) ^ n)) *
        Real.exp (n : ℝ) := by gcongr
    _ = 6 * (n : ℝ) * ((n : ℝ) ^ n) := by
      rw [show 3 * ((2 * (n : ℝ)) * (((n : ℝ) / Real.exp 1) ^ n)) *
          Real.exp (n : ℝ) =
        6 * (n : ℝ) * ((((n : ℝ) / Real.exp 1) ^ n) *
          Real.exp (n : ℝ)) by ring, he]
    _ = 6 * (n : ℝ) ^ (n + 1) := by rw [pow_succ]; ring

private theorem falling_exp_entropy_bound
    {n K : ℕ} (hn : 2 ≤ n) (hKn : K ≤ n) :
    (falling n K : ℝ) * Real.exp (K : ℝ) ≤
      6 * (n : ℝ) ^ (K + 1) *
        Real.exp (-((n : ℝ) - K) * Real.log (1 - (K : ℝ) / n)) := by
  by_cases hKn' : K = n
  · subst K
    simpa using! endpoint_falling_exp_bound hn
  · have hKlt : K < n := lt_of_le_of_ne hKn hKn'
    have hnpos : 0 < n := by omega
    have hnr : 0 < (n : ℝ) := by positivity
    have htpos : 0 < 1 - (K : ℝ) / n := by
      exact sub_pos.mpr ((div_lt_one hnr).2 (by exact_mod_cast hKlt))
    have hfallpos : 0 < (falling n K : ℝ) := by
      exact_mod_cast (falling_pos hKn)
    have hsum := log_sum_integral_remainder
      (X := (n : ℝ)) (s := K) hnr (by exact_mod_cast hKlt)
    have hint := integral_logOneSubDiv (X := (n : ℝ)) (S := (K : ℝ)) hnr (by positivity)
      (by exact_mod_cast hKlt)
    rw [hint] at hsum
    have hsumUpper : logFallingSum (n : ℝ) K ≤
        -((n : ℝ) - K) * Real.log (1 - (K : ℝ) / n) - K -
          Real.log (1 - (K : ℝ) / n) := by
      linarith [le_abs_self (logFallingSum (n : ℝ) K -
        (-((n : ℝ) - K) * Real.log (1 - (K : ℝ) / n) - K))]
    have hlogLower : -Real.log (1 - (K : ℝ) / n) ≤ Real.log n := by
      have hbase : (1 : ℝ) / n ≤ 1 - (K : ℝ) / n := by
        rw [show 1 - (K : ℝ) / n = ((n : ℝ) - K) / n by field_simp]
        exact div_le_div_of_nonneg_right (by exact_mod_cast (show 1 ≤ n - K by omega)) hnr.le
      have hlogmono := Real.strictMonoOn_log.monotoneOn
        (show 0 < (1 : ℝ) / n by positivity)
        htpos
        hbase
      rw [Real.log_div one_ne_zero (ne_of_gt hnr), Real.log_one] at hlogmono
      linarith
    have hlogfall := log_falling_eq_sum hnpos hKn
    have hlogUpper : Real.log (falling n K : ℝ) + K ≤
        (K + 1 : ℕ) * Real.log n -
          ((n : ℝ) - K) * Real.log (1 - (K : ℝ) / n) := by
      rw [hlogfall]
      push_cast
      linarith
    have hexp := Real.exp_le_exp.mpr hlogUpper
    have hrhs0 : 0 ≤ (n : ℝ) ^ (K + 1) *
        Real.exp (-((n : ℝ) - K) * Real.log (1 - (K : ℝ) / n)) := by
      positivity
    calc
      (falling n K : ℝ) * Real.exp (K : ℝ) ≤
          Real.exp ((K + 1 : ℕ) * Real.log n -
            ((n : ℝ) - K) * Real.log (1 - (K : ℝ) / n)) := by
        have hlhs : (falling n K : ℝ) * Real.exp (K : ℝ) =
            Real.exp (Real.log (falling n K : ℝ) + K) := by
          rw [Real.exp_add, Real.exp_log hfallpos]
        rw [hlhs]
        exact hexp
      _ = (n : ℝ) ^ (K + 1) *
            Real.exp (-((n : ℝ) - K) * Real.log (1 - (K : ℝ) / n)) := by
        rw [Real.exp_sub, Real.exp_nat_mul, Real.exp_log hnr]
        rw [div_eq_mul_inv, ← Real.exp_neg]
        congr 2
        ring
      _ ≤ 6 * (n : ℝ) ^ (K + 1) *
            Real.exp (-((n : ℝ) - K) * Real.log (1 - (K : ℝ) / n)) := by
        nlinarith

private theorem entropy_exponent_identity
    {n K : ℕ} {lam : ℝ} (hn : 0 < n) :
    -((n : ℝ) - K) * Real.log (1 - (K : ℝ) / n) +
          (K : ℝ) * Real.log lam - lam * K +
          lam * (K : ℝ) ^ 2 / (2 * n) =
      (n : ℝ) * independentEntropy lam ((K : ℝ) / n) := by
  unfold independentEntropy
  field_simp

set_option maxHeartbeats 1200000 in
theorem compactIndependentEntropyEnvelope
    (hF : FiniteEnumerationStatement)
    (lo hi : ℝ) (q : ℕ) (hlo0 : 0 < lo) (hlohi : lo ≤ hi) (hq : 0 < q) :
    ∃ D : ℝ, 0 < D ∧ ∃ n0 : ℕ, ∀ (n M : ℕ) (ks : Fin q → ℕ),
      n0 ≤ n → M ≤ capacity n →
      lo ≤ degreeAt n M → degreeAt n M ≤ hi →
      (∀ i, 0 < ks i) →
      tupleMoment n M q ks ≤
        D * (n : ℝ) ^ (q + 3) *
          (∏ i, (ks i : ℝ) ^ (-5 / 2 : ℝ)) *
          Real.exp ((n : ℝ) * independentEntropy (degreeAt n M)
            ((∑ i, (ks i : ℝ)) / n)) := by
  obtain ⟨R, hRpos, hR⟩ := cayleyStirlingRatio_bddAbove
  let C : ℝ := R / Real.sqrt (2 * Real.pi)
  let D : ℝ := 24 * C ^ q * Real.exp (2 + 2 * hi) / lo ^ q
  obtain ⟨nH, hnH⟩ := exists_nat_ge (hi + 3)
  refine ⟨D, by dsimp [D, C]; positivity, max 4 nH, ?_⟩
  intro n M ks hn hM hdeglo hdeghi hpos
  let K : ℕ := ∑ i, ks i
  let N : ℕ := capacity n
  let p : ℝ := (M : ℝ) / N
  let lam : ℝ := degreeAt n M
  have hn4 : 4 ≤ n := le_trans (le_max_left _ _) hn
  have hn2 : 2 ≤ n := by omega
  have hnpos : 0 < n := by omega
  have hnr : 0 < (n : ℝ) := by positivity
  have hnH' : nH ≤ n := le_trans (le_max_right _ _) hn
  have hnhi : hi + 3 ≤ (n : ℝ) := le_trans hnH (by exact_mod_cast hnH')
  have hlamlo : lo ≤ lam := hdeglo
  have hlamhi : lam ≤ hi := hdeghi
  have hlam0 : 0 < lam := lt_of_lt_of_le hlo0 hlamlo
  have hMpos : 0 < M := by
    by_contra hzero
    have : M = 0 := Nat.eq_zero_of_not_pos hzero
    subst M
    simp [lam, degreeAt] at hlam0
  have hMN : M < N := by
    dsimp [N]
    by_contra hnot
    have hEq : M = capacity n := Nat.le_antisymm hM (Nat.le_of_not_gt hnot)
    subst M
    unfold lam degreeAt at hlamhi
    rw [capacity_cast] at hlamhi
    field_simp at hlamhi
    nlinarith
  have hNpos : 0 < N := lt_of_lt_of_le hMpos hMN.le
  have hp0 : 0 < p := by dsimp [p]; positivity
  have hp1 : p ≤ 1 := by
    dsimp [p, N]
    exact (div_le_one (by positivity)).2 (by exact_mod_cast hM)
  have hpdeg : p = lam / ((n : ℝ) - 1) := by
    dsimp [p, lam, N]
    exact probability_eq_degree hn2
  have hqK : q ≤ K := by
    have hcard := Finset.card_nsmul_le_sum
      (Finset.univ : Finset (Fin q)) ks 1 (by
        intro i hi
        exact Nat.succ_le_iff.mpr (hpos i))
    simpa [K] using! hcard
  by_cases hKn : K ≤ n
  · have hcond := tupleMoment_le_conditionedIndependent hF n M q ks hn4
      (by simpa [N] using! hMN) hMpos hpos
    have hfac := tupleFactor_stirling_bound q ks R hRpos.le hR hpos
    have hfall := falling_exp_entropy_bound hn2 hKn
    have hcomp := complement_power_bound hp0.le hp1
      (s := capacity n - (n - K).choose 2 - (K - q))
    have hpLower : lo / n ≤ p := by
      rw [hpdeg]
      have hn1pos : 0 < (n : ℝ) - 1 := by nlinarith
      apply (div_le_div_iff₀ hnr hn1pos).2
      have hn1nonneg : 0 ≤ (n : ℝ) - 1 := hn1pos.le
      nlinarith [mul_nonneg hlo0.le hn1nonneg,
        mul_nonneg (sub_nonneg.mpr hlamlo) hnr.le]
    have hpinv : p⁻¹ ≤ (n : ℝ) / lo := by
      rw [inv_le_comm₀ hp0 (div_pos hnr hlo0)]
      simpa [div_eq_mul_inv, mul_comm] using! hpLower
    have hshift : p ^ (K - q) ≤ p ^ K * ((n : ℝ) / lo) ^ q := by
      have hpq : 0 < p ^ q := pow_pos hp0 _
      have heq : p ^ K = p ^ (K - q) * p ^ q := by
        rw [← pow_add, Nat.sub_add_cancel hqK]
      rw [heq]
      calc
        p ^ (K - q) ≤ p ^ (K - q) * (p ^ q * ((n : ℝ) / lo) ^ q) := by
          have hunit : 1 ≤ p ^ q * ((n : ℝ) / lo) ^ q := by
            rw [← mul_pow]
            have : 1 ≤ p * ((n : ℝ) / lo) := by
              rw [show p * ((n : ℝ) / lo) = p * n / lo by ring]
              apply (le_div_iff₀ hlo0).2
              have h := (div_le_iff₀ hnr).1 hpLower
              simpa using! h
            exact one_le_pow₀ this
          nlinarith [pow_nonneg hp0.le (K - q)]
        _ = (p ^ (K - q) * p ^ q) * ((n : ℝ) / lo) ^ q := by ring
    have hnpow : (n : ℝ) ^ K * p ^ K ≤
        lam ^ K * Real.exp 2 := by
      rw [← mul_pow, hpdeg, show (n : ℝ) * (lam / ((n : ℝ) - 1)) =
          lam * ((n : ℝ) / ((n : ℝ) - 1)) by ring, mul_pow]
      exact mul_le_mul_of_nonneg_left (succ_ratio_pow_bound hn2 hKn)
        (pow_nonneg hlam0.le K)
    have hcompExp := complement_exponent_comparison hn4 hKn hqK hlam0.le
    have hentropy := entropy_exponent_identity (K := K) (lam := lam) hnpos
    have hprod0 : 0 ≤ ∏ i, (ks i : ℝ) ^ (-5 / 2 : ℝ) := by
      apply Finset.prod_nonneg
      intro i hi
      exact (Real.rpow_pos_of_pos (Nat.cast_pos.mpr (hpos i)) _).le
    let P : ℝ := ∏ i, (ks i : ℝ) ^ (-5 / 2 : ℝ)
    have hP0 : 0 ≤ P := by simpa [P] using! hprod0
    have hfac0 : 0 ≤ ∏ i, (cayley (ks i) : ℝ) / ((ks i).factorial : ℝ) := by
      positivity
    have hfall0 : 0 ≤ (falling n K : ℝ) := by positivity
    have hC0 : 0 ≤ C := by dsimp [C]; positivity
    have hKcast : (K : ℝ) = ∑ i, (ks i : ℝ) := by simp [K]
    rw [← hKcast] at hfac
    rw [← hKcast]
    change tupleMoment n M q ks ≤
      D * (n : ℝ) ^ (q + 3) *
        (∏ i, (ks i : ℝ) ^ (-5 / 2 : ℝ)) *
        Real.exp ((n : ℝ) * independentEntropy lam ((K : ℝ) / n))
    have hfallfac :
        (falling n K : ℝ) *
            (∏ i, (cayley (ks i) : ℝ) / ((ks i).factorial : ℝ)) ≤
          (6 * (n : ℝ) ^ (K + 1) *
            Real.exp (-((n : ℝ) - K) * Real.log (1 - (K : ℝ) / n))) *
            (C ^ q * P) := by
      calc
        (falling n K : ℝ) *
            (∏ i, (cayley (ks i) : ℝ) / ((ks i).factorial : ℝ)) ≤
          (falling n K : ℝ) *
            ((C ^ q * P) * Real.exp (K : ℝ)) := by
              exact mul_le_mul_of_nonneg_left (by simpa [C, P] using! hfac) hfall0
        _ = (C ^ q * P) *
            ((falling n K : ℝ) * Real.exp (K : ℝ)) := by ring
        _ ≤ (C ^ q * P) *
            (6 * (n : ℝ) ^ (K + 1) *
              Real.exp (-((n : ℝ) - K) * Real.log (1 - (K : ℝ) / n))) := by
              exact mul_le_mul_of_nonneg_left hfall
                (mul_nonneg (pow_nonneg hC0 q) hP0)
        _ = _ := by ring
    have hstage :
        (falling n K : ℝ) *
              (∏ i, (cayley (ks i) : ℝ) / ((ks i).factorial : ℝ)) *
              p ^ (K - q) *
              (1 - p) ^ (capacity n - (n - K).choose 2 - (K - q)) ≤
          ((6 * (n : ℝ) ^ (K + 1) *
              Real.exp (-((n : ℝ) - K) * Real.log (1 - (K : ℝ) / n))) *
            (C ^ q * P) *
            (p ^ K * ((n : ℝ) / lo) ^ q) *
            Real.exp (-p *
              (capacity n - (n - K).choose 2 - (K - q) : ℕ))) := by
      have hleft0 : 0 ≤ (falling n K : ℝ) *
          (∏ i, (cayley (ks i) : ℝ) / ((ks i).factorial : ℝ)) :=
        mul_nonneg hfall0 hfac0
      have hright0 : 0 ≤ (6 * (n : ℝ) ^ (K + 1) *
          Real.exp (-((n : ℝ) - K) * Real.log (1 - (K : ℝ) / n))) *
          (C ^ q * P) := by positivity
      have hmul :
          ((falling n K : ℝ) *
              (∏ i, (cayley (ks i) : ℝ) / ((ks i).factorial : ℝ))) *
              p ^ (K - q) ≤
            ((6 * (n : ℝ) ^ (K + 1) *
              Real.exp (-((n : ℝ) - K) * Real.log (1 - (K : ℝ) / n))) *
              (C ^ q * P)) * (p ^ K * ((n : ℝ) / lo) ^ q) :=
        mul_le_mul hfallfac hshift (pow_nonneg hp0.le _) hright0
      exact mul_le_mul hmul hcomp
        (pow_nonneg (sub_nonneg.mpr hp1) _)
        (mul_nonneg hright0 (by positivity))
    calc
      tupleMoment n M q ks ≤
          8 * (N : ℝ) *
            ((falling n K : ℝ) *
              (∏ i, (cayley (ks i) : ℝ) / ((ks i).factorial : ℝ)) *
              p ^ (K - q) *
              (1 - p) ^ (capacity n - (n - K).choose 2 - (K - q))) := by
        simpa [K, N, p] using! hcond
      _ ≤ 8 * (N : ℝ) *
          ((6 * (n : ℝ) ^ (K + 1) *
              Real.exp (-((n : ℝ) - K) * Real.log (1 - (K : ℝ) / n))) *
              (C ^ q * (∏ i, (ks i : ℝ) ^ (-5 / 2 : ℝ))) *
            (p ^ K * ((n : ℝ) / lo) ^ q) *
            Real.exp (-p *
              (capacity n - (n - K).choose 2 - (K - q) : ℕ))) := by
        exact mul_le_mul_of_nonneg_left hstage (by positivity)
      _ ≤ D * (n : ℝ) ^ (q + 3) *
          (∏ i, (ks i : ℝ) ^ (-5 / 2 : ℝ)) *
          Real.exp ((n : ℝ) * independentEntropy lam ((K : ℝ) / n)) := by
        have hN : (N : ℝ) ≤ (n : ℝ) ^ 2 / 2 := by
          rw [show (N : ℝ) = (n : ℝ) * (n - 1) / 2 by
            dsimp [N]; exact capacity_cast]
          nlinarith
        rw [show (n : ℝ) ^ (K + 1) = n * (n : ℝ) ^ K by
          rw [pow_succ]; ring]
        have hexpBound :
            Real.exp (-((n : ℝ) - K) * Real.log (1 - (K : ℝ) / n)) *
              Real.exp (-p *
                (capacity n - (n - K).choose 2 - (K - q) : ℕ)) *
              (lam ^ K * Real.exp 2) ≤
            Real.exp (2 + 2 * hi) *
              Real.exp ((n : ℝ) * independentEntropy lam ((K : ℝ) / n)) := by
          rw [show lam ^ K = Real.exp ((K : ℝ) * Real.log lam) by
            calc
              lam ^ K = (Real.exp (Real.log lam)) ^ K := by rw [Real.exp_log hlam0]
              _ = Real.exp ((K : ℝ) * Real.log lam) := (Real.exp_nat_mul _ _).symm]
          rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add,
            ← Real.exp_add]
          apply Real.exp_le_exp.mpr
          rw [← hentropy]
          rw [hpdeg]
          nlinarith
        dsimp [D]
        calc
          8 * (N : ℝ) *
              ((6 * ((n : ℝ) * (n : ℝ) ^ K) *
                  Real.exp (-((n : ℝ) - K) * Real.log (1 - (K : ℝ) / n))) *
                (C ^ q * (∏ i, (ks i : ℝ) ^ (-5 / 2 : ℝ))) *
                (p ^ K * ((n : ℝ) / lo) ^ q) *
                Real.exp (-p *
                  (capacity n - (n - K).choose 2 - (K - q) : ℕ))) ≤
            24 * (n : ℝ) ^ 2 *
              ((n : ℝ) * C ^ q * P *
                ((n : ℝ) / lo) ^ q) *
              ((n : ℝ) ^ K * p ^ K) *
              (Real.exp (-((n : ℝ) - K) * Real.log (1 - (K : ℝ) / n)) *
                Real.exp (-p *
                  (capacity n - (n - K).choose 2 - (K - q) : ℕ))) := by
              have hN0 : 0 ≤ (N : ℝ) := by positivity
              have hrest0 : 0 ≤ (n : ℝ) * C ^ q * P * ((n : ℝ) / lo) ^ q *
                  ((n : ℝ) ^ K * p ^ K) *
                  (Real.exp (-((n : ℝ) - K) * Real.log (1 - (K : ℝ) / n)) *
                    Real.exp (-p *
                      (capacity n - (n - K).choose 2 - (K - q) : ℕ))) := by
                positivity
              rw [show 8 * (N : ℝ) *
                    ((6 * ((n : ℝ) * (n : ℝ) ^ K) *
                        Real.exp (-((n : ℝ) - K) * Real.log (1 - (K : ℝ) / n))) *
                      (C ^ q * P) * (p ^ K * ((n : ℝ) / lo) ^ q) *
                      Real.exp (-p *
                        (capacity n - (n - K).choose 2 - (K - q) : ℕ))) =
                  (48 * (N : ℝ)) *
                    ((n : ℝ) * C ^ q * P * ((n : ℝ) / lo) ^ q *
                      ((n : ℝ) ^ K * p ^ K) *
                      (Real.exp (-((n : ℝ) - K) * Real.log (1 - (K : ℝ) / n)) *
                        Real.exp (-p *
                          (capacity n - (n - K).choose 2 - (K - q) : ℕ)))) by ring,
                show 24 * (n : ℝ) ^ 2 *
                    ((n : ℝ) * C ^ q * P * ((n : ℝ) / lo) ^ q) *
                    ((n : ℝ) ^ K * p ^ K) *
                    (Real.exp (-((n : ℝ) - K) * Real.log (1 - (K : ℝ) / n)) *
                      Real.exp (-p *
                        (capacity n - (n - K).choose 2 - (K - q) : ℕ))) =
                  (24 * (n : ℝ) ^ 2) *
                    ((n : ℝ) * C ^ q * P * ((n : ℝ) / lo) ^ q *
                      ((n : ℝ) ^ K * p ^ K) *
                      (Real.exp (-((n : ℝ) - K) * Real.log (1 - (K : ℝ) / n)) *
                        Real.exp (-p *
                          (capacity n - (n - K).choose 2 - (K - q) : ℕ)))) by ring]
              exact mul_le_mul_of_nonneg_right (by nlinarith) hrest0
          _ ≤ 24 * (n : ℝ) ^ 2 *
              ((n : ℝ) * C ^ q * P *
                ((n : ℝ) / lo) ^ q) *
              (lam ^ K * Real.exp 2) *
              (Real.exp (-((n : ℝ) - K) * Real.log (1 - (K : ℝ) / n)) *
                Real.exp (-p *
                  (capacity n - (n - K).choose 2 - (K - q) : ℕ))) := by
              rw [show 24 * (n : ℝ) ^ 2 *
                    ((n : ℝ) * C ^ q * P * ((n : ℝ) / lo) ^ q) *
                    ((n : ℝ) ^ K * p ^ K) *
                    (Real.exp (-((n : ℝ) - K) * Real.log (1 - (K : ℝ) / n)) *
                      Real.exp (-p *
                        (capacity n - (n - K).choose 2 - (K - q) : ℕ))) =
                  (24 * (n : ℝ) ^ 2 *
                    ((n : ℝ) * C ^ q * P * ((n : ℝ) / lo) ^ q)) *
                    ((n : ℝ) ^ K * p ^ K) *
                    (Real.exp (-((n : ℝ) - K) * Real.log (1 - (K : ℝ) / n)) *
                      Real.exp (-p *
                        (capacity n - (n - K).choose 2 - (K - q) : ℕ))) by ring,
                show 24 * (n : ℝ) ^ 2 *
                    ((n : ℝ) * C ^ q * P * ((n : ℝ) / lo) ^ q) *
                    (lam ^ K * Real.exp 2) *
                    (Real.exp (-((n : ℝ) - K) * Real.log (1 - (K : ℝ) / n)) *
                      Real.exp (-p *
                        (capacity n - (n - K).choose 2 - (K - q) : ℕ))) =
                  (24 * (n : ℝ) ^ 2 *
                    ((n : ℝ) * C ^ q * P * ((n : ℝ) / lo) ^ q)) *
                    (lam ^ K * Real.exp 2) *
                    (Real.exp (-((n : ℝ) - K) * Real.log (1 - (K : ℝ) / n)) *
                      Real.exp (-p *
                        (capacity n - (n - K).choose 2 - (K - q) : ℕ))) by ring]
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hnpow (by positivity)) (by positivity)
          _ ≤ 24 * (n : ℝ) ^ 2 *
              ((n : ℝ) * C ^ q * P *
                ((n : ℝ) / lo) ^ q) *
              (Real.exp (2 + 2 * hi) *
                Real.exp ((n : ℝ) * independentEntropy lam ((K : ℝ) / n))) := by
              rw [show 24 * (n : ℝ) ^ 2 *
                    ((n : ℝ) * C ^ q * P * ((n : ℝ) / lo) ^ q) *
                    (lam ^ K * Real.exp 2) *
                    (Real.exp (-((n : ℝ) - K) * Real.log (1 - (K : ℝ) / n)) *
                      Real.exp (-p *
                        (capacity n - (n - K).choose 2 - (K - q) : ℕ))) =
                  (24 * (n : ℝ) ^ 2 *
                    ((n : ℝ) * C ^ q * P * ((n : ℝ) / lo) ^ q)) *
                    (Real.exp (-((n : ℝ) - K) * Real.log (1 - (K : ℝ) / n)) *
                      Real.exp (-p *
                        (capacity n - (n - K).choose 2 - (K - q) : ℕ)) *
                      (lam ^ K * Real.exp 2)) by ring,
                show 24 * (n : ℝ) ^ 2 *
                    ((n : ℝ) * C ^ q * P * ((n : ℝ) / lo) ^ q) *
                    (Real.exp (2 + 2 * hi) *
                      Real.exp ((n : ℝ) * independentEntropy lam ((K : ℝ) / n))) =
                  (24 * (n : ℝ) ^ 2 *
                    ((n : ℝ) * C ^ q * P * ((n : ℝ) / lo) ^ q)) *
                    (Real.exp (2 + 2 * hi) *
                      Real.exp ((n : ℝ) * independentEntropy lam ((K : ℝ) / n))) by ring]
              exact mul_le_mul_of_nonneg_left hexpBound (by positivity)
          _ = 24 * C ^ q * Real.exp (2 + 2 * hi) / lo ^ q *
              (n : ℝ) ^ (q + 3) * P *
              Real.exp ((n : ℝ) * independentEntropy lam ((K : ℝ) / n)) := by
              have hloq : lo ^ q ≠ 0 := pow_ne_zero _ (ne_of_gt hlo0)
              have hquot : ((n : ℝ) / lo) ^ q = (n : ℝ) ^ q / lo ^ q :=
                div_pow _ _ _
              rw [hquot, pow_add]
              field_simp [hloq]
  · have hbad : ¬ ((∀ i, 0 < ks i) ∧ (∑ i, ks i) ≤ n ∧
        (∑ i, ks i) ≤ M + q) := by
      intro hgood
      exact hKn (by simpa [K] using! hgood.2.1)
    rw [tupleMoment_eq_zero_of_guard_failure hF n M q ks hM hbad]
    have hD0 : 0 < D := by dsimp [D, C]; positivity
    have hprod0' : 0 ≤ ∏ i, (ks i : ℝ) ^ (-5 / 2 : ℝ) := by
      apply Finset.prod_nonneg
      intro i hi
      exact (Real.rpow_pos_of_pos (Nat.cast_pos.mpr (hpos i)) _).le
    exact mul_nonneg (mul_nonneg (mul_nonneg hD0.le (pow_nonneg hnr.le _))
      hprod0') (Real.exp_pos _).le

theorem independentEntropy_one_upper {lam : ℝ} (hlam : 0 < lam) :
    independentEntropy lam 1 ≤ -(1 : ℝ) / 4 := by
  have hloghalf := Real.log_le_sub_one_of_pos (show 0 < lam / 2 by positivity)
  have hrate2 := W04_TUPLES_RateEntropy.rate_quadratic_lower
    (x := (2 : ℝ)) (by norm_num) (by norm_num)
  have hlogtwo : Real.log 2 ≤ (3 : ℝ) / 4 := by
    norm_num [rate] at hrate2
    have hs : Real.log 2 + (1 : ℝ) / 4 ≤ 1 := by
      simpa [add_comm] using! (le_sub_iff_add_le.mp hrate2)
    rw [show (3 : ℝ) / 4 = 1 - 1 / 4 by norm_num]
    exact (le_sub_iff_add_le).2 hs
  have hlog : Real.log lam = Real.log (lam / 2) + Real.log 2 := by
    rw [← Real.log_mul (show lam / 2 ≠ 0 by positivity) (by norm_num : (2 : ℝ) ≠ 0)]
    congr 1
    field_simp
  simp only [independentEntropy, sub_self, zero_mul, Real.log_zero,
    one_mul, one_pow]
  rw [hlog]
  linarith

end

end Erdos745.WrapUp.Proofs.Internal.W04_TUPLES_IndependentEnvelope
