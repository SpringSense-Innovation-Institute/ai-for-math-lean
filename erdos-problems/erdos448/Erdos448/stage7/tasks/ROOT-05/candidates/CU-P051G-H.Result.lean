module

import all Mathlib.Basic.Real.Basic
public import Erdos448.stage7.tasks.«ROOT-05».Recovered

public section

set_option backward.isDefEq.respectTransparency false

namespace Erdos448.Stage7.ROOT05.CUP051GH

open Finset Set
open scoped BigOperators NNReal

noncomputable section

open Erdos448.Stage4
open Erdos448.Stage4.Contracts
open Erdos448.Stage6.TaskContracts

lemma weightTypeSpec_weaken
    {w : ArithmeticWeight} {c C Lambda c' C' Lambda' : ℝ}
    (h : WeightTypeSpec w c C Lambda)
    (hc' : 0 < c') (hcc : c' ≤ c)
    (hC' : 0 < C') (hCC : C ≤ C')
    (hLambda' : 0 < Lambda') (hLL : Lambda ≤ Lambda') :
    WeightTypeSpec w c' C' Lambda' := by
  refine
    { c_pos := hc'
      C_pos := hC'
      Lambda_pos := hLambda'
      nonnegative_multiplicative := h.nonnegative_multiplicative
      normalized := h.normalized
      prime_power := ?_
      prime_power_bounds := ?_ }
  · intro p hp i hi
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
    have hr : (p : ℝ).rpow (-c) ≤ (p : ℝ).rpow (-c') :=
      Real.rpow_le_rpow_of_exponent_le hp1 (neg_le_neg hcc)
    calc
      |w (p ^ i) - 1 / (i + 1 : ℕ)| ≤ C * (p : ℝ).rpow (-c) :=
        h.prime_power p hp i hi
      _ ≤ C' * (p : ℝ).rpow (-c') := by
        exact mul_le_mul hCC hr (Real.rpow_nonneg (Nat.cast_nonneg p) _)
          (h.C_pos.le.trans hCC)
  · intro p hp i hi
    exact ⟨(h.prime_power_bounds p hp i hi).1,
      (h.prime_power_bounds p hp i hi).2.trans hLL⟩

@[expose] def commonWeights : CommonWeightWitnesses := by
  let chain := Erdos448.Stage7.ROOT05.Recovered.weightChain
  let cStar : ℝ := min 1 (min chain.c1 (min chain.c2 (min chain.c3 chain.c4)))
  let CStar : ℝ := max 1 (max chain.C1 (max chain.C2 (max chain.C3 chain.C4)))
  let LambdaBase : ℝ :=
    max 1 (max chain.Lambda1 (max chain.Lambda2 (max chain.Lambda3 chain.Lambda4)))
  let LambdaStar : ℝ := max LambdaBase (1 + CStar * (2 : ℝ).rpow (-cStar))
  have hcStar : 0 < cStar := by
    dsimp [cStar, chain]
    exact lt_min (by norm_num)
      (lt_min Erdos448.Stage7.ROOT05.Recovered.weightChain.c1_pos
        (lt_min Erdos448.Stage7.ROOT05.Recovered.weightChain.c2_pos
          (lt_min Erdos448.Stage7.ROOT05.Recovered.weightChain.c3_pos
            Erdos448.Stage7.ROOT05.Recovered.weightChain.c4_pos)))
  have hCStar : 0 < CStar := by
    dsimp [CStar]
    exact lt_max_of_lt_left (by norm_num)
  have hLambdaBase : 0 < LambdaBase := by
    dsimp [LambdaBase]
    exact lt_max_of_lt_left (by norm_num)
  have hLambdaStar : 0 < LambdaStar :=
    hLambdaBase.trans_le (by dsimp [LambdaStar]; exact le_max_left _ _)
  have hbase : WeightTypeSpec a0Weight 1 1 1 :=
    Erdos448.Stage7.ROOT05.Recovered.p051A.1
  refine
    { cStar := cStar
      CStar := CStar
      LambdaStar := LambdaStar
      cStar_pos := hcStar
      CStar_pos := hCStar
      LambdaStar_pos := hLambdaStar
      LambdaStar_lower := by
        dsimp [LambdaStar]
        exact le_max_right _ _
      weight_type := ?_
      modifier := chain.modifier
      w1_dom_a0 := chain.w1_dom_a0
      w2_dom_w1 := chain.w2_dom_w1
      w3_dom_w1 := chain.w3_dom_w1
      w3_dom_w2 := chain.w3_dom_w2
      w4_dom_w3 := chain.w4_dom_w3 }
  intro q member
  have hc1 : cStar ≤ 1 := by simp [cStar]
  have hcC1 : (1 : ℝ) ≤ CStar := by simp [CStar]
  have hLB1 : (1 : ℝ) ≤ LambdaBase := by
    dsimp [LambdaBase]
    exact le_max_left _ _
  have hLBc1 : chain.Lambda1 ≤ LambdaBase := by
    dsimp [LambdaBase]
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hLBc2 : chain.Lambda2 ≤ LambdaBase := by
    dsimp [LambdaBase]
    exact le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)
  have hLBc3 : chain.Lambda3 ≤ LambdaBase := by
    dsimp [LambdaBase]
    exact le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _))
      (le_max_right _ _)) (le_max_right _ _)
  have hLBc4 : chain.Lambda4 ≤ LambdaBase := by
    dsimp [LambdaBase]
    exact le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _))
      (le_max_right _ _)) (le_max_right _ _)
  have hLBStar : LambdaBase ≤ LambdaStar := by
    dsimp [LambdaStar]
    exact le_max_left _ _
  have hL1 : (1 : ℝ) ≤ LambdaStar := by
    exact hLB1.trans hLBStar
  cases member with
  | a0 =>
      simpa [selectedWeight] using
        weightTypeSpec_weaken hbase hcStar hc1 hCStar hcC1 hLambdaStar hL1
  | w1 =>
      apply weightTypeSpec_weaken chain.w1_type hcStar
      · simp [cStar]
      · exact hCStar
      · simp [CStar]
      · exact hLambdaStar
      · exact hLBc1.trans hLBStar
  | w2 =>
      apply weightTypeSpec_weaken (chain.w2_type q) hcStar
      · simp [cStar]
      · exact hCStar
      · simp [CStar]
      · exact hLambdaStar
      · exact hLBc2.trans hLBStar
  | w3 =>
      apply weightTypeSpec_weaken (chain.w3_type q) hcStar
      · simp [cStar]
      · exact hCStar
      · simp [CStar]
      · exact hLambdaStar
      · exact hLBc3.trans hLBStar
  | w4 =>
      apply weightTypeSpec_weaken (chain.w4_type q) hcStar
      · simp [cStar]
      · exact hCStar
      · simp [CStar]
      · exact hLambdaStar
      · exact hLBc4.trans hLBStar

lemma euler_term_nonnegative
    {w b : ArithmeticWeight} {c C Lambda : ℝ}
    (hw : WeightTypeSpec w c C Lambda) (hb : ModifierSpec b)
    {p : ℕ} (hp : p.Prime) (j : ℕ) :
    0 ≤ w (p ^ j) * b (p ^ j) / (p : ℝ) ^ j := by
  cases j with
  | zero => simp [hw.normalized, hb.normalized]
  | succ j =>
      exact div_nonneg
        (mul_nonneg (hw.prime_power_bounds p hp (j + 1) (by omega)).1
          (hb.prime_power_bounds p hp (j + 1)).1)
        (pow_nonneg (Nat.cast_nonneg p) _)

lemma euler_summable
    {w b : ArithmeticWeight} {c C Lambda : ℝ}
    (hw : WeightTypeSpec w c C Lambda) (hb : ModifierSpec b)
    {p : ℕ} (hp : p.Prime) :
    Summable fun j : ℕ => w (p ^ j) * b (p ^ j) / (p : ℝ) ^ j := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hr0 : 0 ≤ 1 / (p : ℝ) := by positivity
  have hr1 : 1 / (p : ℝ) < 1 := by
    rw [div_lt_one hp0]
    exact_mod_cast hp.one_lt
  refine .of_norm_bounded
    ((summable_geometric_of_lt_one hr0 hr1).mul_left (max 1 Lambda)) ?_
  intro j
  rw [Real.norm_eq_abs, abs_of_nonneg (euler_term_nonnegative hw hb hp j)]
  cases j with
  | zero => simp [hw.normalized, hb.normalized, le_max_left]
  | succ j =>
      have hwB := (hw.prime_power_bounds p hp (j + 1) (by omega)).2
      have hbB := (hb.prime_power_bounds p hp (j + 1)).2
      have hb0 := (hb.prime_power_bounds p hp (j + 1)).1
      calc
        w (p ^ (j + 1)) * b (p ^ (j + 1)) / (p : ℝ) ^ (j + 1)
            ≤ Lambda * 1 / (p : ℝ) ^ (j + 1) := by
              gcongr
              exact hw.Lambda_pos.le
        _ = Lambda * (1 / (p : ℝ)) ^ (j + 1) := by
          simp [div_eq_mul_inv, inv_pow]
        _ ≤ max 1 Lambda * (1 / (p : ℝ)) ^ (j + 1) := by
          gcongr
          exact le_max_right _ _

set_option maxHeartbeats 4000000 in
lemma geometric_tail_bound
    {Lambda : ℝ} (hLambda : 0 < Lambda) {p : ℕ} (hp : p.Prime) :
    (∑' j : ℕ, Lambda * (1 / (p : ℝ)) ^ (j + 2)) ≤
      2 * Lambda * (p : ℝ).rpow (-2) := by
  have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < p := by linarith
  have hr0 : 0 ≤ 1 / (p : ℝ) := by positivity
  have hr1 : 1 / (p : ℝ) < 1 := by
    rw [div_lt_one hp0]
    linarith
  have hvalue :
      (∑' j : ℕ, Lambda * (1 / (p : ℝ)) ^ (j + 2)) =
        Lambda / ((p : ℝ) * ((p : ℝ) - 1)) := by
    calc
      (∑' j : ℕ, Lambda * (1 / (p : ℝ)) ^ (j + 2)) =
          (∑' j : ℕ, (1 / (p : ℝ)) ^ j *
            (Lambda * (1 / (p : ℝ)) ^ 2)) := by
              apply tsum_congr
              intro j
              rw [pow_add]
              ring
      _ = (∑' j : ℕ, (1 / (p : ℝ)) ^ j) *
          (Lambda * (1 / (p : ℝ)) ^ 2) := _root_.tsum_mul_right
      _ = (1 - 1 / (p : ℝ))⁻¹ *
          (Lambda * (1 / (p : ℝ)) ^ 2) := by
            rw [tsum_geometric_of_lt_one hr0 hr1]
      _ = Lambda / ((p : ℝ) * ((p : ℝ) - 1)) := by
        have hpne : (p : ℝ) ≠ 0 := ne_of_gt hp0
        have hpmne : (p : ℝ) - 1 ≠ 0 := by linarith
        field_simp [hpne, hpmne]
  rw [hvalue]
  have hrpowZ : (p : ℝ).rpow (-2 : ℝ) = (p : ℝ) ^ (-2 : ℤ) :=
    Real.rpow_neg_ofNat (p : ℝ) 2
  rw [hrpowZ, zpow_neg, zpow_ofNat]
  have hpm1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hpne : (p : ℝ) ≠ 0 := ne_of_gt hp0
  field_simp [hpne, hpm1.ne']
  nlinarith

set_option maxHeartbeats 1000000 in
lemma euler_tail_bound
    {w b : ArithmeticWeight} {c C Lambda : ℝ}
    (hw : WeightTypeSpec w c C Lambda) (hb : ModifierSpec b)
    {p : ℕ} (hp : p.Prime) :
    |localEulerFactor w b p - (1 + w p * b p / p)| ≤
      2 * Lambda * (p : ℝ).rpow (-2) := by
  have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < p := by linarith
  have hr0 : 0 ≤ 1 / (p : ℝ) := by positivity
  have hr1 : 1 / (p : ℝ) < 1 := by
    rw [div_lt_one hp0]
    linarith
  let f : ℕ → ℝ := fun j => w (p ^ j) * b (p ^ j) / (p : ℝ) ^ j
  have hf : Summable f := euler_summable hw hb hp
  have hf0 : f 0 = 1 := by simp [f, hw.normalized, hb.normalized]
  have hf1 : f 1 = w p * b p / p := by simp [f]
  have hinj1 : Function.Injective (fun j : ℕ => j + 1) := by
    intro a b h
    exact Nat.add_right_cancel h
  have hinj2 : Function.Injective (fun j : ℕ => j + 2) := by
    intro a b h
    exact Nat.add_right_cancel h
  have hfshift : Summable fun j : ℕ => f (j + 1) := hf.comp_injective hinj1
  have hfshift2 : Summable fun j : ℕ => f (j + 2) := hf.comp_injective hinj2
  have hsplit : localEulerFactor w b p =
      1 + w p * b p / p + ∑' j : ℕ, f (j + 2) := by
    rw [localEulerFactor, show (fun j => w (p ^ j) * b (p ^ j) / (p : ℝ) ^ j) = f from rfl,
      hf.tsum_eq_zero_add, hfshift.tsum_eq_zero_add, hf0, hf1]
    ring
  have htail0 : ∀ j : ℕ, 0 ≤ f (j + 2) := by
    intro j
    exact euler_term_nonnegative hw hb hp (j + 2)
  have htail : ∀ j : ℕ,
      f (j + 2) ≤ Lambda * (1 / (p : ℝ)) ^ (j + 2) := by
    intro j
    have hwB := (hw.prime_power_bounds p hp (j + 2) (by omega)).2
    have hbB := (hb.prime_power_bounds p hp (j + 2)).2
    have hb0 := (hb.prime_power_bounds p hp (j + 2)).1
    calc
      f (j + 2) ≤ Lambda * 1 / (p : ℝ) ^ (j + 2) := by
        dsimp [f]
        gcongr
        exact hw.Lambda_pos.le
      _ = Lambda * (1 / (p : ℝ)) ^ (j + 2) := by
        simp [div_eq_mul_inv, inv_pow]
  have hgeom : Summable fun j : ℕ => Lambda * (1 / (p : ℝ)) ^ (j + 2) := by
    have h := (summable_geometric_of_lt_one hr0 hr1).mul_left
      (Lambda * (1 / (p : ℝ)) ^ 2)
    simpa [pow_add, mul_assoc, mul_left_comm, mul_comm] using h
  have htailSum :
      (∑' j : ℕ, f (j + 2)) ≤
        ∑' j : ℕ, Lambda * (1 / (p : ℝ)) ^ (j + 2) :=
    hfshift2.tsum_le_tsum htail hgeom
  rw [hsplit]
  have htailNonneg : 0 ≤ ∑' j : ℕ, f (j + 2) := tsum_nonneg htail0
  rw [show 1 + w p * b p / (p : ℝ) + (∑' j : ℕ, f (j + 2)) -
      (1 + w p * b p / (p : ℝ)) = ∑' j : ℕ, f (j + 2) by ring,
    abs_of_nonneg htailNonneg]
  exact htailSum.trans (geometric_tail_bound hw.Lambda_pos hp)

lemma tail_to_eta
    (W : CommonWeightWitnesses) {p : ℕ} (hp : p.Prime) :
    2 * W.LambdaStar * (p : ℝ).rpow (-2) ≤
      2 * W.LambdaStar * (p : ℝ).rpow (-1 - min W.cStar 1) := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  have heta : min W.cStar 1 ≤ 1 := min_le_right _ _
  have hexp : (-2 : ℝ) ≤ -1 - min W.cStar 1 := by linarith
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hp1 hexp)
    (mul_nonneg (by norm_num) W.LambdaStar_pos.le)

lemma first_term_bound
    (W : CommonWeightWitnesses) (q : WeightParameters) (member : WeightMember)
    {b : ArithmeticWeight} (hb : ModifierSpec b) {p : ℕ} (hp : p.Prime) :
    |selectedWeight q member p * b p / p - b p / (2 * p)| ≤
      W.CStar * (p : ℝ).rpow (-1 - min W.cStar 1) := by
  have hw := W.weight_type q member
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  have hb0 : 0 ≤ b p := by simpa using (hb.prime_power_bounds p hp 1).1
  have hb1 : b p ≤ 1 := by simpa using (hb.prime_power_bounds p hp 1).2
  have hwerr : |selectedWeight q member p - 1 / 2| ≤
      W.CStar * (p : ℝ).rpow (-W.cStar) := by
    simpa using hw.prime_power p hp 1 (by omega)
  have heta : min W.cStar 1 ≤ W.cStar := min_le_left _ _
  have hpow : (p : ℝ).rpow (-W.cStar) * (p : ℝ)⁻¹ ≤
      (p : ℝ).rpow (-1 - min W.cStar 1) := by
    calc
      (p : ℝ).rpow (-W.cStar) * (p : ℝ)⁻¹ =
          (p : ℝ).rpow (-W.cStar) * (p : ℝ).rpow (-1 : ℝ) := by
            congr 1
            exact (Real.rpow_neg_one (p : ℝ)).symm
      _ = (p : ℝ).rpow (-W.cStar + (-1 : ℝ)) := by
            exact (Real.rpow_add hp0 (-W.cStar) (-1 : ℝ)).symm
      _ ≤ (p : ℝ).rpow (-1 - min W.cStar 1) :=
        Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
  calc
    |selectedWeight q member p * b p / p - b p / (2 * p)| =
        |selectedWeight q member p - 1 / 2| * b p * (p : ℝ)⁻¹ := by
      rw [show selectedWeight q member p * b p / (p : ℝ) - b p / (2 * p) =
          (selectedWeight q member p - 1 / 2) * b p * (p : ℝ)⁻¹ by ring]
      rw [abs_mul, abs_mul, abs_of_nonneg hb0, abs_inv, abs_of_pos hp0]
    _ ≤ (W.CStar * (p : ℝ).rpow (-W.cStar)) * 1 * (p : ℝ)⁻¹ := by
      apply mul_le_mul_of_nonneg_right
      · exact mul_le_mul hwerr hb1 hb0
          (mul_nonneg W.CStar_pos.le (Real.rpow_nonneg (by positivity) _))
      · exact inv_nonneg.mpr hp0.le
    _ ≤ W.CStar * (p : ℝ).rpow (-1 - min W.cStar 1) := by
      calc
        (W.CStar * (p : ℝ).rpow (-W.cStar)) * 1 * (p : ℝ)⁻¹ =
            W.CStar * ((p : ℝ).rpow (-W.cStar) * (p : ℝ)⁻¹) := by ring
        _ ≤ W.CStar * (p : ℝ).rpow (-1 - min W.cStar 1) := by
          gcongr
          exact W.CStar_pos.le

theorem p051H : P051HStatement := by
  intro W q member b hb p hp
  let w := selectedWeight q member
  have hw : WeightTypeSpec w W.cStar W.CStar W.LambdaStar := W.weight_type q member
  have hsummable := euler_summable hw hb hp
  have htail := euler_tail_bound hw hb hp
  have heta := tail_to_eta W hp
  have hfirst := first_term_bound W q member hb hp
  have hpositive : 0 < localEulerFactor w b p := by
    let f : ℕ → ℝ := fun j => w (p ^ j) * b (p ^ j) / (p : ℝ) ^ j
    have hf0 : f 0 = 1 := by simp [f, hw.normalized, hb.normalized]
    have hnonneg : ∀ j : ℕ, 0 ≤ f j := euler_term_nonnegative hw hb hp
    have hsumNonneg : 0 ≤ ∑' j : ℕ, f (j + 1) := tsum_nonneg fun j => hnonneg (j + 1)
    have hf : Summable f := hsummable
    have hsplit0 : localEulerFactor w b p = f 0 + ∑' j : ℕ, f (j + 1) := by
      exact hf.tsum_eq_zero_add
    rw [hsplit0, hf0]
    linarith
  refine
    { domain :=
        { prime := hp
          modifier := hb
          summable := hsummable
          positive := hpositive }
      tail_bound := htail
      tail_to_eta := heta
      replaced_main_term := ?_ }
  calc
    |localEulerFactor w b p - (1 + b p / (2 * p))| ≤
        |localEulerFactor w b p - (1 + w p * b p / p)| +
          |w p * b p / p - b p / (2 * p)| := by
            have h := abs_add_le
              (localEulerFactor w b p - (1 + w p * b p / p))
              (w p * b p / p - b p / (2 * p))
            convert h using 1 <;> ring
    _ ≤ 2 * W.LambdaStar * (p : ℝ).rpow (-1 - min W.cStar 1) +
          W.CStar * (p : ℝ).rpow (-1 - min W.cStar 1) :=
      add_le_add (htail.trans heta) hfirst
    _ = (W.CStar + 2 * W.LambdaStar) *
          (p : ℝ).rpow (-1 - min W.cStar 1) := by ring

end

end Erdos448.Stage7.ROOT05.CUP051GH
