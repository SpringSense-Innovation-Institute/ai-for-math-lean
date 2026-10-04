module

import all Mathlib.Basic.Real.Basic
public import Erdos448.dependencies.«DP-MERTENS».stage6.FrozenTaskContracts

public section

set_option backward.isDefEq.respectTransparency false

namespace Erdos448.DPMertens.Tasks.MSCAssembly

open Filter Finset Set
open scoped BigOperators Topology

open Erdos448.DPMertens
open Erdos448.DPMertens.Lowering

noncomputable section

@[expose] def PublicTarget : Type :=
  ∀ (corr : CorrectionOutput) (C_A : ℝ),
    PrimeZetaOutput corr.H → PrimeTailOutputOf C_A → ExpIntegralOutput →
      SumAssemblyOutput corr.H

@[expose] def finitePrimeZeta (G : ℕ) (rho : ℝ) : ℝ :=
  ∑ p ∈ (Finset.range (G + 1)).filter Nat.Prime,
    Real.rpow p (-(1 + rho))

lemma primeZetaSummable {rho : ℝ} (hrho : 0 < rho) :
    Summable (fun p : ℕ =>
      if p.Prime then Real.rpow p (-(1 + rho)) else 0) := by
  apply Summable.of_nonneg_of_le
      (f := fun p : ℕ => Real.rpow p (-(1 + rho)))
  · intro p
    split_ifs
    · exact Real.rpow_nonneg (Nat.cast_nonneg p) _
    · exact le_rfl
  · intro p
    split_ifs
    · exact le_rfl
    · exact Real.rpow_nonneg (Nat.cast_nonneg p) _
  · apply Real.summable_nat_rpow.mpr
    linarith

lemma primeZeta_split (G : ℕ) {rho : ℝ} (hrho : 0 < rho) :
    primeZetaOnePlus rho = finitePrimeZeta G rho +
      ∑' p : ℕ, if p.Prime ∧ G < p then
        Real.rpow p (-(1 + rho)) else 0 := by
  let a : ℕ → ℝ := fun p =>
    if p.Prime then Real.rpow p (-(1 + rho)) else 0
  let s : Finset ℕ := (Finset.range (G + 1)).filter Nat.Prime
  have ha : Summable a := primeZetaSummable hrho
  have split := ha.sum_add_tsum_compl (s := s)
  change (∑' p : ℕ, a p) = _
  rw [← split]
  unfold finitePrimeZeta a s
  congr 1
  · apply Finset.sum_congr rfl
    intro p hp
    simp only [Finset.mem_filter] at hp
    simp [hp.2]
  · change (∑' p : (Set.compl (↑s : Set ℕ)), a p) = _
    rw [_root_.tsum_subtype]
    apply tsum_congr
    intro p
    by_cases hp : p.Prime
    · by_cases hpG : p ≤ G
      · have hmem : p ∈ (Finset.range (G + 1)).filter Nat.Prime := by
          simp [hp, hpG]
        have hs_mem : p ∈ s := by
          change p ∈ (Finset.range (G + 1)).filter Nat.Prime
          exact hmem
        have hc : p ∉ (↑s : Set ℕ)ᶜ := by
          intro hcp
          exact hcp hs_mem
        have hc' : p ∉ ((↑s : Set ℕ).compl) := hc
        simp only [Set.indicator, hc', if_false]
        simp [a, hp, hpG]
      · have hnotmem : p ∉ (Finset.range (G + 1)).filter Nat.Prime := by
          simp [hp, hpG]
        have hGp : G < p := Nat.lt_of_not_ge hpG
        have hs_mem : p ∉ s := by
          intro hps
          apply hnotmem
          change p ∈ (Finset.range (G + 1)).filter Nat.Prime at hps
          exact hps
        have hc : p ∈ (↑s : Set ℕ)ᶜ := by
          exact fun hps => hs_mem hps
        have hc' : p ∈ ((↑s : Set ℕ).compl) := hc
        simp only [Set.indicator, hc', if_true]
        simp [a, hp, hGp]
    · have hnotmem : p ∉ (Finset.range (G + 1)).filter Nat.Prime := by
        simp [hp]
      simp [Set.indicator, a, hp]

lemma finitePrimeZeta_tendsto (G : ℕ) :
    Tendsto (finitePrimeZeta G) rhoDownZero
      (𝓝 (reciprocalPrimeSumNat G)) := by
  unfold finitePrimeZeta reciprocalPrimeSumNat
  apply tendsto_finset_sum
  intro p hp
  have hp_prime : p.Prime := (Finset.mem_filter.1 hp).2
  have hp_ne : (p : ℝ) ≠ 0 := by exact_mod_cast hp_prime.ne_zero
  have hcont : ContinuousAt (fun rho : ℝ =>
      Real.rpow p (-(1 + rho))) 0 := by
    simpa only [Function.comp_def, Real.rpow_eq_pow] using
      (Real.continuousAt_const_rpow hp_ne).comp (by fun_prop :
        ContinuousAt (fun rho : ℝ => -(1 + rho)) 0)
  have h := hcont.tendsto.mono_left
    (show rhoDownZero ≤ 𝓝 (0 : ℝ) from inf_le_left)
  simpa only [add_zero, Real.rpow_eq_pow, Real.rpow_neg_one] using h

@[expose] def integerDelta (H : ℝ) (G : ℕ) : ℝ :=
  reciprocalPrimeSumNat G - Real.log (Real.log G) -
    (Real.eulerMascheroniConstant - H)

lemma integer_delta_bound
    (corr : CorrectionOutput) (C_A : ℝ)
    (pz : PrimeZetaOutput corr.H) (pt : PrimeTailOutputOf C_A)
    (ei : ExpIntegralOutput) (G : ℕ) (hG : 2 ≤ G) :
    |integerDelta corr.H G| ≤ 2 * C_A / Real.log G := by
  letI : NeBot rhoDownZero := by
    unfold rhoDownZero
    infer_instance
  let residual : ℝ → ℝ := fun rho =>
    finitePrimeZeta G rho - Real.log (Real.log G) -
      (Real.eulerMascheroniConstant - corr.H) - pz.epsilon0 rho +
        ei.epsilonG G rho
  have residual_eq : ∀ rho : ℝ, 0 < rho →
      residual rho = -pt.mathcalE G rho := by
    intro rho hrho
    have hsplit := primeZeta_split G hrho
    have hz := pz.formula rho hrho
    have ht := pt.formula G hG rho hrho
    have hi := ei.formula G (by exact_mod_cast hG) rho hrho
    unfold residual
    rw [hsplit, ht, hi] at hz
    linarith
  have residual_tendsto : Tendsto residual rhoDownZero
      (𝓝 (integerDelta corr.H G)) := by
    have hfinite := finitePrimeZeta_tendsto G
    have he0 := pz.epsilon0_tendsto
    have heG := ei.epsilonG_tendsto G (by exact_mod_cast hG)
    have hcLog : Tendsto (fun _ : ℝ => Real.log (Real.log G)) rhoDownZero
        (𝓝 (Real.log (Real.log G))) := tendsto_const_nhds
    have hcB : Tendsto (fun _ : ℝ =>
        Real.eulerMascheroniConstant - corr.H) rhoDownZero
        (𝓝 (Real.eulerMascheroniConstant - corr.H)) := tendsto_const_nhds
    have h := (((hfinite.sub hcLog).sub hcB).sub he0).add heG
    simpa [residual, integerDelta] using h
  have residual_bound : ∀ᶠ rho in rhoDownZero,
      |residual rho| ≤ 2 * C_A / Real.log G := by
    filter_upwards [self_mem_nhdsWithin] with rho hrho
    rw [residual_eq rho hrho, abs_neg]
    exact pt.uniform_bound G hG rho hrho
  have hclosed : IsClosed (Set.Icc
      (-(2 * C_A / Real.log G)) (2 * C_A / Real.log G)) := isClosed_Icc
  have hmem := hclosed.mem_of_tendsto residual_tendsto
    (residual_bound.mono fun rho hr => (abs_le.mp hr))
  exact abs_le.mpr hmem

lemma integer_formula (H : ℝ) (G : ℕ) :
    reciprocalPrimeSumNat G = Real.log (Real.log G) +
      (Real.eulerMascheroniConstant - H) + integerDelta H G := by
  unfold integerDelta
  ring

lemma reciprocalPrimeSum_floor (x : ℝ) :
    reciprocalPrimeSum x = reciprocalPrimeSumNat (Nat.floor x) := by
  unfold reciprocalPrimeSum reciprocalPrimeSumNat primesLE
  rfl

@[expose] def realRemainder (H : ℝ) (Delta : ℕ → ℝ) (x : ℝ) : ℝ :=
  if 2 ≤ x then
    Delta (Nat.floor x) +
      Real.log (Real.log (Nat.floor x)) - Real.log (Real.log x)
  else 0

lemma floor_ge_two {x : ℝ} (hx : 4 ≤ x) : 2 ≤ Nat.floor x := by
  exact Nat.le_floor (by linarith : (2 : ℝ) ≤ x)

lemma floor_bounds {x : ℝ} (hx : 4 ≤ x) :
    x / 2 ≤ (Nat.floor x : ℝ) ∧ (Nat.floor x : ℝ) ≤ x := by
  constructor
  · have hfloor := Nat.lt_floor_add_one x
    linarith
  · exact Nat.floor_le (by linarith)

lemma loglog_floor_difference_bound {x : ℝ} (hx : 4 ≤ x) :
    |Real.log (Real.log (Nat.floor x)) - Real.log (Real.log x)| ≤
      2 / Real.log x := by
  have hf := floor_bounds hx
  have hfloor_two : (2 : ℝ) ≤ Nat.floor x := by
    exact_mod_cast floor_ge_two hx
  have hlog_floor_pos : 0 < Real.log (Nat.floor x) :=
    Real.log_pos (lt_of_lt_of_le (by norm_num) hfloor_two)
  have hlog_x_pos : 0 < Real.log x := Real.log_pos (by linarith)
  have hlog_floor_le : Real.log (Nat.floor x) ≤ Real.log x :=
    Real.strictMonoOn_log.monotoneOn
      (by exact lt_of_lt_of_le (by norm_num) hfloor_two)
      (show 0 < x by linarith) hf.2
  have hratio : x / (Nat.floor x : ℝ) ≤ 2 := by
    apply (div_le_iff₀ (lt_of_lt_of_le (by norm_num) hfloor_two)).2
    linarith
  have hlog_ratio_nonneg : 0 ≤ Real.log (x / (Nat.floor x : ℝ)) := by
    apply Real.log_nonneg
    apply (le_div_iff₀ (lt_of_lt_of_le (by norm_num) hfloor_two)).2
    simpa only [one_mul] using hf.2
  have hlog_ratio_le : Real.log (x / (Nat.floor x : ℝ)) ≤ Real.log 2 :=
    Real.strictMonoOn_log.monotoneOn
      (div_pos (by linarith) (lt_of_lt_of_le (by norm_num) hfloor_two))
      (by norm_num) hratio
  rw [abs_of_nonpos (sub_nonpos.mpr (Real.strictMonoOn_log.monotoneOn
    hlog_floor_pos hlog_x_pos hlog_floor_le))]
  rw [neg_sub]
  have hlog_sub : Real.log x - Real.log (Nat.floor x) =
      Real.log (x / (Nat.floor x : ℝ)) := by
    rw [Real.log_div (by positivity) (by positivity)]
  have hloglog_le :
      Real.log (Real.log x) - Real.log (Real.log (Nat.floor x)) ≤
        (Real.log x - Real.log (Nat.floor x)) / Real.log (Nat.floor x) := by
    rw [← Real.log_div hlog_x_pos.ne' hlog_floor_pos.ne']
    calc
      Real.log (Real.log x / Real.log (Nat.floor x))
          ≤ Real.log x / Real.log (Nat.floor x) - 1 :=
            Real.log_le_sub_one_of_pos (div_pos hlog_x_pos hlog_floor_pos)
      _ = (Real.log x - Real.log (Nat.floor x)) /
          Real.log (Nat.floor x) := by field_simp
  have hden : Real.log x ≤ 2 * Real.log (Nat.floor x) := by
    have hlog_two_floor : Real.log 2 ≤ Real.log (Nat.floor x) :=
      Real.strictMonoOn_log.monotoneOn (by norm_num)
        (lt_of_lt_of_le (by norm_num) hfloor_two) hfloor_two
    linarith [hlog_sub, hlog_ratio_le]
  calc
    Real.log (Real.log x) - Real.log (Real.log (Nat.floor x))
        ≤ (Real.log x - Real.log (Nat.floor x)) /
            Real.log (Nat.floor x) := hloglog_le
    _ ≤ Real.log 2 / Real.log (Nat.floor x) := by
      gcongr
      simpa only [hlog_sub] using hlog_ratio_le
    _ ≤ 1 / Real.log (Nat.floor x) := by
      gcongr
      nlinarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
    _ ≤ 2 / Real.log x := by
      apply (div_le_div_iff₀ hlog_floor_pos hlog_x_pos).2
      nlinarith

lemma real_formula
    (H : ℝ) (Delta : ℕ → ℝ)
    (hint : ∀ G : ℕ, 2 ≤ G → reciprocalPrimeSumNat G =
      Real.log (Real.log G) + (Real.eulerMascheroniConstant - H) + Delta G)
    (x : ℝ) (hx : 2 ≤ x) :
    reciprocalPrimeSum x = Real.log (Real.log x) +
      (Real.eulerMascheroniConstant - H) + realRemainder H Delta x := by
  rw [reciprocalPrimeSum_floor]
  unfold realRemainder
  rw [if_pos hx]
  have hfloor : 2 ≤ Nat.floor x := Nat.le_floor hx
  rw [hint _ hfloor]
  ring

lemma real_rate
    (corr : CorrectionOutput) (C_A : ℝ)
    (pz : PrimeZetaOutput corr.H) (pt : PrimeTailOutputOf C_A)
    (ei : ExpIntegralOutput) :
    ReciprocalLogRate (realRemainder corr.H (integerDelta corr.H))
      (4 * |C_A| + 4) 4 := by
  refine ⟨by positivity, by norm_num, ?_⟩
  intro x hx
  have hfloor := floor_ge_two hx
  have hdelta := integer_delta_bound corr C_A pz pt ei _ hfloor
  have hdiff := loglog_floor_difference_bound hx
  unfold realRemainder
  rw [if_pos (by linarith : 2 ≤ x)]
  rw [add_sub_assoc]
  calc
    |integerDelta corr.H (Nat.floor x) +
        (Real.log (Real.log (Nat.floor x)) - Real.log (Real.log x))|
        ≤ |integerDelta corr.H (Nat.floor x)| +
          |Real.log (Real.log (Nat.floor x)) - Real.log (Real.log x)| :=
            abs_add_le _ _
    _ ≤ (4 * |C_A| + 4) / Real.log x := by
      have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
      have hlogfloor : 0 < Real.log (Nat.floor x) :=
        Real.log_pos (by exact_mod_cast (show 1 < Nat.floor x by omega))
      have hlogs : Real.log x ≤ 2 * Real.log (Nat.floor x) := by
        have hf := floor_bounds hx
        have hfloor_pos : (0 : ℝ) < Nat.floor x := by
          exact_mod_cast (show 0 < Nat.floor x by omega)
        have hratio : x / (Nat.floor x : ℝ) ≤ 2 := by
          apply (div_le_iff₀ hfloor_pos).2
          linarith
        have hlogratio : Real.log (x / (Nat.floor x : ℝ)) ≤ Real.log 2 :=
          Real.strictMonoOn_log.monotoneOn
            (div_pos (by linarith) hfloor_pos)
            (by norm_num) hratio
        have hlogsplit : Real.log x = Real.log (Nat.floor x) +
            Real.log (x / (Nat.floor x : ℝ)) := by
          rw [Real.log_div (by positivity) (by positivity)]
          ring
        have hlogtwo : Real.log 2 ≤ Real.log (Nat.floor x) :=
          Real.strictMonoOn_log.monotoneOn (by norm_num)
            (show 0 < (Nat.floor x : ℝ) by exact_mod_cast (show 0 < Nat.floor x by omega))
            (by exact_mod_cast hfloor)
        linarith
      have hCA : 0 ≤ C_A := by
        have hb := pt.uniform_bound (Nat.floor x) hfloor 1 (by norm_num)
        by_contra hneg
        have hright : 2 * C_A / Real.log (Nat.floor x) < 0 :=
          div_neg_of_neg_of_pos (by linarith) hlogfloor
        linarith [abs_nonneg (pt.mathcalE (Nat.floor x) 1)]
      have hcalc :
          |integerDelta corr.H (Nat.floor x)| +
              |Real.log (Real.log (Nat.floor x)) - Real.log (Real.log x)|
              ≤ (4 * C_A + 4) / Real.log x := by
        calc
        |integerDelta corr.H (Nat.floor x)| +
            |Real.log (Real.log (Nat.floor x)) - Real.log (Real.log x)|
            ≤ 2 * C_A / Real.log (Nat.floor x) + 2 / Real.log x :=
              add_le_add hdelta hdiff
        _ ≤ (4 * C_A + 4) / Real.log x := by
          field_simp
          nlinarith
      simpa [abs_of_nonneg hCA] using hcalc

lemma rate_tendsto_zero {R : ℝ → ℝ} {C X : ℝ}
    (hR : ReciprocalLogRate R C X) : Tendsto R atTop (𝓝 0) := by
  apply (tendsto_zero_iff_abs_tendsto_zero R).2
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun x => abs_nonneg (R x)
  · filter_upwards [eventually_ge_atTop X] with x hx
    exact hR.2.2 x hx
  · exact tendsto_const_nhds.div_atTop Real.tendsto_log_atTop

@[expose] def buildAssembly : PublicTarget := by
  intro corr C_A pz pt ei
  let B : ℝ := Real.eulerMascheroniConstant - corr.H
  let Delta : ℕ → ℝ := integerDelta corr.H
  let C0 : ℝ := 2 * |C_A| + 1
  let R : ℝ → ℝ := realRemainder corr.H Delta
  let CR : ℝ := 4 * |C_A| + 4
  let XR : ℝ := 4
  have hrate : ReciprocalLogRate R CR XR := real_rate corr C_A pz pt ei
  refine {
    data := {
      H := corr.H
      correction_norm_summable := corr.convergence.1
      correction_hasSum := corr.convergence.2.1
      correction_partial_tendsto := corr.convergence.2.2
      B := B
      B_identity := rfl
      Delta := Delta
      C0 := C0
      C0_pos := by positivity
      integer_formula := ?_
      integer_rate := ?_
      R := R
      CR := CR
      XR := XR
      remainder_rate := hrate
      real_formula := ?_
      remainder_tendsto := rate_tendsto_zero hrate
    }
    same_H := rfl
  }
  · intro G hG
    exact integer_formula corr.H G
  · intro G hG
    have hd := integer_delta_bound corr C_A pz pt ei G hG
    have hlog : 0 < Real.log G := Real.log_pos (by exact_mod_cast (show 1 < G by omega))
    have hCA : 0 ≤ C_A := by
      have hb := pt.uniform_bound G hG 1 (by norm_num)
      by_contra hneg
      have hright : 2 * C_A / Real.log G < 0 :=
        div_neg_of_neg_of_pos (by linarith) hlog
      linarith [abs_nonneg (pt.mathcalE G 1)]
    unfold C0 Delta
    rw [abs_of_nonneg hCA]
    calc
      |integerDelta corr.H G| ≤ 2 * C_A / Real.log G := hd
      _ ≤ (2 * C_A + 1) / Real.log G := by
        gcongr
        linarith
  · intro x hx
    exact real_formula corr.H Delta (fun G hG => integer_formula corr.H G) x hx

@[expose] def result : TASK_MSC_ASSEMBLY_Target := by
  intro zeta tail ei
  exact {
    zeta := zeta
    assembly := buildAssembly zeta.corr tail.first.C_A
      zeta.prime_zeta tail.tail ei
  }

end

end Erdos448.DPMertens.Tasks.MSCAssembly
