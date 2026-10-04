module

import all Mathlib.Basic.Real.Basic
public import Erdos448.stage7.tasks.«ROOT-02».Tails
public import Erdos448.stage7.tasks.«ROOT-02».Numerics

public section

set_option backward.isDefEq.respectTransparency false

namespace Erdos448.Stage7.ROOT02.Grid

open Filter Finset Set
open scoped BigOperators Topology
open Erdos448.Stage4
open Erdos448.Stage4.Contracts

noncomputable section

lemma card_biUnion_le_sum_card {s : Finset ℕ} (F : ℕ → Finset ℕ) :
    #(s.biUnion F) ≤ ∑ i ∈ s, #(F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.biUnion_insert]
      calc
        #(F a ∪ s.biUnion F) ≤ #(F a) + #(s.biUnion F) :=
          Finset.card_union_le _ _
        _ ≤ #(F a) + ∑ i ∈ s, #(F i) := Nat.add_le_add_left ih _
        _ = ∑ i ∈ insert a s, #(F i) := by simp [ha]

lemma card_filter_union_bound
    (D J : Finset ℕ) (P A : ℕ → Prop) (B C : ℕ → ℕ → Prop)
    (hcover : ∀ d ∈ D, P d → A d ∨ ∃ j ∈ J, B j d ∨ C j d) :
    #(D.filter P) ≤ #(D.filter A) +
      ∑ j ∈ J, (#(D.filter (B j)) + #(D.filter (C j))) := by
  classical
  let U := J.biUnion fun j => D.filter fun d => B j d ∨ C j d
  have hsub : D.filter P ⊆ D.filter A ∪ U := by
    intro d hd
    have hdD := (Finset.mem_filter.mp hd).1
    rcases hcover d hdD (Finset.mem_filter.mp hd).2 with hA | ⟨j, hj, hBC⟩
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hdD, hA⟩)
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨j, hj, Finset.mem_filter.mpr ⟨hdD, hBC⟩⟩)
  calc
    #(D.filter P) ≤ #(D.filter A ∪ U) := Finset.card_le_card hsub
    _ ≤ #(D.filter A) + #U := Finset.card_union_le _ _
    _ ≤ #(D.filter A) +
        ∑ j ∈ J, #(D.filter fun d => B j d ∨ C j d) :=
      Nat.add_le_add_left (card_biUnion_le_sum_card _) _
    _ ≤ #(D.filter A) +
        ∑ j ∈ J, (#(D.filter (B j)) + #(D.filter (C j))) := by
      gcongr with j hj
      calc
        #({d ∈ D | B j d ∨ C j d}) ≤
            #(D.filter (B j) ∪ D.filter (C j)) := by
          apply Finset.card_le_card
          intro d hd
          rcases (Finset.mem_filter.mp hd).2 with hB | hC
          · exact Finset.mem_union_left _ (Finset.mem_filter.mpr
              ⟨(Finset.mem_filter.mp hd).1, hB⟩)
          · exact Finset.mem_union_right _ (Finset.mem_filter.mpr
              ⟨(Finset.mem_filter.mp hd).1, hC⟩)
        _ ≤ #(D.filter (B j)) + #(D.filter (C j)) :=
          Finset.card_union_le _ _

lemma gridPoint_tendsto (xi sigma : ℝ)
    (hxi : Real.exp 1 < xi) (hsigma : 2 ≤ sigma) :
    Tendsto (gridPoint xi sigma) atTop atTop := by
  have hlogxi : 0 < Real.log xi :=
    Real.log_pos ((Real.one_lt_exp_iff.mpr zero_lt_one).trans hxi)
  have hlogsigma : 0 < Real.log sigma :=
    Real.log_pos (one_lt_two.trans_le hsigma)
  have hexp : Tendsto (fun j : ℕ => Real.exp (j : ℝ)) atTop atTop :=
    Real.tendsto_exp_atTop.comp tendsto_natCast_atTop_atTop
  have hmul : Tendsto
      (fun j : ℕ => Real.exp (j : ℝ) *
        (Real.log sigma * Real.log xi)) atTop atTop :=
    by simpa [mul_comm] using
      hexp.const_mul_atTop (mul_pos hlogsigma hlogxi)
  apply (Real.tendsto_exp_atTop.comp hmul).congr'
  exact Eventually.of_forall fun j => by
    simp only [Function.comp_apply, gridPoint]
    congr 1
    ring

lemma gridPoint_gt_sigma (xi sigma : ℝ)
    (hxi : Real.exp 1 < xi) (hsigma : 2 ≤ sigma) (j : ℕ) :
    sigma < gridPoint xi sigma j := by
  have hs0 : 0 < sigma := zero_lt_two.trans_le hsigma
  have hlogs : 0 < Real.log sigma := Real.log_pos (one_lt_two.trans_le hsigma)
  have hxi0 : 0 < xi := (Real.exp_pos 1).trans hxi
  have hlogxi : 1 < Real.log xi := (Real.lt_log_iff_exp_lt hxi0).2 hxi
  have hexpj : 1 ≤ Real.exp (j : ℝ) := Real.one_le_exp (Nat.cast_nonneg j)
  have hprod : 1 < Real.exp (j : ℝ) * Real.log xi := by
    calc
      1 < 1 * Real.log xi := by simpa using hlogxi
      _ ≤ Real.exp (j : ℝ) * Real.log xi :=
        mul_le_mul_of_nonneg_right hexpj
          (Real.log_pos ((Real.one_lt_exp_iff.mpr zero_lt_one).trans hxi)).le
  have hexponent :
      Real.log sigma < Real.exp (j : ℝ) * Real.log sigma * Real.log xi := by
    have haux := mul_pos hlogs (sub_pos.mpr hprod)
    calc
      Real.log sigma = Real.log sigma * 1 := by ring
      _ < Real.log sigma * (Real.exp (j : ℝ) * Real.log xi) := by
        nlinarith
      _ = Real.exp (j : ℝ) * Real.log sigma * Real.log xi := by ring
  calc
    sigma = Real.exp (Real.log sigma) := (Real.exp_log hs0).symm
    _ < Real.exp (Real.exp (j : ℝ) * Real.log sigma * Real.log xi) := by
      exact Real.exp_lt_exp.mpr hexponent
    _ = gridPoint xi sigma j := rfl

lemma lambda_upper_iff
    {epsilon sigma u : ℝ} {d : PosNat}
    (hR : 1 < Real.log u / Real.log sigma) :
    0.98 * epsilon < lambdaDeviation sigma d u ↔
      ((1 + 1.96 * epsilon) / 2) *
          Real.log (Real.log u / Real.log sigma) < omegaBelowRaw d.1 u := by
  unfold lambdaDeviation omegaBelowRaw
  rw [dif_pos d.2, lt_div_iff₀ (Real.log_pos hR)]
  constructor <;> intro h <;> nlinarith

lemma lambda_lower_iff
    {epsilon sigma u : ℝ} {d : PosNat}
    (hR : 1 < Real.log u / Real.log sigma) :
    lambdaDeviation sigma d u < -0.98 * epsilon ↔
      (omegaBelowRaw d.1 u : ℝ) <
        ((1 - 1.96 * epsilon) / 2) *
          Real.log (Real.log u / Real.log sigma) := by
  unfold lambdaDeviation omegaBelowRaw
  rw [dif_pos d.2, div_lt_iff₀ (Real.log_pos hR)]
  constructor <;> intro h <;> nlinarith

lemma plus_exponent_le (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (hepsilon_le : epsilon ≤ 1 / 10) :
    ((1 + 1.96 * epsilon) - 1 -
        (1 + 1.96 * epsilon) * Real.log (1 + 1.96 * epsilon)) / 2 ≤
      -0.901 * epsilon ^ 2 := by
  have h := Erdos448.Stage7.ROOT02.Numerics.p014 epsilon hepsilon hepsilon_le
  dsimp at h
  nlinarith

lemma minus_exponent_le (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (hepsilon_le : epsilon ≤ 1 / 10) :
    ((1 - 1.96 * epsilon) - 1 -
        (1 - 1.96 * epsilon) * Real.log (1 - 1.96 * epsilon)) / 2 ≤
      -0.901 * epsilon ^ 2 := by
  have h := Erdos448.Stage7.ROOT02.Numerics.p015 epsilon hepsilon hepsilon_le
  dsimp at h
  nlinarith

lemma roughDensity_nonneg (theta : ℝ) : 0 ≤ roughDensity theta := by
  unfold roughDensity
  apply Finset.prod_nonneg
  intro p hp
  have hpPrime := (Finset.mem_filter.mp hp).2
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hpPrime.pos
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hpPrime.one_lt.le
  exact sub_nonneg.mpr ((div_le_one hp0).2 hp1)

lemma grid_log_ratio (xi sigma : ℝ) (hsigma : 2 ≤ sigma) (j : ℕ) :
    Real.log (gridPoint xi sigma j) / Real.log sigma =
      Real.exp (j : ℝ) * Real.log xi := by
  have hlog : Real.log sigma ≠ 0 :=
    (Real.log_pos (one_lt_two.trans_le hsigma)).ne'
  unfold gridPoint
  rw [Real.log_exp]
  field_simp [hlog]

lemma grid_rpow_le
    (epsilon xi sigma a : ℝ) (j : ℕ)
    (hepsilon : 0 < epsilon) (hxi : Real.exp 1 < xi)
    (hsigma : 2 ≤ sigma)
    (ha : a ≤ -0.901 * epsilon ^ 2) :
    (Real.log (gridPoint xi sigma j) / Real.log sigma).rpow a ≤
      (Real.log xi).rpow (-0.901 * epsilon ^ 2) *
        (Real.exp (-0.901 * epsilon ^ 2)) ^ j := by
  let alpha : ℝ := 0.901 * epsilon ^ 2
  have halpha : 0 < alpha := mul_pos (by norm_num) (sq_pos_of_pos hepsilon)
  have hxi0 : 0 < xi := (Real.exp_pos 1).trans hxi
  have hlogxi : 1 < Real.log xi := by
    exact (Real.lt_log_iff_exp_lt hxi0).2 hxi
  have hbase : 1 ≤ Real.exp (j : ℝ) * Real.log xi :=
    one_le_mul_of_one_le_of_one_le (Real.one_le_exp (by positivity)) hlogxi.le
  rw [grid_log_ratio xi sigma hsigma j]
  calc
    (Real.exp (j : ℝ) * Real.log xi).rpow a ≤
        (Real.exp (j : ℝ) * Real.log xi).rpow (-alpha) :=
      Real.rpow_le_rpow_of_exponent_le hbase (by simpa [alpha] using ha)
    _ = (Real.exp (j : ℝ)).rpow (-alpha) *
        (Real.log xi).rpow (-alpha) := by
      exact Real.mul_rpow (Real.exp_nonneg _) (zero_le_one.trans hlogxi.le)
    _ = (Real.log xi).rpow (-alpha) * (Real.exp (-alpha)) ^ j := by
      have hexp : (Real.exp (j : ℝ)).rpow (-alpha) =
          (Real.exp (-alpha)) ^ j := by
        calc
          (Real.exp (j : ℝ)).rpow (-alpha) =
              Real.exp ((j : ℝ) * (-alpha)) := (Real.exp_mul _ _).symm
          _ = (Real.exp (-alpha)) ^ j := by
            simpa [mul_comm] using Real.exp_nat_mul (-alpha) j
      rw [hexp]
      ring
    _ = (Real.log xi).rpow (-0.901 * epsilon ^ 2) *
        (Real.exp (-0.901 * epsilon ^ 2)) ^ j := by simp [alpha]

lemma terminal_rpow_le
    (epsilon xi sigma x a : ℝ)
    (hepsilon : 0 < epsilon) (hxi : Real.exp 1 < xi)
    (hsigma : 2 ≤ sigma) (hx : gridU0 xi sigma < x)
    (ha : a ≤ -0.901 * epsilon ^ 2) :
    (Real.log x / Real.log sigma).rpow a ≤
      (Real.log xi).rpow (-0.901 * epsilon ^ 2) := by
  let alpha : ℝ := 0.901 * epsilon ^ 2
  have halpha : 0 < alpha := mul_pos (by norm_num) (sq_pos_of_pos hepsilon)
  have hxi0 : 0 < xi := (Real.exp_pos 1).trans hxi
  have hlogxi : 1 < Real.log xi :=
    (Real.lt_log_iff_exp_lt hxi0).2 hxi
  have hlogsigma : 0 < Real.log sigma :=
    Real.log_pos (one_lt_two.trans_le hsigma)
  have hx0 : 0 < x := (Real.exp_pos _).trans hx
  have hlogx : Real.log xi * Real.log sigma < Real.log x := by
    have h := Real.strictMonoOn_log (Real.exp_pos _) hx0 hx
    simpa [gridU0] using h
  have hratio_xi : Real.log xi ≤ Real.log x / Real.log sigma := by
    rw [le_div_iff₀ hlogsigma]
    exact hlogx.le
  have hratio_one : 1 ≤ Real.log x / Real.log sigma :=
    hlogxi.le.trans hratio_xi
  calc
    (Real.log x / Real.log sigma).rpow a ≤
        (Real.log x / Real.log sigma).rpow (-alpha) :=
      Real.rpow_le_rpow_of_exponent_le hratio_one (by simpa [alpha] using ha)
    _ ≤ (Real.log xi).rpow (-alpha) :=
      Real.rpow_le_rpow_of_nonpos (zero_lt_one.trans hlogxi)
        hratio_xi (neg_nonpos.mpr halpha.le)
    _ = (Real.log xi).rpow (-0.901 * epsilon ^ 2) := by simp [alpha]

@[expose] def plusQ (epsilon theta sigma u : ℝ)
    (hepsilon : 0 < epsilon) (hepsilon_le : epsilon ≤ 1 / 10)
    (htheta : 2 ≤ theta) (hsigma : theta ≤ sigma) (hu : sigma < u) :
    MomentParameters :=
  { y := 1 + 1.96 * epsilon
    y_pos := by positivity
    y_lt_two := by norm_num at hepsilon_le ⊢; nlinarith
    theta := theta, theta_ge_two := htheta
    sigma := sigma, sigma_ge_theta := hsigma
    u := u, u_gt_sigma := hu }

@[expose] def minusQ (epsilon theta sigma u : ℝ)
    (hepsilon : 0 < epsilon) (hepsilon_le : epsilon ≤ 1 / 10)
    (htheta : 2 ≤ theta) (hsigma : theta ≤ sigma) (hu : sigma < u) :
    MomentParameters :=
  { y := 1 - 1.96 * epsilon
    y_pos := by norm_num at hepsilon_le ⊢; nlinarith
    y_lt_two := by nlinarith
    theta := theta, theta_ge_two := htheta
    sigma := sigma, sigma_ge_theta := hsigma
    u := u, u_gt_sigma := hu }

lemma terminal_count_bound
    (epsilon xi sigma theta x : ℝ)
    (hepsilon : 0 < epsilon) (hepsilon_le : epsilon ≤ 1 / 10)
    (hxi : Real.exp 1 < xi) (htheta : 2 ≤ theta) (hsigma : theta ≤ sigma)
    (hx : gridU0 xi sigma < x) :
    ∃ J : Finset ℕ,
      (∀ j ∈ J, gridPoint xi sigma j < x) ∧
      ∀ n : PosNat,
      (terminalGridCount epsilon xi sigma x n : ℝ) ≤
        upperTailCount
          (plusQ epsilon theta sigma x hepsilon hepsilon_le htheta hsigma
            (lt_trans (gridPoint_gt_sigma xi sigma hxi (htheta.trans hsigma) 0)
              (by simpa [gridU0, gridPoint, mul_comm] using hx))) n +
        ∑ j ∈ J,
          ((upperTailCount
              (plusQ epsilon theta sigma (gridPoint xi sigma j)
                hepsilon hepsilon_le htheta hsigma
                (gridPoint_gt_sigma xi sigma hxi (htheta.trans hsigma) j)) n : ℝ) +
            lowerTailCount
              (minusQ epsilon theta sigma (gridPoint xi sigma j)
                hepsilon hepsilon_le htheta hsigma
                (gridPoint_gt_sigma xi sigma hxi (htheta.trans hsigma) j)) n) := by
  have hevent : ∀ᶠ j in atTop, x ≤ gridPoint xi sigma j :=
    (gridPoint_tendsto xi sigma hxi (htheta.trans hsigma)).eventually_ge_atTop x
  rcases Filter.eventually_atTop.1 hevent with ⟨N, hN⟩
  let J := (Finset.range N).filter fun j => gridPoint xi sigma j < x
  refine ⟨J, ?_, ?_⟩
  · intro j hj
    exact (Finset.mem_filter.mp hj).2
  intro n
  let qx := plusQ epsilon theta sigma x hepsilon hepsilon_le htheta hsigma
    (lt_trans (gridPoint_gt_sigma xi sigma hxi (htheta.trans hsigma) 0)
      (by simpa [gridU0, gridPoint, mul_comm] using hx))
  let qp := fun j => plusQ epsilon theta sigma (gridPoint xi sigma j)
    hepsilon hepsilon_le htheta hsigma
      (gridPoint_gt_sigma xi sigma hxi (htheta.trans hsigma) j)
  let qm := fun j => minusQ epsilon theta sigma (gridPoint xi sigma j)
    hepsilon hepsilon_le htheta hsigma
      (gridPoint_gt_sigma xi sigma hxi (htheta.trans hsigma) j)
  let D := divisorSet n
  let P := fun d : ℕ => roughIndicator d sigma = 1 ∧
    if hd : 0 < d then TerminalGridEvent epsilon xi sigma x ⟨d, hd⟩ else False
  let A := fun d : ℕ => roughIndicator d sigma = 1 ∧
    (qx.y / 2) * Real.log (Real.log qx.u / Real.log qx.sigma) <
      omegaBelowRaw d qx.u
  let B := fun j d : ℕ => roughIndicator d sigma = 1 ∧
    (qp j).y / 2 * Real.log (Real.log (qp j).u / Real.log (qp j).sigma) <
      omegaBelowRaw d (qp j).u
  let C := fun j d : ℕ => roughIndicator d sigma = 1 ∧
    (omegaBelowRaw d (qm j).u : ℝ) <
      (qm j).y / 2 * Real.log (Real.log (qm j).u / Real.log (qm j).sigma)
  have hcover : ∀ d ∈ D, P d → A d ∨ ∃ j ∈ J, B j d ∨ C j d := by
    intro d hdD hdP
    rcases hdP with ⟨hdrough, hdterm⟩
    have hdpos : 0 < d :=
      Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hdD).1 n.2
    simp only [dif_pos hdpos] at hdterm
    rcases hdterm with ⟨j, hju, hjdev⟩ | hfinal
    · right
      have hjN : j < N := by
        by_contra hjN
        exact (not_lt_of_ge (hN j (Nat.le_of_not_gt hjN))) hju
      have hjJ : j ∈ J := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hjN, hju⟩
      refine ⟨j, hjJ, ?_⟩
      have hR : 1 < Real.log (gridPoint xi sigma j) / Real.log sigma := by
        have hslog := Real.log_pos (one_lt_two.trans_le (htheta.trans hsigma))
        rw [one_lt_div hslog]
        exact Real.strictMonoOn_log
          (show sigma ∈ Set.Ioi 0 by exact (zero_lt_two.trans_le (htheta.trans hsigma)))
          (show gridPoint xi sigma j ∈ Set.Ioi 0 by exact Real.exp_pos _)
          (gridPoint_gt_sigma xi sigma hxi (htheta.trans hsigma) j)
      rcases hjdev with hup | hlo
      · left
        refine ⟨hdrough, ?_⟩
        simpa [B, qp, plusQ] using (lambda_upper_iff hR).mp hup
      · right
        refine ⟨hdrough, ?_⟩
        simpa [C, qm, minusQ] using (lambda_lower_iff hR).mp hlo
    · left
      refine ⟨hdrough, ?_⟩
      have hR : 1 < Real.log x / Real.log sigma := by
        have hslog := Real.log_pos (one_lt_two.trans_le (htheta.trans hsigma))
        rw [one_lt_div hslog]
        apply Real.strictMonoOn_log
        · exact zero_lt_two.trans_le (htheta.trans hsigma)
        · exact lt_trans (zero_lt_two.trans_le (htheta.trans hsigma))
            (lt_trans (gridPoint_gt_sigma xi sigma hxi (htheta.trans hsigma) 0)
              (by simpa [gridU0, gridPoint, mul_comm] using hx))
        · exact lt_trans (gridPoint_gt_sigma xi sigma hxi (htheta.trans hsigma) 0)
            (by simpa [gridU0, gridPoint, mul_comm] using hx)
      simpa [A, qx, plusQ] using (lambda_upper_iff hR).mp hfinal
  letI : DecidablePred P := fun _ => instDecidableAnd
  letI : DecidablePred A := fun _ => instDecidableAnd
  letI (j : ℕ) : DecidablePred (B j) := fun _ => instDecidableAnd
  letI (j : ℕ) : DecidablePred (C j) := fun _ => instDecidableAnd
  have hcard := card_filter_union_bound D J P A B C hcover
  have hPfilter :
      @Finset.filter ℕ P (fun d => Classical.propDecidable (P d)) D =
        D.filter P :=
    Finset.filter_congr_decidable D P _
  have hPcard := congrArg Finset.card hPfilter
  rw [hPcard] at hcard
  have hAfilter :
      @Finset.filter ℕ A (fun d => Classical.propDecidable (A d)) D =
        D.filter A :=
    Finset.filter_congr_decidable D A _
  have hAcard := congrArg Finset.card hAfilter
  rw [hAcard] at hcard
  have hBcard (j : ℕ) :
      #(@Finset.filter ℕ (B j)
          (fun d => Classical.propDecidable (B j d)) D) =
        #(D.filter (B j)) :=
    congrArg Finset.card (Finset.filter_congr_decidable D (B j) _)
  have hCcard (j : ℕ) :
      #(@Finset.filter ℕ (C j)
          (fun d => Classical.propDecidable (C j d)) D) =
        #(D.filter (C j)) :=
    congrArg Finset.card (Finset.filter_congr_decidable D (C j) _)
  simp_rw [hBcard, hCcard] at hcard
  change (#(D.filter P) : ℝ) ≤ (#(D.filter A) : ℝ) +
    ∑ j ∈ J, ((#(D.filter (B j)) : ℝ) + (#(D.filter (C j)) : ℝ))
  have hcard' : #(D.filter P) ≤ #(D.filter A) +
      ∑ j ∈ J, (#(D.filter (B j)) + #(D.filter (C j))) := by
    exact hcard
  have hcast : (#(D.filter P) : ℝ) ≤
      ((#(D.filter A) +
        ∑ j ∈ J, (#(D.filter (B j)) + #(D.filter (C j))) : ℕ) : ℝ) :=
    (Nat.cast_le).2 hcard'
  push_cast at hcast
  exact hcast

theorem p016
    (hEXT : EXT001Statement) (h007 : P007Statement) (h008 : P008Statement.{0}) :
    P016Statement := by
  intro epsilon hepsilon hepsilon_le
  let yP : ℝ := 1 + 1.96 * epsilon
  let yM : ℝ := 1 - 1.96 * epsilon
  have hyP1 : 1 < yP := by dsimp [yP]; nlinarith
  have hyP2 : yP < 2 := by dsimp [yP]; norm_num at hepsilon_le ⊢; nlinarith
  have hyM0 : 0 < yM := by dsimp [yM]; norm_num at hepsilon_le ⊢; nlinarith
  have hyM1 : yM < 1 := by dsimp [yM]; nlinarith
  have h011 := Erdos448.Stage7.ROOT02.Mean.p011 hEXT h007 h008
  rcases Erdos448.Stage7.ROOT02.Tails.p012 h011 yP hyP1 hyP2 with ⟨upper⟩
  rcases Erdos448.Stage7.ROOT02.Tails.p013 h011 yM hyM0 hyM1 with ⟨lower⟩
  let alpha : ℝ := 0.901 * epsilon ^ 2
  let r : ℝ := Real.exp (-alpha)
  have halpha : 0 < alpha := mul_pos (by norm_num) (sq_pos_of_pos hepsilon)
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := by
    dsimp [r]
    rw [Real.exp_lt_one_iff]
    linarith
  have hden : 0 < 1 - r := sub_pos.mpr hr1
  let Cgrid : ℝ := upper.C_y + (upper.C_y + lower.C_y) / (1 - r)
  have hCgrid : 0 < Cgrid := by
    dsimp [Cgrid]
    have hsum : 0 < upper.C_y + lower.C_y := add_pos upper.C_y_pos lower.C_y_pos
    exact add_pos upper.C_y_pos (div_pos hsum hden)
  refine ⟨{
    Cgrid := Cgrid
    Cgrid_pos := hCgrid
    grid_bound := ?_
  }⟩
  intro xi sigma theta x hxi htheta hsigma hx
  have hsigma2 : 2 ≤ sigma := htheta.trans hsigma
  have hsx : sigma < x :=
    (gridPoint_gt_sigma xi sigma hxi hsigma2 0).trans
      (by simpa [gridU0, gridPoint, mul_comm] using hx)
  have hx2 : 2 ≤ x := htheta.trans hsigma |>.trans hsx.le
  rcases terminal_count_bound epsilon xi sigma theta x hepsilon hepsilon_le
      hxi htheta hsigma hx with ⟨J, hJx, hcount⟩
  let qx := plusQ epsilon theta sigma x hepsilon hepsilon_le htheta hsigma hsx
  let qp := fun j => plusQ epsilon theta sigma (gridPoint xi sigma j)
    hepsilon hepsilon_le htheta hsigma
      (gridPoint_gt_sigma xi sigma hxi hsigma2 j)
  let qm := fun j => minusQ epsilon theta sigma (gridPoint xi sigma j)
    hepsilon hepsilon_le htheta hsigma
      (gridPoint_gt_sigma xi sigma hxi hsigma2 j)
  have hmass :
      gridExceptionalMass epsilon xi sigma theta x ≤
        tailMeanSubject true qx x +
          ∑ j ∈ J,
            (tailMeanSubject true (qp j) x + tailMeanSubject false (qm j) x) := by
    classical
    unfold gridExceptionalMass tailMeanSubject
    calc
      (∑ n ∈ positiveNatsBelow x,
          if hn : 0 < n then
            (roughIndicator n theta : ℝ) / (roughTau ⟨n, hn⟩ sigma : ℝ) *
              (terminalGridCount epsilon xi sigma x ⟨n, hn⟩ : ℝ)
          else 0) ≤
        (∑ n ∈ positiveNatsBelow x,
          if hn : 0 < n then
            tailPointSubject true qx ⟨n, hn⟩ +
              ∑ j ∈ J,
                (tailPointSubject true (qp j) ⟨n, hn⟩ +
                  tailPointSubject false (qm j) ⟨n, hn⟩)
          else 0) := by
        apply Finset.sum_le_sum
        intro n hnmem
        split_ifs with hn
        · have hc : 0 ≤ (roughIndicator n theta : ℝ) /
              (roughTau ⟨n, hn⟩ sigma : ℝ) := by positivity
          calc
            (roughIndicator n theta : ℝ) / (roughTau ⟨n, hn⟩ sigma : ℝ) *
                (terminalGridCount epsilon xi sigma x ⟨n, hn⟩ : ℝ) ≤
              (roughIndicator n theta : ℝ) / (roughTau ⟨n, hn⟩ sigma : ℝ) *
                ((upperTailCount qx ⟨n, hn⟩ : ℝ) +
                  ∑ j ∈ J,
                    ((upperTailCount (qp j) ⟨n, hn⟩ : ℝ) +
                      lowerTailCount (qm j) ⟨n, hn⟩)) := by
                exact mul_le_mul_of_nonneg_left (hcount ⟨n, hn⟩) hc
            _ = tailPointSubject true qx ⟨n, hn⟩ +
                ∑ j ∈ J,
                  (tailPointSubject true (qp j) ⟨n, hn⟩ +
                    tailPointSubject false (qm j) ⟨n, hn⟩) := by
              simp only [tailPointSubject, if_true]
              dsimp [qx, qp, qm, plusQ, minusQ]
              rw [mul_add, Finset.mul_sum]
              congr 1
              apply Finset.sum_congr rfl
              intro j hj
              ring
        · exact le_rfl
      _ = tailMeanSubject true qx x +
          ∑ j ∈ J,
            (tailMeanSubject true (qp j) x + tailMeanSubject false (qm j) x) := by
        unfold tailMeanSubject
        calc
          (∑ n ∈ positiveNatsBelow x,
              if hn : 0 < n then
                tailPointSubject true qx ⟨n, hn⟩ +
                  ∑ j ∈ J,
                    (tailPointSubject true (qp j) ⟨n, hn⟩ +
                      tailPointSubject false (qm j) ⟨n, hn⟩)
              else 0) =
            (∑ n ∈ positiveNatsBelow x,
                if hn : 0 < n then tailPointSubject true qx ⟨n, hn⟩ else 0) +
              ((∑ n ∈ positiveNatsBelow x,
                  if hn : 0 < n then
                    ∑ j ∈ J, tailPointSubject true (qp j) ⟨n, hn⟩
                  else 0) +
                (∑ n ∈ positiveNatsBelow x,
                  if hn : 0 < n then
                    ∑ j ∈ J, tailPointSubject false (qm j) ⟨n, hn⟩
                  else 0)) := by
            rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro n hnmem
            by_cases hn : 0 < n
            · simp only [dif_pos hn, Finset.sum_add_distrib]
            · simp only [dif_neg hn, zero_add]
          _ = (∑ n ∈ positiveNatsBelow x,
                if hn : 0 < n then tailPointSubject true qx ⟨n, hn⟩ else 0) +
              ((∑ j ∈ J, ∑ n ∈ positiveNatsBelow x,
                  if hn : 0 < n then tailPointSubject true (qp j) ⟨n, hn⟩ else 0) +
                (∑ j ∈ J, ∑ n ∈ positiveNatsBelow x,
                  if hn : 0 < n then tailPointSubject false (qm j) ⟨n, hn⟩ else 0)) := by
            congr 1
            apply congrArg₂ (· + ·)
            · rw [Finset.sum_comm]
              apply Finset.sum_congr rfl
              intro n hnmem
              by_cases hn : 0 < n <;> simp [hn]
            · rw [Finset.sum_comm]
              apply Finset.sum_congr rfl
              intro n hnmem
              by_cases hn : 0 < n <;> simp [hn]
          _ = (∑ n ∈ positiveNatsBelow x,
                if hn : 0 < n then tailPointSubject true qx ⟨n, hn⟩ else 0) +
              ∑ j ∈ J,
                ((∑ n ∈ positiveNatsBelow x,
                    if hn : 0 < n then tailPointSubject true (qp j) ⟨n, hn⟩ else 0) +
                  ∑ n ∈ positiveNatsBelow x,
                    if hn : 0 < n then tailPointSubject false (qm j) ⟨n, hn⟩ else 0) := by
            rw [Finset.sum_add_distrib]
  have hprefix0 : 0 ≤ upper.C_y * x * roughDensity theta :=
    mul_nonneg (mul_nonneg upper.C_y_pos.le (by positivity))
      (roughDensity_nonneg theta)
  have hprefixM0 : 0 ≤ lower.C_y * x * roughDensity theta :=
    mul_nonneg (mul_nonneg lower.C_y_pos.le (by positivity))
      (roughDensity_nonneg theta)
  have hterminal :
      tailMeanSubject true qx x ≤
        upper.C_y * x * roughDensity theta *
          (Real.log xi).rpow (-alpha) := by
    have h := (upper.bound theta sigma x x htheta hsigma hsx le_rfl hx2).2
    have hexp : ((yP - 1 - yP * Real.log yP) / 2) ≤
        -0.901 * epsilon ^ 2 := by
      simpa [yP] using plus_exponent_le epsilon hepsilon hepsilon_le
    have hrp := terminal_rpow_le epsilon xi sigma x
      ((yP - 1 - yP * Real.log yP) / 2) hepsilon hxi hsigma2 hx hexp
    have hmul := mul_le_mul_of_nonneg_left hrp hprefix0
    simpa [qx, plusQ, yP, alpha] using h.trans hmul
  have hsampleP : ∀ j ∈ J,
      tailMeanSubject true (qp j) x ≤
        upper.C_y * x * roughDensity theta *
          ((Real.log xi).rpow (-alpha) * r ^ j) := by
    intro j hj
    have h := (upper.bound theta sigma (gridPoint xi sigma j) x
      htheta hsigma (gridPoint_gt_sigma xi sigma hxi hsigma2 j)
      (hJx j hj).le hx2).2
    have hexp : ((yP - 1 - yP * Real.log yP) / 2) ≤
        -0.901 * epsilon ^ 2 := by
      simpa [yP] using plus_exponent_le epsilon hepsilon hepsilon_le
    have hrp := grid_rpow_le epsilon xi sigma
      ((yP - 1 - yP * Real.log yP) / 2) j hepsilon hxi hsigma2 hexp
    have hmul := mul_le_mul_of_nonneg_left hrp hprefix0
    simpa [qp, plusQ, yP, alpha, r] using h.trans hmul
  have hsampleM : ∀ j ∈ J,
      tailMeanSubject false (qm j) x ≤
        lower.C_y * x * roughDensity theta *
          ((Real.log xi).rpow (-alpha) * r ^ j) := by
    intro j hj
    have h := (lower.bound theta sigma (gridPoint xi sigma j) x
      htheta hsigma (gridPoint_gt_sigma xi sigma hxi hsigma2 j)
      (hJx j hj).le hx2).2
    have hexp : ((yM - 1 - yM * Real.log yM) / 2) ≤
        -0.901 * epsilon ^ 2 := by
      simpa [yM] using minus_exponent_le epsilon hepsilon hepsilon_le
    have hrp := grid_rpow_le epsilon xi sigma
      ((yM - 1 - yM * Real.log yM) / 2) j hepsilon hxi hsigma2 hexp
    have hmul := mul_le_mul_of_nonneg_left hrp hprefixM0
    simpa [qm, minusQ, yM, alpha, r] using h.trans hmul
  have hgeom : ∑ j ∈ J, r ^ j ≤ (1 - r)⁻¹ := by
    calc
      ∑ j ∈ J, r ^ j ≤ ∑' j : ℕ, r ^ j :=
        (summable_geometric_of_lt_one hr0 hr1).sum_le_tsum J
          (fun j hj => pow_nonneg hr0 j)
      _ = (1 - r)⁻¹ := tsum_geometric_of_lt_one hr0 hr1
  calc
    gridExceptionalMass epsilon xi sigma theta x ≤
        tailMeanSubject true qx x +
          ∑ j ∈ J,
            (tailMeanSubject true (qp j) x + tailMeanSubject false (qm j) x) := hmass
    _ ≤ upper.C_y * x * roughDensity theta *
          (Real.log xi).rpow (-alpha) +
        ∑ j ∈ J,
          ((upper.C_y + lower.C_y) * x * roughDensity theta *
            ((Real.log xi).rpow (-alpha) * r ^ j)) := by
      apply add_le_add hterminal
      apply Finset.sum_le_sum
      intro j hj
      calc
        tailMeanSubject true (qp j) x + tailMeanSubject false (qm j) x ≤
            upper.C_y * x * roughDensity theta *
                ((Real.log xi).rpow (-alpha) * r ^ j) +
              lower.C_y * x * roughDensity theta *
                ((Real.log xi).rpow (-alpha) * r ^ j) :=
          add_le_add (hsampleP j hj) (hsampleM j hj)
        _ = (upper.C_y + lower.C_y) * x * roughDensity theta *
            ((Real.log xi).rpow (-alpha) * r ^ j) := by ring
    _ = upper.C_y * x * roughDensity theta *
          (Real.log xi).rpow (-alpha) +
        ((upper.C_y + lower.C_y) * x * roughDensity theta *
          (Real.log xi).rpow (-alpha)) * (∑ j ∈ J, r ^ j) := by
      rw [Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ ≤ upper.C_y * x * roughDensity theta *
          (Real.log xi).rpow (-alpha) +
        ((upper.C_y + lower.C_y) * x * roughDensity theta *
          (Real.log xi).rpow (-alpha)) * (1 - r)⁻¹ := by
      apply add_le_add_right
      exact mul_le_mul_of_nonneg_left hgeom
        (mul_nonneg
          (mul_nonneg
            (mul_nonneg (add_nonneg upper.C_y_pos.le lower.C_y_pos.le)
              (by positivity))
            (roughDensity_nonneg theta))
          (Real.rpow_nonneg (zero_lt_one.trans
            ((Real.lt_log_iff_exp_lt ((Real.exp_pos 1).trans hxi)).2 hxi)).le _))
    _ = Cgrid * x * roughDensity theta *
          (Real.log xi).rpow (-0.901 * epsilon ^ 2) := by
      dsimp [Cgrid, alpha]
      rw [inv_eq_one_div]
      field_simp [hden.ne']

end

end Erdos448.Stage7.ROOT02.Grid
