module

import all Mathlib.Basic.Real.Basic
public import Erdos448.stage7.tasks.«ROOT-02».Grid
public import Erdos448.stage7.tasks.«ROOT-02».Threshold

public section

set_option backward.isDefEq.respectTransparency false

namespace Erdos448.Stage7.ROOT02.AllU

open Filter Finset Set
open scoped BigOperators Topology
open Erdos448.Stage4
open Erdos448.Stage4.Contracts

noncomputable section

lemma omegaBelow_mono {m : PosNat} {u v : ℝ} (huv : u ≤ v) :
    omegaBelow m u ≤ omegaBelow m v := by
  unfold omegaBelow
  exact Finset.sum_le_sum fun p hp => by
    by_cases hpu : (p : ℝ) < u
    · have hpv : (p : ℝ) < v := lt_of_lt_of_le hpu huv
      simp [hpu, hpv]
    · simp [hpu]

lemma gridPoint_zero (xi sigma : ℝ) :
    gridPoint xi sigma 0 = gridU0 xi sigma := by
  simp [gridPoint, gridU0, mul_comm]

lemma gridPoint_ge_zero (xi sigma : ℝ)
    (hxi : Real.exp 1 < xi) (hsigma : 2 ≤ sigma) (j : ℕ) :
    gridU0 xi sigma ≤ gridPoint xi sigma j := by
  rw [← gridPoint_zero xi sigma]
  unfold gridPoint
  apply Real.exp_le_exp.mpr
  have hlogs : 0 ≤ Real.log sigma :=
    (Real.log_pos (one_lt_two.trans_le hsigma)).le
  have hlogxi : 0 ≤ Real.log xi :=
    (Real.log_pos ((Real.one_lt_exp_iff.mpr zero_lt_one).trans hxi)).le
  have hexp : 1 ≤ Real.exp (j : ℝ) := Real.one_le_exp (by positivity)
  have hfirst : Real.log sigma ≤ Real.exp (j : ℝ) * Real.log sigma :=
    by simpa only [one_mul] using mul_le_mul_of_nonneg_right hexp hlogs
  simpa only [Nat.cast_zero, Real.exp_zero, one_mul] using
    mul_le_mul_of_nonneg_right hfirst hlogxi

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

lemma logRatio_pos (xi sigma u : ℝ)
    (hxi : Real.exp 1 < xi) (hsigma : 2 ≤ sigma)
    (hu : gridU0 xi sigma ≤ u) :
    0 < Real.log u / Real.log sigma := by
  have hlogs : 0 < Real.log sigma := Real.log_pos (one_lt_two.trans_le hsigma)
  have hu0 : 0 < u := (Real.exp_pos _).trans_le hu
  have hlogu : 0 < Real.log u := by
    have hU1 : 1 < gridU0 xi sigma := by
      unfold gridU0
      rw [Real.one_lt_exp_iff]
      exact mul_pos
        (Real.log_pos ((Real.one_lt_exp_iff.mpr zero_lt_one).trans hxi)) hlogs
    exact Real.log_pos (hU1.trans_le hu)
  exact div_pos hlogu hlogs

lemma center_mono (xi sigma u v : ℝ)
    (hxi : Real.exp 1 < xi) (hsigma : 2 ≤ sigma)
    (huU : gridU0 xi sigma ≤ u) (huv : u ≤ v) :
    Real.log (Real.log u / Real.log sigma) ≤
      Real.log (Real.log v / Real.log sigma) := by
  have hlogs : 0 < Real.log sigma := Real.log_pos (one_lt_two.trans_le hsigma)
  have hu0 : 0 < u := (Real.exp_pos _).trans_le huU
  have hv0 : 0 < v := hu0.trans_le huv
  have hlog : Real.log u ≤ Real.log v :=
    Real.strictMonoOn_log.monotoneOn hu0 hv0 huv
  have hratio : Real.log u / Real.log sigma ≤ Real.log v / Real.log sigma :=
    div_le_div_of_nonneg_right hlog hlogs.le
  exact Real.strictMonoOn_log.monotoneOn
    (logRatio_pos xi sigma u hxi hsigma huU)
    (logRatio_pos xi sigma v hxi hsigma (huU.trans huv)) hratio

lemma grid_center (xi sigma : ℝ)
    (hxi : Real.exp 1 < xi) (hsigma : 2 ≤ sigma) (j : ℕ) :
    Real.log (Real.log (gridPoint xi sigma j) / Real.log sigma) =
      (j : ℝ) + Real.log (Real.log xi) := by
  have hlogs : Real.log sigma ≠ 0 :=
    (Real.log_pos (one_lt_two.trans_le hsigma)).ne'
  have hlogxi : 0 < Real.log xi :=
    Real.log_pos ((Real.one_lt_exp_iff.mpr zero_lt_one).trans hxi)
  unfold gridPoint
  rw [Real.log_exp]
  have hratio :
      Real.exp (j : ℝ) * Real.log sigma * Real.log xi / Real.log sigma =
        Real.exp (j : ℝ) * Real.log xi := by
    field_simp [hlogs]
  rw [hratio, Real.log_mul (Real.exp_ne_zero _) hlogxi.ne', Real.log_exp]

lemma base_center_pos (xi : ℝ) (hxi : Real.exp 1 < xi) :
    0 < Real.log (Real.log xi) := by
  apply Real.log_pos
  exact (Real.lt_log_iff_exp_lt ((Real.exp_pos 1).trans hxi)).2 hxi

lemma terminal_of_bad
    (epsilon xi sigma x : ℝ) (n d : PosNat)
    (hepsilon : 0 < epsilon) (hepsilon_le : epsilon ≤ 1 / 10)
    (hxi : Real.exp 1 < xi)
    (hsigma : 2 ≤ sigma) (hnx : (n.1 : ℝ) < x)
    (hsmall : 1 / Real.log (Real.log xi) ≤ 0.01 * epsilon)
    (hbad : ¬ Good
      (makeGoodParameters epsilon hepsilon hepsilon_le xi
        ((Real.one_lt_exp_iff.mpr zero_lt_one).trans hxi) sigma hsigma) n d) :
    TerminalGridEvent epsilon xi sigma x d := by
  let q := makeGoodParameters epsilon hepsilon hepsilon_le xi
    ((Real.one_lt_exp_iff.mpr zero_lt_one).trans hxi) sigma hsigma
  have hU : goodU0 q = gridU0 xi sigma := rfl
  have hviolate : ∃ u : ℝ,
      gridU0 xi sigma ≤ u ∧ u < n.1 ∧
        epsilon * Real.log (Real.log u / Real.log sigma) <
          |(omegaBelow d u : ℝ) -
            (1 / 2) * Real.log (Real.log u / Real.log sigma)| := by
    simp only [Good, makeGoodParameters] at hbad
    push_neg at hbad
    rcases hbad with ⟨u, huU, hun, hu⟩
    exact ⟨u, huU, hun, hu⟩
  rcases hviolate with ⟨u, huU, hun, hviol⟩
  have hux : u < x := hun.trans hnx
  have hexists : ∃ k : ℕ, u < gridPoint xi sigma k := by
    have hev : ∀ᶠ k : ℕ in atTop, u < gridPoint xi sigma k :=
      (gridPoint_tendsto xi sigma hxi hsigma).eventually_gt_atTop u
    exact Filter.Eventually.exists hev
  let k := Nat.find hexists
  have hk : u < gridPoint xi sigma k := Nat.find_spec hexists
  have hkpos : 0 < k := by
    apply Nat.pos_of_ne_zero
    intro hk0
    have : u < gridU0 xi sigma := by
      simpa [k, hk0, gridPoint_zero] using hk
    exact (not_lt_of_ge huU) this
  let j := k - 1
  have hkj : k = j + 1 := by
    dsimp [j]
    omega
  have hj_le : gridPoint xi sigma j ≤ u := by
    have hjk : j < k := by dsimp [j]; omega
    exact le_of_not_gt (Nat.find_min hexists hjk)
  have hjx : gridPoint xi sigma j < x := hj_le.trans_lt hux
  let L := fun z : ℝ => Real.log (Real.log z / Real.log sigma)
  have hbase : 0 < Real.log (Real.log xi) := base_center_pos xi hxi
  have hbase_large : 1 ≤ 0.01 * epsilon * Real.log (Real.log xi) := by
    have := mul_le_mul_of_nonneg_right hsmall hbase.le
    field_simp at this
    nlinarith
  have hLj : L (gridPoint xi sigma j) =
      (j : ℝ) + Real.log (Real.log xi) := grid_center xi sigma hxi hsigma j
  have hLk : L (gridPoint xi sigma k) =
      (k : ℝ) + Real.log (Real.log xi) := grid_center xi sigma hxi hsigma k
  have hLjpos : 0 < L (gridPoint xi sigma j) := by
    rw [hLj]
    positivity
  have hLupos : 0 < L u := by
    have hratio := logRatio_pos xi sigma u hxi hsigma huU
    have hbase_le : Real.log xi ≤ Real.log u / Real.log sigma := by
      have hlogs := Real.log_pos (one_lt_two.trans_le hsigma)
      have hu0 : 0 < u := (Real.exp_pos _).trans_le huU
      have hlogU : Real.log (gridU0 xi sigma) ≤ Real.log u :=
        Real.strictMonoOn_log.monotoneOn (Real.exp_pos _) hu0 huU
      unfold gridU0 at hlogU
      rw [Real.log_exp] at hlogU
      rw [le_div_iff₀ hlogs]
      nlinarith
    exact Real.log_pos (lt_of_lt_of_le
      ((Real.lt_log_iff_exp_lt ((Real.exp_pos 1).trans hxi)).2 hxi) hbase_le)
  have hLjLu : L (gridPoint xi sigma j) ≤ L u := by
    apply center_mono xi sigma (gridPoint xi sigma j) u hxi hsigma
    · exact gridPoint_ge_zero xi sigma hxi hsigma j
    · exact hj_le
  have hLuLk : L u ≤ L (gridPoint xi sigma k) :=
    center_mono xi sigma u (gridPoint xi sigma k) hxi hsigma huU hk.le
  have hstep : L (gridPoint xi sigma k) = L (gridPoint xi sigma j) + 1 := by
    rw [hLk, hLj, hkj]
    push_cast
    ring
  have hLj_large : 1 ≤ 0.01 * epsilon * L (gridPoint xi sigma j) := by
    rw [hLj]
    have hj0 : 0 ≤ (j : ℝ) := by positivity
    nlinarith [hbase_large]
  rw [lt_abs] at hviol
  rcases hviol with hupp | hlow
  · by_cases hkx : gridPoint xi sigma k < x
    · left
      refine ⟨k, hkx, Or.inl ?_⟩
      unfold lambdaDeviation
      have homega : (omegaBelow d u : ℝ) ≤ omegaBelow d (gridPoint xi sigma k) := by
        exact_mod_cast omegaBelow_mono hk.le
      have hLkpos : 0 < L (gridPoint xi sigma k) := hLjpos.trans_le (by
        rw [hstep]
        linarith)
      rw [hstep] at hLuLk
      rw [lt_div_iff₀ hLkpos]
      nlinarith [hLj_large]
    · right
      have hxk : x ≤ gridPoint xi sigma k := le_of_not_gt hkx
      have hUx : gridU0 xi sigma ≤ x := huU.trans hux.le
      have hLux : L u ≤ L x := center_mono xi sigma u x hxi hsigma huU hux.le
      have hLxk : L x ≤ L (gridPoint xi sigma k) :=
        center_mono xi sigma x (gridPoint xi sigma k) hxi hsigma hUx hxk
      have hLxpos : 0 < L x := hLupos.trans_le hLux
      have homega : (omegaBelow d u : ℝ) ≤ omegaBelow d x := by
        exact_mod_cast omegaBelow_mono hux.le
      unfold lambdaDeviation
      rw [hstep] at hLuLk
      rw [lt_div_iff₀ hLxpos]
      nlinarith [hLj_large]
  · left
    refine ⟨j, hjx, Or.inr ?_⟩
    unfold lambdaDeviation
    have homega : (omegaBelow d (gridPoint xi sigma j) : ℝ) ≤ omegaBelow d u := by
      exact_mod_cast omegaBelow_mono hj_le
    rw [hstep] at hLuLk
    have hepsLjLu := mul_le_mul_of_nonneg_left hLjLu hepsilon.le
    have hhalf := mul_le_mul_of_nonneg_left hLuLk (by norm_num : (0 : ℝ) ≤ 1 / 2)
    rw [div_lt_iff₀ hLjpos]
    nlinarith [hLj_large, hepsLjLu, hhalf]

lemma roughDensity_nonneg (theta : ℝ) : 0 ≤ roughDensity theta := by
  unfold roughDensity
  apply Finset.prod_nonneg
  intro p hp
  have hpPrime := (Finset.mem_filter.mp hp).2
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hpPrime.pos
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hpPrime.one_lt.le
  exact sub_nonneg.mpr ((div_le_one hp0).2 hp1)

lemma bad_count_le_terminal
    (epsilon xi sigma x : ℝ) (n : PosNat)
    (hepsilon : 0 < epsilon) (hepsilon_le : epsilon ≤ 1 / 10)
    (hxi : Real.exp 1 < xi) (hsigma : 2 ≤ sigma)
    (hnx : (n.1 : ℝ) < x)
    (hsmall : 1 / Real.log (Real.log xi) ≤ 0.01 * epsilon) :
    badDivisorCount
        (makeGoodParameters epsilon hepsilon hepsilon_le xi
          ((Real.one_lt_exp_iff.mpr zero_lt_one).trans hxi) sigma hsigma) n ≤
      terminalGridCount epsilon xi sigma x n := by
  classical
  unfold badDivisorCount terminalGridCount
  apply Finset.card_le_card
  intro d hd
  simp only [Finset.mem_filter] at hd ⊢
  rcases hd with ⟨hdD, hrough, hbad⟩
  refine ⟨hdD, hrough, ?_⟩
  by_cases hdpos : 0 < d
  · rw [dif_pos hdpos] at hbad ⊢
    exact terminal_of_bad epsilon xi sigma x n ⟨d, hdpos⟩
      hepsilon hepsilon_le hxi hsigma hnx hsmall hbad
  · rw [dif_neg hdpos] at hbad
    exact False.elim hbad

lemma bad_mass_le_grid
    (epsilon xi sigma theta x : ℝ)
    (hepsilon : 0 < epsilon) (hepsilon_le : epsilon ≤ 1 / 10)
    (hxi : Real.exp 1 < xi) (htheta : 2 ≤ theta) (hsigma : theta ≤ sigma)
    (hsmall : 1 / Real.log (Real.log xi) ≤ 0.01 * epsilon) :
    badDivisorMass
        (makeGoodParameters epsilon hepsilon hepsilon_le xi
          ((Real.one_lt_exp_iff.mpr zero_lt_one).trans hxi) sigma
            (htheta.trans hsigma)) theta x ≤
      gridExceptionalMass epsilon xi sigma theta x := by
  classical
  unfold badDivisorMass gridExceptionalMass
  apply Finset.sum_le_sum
  intro n hnmem
  have hnx : (n : ℝ) < x := (Finset.mem_filter.mp hnmem).2.2
  have hn : 0 < n := (Finset.mem_filter.mp hnmem).2.1
  rw [dif_pos hn, dif_pos hn]
  apply mul_le_mul_of_nonneg_left
  · exact_mod_cast bad_count_le_terminal epsilon xi sigma x ⟨n, hn⟩
      hepsilon hepsilon_le hxi (htheta.trans hsigma) hnx hsmall
  · exact div_nonneg (by positivity) (by positivity)

theorem p018
    (hEXT : EXT001Statement) (h007 : P007Statement) (h008 : P008Statement.{0}) :
    P018Statement := by
  intro epsilon hepsilon hepsilon_le
  rcases Erdos448.Stage7.ROOT02.Grid.p016 hEXT h007 h008
      epsilon hepsilon hepsilon_le with ⟨g⟩
  let q := makeGridParameters epsilon hepsilon hepsilon_le g.Cgrid g.Cgrid_pos
  rcases Erdos448.Stage7.ROOT02.Threshold.p017 q with ⟨t⟩
  refine ⟨{
    Cgrid := g.Cgrid
    Cgrid_pos := g.Cgrid_pos
    grid_bound := g.grid_bound
    Xi0 := t.Xi0
    Xi0_gt_one := t.Xi0_gt_one
    threshold_spec := t.threshold_spec
    all_u_bound := ?_
  }⟩
  intro xi sigma theta x hxi htheta hsigma hx
  have hthreshold := t.threshold_spec.2 xi hxi
  rcases hthreshold with ⟨hxi_exp, hsmall, hscale⟩
  have hmass := bad_mass_le_grid epsilon xi sigma theta x
    hepsilon hepsilon_le hxi_exp htheta hsigma hsmall
  have hgrid := g.grid_bound xi sigma theta x hxi_exp htheta hsigma hx
  calc
    badDivisorMass
        (makeGoodParameters epsilon hepsilon hepsilon_le xi
          (lt_of_lt_of_le t.Xi0_gt_one hxi) sigma (le_trans htheta hsigma))
        theta x ≤
      gridExceptionalMass epsilon xi sigma theta x := by
        simpa only using hmass
    _ ≤ g.Cgrid * x * roughDensity theta *
        (Real.log xi).rpow (-0.901 * epsilon ^ 2) := hgrid
    _ = ((1 / 10 : ℝ) * x * roughDensity theta) *
        (10 * g.Cgrid *
          (Real.log xi).rpow (-0.901 * epsilon ^ 2)) := by ring
    _ ≤ ((1 / 10 : ℝ) * x * roughDensity theta) *
        (Real.log xi).rpow (-0.9 * epsilon ^ 2) := by
      apply mul_le_mul_of_nonneg_left hscale
      exact mul_nonneg
        (mul_nonneg (by norm_num) (le_of_lt (Real.exp_pos _ |>.trans hx)))
        (roughDensity_nonneg theta)
    _ = (1 / 10 : ℝ) * x * roughDensity theta *
        (Real.log xi).rpow (-0.9 * epsilon ^ 2) := by ring

end

end Erdos448.Stage7.ROOT02.AllU
