module

public import Erdos745.WrapUp.Contracts

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local simp] Pi.div_def Pi.mul_def Pi.add_def Pi.sub_def Pi.neg_def Pi.inv_def Function.comp_def Pi.pow_def Pi.smul_def Real.rpow_eq_pow

set_option maxHeartbeats 5000000

@[expose] public section


/-!
The rooted labelled-tree series.  The finite coefficient identity is proved
from Abel's binomial identity; the resulting differential equation identifies
the sum with the small real branch of `t * exp (-t) = z`.
-/

namespace Erdos745.WrapUp.Proofs.Internal.W05_SUMS_TreeSeries

open Erdos745.WrapUp
open Filter Set
open scoped BigOperators Topology ENNReal

noncomputable section

private def abel (n : ℕ) (x y z : ℝ) : ℝ :=
  y ^ n + ∑ j ∈ Finset.range n,
    (n.choose (j + 1) : ℝ) * x * (x + (j + 1 : ℝ) * z) ^ j *
      (y - (j + 1 : ℝ) * z) ^ (n - j - 1)

private lemma abelTerm_hasDerivAt (n j : ℕ) (x y z : ℝ) :
    HasDerivAt
      (fun w : ℝ =>
        (n.choose (j + 1) : ℝ) * w * (w + (j + 1 : ℝ) * z) ^ j *
          (y - (j + 1 : ℝ) * z) ^ (n - j - 1))
      ((n.choose (j + 1) : ℝ) *
        ((x + (j + 1 : ℝ) * z) ^ j +
          x * (j : ℝ) * (x + (j + 1 : ℝ) * z) ^ (j - 1)) *
        (y - (j + 1 : ℝ) * z) ^ (n - j - 1)) x := by
  have hp : HasDerivAt (fun w : ℝ => (w + (j + 1 : ℝ) * z) ^ j)
      ((j : ℝ) * (x + (j + 1 : ℝ) * z) ^ (j - 1)) x := by
    simpa using! ((hasDerivAt_id x).add_const ((j + 1 : ℝ) * z)).pow j
  have hm := (hasDerivAt_id x).mul hp
  have hc := (hm.const_mul (n.choose (j + 1) : ℝ)).mul_const
    ((y - (j + 1 : ℝ) * z) ^ (n - j - 1))
  convert hc using 1
  · funext w
    dsimp [id]
    ring
  · dsimp [id]
    ring

private lemma abel_hasDerivAt_raw (n : ℕ) (x y z : ℝ) :
    HasDerivAt (fun w : ℝ => abel n w y z)
      (∑ j ∈ Finset.range n,
        (n.choose (j + 1) : ℝ) *
          ((x + (j + 1 : ℝ) * z) ^ j +
            x * (j : ℝ) * (x + (j + 1 : ℝ) * z) ^ (j - 1)) *
          (y - (j + 1 : ℝ) * z) ^ (n - j - 1)) x := by
  have hs := fun j (_hj : j ∈ Finset.range n) =>
    abelTerm_hasDerivAt n j x y z
  have hsum := HasDerivAt.sum (u := Finset.range n) hs
  convert (hasDerivAt_const x (y ^ n)).add hsum using 1
  · funext w
    simp only [abel, Pi.add_apply, Finset.sum_apply, add_left_inj]
  · simp

private lemma abel_succ_term (n i : ℕ) (hi : i < n) (x y z : ℝ) :
    ((n + 1).choose ((i + 1) + 1) : ℝ) *
        ((x + ((i + 1) + 1 : ℕ) * z) ^ (i + 1) +
          x * ((i + 1 : ℕ) : ℝ) *
            (x + ((i + 1) + 1 : ℕ) * z) ^ ((i + 1) - 1)) *
        (y - (((i + 1) + 1 : ℕ) : ℝ) * z) ^
          ((n + 1) - (i + 1) - 1) =
      (n + 1 : ℝ) * ((n.choose (i + 1) : ℝ) * (x + z) *
        ((x + z) + (i + 1 : ℝ) * z) ^ i *
        ((y - z) - (i + 1 : ℝ) * z) ^ (n - i - 1)) := by
  have hc := Nat.add_one_mul_choose_eq n (i + 1)
  have hcoef : (((n + 1).choose ((i + 1) + 1) : ℕ) : ℝ) * (i + 2 : ℝ) =
      (n + 1 : ℝ) * (n.choose (i + 1) : ℝ) := by
    exact_mod_cast hc.symm
  rw [show (i + 1) - 1 = i by omega,
    show (n + 1) - (i + 1) - 1 = n - i - 1 by omega]
  norm_num only [Nat.cast_add, Nat.cast_one]
  calc
    _ = ((((n + 1).choose ((i + 1) + 1) : ℕ) : ℝ) * (i + 2 : ℝ)) *
        (x + z) * (x + z + (i + 1 : ℝ) * z) ^ i *
        (y - z - (i + 1 : ℝ) * z) ^ (n - i - 1) := by ring
    _ = _ := by rw [hcoef]; ring

private lemma abel_derivative_succ (n : ℕ) (x y z : ℝ) :
    (∑ j ∈ Finset.range (n + 1),
      ((n + 1).choose (j + 1) : ℝ) *
        ((x + (j + 1 : ℝ) * z) ^ j +
          x * (j : ℝ) * (x + (j + 1 : ℝ) * z) ^ (j - 1)) *
        (y - (j + 1 : ℝ) * z) ^ ((n + 1) - j - 1)) =
      (n + 1 : ℝ) * abel n (x + z) (y - z) z := by
  rw [Finset.sum_range_succ']
  have hsum :
      (∑ i ∈ Finset.range n,
        ((n + 1).choose ((i + 1) + 1) : ℝ) *
          ((x + (((i + 1 : ℕ) : ℝ) + 1) * z) ^ (i + 1) +
            x * ((i + 1 : ℕ) : ℝ) *
              (x + (((i + 1 : ℕ) : ℝ) + 1) * z) ^ ((i + 1) - 1)) *
          (y - (((i + 1 : ℕ) : ℝ) + 1) * z) ^
            ((n + 1) - (i + 1) - 1)) =
      ∑ i ∈ Finset.range n, (n + 1 : ℝ) *
        ((n.choose (i + 1) : ℝ) * (x + z) *
          ((x + z) + (i + 1 : ℝ) * z) ^ i *
          ((y - z) - (i + 1 : ℝ) * z) ^ (n - i - 1)) := by
    apply Finset.sum_congr rfl
    intro i hi
    simpa only [Nat.cast_add, Nat.cast_one] using!
      abel_succ_term n i (Finset.mem_range.mp hi) x y z
  rw [hsum]
  simp only [Nat.cast_zero, zero_add, Nat.cast_one, Nat.choose_one_right,
    Nat.cast_add, pow_zero, zero_mul, add_zero, Nat.add_sub_cancel, Nat.sub_zero,
    mul_zero, one_mul]
  unfold abel
  rw [← Finset.mul_sum]
  ring

private lemma abel_eq_add_pow (n : ℕ) (x y z : ℝ) :
    abel n x y z = (x + y) ^ n := by
  induction n generalizing x y z with
  | zero => simp [abel]
  | succ n ih =>
      have hA : ∀ w : ℝ,
          HasDerivAt (fun q : ℝ => abel (n + 1) q y z)
            ((n + 1 : ℝ) * (w + y) ^ n) w := by
        intro w
        apply (abel_hasDerivAt_raw (n + 1) w y z).congr_deriv
        rw [abel_derivative_succ, ih]
        ring
      have hB : ∀ w : ℝ,
          HasDerivAt (fun q : ℝ => (q + y) ^ (n + 1))
            ((n + 1 : ℝ) * (w + y) ^ n) w := by
        intro w
        simpa [mul_comm] using! ((hasDerivAt_id w).add_const y).pow (n + 1)
      let F : ℝ → ℝ := fun w => abel (n + 1) w y z - (w + y) ^ (n + 1)
      have hF : ∀ w : ℝ, HasDerivAt F 0 w := by
        intro w
        dsimp [F]
        convert (hA w).sub (hB w) using 1 <;> ring
      have hdiff : DifferentiableOn ℝ F Set.univ := by
        intro w _
        exact (hF w).differentiableAt.differentiableWithinAt
      have hzero : Set.EqOn (deriv F) 0 Set.univ := by
        intro w _
        exact (hF w).deriv
      have hc := isOpen_univ.is_const_of_deriv_eq_zero
        isPreconnected_univ hdiff hzero (Set.mem_univ x) (Set.mem_univ 0)
      have hF0 : F 0 = 0 := by simp [F, abel]
      dsimp [F] at hc
      linarith

private lemma cayley_convolution (n : ℕ) :
    (∑ j ∈ Finset.range n, (n.choose (j + 1) : ℝ) *
      (j + 1 : ℝ) ^ j * (((n - j : ℕ) : ℝ)) ^ (n - j - 1)) =
      (n : ℝ) * (n + 1 : ℝ) ^ (n - 1) := by
  have hA := abel_hasDerivAt_raw n 0 (n + 1 : ℝ) 1
  have hB : HasDerivAt (fun w : ℝ => (w + (n + 1 : ℝ)) ^ n)
      ((n : ℝ) * (n + 1 : ℝ) ^ (n - 1)) 0 := by
    simpa using! ((hasDerivAt_id (0 : ℝ)).add_const (n + 1 : ℝ)).pow n
  have hfun : (fun w : ℝ => abel n w (n + 1 : ℝ) 1) =
      (fun w : ℝ => (w + (n + 1 : ℝ)) ^ n) := by
    funext w
    exact abel_eq_add_pow n w (n + 1 : ℝ) 1
  rw [hfun] at hA
  have hd := hA.unique hB
  simp only [zero_add, zero_mul, add_zero, mul_one] at hd
  calc
    _ = ∑ j ∈ Finset.range n, (n.choose (j + 1) : ℝ) *
        (j + 1 : ℝ) ^ j *
        ((n : ℝ) + 1 - ((j : ℝ) + 1)) ^ (n - j - 1) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hjn : j ≤ n := (Finset.mem_range.mp hj).le
      rw [Nat.cast_sub hjn]
      ring
    _ = _ := hd

private def treeCoeff (k : ℕ) : ℝ :=
  if k = 0 then 0 else (k : ℝ) ^ (k - 1) / (k.factorial : ℝ)

private def derivCoeff (n : ℕ) : ℝ :=
  (n + 1 : ℝ) ^ n / (n.factorial : ℝ)

private lemma treeCoeff_nonneg (k : ℕ) : 0 ≤ treeCoeff k := by
  simp only [treeCoeff]
  split_ifs
  · exact le_rfl
  · positivity

private lemma treeCoeff_succ (n : ℕ) :
    treeCoeff (n + 1) =
      (n + 1 : ℝ) ^ n / ((n + 1).factorial : ℝ) := by
  simp [treeCoeff]

private lemma convolution_term (n j : ℕ) (hj : j < n) :
    treeCoeff (j + 1) * derivCoeff (n - (j + 1)) =
      (n.choose (j + 1) : ℝ) * (j + 1 : ℝ) ^ j *
        (((n - j : ℕ) : ℝ) ^ (n - j - 1)) / (n.factorial : ℝ) := by
  rw [treeCoeff_succ]
  unfold derivCoeff
  have hsub : n - (j + 1) + 1 = n - j := by omega
  have hcast : ((n - (j + 1) : ℕ) : ℝ) + 1 = ((n - j : ℕ) : ℝ) := by
    exact_mod_cast hsub
  have hfac : n - (j + 1) = n - j - 1 := by omega
  rw [hcast, hfac]
  rw [Nat.cast_choose ℝ (show j + 1 ≤ n by omega)]
  have h1 : (((j + 1).factorial : ℕ) : ℝ) ≠ 0 := by positivity
  have h2 : (((n - j - 1).factorial : ℕ) : ℝ) ≠ 0 := by positivity
  have hn : ((n.factorial : ℕ) : ℝ) ≠ 0 := by positivity
  rw [show n - (j + 1) = n - j - 1 by omega]
  field_simp

private lemma convolution_sum (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1),
      treeCoeff k * derivCoeff (n - k)) =
      (n : ℝ) * (n + 1 : ℝ) ^ (n - 1) / (n.factorial : ℝ) := by
  rw [Finset.sum_range_succ']
  rw [show treeCoeff 0 * derivCoeff (n - 0) = 0 by simp [treeCoeff], add_zero]
  rw [Finset.sum_congr rfl (fun j hj =>
    convolution_term n j (Finset.mem_range.mp hj))]
  rw [← Finset.sum_div, cayley_convolution]

private lemma coefficient_ode (n : ℕ) :
    derivCoeff n -
      (∑ k ∈ Finset.range (n + 1),
        treeCoeff k * derivCoeff (n - k)) = treeCoeff (n + 1) := by
  rw [convolution_sum]
  cases n with
  | zero => simp [derivCoeff, treeCoeff]
  | succ m =>
      rw [treeCoeff_succ]
      unfold derivCoeff
      simp only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel,
        Nat.factorial_succ]
      have hf : ((m.factorial : ℕ) : ℝ) ≠ 0 := by positivity
      field_simp
      push_cast
      ring

private lemma treeCoeff_ratio (n : ℕ) (hn : 0 < n) :
    ‖treeCoeff (n + 1)‖ / ‖treeCoeff n‖ =
      (1 + 1 / (n : ℝ)) ^ (n - 1) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hfn : ((n.factorial : ℕ) : ℝ) ≠ 0 := by positivity
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnR
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg, abs_of_nonneg]
  · simp only [treeCoeff, if_neg (Nat.succ_ne_zero n),
      if_neg (Nat.ne_of_gt hn)]
    rw [Nat.factorial_succ]
    push_cast
    rw [show 1 + 1 / (n : ℝ) = (n + 1) / n by field_simp]
    rw [div_pow]
    field_simp
    rw [show n = (n - 1) + 1 by omega, pow_succ]
    rw [show n - 1 + 1 - 1 = n - 1 by omega]
    ring
  · simp [treeCoeff]
    positivity
  · simp [treeCoeff]
    positivity

private lemma treeCoeff_ratio_tendsto :
    Tendsto (fun n : ℕ => ‖treeCoeff (n + 1)‖ / ‖treeCoeff n‖)
      atTop (𝓝 (Real.exp 1)) := by
  have hp := Real.tendsto_one_add_div_pow_exp 1
  have hd : Tendsto (fun n : ℕ => 1 + 1 / (n : ℝ)) atTop (𝓝 1) := by
    simpa using! (tendsto_const_nhds.add
      (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)))
  have hq : Tendsto (fun n : ℕ => (1 + 1 / (n : ℝ)) ^ (n - 1))
      atTop (𝓝 (Real.exp 1)) := by
    have hquot := hp.div hd one_ne_zero
    have hev : ((fun n : ℕ => (1 + 1 / (n : ℝ)) ^ n) /
        (fun n : ℕ => 1 + 1 / (n : ℝ))) =ᶠ[atTop]
        (fun n : ℕ => (1 + 1 / (n : ℝ)) ^ (n - 1)) := by
      filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
      change (1 + 1 / (n : ℝ)) ^ n / (1 + 1 / (n : ℝ)) =
        (1 + 1 / (n : ℝ)) ^ (n - 1)
      have hb : 1 + 1 / (n : ℝ) ≠ 0 := by positivity
      rw [show n = (n - 1) + 1 by omega, pow_succ]
      field_simp
      rw [show n - 1 + 1 - 1 = n - 1 by omega]
    simpa using! hquot.congr' hev
  apply hq.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  exact (treeCoeff_ratio n hn).symm

private def treeSeries : FormalMultilinearSeries ℝ ℝ ℝ :=
  FormalMultilinearSeries.ofScalars ℝ treeCoeff

private def treeFun (z : ℝ) : ℝ := treeSeries.sum z

private def convergenceRadius : NNReal :=
  NNReal.mk (Real.exp (-1)) ((Real.exp_pos _).le)

private lemma convergenceRadius_le_radius :
    (convergenceRadius : ENNReal) ≤ treeSeries.radius := by
  have hrho : convergenceRadius ≠ 0 := by
    intro h
    have hv := congrArg (fun q : NNReal => (q : ℝ)) h
    change Real.exp (-1) = 0 at hv
    exact (Real.exp_ne_zero (-1)) hv
  have hinv : (↑(convergenceRadius⁻¹) : ℝ) = Real.exp 1 := by
    change (Real.exp (-1))⁻¹ = Real.exp 1
    rw [Real.exp_neg, inv_inv]
  have hlim' : Tendsto
      (fun n : ℕ => ‖treeCoeff (n + 1)‖ / ‖treeCoeff n‖)
      atTop (𝓝 (↑(convergenceRadius⁻¹) : ℝ)) := by
    simpa [hinv] using! treeCoeff_ratio_tendsto
  have h := FormalMultilinearSeries.inv_le_ofScalars_radius_of_tendsto
    ℝ treeCoeff (inv_ne_zero hrho) hlim'
  simpa [treeSeries] using! h

private lemma treeSeries_radius_pos : 0 < treeSeries.radius := by
  have hr : (0 : NNReal) < convergenceRadius := by
    change 0 < Real.exp (-1)
    exact Real.exp_pos (-1)
  have h : (0 : ENNReal) < (convergenceRadius : ENNReal) :=
    ENNReal.coe_pos.mpr hr
  exact lt_of_lt_of_le h convergenceRadius_le_radius

private lemma mem_treeSeries_ball {z : ℝ} (hz : 0 < z)
    (hzr : z < Real.exp (-1)) :
    z ∈ Metric.eball 0 treeSeries.radius := by
  apply lt_of_lt_of_le ?_ convergenceRadius_le_radius
  rw [edist_dist, ENNReal.ofReal_lt_coe_iff dist_nonneg]
  simpa [convergenceRadius, Real.dist_eq, abs_of_pos hz] using! hzr

private lemma hasSum_treeCoeff {z : ℝ}
    (hzmem : z ∈ Metric.eball 0 treeSeries.radius) :
    HasSum (fun n => treeCoeff n * z ^ n) (treeFun z) := by
  convert! treeSeries.hasSum hzmem using 1
  funext n
  rw [FormalMultilinearSeries.apply_eq_pow_smul_coeff]
  simp [treeSeries, FormalMultilinearSeries.coeff_ofScalars, smul_eq_mul]
  ring

private lemma hasSum_rootedTerm {z : ℝ}
    (hzmem : z ∈ Metric.eball 0 treeSeries.radius) :
    HasSum (rootedTerm z) (treeFun z) := by
  change HasSum (fun k : ℕ => if k = 0 then 0 else
    (k : ℝ) ^ (k - 1) * z ^ k / (k.factorial : ℝ)) (treeFun z)
  convert! hasSum_treeCoeff hzmem using 1
  funext k
  simp only [treeCoeff]
  split_ifs <;> ring

private lemma derivCoeff_eq (n : ℕ) :
    (n + 1 : ℝ) * treeCoeff (n + 1) = derivCoeff n := by
  simp [treeCoeff, derivCoeff, Nat.factorial_succ]
  have h : ((n.factorial : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp

private lemma hasSum_derivative {z : ℝ}
    (hzmem : z ∈ Metric.eball 0 treeSeries.radius) :
    HasSum (fun n => derivCoeff n * z ^ n) (deriv treeFun z) := by
  have hps := treeSeries.hasFPowerSeriesOnBall treeSeries_radius_pos
  have hfd := hps.hasFDerivAt hzmem
  have hw := hps.hasFPowerSeriesWithinOnBall (s := Set.univ)
  have hs := hw.hasSum_derivSeries_of_hasFDerivWithinAt hzmem (by simp)
    hfd.hasFDerivWithinAt
    (by simpa using! (uniqueDiffOn_univ : UniqueDiffOn ℝ (Set.univ : Set ℝ)))
  have hm := hs.map ((ContinuousLinearMap.apply ℝ ℝ) (1 : ℝ))
    ((ContinuousLinearMap.apply ℝ ℝ) (1 : ℝ)).continuous
  have hderiv : deriv treeFun z =
      ((continuousMultilinearCurryFin1 ℝ ℝ ℝ)
        (treeSeries.changeOrigin (z - 0) 1)) 1 := by
    simpa [treeFun] using! hfd.hasDerivAt.deriv
  rw [hderiv]
  convert! hm using 1
  funext n
  dsimp [Function.comp_apply]
  rw [FormalMultilinearSeries.apply_eq_pow_smul_coeff]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, sub_zero]
  rw [FormalMultilinearSeries.derivSeries_coeff_one]
  simp only [treeSeries, FormalMultilinearSeries.coeff_ofScalars,
    nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
  rw [derivCoeff_eq]
  ring

private lemma ode_from_series {z T D : ℝ} (hz : z ≠ 0)
    (hT : HasSum (fun n => treeCoeff n * z ^ n) T)
    (hD : HasSum (fun n => derivCoeff n * z ^ n) D) :
    (1 - T) * D = T / z := by
  let f : ℕ → ℝ := fun n => treeCoeff n * z ^ n
  let g : ℕ → ℝ := fun n => derivCoeff n * z ^ n
  have hconv0 := hasSum_sum_range_mul_of_summable_norm
    hT.summable.norm hD.summable.norm
  have hconv : HasSum
      (fun n => (∑ k ∈ Finset.range (n + 1),
        treeCoeff k * derivCoeff (n - k)) * z ^ n) (T * D) := by
    have htT : ∑' n, f n = T := hT.tsum_eq
    have htD : ∑' n, g n = D := hD.tsum_eq
    rw [htT, htD] at hconv0
    convert hconv0 using 1
    funext n
    try dsimp [f, g]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k hk
    have hkn : k ≤ n := by
      have := Finset.mem_range.mp hk
      omega
    have hp : z ^ n = z ^ k * z ^ (n - k) := by
      rw [← pow_add, Nat.add_sub_of_le hkn]
    rw [hp]
    ring
  have hdiff := hD.sub hconv
  have hnext : HasSum (fun n => treeCoeff (n + 1) * z ^ n)
      ((1 - T) * D) := by
    convert hdiff using 1
    · funext n
      rw [← coefficient_ode n]
      ring
    · ring
  have hshift0 :=
    (hasSum_nat_add_iff' (f := fun n => treeCoeff n * z ^ n) 1).2 hT
  have hshift : HasSum (fun n => treeCoeff (n + 1) * z ^ (n + 1)) T := by
    simpa [treeCoeff] using! hshift0
  have hscaled := hshift.mul_left z⁻¹
  have hnext' : HasSum (fun n => treeCoeff (n + 1) * z ^ n) (T / z) := by
    convert hscaled using 1
    · funext n
      field_simp
      rw [pow_succ]
      ring
    · field_simp
  exact hnext.unique hnext'

private def normalizedTree (z : ℝ) : ℝ :=
  treeFun z * Real.exp (-treeFun z) / z

private lemma treeFun_zero : treeFun 0 = 0 := by
  have hz0 : (0 : ℝ) ∈ Metric.eball 0 treeSeries.radius :=
    Metric.mem_eball_self treeSeries_radius_pos
  have h0 := hasSum_treeCoeff hz0
  have hzero : HasSum (fun _ : ℕ => (0 : ℝ)) 0 := hasSum_zero
  have hzero' : HasSum (fun n => treeCoeff n * (0 : ℝ) ^ n) 0 := by
    convert hzero using 1
    funext n
    cases n <;> simp [treeCoeff]
  exact h0.unique hzero'

private lemma treeFun_hasDerivAt_zero : HasDerivAt treeFun 1 0 := by
  have hz0 : (0 : ℝ) ∈ Metric.eball 0 treeSeries.radius :=
    Metric.mem_eball_self treeSeries_radius_pos
  have hps := treeSeries.hasFPowerSeriesOnBall treeSeries_radius_pos
  have hraw := (hps.hasFDerivAt hz0).hasDerivAt
  have hd0 := hasSum_derivative hz0
  have hsingle : HasSum (fun n : ℕ => if n = 0 then (1 : ℝ) else 0) 1 :=
    hasSum_ite_eq 0 1
  have hone : HasSum (fun n => derivCoeff n * (0 : ℝ) ^ n) 1 := by
    convert! hsingle using 1
    funext n
    cases n <;> simp [derivCoeff]
  have hder : deriv treeFun 0 = 1 := hd0.unique hone
  convert! hraw using 1
  · exact hder.symm.trans (by simpa [treeFun] using! hraw.deriv)
  · simp

private lemma treeFun_hasDerivAt {z : ℝ}
    (hzmem : z ∈ Metric.eball 0 treeSeries.radius) :
    HasDerivAt treeFun (deriv treeFun z) z := by
  have hps := treeSeries.hasFPowerSeriesOnBall treeSeries_radius_pos
  have hraw := (hps.hasFDerivAt hzmem).hasDerivAt
  convert! hraw using 1
  · simpa [treeFun] using! hraw.deriv
  · simp

private lemma normalizedTree_hasDerivAt_zero {z : ℝ}
    (hz : 0 < z) (hzr : z < Real.exp (-1)) :
    HasDerivAt normalizedTree 0 z := by
  have hm := mem_treeSeries_ball hz hzr
  have hF := treeFun_hasDerivAt hm
  have ho := ode_from_series (ne_of_gt hz)
    (hasSum_treeCoeff hm) (hasSum_derivative hm)
  have hode' : (1 - treeFun z) * deriv treeFun z * z = treeFun z := by
    field_simp at ho
    exact ho
  have he := hF.neg.exp
  have hn := hF.mul he
  have hq := hn.div (hasDerivAt_id z) (ne_of_gt hz)
  apply hq.congr_deriv
  dsimp [normalizedTree] at hq ⊢
  field_simp
  linear_combination Real.exp (-treeFun z) * hode'

private lemma normalizedTree_tendsto_one :
    Tendsto normalizedTree (nhdsWithin 0 (Ioi 0)) (𝓝 1) := by
  have hslope0 := treeFun_hasDerivAt_zero.tendsto_slope_zero_right
  have hslope : Tendsto (fun t : ℝ => treeFun t / t)
      (nhdsWithin 0 (Ioi 0)) (𝓝 1) := by
    convert! hslope0 using 1
    funext t
    rw [zero_add, treeFun_zero, sub_zero]
    simp [smul_eq_mul, div_eq_mul_inv, mul_comm]
  have hfun : Tendsto treeFun (nhdsWithin 0 (Ioi 0)) (𝓝 0) := by
    simpa [treeFun_zero] using!
      treeFun_hasDerivAt_zero.continuousAt.tendsto.mono_left inf_le_left
  have hexp : Tendsto (fun t : ℝ => Real.exp (-treeFun t))
      (nhdsWithin 0 (Ioi 0)) (𝓝 1) := by
    simpa using! Real.continuous_exp.continuousAt.tendsto.comp hfun.neg
  have hp := hslope.mul hexp
  simpa only [one_mul] using! hp.congr' (Eventually.of_forall fun t => by
    dsimp [normalizedTree]
    ring)

private lemma constant_limit_one {V : ℝ → ℝ} {r : ℝ} (hr : 0 < r)
    (hderiv : ∀ z : ℝ, 0 < z → z < r → HasDerivAt V 0 z)
    (hlim : Tendsto V (nhdsWithin 0 (Ioi 0)) (𝓝 1)) :
    ∀ z : ℝ, 0 < z → z < r → V z = 1 := by
  have hdiff : DifferentiableOn ℝ V (Ioo 0 r) := by
    intro z hz
    exact (hderiv z hz.1 hz.2).differentiableAt.differentiableWithinAt
  have hzero : Set.EqOn (deriv V) 0 (Ioo 0 r) := by
    intro z hz
    exact (hderiv z hz.1 hz.2).deriv
  have hconst : ∀ x ∈ Ioo (0 : ℝ) r, ∀ y ∈ Ioo 0 r, V x = V y := by
    intro x hx y hy
    exact isOpen_Ioo.is_const_of_deriv_eq_zero
      (convex_Ioo 0 r).isPreconnected hdiff hzero hx hy
  intro z hz hz'
  have hIio : ∀ᶠ w in nhdsWithin 0 (Ioi 0), w < r :=
    Filter.Eventually.filter_mono inf_le_left (Iio_mem_nhds hr)
  have hev : V =ᶠ[nhdsWithin 0 (Ioi 0)] fun _ => V z := by
    filter_upwards [hIio, self_mem_nhdsWithin] with w hwr hw0
    exact hconst w ⟨hw0, hwr⟩ z ⟨hz, hz'⟩
  have hc : Tendsto V (nhdsWithin 0 (Ioi 0)) (𝓝 (V z)) :=
    tendsto_const_nhds.congr' hev.symm
  exact tendsto_nhds_unique hc hlim

private lemma treeFun_fixed {z : ℝ} (hz : 0 < z)
    (hzr : z < Real.exp (-1)) :
    treeFun z * Real.exp (-treeFun z) = z := by
  have hn := constant_limit_one (Real.exp_pos (-1))
    (fun w hw hwr => normalizedTree_hasDerivAt_zero hw hwr)
    normalizedTree_tendsto_one z hz hzr
  dsimp [normalizedTree] at hn
  field_simp [ne_of_gt hz] at hn
  exact hn

private lemma treeFun_pos {z : ℝ} (hz : 0 < z)
    (hzr : z < Real.exp (-1)) : 0 < treeFun z := by
  have hsum := hasSum_treeCoeff (mem_treeSeries_ball hz hzr)
  have hlt := lt_hasSum hsum 0
    (fun j _ => mul_nonneg (treeCoeff_nonneg j) (by positivity))
    1 (by norm_num) (by simpa [treeCoeff] using! hz)
  simpa [treeCoeff] using! hlt

private lemma mem_treeSeries_ball_nonneg {z : ℝ} (hz : 0 ≤ z)
    (hzr : z < Real.exp (-1)) :
    z ∈ Metric.eball 0 treeSeries.radius := by
  rcases hz.eq_or_lt with rfl | hz'
  · exact Metric.mem_eball_self treeSeries_radius_pos
  · exact mem_treeSeries_ball hz' hzr

private lemma treeFun_lt_one {z : ℝ} (hz : 0 < z)
    (hzr : z < Real.exp (-1)) : treeFun z < 1 := by
  have hcont : ContinuousOn treeFun (Icc 0 z) := by
    apply (treeSeries.hasFPowerSeriesOnBall treeSeries_radius_pos).continuousOn.mono
    intro w hw
    exact mem_treeSeries_ball_nonneg hw.1 (lt_of_le_of_lt hw.2 hzr)
  by_contra hn
  have hone : (1 : ℝ) ∈ Icc (treeFun 0) (treeFun z) := by
    constructor
    · rw [treeFun_zero]
      norm_num
    · exact le_of_not_gt hn
  obtain ⟨w, hw, hwval⟩ := intermediate_value_Icc hz.le hcont hone
  have hwpos : 0 < w := by
    exact lt_of_le_of_ne hw.1 (fun h => by
      subst w
      simp [treeFun_zero] at hwval)
  have hwr : w < Real.exp (-1) := lt_of_le_of_lt hw.2 hzr
  have heq := treeFun_fixed hwpos hwr
  rw [hwval] at heq
  norm_num at heq
  linarith

private lemma strictMonoOn_unit :
    StrictMonoOn (fun x : ℝ => x * Real.exp (-x)) (Icc 0 1) := by
  apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc 0 1)
  · fun_prop
  · intro x hx
    have h := (hasDerivAt_id x).mul
      ((Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_id x).neg)
    have hd : HasDerivAt (fun y : ℝ => y * Real.exp (-y))
        (Real.exp (-x) * (1 - x)) x := by
      convert h using 1 <;> simp [Function.comp_apply] <;> ring
    exact hd.hasDerivWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    exact mul_pos (Real.exp_pos _) (sub_pos.mpr hx.2)

private lemma rate_argument (lam : ℝ) (hlam : 0 < lam) :
    lam * Real.exp (-lam) = Real.exp (-1 - rate lam) := by
  rw [show -1 - rate lam = Real.log lam + (-lam) by
    simp [rate]
    ring]
  rw [Real.exp_add, Real.exp_log hlam]

theorem result (_hEnum : FiniteEnumerationStatement) (hRate : RateStatement) :
    ∀ lam : ℝ, 0 < lam → lam ≠ 1 →
      HasSum (rootedTerm (lam * Real.exp (-lam)))
        (if lam < 1 then lam else conjugate lam) := by
  intro lam hlam hne
  let z : ℝ := lam * Real.exp (-lam)
  have hz : 0 < z := by dsimp [z]; positivity
  have hzr : z < Real.exp (-1) := by
    dsimp [z]
    rw [rate_argument lam hlam]
    exact Real.exp_lt_exp.mpr (by
      have hr := hRate.1 lam hlam hne
      linarith)
  have hsum := hasSum_rootedTerm (mem_treeSeries_ball hz hzr)
  have hpos := treeFun_pos hz hzr
  have hlt := treeFun_lt_one hz hzr
  have hfixed := treeFun_fixed hz hzr
  by_cases hsub : lam < 1
  · have heq : treeFun z = lam := by
      apply strictMonoOn_unit.injOn
      · exact ⟨hpos.le, hlt.le⟩
      · exact ⟨hlam.le, hsub.le⟩
      · simpa [z] using! hfixed
    simpa [if_pos hsub, heq] using! hsum
  · have hsuper : 1 < lam := lt_of_le_of_ne (le_of_not_gt hsub) hne.symm
    have hc := hRate.2.1 lam hsuper
    have heq : treeFun z = conjugate lam :=
      hc.2.2.2.2 (treeFun z) hpos hlt (by simpa [z] using! hfixed)
    simpa [if_neg hsub, heq] using! hsum

end

end Erdos745.WrapUp.Proofs.Internal.W05_SUMS_TreeSeries


/-!
The fixed-rate tree tail.  After shifting the lower endpoint, normalization
turns the tail into a geometrically dominated series whose summands converge
pointwise to the corresponding geometric summands.
-/

namespace Erdos745.WrapUp.Proofs.Internal.W05_SUMS_Tails

open Erdos745.WrapUp
open Filter Set
open scoped BigOperators Topology ENNReal

noncomputable section

private def tailTerm (a : ℝ) (k : ℕ) : ℝ :=
  Real.rpow (k : ℝ) (-5 / 2 : ℝ) * Real.exp (-a * k)

private def addEquivIci (h : ℕ) : ℕ ≃ Set.Ici h where
  toFun j := ⟨h + j, by simp⟩
  invFun k := k.1 - h
  left_inv j := by simp
  right_inv k := by
    apply Subtype.ext
    exact Nat.add_sub_of_le k.2

private lemma treeTail_reindex (a : ℝ) {h : ℕ} (hh : 0 < h) :
    treeTail a h = ∑' j : ℕ, tailTerm a (h + j) := by
  unfold treeTail
  calc
    (∑' k : ℕ, if h ≤ k ∧ 0 < k then tailTerm a k else 0) =
        ∑' k : Set.Ici h, tailTerm a k := by
      rw [tsum_subtype]
      apply tsum_congr
      intro k
      simp only [Set.indicator, Set.mem_Ici]
      by_cases hk : h ≤ k
      · simp [hk, lt_of_lt_of_le hh hk]
      · simp [hk]
    _ = ∑' j : ℕ, tailTerm a (h + j) := by
      symm
      simpa [addEquivIci] using!
        (Equiv.tsum_eq (addEquivIci h) (fun k : Set.Ici h => tailTerm a k))

private def normalizedSummand (a : ℝ) (h j : ℕ) : ℝ :=
  if h = 0 then 0 else
    (1 - Real.exp (-a)) *
      Real.rpow (1 + (j : ℝ) / (h : ℝ)) (-5 / 2 : ℝ) *
      Real.exp (-a) ^ j

private lemma normalized_term (a : ℝ) {h : ℕ} (hh : 0 < h) (j : ℕ) :
    tailTerm a (h + j) /
        (Real.rpow (h : ℝ) (-5 / 2 : ℝ) * Real.exp (-a * h) /
          (1 - Real.exp (-a))) = normalizedSummand a h j := by
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh
  have hbase : 0 ≤ (1 + (j : ℝ) / (h : ℝ)) := by positivity
  have hratio : 1 + (j : ℝ) / (h : ℝ) = ((h + j : ℕ) : ℝ) / (h : ℝ) := by
    push_cast
    field_simp
  have hrpow :
      Real.rpow (1 + (j : ℝ) / (h : ℝ)) (-5 / 2 : ℝ) =
        Real.rpow ((h + j : ℕ) : ℝ) (-5 / 2 : ℝ) /
          Real.rpow (h : ℝ) (-5 / 2 : ℝ) := by
    rw [hratio]
    exact Real.div_rpow (by positivity) (by positivity) _
  have hexp : Real.exp (-a * ((h + j : ℕ) : ℝ)) =
      Real.exp (-a * h) * Real.exp (-a) ^ j := by
    rw [show -a * ((h + j : ℕ) : ℝ) = -a * (h : ℝ) + (j : ℝ) * (-a) by
      push_cast
      ring]
    rw [Real.exp_add, Real.exp_nat_mul]
  have hp : Real.rpow (h : ℝ) (-5 / 2 : ℝ) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos hhR _)
  have he : Real.exp (-a * h) ≠ 0 := Real.exp_ne_zero _
  simp only [normalizedSummand, if_neg (Nat.ne_of_gt hh), tailTerm]
  rw [hexp, hrpow]
  field_simp

private lemma normalized_tail (a : ℝ) {h : ℕ} (hh : 0 < h) :
    treeTail a h /
        (Real.rpow (h : ℝ) (-5 / 2 : ℝ) * Real.exp (-a * h) /
          (1 - Real.exp (-a))) =
      ∑' j : ℕ, normalizedSummand a h j := by
  rw [treeTail_reindex a hh, ← tsum_div_const]
  apply tsum_congr
  exact normalized_term a hh

private lemma normalizedSummand_nonneg {a : ℝ} (ha : 0 < a) (h j : ℕ) :
    0 ≤ normalizedSummand a h j := by
  by_cases hh : h = 0
  · simp [normalizedSummand, hh]
  · simp only [normalizedSummand, if_neg hh]
    have hq0 : 0 < Real.exp (-a) := Real.exp_pos _
    have hq1 : Real.exp (-a) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    exact mul_nonneg
      (mul_nonneg (sub_nonneg.mpr hq1.le) (Real.rpow_nonneg (by positivity) _))
      (pow_nonneg hq0.le _)

private lemma normalizedSummand_le {a : ℝ} (ha : 0 < a) (h j : ℕ) :
    normalizedSummand a h j ≤
      (1 - Real.exp (-a)) * Real.exp (-a) ^ j := by
  by_cases hh : h = 0
  · simp only [normalizedSummand, hh, if_pos]
    exact mul_nonneg
      (sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by linarith)))
      (pow_nonneg (Real.exp_pos _).le _)
  · simp only [normalizedSummand, if_neg hh]
    have hhR : (0 : ℝ) < h := by exact_mod_cast Nat.pos_of_ne_zero hh
    have hbase : 1 ≤ 1 + (j : ℝ) / (h : ℝ) :=
      le_add_of_nonneg_right (div_nonneg (Nat.cast_nonneg _) hhR.le)
    have hr := Real.rpow_le_one_of_one_le_of_nonpos hbase (by norm_num : (-5 / 2 : ℝ) ≤ 0)
    have hq0 : 0 ≤ Real.exp (-a) := (Real.exp_pos _).le
    have hc : 0 ≤ 1 - Real.exp (-a) := by
      exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by linarith))
    exact mul_le_mul_of_nonneg_right
      (by simpa using! mul_le_mul_of_nonneg_left hr hc) (pow_nonneg hq0 _)

private lemma normalizedSummand_tendsto (a : ℝ) (j : ℕ) :
    Tendsto (fun h : ℕ => normalizedSummand a h j) atTop
      (𝓝 ((1 - Real.exp (-a)) * Real.exp (-a) ^ j)) := by
  have hone : Tendsto (fun h : ℕ => 1 + (j : ℝ) / (h : ℝ)) atTop (𝓝 1) := by
    have hz := (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (j : ℝ)
    simpa [div_eq_mul_inv] using! tendsto_const_nhds.add hz
  have hrpow : Tendsto
      (fun h : ℕ => Real.rpow (1 + (j : ℝ) / (h : ℝ)) (-5 / 2 : ℝ))
      atTop (𝓝 1) := by
    simpa using! hone.rpow tendsto_const_nhds (Or.inl one_ne_zero)
  have hprod : Tendsto
      (fun h : ℕ => (1 - Real.exp (-a)) *
        Real.rpow (1 + (j : ℝ) / (h : ℝ)) (-5 / 2 : ℝ) *
        Real.exp (-a) ^ j) atTop
      (𝓝 ((1 - Real.exp (-a)) * Real.exp (-a) ^ j)) := by
    have hc : Tendsto (fun _ : ℕ => 1 - Real.exp (-a)) atTop
        (𝓝 (1 - Real.exp (-a))) := tendsto_const_nhds
    have hq : Tendsto (fun _ : ℕ => Real.exp (-a) ^ j) atTop
        (𝓝 (Real.exp (-a) ^ j)) := tendsto_const_nhds
    simpa only [one_mul, mul_one] using! (hc.mul hrpow).mul hq
  apply hprod.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with h hh
  simp [normalizedSummand, Nat.ne_of_gt hh]

theorem powerWeightSummable (beta u : ℝ) (hu : 0 < u) :
    Summable (fun k : ℕ => Real.rpow ((k + 1 : ℕ) : ℝ) beta *
      Real.exp (-u * (k + 1))) := by
  obtain ⟨m, hm⟩ := exists_nat_ge beta
  have hmajor0 := Real.summable_pow_mul_exp_neg_nat_mul m hu
  have hmajor : Summable (fun k : ℕ => (((k + 1 : ℕ) : ℝ) ^ m) *
      Real.exp (-u * (k + 1))) := by
    simpa [Nat.cast_add, Nat.cast_one] using!
      (summable_nat_add_iff (f := fun n : ℕ =>
        ((n : ℝ) ^ m) * Real.exp (-u * n)) 1).2 hmajor0
  apply Summable.of_nonneg_of_le
  · intro k
    exact mul_nonneg (Real.rpow_nonneg (by positivity) _)
      (Real.exp_pos _).le
  · intro k
    have hk : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by norm_num
    have hp : Real.rpow ((k + 1 : ℕ) : ℝ) beta ≤
        Real.rpow ((k + 1 : ℕ) : ℝ) (m : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hk hm
    calc
      Real.rpow ((k + 1 : ℕ) : ℝ) beta * Real.exp (-u * (k + 1)) ≤
          Real.rpow ((k + 1 : ℕ) : ℝ) (m : ℝ) * Real.exp (-u * (k + 1)) :=
        mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le
      _ = (((k + 1 : ℕ) : ℝ) ^ m) * Real.exp (-u * (k + 1)) := by
        congr 1
        exact Real.rpow_natCast _ _
  · exact hmajor

private lemma one_add_rpow_le {beta x : ℝ} (hbeta : 0 ≤ beta) (hx : 0 ≤ x) :
    Real.rpow (x + 1) beta ≤
      Real.rpow 2 beta * (1 + Real.rpow x beta) := by
  by_cases hx1 : x ≤ 1
  · have hpow : Real.rpow (x + 1) beta ≤ Real.rpow 2 beta :=
      Real.rpow_le_rpow (by positivity) (by linarith) hbeta
    have htwo : 0 ≤ Real.rpow 2 beta := Real.rpow_nonneg (by norm_num) _
    have hxr : 0 ≤ Real.rpow x beta := Real.rpow_nonneg hx _
    nlinarith
  · have hx1' : 1 ≤ x := le_of_not_ge hx1
    have hpow : Real.rpow (x + 1) beta ≤ Real.rpow (2 * x) beta :=
      Real.rpow_le_rpow (by positivity) (by linarith) hbeta
    have hmul : Real.rpow (2 * x) beta =
        Real.rpow 2 beta * Real.rpow x beta :=
      Real.mul_rpow (by norm_num) hx
    rw [hmul] at hpow
    have htwo : 0 ≤ Real.rpow 2 beta := Real.rpow_nonneg (by norm_num) _
    have hxr : 0 ≤ Real.rpow x beta := Real.rpow_nonneg hx _
    nlinarith

private lemma power_exp_antitone {beta u : ℝ} (hbeta : beta < 0) (hu : 0 < u) :
    AntitoneOn (fun x : ℝ => Real.rpow x beta * Real.exp (-u * x)) (Set.Ici 1) := by
  intro x hx y hy hxy
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hy0 : 0 < y := lt_of_lt_of_le hx0 hxy
  have hpow : Real.rpow y beta ≤ Real.rpow x beta :=
    (Real.strictAntiOn_rpow_Ioi_of_exponent_neg hbeta).antitoneOn hx0 hy0 hxy
  have hexp : Real.exp (-u * y) ≤ Real.exp (-u * x) := by
    rw [Real.exp_le_exp]
    exact mul_le_mul_of_nonpos_left hxy (by linarith)
  exact mul_le_mul hpow hexp (Real.exp_pos _).le
    (Real.rpow_nonneg (le_of_lt hx0) _)

private lemma power_exp_integrable {beta u : ℝ} (hbeta : -1 < beta) (hu : 0 < u) :
    MeasureTheory.IntegrableOn (fun x : ℝ => Real.rpow x beta * Real.exp (-u * x))
      (Set.Ioi 0) := by
  simpa only [Real.rpow_one] using!
    (integrableOn_rpow_mul_exp_neg_mul_rpow
      (p := (1 : ℝ)) (s := beta) (b := u) hbeta (by norm_num) hu)

private lemma power_exp_integral {beta u : ℝ} (hbeta : -1 < beta) (hu : 0 < u) :
    (∫ x in Set.Ioi (0 : ℝ), Real.rpow x beta * Real.exp (-u * x)) =
      Real.rpow u (-beta - 1) * Real.Gamma (beta + 1) := by
  change (∫ x in Set.Ioi (0 : ℝ), x ^ beta * Real.exp (-u * x)) =
    u ^ (-beta - 1) * Real.Gamma (beta + 1)
  have h := integral_rpow_mul_exp_neg_mul_rpow
    (p := (1 : ℝ)) (q := beta) (b := u) (by norm_num) hbeta hu
  simp at h
  convert h using 1 <;> ring_nf

private lemma exp_integrable (u : ℝ) (hu : 0 < u) :
    MeasureTheory.IntegrableOn (fun x : ℝ => Real.exp (-u * x)) (Set.Ioi 0) := by
  simpa only [Real.rpow_zero, one_mul, Real.rpow_one] using!
    (integrableOn_rpow_mul_exp_neg_mul_rpow
      (p := (1 : ℝ)) (s := (0 : ℝ)) (b := u)
      (by norm_num) (by norm_num) hu)

private lemma exp_integral (u : ℝ) (hu : 0 < u) :
    (∫ x in Set.Ioi (0 : ℝ), Real.exp (-u * x)) = Real.rpow u (-1) := by
  change (∫ x in Set.Ioi (0 : ℝ), Real.exp (-u * x)) = u ^ (-1 : ℝ)
  have h := integral_rpow_mul_exp_neg_mul_rpow
    (p := (1 : ℝ)) (q := (0 : ℝ)) (b := u)
      (by norm_num) (by norm_num) hu
  simp at h
  simpa using! h

theorem powerWeight :
    ∀ beta : ℝ, -1 < beta → ∃ C : ℝ, 0 < C ∧ ∀ u : ℝ, 0 < u → u ≤ 1 →
      Summable (fun k : ℕ => Real.rpow ((k + 1 : ℕ) : ℝ) beta *
        Real.exp (-u * (k + 1))) ∧
      (∑' k : ℕ, Real.rpow ((k + 1 : ℕ) : ℝ) beta * Real.exp (-u * (k + 1))) ≤
        C * Real.rpow u (-beta - 1) := by
  intro beta hbeta
  have hGammaPos : 0 < Real.Gamma (beta + 1) :=
    Real.Gamma_pos_of_pos (by linarith)
  by_cases hneg : beta < 0
  · refine ⟨1 + Real.Gamma (beta + 1), by linarith, ?_⟩
    intro u hu hu1
    refine ⟨powerWeightSummable beta u hu, ?_⟩
    apply Real.tsum_le_of_sum_range_le
    · intro k
      exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.exp_pos _).le
    · intro n
      have hRpos : 0 < Real.rpow u (-beta - 1) := Real.rpow_pos_of_pos hu _
      have hfirst : Real.exp (-u) ≤ Real.rpow u (-beta - 1) := by
        exact (Real.exp_le_one_iff.mpr (by linarith)).trans
          (Real.one_le_rpow_of_pos_of_le_one_of_nonpos hu hu1 (by linarith))
      cases n with
      | zero =>
          simp only [Finset.sum_range_zero]
          positivity
      | succ N =>
          have hsumInt :
              (∑ k ∈ Finset.range N,
                Real.rpow ((((k + 1) + 1 : ℕ) : ℝ)) beta *
                  Real.exp (-u * ((k + 1) + 1))) ≤
                ∫ x in (1 : ℝ)..1 + N,
                  Real.rpow x beta * Real.exp (-u * x) := by
            have hsum := ((power_exp_antitone hneg hu).mono (by
              intro x hx
              exact hx.1)).sum_le_integral (x₀ := (1 : ℝ)) (a := N)
            have heq :
                (∑ k ∈ Finset.range N,
                  Real.rpow ((((k + 1) + 1 : ℕ) : ℝ)) beta *
                    Real.exp (-u * ((k + 1) + 1))) =
                  ∑ k ∈ Finset.range N,
                    Real.rpow (1 + ((k + 1 : ℕ) : ℝ)) beta *
                      Real.exp (-u * (1 + ((k + 1 : ℕ) : ℝ))) := by
              apply Finset.sum_congr rfl
              intro k hk
              congr 2 <;> push_cast <;> ring
            rw [heq]
            exact hsum
          have hInterval :
              (∫ x in (1 : ℝ)..1 + N,
                Real.rpow x beta * Real.exp (-u * x)) ≤
                ∫ x in Set.Ioi (0 : ℝ),
                  Real.rpow x beta * Real.exp (-u * x) := by
            rw [intervalIntegral.integral_of_le
              (le_add_of_nonneg_right (Nat.cast_nonneg N))]
            apply MeasureTheory.setIntegral_mono_set
              (power_exp_integrable hbeta hu)
            · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with x hx
              exact mul_nonneg (Real.rpow_nonneg hx.le _) (Real.exp_pos _).le
            · filter_upwards with x
              intro hx
              exact zero_lt_one.trans hx.1
          have htail :
              (∑ k ∈ Finset.range N,
                Real.rpow ((((k + 1) + 1 : ℕ) : ℝ)) beta *
                  Real.exp (-u * ((k + 1) + 1))) ≤
                Real.rpow u (-beta - 1) * Real.Gamma (beta + 1) := by
            exact hsumInt.trans (hInterval.trans_eq (power_exp_integral hbeta hu))
          rw [Finset.sum_range_succ']
          calc
            _ ≤
                Real.rpow u (-beta - 1) * Real.Gamma (beta + 1) +
                  Real.rpow u (-beta - 1) := by
              convert add_le_add htail hfirst using 1
              all_goals norm_num [Nat.cast_add, Nat.cast_one]
            _ = (1 + Real.Gamma (beta + 1)) * Real.rpow u (-beta - 1) := by ring
  · have hbeta0 : 0 ≤ beta := le_of_not_gt hneg
    let A : ℝ := Real.rpow 2 beta
    refine ⟨1 + A * (1 + Real.Gamma (beta + 1)), ?_, ?_⟩
    · have hA : 0 < A := Real.rpow_pos_of_pos (by norm_num) _
      have hfactor : 0 < 1 + Real.Gamma (beta + 1) := by linarith
      have hprod : 0 < A * (1 + Real.Gamma (beta + 1)) := mul_pos hA hfactor
      linarith
    · intro u hu hu1
      refine ⟨powerWeightSummable beta u hu, ?_⟩
      apply Real.tsum_le_of_sum_range_le
      · intro k
        exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.exp_pos _).le
      · intro n
        have hRpos : 0 < Real.rpow u (-beta - 1) := Real.rpow_pos_of_pos hu _
        have hfirst : Real.exp (-u) ≤ Real.rpow u (-beta - 1) := by
          exact (Real.exp_le_one_iff.mpr (by linarith)).trans
            (Real.one_le_rpow_of_pos_of_le_one_of_nonpos hu hu1 (by linarith))
        have hIntExp := exp_integrable u hu
        have hIntPow := power_exp_integrable hbeta hu
        have hIntMaj : MeasureTheory.IntegrableOn
            (fun x : ℝ => A *
              (Real.exp (-u * x) + Real.rpow x beta * Real.exp (-u * x)))
            (Set.Ioi 0) :=
          (hIntExp.add hIntPow).const_mul A
        have hApos : 0 < A := Real.rpow_pos_of_pos (by norm_num) _
        have hCpos : 0 < 1 + A * (1 + Real.Gamma (beta + 1)) := by
          have hfactor : 0 < 1 + Real.Gamma (beta + 1) := by linarith
          have hprod : 0 < A * (1 + Real.Gamma (beta + 1)) :=
            mul_pos hApos hfactor
          linarith
        cases n with
        | zero =>
            simp only [Finset.sum_range_zero]
            exact mul_nonneg hCpos.le hRpos.le
        | succ N =>
            have hcomp :
                (∑ i ∈ Finset.Ico 1 (N + 1),
                  Real.rpow ((i + 1 : ℕ) : ℝ) beta *
                    Real.exp (-u * (i + 1))) ≤
                  ∫ x in (1 : ℝ)..(N + 1 : ℕ), A *
                    (Real.exp (-u * x) +
                      Real.rpow x beta * Real.exp (-u * x)) := by
              have h := sum_Ico_le_integral_of_le
                (a := 1) (b := N + 1)
                (f := fun y : ℝ =>
                  Real.rpow (y + 1) beta * Real.exp (-u * (y + 1)))
                (g := fun x : ℝ => A *
                  (Real.exp (-u * x) +
                    Real.rpow x beta * Real.exp (-u * x)))
                (by omega)
                (by
                  intro i hi x hx
                  have hx1 : (1 : ℝ) ≤ x := by
                    have hi1 : (1 : ℝ) ≤ i := by exact_mod_cast hi.1
                    exact hi1.trans hx.1
                  have hx0 : 0 ≤ x := zero_le_one.trans hx1
                  have hibase : (i : ℝ) + 1 ≤ x + 1 := by linarith [hx.1]
                  have hfirstPow : Real.rpow ((i : ℝ) + 1) beta ≤
                      Real.rpow (x + 1) beta :=
                    Real.rpow_le_rpow (by positivity) hibase hbeta0
                  have hrpow : Real.rpow ((i : ℝ) + 1) beta ≤
                      A * (1 + Real.rpow x beta) := by
                    dsimp [A]
                    exact hfirstPow.trans (one_add_rpow_le hbeta0 hx0)
                  have hexp : Real.exp (-u * ((i : ℝ) + 1)) ≤
                      Real.exp (-u * x) := by
                    rw [Real.exp_le_exp]
                    have hxi : x ≤ (i : ℝ) + 1 := by
                      push_cast at hx
                      exact le_of_lt hx.2
                    exact mul_le_mul_of_nonpos_left hxi (by linarith)
                  have hcoef : 0 ≤ A * (1 + Real.rpow x beta) := by
                    dsimp [A]
                    exact mul_nonneg (Real.rpow_nonneg (by norm_num) _)
                      (add_nonneg zero_le_one (Real.rpow_nonneg hx0 _))
                  calc
                    Real.rpow ((i : ℝ) + 1) beta *
                        Real.exp (-u * ((i : ℝ) + 1)) ≤
                        (A * (1 + Real.rpow x beta)) * Real.exp (-u * x) :=
                      mul_le_mul hrpow hexp (Real.exp_pos _).le hcoef
                    _ = A * (Real.exp (-u * x) +
                        Real.rpow x beta * Real.exp (-u * x)) := by ring)
                (MeasureTheory.IntegrableOn.mono_set hIntMaj (by
                  intro x hx
                  norm_num at hx
                  exact zero_lt_one.trans_le hx.1))
              simpa only [Nat.cast_add, Nat.cast_one] using! h
            have hreindex :
                (∑ k ∈ Finset.range N,
                  Real.rpow ((((k + 1) + 1 : ℕ) : ℝ)) beta *
                    Real.exp (-u * ((k + 1) + 1))) =
                  ∑ i ∈ Finset.Ico 1 (N + 1),
                    Real.rpow ((i + 1 : ℕ) : ℝ) beta *
                      Real.exp (-u * (i + 1)) := by
              have h := Finset.sum_Ico_add
                (fun i : ℕ => Real.rpow ((i + 1 : ℕ) : ℝ) beta *
                  Real.exp (-u * (i + 1))) 0 N 1
              simpa [Nat.Ico_zero_eq_range, add_comm] using! h
            have hInterval :
                (∫ x in (1 : ℝ)..(N + 1 : ℕ), A *
                    (Real.exp (-u * x) +
                      Real.rpow x beta * Real.exp (-u * x))) ≤
                  ∫ x in Set.Ioi (0 : ℝ), A *
                    (Real.exp (-u * x) +
                      Real.rpow x beta * Real.exp (-u * x)) := by
              rw [intervalIntegral.integral_of_le (by exact_mod_cast (by omega : 1 ≤ N + 1))]
              apply MeasureTheory.setIntegral_mono_set hIntMaj
              · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with x hx
                exact mul_nonneg (le_of_lt (Real.rpow_pos_of_pos (by norm_num) _))
                  (add_nonneg (Real.exp_pos _).le
                    (mul_nonneg (Real.rpow_nonneg hx.le _) (Real.exp_pos _).le))
              · filter_upwards with x
                intro hx
                norm_num at hx
                exact zero_lt_one.trans hx.1
            have hMajEval :
                (∫ x in Set.Ioi (0 : ℝ), A *
                    (Real.exp (-u * x) +
                      Real.rpow x beta * Real.exp (-u * x))) =
                  A * (Real.rpow u (-1) +
                    Real.rpow u (-beta - 1) * Real.Gamma (beta + 1)) := by
              calc
                _ = A * (∫ x in Set.Ioi (0 : ℝ),
                    Real.exp (-u * x) +
                      Real.rpow x beta * Real.exp (-u * x)) := by
                  exact MeasureTheory.integral_const_mul A _
                _ = A * ((∫ x in Set.Ioi (0 : ℝ), Real.exp (-u * x)) +
                    ∫ x in Set.Ioi (0 : ℝ),
                      Real.rpow x beta * Real.exp (-u * x)) := by
                  rw [MeasureTheory.integral_add hIntExp hIntPow]
                _ = A * (Real.rpow u (-1) +
                    Real.rpow u (-beta - 1) * Real.Gamma (beta + 1)) := by
                  rw [exp_integral u hu, power_exp_integral hbeta hu]
            have hpowRates : Real.rpow u (-1) ≤ Real.rpow u (-beta - 1) :=
              Real.rpow_le_rpow_of_exponent_ge hu hu1 (by linarith)
            have hA0 : 0 ≤ A := by
              dsimp [A]
              exact Real.rpow_nonneg (by norm_num) _
            have hMajBound :
                A * (Real.rpow u (-1) +
                    Real.rpow u (-beta - 1) * Real.Gamma (beta + 1)) ≤
                  A * (1 + Real.Gamma (beta + 1)) *
                    Real.rpow u (-beta - 1) := by
              calc
                A * (Real.rpow u (-1) +
                    Real.rpow u (-beta - 1) * Real.Gamma (beta + 1)) ≤
                    A * (Real.rpow u (-beta - 1) +
                      Real.rpow u (-beta - 1) * Real.Gamma (beta + 1)) :=
                  mul_le_mul_of_nonneg_left
                    (add_le_add hpowRates (le_refl _)) hA0
                _ = A * (1 + Real.Gamma (beta + 1)) *
                    Real.rpow u (-beta - 1) := by ring
            have htail :
                (∑ k ∈ Finset.range N,
                  Real.rpow ((((k + 1) + 1 : ℕ) : ℝ)) beta *
                    Real.exp (-u * ((k + 1) + 1))) ≤
                  A * (1 + Real.Gamma (beta + 1)) *
                    Real.rpow u (-beta - 1) := by
              rw [hreindex]
              exact hcomp.trans (hInterval.trans (hMajEval.le.trans hMajBound))
            rw [Finset.sum_range_succ']
            calc
              _ ≤
                  A * (1 + Real.Gamma (beta + 1)) *
                    Real.rpow u (-beta - 1) + Real.rpow u (-beta - 1) := by
                convert add_le_add htail hfirst using 1
                all_goals norm_num [Nat.cast_add, Nat.cast_one]
              _ = (1 + A * (1 + Real.Gamma (beta + 1))) *
                  Real.rpow u (-beta - 1) := by ring

theorem fixedTail :
    ∀ a : ℝ, 0 < a → Tendsto (fun h : ℕ => treeTail a h /
      (Real.rpow (h : ℝ) (-5 / 2 : ℝ) * Real.exp (-a * h) /
        (1 - Real.exp (-a)))) atTop (𝓝 1) := by
  intro a ha
  let q : ℝ := Real.exp (-a)
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := by
    dsimp [q]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have hsumq : Summable (fun j : ℕ => (1 - q) * q ^ j) :=
    (summable_geometric_of_norm_lt_one (by simpa [Real.norm_eq_abs, abs_of_nonneg hq0])).mul_left _
  have ht : Tendsto (fun h => ∑' j, normalizedSummand a h j) atTop
      (𝓝 (∑' j, (1 - q) * q ^ j)) :=
    tendsto_tsum_of_dominated_convergence hsumq
    (fun j => normalizedSummand_tendsto a j)
    (Filter.Eventually.of_forall fun h j => by
      rw [Real.norm_eq_abs, abs_of_nonneg (normalizedSummand_nonneg ha h j)]
      simpa [q] using! normalizedSummand_le ha h j)
  have hgeom : (∑' j : ℕ, (1 - q) * q ^ j) = 1 := by
    calc
      (∑' j : ℕ, (1 - q) * q ^ j) =
          (1 - q) * ∑' j : ℕ, q ^ j := tsum_mul_left
      _ = (1 - q) * (1 - q)⁻¹ := by
        rw [tsum_geometric_of_norm_lt_one]
        simpa [Real.norm_eq_abs, abs_of_nonneg hq0]
      _ = 1 := by
        field_simp [sub_ne_zero.mpr (ne_of_gt hq1)]
  rw [hgeom] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with h hh
  exact (normalized_tail a (by omega)).symm

private def tailIntegrand (a t : ℝ) : ℝ :=
  Real.rpow t (-5 / 2 : ℝ) * Real.exp (-a * t)

private lemma tailIntegrand_integrable {q a h : ℝ}
    (hq : q < -1) (ha : 0 < a) (hh : 0 < h) :
    MeasureTheory.IntegrableOn
      (fun t : ℝ => Real.rpow t q * Real.exp (-a * t)) (Set.Ioi h) := by
  have hp : MeasureTheory.IntegrableOn (fun t : ℝ => Real.rpow t q) (Set.Ioi h) := by
    change MeasureTheory.IntegrableOn (fun t : ℝ => t ^ q) (Set.Ioi h)
    exact integrableOn_Ioi_rpow_of_lt hq hh
  apply hp.mul_bdd
  · have hc : Continuous (fun t : ℝ => Real.exp (-a * t)) := by fun_prop
    exact hc.aestronglyMeasurable
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg
      (by linarith) (le_of_lt (hh.trans ht)))

private lemma tailIntegrand_antitone {a h : ℝ} (ha : 0 < a) (hh : 0 < h) :
    AntitoneOn (tailIntegrand a) (Set.Ici h) := by
  intro x hx y hy hxy
  have hx0 : 0 < x := hh.trans_le hx
  have hy0 : 0 < y := hx0.trans_le hxy
  have hp : Real.rpow y (-5 / 2 : ℝ) ≤ Real.rpow x (-5 / 2 : ℝ) :=
    (Real.strictAntiOn_rpow_Ioi_of_exponent_neg (by norm_num)).antitoneOn
      hx0 hy0 hxy
  have he : Real.exp (-a * y) ≤ Real.exp (-a * x) := by
    rw [Real.exp_le_exp]
    exact mul_le_mul_of_nonpos_left hxy (by linarith)
  exact mul_le_mul hp he (Real.exp_pos _).le (Real.rpow_nonneg hx0.le _)

private lemma tail_sum_integral_squeeze {a : ℝ} {h : ℕ} (ha : 0 < a) (hh : 0 < h) :
    let I := ∫ t in Set.Ioi (h : ℝ), tailIntegrand a t
    I ≤ ∑' j : ℕ, tailTerm a (h + j) ∧
      (∑' j : ℕ, tailTerm a (h + j)) ≤ I + tailTerm a h := by
  dsimp only
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh
  have hInt : MeasureTheory.IntegrableOn (tailIntegrand a) (Set.Ioi (h : ℝ)) := by
    change MeasureTheory.IntegrableOn
      (fun t : ℝ => t ^ (-5 / 2 : ℝ) * Real.exp (-a * t)) (Set.Ioi (h : ℝ))
    exact tailIntegrand_integrable (q := (-5 / 2 : ℝ)) (by norm_num) ha hhR
  have hant := tailIntegrand_antitone ha hhR
  have hnonneg : ∀ j : ℕ, 0 ≤ tailTerm a (h + j) := by
    intro j
    exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.exp_pos _).le
  have hsumBound : ∀ n : ℕ,
      (∑ j ∈ Finset.range n, tailTerm a (h + j)) ≤
        (∫ t in Set.Ioi (h : ℝ), tailIntegrand a t) + tailTerm a h := by
    intro n
    cases n with
    | zero =>
        simp only [Finset.sum_range_zero]
        have hi0 : 0 ≤ ∫ t in Set.Ioi (h : ℝ), tailIntegrand a t := by
          apply MeasureTheory.setIntegral_nonneg measurableSet_Ioi
          intro t ht
          exact mul_nonneg (Real.rpow_nonneg (hhR.trans ht).le _) (Real.exp_pos _).le
        exact add_nonneg hi0 (hnonneg 0)
    | succ N =>
        rw [Finset.sum_range_succ']
        have hs := (hant.mono (by intro x hx; exact hx.1)).sum_le_integral
          (x₀ := (h : ℝ)) (a := N)
        have hs' : (∑ j ∈ Finset.range N, tailTerm a (h + (j + 1))) ≤
            ∫ t in (h : ℝ)..(h : ℝ) + N, tailIntegrand a t := by
          convert hs using 1
          apply Finset.sum_congr rfl
          intro j hj
          simp only [tailTerm, tailIntegrand]
          congr 2 <;> push_cast <;> ring
        have hfinle : (∫ t in (h : ℝ)..(h : ℝ) + N, tailIntegrand a t) ≤
            ∫ t in Set.Ioi (h : ℝ), tailIntegrand a t := by
          rw [intervalIntegral.integral_of_le
            (le_add_of_nonneg_right (Nat.cast_nonneg N))]
          apply MeasureTheory.setIntegral_mono_set hInt
          · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
            exact mul_nonneg (Real.rpow_nonneg (hhR.trans ht).le _) (Real.exp_pos _).le
          · filter_upwards with t
            intro ht
            exact ht.1
        have ht := hs'.trans hfinle
        have heq : tailTerm a (h + 0) = tailTerm a h := by rw [Nat.add_zero]
        rw [heq]
        linarith
  have hsumm : Summable (fun j : ℕ => tailTerm a (h + j)) :=
    summable_of_sum_range_le hnonneg hsumBound
  constructor
  · have htop : Tendsto (fun N : ℕ => (h : ℝ) + (N : ℝ)) atTop atTop :=
      Filter.tendsto_atTop_add_const_left atTop (h : ℝ) tendsto_natCast_atTop_atTop
    have hIlim := MeasureTheory.intervalIntegral_tendsto_integral_Ioi
      (h : ℝ) hInt htop
    have hSlim := hsumm.hasSum.tendsto_sum_nat
    apply le_of_tendsto_of_tendsto hIlim hSlim
    filter_upwards with N
    have hs := (hant.mono (by intro x hx; exact hx.1)).integral_le_sum
      (x₀ := (h : ℝ)) (a := N)
    convert hs using 1
    apply Finset.sum_congr rfl
    intro j hj
    simp only [tailTerm, tailIntegrand]
    congr 2 <;> push_cast <;> ring
  · exact Real.tsum_le_of_sum_range_le hnonneg hsumBound

private lemma tail_integral_identity {a h : ℝ} (ha : 0 < a) (hh : 0 < h) :
    (∫ t in Set.Ioi h, tailIntegrand a t) =
      tailIntegrand a h / a - (5 / (2 * a)) *
        ∫ t in Set.Ioi h, Real.rpow t (-7 / 2 : ℝ) * Real.exp (-a * t) := by
  let u : ℝ → ℝ := fun t => Real.rpow t (-5 / 2 : ℝ)
  let u' : ℝ → ℝ := fun t => (-5 / 2 : ℝ) * Real.rpow t (-7 / 2 : ℝ)
  let v : ℝ → ℝ := fun t => -(1 / a) * Real.exp (-a * t)
  let v' : ℝ → ℝ := fun t => Real.exp (-a * t)
  have hu : ∀ x ∈ Set.Ioi h, HasDerivAt u (u' x) x := by
    intro x hx
    dsimp [u, u']
    convert Real.hasDerivAt_rpow_const (x := x) (p := (-5 / 2 : ℝ))
      (Or.inl (ne_of_gt (hh.trans hx))) using 1
    ring_nf
  have hv : ∀ x ∈ Set.Ioi h, HasDerivAt v (v' x) x := by
    intro x hx
    dsimp [v, v']
    have hi : HasDerivAt (fun t : ℝ => -a * t) (-a) x := by
      simpa using! (hasDerivAt_id x).const_mul (-a)
    have he : HasDerivAt (fun t : ℝ => Real.exp (-a * t))
        (Real.exp (-a * x) * (-a)) x := by
      simpa only [Function.comp_apply] using!
        (Real.hasDerivAt_exp (-a * x)).comp x hi
    convert he.const_mul (-(1 / a)) using 1
    field_simp [ha.ne']
  have huv' : MeasureTheory.IntegrableOn (u * v') (Set.Ioi h) := by
    simpa [u, v', Pi.mul_apply] using!
      (tailIntegrand_integrable (q := (-5 / 2 : ℝ)) (by norm_num) ha hh)
  have hbase := tailIntegrand_integrable (q := (-7 / 2 : ℝ)) (by norm_num) ha hh
  have heq : u' * v = fun t : ℝ =>
      (5 / (2 * a)) * (Real.rpow t (-7 / 2 : ℝ) * Real.exp (-a * t)) := by
    funext t
    dsimp [u', v]
    field_simp [ha.ne']
  have hu'v : MeasureTheory.IntegrableOn (u' * v) (Set.Ioi h) := by
    rw [heq]
    exact hbase.const_mul (5 / (2 * a))
  have hzero : Tendsto (u * v) (𝓝[>] h)
      (𝓝 (Real.rpow h (-5 / 2 : ℝ) * (-(1 / a) * Real.exp (-a * h)))) := by
    change Tendsto
      (fun t : ℝ => Real.rpow t (-5 / 2 : ℝ) * (-(1 / a) * Real.exp (-a * t)))
      (𝓝[>] h)
      (𝓝 (Real.rpow h (-5 / 2 : ℝ) * (-(1 / a) * Real.exp (-a * h))))
    have hp := Real.continuousAt_rpow_const h (-5 / 2 : ℝ) (Or.inl hh.ne')
    have he : ContinuousAt (fun t : ℝ => -(1 / a) * Real.exp (-a * t)) h := by
      fun_prop
    exact (hp.mul he).continuousWithinAt
  have hinfty : Tendsto (u * v) atTop (𝓝 0) := by
    have ht := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (-5 / 2 : ℝ) a ha
    have hc := ht.const_mul (-(1 / a))
    change Tendsto
      (fun t : ℝ => Real.rpow t (-5 / 2 : ℝ) * (-(1 / a) * Real.exp (-a * t)))
      atTop (𝓝 0)
    convert hc using 1
    · funext t
      change Real.rpow t (-5 / 2 : ℝ) * (-(1 / a) * Real.exp (-a * t)) =
        -(1 / a) * (Real.rpow t (-5 / 2 : ℝ) * Real.exp (-a * t))
      ring
    · ring_nf
  have hibp := MeasureTheory.integral_Ioi_mul_deriv_eq_deriv_mul
    hu hv huv' hu'v hzero hinfty
  have hK : (∫ x in Set.Ioi h, u' x * v x) =
      (5 / (2 * a)) * ∫ t in Set.Ioi h,
        Real.rpow t (-7 / 2 : ℝ) * Real.exp (-a * t) := by
    rw [show (fun x => u' x * v x) = u' * v by rfl, heq]
    exact MeasureTheory.integral_const_mul _ _
  rw [hK] at hibp
  change
    (∫ x in Set.Ioi h, Real.rpow x (-5 / 2 : ℝ) * Real.exp (-a * x)) =
      0 - Real.rpow h (-5 / 2 : ℝ) * (-(1 / a) * Real.exp (-a * h)) -
        (5 / (2 * a)) *
          ∫ t in Set.Ioi h, Real.rpow t (-7 / 2 : ℝ) * Real.exp (-a * t)
    at hibp
  calc
    (∫ t in Set.Ioi h, tailIntegrand a t) =
        0 - Real.rpow h (-5 / 2 : ℝ) * (-(1 / a) * Real.exp (-a * h)) -
          (5 / (2 * a)) *
            ∫ t in Set.Ioi h, Real.rpow t (-7 / 2 : ℝ) * Real.exp (-a * t) := by
      simpa [tailIntegrand] using! hibp
    _ = tailIntegrand a h / a - (5 / (2 * a)) *
        ∫ t in Set.Ioi h, Real.rpow t (-7 / 2 : ℝ) * Real.exp (-a * t) := by
      simp only [tailIntegrand]
      field_simp [ha.ne']
      ring

private lemma tail_integral_bounds {a h : ℝ} (ha : 0 < a) (hh : 0 < h) :
    let I := ∫ t in Set.Ioi h, tailIntegrand a t
    let D := tailIntegrand a h / a
    D / (1 + 5 / (2 * a * h)) ≤ I ∧ I ≤ D := by
  dsimp only
  let I := ∫ t in Set.Ioi h, tailIntegrand a t
  let K := ∫ t in Set.Ioi h,
    Real.rpow t (-7 / 2 : ℝ) * Real.exp (-a * t)
  let D := tailIntegrand a h / a
  have hIint : MeasureTheory.IntegrableOn (tailIntegrand a) (Set.Ioi h) := by
    change MeasureTheory.IntegrableOn
      (fun t : ℝ => t ^ (-5 / 2 : ℝ) * Real.exp (-a * t)) (Set.Ioi h)
    exact tailIntegrand_integrable (q := (-5 / 2 : ℝ)) (by norm_num) ha hh
  have hKint : MeasureTheory.IntegrableOn
      (fun t : ℝ => Real.rpow t (-7 / 2 : ℝ) * Real.exp (-a * t))
      (Set.Ioi h) :=
    tailIntegrand_integrable (q := (-7 / 2 : ℝ)) (by norm_num) ha hh
  have hKle : K ≤ (1 / h) * I := by
    have hscaled : MeasureTheory.IntegrableOn
        (fun t : ℝ => (1 / h) * tailIntegrand a t) (Set.Ioi h) :=
      hIint.const_mul (1 / h)
    have hmono := MeasureTheory.setIntegral_mono_on hKint hscaled measurableSet_Ioi (by
      intro t ht
      have ht0 : 0 < t := hh.trans ht
      have hrpow : Real.rpow t (-7 / 2 : ℝ) ≤
          (1 / h) * Real.rpow t (-5 / 2 : ℝ) := by
        have heq : Real.rpow t (-7 / 2 : ℝ) =
            Real.rpow t (-5 / 2 : ℝ) * Real.rpow t (-1 : ℝ) := by
          change t ^ (-7 / 2 : ℝ) = t ^ (-5 / 2 : ℝ) * t ^ (-1 : ℝ)
          rw [← Real.rpow_add ht0]
          congr 1
          ring
        have hnegone : Real.rpow t (-1 : ℝ) = t⁻¹ := by
          change t ^ (-1 : ℝ) = t⁻¹
          exact Real.rpow_neg_one t
        rw [heq, hnegone]
        have hinv : t⁻¹ ≤ h⁻¹ := (inv_le_inv₀ ht0 hh).2 ht.le
        simpa [one_div, mul_comm] using!
          (mul_le_mul_of_nonneg_left hinv (Real.rpow_nonneg ht0.le (-5 / 2 : ℝ)))
      simpa only [tailIntegrand, mul_assoc] using!
        (mul_le_mul_of_nonneg_right hrpow (Real.exp_pos (-a * t)).le))
    calc
      K ≤ ∫ t in Set.Ioi h, (1 / h) * tailIntegrand a t := hmono
      _ = (1 / h) * I := MeasureTheory.integral_const_mul _ _
  have hI0 : 0 ≤ I := by
    apply MeasureTheory.setIntegral_nonneg measurableSet_Ioi
    intro t ht
    exact mul_nonneg (Real.rpow_nonneg (hh.trans ht).le _) (Real.exp_pos _).le
  have hK0 : 0 ≤ K := by
    apply MeasureTheory.setIntegral_nonneg measurableSet_Ioi
    intro t ht
    exact mul_nonneg (Real.rpow_nonneg (hh.trans ht).le _) (Real.exp_pos _).le
  have hid : I = D - (5 / (2 * a)) * K := by
    dsimp [I, D, K]
    exact tail_integral_identity ha hh
  have hq0 : 0 ≤ 5 / (2 * a) := by positivity
  have hupper : I ≤ D := by
    rw [hid]
    exact sub_le_self _ (mul_nonneg hq0 hK0)
  constructor
  · have hden : 0 < 1 + 5 / (2 * a * h) := by positivity
    apply (div_le_iff₀ hden).2
    have hstep : D ≤ I + (5 / (2 * a)) * ((1 / h) * I) := by
      have hd : D = I + (5 / (2 * a)) * K := by linarith [hid]
      rw [hd]
      exact add_le_add (le_refl I) (mul_le_mul_of_nonneg_left hKle hq0)
    calc
      D ≤ I + (5 / (2 * a)) * ((1 / h) * I) := hstep
      _ = I * (1 + 5 / (2 * a * h)) := by
        field_simp [ha.ne', hh.ne']
  · exact hupper

private lemma natural_denominator_eq {a h : ℝ} (ha : 0 < a) (hh : 0 < h) :
    tailIntegrand a h / a =
      Real.rpow a (3 / 2 : ℝ) * Real.rpow (a * h) (-5 / 2 : ℝ) *
        Real.exp (-(a * h)) := by
  have hmul : Real.rpow (a * h) (-5 / 2 : ℝ) =
      Real.rpow a (-5 / 2 : ℝ) * Real.rpow h (-5 / 2 : ℝ) :=
    Real.mul_rpow ha.le hh.le
  have hpow : Real.rpow a (3 / 2 : ℝ) * Real.rpow a (-5 / 2 : ℝ) =
      Real.rpow a (-1 : ℝ) := by
    change a ^ (3 / 2 : ℝ) * a ^ (-5 / 2 : ℝ) = a ^ (-1 : ℝ)
    rw [← Real.rpow_add ha]
    congr 1
    ring
  have hneg : Real.rpow a (-1 : ℝ) = a⁻¹ := by
    change a ^ (-1 : ℝ) = a⁻¹
    exact Real.rpow_neg_one a
  rw [tailIntegrand, hmul, ← mul_assoc, hpow, hneg]
  field_simp [ha.ne']

private lemma treeTail_natural_bounds {a : ℝ} {h : ℕ} (ha : 0 < a) (hh : 0 < h) :
    let x := a * (h : ℝ)
    let D := Real.rpow a (3 / 2 : ℝ) * Real.rpow x (-5 / 2 : ℝ) * Real.exp (-x)
    1 / (1 + 5 / (2 * x)) ≤ treeTail a h / D ∧
      treeTail a h / D ≤ 1 + a := by
  dsimp only
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh
  let I := ∫ t in Set.Ioi (h : ℝ), tailIntegrand a t
  let D0 := tailIntegrand a (h : ℝ) / a
  have hD0 : 0 < D0 := by
    dsimp [D0, tailIntegrand]
    positivity
  have hsqueeze := tail_sum_integral_squeeze ha hh
  have hint := tail_integral_bounds ha hhR
  have htree : treeTail a h = ∑' j : ℕ, tailTerm a (h + j) :=
    treeTail_reindex a hh
  have hDeq : D0 = Real.rpow a (3 / 2 : ℝ) *
      Real.rpow (a * (h : ℝ)) (-5 / 2 : ℝ) * Real.exp (-(a * (h : ℝ))) :=
    natural_denominator_eq ha hhR
  rw [← hDeq, htree]
  constructor
  · apply (le_div_iff₀ hD0).2
    have hlow : D0 / (1 + 5 / (2 * a * (h : ℝ))) ≤
        ∑' j : ℕ, tailTerm a (h + j) := hint.1.trans hsqueeze.1
    convert hlow using 1
    field_simp
  · apply (div_le_iff₀ hD0).2
    have hF : tailTerm a h = a * D0 := by
      dsimp [D0, tailTerm, tailIntegrand]
      field_simp [ha.ne']
    calc
      (∑' j : ℕ, tailTerm a (h + j)) ≤ I + tailTerm a h := hsqueeze.2
      _ ≤ D0 + tailTerm a h := add_le_add hint.2 (le_refl _)
      _ = (1 + a) * D0 := by rw [hF]; ring

private lemma scale_ratio {a x L : ℝ} (ha : 0 < a) (hx : 0 < x) (hL : 0 < L) :
    (Real.rpow a (3 / 2 : ℝ) * Real.rpow x (-5 / 2 : ℝ) * Real.exp (-x)) /
      (Real.rpow a (3 / 2 : ℝ) * Real.rpow L (-5 / 2 : ℝ) * Real.exp (-L)) =
      Real.rpow (x / L) (-5 / 2 : ℝ) * Real.exp (-(x - L)) := by
  have hdiv : Real.rpow (x / L) (-5 / 2 : ℝ) =
      Real.rpow x (-5 / 2 : ℝ) / Real.rpow L (-5 / 2 : ℝ) :=
    Real.div_rpow hx.le hL.le _
  rw [hdiv, show -(x - L) = -x + L by ring, Real.exp_add]
  rw [show Real.exp L = (Real.exp (-L))⁻¹ by rw [← Real.exp_neg]; simp]
  field_simp [(Real.rpow_pos_of_pos ha (3 / 2 : ℝ)).ne']

theorem movingTail :
    ∀ (aa Ls : RealSeq) (hs : NatSeq), (∀ᶠ n in atTop, 0 < aa n) →
      Tendsto aa atTop (𝓝 0) → Tendsto Ls atTop atTop →
      Tendsto (fun n => aa n * (hs n : ℝ) - Ls n) atTop (𝓝 0) →
      Tendsto (fun n => treeTail (aa n) (hs n) /
        (Real.rpow (aa n) (3 / 2 : ℝ) * Real.rpow (Ls n) (-5 / 2 : ℝ) *
          Real.exp (-Ls n))) atTop (𝓝 1) := by
  intro aa Ls hs haaPos haa hLs hdiff
  let xs : ℕ → ℝ := fun n => aa n * (hs n : ℝ)
  let D : ℕ → ℝ := fun n =>
    Real.rpow (aa n) (3 / 2 : ℝ) * Real.rpow (xs n) (-5 / 2 : ℝ) *
      Real.exp (-xs n)
  let DL : ℕ → ℝ := fun n =>
    Real.rpow (aa n) (3 / 2 : ℝ) * Real.rpow (Ls n) (-5 / 2 : ℝ) *
      Real.exp (-Ls n)
  change Tendsto (fun n => treeTail (aa n) (hs n) / DL n) atTop (𝓝 1)
  have hdiffXs : Tendsto (fun n => xs n - Ls n) atTop (𝓝 0) := by
    simpa [xs] using! hdiff
  have hxsEq : xs = fun n => Ls n + (xs n - Ls n) := by
    funext n
    ring
  have hxsTop : Tendsto xs atTop atTop := by
    rw [hxsEq]
    exact hLs.atTop_add hdiffXs
  have hxsPos : ∀ᶠ n in atTop, 0 < xs n :=
    hxsTop.eventually (eventually_gt_atTop (0 : ℝ))
  have hLsPos : ∀ᶠ n in atTop, 0 < Ls n :=
    hLs.eventually (eventually_gt_atTop (0 : ℝ))
  have hhsPos : ∀ᶠ n in atTop, 0 < hs n := by
    filter_upwards [haaPos, hxsPos] with n han hxn
    by_contra hn
    have : hs n = 0 := Nat.eq_zero_of_not_pos hn
    simp [xs, this] at hxn
  have hbounds : ∀ᶠ n in atTop,
      1 / (1 + 5 / (2 * xs n)) ≤ treeTail (aa n) (hs n) / D n ∧
        treeTail (aa n) (hs n) / D n ≤ 1 + aa n := by
    filter_upwards [haaPos, hhsPos] with n han hhn
    simpa [xs, D] using! treeTail_natural_bounds han hhn
  have hInvX : Tendsto (fun n => (xs n)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hxsTop
  have hsmall : Tendsto (fun n => 5 / (2 * xs n)) atTop (𝓝 0) := by
    have ht := hInvX.const_mul (5 / 2 : ℝ)
    convert ht using 1
    · funext n
      field_simp
    · rw [mul_zero]
  have hlower : Tendsto (fun n => 1 / (1 + 5 / (2 * xs n))) atTop (𝓝 1) := by
    have hc : ContinuousAt (fun z : ℝ => 1 / (1 + z)) 0 :=
      continuousAt_const.div₀ (continuousAt_const.add continuousAt_id) (by norm_num)
    simpa using! hc.tendsto.comp hsmall
  have hupper : Tendsto (fun n => 1 + aa n) atTop (𝓝 1) := by
    simpa using! tendsto_const_nhds.add haa
  have hnatural : Tendsto (fun n => treeTail (aa n) (hs n) / D n)
      atTop (𝓝 1) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper
    · exact hbounds.mono fun n hn => hn.1
    · exact hbounds.mono fun n hn => hn.2
  have hdiffDiv : Tendsto (fun n => (xs n - Ls n) / Ls n) atTop (𝓝 0) :=
    hdiffXs.div_atTop hLs
  have hxDivL : Tendsto (fun n => xs n / Ls n) atTop (𝓝 1) := by
    have ht : Tendsto (fun n => 1 + (xs n - Ls n) / Ls n) atTop (𝓝 1) := by
      simpa using! tendsto_const_nhds.add hdiffDiv
    apply ht.congr'
    filter_upwards [hLsPos] with n hLn
    field_simp [hLn.ne']
    ring
  have hrpowScale : Tendsto (fun n => Real.rpow (xs n / Ls n) (-5 / 2 : ℝ))
      atTop (𝓝 1) := by
    simpa using! hxDivL.rpow tendsto_const_nhds (Or.inl one_ne_zero)
  have hexpScale : Tendsto (fun n => Real.exp (-(xs n - Ls n))) atTop (𝓝 1) := by
    have he : Tendsto Real.exp (𝓝 0) (𝓝 1) := by
      simpa using! Real.continuous_exp.tendsto 0
    have hneg : Tendsto (fun n => -(xs n - Ls n)) atTop (𝓝 0) := by
      simpa using! hdiffXs.neg
    exact he.comp hneg
  have hscale : Tendsto (fun n => D n / DL n) atTop (𝓝 1) := by
    have ht : Tendsto (fun n => Real.rpow (xs n / Ls n) (-5 / 2 : ℝ) *
        Real.exp (-(xs n - Ls n))) atTop (𝓝 1) := by
      simpa using! hrpowScale.mul hexpScale
    apply ht.congr'
    filter_upwards [haaPos, hxsPos, hLsPos] with n han hxn hLn
    exact (scale_ratio han hxn hLn).symm
  have hprod : Tendsto
      (fun n => treeTail (aa n) (hs n) / D n * (D n / DL n))
      atTop (𝓝 1) := by
    simpa using! hnatural.mul hscale
  apply hprod.congr'
  filter_upwards [haaPos, hxsPos, hLsPos] with n han hxn hLn
  have hD : D n ≠ 0 := by
    dsimp [D]
    positivity
  have hDL : DL n ≠ 0 := by
    dsimp [DL]
    positivity
  field_simp

end

end Erdos745.WrapUp.Proofs.Internal.W05_SUMS_Tails
