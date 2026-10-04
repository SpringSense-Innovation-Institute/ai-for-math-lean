module

public import Erdos745.WrapUp.Proofs.Internal.Linked.W13_Excursions
public import Mathlib.MeasureTheory.Integral.Indicator

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local simp] Pi.div_def Pi.mul_def Pi.add_def Pi.sub_def Pi.neg_def Pi.inv_def Function.comp_def Pi.pow_def Pi.smul_def Real.rpow_eq_pow

@[expose] public section


/-!
At a fixed positive time, backward Brownian increments cannot eventually lie
below a linear bound. The eventual-bound event is measurable using increments
in every terminal time window. Gap independence and continuity therefore make
it independent of each backward increment. A uniform positive Gaussian tail,
together with convergence of indicators on that event, forces its measure to
vanish. This proves fixed-time reflected-zero nullity without a stopping theorem.
-/
namespace Erdos745.WrapUp.Proofs.Internal.W13_BROWNIAN_Nullity

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local simp] Pi.div_def Pi.mul_def Pi.add_def Pi.sub_def Pi.neg_def Pi.inv_def Function.comp_def
open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology
open W13_BROWNIAN_Regularity W13_BROWNIAN_Minima W13_BROWNIAN_Geometry

local instance : MeasurableSpace BrownianPath := borel BrownianPath
local instance : BorelSpace BrownianPath := ⟨rfl⟩

private lemma measurable_increment (a b : NNReal) :
    Measurable (fun w : BrownianPath ↦ w b - w a) :=
  (ContinuousEvalConst.continuous_eval_const b).measurable.sub
    (ContinuousEvalConst.continuous_eval_const a).measurable

private lemma increment_law (mu : PathLaw) (hmu : BrownianLaw mu)
    (a b : NNReal) (hab : a < b) :
    mu.map (fun w : BrownianPath ↦ w b - w a) =
      gaussianReal 0 ((b : ℝ) - (a : ℝ)).toNNReal := by
  let u : ℕ → NNReal := fun n ↦ if n = 0 then a else b
  have hu : ∀ j < 1, u j < u (j + 1) := by
    intro j hj
    have : j = 0 := by omega
    subst j
    simpa [u] using! hab
  simpa [brownianIncrementVector, u] using!
    brownianIncrementCoordinate_law mu hmu 1 u hu (0 : Fin 1)

private lemma measurable_eventually_le {Ω : Type*} [MeasurableSpace Ω]
    (X : ℕ → Ω → ℝ) (hX : ∀ n, Measurable (X n)) (d : ℕ → ℝ) :
    MeasurableSet {w | ∀ᶠ n in atTop, X n w ≤ d n} := by
  simp only [eventually_atTop, Set.setOf_exists, Set.setOf_forall]
  exact MeasurableSet.iUnion fun N ↦ MeasurableSet.iInter fun n ↦
    MeasurableSet.iInter fun _ ↦ measurableSet_le (hX n) measurable_const

/-- Independence of an event and threshold tests passes to an almost-sure
limit whenever the limiting variable does not charge the threshold. -/
private lemma measure_inter_gt_of_tendsto {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) [IsFiniteMeasure mu] (E : Set Ω) (hE : MeasurableSet E)
    (X : ℕ → Ω → ℝ) (Y : Ω → ℝ) (hX : ∀ n, Measurable (X n))
    (hY : Measurable Y) (c : ℝ) (hne : ∀ᵐ w ∂mu, Y w ≠ c)
    (hlim : ∀ᵐ w ∂mu, Tendsto (fun n ↦ X n w) atTop (𝓝 (Y w)))
    (hind : ∀ n, mu (E ∩ {w | c < X n w}) = mu E * mu {w | c < X n w}) :
    mu (E ∩ {w | c < Y w}) = mu E * mu {w | c < Y w} := by
  have hevent : ∀ᵐ w ∂mu, ∀ᶠ n in atTop, c < X n w ↔ c < Y w := by
    filter_upwards [hne, hlim] with w hw hl
    rcases lt_or_gt_of_ne hw with hlt | hgt
    · filter_upwards [hl.eventually_lt_const hlt] with n hn
      exact iff_of_false (not_lt_of_ge hn.le) (not_lt_of_ge hlt.le)
    · filter_upwards [hl.eventually_const_lt hgt] with n hn
      exact iff_of_true hn hgt
  have h1 := tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure
    (μ := mu) atTop (measurableSet_lt measurable_const hY)
    (fun n ↦ measurableSet_lt measurable_const (hX n)) hevent
  have h2 := tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure
    (μ := mu) atTop (hE.inter (measurableSet_lt measurable_const hY))
    (fun n ↦ hE.inter (measurableSet_lt measurable_const (hX n)))
    (hevent.mono fun w hw ↦ hw.mono fun n hn ↦ and_congr_right fun _ ↦ hn)
  have h3 := ENNReal.Tendsto.const_mul h1 (Or.inr (measure_ne_top mu E))
  exact tendsto_nhds_unique h2 (h3.congr (fun n ↦ (hind n).symm))

/-- A Gaussian increment with duration at most `T` has a uniform positive
chance to exceed `C` times its duration. -/
private lemma gaussian_linear_tail_lower (C T h : ℝ) (hC : 0 ≤ C)
    (hh : 0 < h) (hhT : h ≤ T) :
    gaussianReal 0 1 (Set.Ioi (C * (T + 1))) ≤
      gaussianReal 0 h.toNNReal (Set.Ioi (C * h)) := by
  have hs : 0 < Real.sqrt h := Real.sqrt_pos.2 hh
  have hs2 : (Real.sqrt h) ^ 2 = h := Real.sq_sqrt hh.le
  have hT : 0 ≤ T := hh.le.trans hhT
  have hsT : Real.sqrt h ≤ T + 1 := by nlinarith [sq_nonneg T]
  have hvar : NNReal.mk ((Real.sqrt h) ^ 2) (sq_nonneg _) * 1 = h.toNNReal := by
    apply NNReal.eq
    simp [hs2, Real.toNNReal_of_nonneg hh.le]
  have hmap : (gaussianReal 0 1).map (fun x ↦ Real.sqrt h * x) =
      gaussianReal 0 h.toNNReal := by
    rw [gaussianReal_map_const_mul, mul_zero, hvar]
  rw [← hmap, Measure.map_apply (by fun_prop) measurableSet_Ioi]
  apply measure_mono
  intro x hx
  change C * h < Real.sqrt h * x
  have hbound : C * h ≤ Real.sqrt h * (C * (T + 1)) := by
    have := mul_nonneg hC (sub_nonneg.mpr hsT)
    have := mul_nonneg hs.le this
    nlinarith
  exact hbound.trans_lt (mul_lt_mul_of_pos_left hx hs)

private lemma gaussian_tail_pos (D : ℝ) : 0 < gaussianReal 0 1 (Set.Ioi D) := by
  apply pos_iff_ne_zero.mpr
  intro h
  have hv := gaussianReal_absolutelyContinuous' (0 : ℝ) (v := 1) (by norm_num) h
  simp at hv

/-- The event of an eventual backward linear bound is independent of each
individual backward increment, at every real threshold. -/
theorem backward_bound_inter_gt
    (mu : PathLaw) (hmu : BrownianLaw mu) (T : NNReal)
    (s : ℕ → NNReal) (hs : StrictMono s) (hsT : ∀ n, s n < T)
    (hlim : Tendsto s atTop (𝓝 T)) (d : ℕ → ℝ) (k : ℕ) (c : ℝ) :
    let E := {w : BrownianPath | ∀ᶠ n in atTop, w T - w (s n) ≤ d n}
    mu (E ∩ {w | c < w T - w (s k)}) = mu E * mu {w | c < w T - w (s k)} := by
  letI : IsProbabilityMeasure mu := hmu.1
  let E := {w : BrownianPath | ∀ᶠ n in atTop, w T - w (s n) ≤ d n}
  have hE : MeasurableSet E := measurable_eventually_le _
    (fun n ↦ measurable_increment (s n) T) d
  let r : ℕ → NNReal := fun n ↦ s (n + (k + 1))
  have hkr (n : ℕ) : s k < r n := hs (by omega)
  have hrT (n : ℕ) : r n < T := hsT _
  have hr : Tendsto r atTop (𝓝 T) := hlim.comp (tendsto_add_atTop_nat (k + 1))
  have hind (n : ℕ) :
      mu (E ∩ {w | c < w (r n) - w (s k)}) =
        mu E * mu {w | c < w (r n) - w (s k)} := by
    let a : ℕ → NNReal := fun m ↦ max (r n) (s m)
    let Z : BrownianPath → ℕ → ℝ := fun w m ↦ w T - w (a m)
    let H : Set (ℕ → ℝ) := {z | ∀ᶠ m in atTop, z m ≤ d m}
    have hH : MeasurableSet H := measurable_eventually_le _
      (fun m ↦ measurable_pi_apply m) d
    have hEZ : E = Z ⁻¹' H := by
      ext w
      apply eventually_congr
      filter_upwards [eventually_ge_atTop (n + (k + 1))] with m hm
      have ham : a m = s m := max_eq_right (hs.monotone hm)
      simp only [Z, ham]
    have hi := indepFun_gap_increments mu hmu (s k) (r n) (hkr n)
      a (fun _ ↦ T) (fun m ↦ max_le (hrT n).le (hsT m).le)
      (fun _ ↦ Or.inr (le_max_left _ _))
    have hi' := hi.measure_inter_preimage_eq_mul (Set.Ioi c) H measurableSet_Ioi hH
    rw [← hEZ] at hi'
    simpa only [Set.preimage_setOf_eq, Set.mem_Ioi, Set.inter_comm, mul_comm] using! hi'
  have hne : ∀ᵐ w ∂mu, w T - w (s k) ≠ c := by
    have hv : ((T : ℝ) - (s k : ℝ)).toNNReal ≠ 0 :=
      ne_of_gt (Real.toNNReal_pos.mpr (sub_pos.mpr (hsT k)))
    haveI : NullSingletonClass (mu.map (fun w : BrownianPath ↦ w T - w (s k))) := by
      rw [increment_law mu hmu (s k) T (hsT k)]
      exact nullSingletonClass_gaussianReal hv
    exact (ae_map_iff (measurable_increment (s k) T).aemeasurable
      (measurableSet_singleton c).compl).1 ((mu.map _).ae_ne c)
  exact measure_inter_gt_of_tendsto mu E hE
    (fun n w ↦ w (r n) - w (s k)) (fun w ↦ w T - w (s k))
    (fun n ↦ measurable_increment (s k) (r n)) (measurable_increment (s k) T) c hne
    (Eventually.of_forall fun w ↦ (w.continuous.tendsto T |>.comp hr).sub tendsto_const_nhds)
    hind

/-- Along any increasing deterministic sequence approaching a positive terminal
time, backward increments almost surely fail every fixed eventual linear bound. -/
theorem measure_eventually_backward_le_eq_zero
    (mu : PathLaw) (hmu : BrownianLaw mu) (T : NNReal)
    (s : ℕ → NNReal) (hs : StrictMono s) (hsT : ∀ n, s n < T)
    (hlim : Tendsto s atTop (𝓝 T)) (C : ℝ) (hC : 0 ≤ C) :
    mu {w : BrownianPath | ∀ᶠ n in atTop,
      w T - w (s n) ≤ C * ((T : ℝ) - (s n : ℝ))} = 0 := by
  letI : IsProbabilityMeasure mu := hmu.1
  let d : ℕ → ℝ := fun n ↦ C * ((T : ℝ) - (s n : ℝ))
  let E := {w : BrownianPath | ∀ᶠ n in atTop, w T - w (s n) ≤ d n}
  let B : ℕ → Set BrownianPath := fun n ↦ {w | d n < w T - w (s n)}
  let p := gaussianReal 0 1 (Set.Ioi (C * ((T : ℝ) + 1)))
  have hp : 0 < p := gaussian_tail_pos _
  have hE : MeasurableSet E := measurable_eventually_le _
    (fun n ↦ measurable_increment (s n) T) d
  have hB (n : ℕ) : MeasurableSet (B n) :=
    measurableSet_lt measurable_const (measurable_increment (s n) T)
  have hlower (n : ℕ) : p ≤ mu (B n) := by
    have hmap := congrArg (fun m : Measure ℝ ↦ m (Set.Ioi (d n)))
      (increment_law mu hmu (s n) T (hsT n))
    try dsimp only at hmap
    rw [Measure.map_apply (measurable_increment (s n) T) measurableSet_Ioi] at hmap
    change mu (B n) = _ at hmap
    rw [hmap]
    exact gaussian_linear_tail_lower C T _ hC (sub_pos.mpr (hsT n))
      (sub_le_self _ (s n).coe_nonneg)
  have hind (n : ℕ) : mu (E ∩ B n) = mu E * mu (B n) :=
    backward_bound_inter_gt mu hmu T s hs hsT hlim d n (d n)
  have hz : Tendsto (fun n ↦ mu (E ∩ B n)) atTop (𝓝 0) := by
    have h := tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure
      (μ := mu) atTop (A := ∅) MeasurableSet.empty (fun n ↦ hE.inter (hB n))
    simp only [measure_empty] at h
    apply h
    apply Eventually.of_forall
    intro w
    by_cases hw : w ∈ E
    · filter_upwards [hw] with n hn
      simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
      intro _
      exact not_lt_of_ge hn
    · exact Eventually.of_forall fun n ↦ by simp [hw]
  have hzero : mu E * p = 0 := by
    apply le_antisymm _ (zero_le)
    exact ge_of_tendsto hz (Eventually.of_forall fun n ↦ by
      rw [hind n]
      exact mul_le_mul_right (hlower n) (mu E))
  exact (mul_eq_zero.mp hzero).resolve_right hp.ne'

/-- A deterministic positive time is almost surely not a zero of the reflected
Brownian motion with parabolic drift. -/
theorem fixedTime_reflected_zero_null
    (mu : PathLaw) (hmu : BrownianLaw mu) (lam t : ℝ) (ht : 0 < t) :
    mu {w : BrownianPath | reflected w lam t.toNNReal = 0} = 0 := by
  let T := t.toNNReal
  have hT : 0 < T := Real.toNNReal_pos.mpr ht
  obtain ⟨s, hs, hs0T, hlim⟩ := exists_seq_strictMono_tendsto' hT
  let C := |lam| + (T : ℝ)
  have hC : 0 ≤ C := add_nonneg (abs_nonneg _) T.coe_nonneg
  apply measure_mono_null (t := {w : BrownianPath | ∀ᶠ n in atTop,
    w T - w (s n) ≤ C * ((T : ℝ) - (s n : ℝ))})
  · intro w hw
    apply Eventually.of_forall
    intro n
    have hsn : s n ≤ T := (hs0T n).2.le
    have hd := drift_le_of_reflected_zero w lam hw hsn
    have hdiff : 0 ≤ (T : ℝ) - (s n : ℝ) := sub_nonneg.mpr hsn
    have hm : 0 ≤ (|lam| + lam) * ((T : ℝ) - (s n : ℝ)) :=
      mul_nonneg (by linarith [neg_abs_le lam]) hdiff
    change w T + lam * (T : ℝ) - (T : ℝ) ^ 2 / 2 ≤
      w (s n) + lam * (s n : ℝ) - (s n : ℝ) ^ 2 / 2 at hd
    dsimp [C]
    nlinarith [sq_nonneg ((T : ℝ) - (s n : ℝ))]
  · exact measure_eventually_backward_le_eq_zero mu hmu T s hs
      (fun n ↦ (hs0T n).2) hlim C hC

end

end Erdos745.WrapUp.Proofs.Internal.W13_BROWNIAN_Nullity
