module

public import Erdos745.WrapUp.Contracts
public import Erdos745.WrapUp.Compat

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local simp] Pi.div_def Pi.mul_def Pi.add_def Pi.sub_def Pi.neg_def Pi.inv_def Function.comp_def Pi.pow_def Pi.smul_def Real.rpow_eq_pow

@[expose] public section


/-!
The law-construction component of W13.  The finite-dimensional bridge below is
kept separate from the path construction: it converts an exact product law for
strictly ordered increments into the literal `BrownianLaw` predicate, including
the project's integral definition of `normalCDF`.
-/
namespace Erdos745.WrapUp.Proofs.Internal.W13_BROWNIAN_Law

noncomputable section
open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal Topology

local instance : MeasurableSpace BrownianPath := borel BrownianPath
local instance : BorelSpace BrownianPath := ⟨rfl⟩
local instance : MeasurableSpace C(unitInterval, ℝ) := borel C(unitInterval, ℝ)
local instance : BorelSpace C(unitInterval, ℝ) := ⟨rfl⟩

/-- The countable standard-normal source used by the Lévy--Ciesielski
construction.  `Sum.inl ()` is the affine unit increment and `Sum.inr ⟨m,k⟩`
is the level-`m`, position-`k` bridge coordinate on unit interval `j`. -/
abbrev GaussianCoordinate :=
  ℕ × (Unit ⊕ Sigma fun m : ℕ ↦ Fin (2 ^ m))

abbrev GaussianSample := GaussianCoordinate → ℝ

def gaussianSource : Measure GaussianSample :=
  Measure.infinitePi fun _ : GaussianCoordinate ↦ gaussianReal 0 1

instance : IsProbabilityMeasure gaussianSource := by
  unfold gaussianSource
  infer_instance

def coordinate (c : GaussianCoordinate) : GaussianSample → ℝ :=
  fun omega ↦ omega c

lemma measurable_coordinate (c : GaussianCoordinate) : Measurable (coordinate c) :=
  measurable_pi_apply c

private lemma continuous_coordinate (c : GaussianCoordinate) : Continuous (coordinate c) :=
  continuous_apply c

lemma coordinate_law (c : GaussianCoordinate) :
    Measure.map (coordinate c) gaussianSource = gaussianReal 0 1 := by
  exact Measure.infinitePi_map_eval (fun _ : GaussianCoordinate ↦ gaussianReal 0 1) c

lemma independent_coordinates :
    iIndepFun coordinate gaussianSource := by
  exact iIndepFun_infinitePi fun _ ↦ measurable_id

private def hat (x : ℝ) : ℝ :=
  max 0 (min (2 * x) (2 - 2 * x))

private lemma continuous_hat : Continuous hat := by
  unfold hat
  fun_prop

private lemma hat_nonneg (x : ℝ) : 0 ≤ hat x := by
  simp [hat]

private lemma hat_le_one (x : ℝ) : hat x ≤ 1 := by
  unfold hat
  rcases le_total x (1 / 2 : ℝ) with hx | hx
  · have h2x : 2 * x ≤ 1 := by linarith
    exact max_le (by norm_num) (le_trans (min_le_left _ _) h2x)
  · have h2x : 2 - 2 * x ≤ 1 := by linarith
    exact max_le (by norm_num) (le_trans (min_le_right _ _) h2x)

private lemma hat_eq_zero_of_nonpos {x : ℝ} (hx : x ≤ 0) : hat x = 0 := by
  unfold hat
  rw [max_eq_left]
  exact le_trans (min_le_left _ _) (by linarith)

private lemma hat_eq_zero_of_one_le {x : ℝ} (hx : 1 ≤ x) : hat x = 0 := by
  unfold hat
  rw [max_eq_left]
  exact le_trans (min_le_right _ _) (by linarith)

private lemma hat_ne_zero_support {x : ℝ} (hx : hat x ≠ 0) :
    0 < x ∧ x < 1 := by
  have hp : 0 < hat x := lt_of_le_of_ne (hat_nonneg x) (Ne.symm hx)
  simp only [hat, lt_max_iff, lt_min_iff] at hp
  rcases hp with hp | hp
  · exact (lt_irrefl 0 hp).elim
  · constructor <;> linarith

private lemma hat_translate_disjoint {a : ℝ} {k l : ℕ} (hkl : k ≠ l)
    (hk : hat (a - k) ≠ 0) : hat (a - l) = 0 := by
  by_contra hl
  have hk' := hat_ne_zero_support hk
  have hl' := hat_ne_zero_support hl
  rcases lt_or_gt_of_ne hkl with hlt | hgt
  · have hstep : (k : ℝ) + 1 ≤ (l : ℝ) := by
      exact_mod_cast (Nat.succ_le_iff.mpr hlt)
    linarith
  · have hstep : (l : ℝ) + 1 ≤ (k : ℝ) := by
      exact_mod_cast (Nat.succ_le_iff.mpr hgt)
    linarith

private def hatScale (m : ℕ) : ℝ :=
  Real.rpow 2 (-(m : ℝ) / 2 - 1)

private lemma hatScale_pos (m : ℕ) : 0 < hatScale m := by
  exact Real.rpow_pos_of_pos (by norm_num) _

private def hatMap (m : ℕ) (k : Fin (2 ^ m)) : C(unitInterval, ℝ) where
  toFun x := hat (((2 ^ m : ℕ) : ℝ) * (x : ℝ) - (k : ℕ))
  continuous_toFun := continuous_hat.comp
    (((continuous_const.mul continuous_subtype_val).sub continuous_const))

private def unitLinear : C(unitInterval, ℝ) where
  toFun x := (x : ℝ)
  continuous_toFun := continuous_subtype_val

@[simp] private lemma unitLinear_apply (x : unitInterval) : unitLinear x = (x : ℝ) := rfl

@[simp] private lemma unitLinear_zero : unitLinear (0 : unitInterval) = 0 := rfl

@[simp] private lemma unitLinear_one : unitLinear (1 : unitInterval) = 1 := rfl

private def affineMap (j : ℕ) (omega : GaussianSample) : C(unitInterval, ℝ) :=
  coordinate (j, Sum.inl ()) omega • unitLinear

private def bridgeLevel (j m : ℕ) (omega : GaussianSample) : C(unitInterval, ℝ) :=
  ∑ k : Fin (2 ^ m),
    (hatScale m * coordinate (j, Sum.inr ⟨m, k⟩) omega) • hatMap m k

private def coefficientMax (j m : ℕ) (omega : GaussianSample) : NNReal :=
  Finset.univ.sup fun k : Fin (2 ^ m) ↦
    ‖coordinate (j, Sum.inr ⟨m, k⟩) omega‖₊

private lemma coordinate_nnnorm_le_max (j m : ℕ) (omega : GaussianSample)
    (k : Fin (2 ^ m)) :
    ‖coordinate (j, Sum.inr ⟨m, k⟩) omega‖₊ ≤ coefficientMax j m omega := by
  exact Finset.le_sup (s := Finset.univ)
    (f := fun l : Fin (2 ^ m) ↦
      ‖coordinate (j, Sum.inr ⟨m, l⟩) omega‖₊) (Finset.mem_univ k)

private lemma bridgeLevel_apply_bound (j m : ℕ) (omega : GaussianSample)
    (x : unitInterval) :
    ‖bridgeLevel j m omega x‖ ≤ hatScale m * coefficientMax j m omega := by
  let a : ℝ := ((2 ^ m : ℕ) : ℝ) * (x : ℝ)
  by_cases hex : ∃ k : Fin (2 ^ m), hat (a - (k : ℕ)) ≠ 0
  · rcases hex with ⟨k, hk⟩
    have hsingle : bridgeLevel j m omega x =
        (hatScale m * coordinate (j, Sum.inr ⟨m, k⟩) omega) * hatMap m k x := by
      unfold bridgeLevel
      rw [ContinuousMap.sum_apply]
      rw [Finset.sum_eq_single k]
      · rw [ContinuousMap.smul_apply, smul_eq_mul]
      · intro l hl hlk
        rw [ContinuousMap.smul_apply, smul_eq_mul]
        have hz : hatMap m l x = 0 := by
          apply hat_translate_disjoint (k := (k : ℕ)) (l := (l : ℕ))
          · intro hval
            apply Ne.symm hlk
            exact Fin.ext hval
          simpa [hatMap, a] using! hk
        simp [hz]
      · simp
    rw [hsingle, norm_mul, norm_mul]
    have hhat_nonneg : 0 ≤ hatMap m k x := hat_nonneg _
    have hhat_le : hatMap m k x ≤ 1 := hat_le_one _
    simp only [Real.norm_eq_abs]
    rw [abs_of_pos (hatScale_pos m), abs_of_nonneg hhat_nonneg]
    calc
      hatScale m * |coordinate (j, Sum.inr ⟨m, k⟩) omega| * hatMap m k x
          ≤ hatScale m * |coordinate (j, Sum.inr ⟨m, k⟩) omega| * 1 := by
            gcongr
            exact mul_nonneg (hatScale_pos m).le (abs_nonneg _)
      _ ≤ hatScale m * coefficientMax j m omega := by
        rw [mul_one]
        apply mul_le_mul_of_nonneg_left _ (hatScale_pos m).le
        exact_mod_cast coordinate_nnnorm_le_max j m omega k
  · have hall : ∀ k : Fin (2 ^ m), hatMap m k x = 0 := by
      intro k
      by_contra hk
      exact hex ⟨k, by simpa [hatMap, a] using! hk⟩
    simp [bridgeLevel, hall]
    exact mul_nonneg (hatScale_pos m).le (coefficientMax j m omega).2

private lemma bridgeLevel_norm_bound (j m : ℕ) (omega : GaussianSample) :
    ‖bridgeLevel j m omega‖ ≤ hatScale m * coefficientMax j m omega := by
  apply (ContinuousMap.norm_le _
    (mul_nonneg (hatScale_pos m).le (coefficientMax j m omega).2)).mpr
  exact bridgeLevel_apply_bound j m omega

private lemma standardGaussian_subgaussian :
    HasSubgaussianMGF id 1 (gaussianReal 0 1) := by
  constructor
  · exact integrable_exp_mul_gaussianReal
  · intro t
    rw [mgf_id_gaussianReal]
    simp

private lemma standardGaussian_abs_tail {a : ℝ} (ha : 0 ≤ a) :
    (gaussianReal 0 1).real {z | a < |z|} ≤
      2 * Real.exp (-a ^ 2 / 2) := by
  let upper : Set ℝ := {z | a ≤ z}
  let lower : Set ℝ := {z | a ≤ -z}
  have hsub : {z : ℝ | a < |z|} ⊆ upper ∪ lower := by
    intro z hz
    change a < |z| at hz
    simp only [Set.mem_union, Set.mem_setOf_eq, upper, lower]
    by_cases h : 0 ≤ z
    · left
      rw [abs_of_nonneg h] at hz
      exact hz.le
    · right
      rw [abs_of_neg (lt_of_not_ge h)] at hz
      exact hz.le
  calc
    (gaussianReal 0 1).real {z | a < |z|}
        ≤ (gaussianReal 0 1).real (upper ∪ lower) := measureReal_mono hsub
    _ ≤ (gaussianReal 0 1).real upper + (gaussianReal 0 1).real lower :=
      measureReal_union_le _ _
    _ ≤ Real.exp (-a ^ 2 / 2) + Real.exp (-a ^ 2 / 2) := by
      gcongr
      · simpa [upper] using! standardGaussian_subgaussian.measure_ge_le ha
      · simpa [lower] using! standardGaussian_subgaussian.neg.measure_ge_le ha
    _ = 2 * Real.exp (-a ^ 2 / 2) := by ring

/-! We use a deliberately generous linear cutoff.  It is stronger than needed
for uniform convergence, but makes the Borel--Cantelli estimate completely
elementary while retaining an exponentially summable deterministic majorant. -/
private def coefficientThreshold (m : ℕ) : NNReal :=
  4 * (m + 1)

private def badCoefficient (j m : ℕ) : Set GaussianSample :=
  {omega | coefficientThreshold m < coefficientMax j m omega}

private def badCoordinate (j m : ℕ) (k : Fin (2 ^ m)) : Set GaussianSample :=
  {omega | (coefficientThreshold m : ℝ) <
    |coordinate (j, Sum.inr ⟨m, k⟩) omega|}

private lemma badCoefficient_eq_iUnion (j m : ℕ) :
    badCoefficient j m = ⋃ k : Fin (2 ^ m), badCoordinate j m k := by
  ext omega
  simp only [badCoefficient, badCoordinate, Set.mem_setOf_eq, Set.mem_iUnion]
  unfold coefficientMax
  constructor
  · intro h
    rcases Finset.lt_sup_iff.mp h with ⟨k, _hk, hk⟩
    exact ⟨k, by exact_mod_cast hk⟩
  · rintro ⟨k, hk⟩
    apply Finset.lt_sup_iff.mpr
    exact ⟨k, Finset.mem_univ k, by exact_mod_cast hk⟩

private lemma badCoordinate_measureReal (j m : ℕ) (k : Fin (2 ^ m)) :
    gaussianSource.real (badCoordinate j m k) =
      (gaussianReal 0 1).real
        {z | (coefficientThreshold m : ℝ) < |z|} := by
  rw [← coordinate_law (j, Sum.inr ⟨m, k⟩)]
  rw [Measure.real, Measure.real, Measure.map_apply_of_aemeasurable
    (measurable_coordinate _).aemeasurable]
  · rfl
  · exact measurableSet_lt measurable_const
      (measurable_abs.comp (measurable_id : Measurable (id : ℝ → ℝ)))

private lemma badCoordinate_tail (j m : ℕ) (k : Fin (2 ^ m)) :
    gaussianSource.real (badCoordinate j m k) ≤
      2 * Real.exp (-((coefficientThreshold m : ℝ) ^ 2) / 2) := by
  rw [badCoordinate_measureReal]
  exact standardGaussian_abs_tail (coefficientThreshold m).2

private lemma badCoefficient_measureReal_le (j m : ℕ) :
    gaussianSource.real (badCoefficient j m) ≤
      (2 ^ m : ℝ) *
        (2 * Real.exp (-((coefficientThreshold m : ℝ) ^ 2) / 2)) := by
  rw [badCoefficient_eq_iUnion]
  calc
    gaussianSource.real (⋃ k : Fin (2 ^ m), badCoordinate j m k)
        ≤ ∑ k : Fin (2 ^ m), gaussianSource.real (badCoordinate j m k) := by
          simpa using! measureReal_biUnion_finset_le Finset.univ
            (badCoordinate j m)
    _ ≤ ∑ _k : Fin (2 ^ m),
          (2 * Real.exp (-((coefficientThreshold m : ℝ) ^ 2) / 2)) := by
          exact Finset.sum_le_sum fun k _ ↦ badCoordinate_tail j m k
    _ = (2 ^ m : ℝ) *
          (2 * Real.exp (-((coefficientThreshold m : ℝ) ^ 2) / 2)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
          norm_num

private lemma badCoefficient_measureReal_geometric (j m : ℕ) :
    gaussianSource.real (badCoefficient j m) ≤
      (2 * Real.exp (-8)) ^ (m + 1) := by
  refine (badCoefficient_measureReal_le j m).trans ?_
  simp only [coefficientThreshold, NNReal.coe_mul, NNReal.coe_ofNat]
  calc
    (2 ^ m : ℝ) * (2 * Real.exp (-((4 * ((m : ℝ) + 1)) ^ 2) / 2)) =
        (2 : ℝ) ^ (m + 1) *
          Real.exp (-8 * ((m : ℝ) + 1) ^ 2) := by
      rw [show (2 : ℝ) ^ (m + 1) = (2 : ℝ) ^ m * 2 by exact pow_succ 2 m]
      have he : -((4 * ((m : ℝ) + 1)) ^ 2) / 2 =
          -8 * ((m : ℝ) + 1) ^ 2 := by ring
      rw [he]
      ring
    _ ≤ (2 : ℝ) ^ (m + 1) *
          Real.exp (-8 * ((m : ℝ) + 1)) := by
      have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      have hx : (-8 : ℝ) * ((m : ℝ) + 1) ^ 2 ≤
          (-8 : ℝ) * ((m : ℝ) + 1) := by nlinarith
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hx) (by positivity)
    _ = (2 * Real.exp (-8)) ^ (m + 1) := by
      have he : -8 * ((m : ℝ) + 1) = ((m + 1 : ℕ) : ℝ) * (-8) := by
        push_cast
        ring
      rw [he, Real.exp_nat_mul, mul_pow]

private lemma badCoefficient_measureReal_summable (j : ℕ) :
    Summable fun m ↦ gaussianSource.real (badCoefficient j m) := by
  have hratio : ‖(2 * Real.exp (-8) : ℝ)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (mul_pos (by norm_num) (Real.exp_pos _))]
    rw [Real.exp_neg, ← div_eq_mul_inv]
    apply (div_lt_iff₀ (Real.exp_pos 8)).mpr
    have h := Real.add_one_le_exp (8 : ℝ)
    norm_num at h ⊢
    linarith
  have hgeom : Summable fun m : ℕ ↦ (2 * Real.exp (-8)) ^ (m + 1) := by
    exact (summable_geometric_of_norm_lt_one hratio).comp_injective
      (fun _ _ h ↦ Nat.add_right_cancel h)
  exact hgeom.of_nonneg_of_le
    (fun _ ↦ measureReal_nonneg)
    (fun m ↦ badCoefficient_measureReal_geometric j m)

private lemma badCoefficient_measure_tsum_ne_top (j : ℕ) :
    (∑' m, gaussianSource (badCoefficient j m)) ≠ ∞ := by
  let p : ℕ → NNReal := fun m ↦
    NNReal.mk (gaussianSource.real (badCoefficient j m)) (measureReal_nonneg)
  have hp : Summable fun m ↦ (p m : ℝ) := by
    simpa only [p, NNReal.smul_def] using! badCoefficient_measureReal_summable j
  have hfinite : (∑' m, ENNReal.ofNNReal (p m)) ≠ ∞ :=
    ENNReal.tsum_coe_ne_top_iff_summable_coe.mpr hp
  have hfun : (fun m ↦ gaussianSource (badCoefficient j m)) =
      fun m ↦ ENNReal.ofNNReal (p m) := by
    funext m
    symm
    calc
      ENNReal.ofNNReal (p m) =
          ENNReal.ofReal (gaussianSource.real (badCoefficient j m)) := by
        exact (ENNReal.ofReal_eq_coe_nnreal measureReal_nonneg).symm
      _ = gaussianSource (badCoefficient j m) := ofReal_measureReal
  rw [hfun]
  exact hfinite

private lemma ae_eventually_coefficientMax_le (j : ℕ) :
    ∀ᵐ omega ∂gaussianSource, ∀ᶠ m in atTop,
      coefficientMax j m omega ≤ coefficientThreshold m := by
  filter_upwards [ae_eventually_notMem (badCoefficient_measure_tsum_ne_top j)]
    with omega homega
  filter_upwards [homega] with m hm
  simpa only [badCoefficient, Set.mem_setOf_eq, not_lt] using! hm

private lemma ae_all_eventually_coefficientMax_le :
    ∀ᵐ omega ∂gaussianSource, ∀ j : ℕ, ∀ᶠ m in atTop,
      coefficientMax j m omega ≤ coefficientThreshold m := by
  simp only [ae_all_iff]
  exact ae_eventually_coefficientMax_le

/-- Samples whose bridge coefficients are eventually controlled on every unit
interval.  The Gaussian tail budget proves that this holds almost surely. -/
def GoodSample (omega : GaussianSample) : Prop :=
  ∀ j : ℕ, ∀ᶠ m in atTop,
    coefficientMax j m omega ≤ coefficientThreshold m

private lemma ae_goodSample : ∀ᵐ omega ∂gaussianSource, GoodSample omega :=
  ae_all_eventually_coefficientMax_le

private lemma summable_bridge_majorant :
    Summable fun m : ℕ ↦ hatScale m * (coefficientThreshold m : ℝ) := by
  let r : ℝ := Real.log 2 / 2
  have hr : 0 < r := div_pos (Real.log_pos (by norm_num)) (by norm_num)
  have h1 := Real.summable_pow_mul_exp_neg_nat_mul 1 hr
  have h0 := Real.summable_pow_mul_exp_neg_nat_mul 0 hr
  have hbase : Summable fun m : ℕ ↦
      ((m : ℝ) + 1) * Real.exp (-r * (m : ℝ)) := by
    convert h1.add h0 using 1
    funext m
    simp only [pow_one, pow_zero, one_mul]
    ring
  have hc := hbase.mul_left (4 * Real.exp (-Real.log 2))
  convert hc using 1
  funext m
  simp only [hatScale, coefficientThreshold, NNReal.coe_mul, NNReal.coe_ofNat]
  rw [show Real.rpow 2 (-(m : ℝ) / 2 - 1) =
      Real.exp (Real.log 2 * (-(m : ℝ) / 2 - 1)) by
    exact Real.rpow_def_of_pos (by norm_num) _]
  have he : Real.log 2 * (-(m : ℝ) / 2 - 1) =
      -Real.log 2 + (-r * (m : ℝ)) := by
    dsimp [r]
    ring
  rw [he, Real.exp_add]
  norm_cast
  ring

private def boundedBridgeLevel (j m : ℕ) (omega : GaussianSample) :
    BoundedContinuousFunction unitInterval ℝ :=
  ContinuousMap.linearIsometryBoundedOfCompact unitInterval ℝ ℝ
    (bridgeLevel j m omega)

private lemma boundedBridgeLevel_norm (j m : ℕ) (omega : GaussianSample) :
    ‖boundedBridgeLevel j m omega‖ = ‖bridgeLevel j m omega‖ := by
  exact (ContinuousMap.linearIsometryBoundedOfCompact unitInterval ℝ ℝ).norm_map _

private lemma summable_boundedBridgeLevel_of_good {omega : GaussianSample}
    (homega : GoodSample omega) (j : ℕ) :
    Summable fun m ↦ boundedBridgeLevel j m omega := by
  rcases (eventually_atTop.1 (homega j)) with ⟨N, hN⟩
  apply (summable_nat_add_iff N).mp
  apply Summable.of_norm_bounded
    ((summable_nat_add_iff N).mpr summable_bridge_majorant)
  intro m
  rw [boundedBridgeLevel_norm]
  refine (bridgeLevel_norm_bound j (m + N) omega).trans ?_
  exact mul_le_mul_of_nonneg_left
    (by exact_mod_cast hN (m + N) (Nat.le_add_left N m))
    (hatScale_pos (m + N)).le

private def bcfEval (x : unitInterval) :
    BoundedContinuousFunction unitInterval ℝ →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun f ↦ f x
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
    1 (fun f ↦ by simpa using! BoundedContinuousFunction.norm_coe_le_norm f x)

private def bridgeSum (j : ℕ) (omega : GaussianSample) : C(unitInterval, ℝ) :=
  (∑' m, boundedBridgeLevel j m omega).toContinuousMap

/-- The affine increment plus the uniformly convergent bridge series on unit
interval `j`. -/
def unitBlock (j : ℕ) (omega : GaussianSample) : C(unitInterval, ℝ) :=
  affineMap j omega + bridgeSum j omega

private def unitPartial (j N : ℕ) (omega : GaussianSample) : C(unitInterval, ℝ) :=
  affineMap j omega + ∑ m ∈ Finset.range N, bridgeLevel j m omega

private lemma hatMap_zero (m : ℕ) (k : Fin (2 ^ m)) :
    hatMap m k ⟨0, by constructor <;> norm_num⟩ = 0 := by
  apply hat_eq_zero_of_nonpos
  simp

private lemma hatMap_one (m : ℕ) (k : Fin (2 ^ m)) :
    hatMap m k ⟨1, by constructor <;> norm_num⟩ = 0 := by
  apply hat_eq_zero_of_one_le
  have hkR : ((k : ℕ) : ℝ) + 1 ≤ ((2 ^ m : ℕ) : ℝ) := by
    exact_mod_cast (Nat.succ_le_iff.mpr k.isLt)
  norm_num only [one_mul]
  linarith

private lemma bridgeLevel_zero (j m : ℕ) (omega : GaussianSample) :
    bridgeLevel j m omega ⟨0, by constructor <;> norm_num⟩ = 0 := by
  simp [bridgeLevel, hatMap, hat]

private lemma bridgeLevel_one (j m : ℕ) (omega : GaussianSample) :
    bridgeLevel j m omega ⟨1, by constructor <;> norm_num⟩ = 0 := by
  unfold bridgeLevel
  rw [ContinuousMap.sum_apply]
  apply Finset.sum_eq_zero
  intro k hk
  rw [ContinuousMap.smul_apply, hatMap_one]
  simp

private lemma continuous_unitPartial (j N : ℕ) :
    Continuous (fun omega : GaussianSample ↦ unitPartial j N omega) := by
  unfold unitPartial affineMap bridgeLevel
  apply Continuous.add
  · exact (continuous_coordinate _).smul continuous_const
  · apply continuous_finset_sum
    intro m _hm
    apply continuous_finset_sum
    intro k _hk
    exact (continuous_const.mul (continuous_coordinate _)).smul continuous_const

private lemma unitPartial_tendsto_unitBlock {omega : GaussianSample}
    (homega : GoodSample omega) (j : ℕ) :
    Tendsto (fun N ↦ unitPartial j N omega) atTop (𝓝 (unitBlock j omega)) := by
  let L := ContinuousMap.linearIsometryBoundedOfCompact unitInterval ℝ ℝ
  have hsum : HasSum (fun m ↦ boundedBridgeLevel j m omega)
      (∑' m, boundedBridgeLevel j m omega) :=
    (summable_boundedBridgeLevel_of_good homega j).hasSum
  have hpartial : Tendsto
      (fun N ↦ ∑ m ∈ Finset.range N, boundedBridgeLevel j m omega)
      atTop (𝓝 (∑' m, boundedBridgeLevel j m omega)) := by
    simpa only [Finset.sum_range] using! hsum.tendsto_sum_nat
  have hL : Tendsto
      (fun N ↦ L (unitPartial j N omega)) atTop
      (𝓝 (L (unitBlock j omega))) := by
    simpa [L, unitPartial, unitBlock, bridgeSum, boundedBridgeLevel,
      map_add, map_sum] using!
      (Tendsto.const_add (L (affineMap j omega)) hpartial)
  have hL' : Tendsto
      (fun N ↦ ContinuousMap.isometryEquivBoundedOfCompact unitInterval ℝ
        (unitPartial j N omega)) atTop
      (𝓝 (ContinuousMap.isometryEquivBoundedOfCompact unitInterval ℝ
        (unitBlock j omega))) := by
    simpa [L] using! hL
  simpa using!
    ((ContinuousMap.isometryEquivBoundedOfCompact unitInterval ℝ).symm.continuous.tendsto
      (ContinuousMap.isometryEquivBoundedOfCompact unitInterval ℝ (unitBlock j omega))).comp hL'

/-- On each unit interval the uniformly summed bridge block is an almost
everywhere measurable function of the Gaussian product sample.  This is the
measurability input for the eventual global sample-to-path map. -/
theorem aeMeasurable_unitBlock (j : ℕ) :
    AEMeasurable (unitBlock j) gaussianSource := by
  apply aemeasurable_of_tendsto_metrizable_ae atTop
      (fun N ↦ (continuous_unitPartial j N).measurable.aemeasurable)
  filter_upwards [ae_goodSample] with omega homega
  exact unitPartial_tendsto_unitBlock homega j

private lemma bridgeSum_zero {omega : GaussianSample} (homega : GoodSample omega)
    (j : ℕ) :
    bridgeSum j omega ⟨0, by constructor <;> norm_num⟩ = 0 := by
  change bcfEval ⟨0, by constructor <;> norm_num⟩
      (∑' m, boundedBridgeLevel j m omega) = 0
  rw [(bcfEval ⟨0, by constructor <;> norm_num⟩).map_tsum
    (summable_boundedBridgeLevel_of_good homega j)]
  have hz : (fun m ↦ bcfEval ⟨0, by constructor <;> norm_num⟩
      (boundedBridgeLevel j m omega)) = fun _ ↦ 0 := by
    funext m
    change bridgeLevel j m omega ⟨0, by constructor <;> norm_num⟩ = 0
    exact bridgeLevel_zero j m omega
  rw [hz, tsum_zero]

private lemma unitBlock_zero {omega : GaussianSample} (homega : GoodSample omega)
    (j : ℕ) :
    unitBlock j omega ⟨0, by constructor <;> norm_num⟩ = 0 := by
  rw [unitBlock, ContinuousMap.add_apply, bridgeSum_zero homega j]
  simp [affineMap]

private lemma continuous_tsum_of_locallyFinite_support
    {X : Type*} [TopologicalSpace X] {f : ℕ → X → ℝ}
    (hf : ∀ n, Continuous (f n))
    (hlf : LocallyFinite fun n ↦ Function.support (f n)) :
    Continuous fun x ↦ ∑' n, f n x := by
  rw [continuous_iff_continuousAt]
  intro x
  rcases hlf.exists_finset_nhds_support_subset
      (U := fun _ ↦ Set.univ) (fun _ ↦ Set.subset_univ _) (fun _ ↦ isOpen_univ) x with
    ⟨s, n, hn, _hnU, hs⟩
  have heq : (fun y ↦ ∑' i, f i y) =ᶠ[𝓝 x]
      (fun y ↦ ∑ i ∈ s, f i y) := by
    filter_upwards [hn] with y hy
    exact tsum_eq_sum' (hs y hy)
  exact (continuous_finset_sum s fun i _ ↦ hf i).continuousAt.congr_of_eventuallyEq heq

private def unitCoord (j : ℕ) : C(NNReal, unitInterval) where
  toFun t := ⟨max 0 (min ((t : ℝ) - (j : ℝ)) 1), by
    constructor
    · exact le_max_left _ _
    · exact max_le (by norm_num) (min_le_right _ _)⟩
  continuous_toFun := Continuous.subtype_mk
    (continuous_const.max
      ((continuous_subtype_val.sub continuous_const).min continuous_const)) _

private lemma unitCoord_eq_zero_of_le (j : ℕ) {t : NNReal} (ht : t ≤ j) :
    unitCoord j t = 0 := by
  ext
  have ht' : (t : ℝ) ≤ (j : ℝ) := by exact_mod_cast ht
  have hsub : (t : ℝ) - (j : ℝ) ≤ 0 := sub_nonpos.mpr ht'
  change max 0 (min ((t : ℝ) - (j : ℝ)) 1) = 0
  exact max_eq_left (le_trans (min_le_left _ _) hsub)

private lemma unitCoord_eq_one_of_succ_le (j : ℕ) {t : NNReal}
    (ht : (j + 1 : ℕ) ≤ t) : unitCoord j t = 1 := by
  ext
  have ht' : ((j + 1 : ℕ) : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
  have hsub : 1 ≤ (t : ℝ) - (j : ℝ) := by
    push_cast at ht'
    linarith
  change max 0 (min ((t : ℝ) - (j : ℝ)) 1) = 1
  rw [min_eq_right hsub]
  norm_num

private def blockContribution (f : ℕ → C(unitInterval, ℝ)) (j : ℕ) :
    C(NNReal, ℝ) := (f j).comp (unitCoord j)

private lemma locallyFinite_Ici_nat :
    LocallyFinite (fun j : ℕ ↦ Set.Ici (j : NNReal)) := by
  intro t
  refine ⟨Set.Iio (t + 1), Iio_mem_nhds (lt_add_one t), ?_⟩
  apply Set.Finite.subset (Set.finite_Iic (Nat.floor (t + 1)))
  intro j hj
  rcases hj with ⟨x, hxj, hxt⟩
  rw [Set.mem_Iic]
  exact Nat.le_floor (le_of_lt (hxj.trans_lt hxt))

private lemma locallyFinite_block_support (f : ℕ → C(unitInterval, ℝ))
    (hzero : ∀ j, f j 0 = 0) :
    LocallyFinite fun j ↦ Function.support (blockContribution f j) := by
  apply locallyFinite_Ici_nat.subset
  intro j t ht
  rw [Function.mem_support] at ht
  rw [Set.mem_Ici]
  by_contra hj
  have hcoord : unitCoord j t = 0 :=
    unitCoord_eq_zero_of_le j (le_of_not_ge hj)
  exact ht (by simp [blockContribution, hcoord, hzero])

private def assembleUnitBlocks (f : ℕ → C(unitInterval, ℝ))
    (hzero : ∀ j, f j 0 = 0) : C(NNReal, ℝ) where
  toFun t := ∑' j, blockContribution f j t
  continuous_toFun := continuous_tsum_of_locallyFinite_support
    (fun j ↦ (blockContribution f j).continuous)
    (locallyFinite_block_support f hzero)

/-- The time obtained by placing `x ∈ [0,1]` in unit interval `j`. -/
def unitTime (j : ℕ) (x : unitInterval) : NNReal :=
  NNReal.mk ((j : ℝ) + (x : ℝ)) (add_nonneg (Nat.cast_nonneg j) x.property.1)

private lemma unitCoord_unitTime_self (j : ℕ) (x : unitInterval) :
    unitCoord j (unitTime j x) = x := by
  ext
  change max 0 (min (((j : ℝ) + (x : ℝ)) - (j : ℝ)) 1) = (x : ℝ)
  rw [show ((j : ℝ) + (x : ℝ)) - (j : ℝ) = (x : ℝ) by ring]
  rw [min_eq_left x.property.2, max_eq_right x.property.1]

private lemma assembleUnitBlocks_unitTime (f : ℕ → C(unitInterval, ℝ))
    (hzero : ∀ j, f j 0 = 0) (j : ℕ) (x : unitInterval) :
    assembleUnitBlocks f hzero (unitTime j x) =
      (∑ l ∈ Finset.range j, f l 1) + f j x := by
  change (∑' l, blockContribution f l (unitTime j x)) = _
  rw [tsum_eq_sum', Finset.sum_range_succ]
  · congr 1
    · apply Finset.sum_congr rfl
      intro l hl
      have hlj : l + 1 ≤ j := Nat.succ_le_iff.mpr (Finset.mem_range.mp hl)
      simp only [blockContribution, ContinuousMap.comp_apply]
      rw [unitCoord_eq_one_of_succ_le l]
      change ((l + 1 : ℕ) : ℝ) ≤ (j : ℝ) + (x : ℝ)
      exact (by exact_mod_cast hlj : ((l + 1 : ℕ) : ℝ) ≤ (j : ℝ)).trans
        (le_add_of_nonneg_right x.property.1)
    · simp [blockContribution, unitCoord_unitTime_self]
  · intro l hl
    rw [Function.mem_support] at hl
    rw [Finset.mem_coe, Finset.mem_range]
    by_contra hlj
    have hjl : j + 1 ≤ l := Nat.add_one_le_iff.mpr (Nat.le_of_not_gt hlj)
    have htime : unitTime j x ≤ l := by
      change (j : ℝ) + (x : ℝ) ≤ (l : ℝ)
      calc
        (j : ℝ) + (x : ℝ) ≤ (j : ℝ) + 1 := by
          gcongr
          exact x.property.2
        _ = ((j + 1 : ℕ) : ℝ) := by push_cast; ring
        _ ≤ (l : ℝ) := by exact_mod_cast hjl
    have hcoord : unitCoord l (unitTime j x) = 0 :=
      unitCoord_eq_zero_of_le l htime
    exact hl (by simp [blockContribution, hcoord, hzero])

/-- Compact summability of every bridge block assembles the countable product
sample into one globally continuous path, with the exact affine-plus-bridge
formula on every unit interval. -/
private lemma bridgeSum_zero_all (j : ℕ) (omega : GaussianSample) :
    bridgeSum j omega ⟨0, by constructor <;> norm_num⟩ = 0 := by
  by_cases hsum : Summable fun m ↦ boundedBridgeLevel j m omega
  · change bcfEval ⟨0, by constructor <;> norm_num⟩
        (∑' m, boundedBridgeLevel j m omega) = 0
    rw [(bcfEval ⟨0, by constructor <;> norm_num⟩).map_tsum hsum]
    have hz : (fun m ↦ bcfEval ⟨0, by constructor <;> norm_num⟩
        (boundedBridgeLevel j m omega)) = fun _ ↦ 0 := by
      funext m
      change bridgeLevel j m omega ⟨0, by constructor <;> norm_num⟩ = 0
      exact bridgeLevel_zero j m omega
    rw [hz, tsum_zero]
  · rw [bridgeSum, tsum_eq_zero_of_not_summable hsum]
    rfl

private lemma bridgeSum_one_all (j : ℕ) (omega : GaussianSample) :
    bridgeSum j omega ⟨1, by constructor <;> norm_num⟩ = 0 := by
  by_cases hsum : Summable fun m ↦ boundedBridgeLevel j m omega
  · change bcfEval ⟨1, by constructor <;> norm_num⟩
        (∑' m, boundedBridgeLevel j m omega) = 0
    rw [(bcfEval ⟨1, by constructor <;> norm_num⟩).map_tsum hsum]
    have hz : (fun m ↦ bcfEval ⟨1, by constructor <;> norm_num⟩
        (boundedBridgeLevel j m omega)) = fun _ ↦ 0 := by
      funext m
      change bridgeLevel j m omega ⟨1, by constructor <;> norm_num⟩ = 0
      exact bridgeLevel_one j m omega
    rw [hz, tsum_zero]
  · rw [bridgeSum, tsum_eq_zero_of_not_summable hsum]
    rfl

private lemma unitBlock_zero_all (j : ℕ) (omega : GaussianSample) :
    unitBlock j omega ⟨0, by constructor <;> norm_num⟩ = 0 := by
  rw [unitBlock, ContinuousMap.add_apply, bridgeSum_zero_all]
  simp [affineMap]

private lemma unitBlock_one_all (j : ℕ) (omega : GaussianSample) :
    unitBlock j omega ⟨1, by constructor <;> norm_num⟩ =
      coordinate (j, Sum.inl ()) omega := by
  rw [unitBlock, ContinuousMap.add_apply, bridgeSum_one_all]
  simp [affineMap]

/-- The canonical global continuous path associated with every Gaussian
sample.  On the almost-sure good set this is the locally uniformly convergent
Lévy--Ciesielski path; on a nonsummable unit block Lean's `tsum` convention
uses the zero bridge sum. -/
def globalPath (omega : GaussianSample) : BrownianPath :=
  assembleUnitBlocks (fun j ↦ unitBlock j omega) (fun j ↦ unitBlock_zero_all j omega)

@[simp] theorem globalPath_zero (omega : GaussianSample) : globalPath omega 0 = 0 := by
  have h := assembleUnitBlocks_unitTime
    (fun j ↦ unitBlock j omega) (fun j ↦ unitBlock_zero_all j omega)
      0 (0 : unitInterval)
  simp only [Finset.range_zero, Finset.sum_empty, zero_add] at h
  have hz : unitBlock 0 omega (0 : unitInterval) = 0 := unitBlock_zero_all 0 omega
  rw [hz] at h
  simpa [globalPath, unitTime] using! h

theorem globalPath_unitTime (omega : GaussianSample) (j : ℕ) (x : unitInterval) :
    globalPath omega (unitTime j x) =
      (∑ l ∈ Finset.range j, coordinate (l, Sum.inl ()) omega) + unitBlock j omega x := by
  rw [globalPath, assembleUnitBlocks_unitTime]
  congr 1
  apply Finset.sum_congr rfl
  intro l _hl
  exact unitBlock_one_all l omega

private def unitFraction (t : NNReal) : unitInterval :=
  ⟨(t : ℝ) - (⌊(t : ℝ)⌋₊ : ℝ), by
    constructor
    · exact sub_nonneg.mpr (Nat.floor_le t.property)
    · have ht := Nat.lt_floor_add_one (t : ℝ)
      linarith⟩

private lemma unitTime_floor_unitFraction (t : NNReal) :
    unitTime ⌊(t : ℝ)⌋₊ (unitFraction t) = t := by
  ext
  simp [unitTime, unitFraction]

/-- Evaluation on a fixed countable dense sequence.  This realizes the Borel
space of continuous paths as a measurable subspace of a countable product. -/
def denseEval (w : BrownianPath) : ℕ → ℝ :=
  fun n ↦ w (TopologicalSpace.denseSeq NNReal n)

lemma measurable_denseEval : Measurable denseEval := by
  apply measurable_pi_lambda
  intro n
  exact (ContinuousEvalConst.continuous_eval_const
    (TopologicalSpace.denseSeq NNReal n)).measurable

private lemma injective_denseEval : Function.Injective denseEval := by
  intro w v hwv
  apply ContinuousMap.ext
  have heq : (w : NNReal → ℝ) = (v : NNReal → ℝ) :=
    (TopologicalSpace.denseRange_denseSeq NNReal).equalizer
      w.continuous v.continuous (by simpa [denseEval] using! hwv)
  exact congrFun heq

lemma measurableEmbedding_denseEval : MeasurableEmbedding denseEval :=
  measurable_denseEval.measurableEmbedding injective_denseEval

theorem aeMeasurable_globalPath_eval (t : NNReal) :
    AEMeasurable (fun omega ↦ globalPath omega t) gaussianSource := by
  let j : ℕ := ⌊(t : ℝ)⌋₊
  let x : unitInterval := unitFraction t
  have ht : unitTime j x = t := by
    simpa [j, x] using! unitTime_floor_unitFraction t
  have heq : (fun omega ↦ globalPath omega t) =
      fun omega ↦
        (∑ l ∈ Finset.range j, coordinate (l, Sum.inl ()) omega) +
          unitBlock j omega x := by
    funext omega
    rw [← ht, globalPath_unitTime]
  rw [heq]
  have hsum : Measurable (fun omega : GaussianSample ↦
      ∑ l ∈ Finset.range j, coordinate (l, Sum.inl ()) omega) := by
    exact Finset.measurable_fun_sum (Finset.range j) fun l _hl ↦
      measurable_coordinate (l, Sum.inl ())
  have hblock : AEMeasurable (fun omega : GaussianSample ↦ unitBlock j omega x)
      gaussianSource :=
    (ContinuousEvalConst.continuous_eval_const x).measurable.comp_aemeasurable
      (aeMeasurable_unitBlock j)
  exact hsum.aemeasurable.add hblock

/-- The globally assembled Lévy--Ciesielski sample path is measurable modulo
the null set on which one of the bridge series is not summable. -/
theorem aeMeasurable_globalPath : AEMeasurable globalPath gaussianSource := by
  apply measurableEmbedding_denseEval.aemeasurable_comp_iff.mp
  apply aemeasurable_pi_lambda
  intro n
  simpa [denseEval, Function.comp_def] using!
    aeMeasurable_globalPath_eval (TopologicalSpace.denseSeq NNReal n)

/-- The concrete continuous-path law obtained by pushing the countable
Gaussian product source through the globally assembled path map. -/
def brownianCandidate : PathLaw :=
  Measure.map globalPath gaussianSource

instance : IsProbabilityMeasure brownianCandidate :=
  Measure.isProbabilityMeasure_map aeMeasurable_globalPath

theorem brownianCandidate_start_zero :
    brownianCandidate {w | w 0 = 0} = 1 := by
  have hset : MeasurableSet {w : BrownianPath | w 0 = 0} :=
    show MeasurableSet
      ((fun w : BrownianPath ↦ w 0) ⁻¹' ({0} : Set ℝ)) from
      MeasurableSet.preimage (measurableSet_singleton 0)
        (ContinuousEvalConst.continuous_eval_const (0 : NNReal)).measurable
  rw [brownianCandidate,
    Measure.map_apply_of_aemeasurable aeMeasurable_globalPath hset]
  rw [show globalPath ⁻¹' {w : BrownianPath | w 0 = 0} = Set.univ by
    ext omega
    simp]
  exact measure_univ

/-- Any finite injective selection of the product coordinates has the exact
standard Gaussian product law.  This is the reusable source-side input for
the dyadic bridge refinements. -/
def coordinateVector {ι : Type*} (c : ι → GaussianCoordinate) :
    GaussianSample → ι → ℝ :=
  fun omega i ↦ coordinate (c i) omega

theorem coordinateVector_hasGaussianLaw {ι : Type*} [Fintype ι]
    (c : ι → GaussianCoordinate) (hc : Function.Injective c) :
    HasGaussianLaw (coordinateVector c) gaussianSource := by
  apply iIndepFun.hasGaussianLaw
    (hX2 := iIndepFun.precomp hc independent_coordinates)
  intro i
  refine ⟨(measurable_coordinate (c i)).aemeasurable, ?_⟩
  simpa only [coordinate_law] using!
    (show IsGaussian (gaussianReal 0 1) by infer_instance)

private abbrev UnitPartialCoordinate (N : ℕ) :=
  Unit ⊕ Sigma fun m : Fin N ↦ Fin (2 ^ (m : ℕ))

private def unitPartialCoordinate (j N : ℕ) :
    UnitPartialCoordinate N → GaussianCoordinate
  | Sum.inl _ => (j, Sum.inl ())
  | Sum.inr ⟨m, k⟩ => (j, Sum.inr ⟨(m : ℕ), k⟩)

private lemma injective_unitPartialCoordinate (j N : ℕ) :
    Function.Injective (unitPartialCoordinate j N) := by
  rintro (u | ⟨m, k⟩) (v | ⟨n, l⟩) h
  · rfl
  · simp [unitPartialCoordinate] at h
  · simp [unitPartialCoordinate] at h
  · simp only [unitPartialCoordinate, Prod.mk.injEq, true_and, Sum.inr.injEq,
      Sigma.mk.injEq] at h
    rcases h with ⟨hmn, hkl⟩
    have hmn' : m = n := Fin.ext hmn
    subst n
    cases hkl
    rfl

private def unitPartialEvalLinear (N : ℕ) (x : unitInterval) :
    (UnitPartialCoordinate N → ℝ) →L[ℝ] ℝ where
  toFun z := z (Sum.inl ()) * (x : ℝ) +
    ∑ m : Fin N, ∑ k : Fin (2 ^ (m : ℕ)),
      (hatScale m * z (Sum.inr ⟨m, k⟩)) * hatMap m k x
  map_add' z y := by
    dsimp
    simp only [mul_add, add_mul, Finset.sum_add_distrib]
    ring
  map_smul' a z := by
    dsimp
    rw [mul_add]
    congr 1
    · ring
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m _hm
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _hk
      ring
  cont := by fun_prop

private lemma unitPartial_apply_eq_linear (j N : ℕ) (omega : GaussianSample)
    (x : unitInterval) :
    unitPartial j N omega x =
      unitPartialEvalLinear N x
        (coordinateVector (unitPartialCoordinate j N) omega) := by
  unfold unitPartial unitPartialEvalLinear affineMap bridgeLevel
  rw [ContinuousMap.add_apply, ContinuousMap.sum_apply]
  change coordinate (j, Sum.inl ()) omega * (x : ℝ) +
      ∑ i ∈ Finset.range N,
        (∑ k : Fin (2 ^ i),
          (hatScale i * coordinate (j, Sum.inr ⟨i, k⟩) omega) • hatMap i k) x =
    coordinate (j, Sum.inl ()) omega * (x : ℝ) +
      ∑ m : Fin N, ∑ k : Fin (2 ^ (m : ℕ)),
        (hatScale m * coordinate (j, Sum.inr ⟨(m : ℕ), k⟩) omega) * hatMap m k x
  simp_rw [ContinuousMap.sum_apply, ContinuousMap.smul_apply, smul_eq_mul]
  congr 1
  symm
  exact Fin.sum_univ_eq_sum_range (fun m : ℕ ↦
    ∑ k : Fin (2 ^ m),
      hatScale m * coordinate (j, Sum.inr ⟨m, k⟩) omega * hatMap m k x) N

theorem unitPartial_eval_hasGaussianLaw (j N : ℕ) (x : unitInterval) :
    HasGaussianLaw (fun omega ↦ unitPartial j N omega x) gaussianSource := by
  have hcoord := coordinateVector_hasGaussianLaw (unitPartialCoordinate j N)
    (injective_unitPartialCoordinate j N)
  have hmap := hcoord.map (unitPartialEvalLinear N x)
  apply hmap.congr
  filter_upwards with omega
  exact (unitPartial_apply_eq_linear j N omega x).symm

private def unitPartialEvalVectorLinear (N r : ℕ) (x : Fin r → unitInterval) :
    (UnitPartialCoordinate N → ℝ) →L[ℝ] Fin r → ℝ where
  toFun z q := unitPartialEvalLinear N (x q) z
  map_add' z y := by
    ext q
    exact (unitPartialEvalLinear N (x q)).map_add z y
  map_smul' a z := by
    ext q
    exact (unitPartialEvalLinear N (x q)).map_smul a z
  cont := by fun_prop

theorem unitPartial_evalVector_hasGaussianLaw (j N r : ℕ)
    (x : Fin r → unitInterval) :
    HasGaussianLaw (fun omega q ↦ unitPartial j N omega (x q)) gaussianSource := by
  have hcoord := coordinateVector_hasGaussianLaw (unitPartialCoordinate j N)
    (injective_unitPartialCoordinate j N)
  have hmap := hcoord.map (unitPartialEvalVectorLinear N r x)
  apply hmap.congr
  filter_upwards with omega
  funext q
  exact (unitPartial_apply_eq_linear j N omega (x q)).symm

private def dyadicPoint (N : ℕ) (k : Fin (2 ^ N + 1)) : unitInterval :=
  ⟨(k : ℝ) / (2 ^ N : ℕ), by
    constructor
    · positivity
    · rw [div_le_one (by positivity : (0 : ℝ) < (2 ^ N : ℕ))]
      exact_mod_cast Nat.le_of_lt_succ k.isLt⟩

private def dyadicLeft (N : ℕ) (k : Fin (2 ^ N)) : Fin (2 ^ N + 1) :=
  ⟨k, lt_trans k.isLt (Nat.lt_succ_self _)⟩

private def dyadicRight (N : ℕ) (k : Fin (2 ^ N)) : Fin (2 ^ N + 1) :=
  ⟨k + 1, Nat.succ_lt_succ k.isLt⟩

private def dyadicDifferenceLinear (N : ℕ) :
    (Fin (2 ^ N + 1) → ℝ) →L[ℝ] Fin (2 ^ N) → ℝ where
  toFun z k := z (dyadicRight N k) - z (dyadicLeft N k)
  map_add' z y := by ext; simp; ring
  map_smul' a z := by ext; simp; ring
  cont := by fun_prop

private def dyadicIncrementVector (j N : ℕ) :
    GaussianSample → Fin (2 ^ N) → ℝ :=
  fun omega k ↦ unitPartial j N omega (dyadicPoint N (dyadicRight N k)) -
    unitPartial j N omega (dyadicPoint N (dyadicLeft N k))

theorem dyadicIncrementVector_hasGaussianLaw (j N : ℕ) :
    HasGaussianLaw (dyadicIncrementVector j N) gaussianSource := by
  have heval := unitPartial_evalVector_hasGaussianLaw j N (2 ^ N + 1)
    (dyadicPoint N)
  have hmap := heval.map (dyadicDifferenceLinear N)
  apply hmap.congr
  filter_upwards with omega
  rfl

private def dyadicMidpoint (N : ℕ) (k : Fin (2 ^ N)) : unitInterval :=
  ⟨((k : ℝ) + 1 / 2) / (2 ^ N : ℕ), by
    constructor
    · positivity
    · rw [div_le_one (by positivity : (0 : ℝ) < (2 ^ N : ℕ))]
      have hk : (k : ℕ) + 1 ≤ 2 ^ N := k.isLt
      exact_mod_cast (show (k : ℝ) + 1 / 2 ≤ (2 ^ N : ℕ) by
        exact (by exact_mod_cast hk : (k : ℝ) + 1 ≤ (2 ^ N : ℕ)).trans'
          (by linarith))⟩

private lemma hatMap_dyadicPoint (N : ℕ) (k : Fin (2 ^ N + 1))
    (l : Fin (2 ^ N)) :
    hatMap N l (dyadicPoint N k) = 0 := by
  change hat (((2 ^ N : ℕ) : ℝ) * ((k : ℝ) / (2 ^ N : ℕ)) - (l : ℕ)) = 0
  have hpow : (((2 ^ N : ℕ) : ℝ)) ≠ 0 := by positivity
  rw [show (((2 ^ N : ℕ) : ℝ) * ((k : ℝ) / (2 ^ N : ℕ)) - (l : ℕ)) =
      (k : ℝ) - (l : ℝ) by field_simp]
  by_cases hlk : (l : ℕ) < (k : ℕ)
  · apply hat_eq_zero_of_one_le
    have hstep : (l : ℝ) + 1 ≤ (k : ℝ) := by
      exact_mod_cast (Nat.succ_le_iff.mpr hlk)
    linarith
  · apply hat_eq_zero_of_nonpos
    have hstep : (k : ℝ) ≤ (l : ℝ) := by
      exact_mod_cast (Nat.le_of_not_gt hlk)
    linarith

private lemma hatMap_dyadicMidpoint_self (N : ℕ) (k : Fin (2 ^ N)) :
    hatMap N k (dyadicMidpoint N k) = 1 := by
  change hat (((2 ^ N : ℕ) : ℝ) *
    (((k : ℝ) + 1 / 2) / (2 ^ N : ℕ)) - (k : ℕ)) = 1
  have hpow : (((2 ^ N : ℕ) : ℝ)) ≠ 0 := by positivity
  rw [show (((2 ^ N : ℕ) : ℝ) *
      (((k : ℝ) + 1 / 2) / (2 ^ N : ℕ)) - (k : ℕ)) = 1 / 2 by
        field_simp
        ring]
  change max 0 (min (2 * (1 / 2 : ℝ)) (2 - 2 * (1 / 2 : ℝ))) = 1
  norm_num only [one_div, Nat.cast_ofNat, mul_inv_cancel₀, OfNat.ofNat_ne_zero,
    sub_self]
  apply le_antisymm
  · exact max_le zero_le_one (le_trans (min_le_left _ _) le_rfl)
  · exact le_max_of_le_right (le_min le_rfl le_rfl)

private lemma hatMap_dyadicMidpoint_ne (N : ℕ) (k l : Fin (2 ^ N))
    (hlk : l ≠ k) :
    hatMap N l (dyadicMidpoint N k) = 0 := by
  apply hat_translate_disjoint
      (a := ((2 ^ N : ℕ) : ℝ) * (dyadicMidpoint N k : ℝ))
      (k := (k : ℕ)) (l := (l : ℕ))
  · intro hval
    exact hlk (Fin.ext hval.symm)
  · simpa [hatMap] using!
      (show hat (((2 ^ N : ℕ) : ℝ) * (dyadicMidpoint N k : ℝ) - (k : ℕ)) ≠ 0 by
        rw [show (((2 ^ N : ℕ) : ℝ) * (dyadicMidpoint N k : ℝ) - (k : ℕ)) =
          1 / 2 by
            change (((2 ^ N : ℕ) : ℝ) *
              (((k : ℝ) + 1 / 2) / (2 ^ N : ℕ)) - (k : ℕ)) = 1 / 2
            field_simp
            ring]
        change max 0 (min (2 * (1 / 2 : ℝ)) (2 - 2 * (1 / 2 : ℝ))) ≠ 0
        norm_num only [one_div, Nat.cast_ofNat, mul_inv_cancel₀, OfNat.ofNat_ne_zero,
          sub_self]
        intro hzero
        have hpos : (0 : ℝ) < max 0 (min 1 1) :=
          zero_lt_one.trans_le (le_max_of_le_right (le_min le_rfl le_rfl))
        exact (ne_of_gt hpos) hzero)

private lemma bridgeLevel_dyadicPoint (j N : ℕ) (omega : GaussianSample)
    (k : Fin (2 ^ N + 1)) :
    bridgeLevel j N omega (dyadicPoint N k) = 0 := by
  unfold bridgeLevel
  rw [ContinuousMap.sum_apply]
  apply Finset.sum_eq_zero
  intro l _hl
  rw [ContinuousMap.smul_apply, hatMap_dyadicPoint]
  simp

private lemma bridgeLevel_dyadicMidpoint (j N : ℕ) (omega : GaussianSample)
    (k : Fin (2 ^ N)) :
    bridgeLevel j N omega (dyadicMidpoint N k) =
      hatScale N * coordinate (j, Sum.inr ⟨N, k⟩) omega := by
  unfold bridgeLevel
  rw [ContinuousMap.sum_apply, Finset.sum_eq_single k]
  · rw [ContinuousMap.smul_apply, hatMap_dyadicMidpoint_self, smul_eq_mul, mul_one]
  · intro l _hl hlk
    rw [ContinuousMap.smul_apply, hatMap_dyadicMidpoint_ne N k l hlk]
    simp
  · simp

private lemma hat_eq_two_mul {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    hat x = 2 * x := by
  unfold hat
  rw [min_eq_left (by linarith), max_eq_right (by positivity)]

private lemma hat_eq_two_sub {x : ℝ} (hx0 : 1 / 2 ≤ x) (hx1 : x ≤ 1) :
    hat x = 2 - 2 * x := by
  unfold hat
  rw [min_eq_right (by linarith), max_eq_right (by linarith)]

/-! Every coarser Faber--Schauder hat is affine on a level-`N` dyadic cell.
The proof normalizes the cell by the integral scale `D = 2^(N-m)` and splits
at the support endpoints and midpoint, all of which are grid points. -/
private lemma hatMap_dyadicMidpoint_average {m N : ℕ} (hmN : m < N)
    (l : Fin (2 ^ m)) (k : Fin (2 ^ N)) :
    hatMap m l (dyadicMidpoint N k) =
      (hatMap m l (dyadicPoint N (dyadicLeft N k)) +
        hatMap m l (dyadicPoint N (dyadicRight N k))) / 2 := by
  obtain ⟨d, hNd⟩ : ∃ d, N = m + 1 + d := by
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (Nat.succ_le_iff.mpr hmN)
    exact ⟨d, by omega⟩
  subst N
  let D : ℕ := 2 ^ (d + 1)
  let H : ℕ := 2 ^ d
  let L : ℕ := (l : ℕ) * D
  have hD : D = 2 * H := by
    simp [D, H, pow_succ, mul_comm]
  have hDR : (0 : ℝ) < D := by positivity
  have hDreal : (D : ℝ) = 2 * (H : ℝ) := by exact_mod_cast hD
  let a0 : ℝ := ((k : ℝ) - (L : ℝ)) / D
  let ah : ℝ := ((k : ℝ) + 1 / 2 - (L : ℝ)) / D
  let a1 : ℝ := ((k : ℝ) + 1 - (L : ℝ)) / D
  have harg0 : hatMap m l (dyadicPoint (m + 1 + d) (dyadicLeft (m + 1 + d) k)) =
      hat a0 := by
    simp only [hatMap, dyadicPoint, dyadicLeft, ContinuousMap.coe_mk, Subtype.coe_mk]
    change hat (((2 ^ m : ℕ) : ℝ) *
      ((k : ℝ) / (2 ^ (m + 1 + d) : ℕ)) - (l : ℕ)) = hat a0
    congr 1
    dsimp [a0, L, D]
    norm_num [pow_add, pow_succ]
    field_simp
  have hargh : hatMap m l (dyadicMidpoint (m + 1 + d) k) = hat ah := by
    simp only [hatMap, dyadicMidpoint, ContinuousMap.coe_mk, Subtype.coe_mk]
    change hat (((2 ^ m : ℕ) : ℝ) *
      (((k : ℝ) + 1 / 2) / (2 ^ (m + 1 + d) : ℕ)) - (l : ℕ)) = hat ah
    congr 1
    dsimp [ah, L, D]
    norm_num [pow_add, pow_succ]
    field_simp
  have harg1 : hatMap m l (dyadicPoint (m + 1 + d) (dyadicRight (m + 1 + d) k)) =
      hat a1 := by
    simp only [hatMap, dyadicPoint, dyadicRight, ContinuousMap.coe_mk, Subtype.coe_mk]
    push_cast
    change hat ((2 : ℝ) ^ m *
      (((k : ℝ) + 1) / (2 : ℝ) ^ (m + 1 + d)) - (l : ℝ)) = hat a1
    congr 1
    dsimp [a1, L, D]
    norm_num [pow_add, pow_succ]
    field_simp
  rw [harg0, hargh, harg1]
  by_cases hkL : (k : ℕ) < L
  · have hk1L : (k : ℕ) + 1 ≤ L := by omega
    have ha0 : a0 ≤ 0 := by
      dsimp [a0]
      rw [div_nonpos_iff]
      exact Or.inr ⟨sub_nonpos.mpr (by exact_mod_cast (Nat.le_of_lt hkL)), hDR.le⟩
    have hah : ah ≤ 0 := by
      dsimp [ah]
      rw [div_nonpos_iff]
      right
      constructor
      have : (k : ℝ) + 1 ≤ (L : ℝ) := by exact_mod_cast hk1L
      linarith
      exact hDR.le
    have ha1 : a1 ≤ 0 := by
      dsimp [a1]
      rw [div_nonpos_iff]
      exact Or.inr ⟨sub_nonpos.mpr (by exact_mod_cast hk1L), hDR.le⟩
    rw [hat_eq_zero_of_nonpos ha0, hat_eq_zero_of_nonpos hah,
      hat_eq_zero_of_nonpos ha1]
    ring
  · by_cases hRk : L + D ≤ (k : ℕ)
    · have ha0 : 1 ≤ a0 := by
        dsimp [a0]
        rw [le_div_iff₀ hDR]
        have : (L : ℝ) + (D : ℝ) ≤ (k : ℝ) := by exact_mod_cast hRk
        linarith
      have hah : 1 ≤ ah := ha0.trans (by
        dsimp [a0, ah]
        gcongr
        linarith)
      have ha1 : 1 ≤ a1 := hah.trans (by
        dsimp [ah, a1]
        gcongr
        linarith)
      rw [hat_eq_zero_of_one_le ha0, hat_eq_zero_of_one_le hah,
        hat_eq_zero_of_one_le ha1]
      ring
    · have hLk : L ≤ (k : ℕ) := Nat.le_of_not_gt hkL
      have hkR : (k : ℕ) < L + D := Nat.lt_of_not_ge hRk
      by_cases hkM : (k : ℕ) < L + H
      · have hk1M : (k : ℕ) + 1 ≤ L + H := by omega
        have ha00 : 0 ≤ a0 := by
          dsimp [a0]
          exact div_nonneg (sub_nonneg.mpr (by exact_mod_cast hLk)) hDR.le
        have hah0 : 0 ≤ ah := ha00.trans (by
          dsimp [a0, ah]
          gcongr
          linarith)
        have ha10 : 0 ≤ a1 := hah0.trans (by
          dsimp [ah, a1]
          gcongr
          linarith)
        have ha01 : a0 ≤ 1 / 2 := by
          dsimp [a0]
          apply (div_le_iff₀ hDR).2
          have hkMle : (k : ℕ) ≤ L + H := by omega
          have : (k : ℝ) ≤ (L + H : ℕ) := by exact_mod_cast hkMle
          push_cast at this
          rw [hDreal]
          linarith
        have hah1 : ah ≤ 1 / 2 := by
          dsimp [ah]
          apply (div_le_iff₀ hDR).2
          have : (k : ℝ) + 1 ≤ (L + H : ℕ) := by exact_mod_cast hk1M
          push_cast at this
          rw [hDreal]
          linarith
        have ha11 : a1 ≤ 1 / 2 := by
          dsimp [a1]
          apply (div_le_iff₀ hDR).2
          have : (k : ℝ) + 1 ≤ (L + H : ℕ) := by exact_mod_cast hk1M
          push_cast at this
          rw [hDreal]
          linarith
        rw [hat_eq_two_mul ha00 ha01, hat_eq_two_mul hah0 hah1,
          hat_eq_two_mul ha10 ha11]
        dsimp [a0, ah, a1]
        ring
      · have hMk : L + H ≤ (k : ℕ) := Nat.le_of_not_gt hkM
        have ha01 : 1 / 2 ≤ a0 := by
          dsimp [a0]
          apply (le_div_iff₀ hDR).2
          have : (L + H : ℕ) ≤ (k : ℝ) := by exact_mod_cast hMk
          push_cast at this
          rw [hDreal]
          linarith
        have hah0 : 1 / 2 ≤ ah := ha01.trans (by
          dsimp [a0, ah]
          gcongr
          linarith)
        have ha10 : 1 / 2 ≤ a1 := hah0.trans (by
          dsimp [ah, a1]
          gcongr
          linarith)
        have ha01' : a0 ≤ 1 := by
          dsimp [a0]
          apply (div_le_one hDR).2
          have : (k : ℝ) < (L + D : ℕ) := by exact_mod_cast hkR
          push_cast at this
          linarith
        have hah1 : ah ≤ 1 := by
          dsimp [ah]
          apply (div_le_one hDR).2
          have hk1R : (k : ℕ) + 1 ≤ L + D := by omega
          have : (k : ℝ) + 1 ≤ (L + D : ℕ) := by exact_mod_cast hk1R
          push_cast at this
          linarith
        have ha11 : a1 ≤ 1 := by
          dsimp [a1]
          apply (div_le_one hDR).2
          have hk1R : (k : ℕ) + 1 ≤ L + D := by omega
          have : (k : ℝ) + 1 ≤ (L + D : ℕ) := by exact_mod_cast hk1R
          push_cast at this
          linarith
        rw [hat_eq_two_sub ha01 ha01', hat_eq_two_sub hah0 hah1,
          hat_eq_two_sub ha10 ha11]
        dsimp [a0, ah, a1]
        ring

private lemma bridgeLevel_dyadicMidpoint_average {m N : ℕ} (hmN : m < N)
    (j : ℕ) (omega : GaussianSample) (k : Fin (2 ^ N)) :
    bridgeLevel j m omega (dyadicMidpoint N k) =
      (bridgeLevel j m omega (dyadicPoint N (dyadicLeft N k)) +
        bridgeLevel j m omega (dyadicPoint N (dyadicRight N k))) / 2 := by
  unfold bridgeLevel
  simp_rw [ContinuousMap.sum_apply, ContinuousMap.smul_apply, smul_eq_mul,
    hatMap_dyadicMidpoint_average hmN]
  simp_rw [div_eq_mul_inv]
  ring_nf
  rw [Finset.sum_add_distrib, Finset.sum_mul, Finset.sum_mul]

private lemma unitPartial_dyadicMidpoint_average (j N : ℕ) (omega : GaussianSample)
    (k : Fin (2 ^ N)) :
    unitPartial j N omega (dyadicMidpoint N k) =
      (unitPartial j N omega (dyadicPoint N (dyadicLeft N k)) +
        unitPartial j N omega (dyadicPoint N (dyadicRight N k))) / 2 := by
  have haff : affineMap j omega (dyadicMidpoint N k) =
      (affineMap j omega (dyadicPoint N (dyadicLeft N k)) +
        affineMap j omega (dyadicPoint N (dyadicRight N k))) / 2 := by
    unfold affineMap
    simp only [ContinuousMap.smul_apply, smul_eq_mul, unitLinear_apply]
    simp only [dyadicMidpoint, dyadicPoint, dyadicLeft, dyadicRight, Subtype.coe_mk]
    change coordinate (j, Sum.inl ()) omega *
        (((k : ℝ) + 1 / 2) / (2 ^ N : ℕ)) =
      (coordinate (j, Sum.inl ()) omega * ((k : ℝ) / (2 ^ N : ℕ)) +
        coordinate (j, Sum.inl ()) omega * (((k + 1 : ℕ) : ℝ) / (2 ^ N : ℕ))) / 2
    push_cast
    ring
  have hsum :
      (∑ m ∈ Finset.range N, bridgeLevel j m omega (dyadicMidpoint N k)) =
        ((∑ m ∈ Finset.range N,
            bridgeLevel j m omega (dyadicPoint N (dyadicLeft N k))) +
          (∑ m ∈ Finset.range N,
            bridgeLevel j m omega (dyadicPoint N (dyadicRight N k)))) / 2 := by
    calc
      _ = ∑ m ∈ Finset.range N,
          (bridgeLevel j m omega (dyadicPoint N (dyadicLeft N k)) +
            bridgeLevel j m omega (dyadicPoint N (dyadicRight N k))) / 2 := by
            apply Finset.sum_congr rfl
            intro m hm
            exact bridgeLevel_dyadicMidpoint_average (Finset.mem_range.mp hm) j omega k
      _ = _ := by
        simp_rw [add_div]
        rw [Finset.sum_add_distrib, Finset.sum_div, Finset.sum_div]
  unfold unitPartial
  simp only [ContinuousMap.add_apply, ContinuousMap.sum_apply]
  rw [haff, hsum]
  ring

private lemma unitPartial_succ_apply (j N : ℕ) (omega : GaussianSample)
    (x : unitInterval) :
    unitPartial j (N + 1) omega x =
      unitPartial j N omega x + bridgeLevel j N omega x := by
  unfold unitPartial
  rw [Finset.sum_range_succ]
  simp only [ContinuousMap.add_apply, ContinuousMap.sum_apply]
  ring

private def dyadicChildIncrementVector (j N : ℕ) :
    GaussianSample → (Fin (2 ^ N) × Fin 2) → ℝ :=
  fun omega kb ↦
    if kb.2 = 0 then
      unitPartial j (N + 1) omega (dyadicMidpoint N kb.1) -
        unitPartial j (N + 1) omega (dyadicPoint N (dyadicLeft N kb.1))
    else
      unitPartial j (N + 1) omega (dyadicPoint N (dyadicRight N kb.1)) -
        unitPartial j (N + 1) omega (dyadicMidpoint N kb.1)

private lemma dyadicChildIncrementVector_refinement (j N : ℕ)
    (omega : GaussianSample) (k : Fin (2 ^ N)) (b : Fin 2) :
    dyadicChildIncrementVector j N omega (k, b) =
      dyadicIncrementVector j N omega k / 2 +
        (if b = 0 then 1 else -1) *
          (hatScale N * coordinate (j, Sum.inr ⟨N, k⟩) omega) := by
  have havg := unitPartial_dyadicMidpoint_average j N omega k
  have hleft := unitPartial_succ_apply j N omega
    (dyadicPoint N (dyadicLeft N k))
  have hmid := unitPartial_succ_apply j N omega (dyadicMidpoint N k)
  have hright := unitPartial_succ_apply j N omega
    (dyadicPoint N (dyadicRight N k))
  rw [bridgeLevel_dyadicPoint] at hleft hright
  rw [bridgeLevel_dyadicMidpoint] at hmid
  fin_cases b <;>
    simp only [dyadicChildIncrementVector, Fin.isValue, if_true, if_false,
      one_mul, neg_one_mul] <;>
    rw [hleft, hmid, hright] <;>
    rw [havg] <;>
    dsimp [dyadicIncrementVector] <;>
    ring

private lemma coordinate_hasGaussianLaw (c : GaussianCoordinate) :
    HasGaussianLaw (coordinate c) gaussianSource := by
  refine ⟨(measurable_coordinate c).aemeasurable, ?_⟩
  rw [coordinate_law]
  infer_instance

private lemma coordinate_memLp_two (c : GaussianCoordinate) :
    MemLp (coordinate c) 2 gaussianSource :=
  (coordinate_hasGaussianLaw c).memLp_two

private lemma coordinate_variance (c : GaussianCoordinate) :
    Var[coordinate c; gaussianSource] = 1 := by
  rw [← variance_id_map (measurable_coordinate c).aemeasurable]
  rw [coordinate_law, variance_id_gaussianReal]
  norm_num

private lemma coordinate_covariance (c d : GaussianCoordinate) :
    cov[coordinate c, coordinate d; gaussianSource] = if c = d then 1 else 0 := by
  split_ifs with hcd
  · subst d
    rw [covariance_self (measurable_coordinate c).aemeasurable]
    exact coordinate_variance c
  · exact (independent_coordinates.indepFun hcd).covariance_eq_zero
        (coordinate_memLp_two c) (coordinate_memLp_two d)

private def partialEvalTerm (j m : ℕ) (l : Fin (2 ^ m)) (x : unitInterval) :
    GaussianSample → ℝ :=
  fun omega ↦ (hatScale m * hatMap m l x) * coordinate (j, Sum.inr ⟨m, l⟩) omega

private lemma partialEvalTerm_memLp_two (j m : ℕ) (l : Fin (2 ^ m))
    (x : unitInterval) :
    MemLp (partialEvalTerm j m l x) 2 gaussianSource :=
  (coordinate_memLp_two (j, Sum.inr ⟨m, l⟩)).const_mul _

private lemma unitPartial_eval_repr (j N : ℕ) (x : unitInterval) :
    (fun omega ↦ unitPartial j N omega x) =
      fun omega ↦ (x : ℝ) * coordinate (j, Sum.inl ()) omega +
        ∑ m ∈ Finset.range N, ∑ l : Fin (2 ^ m), partialEvalTerm j m l x omega := by
  funext omega
  unfold unitPartial affineMap bridgeLevel partialEvalTerm
  simp only [ContinuousMap.add_apply, ContinuousMap.sum_apply,
    ContinuousMap.smul_apply, smul_eq_mul, unitLinear_apply, Finset.sum_apply]
  congr 1
  · ring
  · apply Finset.sum_congr rfl
    intro m _hm
    apply Finset.sum_congr rfl
    intro l _hl
    ring

private lemma unitPartial_eval_memLp_two (j N : ℕ) (x : unitInterval) :
    MemLp (fun omega ↦ unitPartial j N omega x) 2 gaussianSource :=
  (unitPartial_eval_hasGaussianLaw j N x).memLp_two

private lemma unitPartial_newCoordinate_covariance_zero (j N : ℕ)
    (x : unitInterval) (k : Fin (2 ^ N)) :
    cov[(fun omega ↦ unitPartial j N omega x),
      coordinate (j, Sum.inr ⟨N, k⟩); gaussianSource] = 0 := by
  rw [unitPartial_eval_repr]
  change cov[((fun omega ↦ (x : ℝ) * coordinate (j, Sum.inl ()) omega) +
      (fun omega ↦ ∑ m ∈ Finset.range N, ∑ l : Fin (2 ^ m),
        partialEvalTerm j m l x omega)),
      coordinate (j, Sum.inr ⟨N, k⟩); gaussianSource] = 0
  have hA : MemLp (fun omega ↦ (x : ℝ) * coordinate (j, Sum.inl ()) omega)
      2 gaussianSource := (coordinate_memLp_two _).const_mul _
  have hB : MemLp (fun omega ↦ ∑ m ∈ Finset.range N,
      ∑ l : Fin (2 ^ m), partialEvalTerm j m l x omega) 2 gaussianSource :=
    memLp_finset_sum _ fun m hm ↦
      memLp_finset_sum _ fun l _hl ↦ partialEvalTerm_memLp_two j m l x
  have hZ := coordinate_memLp_two (j, Sum.inr ⟨N, k⟩)
  rw [covariance_add_left hA hB hZ]
  rw [covariance_const_mul_left, coordinate_covariance]
  simp only [Prod.mk.injEq]
  simp
  rw [covariance_fun_sum_left'
      (fun m hm ↦ memLp_finset_sum _ fun l _hl ↦
        partialEvalTerm_memLp_two j m l x) hZ]
  apply Finset.sum_eq_zero
  intro m hm
  rw [covariance_fun_sum_left (fun l ↦ partialEvalTerm_memLp_two j m l x) hZ]
  apply Finset.sum_eq_zero
  intro l _hl
  unfold partialEvalTerm
  rw [covariance_const_mul_left, coordinate_covariance]
  have hmn : m ≠ N := ne_of_lt (Finset.mem_range.mp hm)
  simp [hmn]

private lemma dyadicIncrement_newCoordinate_covariance_zero (j N : ℕ)
    (k l : Fin (2 ^ N)) :
    cov[(fun omega ↦ dyadicIncrementVector j N omega k),
      coordinate (j, Sum.inr ⟨N, l⟩); gaussianSource] = 0 := by
  unfold dyadicIncrementVector
  change cov[((fun omega ↦ unitPartial j N omega
      (dyadicPoint N (dyadicRight N k))) -
      (fun omega ↦ unitPartial j N omega
        (dyadicPoint N (dyadicLeft N k)))),
      coordinate (j, Sum.inr ⟨N, l⟩); gaussianSource] = 0
  rw [covariance_sub_left]
  · rw [unitPartial_newCoordinate_covariance_zero,
      unitPartial_newCoordinate_covariance_zero, sub_self]
  · exact unitPartial_eval_memLp_two j N _
  · exact unitPartial_eval_memLp_two j N _
  · exact coordinate_memLp_two (j, Sum.inr ⟨N, l⟩)

private def dyadicVariance : ℕ → ℝ
  | 0 => 1
  | N + 1 => dyadicVariance N / 2

private lemma dyadicVariance_pos (N : ℕ) : 0 < dyadicVariance N := by
  induction N with
  | zero => simp [dyadicVariance]
  | succ N ih => simpa only [dyadicVariance] using! div_pos ih (by norm_num : (0 : ℝ) < 2)

private lemma dyadicVariance_eq (N : ℕ) :
    dyadicVariance N = 1 / (2 ^ N : ℕ) := by
  induction N with
  | zero => simp [dyadicVariance]
  | succ N ih =>
      rw [dyadicVariance, ih]
      push_cast
      rw [pow_succ]
      ring

private lemma hatScale_succ (N : ℕ) :
    hatScale (N + 1) = hatScale N * Real.rpow 2 (-1 / 2 : ℝ) := by
  unfold hatScale
  rw [show (-(N + 1 : ℕ) / 2 - 1 : ℝ) =
      (-(N : ℝ) / 2 - 1) + (-1 / 2) by push_cast; ring]
  exact Real.rpow_add (by norm_num) _ _

private lemma rpow_two_neg_half_sq :
    Real.rpow 2 (-1 / 2 : ℝ) * Real.rpow 2 (-1 / 2 : ℝ) = 1 / 2 := by
  calc
    _ = Real.rpow 2 ((-1 / 2 : ℝ) + (-1 / 2 : ℝ)) :=
      (Real.rpow_add (by norm_num : (0 : ℝ) < 2) _ _).symm
    _ = Real.rpow 2 (-1 : ℝ) := by congr 1 <;> ring
    _ = 1 / 2 := by
      exact (Real.rpow_neg_one 2).trans (by norm_num)

private lemma hatScale_sq (N : ℕ) :
    hatScale N * hatScale N = dyadicVariance N / 4 := by
  induction N with
  | zero =>
      unfold hatScale
      norm_num [dyadicVariance, Real.rpow_neg_one]
  | succ N ih =>
      rw [hatScale_succ, dyadicVariance]
      rw [mul_mul_mul_comm, rpow_two_neg_half_sq, ih]
      ring

private lemma coordinate_integral_zero (c : GaussianCoordinate) :
    ∫ omega, coordinate c omega ∂gaussianSource = 0 := by
  calc
    _ = ∫ x : ℝ, id x ∂Measure.map (coordinate c) gaussianSource := by
      simpa using!
        (integral_map (measurable_coordinate c).aemeasurable
          aestronglyMeasurable_id).symm
    _ = 0 := by
      rw [coordinate_law]
      change (∫ x : ℝ, x ∂gaussianReal 0 1) = 0
      rw [integral_id_gaussianReal]

private lemma unitPartial_eval_integral_zero (j N : ℕ) (x : unitInterval) :
    ∫ omega, unitPartial j N omega x ∂gaussianSource = 0 := by
  rw [unitPartial_eval_repr]
  rw [integral_add]
  · have hfirst : (∫ a, (x : ℝ) * coordinate (j, Sum.inl ()) a ∂gaussianSource) = 0 := by
      calc
        _ = (x : ℝ) * ∫ a, coordinate (j, Sum.inl ()) a ∂gaussianSource :=
          integral_const_mul (x : ℝ) (coordinate (j, Sum.inl ()))
        _ = 0 := by rw [coordinate_integral_zero, mul_zero]
    rw [hfirst, zero_add]
    rw [integral_finset_sum]
    · apply Finset.sum_eq_zero
      intro m hm
      rw [integral_finset_sum]
      · apply Finset.sum_eq_zero
        intro l _hl
        unfold partialEvalTerm
        calc
          _ = (hatScale m * hatMap m l x) *
              ∫ a, coordinate (j, Sum.inr ⟨m, l⟩) a ∂gaussianSource :=
            integral_const_mul _ _
          _ = 0 := by rw [coordinate_integral_zero, mul_zero]
      · intro l _hl
        exact (partialEvalTerm_memLp_two j m l x).integrable one_le_two
    · intro m hm
      exact (memLp_finset_sum _ fun l _hl ↦ partialEvalTerm_memLp_two j m l x).integrable
        one_le_two
  · exact (coordinate_memLp_two (j, Sum.inl ())).const_mul _ |>.integrable one_le_two
  · exact memLp_finset_sum _ (fun m hm ↦
      memLp_finset_sum _ fun l _hl ↦ partialEvalTerm_memLp_two j m l x) |>.integrable one_le_two

private lemma dyadicIncrement_integral_zero (j N : ℕ) (k : Fin (2 ^ N)) :
    ∫ omega, dyadicIncrementVector j N omega k ∂gaussianSource = 0 := by
  unfold dyadicIncrementVector
  rw [integral_sub]
  · rw [unitPartial_eval_integral_zero, unitPartial_eval_integral_zero, sub_self]
  · exact (unitPartial_eval_memLp_two j N _).integrable one_le_two
  · exact (unitPartial_eval_memLp_two j N _).integrable one_le_two

private lemma dyadicChild_covariance_of_parent (j N : ℕ)
    (hparent : ∀ k l : Fin (2 ^ N),
      cov[(fun omega ↦ dyadicIncrementVector j N omega k),
        (fun omega ↦ dyadicIncrementVector j N omega l); gaussianSource] =
          if k = l then dyadicVariance N else 0)
    (p q : Fin (2 ^ N) × Fin 2) :
    cov[(fun omega ↦ dyadicChildIncrementVector j N omega p),
      (fun omega ↦ dyadicChildIncrementVector j N omega q); gaussianSource] =
        if p = q then dyadicVariance (N + 1) else 0 := by
  rcases p with ⟨k, b⟩
  rcases q with ⟨l, c⟩
  have hreprk := funext fun omega ↦ dyadicChildIncrementVector_refinement j N omega k b
  have hreprl := funext fun omega ↦ dyadicChildIncrementVector_refinement j N omega l c
  rw [hreprk, hreprl]
  let Xk : GaussianSample → ℝ := fun omega ↦ dyadicIncrementVector j N omega k
  let Xl : GaussianSample → ℝ := fun omega ↦ dyadicIncrementVector j N omega l
  let Zk : GaussianSample → ℝ := fun omega ↦ coordinate (j, Sum.inr ⟨N, k⟩) omega
  let Zl : GaussianSample → ℝ := fun omega ↦ coordinate (j, Sum.inr ⟨N, l⟩) omega
  let sb : ℝ := if b = 0 then 1 else -1
  let sc : ℝ := if c = 0 then 1 else -1
  change cov[((fun omega ↦ Xk omega / 2) +
      (fun omega ↦ sb * (hatScale N * Zk omega))),
    ((fun omega ↦ Xl omega / 2) +
      (fun omega ↦ sc * (hatScale N * Zl omega))); gaussianSource] = _
  have hXk : MemLp Xk 2 gaussianSource :=
    ((dyadicIncrementVector_hasGaussianLaw j N).eval k).memLp_two
  have hXl : MemLp Xl 2 gaussianSource :=
    ((dyadicIncrementVector_hasGaussianLaw j N).eval l).memLp_two
  have hZk : MemLp Zk 2 gaussianSource := coordinate_memLp_two _
  have hZl : MemLp Zl 2 gaussianSource := coordinate_memLp_two _
  have hAk : MemLp (fun omega ↦ Xk omega / 2) 2 gaussianSource := hXk.mul_const _
  have hAl : MemLp (fun omega ↦ Xl omega / 2) 2 gaussianSource := hXl.mul_const _
  have hBk : MemLp (fun omega ↦ sb * (hatScale N * Zk omega)) 2 gaussianSource :=
    (hZk.const_mul _).const_mul _
  have hBl : MemLp (fun omega ↦ sc * (hatScale N * Zl omega)) 2 gaussianSource :=
    (hZl.const_mul _).const_mul _
  rw [covariance_add_left hAk hBk (hAl.add hBl),
    covariance_add_right hAk hAl hBl, covariance_add_right hBk hAl hBl]
  simp_rw [div_eq_mul_inv, covariance_mul_const_left,
    covariance_mul_const_right, covariance_const_mul_left,
    covariance_const_mul_right]
  rw [hparent k l]
  rw [dyadicIncrement_newCoordinate_covariance_zero j N k l]
  rw [covariance_comm, dyadicIncrement_newCoordinate_covariance_zero j N l k]
  rw [coordinate_covariance]
  have hs := hatScale_sq N
  by_cases hkl : k = l
  · subst l
    fin_cases b <;> fin_cases c <;> simp_all [sb, sc, dyadicVariance] <;>
      norm_num at * <;> nlinarith
  · have hpq : (k, b) ≠ (l, c) := by intro h; exact hkl (congrArg Prod.fst h)
    simp [hkl, hpq]

private def dyadicChildEquiv (N : ℕ) :
    Fin (2 ^ N) × Fin 2 ≃ Fin (2 ^ (N + 1)) :=
  finProdFinEquiv.trans (finCongr (by simp [pow_succ]))

private lemma dyadicChild_points (N : ℕ) (k : Fin (2 ^ N)) (b : Fin 2) :
    dyadicPoint (N + 1) (dyadicLeft (N + 1) (dyadicChildEquiv N (k, b))) =
        if b = 0 then dyadicPoint N (dyadicLeft N k) else dyadicMidpoint N k := by
  fin_cases b <;> ext <;>
    simp [dyadicChildEquiv, dyadicLeft, dyadicPoint, dyadicMidpoint,
      finProdFinEquiv, Fin.val_cast, Equiv.trans_apply, finCongr, pow_succ] <;> field_simp <;> ring

private lemma dyadicChild_points_right (N : ℕ) (k : Fin (2 ^ N)) (b : Fin 2) :
    dyadicPoint (N + 1) (dyadicRight (N + 1) (dyadicChildEquiv N (k, b))) =
        if b = 0 then dyadicMidpoint N k else dyadicPoint N (dyadicRight N k) := by
  fin_cases b <;> ext <;>
    simp [dyadicChildEquiv, dyadicRight, dyadicPoint, dyadicMidpoint,
      finProdFinEquiv, Fin.val_cast, Equiv.trans_apply, finCongr, pow_succ] <;> field_simp <;> ring

private lemma dyadicIncrementVector_succ_reindex (j N : ℕ) :
    (fun omega p ↦ dyadicIncrementVector j (N + 1) omega (dyadicChildEquiv N p)) =
      dyadicChildIncrementVector j N := by
  funext omega p
  rcases p with ⟨k, b⟩
  unfold dyadicIncrementVector dyadicChildIncrementVector
  rw [dyadicChild_points, dyadicChild_points_right]
  split_ifs <;> rfl

private lemma dyadicIncrement_covariance (j N : ℕ) (k l : Fin (2 ^ N)) :
    cov[(fun omega ↦ dyadicIncrementVector j N omega k),
      (fun omega ↦ dyadicIncrementVector j N omega l); gaussianSource] =
        if k = l then dyadicVariance N else 0 := by
  induction N with
  | zero =>
      have hk : k = ⟨0, by norm_num⟩ := Fin.ext (by omega)
      have hl : l = ⟨0, by norm_num⟩ := Fin.ext (by omega)
      subst k
      subst l
      have hbase : (fun omega ↦ dyadicIncrementVector j 0 omega (⟨0, by norm_num⟩ : Fin (2 ^ 0))) =
          fun omega ↦ coordinate (j, Sum.inl ()) omega := by
        funext omega
        simp [dyadicIncrementVector, dyadicPoint, dyadicLeft, dyadicRight,
          unitPartial, affineMap, unitLinear]
      rw [hbase]
      rw [covariance_self (measurable_coordinate (j, Sum.inl ())).aemeasurable]
      simpa [dyadicVariance] using! coordinate_variance (j, Sum.inl ())
  | succ N ih =>
      let p := (dyadicChildEquiv N).symm k
      let q := (dyadicChildEquiv N).symm l
      have hk' : dyadicChildEquiv N p = k := (dyadicChildEquiv N).apply_symm_apply k
      have hl' : dyadicChildEquiv N q = l := (dyadicChildEquiv N).apply_symm_apply l
      have hreindex := dyadicIncrementVector_succ_reindex j N
      have hkp : (fun omega ↦ dyadicIncrementVector j (N + 1) omega k) =
          fun omega ↦ dyadicChildIncrementVector j N omega p := by
        funext omega
        rw [← hk']
        exact congrFun (congrFun hreindex omega) p
      have hlq : (fun omega ↦ dyadicIncrementVector j (N + 1) omega l) =
          fun omega ↦ dyadicChildIncrementVector j N omega q := by
        funext omega
        rw [← hl']
        exact congrFun (congrFun hreindex omega) q
      rw [hkp, hlq]
      have heq : (k = l) ↔ (p = q) := by
        rw [← hk', ← hl', (dyadicChildEquiv N).injective.eq_iff]
      simpa only [heq] using! dyadicChild_covariance_of_parent j N ih p q

private def refineDyadicIndex (N m : ℕ) (hNm : N ≤ m)
    (k : Fin (2 ^ N + 1)) : Fin (2 ^ m + 1) :=
  ⟨(k : ℕ) * 2 ^ (m - N), by
    have hk : (k : ℕ) ≤ 2 ^ N := Nat.le_of_lt_succ k.isLt
    have hp : 2 ^ N * 2 ^ (m - N) = 2 ^ m := by
      rw [← pow_add, Nat.add_sub_of_le hNm]
    calc
      (k : ℕ) * 2 ^ (m - N) ≤ 2 ^ N * 2 ^ (m - N) :=
        Nat.mul_le_mul_right _ hk
      _ = 2 ^ m := hp
      _ < 2 ^ m + 1 := Nat.lt_succ_self _⟩

private lemma dyadicPoint_refine (N m : ℕ) (hNm : N ≤ m)
    (k : Fin (2 ^ N + 1)) :
    dyadicPoint m (refineDyadicIndex N m hNm k) = dyadicPoint N k := by
  ext
  unfold dyadicPoint refineDyadicIndex
  simp only [ContinuousMap.coe_mk, Subtype.coe_mk]
  have hp : (2 ^ N : ℝ) * (2 ^ (m - N) : ℕ) = (2 ^ m : ℕ) := by
    norm_cast
    rw [← pow_add, Nat.add_sub_of_le hNm]
  field_simp
  push_cast at hp ⊢
  rw [← hp]
  ring

private lemma bridgeLevel_coarseDyadicPoint (j N m : ℕ) (hNm : N ≤ m)
    (omega : GaussianSample) (k : Fin (2 ^ N + 1)) :
    bridgeLevel j m omega (dyadicPoint N k) = 0 := by
  rw [← dyadicPoint_refine N m hNm k]
  exact bridgeLevel_dyadicPoint j m omega (refineDyadicIndex N m hNm k)

private lemma unitPartial_coarseDyadicPoint (j N P : ℕ) (hNP : N ≤ P)
    (omega : GaussianSample) (k : Fin (2 ^ N + 1)) :
    unitPartial j P omega (dyadicPoint N k) =
      unitPartial j N omega (dyadicPoint N k) := by
  induction P, hNP using Nat.le_induction with
  | base => rfl
  | succ P hNP ih =>
      rw [unitPartial_succ_apply, ih,
        bridgeLevel_coarseDyadicPoint j N P hNP]
      simp

private lemma unitBlock_dyadicPoint_of_good {omega : GaussianSample}
    (homega : GoodSample omega) (j N : ℕ) (k : Fin (2 ^ N + 1)) :
    unitBlock j omega (dyadicPoint N k) =
      unitPartial j N omega (dyadicPoint N k) := by
  have hlim := ((ContinuousEvalConst.continuous_eval_const (dyadicPoint N k)).tendsto _)
    |>.comp (unitPartial_tendsto_unitBlock homega j)
  have hconst : Tendsto
      (fun P ↦ unitPartial j P omega (dyadicPoint N k)) atTop
      (𝓝 (unitPartial j N omega (dyadicPoint N k))) := by
    refine (tendsto_congr' ?_).2 tendsto_const_nhds
    filter_upwards [eventually_ge_atTop N] with P hNP
    exact unitPartial_coarseDyadicPoint j N P hNP omega k
  exact tendsto_nhds_unique hlim hconst

private def globalBlockDyadicIncrementVector (J N : ℕ) :
    GaussianSample → (Fin J × Fin (2 ^ N)) → ℝ :=
  fun omega jk ↦ dyadicIncrementVector (jk.1 : ℕ) N omega jk.2

private abbrev GlobalPartialCoordinate (J N : ℕ) :=
  Fin J × UnitPartialCoordinate N

private def globalPartialCoordinate (J N : ℕ) :
    GlobalPartialCoordinate J N → GaussianCoordinate
  | ⟨j, Sum.inl _⟩ => ((j : ℕ), Sum.inl ())
  | ⟨j, Sum.inr ⟨m, k⟩⟩ => ((j : ℕ), Sum.inr ⟨(m : ℕ), k⟩)

private lemma injective_globalPartialCoordinate (J N : ℕ) :
    Function.Injective (globalPartialCoordinate J N) := by
  rintro ⟨j, u | ⟨m, k⟩⟩ ⟨j', u' | ⟨m', k'⟩⟩ h <;>
    simp [globalPartialCoordinate, Sigma.mk.injEq] at h ⊢
  all_goals aesop

private def globalBlockDyadicIncrementLinear (J N : ℕ) :
    (GlobalPartialCoordinate J N → ℝ) →L[ℝ]
      (Fin J × Fin (2 ^ N)) → ℝ where
  toFun z jk :=
    unitPartialEvalLinear N (dyadicPoint N (dyadicRight N jk.2))
        (fun c ↦ z (jk.1, c)) -
      unitPartialEvalLinear N (dyadicPoint N (dyadicLeft N jk.2))
        (fun c ↦ z (jk.1, c))
  map_add' z y := by
    ext jk
    change unitPartialEvalLinear N (dyadicPoint N (dyadicRight N jk.2))
        ((fun c ↦ z (jk.1, c)) + fun c ↦ y (jk.1, c)) -
      unitPartialEvalLinear N (dyadicPoint N (dyadicLeft N jk.2))
        ((fun c ↦ z (jk.1, c)) + fun c ↦ y (jk.1, c)) = _
    rw [map_add, map_add]
    simp only [Pi.add_apply]
    ring
  map_smul' a z := by
    ext jk
    change unitPartialEvalLinear N (dyadicPoint N (dyadicRight N jk.2))
        (a • fun c ↦ z (jk.1, c)) -
      unitPartialEvalLinear N (dyadicPoint N (dyadicLeft N jk.2))
        (a • fun c ↦ z (jk.1, c)) = _
    rw [map_smul, map_smul]
    simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
    ring
  cont := by fun_prop

private lemma globalBlockDyadicIncrementVector_hasGaussianLaw (J N : ℕ) :
    HasGaussianLaw (globalBlockDyadicIncrementVector J N) gaussianSource := by
  have hcoord := coordinateVector_hasGaussianLaw (globalPartialCoordinate J N)
    (injective_globalPartialCoordinate J N)
  have hmap := hcoord.map (globalBlockDyadicIncrementLinear J N)
  apply hmap.congr
  filter_upwards with omega
  funext jk
  rcases jk with ⟨j, k⟩
  unfold globalBlockDyadicIncrementVector globalBlockDyadicIncrementLinear
  simp only [ContinuousLinearMap.coe_mk']
  change unitPartialEvalLinear N (dyadicPoint N (dyadicRight N k))
      (coordinateVector (unitPartialCoordinate (j : ℕ) N) omega) -
    unitPartialEvalLinear N (dyadicPoint N (dyadicLeft N k))
      (coordinateVector (unitPartialCoordinate (j : ℕ) N) omega) = _
  rw [← unitPartial_apply_eq_linear, ← unitPartial_apply_eq_linear]
  rfl

private lemma unitPartial_crossBlock_covariance_zero {j l N : ℕ} (hjl : j ≠ l)
    (x y : unitInterval) :
    cov[(fun omega ↦ unitPartial j N omega x),
      (fun omega ↦ unitPartial l N omega y); gaussianSource] = 0 := by
  let A : GaussianSample → ℝ := fun omega ↦ (x : ℝ) * coordinate (j, Sum.inl ()) omega
  let B : GaussianSample → ℝ := fun omega ↦
    ∑ m ∈ Finset.range N, ∑ k : Fin (2 ^ m), partialEvalTerm j m k x omega
  let C : GaussianSample → ℝ := fun omega ↦ (y : ℝ) * coordinate (l, Sum.inl ()) omega
  let D : GaussianSample → ℝ := fun omega ↦
    ∑ m ∈ Finset.range N, ∑ k : Fin (2 ^ m), partialEvalTerm l m k y omega
  rw [unitPartial_eval_repr, unitPartial_eval_repr]
  change cov[A + B, C + D; gaussianSource] = 0
  have hA : MemLp A 2 gaussianSource := (coordinate_memLp_two _).const_mul _
  have hB : MemLp B 2 gaussianSource :=
    memLp_finset_sum _ fun m hm ↦
      memLp_finset_sum _ fun k hk ↦ partialEvalTerm_memLp_two _ _ _ _
  have hC : MemLp C 2 gaussianSource := (coordinate_memLp_two _).const_mul _
  have hD : MemLp D 2 gaussianSource :=
    memLp_finset_sum _ fun m hm ↦
      memLp_finset_sum _ fun k hk ↦ partialEvalTerm_memLp_two _ _ _ _
  rw [covariance_add_left hA hB (hC.add hD),
    covariance_add_right hA hC hD, covariance_add_right hB hC hD]
  unfold A B C D
  simp_rw [covariance_const_mul_left, covariance_const_mul_right]
  rw [coordinate_covariance]
  have hbase : ((j, Sum.inl ()) : GaussianCoordinate) ≠ (l, Sum.inl ()) := by
    intro h
    exact hjl (congrArg Prod.fst h)
  simp only [if_neg hbase, mul_zero, zero_add]
  rw [covariance_fun_sum_right'
      (fun m hm ↦ memLp_finset_sum _ fun k hk ↦ partialEvalTerm_memLp_two _ _ _ _)
      (coordinate_memLp_two _)]
  rw [covariance_fun_sum_left'
      (fun m hm ↦ memLp_finset_sum _ fun k hk ↦ partialEvalTerm_memLp_two _ _ _ _)
      (coordinate_memLp_two _)]
  rw [covariance_fun_sum_left'
      (fun m hm ↦ memLp_finset_sum _ fun k hk ↦ partialEvalTerm_memLp_two _ _ _ _)
      hD]
  have hright : (∑ m ∈ Finset.range N,
      cov[coordinate (j, Sum.inl ()),
        (fun a ↦ ∑ k : Fin (2 ^ m), partialEvalTerm l m k y a); gaussianSource]) = 0 := by
    apply Finset.sum_eq_zero
    intro m hm
    rw [covariance_fun_sum_right
      (fun k ↦ partialEvalTerm_memLp_two l m k y) (coordinate_memLp_two _)]
    apply Finset.sum_eq_zero
    intro k _
    unfold partialEvalTerm
    rw [covariance_const_mul_right, coordinate_covariance]
    simp
  have hleft : (∑ m ∈ Finset.range N,
      cov[(fun a ↦ ∑ k : Fin (2 ^ m), partialEvalTerm j m k x a),
        coordinate (l, Sum.inl ()); gaussianSource]) = 0 := by
    apply Finset.sum_eq_zero
    intro m hm
    rw [covariance_fun_sum_left
      (fun k ↦ partialEvalTerm_memLp_two j m k x) (coordinate_memLp_two _)]
    apply Finset.sum_eq_zero
    intro k _
    unfold partialEvalTerm
    rw [covariance_const_mul_left, coordinate_covariance]
    simp
  have hboth : (∑ m ∈ Finset.range N,
      cov[(fun a ↦ ∑ k : Fin (2 ^ m), partialEvalTerm j m k x a),
        D; gaussianSource]) = 0 := by
    apply Finset.sum_eq_zero
    intro m hm
    rw [covariance_fun_sum_left
      (fun k ↦ partialEvalTerm_memLp_two j m k x) hD]
    apply Finset.sum_eq_zero
    intro k _
    rw [covariance_fun_sum_right'
      (fun n hn ↦ memLp_finset_sum _ fun q hq ↦ partialEvalTerm_memLp_two l n q y)
      (partialEvalTerm_memLp_two j m k x)]
    apply Finset.sum_eq_zero
    intro n hn
    rw [covariance_fun_sum_right
      (fun q ↦ partialEvalTerm_memLp_two l n q y)
      (partialEvalTerm_memLp_two j m k x)]
    apply Finset.sum_eq_zero
    intro q _
    unfold partialEvalTerm
    rw [covariance_const_mul_left, covariance_const_mul_right,
      coordinate_covariance]
    simp [hjl]
  rw [hright, hleft, hboth]
  ring

private lemma dyadicIncrement_crossBlock_covariance_zero {j l N : ℕ} (hjl : j ≠ l)
    (k q : Fin (2 ^ N)) :
    cov[(fun omega ↦ dyadicIncrementVector j N omega k),
      (fun omega ↦ dyadicIncrementVector l N omega q); gaussianSource] = 0 := by
  unfold dyadicIncrementVector
  change cov[((fun omega ↦ unitPartial j N omega
      (dyadicPoint N (dyadicRight N k))) -
      (fun omega ↦ unitPartial j N omega
        (dyadicPoint N (dyadicLeft N k)))),
    ((fun omega ↦ unitPartial l N omega
      (dyadicPoint N (dyadicRight N q))) -
      (fun omega ↦ unitPartial l N omega
        (dyadicPoint N (dyadicLeft N q)))); gaussianSource] = 0
  have hXR := unitPartial_eval_memLp_two j N (dyadicPoint N (dyadicRight N k))
  have hXL := unitPartial_eval_memLp_two j N (dyadicPoint N (dyadicLeft N k))
  have hYR := unitPartial_eval_memLp_two l N (dyadicPoint N (dyadicRight N q))
  have hYL := unitPartial_eval_memLp_two l N (dyadicPoint N (dyadicLeft N q))
  rw [covariance_sub_left hXR hXL (hYR.sub hYL),
    covariance_sub_right hXR hYR hYL, covariance_sub_right hXL hYR hYL]
  simp_rw [unitPartial_crossBlock_covariance_zero hjl]
  ring

private lemma globalBlockDyadicIncrement_covariance (J N : ℕ)
    (p q : Fin J × Fin (2 ^ N)) :
    cov[(fun omega ↦ globalBlockDyadicIncrementVector J N omega p),
      (fun omega ↦ globalBlockDyadicIncrementVector J N omega q); gaussianSource] =
        if p = q then dyadicVariance N else 0 := by
  rcases p with ⟨j, k⟩
  rcases q with ⟨l, r⟩
  by_cases hjl : j = l
  · subst l
    simp only [globalBlockDyadicIncrementVector]
    rw [dyadicIncrement_covariance]
    by_cases hkr : k = r
    · subst r; simp
    · simp [hkr]
  · rw [show cov[(fun omega ↦ globalBlockDyadicIncrementVector J N omega (j, k)),
        (fun omega ↦ globalBlockDyadicIncrementVector J N omega (l, r)); gaussianSource] = 0 by
      exact dyadicIncrement_crossBlock_covariance_zero
        (show (j : ℕ) ≠ (l : ℕ) by
          intro h
          exact hjl (Fin.ext h)) k r]
    simp [hjl]

theorem globalBlockDyadicIncrementVector_law (J N : ℕ) :
    Measure.map (globalBlockDyadicIncrementVector J N) gaussianSource =
      Measure.pi (fun _ : Fin J × Fin (2 ^ N) ↦
        gaussianReal 0 (dyadicVariance N).toNNReal) := by
  have hgauss := globalBlockDyadicIncrementVector_hasGaussianLaw J N
  have hind := hgauss.iIndepFun_of_covariance_eq_zero fun p q hpq ↦ by
    rw [globalBlockDyadicIncrement_covariance]
    simp [hpq]
  rw [(iIndepFun_iff_map_fun_eq_pi_map
    (fun p ↦ (hgauss.eval p).aemeasurable)).mp hind]
  congr 1
  funext p
  have hpG := hgauss.eval p
  have hmap := hpG.isGaussian_map.eq_gaussianReal
  rcases p with ⟨j, k⟩
  rw [integral_map hpG.aemeasurable aestronglyMeasurable_id] at hmap
  rw [variance_id_map hpG.aemeasurable] at hmap
  have hmean : (∫ x, id (globalBlockDyadicIncrementVector J N x (j, k))
      ∂gaussianSource) = 0 := by
    simpa [globalBlockDyadicIncrementVector] using!
      dyadicIncrement_integral_zero (j : ℕ) N k
  rw [hmean] at hmap
  rw [show Var[(fun omega ↦ globalBlockDyadicIncrementVector J N omega (j, k));
      gaussianSource] = dyadicVariance N by
        rw [← covariance_self hpG.aemeasurable,
          globalBlockDyadicIncrement_covariance]
        simp] at hmap
  simpa using! hmap

private def globalPathBlockDyadicIncrementVector (J N : ℕ) :
    BrownianPath → (Fin J × Fin (2 ^ N)) → ℝ :=
  fun w jk ↦
    w (unitTime jk.1 (dyadicPoint N (dyadicRight N jk.2))) -
      w (unitTime jk.1 (dyadicPoint N (dyadicLeft N jk.2)))

private lemma measurable_globalPathBlockDyadicIncrementVector (J N : ℕ) :
    Measurable (globalPathBlockDyadicIncrementVector J N) := by
  apply measurable_pi_lambda
  intro jk
  exact ((ContinuousEvalConst.continuous_eval_const _).sub
    (ContinuousEvalConst.continuous_eval_const _)).measurable

private lemma globalPathBlockDyadicIncrementVector_ae_eq (J N : ℕ) :
    (globalPathBlockDyadicIncrementVector J N ∘ globalPath) =ᵐ[gaussianSource]
      globalBlockDyadicIncrementVector J N := by
  filter_upwards [ae_goodSample] with omega homega
  funext jk
  rcases jk with ⟨j, k⟩
  rw [Function.comp_apply]
  unfold globalPathBlockDyadicIncrementVector globalBlockDyadicIncrementVector
  rw [globalPath_unitTime, globalPath_unitTime]
  rw [unitBlock_dyadicPoint_of_good homega,
    unitBlock_dyadicPoint_of_good homega]
  simp [dyadicIncrementVector]

theorem brownianCandidate_blockDyadicIncrementVector_law (J N : ℕ) :
    Measure.map (globalPathBlockDyadicIncrementVector J N) brownianCandidate =
      Measure.pi (fun _ : Fin J × Fin (2 ^ N) ↦
        gaussianReal 0 (dyadicVariance N).toNNReal) := by
  rw [brownianCandidate]
  rw [AEMeasurable.map_map_of_aemeasurable
    (measurable_globalPathBlockDyadicIncrementVector J N).aemeasurable
    aeMeasurable_globalPath]
  rw [Measure.map_congr (globalPathBlockDyadicIncrementVector_ae_eq J N)]
  exact globalBlockDyadicIncrementVector_law J N

private def affineCoordinateVector (m : ℕ) : GaussianSample → Fin m → ℝ :=
  fun omega j ↦ coordinate ((j : ℕ), Sum.inl ()) omega

private lemma measurable_affineCoordinateVector (m : ℕ) :
    Measurable (affineCoordinateVector m) := by
  apply measurable_pi_lambda
  intro j
  exact measurable_coordinate ((j : ℕ), Sum.inl ())

private lemma independent_affineCoordinateVector (m : ℕ) :
    iIndepFun (fun j : Fin m ↦ coordinate ((j : ℕ), Sum.inl ())) gaussianSource := by
  apply iIndepFun.precomp (f := coordinate)
    (g := fun j : Fin m ↦ ((j : ℕ), Sum.inl ()))
  · intro j k hjk
    exact Fin.ext (congrArg Prod.fst hjk)
  · exact independent_coordinates

theorem affineCoordinateVector_law (m : ℕ) :
    Measure.map (affineCoordinateVector m) gaussianSource =
      Measure.pi (fun _ : Fin m ↦ gaussianReal 0 1) := by
  have hprod := (iIndepFun_iff_map_fun_eq_pi_map
    (fun j : Fin m ↦ (measurable_coordinate ((j : ℕ), Sum.inl ())).aemeasurable)).mp
      (independent_affineCoordinateVector m)
  change Measure.map (affineCoordinateVector m) gaussianSource = _ at hprod
  simpa only [coordinate_law] using! hprod

private def incrementVector (m : ℕ) (t : ℕ → NNReal) :
    BrownianPath → Fin m → ℝ :=
  fun w j ↦ w (t (j + 1)) - w (t j)

private lemma measurable_incrementVector (m : ℕ) (t : ℕ → NNReal) :
    Measurable (incrementVector m t) := by
  apply measurable_pi_lambda
  intro j
  exact ((ContinuousEvalConst.continuous_eval_const (t (j + 1))).sub
    (ContinuousEvalConst.continuous_eval_const (t j))).measurable

private lemma normalCDF_nonneg (v x : ℝ) : 0 ≤ normalCDF v x := by
  unfold normalCDF
  split_ifs <;> positivity

private lemma gaussianReal_zero_apply_Iic {v : ℝ} (hv : 0 < v) (x : ℝ) :
    gaussianReal 0 v.toNNReal (Set.Iic x) = ENNReal.ofReal (normalCDF v x) := by
  rw [gaussianReal_apply_eq_integral 0 (Real.toNNReal_pos.mpr hv).ne' (Set.Iic x)]
  unfold normalCDF
  simp only [if_neg (not_le.mpr hv), gaussianPDFReal_def]
  congr 2
  funext y
  simp [Real.coe_toNNReal v hv.le, div_eq_mul_inv, mul_comm]

/-- Exact construction-side data needed to obtain the public `BrownianLaw`.
The variances are the positive time increments, represented as `NNReal`. -/
def HasBrownianIncrementLaws (mu : PathLaw) : Prop :=
  IsProbabilityMeasure mu ∧ mu {w | w 0 = 0} = 1 ∧
    ∀ (m : ℕ) (t : ℕ → NNReal),
      (∀ j < m, t j < t (j + 1)) →
      Measure.map (incrementVector m t) mu =
        Measure.pi (fun j : Fin m ↦
          gaussianReal 0
            (((t (j + 1) : NNReal) : ℝ) - ((t j : NNReal) : ℝ)).toNNReal)

/-! ### Arbitrary-time increment laws

The dyadic block theorem above is now aggregated on a single flattened grid.
The resulting exact laws are passed to arbitrary times by convergence in
distribution.  Keeping the aggregation on paths (rather than returning to the
Gaussian-coordinate construction) makes this block reusable for uniqueness.
-/

private def scaledFloor (N : ℕ) (t : NNReal) : ℕ :=
  ⌊(t : ℝ) * (2 ^ N : ℕ)⌋₊

private def dyadicFloorTime (N : ℕ) (t : NNReal) : NNReal :=
  NNReal.mk ((scaledFloor N t : ℝ) / (2 ^ N : ℕ)) (by positivity)

private def gridTime (N p : ℕ) : NNReal :=
  NNReal.mk ((p : ℝ) / (2 ^ N : ℕ)) (by positivity)

private lemma dyadicFloorTime_eq_gridTime (N : ℕ) (t : NNReal) :
    dyadicFloorTime N t = gridTime N (scaledFloor N t) := rfl

private lemma scaledFloor_mono (N : ℕ) {s t : NNReal} (hst : s ≤ t) :
    scaledFloor N s ≤ scaledFloor N t := by
  apply Nat.floor_mono
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hst) (by positivity)

private lemma ordered_times_le {m : ℕ} {t : ℕ → NNReal}
    (ht : ∀ j < m, t j < t (j + 1)) {q : ℕ} (hq : q ≤ m) :
    t q ≤ t m := by
  exact Nat.decreasingInduction
    (motive := fun k hk ↦ t k ≤ t m)
    (fun k hk ih ↦ (ht k hk).le.trans ih) le_rfl hq

private lemma scaledFloor_le_final {m N : ℕ} {t : ℕ → NNReal}
    (ht : ∀ j < m, t j < t (j + 1)) {q : ℕ} (hq : q ≤ m) :
    scaledFloor N (t q) ≤ scaledFloor N (t m) :=
  scaledFloor_mono N (ordered_times_le ht hq)

private lemma tendsto_dyadicFloorTime (t : NNReal) :
    Tendsto (fun N ↦ dyadicFloorTime N t) atTop (nhds t) := by
  rw [← NNReal.tendsto_coe]
  change Tendsto
    (fun N ↦ (scaledFloor N t : ℝ) / (2 ^ N : ℕ)) atTop (nhds (t : ℝ))
  have hp : Tendsto (fun N ↦ (((2 ^ N : ℕ) : ℝ))) atTop atTop := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using!
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2))
  exact (tendsto_nat_floor_mul_div_atTop t.property).comp hp

private lemma tendsto_path_dyadicFloorTime (w : BrownianPath) (t : NNReal) :
    Tendsto (fun N ↦ w (dyadicFloorTime N t)) atTop (nhds (w t)) :=
  (w.continuous.tendsto t).comp (tendsto_dyadicFloorTime t)

private lemma finProdFinEquiv_value (J N : ℕ)
    (p : Fin J × Fin (2 ^ N)) :
    ((finProdFinEquiv p : Fin (J * 2 ^ N)) : ℕ) =
      (p.2 : ℕ) + 2 ^ N * (p.1 : ℕ) := rfl

private lemma blockDyadicCell_eq_gridIncrement (J N : ℕ) (w : BrownianPath)
    (p : Fin J × Fin (2 ^ N)) :
    globalPathBlockDyadicIncrementVector J N w p =
      w (gridTime N ((finProdFinEquiv p : Fin (J * 2 ^ N)) + 1)) -
        w (gridTime N (finProdFinEquiv p : Fin (J * 2 ^ N))) := by
  rcases p with ⟨j, k⟩
  unfold globalPathBlockDyadicIncrementVector gridTime unitTime dyadicPoint
  simp only [dyadicRight, dyadicLeft, finProdFinEquiv_value,
    ContinuousMap.coe_mk, Subtype.coe_mk]
  congr 2 <;> apply NNReal.eq <;> simp only [NNReal.coe_mk]
  · push_cast
    field_simp
    ring
  · push_cast
    field_simp
    ring

private def gridAggregateLinear (J N m : ℕ) (t : ℕ → NNReal) :
    ((Fin J × Fin (2 ^ N)) → ℝ) →L[ℝ] Fin m → ℝ where
  toFun z q := ∑ p : Fin J × Fin (2 ^ N),
    (if scaledFloor N (t q) ≤ (finProdFinEquiv p : Fin (J * 2 ^ N)) ∧
        (finProdFinEquiv p : Fin (J * 2 ^ N)) < scaledFloor N (t (q + 1))
      then 1 else 0) * z p
  map_add' z y := by
    ext q
    simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p _hp
    split_ifs <;> simp
  map_smul' a z := by
    ext q
    simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _hp
    split_ifs <;> simp
  cont := by fun_prop

private def dyadicApproxIncrementVector (m N : ℕ) (t : ℕ → NNReal) :
    BrownianPath → Fin m → ℝ :=
  incrementVector m (fun q ↦ dyadicFloorTime N (t q))

private lemma measurable_dyadicApproxIncrementVector (m N : ℕ)
    (t : ℕ → NNReal) :
    Measurable (dyadicApproxIncrementVector m N t) :=
  measurable_incrementVector m (fun q ↦ dyadicFloorTime N (t q))

private lemma gridAggregate_eq_dyadicApprox (m N : ℕ) (t : ℕ → NNReal)
    (ht : ∀ j < m, t j < t (j + 1)) :
    (gridAggregateLinear (scaledFloor N (t m) + 1) N m t ∘
        globalPathBlockDyadicIncrementVector (scaledFloor N (t m) + 1) N) =
      dyadicApproxIncrementVector m N t := by
  funext w q
  let J := scaledFloor N (t m) + 1
  let a := scaledFloor N (t q)
  let b := scaledFloor N (t (q + 1))
  have hqm : (q : ℕ) ≤ m := Nat.le_of_lt q.isLt
  have hq1m : (q : ℕ) + 1 ≤ m := q.isLt
  have hab : a ≤ b := scaledFloor_mono N (ht q q.isLt).le
  have hbJ : b ≤ J * 2 ^ N := by
    have hb : b ≤ scaledFloor N (t m) := scaledFloor_le_final ht hq1m
    have hpow : 1 ≤ 2 ^ N := one_le_pow₀ (by norm_num)
    calc
      b ≤ scaledFloor N (t m) := hb
      _ ≤ J := Nat.le_of_lt (Nat.lt_succ_self _)
      _ ≤ J * 2 ^ N := Nat.le_mul_of_pos_right J (by positivity)
  change (∑ p : Fin J × Fin (2 ^ N),
      (if a ≤ (finProdFinEquiv p : Fin (J * 2 ^ N)) ∧
          (finProdFinEquiv p : Fin (J * 2 ^ N)) < b
        then 1 else 0) * globalPathBlockDyadicIncrementVector J N w p) = _
  rw [show (∑ p : Fin J × Fin (2 ^ N),
      (if a ≤ (finProdFinEquiv p : Fin (J * 2 ^ N)) ∧
          (finProdFinEquiv p : Fin (J * 2 ^ N)) < b then 1 else 0) *
        globalPathBlockDyadicIncrementVector J N w p) =
      ∑ r : Fin (J * 2 ^ N),
        (if a ≤ r ∧ r < b then 1 else 0) *
          globalPathBlockDyadicIncrementVector J N w (finProdFinEquiv.symm r) by
    simpa using! (Equiv.sum_comp finProdFinEquiv
      (fun r : Fin (J * 2 ^ N) ↦
        (if a ≤ r ∧ r < b then 1 else 0) *
          globalPathBlockDyadicIncrementVector J N w (finProdFinEquiv.symm r)))]
  simp_rw [blockDyadicCell_eq_gridIncrement]
  simp only [Equiv.apply_symm_apply]
  rw [show (∑ x : Fin (J * 2 ^ N),
      (if a ≤ (x : ℕ) ∧ (x : ℕ) < b then 1 else 0) *
        (w (gridTime N ((x : ℕ) + 1)) - w (gridTime N (x : ℕ)))) =
      ∑ p ∈ Finset.range (J * 2 ^ N),
        (if a ≤ p ∧ p < b then 1 else 0) *
          (w (gridTime N (p + 1)) - w (gridTime N p)) by
    exact Fin.sum_univ_eq_sum_range
      (fun p : ℕ ↦ (if a ≤ p ∧ p < b then 1 else 0) *
        (w (gridTime N (p + 1)) - w (gridTime N p))) (J * 2 ^ N)]
  simp only [ite_mul, one_mul, zero_mul]
  have hset : (Finset.range (J * 2 ^ N)).filter (fun p ↦ a ≤ p ∧ p < b) =
      Finset.Ico a b := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    constructor
    · exact fun hp ↦ hp.2
    · intro hp
      exact ⟨lt_of_lt_of_le hp.2 hbJ, hp⟩
  have hfilter :
      (∑ p ∈ Finset.range (J * 2 ^ N),
        if a ≤ p ∧ p < b
          then w (gridTime N (p + 1)) - w (gridTime N p) else 0) =
        ∑ p ∈ Finset.Ico a b,
          (w (gridTime N (p + 1)) - w (gridTime N p)) := by
    rw [← hset, Finset.sum_filter]
  rw [hfilter, Finset.sum_Ico_eq_sub _ hab,
    Finset.sum_range_sub (fun k ↦ w (gridTime N k)) b,
    Finset.sum_range_sub (fun k ↦ w (gridTime N k)) a]
  rw [show w (gridTime N b) - w (gridTime N 0) -
      (w (gridTime N a) - w (gridTime N 0)) =
      w (gridTime N b) - w (gridTime N a) by ring]
  change w (gridTime N b) - w (gridTime N a) = _
  simp only [dyadicApproxIncrementVector, incrementVector,
    dyadicFloorTime_eq_gridTime, a, b]

private lemma dyadicApproxIncrementVector_tendsto (m : ℕ) (t : ℕ → NNReal)
    (w : BrownianPath) :
    Tendsto (fun N ↦ dyadicApproxIncrementVector m N t w) atTop
      (nhds (incrementVector m t w)) := by
  rw [tendsto_pi_nhds]
  intro q
  exact (tendsto_path_dyadicFloorTime w (t (q + 1))).sub
    (tendsto_path_dyadicFloorTime w (t q))

private def dyadicIncrementVariance (N : ℕ) (t : ℕ → NNReal)
    (q : ℕ) : NNReal :=
  NNReal.mk (((scaledFloor N (t (q + 1)) - scaledFloor N (t q) : ℕ) : ℝ) /
      (2 ^ N : ℕ)) (by positivity)

private lemma dyadicIncrementVariance_coe (N : ℕ) (t : ℕ → NNReal)
    (q : ℕ) :
    (dyadicIncrementVariance N t q : ℝ) =
      ((scaledFloor N (t (q + 1)) - scaledFloor N (t q) : ℕ) : ℝ) /
        (2 ^ N : ℕ) := rfl

private lemma tendsto_dyadicIncrementVariance (t : ℕ → NNReal) (q : ℕ)
    (hqt : t q ≤ t (q + 1)) :
    Tendsto (fun N ↦ dyadicIncrementVariance N t q) atTop
      (nhds (((t (q + 1) : NNReal) : ℝ) - ((t q : NNReal) : ℝ)).toNNReal) := by
  rw [← NNReal.tendsto_coe]
  simp only [dyadicIncrementVariance_coe]
  have hp : Tendsto (fun N ↦ (((2 ^ N : ℕ) : ℝ))) atTop atTop := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using!
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2))
  have hq : Tendsto (fun N ↦
      (scaledFloor N (t q) : ℝ) / (2 ^ N : ℕ)) atTop (nhds (t q : ℝ)) := by
    simpa [scaledFloor, Function.comp_def] using!
      (tendsto_nat_floor_mul_div_atTop (t q).property).comp hp
  have hq1 : Tendsto (fun N ↦
      (scaledFloor N (t (q + 1)) : ℝ) / (2 ^ N : ℕ)) atTop
      (nhds (t (q + 1) : ℝ)) := by
    simpa [scaledFloor, Function.comp_def] using!
      (tendsto_nat_floor_mul_div_atTop (t (q + 1)).property).comp hp
  have hsub : Tendsto (fun N ↦
      (scaledFloor N (t (q + 1)) : ℝ) / (2 ^ N : ℕ) -
        (scaledFloor N (t q) : ℝ) / (2 ^ N : ℕ)) atTop
      (nhds (((t (q + 1) : ℝ) - (t q : ℝ)))) := hq1.sub hq
  convert hsub using 1
  · funext N
    have hmono : scaledFloor N (t q) ≤ scaledFloor N (t (q + 1)) :=
      scaledFloor_mono N hqt
    push_cast [Nat.cast_sub hmono]
    ring
  · have hnonneg : 0 ≤ ((t (q + 1) : NNReal) : ℝ) - ((t q : NNReal) : ℝ) :=
      sub_nonneg.mpr (NNReal.coe_le_coe.mpr hqt)
    congr 1
    exact Real.coe_toNNReal _ hnonneg

private lemma ordered_times_le_of_le {m : ℕ} {t : ℕ → NNReal}
    (ht : ∀ j < m, t j < t (j + 1)) {q r : ℕ}
    (hqr : q ≤ r) (hrm : r ≤ m) : t q ≤ t r := by
  exact Nat.decreasingInduction
    (motive := fun k hk ↦ t k ≤ t r)
    (fun k hk ih ↦ (ht k (lt_of_lt_of_le hk hrm)).le.trans ih)
    le_rfl hqr

private def gridCellSet (J N : ℕ) (t : ℕ → NNReal) (q : ℕ) :
    Finset (Fin J × Fin (2 ^ N)) :=
  Finset.univ.filter fun p ↦
    scaledFloor N (t q) ≤ (finProdFinEquiv p : Fin (J * 2 ^ N)) ∧
      (finProdFinEquiv p : Fin (J * 2 ^ N)) < scaledFloor N (t (q + 1))

private lemma gridAggregateLinear_apply (J N m : ℕ) (t : ℕ → NNReal)
    (z : (Fin J × Fin (2 ^ N)) → ℝ) (q : Fin m) :
    gridAggregateLinear J N m t z q = ∑ p ∈ gridCellSet J N t q, z p := by
  change (∑ p, (if scaledFloor N (t q) ≤
      (finProdFinEquiv p : Fin (J * 2 ^ N)) ∧
      (finProdFinEquiv p : Fin (J * 2 ^ N)) < scaledFloor N (t (q + 1))
      then 1 else 0) * z p) = _
  simp only [gridCellSet]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p _hp
  split_ifs <;> simp_all

private lemma gridCellSet_disjoint {m N J : ℕ} {t : ℕ → NNReal}
    (ht : ∀ j < m, t j < t (j + 1)) {q r : Fin m} (hqr : q ≠ r) :
    Disjoint (gridCellSet J N t q) (gridCellSet J N t r) := by
  rw [Finset.disjoint_left]
  intro p hpq hpr
  simp only [gridCellSet, Finset.mem_filter, Finset.mem_univ, true_and] at hpq hpr
  rcases lt_or_gt_of_ne hqr with hlt | hgt
  · have htime : t ((q : ℕ) + 1) ≤ t r :=
      ordered_times_le_of_le ht (Nat.succ_le_iff.mpr hlt) (Nat.le_of_lt r.isLt)
    have hfloor := scaledFloor_mono N htime
    exact (not_lt_of_ge (hfloor.trans hpr.1)) hpq.2
  · have htime : t ((r : ℕ) + 1) ≤ t q :=
      ordered_times_le_of_le ht (Nat.succ_le_iff.mpr hgt) (Nat.le_of_lt q.isLt)
    have hfloor := scaledFloor_mono N htime
    exact (not_lt_of_ge (hfloor.trans hpq.1)) hpr.2

private lemma gridCellSet_card {m N : ℕ} {t : ℕ → NNReal}
    (ht : ∀ j < m, t j < t (j + 1)) (q : Fin m) :
    (gridCellSet (scaledFloor N (t m) + 1) N t q).card =
      scaledFloor N (t (q + 1)) - scaledFloor N (t q) := by
  let J := scaledFloor N (t m) + 1
  let a := scaledFloor N (t q)
  let b := scaledFloor N (t (q + 1))
  have hab : a ≤ b := scaledFloor_mono N (ht q q.isLt).le
  have hb : b ≤ J * 2 ^ N := by
    have hbfinal : b ≤ scaledFloor N (t m) :=
      scaledFloor_le_final ht q.isLt
    have hpow : 1 ≤ 2 ^ N := one_le_pow₀ (by norm_num)
    calc
      b ≤ scaledFloor N (t m) := hbfinal
      _ ≤ J := Nat.le_of_lt (Nat.lt_succ_self _)
      _ ≤ J * 2 ^ N := Nat.le_mul_of_pos_right J (by positivity)
  have himage :
      (gridCellSet J N t q).image
        (fun p ↦ ((finProdFinEquiv p : Fin (J * 2 ^ N)) : ℕ)) = Finset.Ico a b := by
    ext p
    constructor
    · intro hp
      simp only [Finset.mem_image] at hp
      rcases hp with ⟨x, hx, rfl⟩
      simpa [gridCellSet, a, b] using! hx
    · intro hp
      have hpbound : (p : ℕ) < J * 2 ^ N :=
        lt_of_lt_of_le (Finset.mem_Ico.mp hp).2 hb
      let p' : Fin (J * 2 ^ N) := ⟨p, hpbound⟩
      refine Finset.mem_image.mpr ⟨(finProdFinEquiv).symm p', ?_, ?_⟩
      · have heqval :
            (((finProdFinEquiv ((finProdFinEquiv).symm p') :
              Fin (J * 2 ^ N))) : ℕ) = p := by
          simpa [p'] using! congrArg Fin.val (finProdFinEquiv.apply_symm_apply p')
        simp only [gridCellSet, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [heqval]
        exact Finset.mem_Ico.mp hp
      · simpa [p'] using! congrArg Fin.val (finProdFinEquiv.apply_symm_apply p')
  calc
    (gridCellSet J N t q).card =
        ((gridCellSet J N t q).image
          (fun p ↦ ((finProdFinEquiv p : Fin (J * 2 ^ N)) : ℕ))).card :=
      (Finset.card_image_of_injective _
        (Fin.val_injective.comp finProdFinEquiv.injective)).symm
    _ = (Finset.Ico a b).card := by rw [himage]
    _ = b - a := Nat.card_Ico a b

private lemma blockDyadic_hasGaussianLaw (J N : ℕ) :
    HasGaussianLaw (globalPathBlockDyadicIncrementVector J N) brownianCandidate := by
  refine ⟨(measurable_globalPathBlockDyadicIncrementVector J N).aemeasurable, ?_⟩
  rw [brownianCandidate_blockDyadicIncrementVector_law,
    ← globalBlockDyadicIncrementVector_law]
  exact (globalBlockDyadicIncrementVector_hasGaussianLaw J N).isGaussian_map

private lemma blockDyadic_eval_law (J N : ℕ)
    (p : Fin J × Fin (2 ^ N)) :
    Measure.map (fun w ↦ globalPathBlockDyadicIncrementVector J N w p)
        brownianCandidate = gaussianReal 0 (dyadicVariance N).toNNReal := by
  change Measure.map (Function.eval p ∘ globalPathBlockDyadicIncrementVector J N)
    brownianCandidate = _
  rw [← AEMeasurable.map_map_of_aemeasurable
    (measurable_pi_apply p).aemeasurable
    (measurable_globalPathBlockDyadicIncrementVector J N).aemeasurable]
  rw [brownianCandidate_blockDyadicIncrementVector_law, Measure.pi_map_eval]
  simp

private lemma blockDyadic_integral_zero (J N : ℕ)
    (p : Fin J × Fin (2 ^ N)) :
    ∫ w, globalPathBlockDyadicIncrementVector J N w p ∂brownianCandidate = 0 := by
  calc
    _ = ∫ x : ℝ, id x ∂Measure.map
        (fun w ↦ globalPathBlockDyadicIncrementVector J N w p) brownianCandidate := by
      simpa using! (integral_map
        ((measurable_pi_apply p).comp
          (measurable_globalPathBlockDyadicIncrementVector J N)).aemeasurable
        aestronglyMeasurable_id).symm
    _ = 0 := by
      rw [blockDyadic_eval_law]
      simpa only [id_eq] using!
        (integral_id_gaussianReal (μ := 0)
          (v := (dyadicVariance N).toNNReal))

private lemma blockDyadic_memLp_two (J N : ℕ)
    (p : Fin J × Fin (2 ^ N)) :
    MemLp (fun w ↦ globalPathBlockDyadicIncrementVector J N w p)
      2 brownianCandidate :=
  (blockDyadic_hasGaussianLaw J N).eval p |>.memLp_two

private lemma blockDyadic_iIndepFun (J N : ℕ) :
    iIndepFun (fun p ↦ fun w ↦ globalPathBlockDyadicIncrementVector J N w p)
      brownianCandidate := by
  apply (iIndepFun_iff_map_fun_eq_pi_map fun p ↦
    ((measurable_pi_apply p).comp
      (measurable_globalPathBlockDyadicIncrementVector J N)).aemeasurable).2
  change Measure.map (globalPathBlockDyadicIncrementVector J N) brownianCandidate =
    Measure.pi (fun p ↦ Measure.map
      (fun w ↦ globalPathBlockDyadicIncrementVector J N w p) brownianCandidate)
  rw [brownianCandidate_blockDyadicIncrementVector_law]
  congr 1
  funext p
  exact (blockDyadic_eval_law J N p).symm

private lemma blockDyadic_covariance (J N : ℕ)
    (p r : Fin J × Fin (2 ^ N)) :
    cov[(fun w ↦ globalPathBlockDyadicIncrementVector J N w p),
      (fun w ↦ globalPathBlockDyadicIncrementVector J N w r); brownianCandidate] =
        if p = r then dyadicVariance N else 0 := by
  split_ifs with hpr
  · subst r
    rw [show cov[(fun w ↦ globalPathBlockDyadicIncrementVector J N w p),
        (fun w ↦ globalPathBlockDyadicIncrementVector J N w p);
        brownianCandidate] =
        Var[(fun w ↦ globalPathBlockDyadicIncrementVector J N w p);
          brownianCandidate] from covariance_self
      ((measurable_pi_apply p).comp
        (measurable_globalPathBlockDyadicIncrementVector J N)).aemeasurable]
    change Var[(Function.eval p ∘ globalPathBlockDyadicIncrementVector J N);
      brownianCandidate] = dyadicVariance N
    calc
      _ = Var[id; Measure.map
          (Function.eval p ∘ globalPathBlockDyadicIncrementVector J N)
          brownianCandidate] := (variance_id_map
            ((measurable_pi_apply p).comp
              (measurable_globalPathBlockDyadicIncrementVector J N)).aemeasurable).symm
      _ = Var[id; gaussianReal 0 (dyadicVariance N).toNNReal] := by
        rw [show Measure.map
            (Function.eval p ∘ globalPathBlockDyadicIncrementVector J N)
              brownianCandidate = gaussianReal 0 (dyadicVariance N).toNNReal by
          exact blockDyadic_eval_law J N p]
      _ = dyadicVariance N := by
        rw [variance_id_gaussianReal]
        simp [Real.coe_toNNReal, (dyadicVariance_pos N).le]
  · exact (blockDyadic_iIndepFun J N).indepFun hpr |>.covariance_eq_zero
      (blockDyadic_memLp_two J N p) (blockDyadic_memLp_two J N r)

private lemma dyadicApprox_hasGaussianLaw (m N : ℕ) (t : ℕ → NNReal)
    (ht : ∀ j < m, t j < t (j + 1)) :
    HasGaussianLaw (dyadicApproxIncrementVector m N t) brownianCandidate := by
  let J := scaledFloor N (t m) + 1
  have hmap := (blockDyadic_hasGaussianLaw J N).map (gridAggregateLinear J N m t)
  apply hmap.congr
  filter_upwards with w
  exact congrFun (gridAggregate_eq_dyadicApprox m N t ht) w

private lemma dyadicApprox_integral_zero (m N : ℕ) (t : ℕ → NNReal)
    (ht : ∀ j < m, t j < t (j + 1)) (q : Fin m) :
    ∫ w, dyadicApproxIncrementVector m N t w q ∂brownianCandidate = 0 := by
  let J := scaledFloor N (t m) + 1
  rw [← gridAggregate_eq_dyadicApprox m N t ht]
  simp_rw [Function.comp_apply, gridAggregateLinear_apply]
  rw [integral_finset_sum]
  · exact Finset.sum_eq_zero fun p hp ↦ blockDyadic_integral_zero J N p
  · intro p hp
    exact (blockDyadic_memLp_two J N p).integrable one_le_two

private lemma dyadicApprox_covariance (m N : ℕ) (t : ℕ → NNReal)
    (ht : ∀ j < m, t j < t (j + 1)) (q r : Fin m) :
    cov[(fun w ↦ dyadicApproxIncrementVector m N t w q),
      (fun w ↦ dyadicApproxIncrementVector m N t w r); brownianCandidate] =
      if q = r then (dyadicIncrementVariance N t q : ℝ) else 0 := by
  let J := scaledFloor N (t m) + 1
  rw [← gridAggregate_eq_dyadicApprox m N t ht]
  change cov[(fun w ↦ gridAggregateLinear J N m t
      (globalPathBlockDyadicIncrementVector J N w) q),
    (fun w ↦ gridAggregateLinear J N m t
      (globalPathBlockDyadicIncrementVector J N w) r); brownianCandidate] = _
  simp_rw [gridAggregateLinear_apply]
  rw [covariance_fun_sum_fun_sum'
    (fun p hp ↦ blockDyadic_memLp_two J N p)
    (fun p hp ↦ blockDyadic_memLp_two J N p)]
  by_cases hqr : q = r
  · subst r
    simp_rw [blockDyadic_covariance]
    have hdiag : (∑ p ∈ gridCellSet J N t q,
        ∑ r ∈ gridCellSet J N t q,
          if p = r then dyadicVariance N else 0) =
        (gridCellSet J N t q).card * dyadicVariance N := by
      simp
    rw [hdiag, gridCellSet_card ht]
    simp only [if_pos]
    rw [dyadicIncrementVariance_coe, dyadicVariance_eq]
    push_cast
    ring
  · have hdis := gridCellSet_disjoint (J := J) (N := N) ht hqr
    simp only [if_neg hqr]
    apply Finset.sum_eq_zero
    intro p hp
    apply Finset.sum_eq_zero
    intro r hr
    rw [blockDyadic_covariance]
    by_cases hpr : p = r
    · subst r
      exact (Finset.disjoint_left.mp hdis hp hr).elim
    · simp [hpr]

private theorem dyadicApproxIncrementVector_law (m N : ℕ)
    (t : ℕ → NNReal) (ht : ∀ j < m, t j < t (j + 1)) :
    Measure.map (dyadicApproxIncrementVector m N t) brownianCandidate =
      Measure.pi (fun q : Fin m ↦ gaussianReal 0 (dyadicIncrementVariance N t q)) := by
  have hgauss := dyadicApprox_hasGaussianLaw m N t ht
  have hind := hgauss.iIndepFun_of_covariance_eq_zero fun q r hqr ↦ by
    rw [dyadicApprox_covariance m N t ht]
    simp [hqr]
  rw [(iIndepFun_iff_map_fun_eq_pi_map
    (fun q ↦ (hgauss.eval q).aemeasurable)).mp hind]
  congr 1
  funext q
  have hmap := (hgauss.eval q).isGaussian_map.eq_gaussianReal
  rw [integral_map (hgauss.eval q).aemeasurable aestronglyMeasurable_id] at hmap
  rw [variance_id_map (hgauss.eval q).aemeasurable] at hmap
  simp only [id_eq] at hmap
  rw [dyadicApprox_integral_zero m N t ht q] at hmap
  rw [show Var[(fun w ↦ dyadicApproxIncrementVector m N t w q);
      brownianCandidate] = (dyadicIncrementVariance N t q : ℝ) by
        rw [← covariance_self (hgauss.eval q).aemeasurable,
          dyadicApprox_covariance m N t ht]
        simp] at hmap
  simpa using! hmap

private def diagonalScale (m : ℕ) (v : Fin m → NNReal) :
    (Fin m → ℝ) →L[ℝ] Fin m → ℝ where
  toFun z q := Real.sqrt (v q) * z q
  map_add' z y := by ext q; simp [mul_add]
  map_smul' a z := by ext q; simp [mul_assoc, mul_left_comm]
  cont := by fun_prop

private def scaledStandardVector (m : ℕ) (v : Fin m → NNReal) :
    GaussianSample → Fin m → ℝ :=
  fun omega q ↦ Real.sqrt (v q) * affineCoordinateVector m omega q

private lemma measurable_scaledStandardVector (m : ℕ) (v : Fin m → NNReal) :
    Measurable (scaledStandardVector m v) := by
  apply measurable_pi_lambda
  intro q
  exact measurable_const.mul
    ((measurable_pi_apply q).comp (measurable_affineCoordinateVector m))

private lemma scaledStandardVector_comp (m : ℕ) (v : Fin m → NNReal) :
    scaledStandardVector m v = diagonalScale m v ∘ affineCoordinateVector m := rfl

private lemma scaledStandardVector_law (m : ℕ) (v : Fin m → NNReal) :
    Measure.map (scaledStandardVector m v) gaussianSource =
      Measure.pi (fun q : Fin m ↦ gaussianReal 0 (v q)) := by
  rw [scaledStandardVector_comp]
  rw [← AEMeasurable.map_map_of_aemeasurable
    (diagonalScale m v).continuous.aemeasurable
    (measurable_affineCoordinateVector m).aemeasurable]
  rw [affineCoordinateVector_law]
  change Measure.map (fun z q ↦ Real.sqrt (v q) * z q)
      (Measure.pi fun _ : Fin m ↦ gaussianReal 0 1) = _
  rw [Measure.pi_map_pi]
  congr 1
  funext q
  rw [gaussianReal_map_const_mul]
  congr 2
  · simp
  · ext
    simp [Real.sq_sqrt]
  · intro q
    fun_prop

private lemma scaledStandardVector_tendsto {m : ℕ}
    {v : ℕ → Fin m → NNReal} {vlim : Fin m → NNReal}
    (hv : ∀ q, Tendsto (fun N ↦ v N q) atTop (nhds (vlim q)))
    (omega : GaussianSample) :
    Tendsto (fun N ↦ scaledStandardVector m (v N) omega) atTop
      (nhds (scaledStandardVector m vlim omega)) := by
  rw [tendsto_pi_nhds]
  intro q
  have hsqrt : Tendsto (fun N ↦ Real.sqrt (v N q)) atTop
      (nhds (Real.sqrt (vlim q))) := by
    exact (Real.continuous_sqrt.tendsto _).comp
      ((NNReal.tendsto_coe).2 (hv q))
  exact hsqrt.mul_const _

private theorem brownianCandidate_incrementVector_law (m : ℕ)
    (t : ℕ → NNReal) (ht : ∀ j < m, t j < t (j + 1)) :
    Measure.map (incrementVector m t) brownianCandidate =
      Measure.pi (fun q : Fin m ↦ gaussianReal 0
        (((t (q + 1) : NNReal) : ℝ) - ((t q : NNReal) : ℝ)).toNNReal) := by
  let vN : ℕ → Fin m → NNReal := fun N q ↦ dyadicIncrementVariance N t q
  let v : Fin m → NNReal := fun q ↦
    (((t (q + 1) : NNReal) : ℝ) - ((t q : NNReal) : ℝ)).toNNReal
  have hv : ∀ q, Tendsto (fun N ↦ vN N q) atTop (nhds (v q)) := by
    intro q
    exact tendsto_dyadicIncrementVariance t q (ht q q.isLt).le
  have hpathMeasure : TendstoInMeasure brownianCandidate
      (fun N ↦ dyadicApproxIncrementVector m N t) atTop (incrementVector m t) := by
    apply tendstoInMeasure_of_tendsto_ae
    · intro N
      exact (measurable_dyadicApproxIncrementVector m N t).aestronglyMeasurable
    · filter_upwards with w
      exact dyadicApproxIncrementVector_tendsto m t w
  have hpathDist : TendstoInDistribution
      (fun N ↦ dyadicApproxIncrementVector m N t) atTop
      (incrementVector m t) (fun _ => brownianCandidate) brownianCandidate :=
    hpathMeasure.tendstoInDistribution fun N ↦
      (measurable_dyadicApproxIncrementVector m N t).aemeasurable
  have hscaleMeasure : TendstoInMeasure gaussianSource
      (fun N ↦ scaledStandardVector m (vN N)) atTop (scaledStandardVector m v) := by
    apply tendstoInMeasure_of_tendsto_ae
    · intro N
      exact (measurable_scaledStandardVector m (vN N)).aestronglyMeasurable
    · filter_upwards with omega
      exact scaledStandardVector_tendsto hv omega
  have hscaleDist : TendstoInDistribution
      (fun N ↦ scaledStandardVector m (vN N)) atTop
      (scaledStandardVector m v) (fun _ => gaussianSource) gaussianSource :=
    hscaleMeasure.tendstoInDistribution fun N ↦
      (measurable_scaledStandardVector m (vN N)).aemeasurable
  have hseq :
      (fun N ↦ (⟨Measure.map (dyadicApproxIncrementVector m N t) brownianCandidate,
          Measure.isProbabilityMeasure_map
            (measurable_dyadicApproxIncrementVector m N t).aemeasurable⟩ :
            ProbabilityMeasure (Fin m → ℝ))) =
      (fun N ↦ (⟨Measure.map (scaledStandardVector m (vN N)) gaussianSource,
          Measure.isProbabilityMeasure_map
            (measurable_scaledStandardVector m (vN N)).aemeasurable⟩ :
            ProbabilityMeasure (Fin m → ℝ))) := by
    funext N
    apply Subtype.ext
    exact (dyadicApproxIncrementVector_law m N t ht).trans
      (scaledStandardVector_law m (vN N)).symm
  have hscaleDist' := hscaleDist.tendsto
  rw [← hseq] at hscaleDist'
  have hlimit := tendsto_nhds_unique hpathDist.tendsto hscaleDist'
  have hmeasure : Measure.map (incrementVector m t) brownianCandidate =
      Measure.map (scaledStandardVector m v) gaussianSource :=
    congrArg Subtype.val hlimit
  rw [hmeasure, scaledStandardVector_law]

theorem brownianCandidate_hasBrownianIncrementLaws :
    HasBrownianIncrementLaws brownianCandidate := by
  refine ⟨inferInstance, brownianCandidate_start_zero, ?_⟩
  intro m t ht
  exact brownianCandidate_incrementVector_law m t ht

theorem brownianLaw_of_incrementLaws (mu : PathLaw)
    (hmu : HasBrownianIncrementLaws mu) : BrownianLaw mu := by
  refine ⟨hmu.1, hmu.2.1, ?_⟩
  intro m t u ht
  let rectangle : Set (Fin m → ℝ) := Set.univ.pi fun j ↦ Set.Iic (u j)
  have hrectangle : MeasurableSet rectangle :=
    MeasurableSet.univ_pi fun _ ↦ measurableSet_Iic
  have hevent :
      {w : BrownianPath | ∀ j < m, w (t (j + 1)) - w (t j) ≤ u j} =
        incrementVector m t ⁻¹' rectangle := by
    ext w
    simp only [Set.mem_setOf_eq, Set.mem_preimage, rectangle, Set.mem_pi,
      Set.mem_univ, true_implies, Set.mem_Iic, incrementVector]
    constructor
    · intro hw j
      exact hw j j.isLt
    · intro hw j hj
      exact hw ⟨j, hj⟩
  rw [hevent, ← Measure.map_apply_of_aemeasurable
    (measurable_incrementVector m t).aemeasurable hrectangle]
  rw [hmu.2.2 m t ht, Measure.pi_pi]
  have hvar : ∀ j < m,
      0 < ((t (j + 1) : NNReal) : ℝ) - ((t j : NNReal) : ℝ) := by
    intro j hj
    exact sub_pos.mpr (NNReal.coe_lt_coe.mpr (ht j hj))
  simp_rw [gaussianReal_zero_apply_Iic (hvar _ (Fin.isLt _))]
  calc
    (∏ j : Fin m,
        ENNReal.ofReal
          (normalCDF (((t (j + 1) : NNReal) : ℝ) - ((t j : NNReal) : ℝ)) (u j))) =
        ∏ j ∈ Finset.range m,
          ENNReal.ofReal
            (normalCDF (((t (j + 1) : NNReal) : ℝ) - ((t j : NNReal) : ℝ)) (u j)) :=
      Fin.prod_univ_eq_prod_range
        (fun j : ℕ ↦ ENNReal.ofReal
          (normalCDF (((t (j + 1) : NNReal) : ℝ) - ((t j : NNReal) : ℝ)) (u j))) m
    _ = ENNReal.ofReal ((Finset.range m).prod fun j ↦
          normalCDF (((t (j + 1) : NNReal) : ℝ) - ((t j : NNReal) : ℝ)) (u j)) :=
      (ENNReal.ofReal_prod_of_nonneg fun j _ ↦ normalCDF_nonneg _ _).symm

private def extendFin (m : ℕ) (u : Fin m → ℝ) : ℕ → ℝ :=
  fun j ↦ if hj : j < m then u ⟨j, hj⟩ else 0

private lemma extendFin_apply (m : ℕ) (u : Fin m → ℝ) (j : Fin m) :
    extendFin m u j = u j := by
  simp [extendFin, j.isLt]

private def iicSpanning (mu : Measure ℝ) [IsFiniteMeasure mu] :
    mu.FiniteSpanningSetsIn (Set.range Set.Iic) where
  set n := Set.Iic (n : ℝ)
  set_mem n := ⟨n, rfl⟩
  finite n := measure_lt_top mu _
  spanning := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_Iic, Set.mem_univ, iff_true]
    rcases exists_nat_ge x with ⟨n, hn⟩
    exact ⟨n, hn⟩

theorem incrementLaws_of_brownianLaw (mu : PathLaw)
    (hmu : BrownianLaw mu) : HasBrownianIncrementLaws mu := by
  letI : IsProbabilityMeasure mu := hmu.1
  refine ⟨hmu.1, hmu.2.1, ?_⟩
  intro m t ht
  let variance : Fin m → NNReal := fun j ↦
    (((t (j + 1) : NNReal) : ℝ) - ((t j : NNReal) : ℝ)).toNNReal
  let gaussian : Fin m → Measure ℝ := fun j ↦ gaussianReal 0 (variance j)
  apply (Measure.pi_eq_generateFrom
    (fun _ ↦ (borel_eq_generateFrom_Iic ℝ).symm)
    (fun _ ↦ isPiSystem_Iic)
    (fun j ↦ iicSpanning (gaussian j)) (μν := Measure.map (incrementVector m t) mu) ?_).symm
  intro s hs
  choose u hu using hs
  have hs_eq : s = fun j ↦ Set.Iic (u j) := by
    funext j
    exact (hu j).symm
  subst s
  have hrectangle : MeasurableSet (Set.univ.pi fun j : Fin m ↦ Set.Iic (u j)) :=
    MeasurableSet.univ_pi fun _ ↦ measurableSet_Iic
  rw [Measure.map_apply_of_aemeasurable
    (measurable_incrementVector m t).aemeasurable hrectangle]
  have hevent :
      incrementVector m t ⁻¹' (Set.univ.pi fun j : Fin m ↦ Set.Iic (u j)) =
        {w : BrownianPath | ∀ j < m,
          w (t (j + 1)) - w (t j) ≤ extendFin m u j} := by
    ext w
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies,
      Set.mem_Iic, Set.mem_setOf_eq, incrementVector]
    constructor
    · intro hw j hj
      simpa [extendFin, hj] using! hw ⟨j, hj⟩
    · intro hw j
      simpa [extendFin, j.isLt] using! hw j j.isLt
  rw [hevent, hmu.2.2 m t (extendFin m u) ht]
  have hvar : ∀ j < m,
      0 < ((t (j + 1) : NNReal) : ℝ) - ((t j : NNReal) : ℝ) := by
    intro j hj
    exact sub_pos.mpr (NNReal.coe_lt_coe.mpr (ht j hj))
  simp only [gaussian, variance]
  simp_rw [gaussianReal_zero_apply_Iic (hvar _ (Fin.isLt _))]
  rw [ENNReal.ofReal_prod_of_nonneg (fun j _ ↦ normalCDF_nonneg _ _)]
  rw [← Fin.prod_univ_eq_prod_range
    (fun j : ℕ ↦ ENNReal.ofReal
      (normalCDF (((t (j + 1) : NNReal) : ℝ) - ((t j : NNReal) : ℝ))
        (extendFin m u j))) m]
  simp_rw [extendFin_apply]

theorem brownianCandidate_brownianLaw : BrownianLaw brownianCandidate :=
  brownianLaw_of_incrementLaws brownianCandidate
    brownianCandidate_hasBrownianIncrementLaws

private def supportTailCard (s : Finset NNReal) : ℕ :=
  (insert 0 s).card - 1

private lemma support_card_eq (s : Finset NNReal) :
    (insert 0 s).card = supportTailCard s + 1 := by
  unfold supportTailCard
  have hpos : 0 < (insert 0 s).card :=
    Finset.card_pos.mpr ⟨0, Finset.mem_insert_self 0 s⟩
  omega

private def supportOrder (s : Finset NNReal) :
    Fin (supportTailCard s + 1) ≃o {x // x ∈ insert 0 s} :=
  (insert 0 s).orderIsoOfFin (support_card_eq s)

private lemma supportOrder_zero (s : Finset NNReal) :
    ((supportOrder s 0 : {x // x ∈ insert 0 s}) : NNReal) = 0 := by
  let z : {x // x ∈ insert 0 s} := ⟨0, Finset.mem_insert_self 0 s⟩
  rcases (supportOrder s).surjective z with ⟨i, hi⟩
  have hle := (supportOrder s).monotone (Fin.zero_le i)
  change ((supportOrder s 0 : {x // x ∈ insert 0 s}) : NNReal) ≤
    ((supportOrder s i : {x // x ∈ insert 0 s}) : NNReal) at hle
  rw [hi] at hle
  exact le_antisymm hle (zero_le)

private def orderedTimeSeq (s : Finset NNReal) : ℕ → NNReal :=
  fun n ↦ if hn : n < supportTailCard s + 1 then
    ((supportOrder s ⟨n, hn⟩ : {x // x ∈ insert 0 s}) : NNReal)
  else 0

private lemma orderedTimeSeq_zero (s : Finset NNReal) :
    orderedTimeSeq s 0 = 0 := by
  rw [orderedTimeSeq, dif_pos (by omega)]
  exact supportOrder_zero s

private lemma orderedTimeSeq_strict (s : Finset NNReal) :
    ∀ j < supportTailCard s, orderedTimeSeq s j < orderedTimeSeq s (j + 1) := by
  intro j hj
  have hj0 : j < supportTailCard s + 1 := by omega
  have hj1 : j + 1 < supportTailCard s + 1 := by omega
  simp only [orderedTimeSeq, dif_pos hj0, dif_pos hj1]
  exact (supportOrder s).lt_iff_lt.mpr (by simp)

private def orderedEval (s : Finset NNReal) :
    BrownianPath → Fin (supportTailCard s + 1) → ℝ :=
  fun w i ↦ w (orderedTimeSeq s i)

private lemma measurable_orderedEval (s : Finset NNReal) :
    Measurable (orderedEval s) := by
  apply measurable_pi_lambda
  intro i
  exact (ContinuousEvalConst.continuous_eval_const (orderedTimeSeq s i)).measurable

private def tupleDifference (m : ℕ) :
    (Fin (m + 1) → ℝ) → ℝ × (Fin m → ℝ) :=
  fun z ↦ (z 0, fun j ↦ z j.succ - z j.castSucc)

private lemma measurable_tupleDifference (m : ℕ) :
    Measurable (tupleDifference m) := by
  unfold tupleDifference
  fun_prop

private lemma injective_tupleDifference (m : ℕ) :
    Function.Injective (tupleDifference m) := by
  intro z y hzy
  have hzero : z 0 = y 0 := congrArg Prod.fst hzy
  have hstep : ∀ j : Fin m,
      z j.succ - z j.castSucc = y j.succ - y j.castSucc := by
    intro j
    exact congrFun (congrArg Prod.snd hzy) j
  funext i
  exact Fin.induction hzero (fun j ih ↦ by
    have hs := hstep j
    linarith) i

private lemma measurableEmbedding_tupleDifference (m : ℕ) :
    MeasurableEmbedding (tupleDifference m) :=
  (measurable_tupleDifference m).measurableEmbedding (injective_tupleDifference m)

private lemma tupleDifference_orderedEval (s : Finset NNReal) (w : BrownianPath) :
    tupleDifference (supportTailCard s) (orderedEval s w) =
      (w 0, incrementVector (supportTailCard s) (orderedTimeSeq s) w) := by
  apply Prod.ext
  · simp [tupleDifference, orderedEval, orderedTimeSeq_zero]
  · funext j
    rfl

private lemma measurable_zero_prod (m : ℕ) :
    Measurable (fun z : Fin m → ℝ ↦ ((0 : ℝ), z)) := by fun_prop

private lemma orderedEval_law_eq (mu nu : PathLaw)
    (hmu : HasBrownianIncrementLaws mu) (hnu : HasBrownianIncrementLaws nu)
    (s : Finset NNReal) :
    Measure.map (orderedEval s) mu = Measure.map (orderedEval s) nu := by
  letI : IsProbabilityMeasure mu := hmu.1
  letI : IsProbabilityMeasure nu := hnu.1
  let m := supportTailCard s
  let t := orderedTimeSeq s
  have ht : ∀ j < m, t j < t (j + 1) := orderedTimeSeq_strict s
  have hinc : Measure.map (incrementVector m t) mu =
      Measure.map (incrementVector m t) nu := by
    rw [hmu.2.2 m t ht, hnu.2.2 m t ht]
  have hzeroSet : MeasurableSet {w : BrownianPath | w 0 = 0} :=
    MeasurableSet.preimage (measurableSet_singleton 0)
      (ContinuousEvalConst.continuous_eval_const (0 : NNReal)).measurable
  have hstartMu : ∀ᵐ w ∂mu, w 0 = 0 := by
    apply (ae_iff_measure_eq hzeroSet.nullMeasurableSet).2
    simpa using! hmu.2.1
  have hstartNu : ∀ᵐ w ∂nu, w 0 = 0 := by
    apply (ae_iff_measure_eq hzeroSet.nullMeasurableSet).2
    simpa using! hnu.2.1
  have hpairMu : Measure.map
      (tupleDifference m ∘ orderedEval s) mu =
      Measure.map (fun z : Fin m → ℝ ↦ ((0 : ℝ), z))
        (Measure.map (incrementVector m t) mu) := by
    calc
      _ = Measure.map (fun w : BrownianPath ↦
          ((0 : ℝ), incrementVector m t w)) mu := by
        apply Measure.map_congr
        filter_upwards [hstartMu] with w hw
        rw [Function.comp_apply, tupleDifference_orderedEval]
        simp [m, t, hw]
      _ = _ := (AEMeasurable.map_map_of_aemeasurable
        (measurable_zero_prod m).aemeasurable
        (measurable_incrementVector m t).aemeasurable).symm
  have hpairNu : Measure.map
      (tupleDifference m ∘ orderedEval s) nu =
      Measure.map (fun z : Fin m → ℝ ↦ ((0 : ℝ), z))
        (Measure.map (incrementVector m t) nu) := by
    calc
      _ = Measure.map (fun w : BrownianPath ↦
          ((0 : ℝ), incrementVector m t w)) nu := by
        apply Measure.map_congr
        filter_upwards [hstartNu] with w hw
        rw [Function.comp_apply, tupleDifference_orderedEval]
        simp [m, t, hw]
      _ = _ := (AEMeasurable.map_map_of_aemeasurable
        (measurable_zero_prod m).aemeasurable
        (measurable_incrementVector m t).aemeasurable).symm
  apply (measurableEmbedding_tupleDifference m).map_injective
  rw [AEMeasurable.map_map_of_aemeasurable
      (measurable_tupleDifference m).aemeasurable
      (measurable_orderedEval s).aemeasurable,
    AEMeasurable.map_map_of_aemeasurable
      (measurable_tupleDifference m).aemeasurable
      (measurable_orderedEval s).aemeasurable]
  exact hpairMu.trans ((congrArg
    (Measure.map (fun z : Fin m → ℝ ↦ ((0 : ℝ), z))) hinc).trans hpairNu.symm)

private def supportIndex (s : Finset NNReal) (x : s) :
    Fin (supportTailCard s + 1) :=
  (supportOrder s).symm ⟨x, Finset.mem_insert_of_mem x.property⟩

private def supportRestrictMap (s : Finset NNReal) :
    (Fin (supportTailCard s + 1) → ℝ) → s → ℝ :=
  fun z x ↦ z (supportIndex s x)

private lemma measurable_supportRestrictMap (s : Finset NNReal) :
    Measurable (supportRestrictMap s) := by
  apply measurable_pi_lambda
  intro x
  exact measurable_pi_apply (supportIndex s x)

private lemma orderedTimeSeq_supportIndex (s : Finset NNReal) (x : s) :
    orderedTimeSeq s (supportIndex s x) = x := by
  rw [orderedTimeSeq, dif_pos (supportIndex s x).isLt]
  exact congrArg Subtype.val ((supportOrder s).apply_symm_apply
    ⟨x, Finset.mem_insert_of_mem x.property⟩)

private lemma supportRestrictMap_orderedEval (s : Finset NNReal) (w : BrownianPath) :
    supportRestrictMap s (orderedEval s w) = s.restrict w := by
  funext x
  simp [supportRestrictMap, orderedEval, orderedTimeSeq_supportIndex,
    Finset.restrict]

private lemma finiteTimeEval_law_eq (mu nu : PathLaw)
    (hmu : HasBrownianIncrementLaws mu) (hnu : HasBrownianIncrementLaws nu)
    (s : Finset NNReal) :
    Measure.map (fun w : BrownianPath ↦ s.restrict w) mu =
      Measure.map (fun w : BrownianPath ↦ s.restrict w) nu := by
  rw [show (fun w : BrownianPath ↦ s.restrict w) =
      supportRestrictMap s ∘ orderedEval s by
        funext w
        exact (supportRestrictMap_orderedEval s w).symm,
    ← AEMeasurable.map_map_of_aemeasurable
      (measurable_supportRestrictMap s).aemeasurable
      (measurable_orderedEval s).aemeasurable,
    ← AEMeasurable.map_map_of_aemeasurable
      (measurable_supportRestrictMap s).aemeasurable
      (measurable_orderedEval s).aemeasurable,
    orderedEval_law_eq mu nu hmu hnu s]

private def denseFiniteTimes (I : Finset ℕ) : Finset NNReal :=
  I.image (TopologicalSpace.denseSeq NNReal)

private def denseRestrictionMap (I : Finset ℕ) :
    (denseFiniteTimes I → ℝ) → I → ℝ :=
  fun z i ↦ z ⟨TopologicalSpace.denseSeq NNReal i,
    Finset.mem_image.mpr ⟨i, i.property, rfl⟩⟩

private lemma measurable_denseRestrictionMap (I : Finset ℕ) :
    Measurable (denseRestrictionMap I) := by
  apply measurable_pi_lambda
  intro i
  exact measurable_pi_apply _

private lemma denseRestrictionMap_apply (I : Finset ℕ) (w : BrownianPath) :
    denseRestrictionMap I ((denseFiniteTimes I).restrict w) =
      I.restrict (fun n ↦ w (TopologicalSpace.denseSeq NNReal n)) := by
  rfl

private lemma finiteDenseEval_law_eq (mu nu : PathLaw)
    (hmu : HasBrownianIncrementLaws mu) (hnu : HasBrownianIncrementLaws nu)
    (I : Finset ℕ) :
    Measure.map (fun w : BrownianPath ↦ I.restrict (denseEval w)) mu =
      Measure.map (fun w : BrownianPath ↦ I.restrict (denseEval w)) nu := by
  let s := denseFiniteTimes I
  have hfinite := finiteTimeEval_law_eq mu nu hmu hnu s
  have hsmeas : Measurable (fun w : BrownianPath ↦ s.restrict w) := by
    apply measurable_pi_lambda
    intro x
    exact (ContinuousEvalConst.continuous_eval_const (x : NNReal)).measurable
  rw [show (fun w : BrownianPath ↦ I.restrict (denseEval w)) =
      denseRestrictionMap I ∘ (fun w : BrownianPath ↦ s.restrict w) by
        funext w
        exact (denseRestrictionMap_apply I w).symm]
  calc
    _ = Measure.map (denseRestrictionMap I)
        (Measure.map (fun w : BrownianPath ↦ s.restrict w) mu) :=
      (AEMeasurable.map_map_of_aemeasurable
        (measurable_denseRestrictionMap I).aemeasurable hsmeas.aemeasurable).symm
    _ = Measure.map (denseRestrictionMap I)
        (Measure.map (fun w : BrownianPath ↦ s.restrict w) nu) := by rw [hfinite]
    _ = _ := AEMeasurable.map_map_of_aemeasurable
      (measurable_denseRestrictionMap I).aemeasurable hsmeas.aemeasurable

theorem hasBrownianIncrementLaws_unique (mu nu : PathLaw)
    (hmu : HasBrownianIncrementLaws mu) (hnu : HasBrownianIncrementLaws nu) :
    mu = nu := by
  letI : IsProbabilityMeasure mu := hmu.1
  letI : IsProbabilityMeasure nu := hnu.1
  let P : (I : Finset ℕ) → Measure (I → ℝ) :=
    fun I ↦ Measure.map (fun w : BrownianPath ↦ I.restrict (denseEval w)) mu
  have hprojMu : IsProjectiveLimit (Measure.map denseEval mu) P :=
    isProjectiveLimit_map measurable_denseEval.aemeasurable
  have hprojNu : IsProjectiveLimit (Measure.map denseEval nu) P := by
    intro I
    exact (isProjectiveLimit_map measurable_denseEval.aemeasurable I).trans
      (finiteDenseEval_law_eq mu nu hmu hnu I).symm
  letI (I : Finset ℕ) : IsFiniteMeasure (P I) := by
    dsimp [P]
    infer_instance
  apply measurableEmbedding_denseEval.map_injective
  exact hprojMu.unique hprojNu

theorem brownianLaw_unique (mu nu : PathLaw)
    (hmu : BrownianLaw mu) (hnu : BrownianLaw nu) : mu = nu :=
  hasBrownianIncrementLaws_unique mu nu
    (incrementLaws_of_brownianLaw mu hmu)
    (incrementLaws_of_brownianLaw nu hnu)

theorem brownianLaw_existsUnique : ∃! mu : PathLaw, BrownianLaw mu := by
  refine ⟨brownianCandidate, brownianCandidate_brownianLaw, ?_⟩
  intro mu hmu
  exact brownianLaw_unique mu brownianCandidate hmu brownianCandidate_brownianLaw

/-- The existence-and-uniqueness part of the public Brownian foundation is
exactly reduced to constructing a unique path law with the product increment
laws above.  This keeps the remaining Lévy--Ciesielski construction obligation
explicit, while ensuring that its eventual output plugs into the unchanged
public statement without any extra assumption or altered notion of law. -/
private def affineGrowthBad (j : ℕ) : Set GaussianSample :=
  {omega | ((j + 1 : ℕ) : ℝ) / 16 <
    |coordinate (j, Sum.inl ()) omega|}

private lemma affineGrowthBad_measureReal (j : ℕ) :
    gaussianSource.real (affineGrowthBad j) =
      (gaussianReal 0 1).real
        {z | ((j + 1 : ℕ) : ℝ) / 16 < |z|} := by
  rw [← coordinate_law (j, Sum.inl ())]
  rw [Measure.real, Measure.real, Measure.map_apply_of_aemeasurable
    (measurable_coordinate _).aemeasurable]
  · rfl
  · exact measurableSet_lt measurable_const
      (measurable_abs.comp (measurable_id : Measurable (id : ℝ → ℝ)))

private lemma affineGrowthBad_measureReal_le (j : ℕ) :
    gaussianSource.real (affineGrowthBad j) ≤
      2 * Real.exp (-(((j + 1 : ℕ) : ℝ) / 16) ^ 2 / 2) := by
  rw [affineGrowthBad_measureReal]
  exact standardGaussian_abs_tail (by positivity)

private lemma affineGrowthBad_measureReal_geometric (j : ℕ) :
    gaussianSource.real (affineGrowthBad j) ≤
      2 * (Real.exp (-(1 : ℝ) / 512)) ^ (j + 1) := by
  refine (affineGrowthBad_measureReal_le j).trans ?_
  rw [← Real.exp_nat_mul]
  have hj : (1 : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by norm_num
  have hexp :
      -(((j + 1 : ℕ) : ℝ) / 16) ^ 2 / 2 ≤
        ((j + 1 : ℕ) : ℝ) * (-(1 : ℝ) / 512) := by
    nlinarith
  gcongr

private lemma affineGrowthBad_measureReal_summable :
    Summable fun j ↦ gaussianSource.real (affineGrowthBad j) := by
  have hr : ‖Real.exp (-(1 : ℝ) / 512)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_lt_one_iff]
    norm_num
  have hgeom : Summable fun j : ℕ ↦
      2 * (Real.exp (-(1 : ℝ) / 512)) ^ (j + 1) := by
    exact ((summable_geometric_of_norm_lt_one hr).comp_injective
      (fun _ _ h ↦ Nat.add_right_cancel h)).mul_left 2
  exact hgeom.of_nonneg_of_le
    (fun _ ↦ measureReal_nonneg)
    affineGrowthBad_measureReal_geometric

private lemma affineGrowthBad_measure_tsum_ne_top :
    (∑' j, gaussianSource (affineGrowthBad j)) ≠ ∞ := by
  let p : ℕ → NNReal := fun j ↦
    NNReal.mk (gaussianSource.real (affineGrowthBad j)) (measureReal_nonneg)
  have hp : Summable fun j ↦ (p j : ℝ) := by
    simpa only [p, NNReal.smul_def] using! affineGrowthBad_measureReal_summable
  have hfinite : (∑' j, ENNReal.ofNNReal (p j)) ≠ ∞ :=
    ENNReal.tsum_coe_ne_top_iff_summable_coe.mpr hp
  have hfun : (fun j ↦ gaussianSource (affineGrowthBad j)) =
      fun j ↦ ENNReal.ofNNReal (p j) := by
    funext j
    symm
    calc
      ENNReal.ofNNReal (p j) =
          ENNReal.ofReal (gaussianSource.real (affineGrowthBad j)) := by
        exact (ENNReal.ofReal_eq_coe_nnreal measureReal_nonneg).symm
      _ = gaussianSource (affineGrowthBad j) := ofReal_measureReal
  rw [hfun]
  exact hfinite

private lemma ae_eventually_affine_growth :
    ∀ᵐ omega ∂gaussianSource, ∀ᶠ j in atTop,
      |coordinate (j, Sum.inl ()) omega| ≤ ((j + 1 : ℕ) : ℝ) / 16 := by
  filter_upwards [ae_eventually_notMem affineGrowthBad_measure_tsum_ne_top]
    with omega homega
  filter_upwards [homega] with j hj
  simpa only [affineGrowthBad, Set.mem_setOf_eq, not_lt] using! hj

private def pairedBridgeThreshold (n : ℕ) : NNReal :=
  NNReal.mk (4 * Real.sqrt ((n + 1 : ℕ) : ℝ) * (((Nat.unpair n).2 + 1 : ℕ) : ℝ)) (mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) (by positivity))

private def pairedBridgeBadCoordinate (n : ℕ)
    (k : Fin (2 ^ (Nat.unpair n).2)) : Set GaussianSample :=
  {omega | (pairedBridgeThreshold n : ℝ) <
    |coordinate ((Nat.unpair n).1,
      Sum.inr ⟨(Nat.unpair n).2, k⟩) omega|}

private def pairedBridgeBad (n : ℕ) : Set GaussianSample :=
  {omega | pairedBridgeThreshold n <
    coefficientMax (Nat.unpair n).1 (Nat.unpair n).2 omega}

private lemma pairedBridgeBad_eq_iUnion (n : ℕ) :
    pairedBridgeBad n = ⋃ k : Fin (2 ^ (Nat.unpair n).2),
      pairedBridgeBadCoordinate n k := by
  ext omega
  simp only [pairedBridgeBad, pairedBridgeBadCoordinate, Set.mem_setOf_eq,
    Set.mem_iUnion]
  unfold coefficientMax
  constructor
  · intro h
    rcases Finset.lt_sup_iff.mp h with ⟨k, _hk, hk⟩
    exact ⟨k, by exact_mod_cast hk⟩
  · rintro ⟨k, hk⟩
    apply Finset.lt_sup_iff.mpr
    exact ⟨k, Finset.mem_univ k, by exact_mod_cast hk⟩

private lemma pairedBridgeBadCoordinate_measureReal (n : ℕ)
    (k : Fin (2 ^ (Nat.unpair n).2)) :
    gaussianSource.real (pairedBridgeBadCoordinate n k) =
      (gaussianReal 0 1).real {z | (pairedBridgeThreshold n : ℝ) < |z|} := by
  rw [← coordinate_law ((Nat.unpair n).1,
    Sum.inr ⟨(Nat.unpair n).2, k⟩)]
  rw [Measure.real, Measure.real, Measure.map_apply_of_aemeasurable
    (measurable_coordinate _).aemeasurable]
  · rfl
  · exact measurableSet_lt measurable_const
      (measurable_abs.comp (measurable_id : Measurable (id : ℝ → ℝ)))

private lemma pairedBridgeBad_measureReal_le (n : ℕ) :
    gaussianSource.real (pairedBridgeBad n) ≤
      (2 ^ (Nat.unpair n).2 : ℝ) *
        (2 * Real.exp (-((pairedBridgeThreshold n : ℝ)) ^ 2 / 2)) := by
  rw [pairedBridgeBad_eq_iUnion]
  calc
    gaussianSource.real (⋃ k : Fin (2 ^ (Nat.unpair n).2),
        pairedBridgeBadCoordinate n k)
        ≤ ∑ k : Fin (2 ^ (Nat.unpair n).2),
          gaussianSource.real (pairedBridgeBadCoordinate n k) := by
            simpa using! measureReal_biUnion_finset_le Finset.univ
              (pairedBridgeBadCoordinate n)
    _ ≤ ∑ _k : Fin (2 ^ (Nat.unpair n).2),
          2 * Real.exp (-((pairedBridgeThreshold n : ℝ)) ^ 2 / 2) := by
          apply Finset.sum_le_sum
          intro k _hk
          rw [pairedBridgeBadCoordinate_measureReal]
          exact standardGaussian_abs_tail (pairedBridgeThreshold n).property
    _ = (2 ^ (Nat.unpair n).2 : ℝ) *
          (2 * Real.exp (-((pairedBridgeThreshold n : ℝ)) ^ 2 / 2)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
          norm_num

private lemma pairedBridgeBad_measureReal_geometric (n : ℕ) :
    gaussianSource.real (pairedBridgeBad n) ≤
      (2 * Real.exp (-8)) ^ (n + 1) := by
  refine (pairedBridgeBad_measureReal_le n).trans ?_
  let m := (Nat.unpair n).2
  have hmn : m ≤ n := Nat.unpair_right_le n
  have hsqrt : (Real.sqrt (((n + 1 : ℕ) : ℝ))) ^ 2 = ((n + 1 : ℕ) : ℝ) := by
    rw [Real.sq_sqrt]
    positivity
  have hthreshold : -((pairedBridgeThreshold n : ℝ)) ^ 2 / 2 =
      -8 * ((n + 1 : ℕ) : ℝ) * (((m + 1 : ℕ) : ℝ) ^ 2) := by
    simp only [pairedBridgeThreshold, NNReal.coe_mk, m]
    rw [mul_pow, mul_pow, hsqrt]
    ring
  rw [hthreshold]
  calc
    (2 ^ m : ℝ) *
        (2 * Real.exp
          (-8 * ((n + 1 : ℕ) : ℝ) * (((m + 1 : ℕ) : ℝ) ^ 2))) =
        (2 : ℝ) ^ (m + 1) *
          Real.exp
            (-8 * ((n + 1 : ℕ) : ℝ) * (((m + 1 : ℕ) : ℝ) ^ 2)) := by
      rw [pow_succ]
      ring
    _ ≤ (2 : ℝ) ^ (n + 1) *
          Real.exp (-8 * ((n + 1 : ℕ) : ℝ)) := by
      have hpow : (2 : ℝ) ^ (m + 1) ≤ (2 : ℝ) ^ (n + 1) := by
        gcongr <;> norm_num <;> omega
      have hexp : Real.exp
            (-8 * ((n + 1 : ℕ) : ℝ) * (((m + 1 : ℕ) : ℝ) ^ 2)) ≤
          Real.exp (-8 * ((n + 1 : ℕ) : ℝ)) := by
        apply Real.exp_le_exp.mpr
        have hmone : (1 : ℝ) ≤ (((m + 1 : ℕ) : ℝ) ^ 2) := by
          have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
          push_cast
          nlinarith [sq_nonneg (m : ℝ)]
        have hnnonneg : 0 ≤ ((n + 1 : ℕ) : ℝ) := by positivity
        nlinarith
      exact mul_le_mul hpow hexp (Real.exp_pos _).le (pow_nonneg (by norm_num) _)
    _ = (2 * Real.exp (-8)) ^ (n + 1) := by
      rw [mul_pow, ← Real.exp_nat_mul]
      congr 2
      push_cast
      ring

private lemma pairedBridgeBad_measureReal_summable :
    Summable fun n ↦ gaussianSource.real (pairedBridgeBad n) := by
  have hr : ‖(2 * Real.exp (-8) : ℝ)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (mul_pos (by norm_num) (Real.exp_pos _))]
    rw [Real.exp_neg, ← div_eq_mul_inv]
    apply (div_lt_iff₀ (Real.exp_pos 8)).mpr
    have h := Real.add_one_le_exp (8 : ℝ)
    norm_num at h ⊢
    linarith
  have hgeom : Summable fun n : ℕ ↦
      (2 * Real.exp (-8)) ^ (n + 1) := by
    exact (summable_geometric_of_norm_lt_one hr).comp_injective
      (fun _ _ h ↦ Nat.add_right_cancel h)
  exact hgeom.of_nonneg_of_le
    (fun _ ↦ measureReal_nonneg)
    pairedBridgeBad_measureReal_geometric

private lemma pairedBridgeBad_measure_tsum_ne_top :
    (∑' n, gaussianSource (pairedBridgeBad n)) ≠ ∞ := by
  let p : ℕ → NNReal := fun n ↦
    NNReal.mk (gaussianSource.real (pairedBridgeBad n)) (measureReal_nonneg)
  have hp : Summable fun n ↦ (p n : ℝ) := by
    simpa only [p, NNReal.smul_def] using! pairedBridgeBad_measureReal_summable
  have hfinite : (∑' n, ENNReal.ofNNReal (p n)) ≠ ∞ :=
    ENNReal.tsum_coe_ne_top_iff_summable_coe.mpr hp
  have hfun : (fun n ↦ gaussianSource (pairedBridgeBad n)) =
      fun n ↦ ENNReal.ofNNReal (p n) := by
    funext n
    symm
    calc
      ENNReal.ofNNReal (p n) =
          ENNReal.ofReal (gaussianSource.real (pairedBridgeBad n)) := by
        exact (ENNReal.ofReal_eq_coe_nnreal measureReal_nonneg).symm
      _ = gaussianSource (pairedBridgeBad n) := ofReal_measureReal
  rw [hfun]
  exact hfinite

private lemma ae_eventually_pairedBridge_growth :
    ∀ᵐ omega ∂gaussianSource, ∀ᶠ n in atTop,
      (coefficientMax (Nat.unpair n).1 (Nat.unpair n).2 omega : ℝ) ≤
        (pairedBridgeThreshold n : ℝ) := by
  filter_upwards [ae_eventually_notMem pairedBridgeBad_measure_tsum_ne_top]
    with omega homega
  filter_upwards [homega] with n hn
  simpa only [pairedBridgeBad, Set.mem_setOf_eq, not_lt] using! hn

private def bridgeGrowthSeries (m : ℕ) : ℝ :=
  hatScale m * (4 * (((m + 1 : ℕ) : ℝ) ^ 2))

private lemma bridgeGrowthSeries_nonneg (m : ℕ) :
    0 ≤ bridgeGrowthSeries m := by
  unfold bridgeGrowthSeries
  exact mul_nonneg (hatScale_pos m).le (by positivity)

private lemma summable_bridgeGrowthSeries : Summable bridgeGrowthSeries := by
  let r : ℝ := Real.log 2 / 2
  have hr : 0 < r := div_pos (Real.log_pos (by norm_num)) (by norm_num)
  have h2 := Real.summable_pow_mul_exp_neg_nat_mul 2 hr
  have h1 := Real.summable_pow_mul_exp_neg_nat_mul 1 hr
  have h0 := Real.summable_pow_mul_exp_neg_nat_mul 0 hr
  have hbase : Summable fun m : ℕ ↦
      (((m : ℝ) + 1) ^ 2) * Real.exp (-r * (m : ℝ)) := by
    convert (h2.add (h1.mul_left 2)).add h0 using 1
    funext m
    simp only [pow_two, pow_one, pow_zero, one_mul]
    ring
  have hc := hbase.mul_left (4 * Real.exp (-Real.log 2))
  convert hc using 1
  funext m
  simp only [bridgeGrowthSeries, hatScale]
  rw [show Real.rpow 2 (-(m : ℝ) / 2 - 1) =
      Real.exp (Real.log 2 * (-(m : ℝ) / 2 - 1)) by
    exact Real.rpow_def_of_pos (by norm_num) _]
  have he : Real.log 2 * (-(m : ℝ) / 2 - 1) =
      -Real.log 2 + (-r * (m : ℝ)) := by
    dsimp [r]
    ring
  rw [he, Real.exp_add]
  push_cast
  ring

private def bridgeGrowthConstant : ℝ := ∑' m, bridgeGrowthSeries m

private lemma bridgeGrowthConstant_nonneg : 0 ≤ bridgeGrowthConstant :=
  tsum_nonneg bridgeGrowthSeries_nonneg

private lemma coefficientMax_growth_of_eventual
    {omega : GaussianSample} {N j : ℕ}
    (hpair : ∀ n ≥ N,
      (coefficientMax (Nat.unpair n).1 (Nat.unpair n).2 omega : ℝ) ≤
        (pairedBridgeThreshold n : ℝ))
    (hj : N ≤ j) (m : ℕ) :
    (coefficientMax j m omega : ℝ) ≤
      4 * (((j + 1 : ℕ) : ℝ)) * (((m + 1 : ℕ) : ℝ) ^ 2) := by
  let n := Nat.pair j m
  have hNn : N ≤ n := hj.trans (Nat.left_le_pair j m)
  have hn := hpair n hNn
  rw [Nat.unpair_pair] at hn
  refine hn.trans ?_
  have hp := Nat.pair_lt_max_add_one_sq j m
  have hp' : ((n + 1 : ℕ) : ℝ) ≤
      ((((max j m) + 1 : ℕ) : ℝ) ^ 2) := by
    exact_mod_cast (Nat.succ_le_iff.mpr hp)
  have hsqrt : Real.sqrt (((n + 1 : ℕ) : ℝ)) ≤
      (((max j m) + 1 : ℕ) : ℝ) := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · simpa only [sq] using! hp'
  have hmax : max j m + 1 ≤ (j + 1) * (m + 1) := by
    calc
      max j m + 1 ≤ j + m + 1 := by omega
      _ ≤ (j + 1) * (m + 1) := by nlinarith [Nat.zero_le (j * m)]
  have hmax' : (((max j m) + 1 : ℕ) : ℝ) ≤
      (((j + 1 : ℕ) : ℝ) * ((m + 1 : ℕ) : ℝ)) := by
    exact_mod_cast hmax
  simp only [pairedBridgeThreshold, NNReal.coe_mk, n, Nat.unpair_pair]
  calc
    4 * Real.sqrt (((Nat.pair j m + 1 : ℕ) : ℝ)) * (((m + 1 : ℕ) : ℝ))
        ≤ 4 * (((max j m) + 1 : ℕ) : ℝ) * (((m + 1 : ℕ) : ℝ)) := by
          gcongr
    _ ≤ 4 * (((j + 1 : ℕ) : ℝ) * ((m + 1 : ℕ) : ℝ)) *
          (((m + 1 : ℕ) : ℝ)) := by
          gcongr
    _ = 4 * (((j + 1 : ℕ) : ℝ)) * (((m + 1 : ℕ) : ℝ) ^ 2) := by ring

private lemma bridgeSum_norm_growth {omega : GaussianSample}
    (homega : GoodSample omega) {N j : ℕ}
    (hpair : ∀ n ≥ N,
      (coefficientMax (Nat.unpair n).1 (Nat.unpair n).2 omega : ℝ) ≤
        (pairedBridgeThreshold n : ℝ))
    (hj : N ≤ j) :
    ‖bridgeSum j omega‖ ≤
      (((j + 1 : ℕ) : ℝ) * bridgeGrowthConstant) := by
  have hsum := summable_boundedBridgeLevel_of_good homega j
  have hmajorant : ∀ m,
      ‖boundedBridgeLevel j m omega‖ ≤
        (((j + 1 : ℕ) : ℝ) * bridgeGrowthSeries m) := by
    intro m
    rw [boundedBridgeLevel_norm]
    refine (bridgeLevel_norm_bound j m omega).trans ?_
    have hcoeff := coefficientMax_growth_of_eventual hpair hj m
    unfold bridgeGrowthSeries
    calc
      hatScale m * (coefficientMax j m omega : ℝ)
          ≤ hatScale m *
              (4 * (((j + 1 : ℕ) : ℝ)) * (((m + 1 : ℕ) : ℝ) ^ 2)) :=
        mul_le_mul_of_nonneg_left hcoeff (hatScale_pos m).le
      _ = (((j + 1 : ℕ) : ℝ) *
          (hatScale m * (4 * (((m + 1 : ℕ) : ℝ) ^ 2)))) := by ring
  have hsumnorm : Summable fun m ↦ ‖boundedBridgeLevel j m omega‖ :=
    (summable_bridgeGrowthSeries.mul_left _).of_nonneg_of_le
      (fun _ ↦ norm_nonneg _) hmajorant
  calc
    ‖bridgeSum j omega‖ =
        ‖∑' m, boundedBridgeLevel j m omega‖ := rfl
    _ ≤ ∑' m, ‖boundedBridgeLevel j m omega‖ :=
      norm_tsum_le_tsum_norm hsumnorm
    _ ≤ ∑' m, (((j + 1 : ℕ) : ℝ) * bridgeGrowthSeries m) :=
      hsumnorm.tsum_le_tsum hmajorant (summable_bridgeGrowthSeries.mul_left _)
    _ = (((j + 1 : ℕ) : ℝ) * bridgeGrowthConstant) := by
      exact (Summable.tsum_mul_left _ summable_bridgeGrowthSeries)

/-- Almost surely, every sufficiently late unit block of the concrete source
path has a quadratic-with-small-leading-coefficient uniform bound.  This is
the source-side estimate used to prove parabolic-drift escape. -/
theorem ae_globalPath_unitBlock_growth :
    ∀ᵐ omega ∂gaussianSource, ∃ A C : ℝ, 0 ≤ A ∧ 0 ≤ C ∧
      ∀ᶠ j in atTop, ∀ x : unitInterval,
        |globalPath omega (unitTime j x)| ≤
          A + (j : ℝ) ^ 2 / 16 + C * (j + 1) := by
  filter_upwards [ae_goodSample, ae_eventually_affine_growth,
    ae_eventually_pairedBridge_growth] with omega homega haffine hbridge
  rcases eventually_atTop.1 haffine with ⟨Na, ha⟩
  rcases eventually_atTop.1 hbridge with ⟨Nb, hb⟩
  let N := max Na Nb
  let A : ℝ := ∑ l ∈ Finset.range N, |coordinate (l, Sum.inl ()) omega|
  let C : ℝ := (1 / 16 : ℝ) + bridgeGrowthConstant
  refine ⟨A, C, ?_, ?_, ?_⟩
  · exact Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
  · dsimp [C]
    exact add_nonneg (by norm_num) bridgeGrowthConstant_nonneg
  · filter_upwards [eventually_ge_atTop N] with j hj
    intro x
    have hNa : Na ≤ j := (le_max_left Na Nb).trans hj
    have hNb : Nb ≤ j := (le_max_right Na Nb).trans hj
    have hsum_tail :
        ∑ l ∈ Finset.Ico N j, |coordinate (l, Sum.inl ()) omega| ≤
          (j : ℝ) ^ 2 / 16 := by
      calc
        ∑ l ∈ Finset.Ico N j, |coordinate (l, Sum.inl ()) omega|
            ≤ ∑ l ∈ Finset.Ico N j, (((l + 1 : ℕ) : ℝ) / 16) := by
              apply Finset.sum_le_sum
              intro l hl
              exact ha l ((le_max_left Na Nb).trans (Finset.mem_Ico.mp hl).1)
        _ ≤ ∑ _l ∈ Finset.Ico N j, ((j : ℝ) / 16) := by
              apply Finset.sum_le_sum
              intro l hl
              have hlj : l + 1 ≤ j := Finset.mem_Ico.mp hl |>.2
              gcongr
        _ ≤ ∑ _l ∈ Finset.range j, ((j : ℝ) / 16) := by
              apply Finset.sum_le_sum_of_subset_of_nonneg
              · intro l hl
                exact Finset.mem_range.mpr (Finset.mem_Ico.mp hl).2
              · intro l hl _hnot
                positivity
        _ = (j : ℝ) ^ 2 / 16 := by
              simp
              ring
    have hsum :
        |∑ l ∈ Finset.range j, coordinate (l, Sum.inl ()) omega| ≤
          A + (j : ℝ) ^ 2 / 16 := by
      have hsplit :
          (∑ l ∈ Finset.range j, coordinate (l, Sum.inl ()) omega) =
            (∑ l ∈ Finset.range N, coordinate (l, Sum.inl ()) omega) +
              ∑ l ∈ Finset.Ico N j, coordinate (l, Sum.inl ()) omega := by
        exact (Finset.sum_range_add_sum_Ico _ hj).symm
      rw [hsplit]
      calc
        |(∑ l ∈ Finset.range N, coordinate (l, Sum.inl ()) omega) +
            ∑ l ∈ Finset.Ico N j, coordinate (l, Sum.inl ()) omega|
            ≤ |∑ l ∈ Finset.range N, coordinate (l, Sum.inl ()) omega| +
                |∑ l ∈ Finset.Ico N j, coordinate (l, Sum.inl ()) omega| :=
              abs_add_le _ _
        _ ≤ A + ∑ l ∈ Finset.Ico N j,
              |coordinate (l, Sum.inl ()) omega| := by
              gcongr
              · exact Finset.abs_sum_le_sum_abs _ _
              · exact Finset.abs_sum_le_sum_abs _ _
        _ ≤ A + (j : ℝ) ^ 2 / 16 := by gcongr
    have hblock : |unitBlock j omega x| ≤ C * (j + 1) := by
      rw [unitBlock, ContinuousMap.add_apply]
      calc
        |affineMap j omega x + bridgeSum j omega x|
            ≤ |affineMap j omega x| + |bridgeSum j omega x| := abs_add_le _ _
        _ ≤ (((j + 1 : ℕ) : ℝ) / 16) + ‖bridgeSum j omega‖ := by
              gcongr
              · simp only [affineMap, ContinuousMap.smul_apply, smul_eq_mul,
                  unitLinear_apply, abs_mul]
                calc
                  |coordinate (j, Sum.inl ()) omega| * |(x : ℝ)|
                      ≤ |coordinate (j, Sum.inl ()) omega| * 1 := by
                        gcongr
                        rw [abs_of_nonneg x.property.1]
                        exact x.property.2
                  _ ≤ (((j + 1 : ℕ) : ℝ) / 16) := by
                        simpa using! ha j hNa
              · simpa only [Real.norm_eq_abs] using!
                  (ContinuousMap.norm_coe_le_norm (bridgeSum j omega) x)
        _ ≤ (((j + 1 : ℕ) : ℝ) / 16) +
              (((j + 1 : ℕ) : ℝ) * bridgeGrowthConstant) := by
              gcongr
              exact bridgeSum_norm_growth homega hb hNb
        _ = C * (j + 1) := by
              dsimp [C]
              push_cast
              ring
    rw [globalPath_unitTime]
    calc
      |(∑ l ∈ Finset.range j, coordinate (l, Sum.inl ()) omega) +
          unitBlock j omega x|
          ≤ |∑ l ∈ Finset.range j, coordinate (l, Sum.inl ()) omega| +
              |unitBlock j omega x| := abs_add_le _ _
      _ ≤ (A + (j : ℝ) ^ 2 / 16) + C * (j + 1) := by gcongr
      _ = A + (j : ℝ) ^ 2 / 16 + C * (j + 1) := by ring

/-! ### Deterministic Brownian shifts

The shift is constructed as an actual element of the existing compact-open
path space.  Its law is identified from the already verified arbitrary-time
increment vectors, so no second Gaussian construction is introduced. -/

def brownianShift (t : NNReal) (w : BrownianPath) : BrownianPath where
  toFun u := w (t + u) - w t
  continuous_toFun :=
    (w.continuous.comp (continuous_const.add continuous_id)).sub continuous_const

@[simp] theorem brownianShift_apply (t u : NNReal) (w : BrownianPath) :
    brownianShift t w u = w (t + u) - w t := rfl

@[simp] theorem brownianShift_zero (t : NNReal) (w : BrownianPath) :
    brownianShift t w 0 = 0 := by simp

@[simp] theorem brownianShift_add (s t : NNReal) (w : BrownianPath) :
    brownianShift s (brownianShift t w) = brownianShift (t + s) w := by
  ext u
  change (w (t + (s + u)) - w t) - (w (t + s) - w t) =
    w ((t + s) + u) - w (t + s)
  rw [add_assoc]
  ring

private lemma summable_gaussian_level_budget (d : ℝ) (hd : 0 < d)
    (m : ℕ → ℕ) : Summable (fun n : ℕ ↦
      (2 : ℝ) ^ (m n) * (2 * Real.exp
        (-d * (n + 1) * ((m n : ℝ) + 1) ^ 2))) := by
  have hr : ‖Real.exp (-d / 2)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_lt_one_iff]
    linarith
  have hg : Summable (fun n : ℕ ↦ Real.exp (-d / 2) ^ (n + 1)) :=
    (summable_geometric_of_norm_lt_one hr).comp_injective
      (fun _ _ h ↦ Nat.add_right_cancel h)
  apply hg.of_norm_bounded_eventually_nat
  obtain ⟨N, hN⟩ := exists_nat_gt (2 / d)
  filter_upwards [eventually_ge_atTop N] with n hn
  have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hx : 2 ≤ d * ((n : ℝ) + 1) := by
    have := (div_lt_iff₀ hd).mp (hN.trans_le hn')
    nlinarith
  have hy : (1 : ℝ) ≤ (m n : ℝ) + 1 := by have : 0 ≤ (m n : ℝ) := Nat.cast_nonneg _; linarith
  have hsq : ((m n : ℝ) + 1) ≤ ((m n : ℝ) + 1) ^ 2 := by nlinarith
  have hprod := mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ d * ((n : ℝ) + 1))
  have hcross := mul_nonneg (sub_nonneg.mpr hx) (by positivity : 0 ≤ (m n : ℝ))
  have he : (m n : ℝ) + 1 - d * ((n : ℝ) + 1) * ((m n : ℝ) + 1) ^ 2 ≤
      ((n : ℝ) + 1) * (-d / 2) := by nlinarith
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by
    simpa only [one_add_one_eq_two] using! Real.add_one_le_exp (1 : ℝ)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc
    (2 : ℝ) ^ m n * (2 * Real.exp
        (-d * (n + 1) * ((m n : ℝ) + 1) ^ 2)) =
      (2 : ℝ) ^ (m n + 1) * Real.exp
        (-d * (n + 1) * ((m n : ℝ) + 1) ^ 2) := by rw [pow_succ]; ring
    _ ≤ (Real.exp 1) ^ (m n + 1) * Real.exp
        (-d * (n + 1) * ((m n : ℝ) + 1) ^ 2) := by
      gcongr
    _ = Real.exp ((m n : ℝ) + 1 - d * (n + 1) * ((m n : ℝ) + 1) ^ 2) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      push_cast
      ring
    _ ≤ Real.exp (((n : ℝ) + 1) * (-d / 2)) := Real.exp_le_exp.mpr he
    _ = Real.exp (-d / 2) ^ (n + 1) := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring

private lemma measure_tsum_ne_top_of_summable_real
    (E : ℕ → Set GaussianSample)
    (h : Summable (fun n ↦ gaussianSource.real (E n))) :
    (∑' n, gaussianSource (E n)) ≠ ∞ := by
  let p : ℕ → NNReal := fun n ↦ NNReal.mk (gaussianSource.real (E n)) (measureReal_nonneg)
  have hp : Summable (fun n ↦ (p n : ℝ)) := h
  have ht := ENNReal.tsum_coe_ne_top_iff_summable_coe.mpr hp
  have heq : (fun n ↦ (p n : ENNReal)) = fun n ↦ gaussianSource (E n) := by
    funext n
    exact (ENNReal.ofReal_eq_coe_nnreal measureReal_nonneg).symm.trans ofReal_measureReal
  rwa [heq] at ht

private def smallAffineBad (eps : ℝ) (j : ℕ) : Set GaussianSample :=
  {omega | eps * ((j : ℝ) + 1) < |coordinate (j, Sum.inl ()) omega|}

private lemma ae_eventually_smallAffine (eps : ℝ) (heps : 0 < eps) :
    ∀ᵐ omega ∂gaussianSource, ∀ᶠ j in atTop,
      |coordinate (j, Sum.inl ()) omega| ≤ eps * ((j : ℝ) + 1) := by
  have hbound (j : ℕ) : gaussianSource.real (smallAffineBad eps j) ≤
      2 * Real.exp (-(eps ^ 2 / 2) * ((j : ℝ) + 1)) := by
    have hlaw : gaussianSource.real (smallAffineBad eps j) =
        (gaussianReal 0 1).real {z | eps * ((j : ℝ) + 1) < |z|} := by
      rw [← coordinate_law (j, Sum.inl ()), Measure.real, Measure.real,
        Measure.map_apply_of_aemeasurable (measurable_coordinate _).aemeasurable]
      · rfl
      · exact measurableSet_lt measurable_const (measurable_abs.comp measurable_id)
    rw [hlaw]
    refine (standardGaussian_abs_tail (by positivity)).trans ?_
    have hj : (1 : ℝ) ≤ (j : ℝ) + 1 := by have : 0 ≤ (j : ℝ) := Nat.cast_nonneg _; linarith
    have hs : ((j : ℝ) + 1) ≤ ((j : ℝ) + 1) ^ 2 := by nlinarith
    have he := mul_le_mul_of_nonneg_left hs (sq_nonneg eps)
    gcongr
    nlinarith
  have hs := summable_gaussian_level_budget (eps ^ 2 / 2) (by positivity)
    (fun _ ↦ 0)
  have hsum : Summable (fun j ↦ gaussianSource.real (smallAffineBad eps j)) := by
    apply hs.of_nonneg_of_le (fun _ ↦ measureReal_nonneg)
    intro j
    simpa using! hbound j
  filter_upwards [ae_eventually_notMem
    (measure_tsum_ne_top_of_summable_real _ hsum)] with omega ho
  filter_upwards [ho] with j hj
  simpa only [smallAffineBad, Set.mem_setOf_eq, not_lt] using! hj

private def smallBridgeBad (eps : ℝ) (n : ℕ) : Set GaussianSample :=
  {omega | eps * (pairedBridgeThreshold n : ℝ) <
    (coefficientMax (Nat.unpair n).1 (Nat.unpair n).2 omega : ℝ)}

private lemma smallBridgeBad_measureReal_le (eps : ℝ) (heps : 0 < eps) (n : ℕ) :
    gaussianSource.real (smallBridgeBad eps n) ≤
      (2 ^ (Nat.unpair n).2 : ℝ) *
        (2 * Real.exp (-(8 * eps ^ 2) * ((n : ℝ) + 1) *
          (((Nat.unpair n).2 : ℝ) + 1) ^ 2)) := by
  let E (k : Fin (2 ^ (Nat.unpair n).2)) : Set GaussianSample :=
    {omega | eps * (pairedBridgeThreshold n : ℝ) <
      |coordinate ((Nat.unpair n).1, Sum.inr ⟨(Nat.unpair n).2, k⟩) omega|}
  have hunion : smallBridgeBad eps n = ⋃ k, E k := by
    ext omega
    simp only [smallBridgeBad, E, Set.mem_setOf_eq, Set.mem_iUnion]
    have hnn : 0 ≤ eps * (pairedBridgeThreshold n : ℝ) := by positivity
    let r : NNReal := NNReal.mk (eps * (pairedBridgeThreshold n : ℝ)) (hnn)
    change (r : ℝ) < (coefficientMax _ _ omega : ℝ) ↔ _
    rw [NNReal.coe_lt_coe]
    unfold coefficientMax
    constructor
    · intro h
      obtain ⟨k, _, hk⟩ := Finset.lt_sup_iff.mp h
      exact ⟨k, by exact_mod_cast hk⟩
    · rintro ⟨k, hk⟩
      exact Finset.lt_sup_iff.mpr ⟨k, Finset.mem_univ _, by exact_mod_cast hk⟩
  have hcoord (k : Fin (2 ^ (Nat.unpair n).2)) :
      gaussianSource.real (E k) ≤ 2 * Real.exp (-(eps * (pairedBridgeThreshold n : ℝ)) ^ 2 / 2) := by
    have hlaw : gaussianSource.real (E k) =
        (gaussianReal 0 1).real {z | eps * (pairedBridgeThreshold n : ℝ) < |z|} := by
      rw [← coordinate_law ((Nat.unpair n).1, Sum.inr ⟨(Nat.unpair n).2, k⟩),
        Measure.real, Measure.real,
        Measure.map_apply_of_aemeasurable (measurable_coordinate _).aemeasurable]
      · rfl
      · exact measurableSet_lt measurable_const (measurable_abs.comp measurable_id)
    rw [hlaw]
    exact standardGaussian_abs_tail (by positivity)
  have hthreshold : -(eps * (pairedBridgeThreshold n : ℝ)) ^ 2 / 2 =
      -(8 * eps ^ 2) * ((n : ℝ) + 1) * (((Nat.unpair n).2 : ℝ) + 1) ^ 2 := by
    simp only [pairedBridgeThreshold, NNReal.coe_mk, mul_pow]
    rw [Real.sq_sqrt (by positivity)]
    push_cast
    ring
  rw [hunion]
  calc
    gaussianSource.real (⋃ k, E k) ≤ ∑ k, gaussianSource.real (E k) := by
      simpa using! measureReal_biUnion_finset_le Finset.univ E
    _ ≤ ∑ _k : Fin (2 ^ (Nat.unpair n).2),
        2 * Real.exp (-(eps * (pairedBridgeThreshold n : ℝ)) ^ 2 / 2) :=
      Finset.sum_le_sum (fun k _ ↦ hcoord k)
    _ = _ := by rw [hthreshold]; simp

private lemma ae_eventually_smallBridge (eps : ℝ) (heps : 0 < eps) :
    ∀ᵐ omega ∂gaussianSource, ∀ᶠ n in atTop,
      (coefficientMax (Nat.unpair n).1 (Nat.unpair n).2 omega : ℝ) ≤
        eps * (pairedBridgeThreshold n : ℝ) := by
  have hsum : Summable (fun n ↦ gaussianSource.real (smallBridgeBad eps n)) :=
    (summable_gaussian_level_budget (8 * eps ^ 2) (by positivity)
      (fun n ↦ (Nat.unpair n).2)).of_nonneg_of_le
        (fun _ ↦ measureReal_nonneg) (smallBridgeBad_measureReal_le eps heps)
  filter_upwards [ae_eventually_notMem
    (measure_tsum_ne_top_of_summable_real _ hsum)] with omega ho
  filter_upwards [ho] with n hn
  simpa only [smallBridgeBad, Set.mem_setOf_eq, not_lt] using! hn

private lemma small_coefficientMax_of_eventual
    {omega : GaussianSample} {eps : ℝ} (heps : 0 < eps) {N j : ℕ}
    (hpair : ∀ n ≥ N,
      (coefficientMax (Nat.unpair n).1 (Nat.unpair n).2 omega : ℝ) ≤
        eps * (pairedBridgeThreshold n : ℝ)) (hj : N ≤ j) (m : ℕ) :
    (coefficientMax j m omega : ℝ) ≤
      eps * (4 * (((j + 1 : ℕ) : ℝ)) * (((m + 1 : ℕ) : ℝ) ^ 2)) := by
  have hn := hpair (Nat.pair j m) (hj.trans (Nat.left_le_pair j m))
  rw [Nat.unpair_pair] at hn
  refine hn.trans (mul_le_mul_of_nonneg_left ?_ heps.le)
  have hp : ((Nat.pair j m + 1 : ℕ) : ℝ) ≤
      (((max j m + 1 : ℕ) : ℝ) ^ 2) := by
    exact_mod_cast Nat.succ_le_iff.mpr (Nat.pair_lt_max_add_one_sq j m)
  have hs : Real.sqrt (((Nat.pair j m + 1 : ℕ) : ℝ)) ≤
      ((max j m + 1 : ℕ) : ℝ) := Real.sqrt_le_iff.mpr ⟨by positivity, hp⟩
  have hm : max j m + 1 ≤ (j + 1) * (m + 1) := by
    have : max j m ≤ j + m := max_le (by omega) (by omega)
    nlinarith [Nat.zero_le (j * m)]
  have hm' : ((max j m + 1 : ℕ) : ℝ) ≤
      ((j + 1 : ℕ) : ℝ) * ((m + 1 : ℕ) : ℝ) := by exact_mod_cast hm
  simp only [pairedBridgeThreshold, NNReal.coe_mk, Nat.unpair_pair]
  calc
    4 * Real.sqrt (((Nat.pair j m + 1 : ℕ) : ℝ)) * ((m + 1 : ℕ) : ℝ) ≤
      4 * (((j + 1 : ℕ) : ℝ) * ((m + 1 : ℕ) : ℝ)) * ((m + 1 : ℕ) : ℝ) := by
        gcongr
        exact hs.trans hm'
    _ = _ := by ring

private lemma small_bridgeSum_norm {omega : GaussianSample}
    {eps : ℝ} (heps : 0 < eps) {N j : ℕ}
    (hpair : ∀ n ≥ N,
      (coefficientMax (Nat.unpair n).1 (Nat.unpair n).2 omega : ℝ) ≤
        eps * (pairedBridgeThreshold n : ℝ)) (hj : N ≤ j) :
    ‖bridgeSum j omega‖ ≤ eps * ((j : ℝ) + 1) * bridgeGrowthConstant := by
  have hb (m : ℕ) : ‖boundedBridgeLevel j m omega‖ ≤
      (eps * ((j : ℝ) + 1)) * bridgeGrowthSeries m := by
    rw [boundedBridgeLevel_norm]
    refine (bridgeLevel_norm_bound j m omega).trans ?_
    have hc := small_coefficientMax_of_eventual heps hpair hj m
    calc
      hatScale m * (coefficientMax j m omega : ℝ) ≤
        hatScale m * (eps * (4 * ((j + 1 : ℕ) : ℝ) * ((m + 1 : ℕ) : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left hc (hatScale_pos m).le
      _ = _ := by unfold bridgeGrowthSeries; push_cast; ring
  have hs : Summable (fun m ↦ ‖boundedBridgeLevel j m omega‖) :=
    (summable_bridgeGrowthSeries.mul_left _).of_nonneg_of_le (fun _ ↦ norm_nonneg _) hb
  calc
    ‖bridgeSum j omega‖ ≤ ∑' m, ‖boundedBridgeLevel j m omega‖ :=
      norm_tsum_le_tsum_norm hs
    _ ≤ ∑' m, (eps * ((j : ℝ) + 1)) * bridgeGrowthSeries m :=
      hs.tsum_le_tsum hb (summable_bridgeGrowthSeries.mul_left _)
    _ = _ := Summable.tsum_mul_left _ summable_bridgeGrowthSeries

/-- Every positive linear cutoff eventually bounds the local increments of
all unit blocks, almost surely in the concrete Gaussian construction. -/
theorem ae_globalPath_unitIncrement_small (eps : ℝ) (heps : 0 < eps) :
    ∀ᵐ omega ∂gaussianSource, ∀ᶠ j in atTop, ∀ x : unitInterval,
      |globalPath omega (unitTime j x) - globalPath omega (j : NNReal)| ≤
        eps * ((j : ℝ) + 1) := by
  let e : ℝ := eps / (1 + bridgeGrowthConstant)
  have hden : 0 < 1 + bridgeGrowthConstant := by linarith [bridgeGrowthConstant_nonneg]
  have he : 0 < e := div_pos heps hden
  filter_upwards [ae_goodSample, ae_eventually_smallAffine e he,
    ae_eventually_smallBridge e he] with omega homega ha hb
  obtain ⟨N, hN⟩ := eventually_atTop.mp hb
  filter_upwards [ha, eventually_ge_atTop N] with j hj hjN
  intro x
  have hzero : globalPath omega (j : NNReal) =
      ∑ l ∈ Finset.range j, coordinate (l, Sum.inl ()) omega := by
    let z : unitInterval := ⟨0, by constructor <;> norm_num⟩
    have hz := globalPath_unitTime omega j z
    have ht : unitTime j z = (j : NNReal) := by
      ext
      change (j : ℝ) + 0 = (j : ℝ)
      ring
    rw [ht, unitBlock_zero homega j, add_zero] at hz
    exact hz
  rw [globalPath_unitTime, hzero, add_sub_cancel_left]
  have hx : |affineMap j omega x| ≤ e * ((j : ℝ) + 1) := by
    simp only [affineMap, ContinuousMap.smul_apply, smul_eq_mul, unitLinear_apply, abs_mul]
    calc
      |coordinate (j, Sum.inl ()) omega| * |(x : ℝ)| ≤
        |coordinate (j, Sum.inl ()) omega| * 1 := by
          gcongr
          rw [abs_of_nonneg x.property.1]
          exact x.property.2
      _ ≤ _ := by simpa using! hj
  have hbridge : |bridgeSum j omega x| ≤ e * ((j : ℝ) + 1) * bridgeGrowthConstant := by
    calc
      |bridgeSum j omega x| ≤ ‖bridgeSum j omega‖ := by
        simpa only [Real.norm_eq_abs] using!
          ContinuousMap.norm_coe_le_norm (bridgeSum j omega) x
      _ ≤ _ := small_bridgeSum_norm he hN hjN
  rw [unitBlock, ContinuousMap.add_apply]
  calc
    |affineMap j omega x + bridgeSum j omega x| ≤
      |affineMap j omega x| + |bridgeSum j omega x| := abs_add_le _ _
    _ ≤ e * ((j : ℝ) + 1) + e * ((j : ℝ) + 1) * bridgeGrowthConstant := add_le_add hx hbridge
    _ = eps * ((j : ℝ) + 1) := by
      dsimp [e]
      field_simp [ne_of_gt hden]

end

end Erdos745.WrapUp.Proofs.Internal.W13_BROWNIAN_Law


namespace Erdos745.WrapUp.Proofs.Internal.W13_BROWNIAN_Ranks

noncomputable section
open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal Topology

local instance : MeasurableSpace BrownianPath := borel BrownianPath
local instance : BorelSpace BrownianPath := ⟨rfl⟩

private lemma continuous_drift_fixedTime (lam : ℝ) (t : NNReal) :
    Continuous (fun w : BrownianPath ↦ drift w lam t) := by
  unfold drift
  fun_prop

private def unitNNReal (x : unitInterval) : NNReal :=
  NNReal.mk ((x : ℝ)) (x.property.1)

private def scaleToTime (t : NNReal) (x : unitInterval) : NNReal :=
  t * unitNNReal x

private lemma scaleToTime_image (t : NNReal) :
    scaleToTime t '' Set.univ = Set.Icc 0 t := by
  ext u
  constructor
  · rintro ⟨x, _hx, rfl⟩
    constructor
    · exact zero_le
    · exact mul_le_of_le_one_right (zero_le) (by
        exact_mod_cast x.property.2)
  · intro hu
    by_cases ht : t = 0
    · subst t
      have hu0 : u = 0 := le_antisymm hu.2 hu.1
      subst u
      refine ⟨(0 : unitInterval), Set.mem_univ _, ?_⟩
      simp [scaleToTime, unitNNReal]
    · have htpos : 0 < (t : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr ht)
      let x : unitInterval :=
        ⟨(u : ℝ) / (t : ℝ), by
          constructor
          · positivity
          · exact (div_le_one htpos).2 (by exact_mod_cast hu.2)⟩
      refine ⟨x, Set.mem_univ _, ?_⟩
      apply NNReal.eq
      simp only [scaleToTime, unitNNReal, NNReal.coe_mul, NNReal.coe_mk, x]
      field_simp

private lemma continuous_scaleToTime :
    Continuous (Function.uncurry scaleToTime) := by
  unfold scaleToTime unitNNReal
  fun_prop

private def runningInfParam (w : BrownianPath) (lam : ℝ) (t : NNReal) : ℝ :=
  sInf ((fun x : unitInterval ↦ drift w lam (scaleToTime t x)) '' Set.univ)

private lemma runningInfParam_eq (w : BrownianPath) (lam : ℝ) (t : NNReal) :
    runningInfParam w lam t = sInf ((drift w lam) '' Set.Icc 0 t) := by
  unfold runningInfParam
  rw [← scaleToTime_image t, Set.image_image]

private lemma continuous_runningInf_joint (lam : ℝ) :
    Continuous (fun p : BrownianPath × NNReal ↦ runningInfParam p.1 lam p.2) := by
  unfold runningInfParam
  apply isCompact_univ.continuous_sInf
  unfold drift
  have htime : Continuous (fun p : (BrownianPath × NNReal) × unitInterval ↦
      scaleToTime p.1.2 p.2) :=
    continuous_scaleToTime.comp (continuous_fst.snd.prodMk continuous_snd)
  have hw : Continuous (fun p : (BrownianPath × NNReal) × unitInterval ↦ p.1.1) :=
    continuous_fst.fst
  have heval : Continuous (fun p : (BrownianPath × NNReal) × unitInterval ↦
      p.1.1 (scaleToTime p.1.2 p.2)) :=
    ContinuousEval.continuous_eval.comp (hw.prodMk htime)
  have htimeReal : Continuous (fun p : (BrownianPath × NNReal) × unitInterval ↦
      (scaleToTime p.1.2 p.2 : ℝ)) := continuous_subtype_val.comp htime
  exact (heval.add (continuous_const.mul htimeReal)).sub
    ((htimeReal.pow 2).div_const 2)

theorem continuous_reflected_joint (lam : ℝ) :
    Continuous (fun p : BrownianPath × NNReal ↦ reflected p.1 lam p.2) := by
  have hrun := continuous_runningInf_joint lam
  have hdrift : Continuous (fun p : BrownianPath × NNReal ↦ drift p.1 lam p.2) := by
    unfold drift
    fun_prop
  apply Continuous.congr (hdrift.sub hrun)
  intro p
  rw [Pi.sub_apply, reflected, runningInfParam_eq]

private def intervalTime (a b : NNReal) (x : unitInterval) : NNReal :=
  a + (b - a) * unitNNReal x

private lemma intervalTime_image {a b : NNReal} (hab : a ≤ b) :
    intervalTime a b '' Set.univ = Set.Icc a b := by
  ext u
  constructor
  · rintro ⟨x, _hx, rfl⟩
    constructor
    · exact le_add_of_nonneg_right (zero_le)
    · calc
        intervalTime a b x
            ≤ a + (b - a) := by
              unfold intervalTime
              gcongr
              exact mul_le_of_le_one_right (zero_le) (by
                exact_mod_cast x.property.2)
        _ = b := add_tsub_cancel_of_le hab
  · intro hu
    have hv : u - a ∈ Set.Icc (0 : NNReal) (b - a) := by
      constructor
      · exact zero_le
      · exact tsub_le_tsub_right hu.2 a
    rw [← scaleToTime_image (b - a)] at hv
    rcases hv with ⟨x, _hx, hx⟩
    refine ⟨x, Set.mem_univ _, ?_⟩
    unfold intervalTime
    change a + scaleToTime (b - a) x = u
    rw [hx, add_tsub_cancel_of_le hu.1]

def reflectedIntervalInf (lam : ℝ) (a b : NNReal) (w : BrownianPath) : ℝ :=
  sInf ((fun x : unitInterval ↦ reflected w lam (intervalTime a b x)) '' Set.univ)

theorem continuous_reflectedIntervalInf (lam : ℝ) (a b : NNReal) :
    Continuous (reflectedIntervalInf lam a b) := by
  unfold reflectedIntervalInf
  apply isCompact_univ.continuous_sInf
  have htime : Continuous (fun p : BrownianPath × unitInterval ↦
      intervalTime a b p.2) := by
    unfold intervalTime unitNNReal
    fun_prop
  exact (continuous_reflected_joint lam).comp (continuous_fst.prodMk htime)

theorem measurable_reflectedIntervalInf (lam : ℝ) (a b : NNReal) :
    Measurable (reflectedIntervalInf lam a b) :=
  (continuous_reflectedIntervalInf lam a b).measurable

private lemma compact_drift_image (w : BrownianPath) (lam : ℝ) (t : NNReal) :
    IsCompact ((drift w lam) '' Set.Icc 0 t) := by
  rw [← scaleToTime_image t, Set.image_image]
  apply isCompact_univ.image
  unfold drift scaleToTime unitNNReal
  fun_prop

theorem reflected_nonneg (w : BrownianPath) (lam : ℝ) (t : NNReal) :
    0 ≤ reflected w lam t := by
  unfold reflected
  apply sub_nonneg.mpr
  apply csInf_le (compact_drift_image w lam t).bddBelow
  exact ⟨t, ⟨zero_le, le_rfl⟩, rfl⟩

theorem reflectedIntervalInf_nonneg (w : BrownianPath) (lam : ℝ)
    (a b : NNReal) : 0 ≤ reflectedIntervalInf lam a b w := by
  unfold reflectedIntervalInf
  apply le_csInf
  · have hzero : intervalTime a b (0 : unitInterval) = a := by
      apply NNReal.eq
      simp [intervalTime, unitNNReal]
    exact ⟨reflected w lam a, (0 : unitInterval), Set.mem_univ _, by
      change reflected w lam (intervalTime a b 0) = reflected w lam a
      rw [hzero]⟩
  · rintro y ⟨x, _hx, rfl⟩
    exact reflected_nonneg w lam (intervalTime a b x)

private lemma compact_reflectedInterval_image (w : BrownianPath) (lam : ℝ)
    (a b : NNReal) :
    IsCompact ((fun x : unitInterval ↦ reflected w lam (intervalTime a b x)) '' Set.univ) := by
  apply isCompact_univ.image
  exact (continuous_reflected_joint lam).comp (continuous_const.prodMk (by
    unfold unitNNReal
    fun_prop))

theorem reflectedIntervalInf_eq_zero_iff (w : BrownianPath) (lam : ℝ)
    (a b : NNReal) :
    reflectedIntervalInf lam a b w = 0 ↔
      ∃ x : unitInterval, reflected w lam (intervalTime a b x) = 0 := by
  let K := (fun x : unitInterval ↦ reflected w lam (intervalTime a b x)) '' Set.univ
  have hK : IsCompact K := compact_reflectedInterval_image w lam a b
  have hKne : K.Nonempty := ⟨reflected w lam (intervalTime a b 0),
    ⟨0, Set.mem_univ _, rfl⟩⟩
  constructor
  · intro hzero
    change sInf K = 0 at hzero
    have hmem := hK.sInf_mem hKne
    rw [hzero] at hmem
    rcases hmem with ⟨x, _hx, hx⟩
    exact ⟨x, hx⟩
  · rintro ⟨x, hx⟩
    apply le_antisymm
    · apply csInf_le hK.bddBelow
      exact ⟨x, Set.mem_univ _, hx⟩
    · exact reflectedIntervalInf_nonneg w lam a b

theorem measurableSet_reflectedIntervalInf_eq_zero (lam : ℝ) (a b : NNReal) :
    MeasurableSet {w : BrownianPath | reflectedIntervalInf lam a b w = 0} :=
  (measurable_reflectedIntervalInf lam a b)
    (measurableSet_singleton (0 : ℝ))

private lemma continuous_runningInf_fixedTime (lam : ℝ) (t : NNReal) :
    Continuous (fun w : BrownianPath ↦
      sInf ((drift w lam) '' Set.Icc 0 t)) := by
  simpa only [runningInfParam_eq] using!
    (continuous_runningInf_joint lam).comp (continuous_id.prodMk continuous_const)

theorem continuous_reflected_fixedTime (lam : ℝ) (t : NNReal) :
    Continuous (fun w : BrownianPath ↦ reflected w lam t) := by
  unfold reflected
  exact (continuous_drift_fixedTime lam t).sub
    (continuous_runningInf_fixedTime lam t)

theorem measurable_reflected_fixedTime (lam : ℝ) (t : NNReal) :
    Measurable (fun w : BrownianPath ↦ reflected w lam t) :=
  (continuous_reflected_fixedTime lam t).measurable

/-! ### Countable measurable excursion data

The dense probes below implement the endpoint formulas from B01 without a
measurable-selection principle.  A probe contributes to the left endpoint
exactly when the compact interval from that probe to `q` contains a zero.  A
probe contributes to the right endpoint under the analogous condition.  The
countable supremum/infimum therefore remains meaningful on every path,
including paths for which there is no later zero.
-/

private def denseTime (n : ℕ) : NNReal :=
  TopologicalSpace.denseSeq NNReal n

private def leftProbeCondition (lam : ℝ) (q : NNReal) (k : ℕ)
    (w : BrownianPath) : Prop :=
  denseTime k ≤ q ∧ reflectedIntervalInf lam (denseTime k) q w = 0

private def rightProbeCondition (lam : ℝ) (q : NNReal) (k : ℕ)
    (w : BrownianPath) : Prop :=
  q ≤ denseTime k ∧ reflectedIntervalInf lam q (denseTime k) w = 0

private lemma measurableSet_leftProbeCondition
    (lam : ℝ) (q : NNReal) (k : ℕ) :
    MeasurableSet {w : BrownianPath | leftProbeCondition lam q k w} := by
  by_cases hk : denseTime k ≤ q
  · simpa only [leftProbeCondition, hk, true_and] using!
      measurableSet_reflectedIntervalInf_eq_zero lam (denseTime k) q
  · simp only [leftProbeCondition, hk, false_and, Set.setOf_false,
      MeasurableSet.empty]

private lemma measurableSet_rightProbeCondition
    (lam : ℝ) (q : NNReal) (k : ℕ) :
    MeasurableSet {w : BrownianPath | rightProbeCondition lam q k w} := by
  by_cases hk : q ≤ denseTime k
  · simpa only [rightProbeCondition, hk, true_and] using!
      measurableSet_reflectedIntervalInf_eq_zero lam q (denseTime k)
  · simp only [rightProbeCondition, hk, false_and, Set.setOf_false,
      MeasurableSet.empty]

private lemma leftProbeCondition_iff_of_excursion
    (w : BrownianPath) (lam : ℝ) {a b q : NNReal}
    (hab : excursion w lam a b) (hq : q ∈ Set.Ioo a b) (k : ℕ) :
    leftProbeCondition lam q k w ↔ denseTime k ≤ a := by
  constructor
  · rintro ⟨hkq, hkzero⟩
    rcases (reflectedIntervalInf_eq_zero_iff w lam (denseTime k) q).mp hkzero with
      ⟨x, hxzero⟩
    have htime : intervalTime (denseTime k) q x ∈ Set.Icc (denseTime k) q := by
      rw [← intervalTime_image hkq]
      exact ⟨x, Set.mem_univ _, rfl⟩
    have htime_le_a : intervalTime (denseTime k) q x ≤ a := by
      by_contra hta
      have hatime : a < intervalTime (denseTime k) q x := lt_of_not_ge hta
      have htimeb : intervalTime (denseTime k) q x < b := htime.2.trans_lt hq.2
      have hpositive := hab.2.2.2 (intervalTime (denseTime k) q x) ⟨hatime, htimeb⟩
      exact (ne_of_gt hpositive) hxzero
    exact htime.1.trans htime_le_a
  · intro hka
    have hkq : denseTime k ≤ q := hka.trans hq.1.le
    refine ⟨hkq, (reflectedIntervalInf_eq_zero_iff w lam (denseTime k) q).2 ?_⟩
    have ha_mem : a ∈ Set.Icc (denseTime k) q := ⟨hka, hq.1.le⟩
    rw [← intervalTime_image hkq] at ha_mem
    rcases ha_mem with ⟨x, _hx, hxa⟩
    exact ⟨x, by rw [hxa, hab.2.1]⟩

private lemma rightProbeCondition_iff_of_excursion
    (w : BrownianPath) (lam : ℝ) {a b q : NNReal}
    (hab : excursion w lam a b) (hq : q ∈ Set.Ioo a b) (k : ℕ) :
    rightProbeCondition lam q k w ↔ b ≤ denseTime k := by
  constructor
  · rintro ⟨hqk, hkzero⟩
    rcases (reflectedIntervalInf_eq_zero_iff w lam q (denseTime k)).mp hkzero with
      ⟨x, hxzero⟩
    have htime : intervalTime q (denseTime k) x ∈ Set.Icc q (denseTime k) := by
      rw [← intervalTime_image hqk]
      exact ⟨x, Set.mem_univ _, rfl⟩
    have hb_le_time : b ≤ intervalTime q (denseTime k) x := by
      by_contra hbt
      have htimeb : intervalTime q (denseTime k) x < b := lt_of_not_ge hbt
      have hatime : a < intervalTime q (denseTime k) x := hq.1.trans_le htime.1
      have hpositive := hab.2.2.2 (intervalTime q (denseTime k) x) ⟨hatime, htimeb⟩
      exact (ne_of_gt hpositive) hxzero
    exact hb_le_time.trans htime.2
  · intro hbk
    have hqk : q ≤ denseTime k := hq.2.le.trans hbk
    refine ⟨hqk, (reflectedIntervalInf_eq_zero_iff w lam q (denseTime k)).2 ?_⟩
    have hb_mem : b ∈ Set.Icc q (denseTime k) := ⟨hq.2.le, hbk⟩
    rw [← intervalTime_image hqk] at hb_mem
    rcases hb_mem with ⟨x, _hx, hxb⟩
    exact ⟨x, by rw [hxb, hab.2.2.1]⟩

private def excursionLeft (lam : ℝ) (q : NNReal) (w : BrownianPath) : ENNReal := by
  classical
  exact ⨆ k : ℕ, if leftProbeCondition lam q k w then (denseTime k : ENNReal) else 0

private def excursionRight (lam : ℝ) (q : NNReal) (w : BrownianPath) : ENNReal := by
  classical
  exact ⨅ k : ℕ, if rightProbeCondition lam q k w then (denseTime k : ENNReal) else ⊤

private lemma measurable_excursionLeft (lam : ℝ) (q : NNReal) :
    Measurable (excursionLeft lam q) := by
  classical
  unfold excursionLeft
  apply Measurable.iSup
  intro k
  exact Measurable.ite (measurableSet_leftProbeCondition lam q k)
    measurable_const measurable_const

private lemma measurable_excursionRight (lam : ℝ) (q : NNReal) :
    Measurable (excursionRight lam q) := by
  classical
  unfold excursionRight
  apply Measurable.iInf
  intro k
  exact Measurable.ite (measurableSet_rightProbeCondition lam q k)
    measurable_const measurable_const

private lemma excursionLeft_eq_of_excursion
    (w : BrownianPath) (lam : ℝ) {a b q : NNReal}
    (hab : excursion w lam a b) (hq : q ∈ Set.Ioo a b) :
    excursionLeft lam q w = (a : ENNReal) := by
  classical
  unfold excursionLeft
  apply le_antisymm
  · apply iSup_le
    intro k
    split_ifs with hk
    · exact_mod_cast (leftProbeCondition_iff_of_excursion w lam hab hq k).mp hk
    · exact bot_le
  · by_cases ha : a = 0
    · subst a
      exact bot_le
    · have h0a : (0 : NNReal) < a := pos_iff_ne_zero.mpr ha
      have hdense : Dense (Set.range denseTime) := by
        exact TopologicalSpace.denseRange_denseSeq NNReal
      rcases hdense.exists_seq_strictMono_tendsto_of_lt h0a with
        ⟨u, _hu_mono, hu_mem, hu_tendsto⟩
      choose k hk using fun n ↦ (hu_mem n).2
      have hprobe (n : ℕ) : leftProbeCondition lam q (k n) w := by
        apply (leftProbeCondition_iff_of_excursion w lam hab hq (k n)).2
        rw [hk]
        exact (hu_mem n).1.2.le
      have hseq_le : (⨆ n : ℕ, (u n : ENNReal)) ≤
          ⨆ k : ℕ, if leftProbeCondition lam q k w then
            (denseTime k : ENNReal) else 0 := by
        apply iSup_le
        intro n
        apply le_iSup_of_le (k n)
        exact (by simpa only [hprobe n, if_true, hk n] using!
          (le_refl (u n : ENNReal)))
      have hseq_eq : (⨆ n : ℕ, (u n : ENNReal)) = (a : ENNReal) := by
        apply iSup_eq_of_forall_le_of_tendsto (F := atTop)
        · intro n
          exact_mod_cast (hu_mem n).1.2.le
        · exact ENNReal.tendsto_coe.mpr hu_tendsto
      rwa [hseq_eq] at hseq_le

private lemma excursionRight_eq_of_excursion
    (w : BrownianPath) (lam : ℝ) {a b q : NNReal}
    (hab : excursion w lam a b) (hq : q ∈ Set.Ioo a b) :
    excursionRight lam q w = (b : ENNReal) := by
  classical
  unfold excursionRight
  apply le_antisymm
  · have hdense : Dense (Set.range denseTime) := by
      exact TopologicalSpace.denseRange_denseSeq NNReal
    rcases hdense.exists_seq_strictAnti_tendsto b with
      ⟨u, _hu_anti, hu_mem, hu_tendsto⟩
    choose k hk using fun n ↦ (hu_mem n).2
    have hprobe (n : ℕ) : rightProbeCondition lam q (k n) w := by
      apply (rightProbeCondition_iff_of_excursion w lam hab hq (k n)).2
      rw [hk]
      exact (hu_mem n).1.le
    have hfull_le : (⨅ k : ℕ, if rightProbeCondition lam q k w then
          (denseTime k : ENNReal) else ⊤) ≤
        ⨅ n : ℕ, (u n : ENNReal) := by
      apply le_iInf
      intro n
      apply iInf_le_of_le (k n)
      exact (by simpa only [hprobe n, if_true, hk n] using!
        (le_refl (u n : ENNReal)))
    have hseq_eq : (⨅ n : ℕ, (u n : ENNReal)) = (b : ENNReal) := by
      apply iInf_eq_of_forall_le_of_tendsto (F := atTop)
      · intro n
        exact_mod_cast (hu_mem n).1.le
      · exact ENNReal.tendsto_coe.mpr hu_tendsto
    rwa [hseq_eq] at hfull_le
  · apply le_iInf
    intro k
    split_ifs with hk
    · exact_mod_cast (rightProbeCondition_iff_of_excursion w lam hab hq k).mp hk
    · exact le_top

private def certifiedProbe (lam : ℝ) (n : ℕ) (w : BrownianPath) : Prop :=
  excursionLeft lam (denseTime n) w < (denseTime n : ENNReal) ∧
    (denseTime n : ENNReal) < excursionRight lam (denseTime n) w ∧
    excursionRight lam (denseTime n) w < ⊤ ∧
    reflected w lam (excursionLeft lam (denseTime n) w).toNNReal = 0 ∧
    reflected w lam (excursionRight lam (denseTime n) w).toNNReal = 0 ∧
    ∀ k l : ℕ,
      excursionLeft lam (denseTime n) w < (denseTime k : ENNReal) →
      denseTime k < denseTime l →
      (denseTime l : ENNReal) < excursionRight lam (denseTime n) w →
      0 < reflectedIntervalInf lam (denseTime k) (denseTime l) w

private lemma measurable_reflected_excursionLeft (lam : ℝ) (q : NNReal) :
    Measurable (fun w : BrownianPath ↦
      reflected w lam (excursionLeft lam q w).toNNReal) := by
  exact (continuous_reflected_joint lam).measurable.comp
    (measurable_id.prodMk (measurable_excursionLeft lam q).ennreal_toNNReal)

private lemma measurable_reflected_excursionRight (lam : ℝ) (q : NNReal) :
    Measurable (fun w : BrownianPath ↦
      reflected w lam (excursionRight lam q w).toNNReal) := by
  exact (continuous_reflected_joint lam).measurable.comp
    (measurable_id.prodMk (measurable_excursionRight lam q).ennreal_toNNReal)

private lemma measurableSet_certifiedProbe (lam : ℝ) (n : ℕ) :
    MeasurableSet {w : BrownianPath | certifiedProbe lam n w} := by
  have hleft : MeasurableSet {w : BrownianPath |
      excursionLeft lam (denseTime n) w < (denseTime n : ENNReal)} :=
    measurableSet_lt (measurable_excursionLeft lam (denseTime n)) measurable_const
  have hright : MeasurableSet {w : BrownianPath |
      (denseTime n : ENNReal) < excursionRight lam (denseTime n) w} :=
    measurableSet_lt measurable_const (measurable_excursionRight lam (denseTime n))
  have hfinite : MeasurableSet {w : BrownianPath |
      excursionRight lam (denseTime n) w < ⊤} :=
    measurableSet_lt (measurable_excursionRight lam (denseTime n)) measurable_const
  have hleftZero : MeasurableSet {w : BrownianPath |
      reflected w lam (excursionLeft lam (denseTime n) w).toNNReal = 0} :=
    (measurable_reflected_excursionLeft lam (denseTime n))
      (measurableSet_singleton 0)
  have hrightZero : MeasurableSet {w : BrownianPath |
      reflected w lam (excursionRight lam (denseTime n) w).toNNReal = 0} :=
    (measurable_reflected_excursionRight lam (denseTime n))
      (measurableSet_singleton 0)
  have hintervals : MeasurableSet {w : BrownianPath |
      ∀ k l : ℕ,
        excursionLeft lam (denseTime n) w < (denseTime k : ENNReal) →
        denseTime k < denseTime l →
        (denseTime l : ENNReal) < excursionRight lam (denseTime n) w →
        0 < reflectedIntervalInf lam (denseTime k) (denseTime l) w} := by
    rw [show {w : BrownianPath |
        ∀ k l : ℕ,
          excursionLeft lam (denseTime n) w < (denseTime k : ENNReal) →
          denseTime k < denseTime l →
          (denseTime l : ENNReal) < excursionRight lam (denseTime n) w →
          0 < reflectedIntervalInf lam (denseTime k) (denseTime l) w} =
        ⋂ k : ℕ, ⋂ l : ℕ, {w : BrownianPath |
          excursionLeft lam (denseTime n) w < (denseTime k : ENNReal) →
          denseTime k < denseTime l →
          (denseTime l : ENNReal) < excursionRight lam (denseTime n) w →
          0 < reflectedIntervalInf lam (denseTime k) (denseTime l) w} by
      ext w
      simp]
    apply MeasurableSet.iInter
    intro k
    apply MeasurableSet.iInter
    intro l
    by_cases hkl : denseTime k < denseTime l
    · have hante : MeasurableSet {w : BrownianPath |
          excursionLeft lam (denseTime n) w < (denseTime k : ENNReal) ∧
            (denseTime l : ENNReal) < excursionRight lam (denseTime n) w} :=
        (measurableSet_lt (measurable_excursionLeft lam (denseTime n))
          measurable_const).inter
        (measurableSet_lt measurable_const
          (measurable_excursionRight lam (denseTime n)))
      have hpos : MeasurableSet {w : BrownianPath |
          0 < reflectedIntervalInf lam (denseTime k) (denseTime l) w} :=
        measurableSet_lt measurable_const
          (measurable_reflectedIntervalInf lam (denseTime k) (denseTime l))
      rw [show {w : BrownianPath |
          excursionLeft lam (denseTime n) w < (denseTime k : ENNReal) →
          denseTime k < denseTime l →
          (denseTime l : ENNReal) < excursionRight lam (denseTime n) w →
          0 < reflectedIntervalInf lam (denseTime k) (denseTime l) w} =
          {w : BrownianPath |
            excursionLeft lam (denseTime n) w < (denseTime k : ENNReal) ∧
              (denseTime l : ENNReal) < excursionRight lam (denseTime n) w}ᶜ ∪
          {w : BrownianPath |
            0 < reflectedIntervalInf lam (denseTime k) (denseTime l) w} by
        ext w
        simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_compl_iff]
        tauto]
      exact hante.compl.union hpos
    · rw [show {w : BrownianPath |
          excursionLeft lam (denseTime n) w < (denseTime k : ENNReal) →
          denseTime k < denseTime l →
          (denseTime l : ENNReal) < excursionRight lam (denseTime n) w →
          0 < reflectedIntervalInf lam (denseTime k) (denseTime l) w} = Set.univ by
        ext w
        simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
        intro _hleft hbad
        exact (hkl hbad).elim]
      exact MeasurableSet.univ
  exact hleft.inter (hright.inter (hfinite.inter
    (hleftZero.inter (hrightZero.inter hintervals))))

private lemma certifiedProbe_of_excursion
    (w : BrownianPath) (lam : ℝ) {a b : NNReal} (hab : excursion w lam a b)
    {n : ℕ} (hn : denseTime n ∈ Set.Ioo a b) :
    certifiedProbe lam n w := by
  have hleft := excursionLeft_eq_of_excursion w lam hab hn
  have hright := excursionRight_eq_of_excursion w lam hab hn
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hleft]
    exact_mod_cast hn.1
  · rw [hright]
    exact_mod_cast hn.2
  · rw [hright]
    exact ENNReal.coe_lt_top
  · simpa only [hleft, ENNReal.toNNReal_coe] using! hab.2.1
  · simpa only [hright, ENNReal.toNNReal_coe] using! hab.2.2.1
  · intro k l hkleft hkl hlright
    have hak : a < denseTime k := by
      rw [hleft] at hkleft
      exact_mod_cast hkleft
    have hlb : denseTime l < b := by
      rw [hright] at hlright
      exact_mod_cast hlright
    have hnonneg := reflectedIntervalInf_nonneg w lam (denseTime k) (denseTime l)
    apply lt_of_le_of_ne hnonneg
    intro hzero
    rcases (reflectedIntervalInf_eq_zero_iff w lam (denseTime k) (denseTime l)).mp
        hzero.symm with ⟨x, hxzero⟩
    have htime : intervalTime (denseTime k) (denseTime l) x ∈
        Set.Icc (denseTime k) (denseTime l) := by
      rw [← intervalTime_image hkl.le]
      exact ⟨x, Set.mem_univ _, rfl⟩
    have hinside : intervalTime (denseTime k) (denseTime l) x ∈ Set.Ioo a b :=
      ⟨hak.trans_le htime.1, htime.2.trans_lt hlb⟩
    exact (ne_of_gt (hab.2.2.2 _ hinside)) hxzero

private def probeExcursionPair (lam : ℝ) (n : ℕ)
    (w : BrownianPath) : NNReal × NNReal :=
  ((excursionLeft lam (denseTime n) w).toNNReal,
    (excursionRight lam (denseTime n) w).toNNReal)

private lemma probeExcursionPair_excursion_of_certified
    (w : BrownianPath) (lam : ℝ) {n : ℕ} (hn : certifiedProbe lam n w) :
    excursion w lam (probeExcursionPair lam n w).1
      (probeExcursionPair lam n w).2 := by
  let L := excursionLeft lam (denseTime n) w
  let R := excursionRight lam (denseTime n) w
  have hLtop : L ≠ ⊤ := ne_top_of_lt (hn.1.trans hn.2.1 |>.trans hn.2.2.1)
  have hRtop : R ≠ ⊤ := ne_top_of_lt hn.2.2.1
  have hLcoe : ((L.toNNReal : NNReal) : ENNReal) = L := ENNReal.coe_toNNReal hLtop
  have hRcoe : ((R.toNNReal : NNReal) : ENNReal) = R := ENNReal.coe_toNNReal hRtop
  have hLq : L.toNNReal < denseTime n := by
    apply ENNReal.coe_lt_coe.mp
    rw [hLcoe]
    exact hn.1
  have hqR : denseTime n < R.toNNReal := by
    apply ENNReal.coe_lt_coe.mp
    rw [hRcoe]
    exact hn.2.1
  have hLR : L.toNNReal < R.toNNReal := hLq.trans hqR
  refine ⟨hLR, ?_, ?_, ?_⟩
  · exact hn.2.2.2.1
  · exact hn.2.2.2.2.1
  · intro t ht
    have hdense : Dense (Set.range denseTime) := by
      exact TopologicalSpace.denseRange_denseSeq NNReal
    rcases hdense.exists_between ht.1 with ⟨r, ⟨k, hk⟩, hr⟩
    rcases hdense.exists_between ht.2 with ⟨s, ⟨l, hl⟩, hs⟩
    have hLk : L < (denseTime k : ENNReal) := by
      rw [hk, ← hLcoe]
      exact_mod_cast hr.1
    have hkl : denseTime k < denseTime l := by
      rw [hk, hl]
      exact hr.2.trans hs.1
    have hlR : (denseTime l : ENNReal) < R := by
      rw [hl, ← hRcoe]
      exact_mod_cast hs.2
    have hinfpos := hn.2.2.2.2.2 k l hLk hkl hlR
    have htime : t ∈ Set.Icc (denseTime k) (denseTime l) := by
      rw [hk, hl]
      exact ⟨hr.2.le, hs.1.le⟩
    rw [← intervalTime_image hkl.le] at htime
    rcases htime with ⟨x, _hx, hxt⟩
    have hnotzero : reflected w lam t ≠ 0 := by
      intro htzero
      have hz : reflectedIntervalInf lam (denseTime k) (denseTime l) w = 0 :=
        (reflectedIntervalInf_eq_zero_iff w lam (denseTime k) (denseTime l)).2
          ⟨x, by rwa [hxt]⟩
      exact (ne_of_gt hinfpos) hz
    exact lt_of_le_of_ne (reflected_nonneg w lam t) (Ne.symm hnotzero)

private def retainedProbe (lam : ℝ) (n : ℕ) (w : BrownianPath) : Prop :=
  certifiedProbe lam n w ∧
    ∀ m < n, ¬(excursionLeft lam (denseTime n) w < (denseTime m : ENNReal) ∧
      (denseTime m : ENNReal) < excursionRight lam (denseTime n) w)

private lemma measurableSet_retainedProbe (lam : ℝ) (n : ℕ) :
    MeasurableSet {w : BrownianPath | retainedProbe lam n w} := by
  have hprevious : MeasurableSet {w : BrownianPath |
      ∀ m < n, ¬(excursionLeft lam (denseTime n) w < (denseTime m : ENNReal) ∧
        (denseTime m : ENNReal) < excursionRight lam (denseTime n) w)} := by
    have hfin : MeasurableSet {w : BrownianPath |
        ∀ m : Fin n, ¬(excursionLeft lam (denseTime n) w < (denseTime m.val : ENNReal) ∧
          (denseTime m.val : ENNReal) < excursionRight lam (denseTime n) w)} := by
      rw [show {w : BrownianPath |
          ∀ m : Fin n, ¬(excursionLeft lam (denseTime n) w < (denseTime m.val : ENNReal) ∧
            (denseTime m.val : ENNReal) < excursionRight lam (denseTime n) w)} =
          ⋂ m : Fin n, {w : BrownianPath |
            ¬(excursionLeft lam (denseTime n) w < (denseTime m.val : ENNReal) ∧
              (denseTime m.val : ENNReal) < excursionRight lam (denseTime n) w)} by
        ext w
        simp]
      apply MeasurableSet.iInter
      intro m
      exact ((measurableSet_lt (measurable_excursionLeft lam (denseTime n))
          measurable_const).inter
        (measurableSet_lt measurable_const
          (measurable_excursionRight lam (denseTime n)))).compl
    rw [show {w : BrownianPath |
        ∀ m < n, ¬(excursionLeft lam (denseTime n) w < (denseTime m : ENNReal) ∧
          (denseTime m : ENNReal) < excursionRight lam (denseTime n) w)} =
        {w : BrownianPath |
          ∀ m : Fin n, ¬(excursionLeft lam (denseTime n) w < (denseTime m.val : ENNReal) ∧
            (denseTime m.val : ENNReal) < excursionRight lam (denseTime n) w)} by
      ext w
      constructor
      · intro h m
        exact h m.val m.isLt
      · intro h m hm
        exact h ⟨m, hm⟩]
    exact hfin
  exact (measurableSet_certifiedProbe lam n).inter hprevious

private def retainedLength (lam : ℝ) (n : ℕ) (w : BrownianPath) : ENNReal := by
  classical
  exact if retainedProbe lam n w then
    excursionRight lam (denseTime n) w - excursionLeft lam (denseTime n) w else 0

private lemma measurable_retainedLength (lam : ℝ) (n : ℕ) :
    Measurable (retainedLength lam n) := by
  classical
  unfold retainedLength
  exact Measurable.ite (measurableSet_retainedProbe lam n)
    ((measurable_excursionRight lam (denseTime n)).sub
      (measurable_excursionLeft lam (denseTime n)))
    measurable_const

private lemma retainedLength_eq_excursionLength
    (w : BrownianPath) (lam : ℝ) {n : ℕ} (hn : retainedProbe lam n w) :
    retainedLength lam n w = ENNReal.ofReal
      (((probeExcursionPair lam n w).2 : ℝ) -
        ((probeExcursionPair lam n w).1 : ℝ)) := by
  classical
  let L := excursionLeft lam (denseTime n) w
  let R := excursionRight lam (denseTime n) w
  have hLtop : L ≠ ⊤ := ne_top_of_lt ((hn.1.1.trans hn.1.2.1).trans hn.1.2.2.1)
  have hRtop : R ≠ ⊤ := ne_top_of_lt hn.1.2.2.1
  have hLcoe : ((L.toNNReal : NNReal) : ENNReal) = L := ENNReal.coe_toNNReal hLtop
  have hRcoe : ((R.toNNReal : NNReal) : ENNReal) = R := ENNReal.coe_toNNReal hRtop
  have hLR : L.toNNReal ≤ R.toNNReal := by
    apply ENNReal.coe_le_coe.mp
    rw [hLcoe, hRcoe]
    exact (hn.1.1.trans hn.1.2.1).le
  unfold retainedLength
  rw [if_pos hn]
  change R - L = ENNReal.ofReal ((R.toNNReal : ℝ) - (L.toNNReal : ℝ))
  calc
    R - L = (R.toNNReal : ENNReal) - (L.toNNReal : ENNReal) :=
      congrArg₂ (· - ·) hRcoe.symm hLcoe.symm
    _ = (R.toNNReal - L.toNNReal : NNReal) := ENNReal.coe_sub.symm
    _ = ENNReal.ofReal ((R.toNNReal : ℝ) - (L.toNNReal : ℝ)) := by
      rw [← NNReal.coe_sub hLR, ENNReal.ofReal_coe_nnreal]

private lemma denseTime_mem_probeExcursionPair_of_certified
    (w : BrownianPath) (lam : ℝ) {n : ℕ} (hn : certifiedProbe lam n w) :
    denseTime n ∈ Set.Ioo (probeExcursionPair lam n w).1
      (probeExcursionPair lam n w).2 := by
  let L := excursionLeft lam (denseTime n) w
  let R := excursionRight lam (denseTime n) w
  have hLtop : L ≠ ⊤ := ne_top_of_lt ((hn.1.trans hn.2.1).trans hn.2.2.1)
  have hRtop : R ≠ ⊤ := ne_top_of_lt hn.2.2.1
  have hLcoe : ((L.toNNReal : NNReal) : ENNReal) = L := ENNReal.coe_toNNReal hLtop
  have hRcoe : ((R.toNNReal : NNReal) : ENNReal) = R := ENNReal.coe_toNNReal hRtop
  constructor
  · change L.toNNReal < denseTime n
    apply ENNReal.coe_lt_coe.mp
    rw [hLcoe]
    exact hn.1
  · change denseTime n < R.toNNReal
    apply ENNReal.coe_lt_coe.mp
    rw [hRcoe]
    exact hn.2.1

private lemma exists_retainedProbe_of_excursion
    (w : BrownianPath) (lam : ℝ) {a b : NNReal} (hab : excursion w lam a b) :
    ∃ n : ℕ, retainedProbe lam n w ∧ probeExcursionPair lam n w = (a, b) := by
  classical
  have hdense : Dense (Set.range denseTime) := by
    exact TopologicalSpace.denseRange_denseSeq NNReal
  rcases hdense.exists_between hab.1 with ⟨q, ⟨n, hnq⟩, hq⟩
  have hex : ∃ n : ℕ, denseTime n ∈ Set.Ioo a b := ⟨n, by rwa [hnq]⟩
  let n0 := Nat.find hex
  have hn0 : denseTime n0 ∈ Set.Ioo a b := Nat.find_spec hex
  have hleft := excursionLeft_eq_of_excursion w lam hab hn0
  have hright := excursionRight_eq_of_excursion w lam hab hn0
  have hretained : retainedProbe lam n0 w := by
    refine ⟨certifiedProbe_of_excursion w lam hab hn0, ?_⟩
    intro m hm hbetween
    apply Nat.find_min hex hm
    constructor
    · rw [hleft] at hbetween
      exact_mod_cast hbetween.1
    · rw [hright] at hbetween
      exact_mod_cast hbetween.2
  refine ⟨n0, hretained, ?_⟩
  apply Prod.ext
  · simp only [probeExcursionPair, hleft, ENNReal.toNNReal_coe]
  · simp only [probeExcursionPair, hright, ENNReal.toNNReal_coe]

private lemma retainedProbe_pair_injective
    (w : BrownianPath) (lam : ℝ) {n m : ℕ}
    (hn : retainedProbe lam n w) (hm : retainedProbe lam m w)
    (hpairs : probeExcursionPair lam n w = probeExcursionPair lam m w) :
    n = m := by
  rcases lt_trichotomy n m with hnm | hnm | hmn
  · exfalso
    apply hm.2 n hnm
    have hninside := denseTime_mem_probeExcursionPair_of_certified w lam hn.1
    rw [hpairs] at hninside
    let L := excursionLeft lam (denseTime m) w
    let R := excursionRight lam (denseTime m) w
    have hLtop : L ≠ ⊤ := ne_top_of_lt ((hm.1.1.trans hm.1.2.1).trans hm.1.2.2.1)
    have hRtop : R ≠ ⊤ := ne_top_of_lt hm.1.2.2.1
    have hLcoe : ((L.toNNReal : NNReal) : ENNReal) = L := ENNReal.coe_toNNReal hLtop
    have hRcoe : ((R.toNNReal : NNReal) : ENNReal) = R := ENNReal.coe_toNNReal hRtop
    constructor
    · change L < (denseTime n : ENNReal)
      rw [← hLcoe]
      exact_mod_cast hninside.1
    · change (denseTime n : ENNReal) < R
      rw [← hRcoe]
      exact_mod_cast hninside.2
  · exact hnm
  · exfalso
    apply hn.2 m hmn
    have hminside := denseTime_mem_probeExcursionPair_of_certified w lam hm.1
    rw [← hpairs] at hminside
    let L := excursionLeft lam (denseTime n) w
    let R := excursionRight lam (denseTime n) w
    have hLtop : L ≠ ⊤ := ne_top_of_lt ((hn.1.1.trans hn.1.2.1).trans hn.1.2.2.1)
    have hRtop : R ≠ ⊤ := ne_top_of_lt hn.1.2.2.1
    have hLcoe : ((L.toNNReal : NNReal) : ENNReal) = L := ENNReal.coe_toNNReal hLtop
    have hRcoe : ((R.toNNReal : NNReal) : ENNReal) = R := ENNReal.coe_toNNReal hRtop
    constructor
    · change L < (denseTime m : ENNReal)
      rw [← hLcoe]
      exact_mod_cast hminside.1
    · change (denseTime m : ENNReal) < R
      rw [← hRcoe]
      exact_mod_cast hminside.2

private def enumeratedFamilyMinimum (lam : ℝ) (i : ℕ)
    (f : Fin i → ℕ) (w : BrownianPath) : ENNReal := by
  classical
  exact if Function.Injective f then ⨅ j : Fin i, retainedLength lam (f j) w else 0

private lemma measurable_enumeratedFamilyMinimum
    (lam : ℝ) (i : ℕ) (f : Fin i → ℕ) :
    Measurable (enumeratedFamilyMinimum lam i f) := by
  classical
  by_cases hf : Function.Injective f
  · change Measurable (fun w : BrownianPath ↦
      if Function.Injective f then
        ⨅ j : Fin i, retainedLength lam (f j) w else 0)
    simpa only [hf, if_true] using!
      (Measurable.iInf fun j : Fin i ↦ measurable_retainedLength lam (f j))
  · change Measurable (fun w : BrownianPath ↦
      if Function.Injective f then
        ⨅ j : Fin i, retainedLength lam (f j) w else 0)
    simpa only [hf, if_false] using!
      (measurable_const : Measurable (fun _ : BrownianPath ↦ (0 : ENNReal)))

private def enumeratedExcursionRank (lam : ℝ) (i : ℕ)
    (w : BrownianPath) : ENNReal :=
  if i = 0 then 0 else
    ⨆ f : Fin i → ℕ, enumeratedFamilyMinimum lam i f w

theorem measurable_enumeratedExcursionRank (lam : ℝ) (i : ℕ) :
    Measurable (enumeratedExcursionRank lam i) := by
  by_cases hi : i = 0
  · change Measurable (fun w : BrownianPath ↦
      if i = 0 then 0 else
        ⨆ f : Fin i → ℕ, enumeratedFamilyMinimum lam i f w)
    simpa only [hi, if_true] using!
      (measurable_const : Measurable (fun _ : BrownianPath ↦ (0 : ENNReal)))
  · change Measurable (fun w : BrownianPath ↦
      if i = 0 then 0 else
        ⨆ f : Fin i → ℕ, enumeratedFamilyMinimum lam i f w)
    simpa only [hi, if_false] using!
      (Measurable.iSup fun f : Fin i → ℕ ↦
        measurable_enumeratedFamilyMinimum lam i f)

theorem enumeratedExcursionRank_eq_excursionRankExtended
    (w : BrownianPath) (lam : ℝ) (i : ℕ) :
    enumeratedExcursionRank lam i w = excursionRankExtended w lam i := by
  classical
  by_cases hi : i = 0
  · simp only [enumeratedExcursionRank, excursionRankExtended, hi, if_true]
  · rw [show enumeratedExcursionRank lam i w =
        ⨆ f : Fin i → ℕ, enumeratedFamilyMinimum lam i f w by
      change (if i = 0 then 0 else
        ⨆ f : Fin i → ℕ, enumeratedFamilyMinimum lam i f w) = _
      rw [if_neg hi],
      show excursionRankExtended w lam i =
        sSup {r : ENNReal |
          ∃ e : Fin i → NNReal × NNReal, Function.Injective e ∧
            ∀ j, excursion w lam (e j).1 (e j).2 ∧
              r ≤ ENNReal.ofReal (((e j).2 : ℝ) - ((e j).1 : ℝ))} by
      rw [excursionRankExtended, if_neg hi]]
    apply le_antisymm
    · apply iSup_le
      intro f
      by_cases hf : Function.Injective f
      · change (if Function.Injective f then
            ⨅ j : Fin i, retainedLength lam (f j) w else 0) ≤ _
        rw [if_pos hf]
        by_cases hall : ∀ j : Fin i, retainedProbe lam (f j) w
        · let e : Fin i → NNReal × NNReal :=
            fun j ↦ probeExcursionPair lam (f j) w
          have he_injective : Function.Injective e := by
            intro j k hjk
            apply hf
            exact retainedProbe_pair_injective w lam (hall j) (hall k) hjk
          apply le_sSup
          refine ⟨e, he_injective, ?_⟩
          intro j
          refine ⟨probeExcursionPair_excursion_of_certified w lam (hall j).1, ?_⟩
          calc
            (⨅ k : Fin i, retainedLength lam (f k) w)
                ≤ retainedLength lam (f j) w := iInf_le _ j
            _ = ENNReal.ofReal (((e j).2 : ℝ) - ((e j).1 : ℝ)) :=
              retainedLength_eq_excursionLength w lam (hall j)
        · push_neg at hall
          rcases hall with ⟨j, hj⟩
          calc
            (⨅ k : Fin i, retainedLength lam (f k) w)
                ≤ retainedLength lam (f j) w := iInf_le _ j
            _ = 0 := by
              unfold retainedLength
              rw [if_neg hj]
            _ ≤ sSup {r : ENNReal |
                ∃ e : Fin i → NNReal × NNReal, Function.Injective e ∧
                  ∀ j, excursion w lam (e j).1 (e j).2 ∧
                    r ≤ ENNReal.ofReal (((e j).2 : ℝ) - ((e j).1 : ℝ))} := bot_le
      · change (if Function.Injective f then
            ⨅ j : Fin i, retainedLength lam (f j) w else 0) ≤ _
        rw [if_neg hf]
        exact bot_le
    · apply sSup_le
      intro r hr
      rcases hr with ⟨e, he_injective, he⟩
      choose f hf_retained hf_pair using fun j ↦
        exists_retainedProbe_of_excursion w lam (he j).1
      have hf_injective : Function.Injective f := by
        intro j k hjk
        apply he_injective
        calc
          e j = probeExcursionPair lam (f j) w := (hf_pair j).symm
          _ = probeExcursionPair lam (f k) w := by rw [hjk]
          _ = e k := hf_pair k
      apply le_trans _ (le_iSup (fun f : Fin i → ℕ ↦
        enumeratedFamilyMinimum lam i f w) f)
      change r ≤ if Function.Injective f then
        ⨅ j : Fin i, retainedLength lam (f j) w else 0
      rw [if_pos hf_injective]
      apply le_iInf
      intro j
      rw [retainedLength_eq_excursionLength w lam (hf_retained j), hf_pair j]
      exact (he j).2

theorem measurable_excursionRankExtended (lam : ℝ) (i : ℕ) :
    Measurable (fun w : BrownianPath ↦ excursionRankExtended w lam i) := by
  rw [show (fun w : BrownianPath ↦ excursionRankExtended w lam i) =
      enumeratedExcursionRank lam i by
    funext w
    exact (enumeratedExcursionRank_eq_excursionRankExtended w lam i).symm]
  exact measurable_enumeratedExcursionRank lam i

/-!
The final rank bounds are deterministic consequences of the two cardinality
clauses in `GoodExcursionPath`.  Keeping this argument independent of the
probabilistic construction is useful twice: the regularity proof only has to
produce `GoodExcursionPath`, and downstream consumers obtain bounds on the
literal public `sSup`, rather than on an auxiliary ordered list.
-/

theorem excursionRankExtended_pos_lt_top_of_good
    (w : BrownianPath) (lam : ℝ) (hw : GoodExcursionPath w lam)
    (i : ℕ) (hi : 0 < i) :
    0 < excursionRankExtended w lam i ∧
      excursionRankExtended w lam i < ⊤ := by
  classical
  rcases hw with ⟨_hescape, _hzero, _hlevels, _hdescent,
    hfiniteLong, hinfinite⟩
  let S : Set (NNReal × NNReal) :=
    {e | excursion w lam e.1 e.2}
  have hS : S.Infinite := by
    simpa only [S] using! hinfinite
  let emb : ℕ ↪ S := Set.Infinite.natEmbedding S hS
  let e : Fin i → NNReal × NNReal := fun j ↦ (emb j.val).1
  have he_injective : Function.Injective e := by
    intro j k hjk
    apply Fin.ext
    apply emb.injective
    exact Subtype.ext hjk
  have he_excursion (j : Fin i) :
      excursion w lam (e j).1 (e j).2 := by
    exact (emb j.val).property
  let ell : Fin i → NNReal := fun j ↦ (e j).2 - (e j).1
  have hell_pos (j : Fin i) : 0 < ell j := by
    exact tsub_pos_iff_lt.mpr (he_excursion j).1
  letI : Nonempty (Fin i) := Fin.pos_iff_nonempty.mp hi
  let lengths : Finset NNReal := Finset.univ.image ell
  have hlengths : lengths.Nonempty := by
    exact Finset.image_nonempty.mpr Finset.univ_nonempty
  let delta : NNReal := lengths.min' hlengths
  have hdelta_pos : 0 < delta := by
    have hmem : delta ∈ lengths := Finset.min'_mem lengths hlengths
    rcases Finset.mem_image.mp hmem with ⟨j, _hj, hj⟩
    rw [← hj]
    exact hell_pos j
  have hdelta_le (j : Fin i) : delta ≤ ell j := by
    apply Finset.min'_le lengths
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩
  let feasible : Set ENNReal := {r : ENNReal |
    ∃ f : Fin i → NNReal × NNReal, Function.Injective f ∧
      ∀ j, excursion w lam (f j).1 (f j).2 ∧
        r ≤ ENNReal.ofReal (((f j).2 : ℝ) - ((f j).1 : ℝ))}
  have hdelta_mem : (delta : ENNReal) ∈ feasible := by
    refine ⟨e, he_injective, ?_⟩
    intro j
    refine ⟨he_excursion j, ?_⟩
    rw [← NNReal.coe_sub (le_of_lt (he_excursion j).1),
      ENNReal.ofReal_coe_nnreal]
    exact_mod_cast hdelta_le j
  have hi_ne : i ≠ 0 := Nat.ne_of_gt hi
  have hrank_pos : 0 < excursionRankExtended w lam i := by
    rw [excursionRankExtended, if_neg hi_ne]
    change 0 < sSup feasible
    exact lt_of_lt_of_le (ENNReal.coe_pos.mpr hdelta_pos)
      (le_sSup hdelta_mem)

  let longSet : Set (NNReal × NNReal) :=
    {x | excursion w lam x.1 x.2 ∧
      1 ≤ (x.2 : ℝ) - (x.1 : ℝ)}
  have hlong_finite : longSet.Finite := by
    simpa only [longSet] using! hfiniteLong 1 (by norm_num)
  let longFinset : Finset (NNReal × NNReal) := hlong_finite.toFinset
  let M : NNReal :=
    1 + ∑ x ∈ longFinset, (x.2 - x.1)
  have hlength_le_M {a b : NNReal} (hab : excursion w lam a b) :
      b - a ≤ M := by
    by_cases hshort : b - a < 1
    · exact hshort.le.trans (by simp [M])
    · have hreal_long : 1 ≤ (b : ℝ) - (a : ℝ) := by
        rw [← NNReal.coe_sub (le_of_lt hab.1)]
        exact_mod_cast le_of_not_gt hshort
      have hpair_mem : (a, b) ∈ longSet := ⟨hab, hreal_long⟩
      have hpair_finset : (a, b) ∈ longFinset := by
        exact (Set.Finite.mem_toFinset hlong_finite).2 hpair_mem
      have hsum : b - a ≤ ∑ x ∈ longFinset, (x.2 - x.1) := by
        exact Finset.single_le_sum (s := longFinset)
          (f := fun x : NNReal × NNReal ↦ x.2 - x.1)
          (fun x _hx ↦ zero_le) hpair_finset
      exact hsum.trans (by
        dsimp only [M]
        exact le_add_of_nonneg_left zero_le_one)
  have hrank_le : excursionRankExtended w lam i ≤ (M : ENNReal) := by
    rw [excursionRankExtended, if_neg hi_ne]
    change sSup feasible ≤ (M : ENNReal)
    apply sSup_le
    intro r hr
    rcases hr with ⟨f, _hf_injective, hf⟩
    let j0 : Fin i := ⟨0, hi⟩
    calc
      r ≤ ENNReal.ofReal (((f j0).2 : ℝ) - ((f j0).1 : ℝ)) :=
        (hf j0).2
      _ = ((f j0).2 - (f j0).1 : NNReal) := by
        rw [← NNReal.coe_sub (le_of_lt (hf j0).1.1),
          ENNReal.ofReal_coe_nnreal]
      _ ≤ (M : ENNReal) := by
        exact_mod_cast hlength_le_M (hf j0).1
  exact ⟨hrank_pos, hrank_le.trans_lt ENNReal.coe_lt_top⟩

end

end Erdos745.WrapUp.Proofs.Internal.W13_BROWNIAN_Ranks


namespace Erdos745.WrapUp.Proofs.Internal.W13_BROWNIAN_Regularity

noncomputable section
open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal Topology

open W13_BROWNIAN_Law

local instance : MeasurableSpace BrownianPath := borel BrownianPath
local instance : BorelSpace BrownianPath := ⟨rfl⟩

/-! ### Natural Brownian filtration

Mathlib's natural filtration is the increasing supremum of the evaluation
sigma algebras.  This is definitionally the minimal filtration making every
past coordinate measurable and stays below the ambient path Borel space. -/

private def unitNNReal (x : unitInterval) : NNReal :=
  NNReal.mk ((x : ℝ)) (x.property.1)

private def unitFraction (t : NNReal) : unitInterval :=
  ⟨(t : ℝ) - (⌊(t : ℝ)⌋₊ : ℝ), by
    constructor
    · exact sub_nonneg.mpr (Nat.floor_le t.property)
    · have ht := Nat.lt_floor_add_one (t : ℝ)
      linarith⟩

private lemma unitTime_floor_unitFraction (t : NNReal) :
    unitTime ⌊(t : ℝ)⌋₊ (unitFraction t) = t := by
  ext
  simp [unitTime, unitFraction]

/-- The maximum drift on the `j`th unit interval.  This countable family is
the measurable carrier for continuous-time escape. -/
def driftUnitBlockSup (lam : ℝ) (j : ℕ) (w : BrownianPath) : ℝ :=
  sSup ((fun x : unitInterval ↦ drift w lam (unitTime j x)) '' Set.univ)

private lemma compact_driftUnitBlock_image (w : BrownianPath) (lam : ℝ) (j : ℕ) :
    IsCompact ((fun x : unitInterval ↦ drift w lam (unitTime j x)) '' Set.univ) := by
  apply isCompact_univ.image
  unfold drift unitTime
  fun_prop

theorem continuous_driftUnitBlockSup (lam : ℝ) (j : ℕ) :
    Continuous (driftUnitBlockSup lam j) := by
  unfold driftUnitBlockSup
  apply isCompact_univ.continuous_sSup
  unfold drift unitTime
  fun_prop

def UnitBlockEscape (w : BrownianPath) (lam : ℝ) : Prop :=
  Tendsto (fun j : ℕ ↦ driftUnitBlockSup lam j w) atTop atBot

theorem measurableSet_unitBlockEscape (lam : ℝ) :
    MeasurableSet {w : BrownianPath | UnitBlockEscape w lam} := by
  unfold UnitBlockEscape
  exact measurableSet_tendsto atBot fun j ↦
    (continuous_driftUnitBlockSup lam j).measurable

private lemma drift_le_driftUnitBlockSup (w : BrownianPath) (lam : ℝ)
    (j : ℕ) (x : unitInterval) :
    drift w lam (unitTime j x) ≤ driftUnitBlockSup lam j w := by
  unfold driftUnitBlockSup
  apply le_csSup (compact_driftUnitBlock_image w lam j).bddAbove
  exact ⟨x, Set.mem_univ _, rfl⟩

theorem UnitBlockEscape.tendsto_drift {w : BrownianPath} {lam : ℝ}
    (h : UnitBlockEscape w lam) : Tendsto (drift w lam) atTop atBot := by
  rw [tendsto_atTop_atBot]
  intro b
  unfold UnitBlockEscape at h
  rw [tendsto_atTop_atBot] at h
  rcases h b with ⟨N, hN⟩
  refine ⟨(N + 1 : ℕ), ?_⟩
  intro t ht
  let j : ℕ := ⌊(t : ℝ)⌋₊
  let x : unitInterval := unitFraction t
  have hj : N ≤ j := by
    apply Nat.le_floor
    have ht' : ((N + 1 : ℕ) : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
    push_cast at ht'
    linarith
  calc
    drift w lam t = drift w lam (unitTime j x) := by
      rw [show unitTime j x = t by
        simpa [j, x] using! unitTime_floor_unitFraction t]
    _ ≤ driftUnitBlockSup lam j w := drift_le_driftUnitBlockSup w lam j x
    _ ≤ b := hN j hj

private lemma driftUnitBlockSup_le_of_path_growth
    {omega : GaussianSample} {lam A C : ℝ} {j : ℕ}
    (hpath : ∀ x : unitInterval,
      |globalPath omega (unitTime j x)| ≤
        A + (j : ℝ) ^ 2 / 16 + C * (j + 1)) :
    driftUnitBlockSup lam j (globalPath omega) ≤
      A + (j : ℝ) ^ 2 / 16 +
        (C + |lam|) * (j + 1) - (j : ℝ) ^ 2 / 2 := by
  unfold driftUnitBlockSup
  apply csSup_le
  · exact ⟨drift (globalPath omega) lam (unitTime j 0),
      ⟨0, Set.mem_univ _, rfl⟩⟩
  · rintro y ⟨x, _hx, rfl⟩
    have hx0 : 0 ≤ (x : ℝ) := x.property.1
    have hx1 : (x : ℝ) ≤ 1 := x.property.2
    have hj0 : 0 ≤ (j : ℝ) := by positivity
    have htime_lower : (j : ℝ) ≤ (unitTime j x : ℝ) := by
      simp only [unitTime, NNReal.coe_mk]
      linarith
    have htime_upper : (unitTime j x : ℝ) ≤ (j : ℝ) + 1 := by
      simp only [unitTime, NNReal.coe_mk]
      linarith
    have hw : globalPath omega (unitTime j x) ≤
        A + (j : ℝ) ^ 2 / 16 + C * (j + 1) :=
      (le_abs_self _).trans (hpath x)
    have hlam : lam * (unitTime j x : ℝ) ≤ |lam| * ((j : ℝ) + 1) := by
      calc
        lam * (unitTime j x : ℝ) ≤ |lam| * (unitTime j x : ℝ) := by
          gcongr
          exact le_abs_self lam
        _ ≤ |lam| * ((j : ℝ) + 1) := by gcongr
    have hsquare : (j : ℝ) ^ 2 ≤ (unitTime j x : ℝ) ^ 2 := by
      nlinarith
    unfold drift
    nlinarith

private lemma quadratic_escape (A C lam : ℝ) (hA : 0 ≤ A) (hC : 0 ≤ C) :
    Tendsto (fun j : ℕ ↦
      A + (j : ℝ) ^ 2 / 16 +
        (C + |lam|) * (j + 1) - (j : ℝ) ^ 2 / 2) atTop atBot := by
  rw [tendsto_atTop_atBot]
  intro b
  let K : ℝ := A + C + |lam| + |b| + 1
  have hKpos : 0 < K := by
    dsimp [K]
    positivity
  obtain ⟨N, hN⟩ := exists_nat_gt (128 * K)
  refine ⟨N, ?_⟩
  intro j hj
  have hNj : (N : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  have hKj : 128 * K < (j : ℝ) := hN.trans_le hNj
  have hjpos : 0 < (j : ℝ) := by nlinarith
  have hAle : A ≤ K := by dsimp [K]; linarith [abs_nonneg lam, abs_nonneg b]
  have hCle : C + |lam| ≤ K := by dsimp [K]; linarith [abs_nonneg b]
  have hble : -K ≤ b := by
    dsimp [K]
    have := neg_abs_le b
    linarith [hA, hC, abs_nonneg lam]
  have hlin : (C + |lam|) * ((j : ℝ) + 1) ≤
      ((j : ℝ) / 128) * ((j : ℝ) + 1) := by
    apply mul_le_mul_of_nonneg_right
    · nlinarith
    · nlinarith
  have hA' : A ≤ (j : ℝ) / 128 := by nlinarith
  have hK' : K ≤ (j : ℝ) ^ 2 / 128 := by
    have hjnat : 1 ≤ j := by
      apply Nat.one_le_iff_ne_zero.mpr
      intro hjzero
      subst j
      norm_num at hjpos
    have hjone : 1 ≤ (j : ℝ) := by exact_mod_cast hjnat
    nlinarith
  calc
    A + (j : ℝ) ^ 2 / 16 +
        (C + |lam|) * (j + 1) - (j : ℝ) ^ 2 / 2
        ≤ (j : ℝ) / 128 + (j : ℝ) ^ 2 / 16 +
          ((j : ℝ) / 128) * ((j : ℝ) + 1) - (j : ℝ) ^ 2 / 2 := by
            gcongr
    _ ≤ -(j : ℝ) ^ 2 / 128 := by
      have hjnat : 1 ≤ j := by
        apply Nat.one_le_iff_ne_zero.mpr
        intro hjzero
        subst j
        norm_num at hjpos
      have hjone : 1 ≤ (j : ℝ) := by exact_mod_cast hjnat
      nlinarith [sq_nonneg ((j : ℝ) - 1)]
    _ ≤ -K := by nlinarith
    _ ≤ b := hble

private theorem ae_globalPath_unitBlockEscape (lam : ℝ) :
    ∀ᵐ omega ∂gaussianSource, UnitBlockEscape (globalPath omega) lam := by
  filter_upwards [ae_globalPath_unitBlock_growth] with omega homega
  rcases homega with ⟨A, C, hA, hC, hgrowth⟩
  unfold UnitBlockEscape
  apply tendsto_atBot_mono'
  · filter_upwards [hgrowth] with j hj
    exact driftUnitBlockSup_le_of_path_growth hj
  · exact quadratic_escape A C lam hA hC

theorem brownianCandidate_ae_drift_escape (lam : ℝ) :
    ∀ᵐ w ∂brownianCandidate, Tendsto (drift w lam) atTop atBot := by
  have hblock : ∀ᵐ w ∂brownianCandidate, UnitBlockEscape w lam := by
    rw [brownianCandidate, ae_map_iff aeMeasurable_globalPath
      (measurableSet_unitBlockEscape lam)]
    exact ae_globalPath_unitBlockEscape lam
  filter_upwards [hblock] with w hw
  exact hw.tendsto_drift

/-- The first `GoodExcursionPath` clause, for every law satisfying the public
finite-dimensional Brownian specification. -/
theorem ae_drift_escape (mu : PathLaw) (hmu : BrownianLaw mu) (lam : ℝ) :
    ∀ᵐ w ∂mu, Tendsto (drift w lam) atTop atBot := by
  rw [brownianLaw_unique mu brownianCandidate hmu brownianCandidate_brownianLaw]
  exact brownianCandidate_ae_drift_escape lam

/-! ### Zero occupation from deterministic-time nullity

The theorem below isolates the Fubini/Tonelli part of the occupation argument.
Its only stochastic input is the exact fixed-positive-time null statement; all
joint measurability, exceptional time zero, countable compact exhaustion, and
descent to arbitrary positive `T` are discharged here. -/

def reflectedZeroOnCompact (w : BrownianPath) (lam T : ℝ) : Set ℝ :=
  {t : ℝ | 0 ≤ t ∧ t ≤ T ∧ reflected w lam t.toNNReal = 0}

private lemma continuous_reflected_realTime_joint (lam : ℝ) :
    Continuous (fun p : BrownianPath × ℝ ↦
      reflected p.1 lam p.2.toNNReal) := by
  simpa only [Function.comp_apply] using!
    (W13_BROWNIAN_Ranks.continuous_reflected_joint lam).comp
      (continuous_fst.prodMk (by fun_prop))

theorem measurableSet_reflectedZeroOnCompact_joint (lam T : ℝ) :
    MeasurableSet {p : BrownianPath × ℝ |
      p.2 ∈ reflectedZeroOnCompact p.1 lam T} := by
  have href := (continuous_reflected_realTime_joint lam).measurable
  simp only [reflectedZeroOnCompact, Set.mem_setOf_eq]
  exact (measurableSet_le measurable_const measurable_snd).inter
    ((measurableSet_le measurable_snd measurable_const).inter
      (href (measurableSet_singleton 0)))

private theorem ae_zeroOccupation_compact_of_fixedTime_null
    (mu : PathLaw) [SFinite mu] (lam : ℝ)
    (hfixed : ∀ t : ℝ, 0 < t →
      mu {w : BrownianPath | reflected w lam t.toNNReal = 0} = 0)
    (n : ℕ) :
    ∀ᵐ w ∂mu, volume (reflectedZeroOnCompact w lam n) = 0 := by
  let p : BrownianPath → ℝ → Prop := fun w t ↦
    t ∉ reflectedZeroOnCompact w lam n
  have hpmeas : MeasurableSet {z : BrownianPath × ℝ | p z.1 z.2} := by
    exact (measurableSet_reflectedZeroOnCompact_joint lam n).compl
  have htime : ∀ᵐ t ∂(volume : Measure ℝ), ∀ᵐ w ∂mu, p w t := by
    filter_upwards [(volume : Measure ℝ).ae_ne 0] with t ht0
    by_cases ht : 0 < t
    · have hnull := hfixed t ht
      have hae : ∀ᵐ w ∂mu,
          w ∉ {w : BrownianPath | reflected w lam t.toNNReal = 0} :=
        measure_eq_zero_iff_ae_notMem.mp hnull
      filter_upwards [hae] with w hw
      intro hmem
      exact hw hmem.2.2
    · have htneg : t < 0 := lt_of_le_of_ne (le_of_not_gt ht) ht0
      filter_upwards [] with w
      intro hmem
      exact (not_le_of_gt htneg) hmem.1
  have hpath : ∀ᵐ w ∂mu, ∀ᵐ t ∂(volume : Measure ℝ), p w t :=
    ((mu.ae_ae_comm (ν := volume) hpmeas)).mpr htime
  filter_upwards [hpath] with w hw
  apply measure_eq_zero_iff_ae_notMem.mpr
  simpa only [p] using! hw

/-- Fubini upgrade from fixed positive deterministic-time nullity to the
literal zero-occupation clause used by `GoodExcursionPath`. -/
theorem ae_zeroOccupation_of_fixedTime_null
    (mu : PathLaw) (hprob : IsProbabilityMeasure mu) (lam : ℝ)
    (hfixed : ∀ t : ℝ, 0 < t →
      mu {w : BrownianPath | reflected w lam t.toNNReal = 0} = 0) :
    ∀ᵐ w ∂mu, ∀ T : ℝ, 0 < T →
      volume {t : ℝ | 0 ≤ t ∧ t ≤ T ∧
        reflected w lam t.toNNReal = 0} = 0 := by
  letI : IsProbabilityMeasure mu := hprob
  have hcompact : ∀ n : ℕ,
      ∀ᵐ w ∂mu, volume (reflectedZeroOnCompact w lam n) = 0 :=
    ae_zeroOccupation_compact_of_fixedTime_null mu lam hfixed
  have hall : ∀ᵐ w ∂mu, ∀ n : ℕ,
      volume (reflectedZeroOnCompact w lam n) = 0 := by
    simpa only [ae_all_iff] using! hcompact
  filter_upwards [hall] with w hw
  intro T hT
  obtain ⟨n, hn⟩ := exists_nat_ge T
  apply measure_mono_null _ (hw n)
  intro t ht
  exact ⟨ht.1, ht.2.1.trans hn, ht.2.2⟩

/-! ### Independent ordered increment blocks

The public Brownian specification has already been upgraded in `Law` to an
exact product law for every finite strictly ordered increment vector.  The
lemmas below expose the corresponding independence statement in a form that
can be grouped at a deterministic cut.  This is the finite-dimensional core
of past/future independence for the natural filtration and is also the atom
calculation needed by the discretized stopped-shift argument. -/

def brownianIncrementVector (m : ℕ) (t : ℕ → NNReal) :
    BrownianPath → Fin m → ℝ :=
  fun w j ↦ w (t (j + 1)) - w (t j)

theorem measurable_brownianIncrementVector (m : ℕ) (t : ℕ → NNReal) :
    Measurable (brownianIncrementVector m t) := by
  apply measurable_pi_lambda
  intro j
  exact ((ContinuousEvalConst.continuous_eval_const (t (j + 1))).sub
    (ContinuousEvalConst.continuous_eval_const (t j))).measurable

theorem brownianIncrementVector_law (mu : PathLaw) (hmu : BrownianLaw mu)
    (m : ℕ) (t : ℕ → NNReal)
    (ht : ∀ j < m, t j < t (j + 1)) :
    Measure.map (brownianIncrementVector m t) mu =
      Measure.pi (fun j : Fin m ↦
        gaussianReal 0
          (((t (j + 1) : NNReal) : ℝ) - ((t j : NNReal) : ℝ)).toNNReal) := by
  simpa [HasBrownianIncrementLaws, brownianIncrementVector] using!
    (incrementLaws_of_brownianLaw mu hmu).2.2 m t ht

theorem brownianIncrementCoordinate_law (mu : PathLaw) (hmu : BrownianLaw mu)
    (m : ℕ) (t : ℕ → NNReal)
    (ht : ∀ j < m, t j < t (j + 1)) (j : Fin m) :
    Measure.map (fun w : BrownianPath ↦ brownianIncrementVector m t w j) mu =
      gaussianReal 0
        (((t (j + 1) : NNReal) : ℝ) - ((t j : NNReal) : ℝ)).toNNReal := by
  let gaussian : Fin m → Measure ℝ := fun i ↦
    gaussianReal 0
      (((t (i + 1) : NNReal) : ℝ) - ((t i : NNReal) : ℝ)).toNNReal
  calc
    Measure.map (fun w : BrownianPath ↦ brownianIncrementVector m t w j) mu =
        Measure.map (Function.eval j)
          (Measure.map (brownianIncrementVector m t) mu) := by
      rw [AEMeasurable.map_map_of_aemeasurable
        (measurable_pi_apply j).aemeasurable
        (measurable_brownianIncrementVector m t).aemeasurable]
      rfl
    _ = Measure.map (Function.eval j) (Measure.pi gaussian) := by
      rw [brownianIncrementVector_law mu hmu m t ht]
    _ = gaussian j := (measurePreserving_eval gaussian j).map_eq

theorem iIndepFun_brownianIncrementVector
    (mu : PathLaw) (hmu : BrownianLaw mu)
    (m : ℕ) (t : ℕ → NNReal)
    (ht : ∀ j < m, t j < t (j + 1)) :
    iIndepFun
      (fun j : Fin m ↦ fun w : BrownianPath ↦
        brownianIncrementVector m t w j) mu := by
  letI : IsProbabilityMeasure mu := hmu.1
  apply (iIndepFun_iff_map_fun_eq_pi_map fun j ↦
    ((measurable_pi_apply j).comp
      (measurable_brownianIncrementVector m t)).aemeasurable).2
  change Measure.map (brownianIncrementVector m t) mu =
    Measure.pi (fun j : Fin m ↦
      Measure.map (fun w : BrownianPath ↦
        brownianIncrementVector m t w j) mu)
  rw [brownianIncrementVector_law mu hmu m t ht]
  congr 1
  funext j
  exact (brownianIncrementCoordinate_law mu hmu m t ht j).symm

theorem indepFun_brownianIncrementGroups
    (mu : PathLaw) (hmu : BrownianLaw mu)
    (m : ℕ) (t : ℕ → NNReal)
    (ht : ∀ j < m, t j < t (j + 1))
    (S T : Finset (Fin m)) (hST : Disjoint S T) :
    IndepFun
      (fun w : BrownianPath ↦ fun j : S ↦
        brownianIncrementVector m t w j)
      (fun w : BrownianPath ↦ fun j : T ↦
        brownianIncrementVector m t w j) mu := by
  exact (iIndepFun_brownianIncrementVector mu hmu m t ht).indepFun_finset
    S T hST fun j ↦ (measurable_pi_apply j).comp
      (measurable_brownianIncrementVector m t)

end

end Erdos745.WrapUp.Proofs.Internal.W13_BROWNIAN_Regularity


namespace Erdos745.WrapUp.Proofs.Internal.W13_BROWNIAN_Hitting

noncomputable section
open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology

open W13_BROWNIAN_Regularity

local instance : MeasurableSpace BrownianPath := borel BrownianPath
local instance : BorelSpace BrownianPath := ⟨rfl⟩

/-! ### First reflected zero after a deterministic time

This is an extended time so it has a value even on paths with no future zero.
The infimum formulation agrees exactly with the endpoint of every excursion
containing the probe time.  Escape of the drift proves its finiteness on the
Brownian full-measure set, independently of any stopping-time construction. -/

private theorem continuous_drift_path (w : BrownianPath) (lam : ℝ) :
    Continuous (drift w lam) := by
  unfold drift
  fun_prop

private def unitNNReal (x : unitInterval) : NNReal :=
  NNReal.mk ((x : ℝ)) (x.property.1)

private def scaleToTime (t : NNReal) (x : unitInterval) : NNReal :=
  t * unitNNReal x

private theorem scaleToTime_image (t : NNReal) :
    scaleToTime t '' Set.univ = Set.Icc 0 t := by
  ext u
  constructor
  · rintro ⟨x, _hx, rfl⟩
    constructor
    · exact zero_le
    · exact mul_le_of_le_one_right (zero_le) (by
        exact_mod_cast x.property.2)
  · intro hu
    by_cases ht : t = 0
    · subst t
      have hu0 : u = 0 := le_antisymm hu.2 hu.1
      subst u
      refine ⟨(0 : unitInterval), Set.mem_univ _, ?_⟩
      simp [scaleToTime, unitNNReal]
    · have htpos : 0 < (t : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr ht)
      let x : unitInterval :=
        ⟨(u : ℝ) / (t : ℝ), by
          constructor
          · positivity
          · exact (div_le_one htpos).2 (by exact_mod_cast hu.2)⟩
      refine ⟨x, Set.mem_univ _, ?_⟩
      apply NNReal.eq
      simp only [scaleToTime, unitNNReal, NNReal.coe_mul, NNReal.coe_mk, x]
      field_simp

private theorem compact_nnreal_Icc (t : NNReal) :
    IsCompact (Set.Icc (0 : NNReal) t) := by
  rw [← scaleToTime_image t]
  apply isCompact_univ.image
  unfold scaleToTime unitNNReal
  fun_prop

/-- Quadratic escape forces another reflected zero after every finite time.
The minimum of the drift on a sufficiently long compact interval lies after
the probe and is a running minimum at its own time. -/
theorem exists_future_reflected_zero_of_escape
    (w : BrownianPath) (lam : ℝ)
    (hescape : Tendsto (drift w lam) atTop atBot) (q : NNReal) :
    ∃ t : NNReal, q < t ∧ reflected w lam t = 0 := by
  let m : ℝ := sInf ((drift w lam) '' Set.Icc (0 : NNReal) q)
  have hcont : Continuous (drift w lam) := continuous_drift_path w lam
  have hcompact : IsCompact ((drift w lam) '' Set.Icc (0 : NNReal) q) :=
    (compact_nnreal_Icc q).image hcont
  rw [tendsto_atTop_atBot] at hescape
  obtain ⟨N, hN⟩ := hescape (m - 1)
  let T : NNReal := max (q + 1) N
  have hqT : q < T := by
    have hq1 : q < q + 1 := lt_add_of_pos_right q (by norm_num)
    exact hq1.trans_le (le_max_left _ _)
  have hNT : N ≤ T := le_max_right _ _
  have hTbelow : drift w lam T < m := by
    have hbound := hN T hNT
    linarith
  obtain ⟨t, ht, hmin⟩ :=
    (compact_nnreal_Icc T).exists_isMinOn
      ⟨T, ⟨zero_le, le_rfl⟩⟩ hcont.continuousOn
  have hminT : drift w lam t ≤ drift w lam T :=
    hmin ⟨zero_le, le_rfl⟩
  have hqt : q < t := by
    by_contra h
    have htq : t ≤ q := le_of_not_gt h
    have hmt : m ≤ drift w lam t := by
      dsimp [m]
      apply csInf_le hcompact.bddBelow
      exact ⟨t, ⟨zero_le, htq⟩, rfl⟩
    linarith
  have hcompact_t : IsCompact ((drift w lam) '' Set.Icc (0 : NNReal) t) :=
    (compact_nnreal_Icc t).image hcont
  have hmin_eq :
      drift w lam t = sInf ((drift w lam) '' Set.Icc (0 : NNReal) t) := by
    apply le_antisymm
    · apply le_csInf
      · exact ⟨drift w lam t, ⟨t, ⟨zero_le, le_rfl⟩, rfl⟩⟩
      · rintro y ⟨u, ⟨hu0, hut⟩, rfl⟩
        exact hmin ⟨hu0, hut.trans ht.2⟩
    · apply csInf_le hcompact_t.bddBelow
      exact ⟨t, ⟨zero_le, le_rfl⟩, rfl⟩
  refine ⟨t, hqt, ?_⟩
  simp [reflected, hmin_eq]

end

end Erdos745.WrapUp.Proofs.Internal.W13_BROWNIAN_Hitting
