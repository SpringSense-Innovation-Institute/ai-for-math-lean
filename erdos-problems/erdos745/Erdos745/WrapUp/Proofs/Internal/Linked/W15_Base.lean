module

public import Erdos745.WrapUp.Proofs.Internal.Linked.W14_Base
public import Mathlib.MeasureTheory.Measure.Portmanteau
public import Mathlib.Analysis.SpecificLimits.Basic
public import Erdos745.WrapUp.Proofs.Internal.Linked.W13_Law

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local simp] Pi.div_def Pi.mul_def Pi.add_def Pi.sub_def Pi.neg_def Pi.inv_def Function.comp_def Pi.pow_def Pi.smul_def Real.rpow_eq_pow

@[expose] public section


/-!
# Support-aware varying-map theorem for the critical window

The ranked-excursion functional used by W15 varies with the graph size and is
not continuous away from the finite exploration supports.  This file isolates
the exact shrinking-closed-envelope argument needed to pass from weak path
laws to the varying finite-rank functionals.  No extension of a finite-support
functional, Skorokhod representation, or global continuity hypothesis is used.
-/

namespace Erdos745.WrapUp.Proofs.Internal.W15_CRITICAL_Mapping

noncomputable section

open Filter MeasureTheory Set
open scoped Topology ENNReal NNReal

variable {X Y : Type*}
  [TopologicalSpace X] [FirstCountableTopology X] [T2Space X]
  [MeasurableSpace X] [BorelSpace X] [HasOuterApproxClosed X]
  [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]

/-- Points in the size-`n` support whose varying image lies in `C`, with
indices restricted to the tail beginning at `m`. -/
def tailGraph (E : ℕ → Set X) (f : ℕ → X → Y) (C : Set Y) (m : ℕ) : Set X :=
  ⋃ n : ℕ, ⋃ (_h : m ≤ n), E n ∩ f n ⁻¹' C

/-- The closed envelope of all supported inverse images from index `m` on. -/
def closedEnvelope (E : ℕ → Set X) (f : ℕ → X → Y)
    (C : Set Y) (m : ℕ) : Set X :=
  closure (tailGraph E f C m)

theorem isClosed_closedEnvelope (E : ℕ → Set X) (f : ℕ → X → Y)
    (C : Set Y) (m : ℕ) :
    IsClosed (closedEnvelope E f C m) :=
  isClosed_closure

theorem mem_tailGraph {E : ℕ → Set X} {f : ℕ → X → Y}
    {C : Set Y} {m n : ℕ} {x : X} (hmn : m ≤ n)
    (hxE : x ∈ E n) (hxf : f n x ∈ C) :
    x ∈ tailGraph E f C m := by
  apply Set.mem_iUnion_of_mem n
  apply Set.mem_iUnion_of_mem hmn
  exact ⟨hxE, hxf⟩

theorem tailGraph_mono {E : ℕ → Set X} {f : ℕ → X → Y}
    {C : Set Y} {m m' : ℕ} (hmm' : m ≤ m') :
    tailGraph E f C m' ⊆ tailGraph E f C m := by
  intro x hx
  rcases Set.mem_iUnion.mp hx with ⟨n, hx⟩
  rcases Set.mem_iUnion.mp hx with ⟨hm'n, hx⟩
  exact mem_tailGraph (hmm'.trans hm'n) hx.1 hx.2

theorem closedEnvelope_antitone (E : ℕ → Set X) (f : ℕ → X → Y)
    (C : Set Y) :
    Antitone (closedEnvelope E f C) := by
  intro m m' hmm'
  exact closure_mono (tailGraph_mono hmm')

/-- Subsequence-stable convergence on the actual supports forces every point
of all shrinking envelopes, outside the exceptional set, into the limiting
closed inverse image.  The selected indices need only tend to infinity; this
is the form directly produced by choosing one point from each tail envelope. -/
theorem iInter_closedEnvelope_subset_of_support_tendsto
    (E : ℕ → Set X) (f : ℕ → X → Y) (g : X → Y) (G : Set X)
    (hseq : ∀ (ns : ℕ → ℕ) (xs : ℕ → X) (x : X),
      Tendsto ns atTop atTop →
      (∀ j, xs j ∈ E (ns j)) →
      Tendsto xs atTop (𝓝 x) → x ∈ G →
      Tendsto (fun j ↦ f (ns j) (xs j)) atTop (𝓝 (g x)))
    {C : Set Y} (hC : IsClosed C) :
    (⋂ m, closedEnvelope E f C m) ⊆ Gᶜ ∪ g ⁻¹' C := by
  intro x hx
  by_cases hxG : x ∈ G
  · right
    rcases exists_antitone_basis (𝓝 x) with ⟨U, hU⟩
    have hxclose (j : ℕ) : x ∈ closure (tailGraph E f C j) := by
      exact Set.mem_iInter.mp hx j
    have hexists (j : ℕ) :
        ∃ y ∈ U j, y ∈ tailGraph E f C j := by
      rcases (mem_closure_iff_nhds.mp (hxclose j)) (U j) (hU.mem j) with
        ⟨y, hyU, hytail⟩
      exact ⟨y, hyU, hytail⟩
    choose xs hxsU hxs_tail using hexists
    have hdata (j : ℕ) :
        ∃ n : ℕ, j ≤ n ∧ xs j ∈ E n ∧ f n (xs j) ∈ C := by
      rcases Set.mem_iUnion.mp (hxs_tail j) with ⟨n, hn⟩
      rcases Set.mem_iUnion.mp hn with ⟨hjn, hn⟩
      exact ⟨n, hjn, hn.1, hn.2⟩
    choose ns hjns hxsE hxsC using hdata
    have hns : Tendsto ns atTop atTop := by
      rw [tendsto_atTop_atTop]
      intro b
      exact ⟨b, fun a hba ↦ hba.trans (hjns a)⟩
    have hxs : Tendsto xs atTop (𝓝 x) := hU.tendsto hxsU
    have himage := hseq ns xs x hns hxsE hxs hxG
    change g x ∈ C
    exact hC.mem_of_tendsto himage (Eventually.of_forall hxsC)
  · left
    exact hxG

/-- Support-aware continuous mapping theorem for a sequence of varying Borel
maps.  `G` is the full-limit-measure set on which the deterministic matching
condition below holds. -/
theorem tendsto_map_of_support_tendsto
    (μs : ℕ → ProbabilityMeasure X) (μ : ProbabilityMeasure X)
    (E : ℕ → Set X) (f : ℕ → X → Y) (g : X → Y) (G : Set X)
    (hμ : Tendsto μs atTop (𝓝 μ))
    (hf : ∀ n, Measurable (f n)) (hg : Measurable g)
    (hsupport : ∀ n, ∀ᵐ x ∂(μs n : Measure X), x ∈ E n)
    (hG : ∀ᵐ x ∂(μ : Measure X), x ∈ G)
    (hseq : ∀ (ns : ℕ → ℕ) (xs : ℕ → X) (x : X),
      Tendsto ns atTop atTop →
      (∀ j, xs j ∈ E (ns j)) →
      Tendsto xs atTop (𝓝 x) → x ∈ G →
      Tendsto (fun j ↦ f (ns j) (xs j)) atTop (𝓝 (g x))) :
    Tendsto (fun n ↦ (μs n).map (f n)) atTop
      (𝓝 (μ.map g)) := by
  apply tendsto_of_forall_isClosed_limsup_le'
  intro C hC
  change limsup (fun n ↦
      (((μs n).map (f n) : ProbabilityMeasure Y) : Measure Y) C) atTop ≤
    ((μ.map g : ProbabilityMeasure Y) : Measure Y) C
  have hmap (n : ℕ) :
      (((μs n).map (f n) : ProbabilityMeasure Y) : Measure Y) C =
        (μs n : Measure X) (f n ⁻¹' C) :=
    ProbabilityMeasure.map_apply' (μs n) (hf n).aemeasurable hC.measurableSet
  have hmapg : ((μ.map g : ProbabilityMeasure Y) : Measure Y) C =
      (μ : Measure X) (g ⁻¹' C) :=
    ProbabilityMeasure.map_apply' μ hg.aemeasurable hC.measurableSet
  simp_rw [hmap, hmapg]
  let A : ℕ → Set X := closedEnvelope E f C
  have hA_closed (m : ℕ) : IsClosed (A m) :=
    isClosed_closedEnvelope E f C m
  have hpre (m : ℕ) :
      ∀ᶠ n in atTop, (μs n : Measure X) (f n ⁻¹' C) ≤
        (μs n : Measure X) (A m) := by
    filter_upwards [eventually_ge_atTop m] with n hmn
    apply measure_mono_ae
    filter_upwards [hsupport n] with x hxE hxC
    apply subset_closure
    exact mem_tailGraph hmn hxE hxC
  have hbound (m : ℕ) :
      limsup (fun n ↦ (μs n : Measure X) (f n ⁻¹' C)) atTop ≤
        (μ : Measure X) (A m) := by
    calc
      limsup (fun n ↦ (μs n : Measure X) (f n ⁻¹' C)) atTop
          ≤ limsup (fun n ↦ (μs n : Measure X) (A m)) atTop :=
            Filter.limsup_le_limsup (hpre m)
      _ ≤ (μ : Measure X) (A m) :=
        ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hμ (hA_closed m)
  have hA_anti : Antitone A := closedEnvelope_antitone E f C
  have hA_tendsto :
      Tendsto (fun m ↦ (μ : Measure X) (A m)) atTop
        (𝓝 ((μ : Measure X) (⋂ m, A m))) := by
    apply tendsto_measure_iInter_atTop
    · intro m
      exact (hA_closed m).measurableSet.nullMeasurableSet
    · exact hA_anti
    · exact ⟨0, measure_ne_top _ _⟩
  have hinter_bound :
      limsup (fun n ↦ (μs n : Measure X) (f n ⁻¹' C)) atTop ≤
        (μ : Measure X) (⋂ m, A m) := by
    exact ge_of_tendsto' hA_tendsto hbound
  have hinter : (⋂ m, A m) ⊆ Gᶜ ∪ g ⁻¹' C := by
    exact iInter_closedEnvelope_subset_of_support_tendsto E f g G hseq hC
  have hae : (⋂ m, A m) ≤ᵐ[(μ : Measure X)] g ⁻¹' C := by
    filter_upwards [hG] with x hxG hxA
    rcases hinter hxA with hxGc | hxC
    · exact (hxGc hxG).elim
    · exact hxC
  exact hinter_bound.trans (measure_mono_ae hae)

end

end Erdos745.WrapUp.Proofs.Internal.W15_CRITICAL_Mapping


/-!
# Borel endpoint codes and truncated critical ranks

This module supplies the concrete Borel maps needed by the support-aware
mapping theorem.  The limiting code is applied directly to an uncentered
exploration path: `centerPath p lam` removes the deterministic critical drift,
so the already verified reflected-path compact-infimum API from W13 codes the
ordinary running-minimum excursions of `p`.

The discrete code marks strict mesh records and retains only consecutive
record blocks completed inside the prescribed compact window.  Neither code
invents a terminal boundary.  Both rank maps use a countable injection code;
this makes measurability independent of any tie-breaking convention.
-/

namespace Erdos745.WrapUp.Proofs.Internal.W15_CRITICAL_Truncated

open Erdos745.WrapUp
open Erdos745.WrapUp.Proofs.Internal.W13_BROWNIAN_Ranks
open Erdos745.WrapUp.Proofs.Internal.W15_CRITICAL_Mapping
open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology

noncomputable section
attribute [local instance] Classical.propDecidable

local instance : MeasurableSpace BrownianPath := borel BrownianPath
local instance : BorelSpace BrownianPath := ⟨rfl⟩

/-! ## The uncentered limiting endpoint code -/

/-- The deterministic correction which removes the critical drift. -/
def centerCorrection (lam : ℝ) : BrownianPath where
  toFun t := -lam * (t : ℝ) + (t : ℝ) ^ 2 / 2
  continuous_toFun := by fun_prop

/-- Remove the deterministic critical drift from an already drifted path. -/
def centerPath (p : BrownianPath) (lam : ℝ) : BrownianPath :=
  p + centerCorrection lam

theorem continuous_centerPath (lam : ℝ) :
    Continuous (fun p : BrownianPath ↦ centerPath p lam) := by
  unfold centerPath
  fun_prop

theorem measurable_centerPath (lam : ℝ) :
    Measurable (fun p : BrownianPath ↦ centerPath p lam) :=
  (continuous_centerPath lam).measurable

@[simp] theorem drift_centerPath (p : BrownianPath) (lam : ℝ) (t : NNReal) :
    drift (centerPath p lam) lam t = p t := by
  simp [drift, centerPath, centerCorrection]
  ring

@[simp] theorem reflected_centerPath (p : BrownianPath) (lam : ℝ) (t : NNReal) :
    reflected (centerPath p lam) lam t =
      p t - sInf (p '' Set.Icc 0 t) := by
  unfold reflected
  simp only [drift_centerPath]

/-- Fixed dense probes.  Repetitions are harmless because retention is by the
least probe index lying in an excursion. -/
def codeTime (n : ℕ) : NNReal :=
  TopologicalSpace.denseSeq NNReal n

def leftCodeCondition (lam : ℝ) (q : NNReal) (k : ℕ)
    (p : BrownianPath) : Prop :=
  codeTime k ≤ q ∧
    reflectedIntervalInf lam (codeTime k) q (centerPath p lam) = 0

def rightCodeCondition (lam : ℝ) (q : NNReal) (k : ℕ)
    (p : BrownianPath) : Prop :=
  q ≤ codeTime k ∧
    reflectedIntervalInf lam q (codeTime k) (centerPath p lam) = 0

theorem measurableSet_leftCodeCondition (lam : ℝ) (q : NNReal) (k : ℕ) :
    MeasurableSet {p : BrownianPath | leftCodeCondition lam q k p} := by
  by_cases hk : codeTime k ≤ q
  · simp only [leftCodeCondition, hk, true_and]
    exact (measurable_reflectedIntervalInf lam (codeTime k) q).comp
      (measurable_centerPath lam) (measurableSet_singleton 0)
  · simp [leftCodeCondition, hk]

theorem measurableSet_rightCodeCondition (lam : ℝ) (q : NNReal) (k : ℕ) :
    MeasurableSet {p : BrownianPath | rightCodeCondition lam q k p} := by
  by_cases hk : q ≤ codeTime k
  · simp only [rightCodeCondition, hk, true_and]
    exact (measurable_reflectedIntervalInf lam q (codeTime k)).comp
      (measurable_centerPath lam) (measurableSet_singleton 0)
  · simp [rightCodeCondition, hk]

/-- Last coded zero on the left of `q`. -/
def codedLeft (lam : ℝ) (q : NNReal) (p : BrownianPath) : ENNReal :=
  ⨆ k : ℕ, if leftCodeCondition lam q k p then (codeTime k : ENNReal) else 0

/-- First coded zero on the right of `q`, or `∞` if no such zero exists. -/
def codedRight (lam : ℝ) (q : NNReal) (p : BrownianPath) : ENNReal :=
  ⨅ k : ℕ, if rightCodeCondition lam q k p then (codeTime k : ENNReal) else ⊤

theorem measurable_codedLeft (lam : ℝ) (q : NNReal) :
    Measurable (codedLeft lam q) := by
  unfold codedLeft
  apply Measurable.iSup
  intro k
  exact Measurable.ite (measurableSet_leftCodeCondition lam q k)
    measurable_const measurable_const

theorem measurable_codedRight (lam : ℝ) (q : NNReal) :
    Measurable (codedRight lam q) := by
  unfold codedRight
  apply Measurable.iInf
  intro k
  exact Measurable.ite (measurableSet_rightCodeCondition lam q k)
    measurable_const measurable_const

def codeActive (lam : ℝ) (m : ℕ) (p : BrownianPath) : Prop :=
  0 < reflected (centerPath p lam) lam (codeTime m)

def sameCodedExcursion (lam : ℝ) (j m : ℕ) (p : BrownianPath) : Prop :=
  codeActive lam j p ∧ codeActive lam m p ∧
    0 < reflectedIntervalInf lam (min (codeTime j) (codeTime m))
      (max (codeTime j) (codeTime m)) (centerPath p lam)

theorem measurableSet_codeActive (lam : ℝ) (m : ℕ) :
    MeasurableSet {p : BrownianPath | codeActive lam m p} := by
  exact measurableSet_lt measurable_const
    ((measurable_reflected_fixedTime lam (codeTime m)).comp
      (measurable_centerPath lam))

theorem measurableSet_sameCodedExcursion (lam : ℝ) (j m : ℕ) :
    MeasurableSet {p : BrownianPath | sameCodedExcursion lam j m p} := by
  have hpos : MeasurableSet {p : BrownianPath |
      0 < reflectedIntervalInf lam (min (codeTime j) (codeTime m))
        (max (codeTime j) (codeTime m)) (centerPath p lam)} :=
    measurableSet_lt
      (measurable_const : Measurable (fun _ : BrownianPath ↦ (0 : ℝ)))
      ((measurable_reflectedIntervalInf lam
        (min (codeTime j) (codeTime m))
        (max (codeTime j) (codeTime m))).comp
          (measurable_centerPath lam))
  change MeasurableSet ({p : BrownianPath | codeActive lam j p} ∩
    ({p : BrownianPath | codeActive lam m p} ∩
      {p : BrownianPath |
        0 < reflectedIntervalInf lam (min (codeTime j) (codeTime m))
          (max (codeTime j) (codeTime m)) (centerPath p lam)}))
  exact (measurableSet_codeActive lam j).inter
    ((measurableSet_codeActive lam m).inter hpos)

/-- Retain the least dense probe in each positive component. -/
def retainedCode (lam : ℝ) (m : ℕ) (p : BrownianPath) : Prop :=
  codeActive lam m p ∧ ∀ j < m, ¬ sameCodedExcursion lam j m p

theorem measurableSet_retainedCode (lam : ℝ) (m : ℕ) :
    MeasurableSet {p : BrownianPath | retainedCode lam m p} := by
  have hprev : MeasurableSet {p : BrownianPath |
      ∀ j : Fin m, ¬ sameCodedExcursion lam j.val m p} := by
    rw [show {p : BrownianPath |
        ∀ j : Fin m, ¬ sameCodedExcursion lam j.val m p} =
        ⋂ j : Fin m, {p : BrownianPath |
          ¬ sameCodedExcursion lam j.val m p} by
      ext p
      simp]
    exact MeasurableSet.iInter fun j ↦
      (measurableSet_sameCodedExcursion lam j.val m).compl
  have heq : {p : BrownianPath | retainedCode lam m p} =
      {p : BrownianPath | codeActive lam m p} ∩
        {p : BrownianPath | ∀ j : Fin m,
          ¬ sameCodedExcursion lam j.val m p} := by
    ext p
    constructor
    · intro hp
      exact ⟨hp.1, fun j ↦ hp.2 j.val j.isLt⟩
    · intro hp
      exact ⟨hp.1, fun j hj ↦ hp.2 ⟨j, hj⟩⟩
  rw [heq]
  exact (measurableSet_codeActive lam m).inter hprev

/-- Length of the retained coded excursion, with inactive or nonfinite codes
sent to zero. -/
def codedLength (lam : ℝ) (m : ℕ) (p : BrownianPath) : ENNReal :=
  if retainedCode lam m p ∧ codedRight lam (codeTime m) p < ⊤ then
    codedRight lam (codeTime m) p - codedLeft lam (codeTime m) p
  else 0

theorem measurable_codedLength (lam : ℝ) (m : ℕ) :
    Measurable (codedLength lam m) := by
  unfold codedLength
  apply Measurable.ite
  · exact (measurableSet_retainedCode lam m).inter
      (measurableSet_lt (measurable_codedRight lam (codeTime m)) measurable_const)
  · exact (measurable_codedRight lam (codeTime m)).sub
      (measurable_codedLeft lam (codeTime m))
  · exact measurable_const

/-- Limiting excursions retained by the positive length cutoff and strict
compact endpoint window. -/
def limitKeptLength (lam a T U : ℝ) (m : ℕ) (p : BrownianPath) : ENNReal :=
  if a < (codedLength lam m p).toReal ∧
      (codedLeft lam (codeTime m) p).toReal < T ∧
      (codedRight lam (codeTime m) p).toReal < U then
    codedLength lam m p
  else 0

theorem measurable_limitKeptLength (lam a T U : ℝ) (m : ℕ) :
    Measurable (limitKeptLength lam a T U m) := by
  unfold limitKeptLength
  apply Measurable.ite
  · have hlen : MeasurableSet {p : BrownianPath |
        a < (codedLength lam m p).toReal} :=
      measurableSet_lt
        (measurable_const : Measurable (fun _ : BrownianPath ↦ a))
        (measurable_codedLength lam m).ennreal_toReal
    have hleft : MeasurableSet {p : BrownianPath |
        (codedLeft lam (codeTime m) p).toReal < T} :=
      measurableSet_lt
        (measurable_codedLeft lam (codeTime m)).ennreal_toReal
        (measurable_const : Measurable (fun _ : BrownianPath ↦ T))
    have hright : MeasurableSet {p : BrownianPath |
        (codedRight lam (codeTime m) p).toReal < U} :=
      measurableSet_lt
        (measurable_codedRight lam (codeTime m)).ennreal_toReal
        (measurable_const : Measurable (fun _ : BrownianPath ↦ U))
    exact hlen.inter (hleft.inter hright)
  · exact measurable_codedLength lam m
  · exact measurable_const

/-! ## Strict-record blocks on the discrete mesh -/

def meshTime (n j : ℕ) : NNReal :=
  Real.toNNReal ((j : ℝ) / n23 n)

def meshValue (n j : ℕ) (p : BrownianPath) : ℝ :=
  p (meshTime n j)

theorem continuous_meshValue (n j : ℕ) : Continuous (meshValue n j) := by
  unfold meshValue
  fun_prop

theorem measurable_meshValue (n j : ℕ) : Measurable (meshValue n j) :=
  (continuous_meshValue n j).measurable

/-- Index zero is the initial boundary; later boundaries are strict new mesh
records. -/
def meshRecord (n j : ℕ) (p : BrownianPath) : Prop :=
  j = 0 ∨ ∀ l < j, meshValue n j p < meshValue n l p

theorem measurableSet_meshRecord (n j : ℕ) :
    MeasurableSet {p : BrownianPath | meshRecord n j p} := by
  by_cases hj : j = 0
  · simp [meshRecord, hj]
  · have heq : {p : BrownianPath | meshRecord n j p} =
        ⋂ l : Fin j, {p : BrownianPath |
          meshValue n j p < meshValue n l.val p} := by
      ext p
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
      constructor
      · intro hp l
        rcases hp with hp | hp
        · exact (hj hp).elim
        · exact hp l.val l.isLt
      · intro hp
        exact Or.inr fun l hl ↦ hp ⟨l, hl⟩
    rw [heq]
    exact MeasurableSet.iInter fun l ↦
      measurableSet_lt (measurable_meshValue n j)
        (measurable_meshValue n l.val)

def successiveMeshRecords (n s t : ℕ) (p : BrownianPath) : Prop :=
  s < t ∧ meshRecord n s p ∧ meshRecord n t p ∧
    ∀ u, s < u → u < t → ¬ meshRecord n u p

theorem measurableSet_successiveMeshRecords (n s t : ℕ) :
    MeasurableSet {p : BrownianPath | successiveMeshRecords n s t p} := by
  by_cases hst : s < t
  · have hbetween : MeasurableSet {p : BrownianPath |
        ∀ u, s < u → u < t → ¬ meshRecord n u p} := by
      rw [show {p : BrownianPath |
          ∀ u, s < u → u < t → ¬ meshRecord n u p} =
          ⋂ u : ℕ, {p : BrownianPath |
            s < u → u < t → ¬ meshRecord n u p} by
        ext p
        simp]
      apply MeasurableSet.iInter
      intro u
      by_cases hsu : s < u
      · by_cases hut : u < t
        · have heq : {p : BrownianPath |
              s < u → u < t → ¬ meshRecord n u p} =
              {p : BrownianPath | ¬ meshRecord n u p} := by
            ext p
            simp [hsu, hut]
          rw [heq]
          exact (measurableSet_meshRecord n u).compl
        · simp [hut]
      · simp [hsu]
    have heq : {p : BrownianPath | successiveMeshRecords n s t p} =
        {p : BrownianPath | meshRecord n s p} ∩
          {p : BrownianPath | meshRecord n t p} ∩
          {p : BrownianPath |
            ∀ u, s < u → u < t → ¬ meshRecord n u p} := by
      ext p
      simp [successiveMeshRecords, hst, and_assoc]
    rw [heq]
    exact ((measurableSet_meshRecord n s).inter
      (measurableSet_meshRecord n t)).inter hbetween
  · simp [successiveMeshRecords, hst]

def meshBlockLength (n s t : ℕ) : ℝ :=
  ((t : ℝ) - (s : ℝ)) / n23 n

/-- A completed strict-record block in the requested mesh window.  The extra
`t ≤ floor(U*n23 n)+1` guard makes the code finite even away from BFS paths. -/
def discreteKeptLength (n : ℕ) (a T U : ℝ) (z : ℕ × ℕ)
    (p : BrownianPath) : ENNReal :=
  if successiveMeshRecords n z.1 z.2 p ∧
      z.2 ≤ ⌊U * n23 n⌋₊ + 1 ∧
      (meshTime n z.1 : ℝ) < T ∧
      (meshTime n z.2 : ℝ) < U ∧
      a < meshBlockLength n z.1 z.2 then
    ENNReal.ofReal (meshBlockLength n z.1 z.2)
  else 0

theorem measurable_discreteKeptLength (n : ℕ) (a T U : ℝ) (z : ℕ × ℕ) :
    Measurable (discreteKeptLength n a T U z) := by
  by_cases hguard : z.2 ≤ ⌊U * n23 n⌋₊ + 1 ∧
      (meshTime n z.1 : ℝ) < T ∧
      (meshTime n z.2 : ℝ) < U ∧
      a < meshBlockLength n z.1 z.2
  · unfold discreteKeptLength
    simpa only [hguard, and_true] using!
      Measurable.ite (measurableSet_successiveMeshRecords n z.1 z.2)
        measurable_const measurable_const
  · have hzero : discreteKeptLength n a T U z =
        fun _ : BrownianPath ↦ 0 := by
      funext p
      simp only [discreteKeptLength]
      rw [if_neg]
      exact fun hp ↦ hguard hp.2
    exact hzero ▸ measurable_const

/-! ## Countably coded ranks and vector-valued maps -/

/-- The `i`th largest positive candidate value, with multiplicity and zero
padding.  Injections retain ties without imposing an order on equal values. -/
def rankFromCandidates (v : ℕ → BrownianPath → ENNReal) (i : ℕ)
    (p : BrownianPath) : ENNReal :=
  if i = 0 then 0 else
    ⨆ f : Fin i → ℕ,
      if Function.Injective f then ⨅ j : Fin i, v (f j) p else 0

theorem measurable_rankFromCandidates
    (v : ℕ → BrownianPath → ENNReal) (hv : ∀ m, Measurable (v m)) (i : ℕ) :
    Measurable (rankFromCandidates v i) := by
  by_cases hi : i = 0
  · subst i
    change Measurable (fun _ : BrownianPath ↦ (0 : ENNReal))
    exact measurable_const
  · unfold rankFromCandidates
    simp only [hi, if_false]
    apply Measurable.iSup
    intro f
    by_cases hf : Function.Injective f
    · simpa only [hf, if_true] using! Measurable.iInf fun j : Fin i ↦ hv (f j)
    · simp [hf]

def limitTruncatedRank (lam a T U : ℝ) (k : ℕ)
    (p : BrownianPath) : Fin k → ℝ :=
  fun r ↦ (rankFromCandidates (limitKeptLength lam a T U)
    (r.val + 1) p).toReal

theorem measurable_limitTruncatedRank (lam a T U : ℝ) (k : ℕ) :
    Measurable (limitTruncatedRank lam a T U k) := by
  apply measurable_pi_lambda
  intro r
  exact (measurable_rankFromCandidates (limitKeptLength lam a T U)
    (measurable_limitKeptLength lam a T U) (r.val + 1)).ennreal_toReal

def pairCode (m : ℕ) : ℕ × ℕ := Nat.unpair m

def discreteTruncatedRank (n : ℕ) (a T U : ℝ) (k : ℕ)
    (p : BrownianPath) : Fin k → ℝ :=
  fun r ↦ (rankFromCandidates
    (fun m ↦ discreteKeptLength n a T U (pairCode m))
    (r.val + 1) p).toReal

theorem measurable_discreteTruncatedRank (n : ℕ) (a T U : ℝ) (k : ℕ) :
    Measurable (discreteTruncatedRank n a T U k) := by
  apply measurable_pi_lambda
  intro r
  exact (measurable_rankFromCandidates
    (fun m ↦ discreteKeptLength n a T U (pairCode m))
    (fun m ↦ measurable_discreteKeptLength n a T U (pairCode m))
    (r.val + 1)).ennreal_toReal

/-! ## Subsequence-stable support mapping -/

/-- Pointwise form of the path-specific matching obligation.  Its quantifier
order is exactly the one required by shrinking closed envelopes: indices may
be any sequence tending to infinity and paths must lie in the corresponding
finite supports. -/
def SupportStableAt {Y : Type*} [TopologicalSpace Y]
    (E : ℕ → Set BrownianPath) (f : ℕ → BrownianPath → Y)
    (g : BrownianPath → Y) (p : BrownianPath) : Prop :=
  ∀ (ns : ℕ → ℕ) (ps : ℕ → BrownianPath),
    Tendsto ns atTop atTop →
    (∀ j, ps j ∈ E (ns j)) →
    Tendsto ps atTop (𝓝 p) →
    Tendsto (fun j ↦ f (ns j) (ps j)) atTop (𝓝 (g p))

/-- The verified support-aware theorem instantiated with the concrete
discrete and limiting truncated-rank maps. -/
theorem truncated_rank_weak_convergence
    (μs : ℕ → ProbabilityMeasure BrownianPath)
    (μ : ProbabilityMeasure BrownianPath)
    (E : ℕ → Set BrownianPath) (lam a T U : ℝ) (k : ℕ)
    (hμ : Tendsto μs atTop (𝓝 μ))
    (hsupport : ∀ n, ∀ᵐ p ∂(μs n : Measure BrownianPath), p ∈ E n)
    (hmatching : ∀ᵐ p ∂(μ : Measure BrownianPath),
      SupportStableAt E
        (fun n ↦ discreteTruncatedRank n a T U k)
        (limitTruncatedRank lam a T U k) p) :
    Tendsto (fun n ↦ (μs n).map (discreteTruncatedRank n a T U k)) atTop
      (𝓝 (μ.map (limitTruncatedRank lam a T U k))) := by
  let G : Set BrownianPath := {p | SupportStableAt E
    (fun n ↦ discreteTruncatedRank n a T U k)
    (limitTruncatedRank lam a T U k) p}
  apply tendsto_map_of_support_tendsto μs μ E
    (fun n ↦ discreteTruncatedRank n a T U k)
    (limitTruncatedRank lam a T U k) G hμ
    (fun n ↦ measurable_discreteTruncatedRank n a T U k)
    (measurable_limitTruncatedRank lam a T U k) hsupport hmatching
  intro ns ps p hns hps hp hpG
  exact hpG ns ps hns hps hp

end

end Erdos745.WrapUp.Proofs.Internal.W15_CRITICAL_Truncated


/-!
# Exact record blocks of the finite exploration

The integer walk's strict lower records are precisely its queue-empty times
through the last processed vertex.  The public polygonal interpolation takes
the scaled walk value at every mesh point, so the Borel strict-record code
has the same boundaries on exploration paths.
-/

namespace Erdos745.WrapUp.Proofs.Internal.W15_CRITICAL_FiniteBlocks

open Erdos745.WrapUp
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_Finite
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_Interpolation
open Erdos745.WrapUp.Proofs.Internal.W15_CRITICAL_Truncated

noncomputable section
attribute [local instance] Classical.propDecidable

private theorem rootCount_mono {n : ℕ} (G : Graph n) :
    Monotone (rootCount G) := by
  apply monotone_nat_of_le_succ
  intro j
  simp only [rootCount_succ]
  omega

private theorem seen_ne_univ_of_queue_empty {n : ℕ} (G : Graph n)
    {j : ℕ} (hj : j < n) (hq : (explore G j).queue = []) :
    (explore G j).seen ≠ Finset.univ := by
  intro heq
  have hp : processed G j = Finset.univ := by
    simp [processed, hq, heq]
  have hc := processed_card_of_le G j hj.le
  rw [hp] at hc
  simp at hc
  omega

private theorem rootCount_succ_of_queue_empty {n : ℕ} (G : Graph n)
    {j : ℕ} (hj : j < n) (hq : (explore G j).queue = []) :
    rootCount G (j + 1) = rootCount G j + 1 := by
  simp [rootCount_succ, rootStarts, hq,
    seen_ne_univ_of_queue_empty G hj hq]

private theorem rootCount_succ_of_queue_nonempty {n : ℕ} (G : Graph n)
    {j : ℕ} (hq : (explore G j).queue ≠ []) :
    rootCount G (j + 1) = rootCount G j := by
  simp [rootCount_succ, rootStarts, hq]

/-- While a queue is active, an earlier queue-empty time has the same walk
level as the lowest value that the active queue can reach. -/
private theorem active_prior_level {n : ℕ} (G : Graph n) :
    ∀ j : ℕ, j ≤ n → (explore G j).queue ≠ [] →
      ∃ l < j, (explore G l).walk = 1 - (rootCount G j : ℤ)
  | 0, _, hq => by simp at hq
  | j + 1, hj, hq => by
      by_cases hprev : (explore G j).queue = []
      · refine ⟨j, Nat.lt_succ_self j, ?_⟩
        have hr := rootCount_succ_of_queue_empty G
          (Nat.lt_of_succ_le hj) hprev
        have hw := (walk_eq_neg_rootCount_iff G j).2 hprev
        rw [hr]
        omega
      · obtain ⟨l, hl, hw⟩ := active_prior_level G j
          (Nat.le_of_lt (Nat.lt_of_succ_le hj)) hprev
        refine ⟨l, Nat.lt_succ_of_lt hl, ?_⟩
        rw [rootCount_succ_of_queue_nonempty G hprev]
        exact hw

/-- A positive integer time is a strict new minimum of the BFS walk exactly
when the queue has just become empty. -/
theorem strict_walk_record_iff_queue_empty {n : ℕ} (G : Graph n)
    {j : ℕ} (hj : j ≤ n) (hj0 : 0 < j) :
    (∀ l < j, (explore G j).walk < (explore G l).walk) ↔
      (explore G j).queue = [] := by
  constructor
  · intro hrecord
    by_contra hq
    obtain ⟨l, hl, hlevel⟩ := active_prior_level G j hj hq
    have hwalk := walk_eq_queue_sub_rootCount G j
    have hlen : 0 < (explore G j).queue.length :=
      List.length_pos_of_ne_nil hq
    have hle : (explore G l).walk ≤ (explore G j).walk := by
      rw [hlevel, hwalk]
      omega
    exact (not_lt_of_ge hle) (hrecord l hl)
  · intro hq l hl
    have hrle : rootCount G l ≤ rootCount G j :=
      rootCount_mono G hl.le
    have hwj := (walk_eq_neg_rootCount_iff G j).2 hq
    by_cases hlq : (explore G l).queue = []
    · have hltn : l < n := lt_of_lt_of_le hl hj
      have hrstep := rootCount_succ_of_queue_empty G hltn hlq
      have hrstep_le : rootCount G (l + 1) ≤ rootCount G j :=
        rootCount_mono G (Nat.succ_le_of_lt hl)
      have hwl := (walk_eq_neg_rootCount_iff G l).2 hlq
      omega
    · have hwl := walk_eq_queue_sub_rootCount G l
      have hlen : 0 < (explore G l).queue.length :=
        List.length_pos_of_ne_nil hlq
      omega

theorem walk_record_iff_queue_empty {n : ℕ} (G : Graph n)
    {j : ℕ} (hj : j ≤ n) :
    (j = 0 ∨ ∀ l < j, (explore G j).walk < (explore G l).walk) ↔
      (explore G j).queue = [] := by
  by_cases hj0 : j = 0
  · subst j
    simp [initialState]
  · simpa [hj0] using! strict_walk_record_iff_queue_empty G hj (Nat.pos_of_ne_zero hj0)

/-- The floor interpolation evaluates to the integer walk at each genuine
mesh point. -/
theorem meshValue_interpolation {n : ℕ} (G : Graph n) (hn : 0 < n)
    (j : ℕ) :
    meshValue n j (continuousRawExploration G) =
      ((explore G j).walk : ℝ) / n13 n := by
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : 0 < n23 n := Real.rpow_pos_of_pos hnreal _
  have hmesh : ((meshTime n j : NNReal) : ℝ) = (j : ℝ) / n23 n := by
    have hnonneg : (0 : ℝ) ≤ (j : ℝ) / n23 n :=
      div_nonneg (Nat.cast_nonneg _) hs.le
    simp [meshTime, Real.coe_toNNReal, hnonneg]
  have hx : ((meshTime n j : NNReal) : ℝ) * n23 n = (j : ℝ) := by
    rw [hmesh]
    field_simp
  rw [meshValue, continuousRawExploration_apply]
  simp [rawExploration, hx, Nat.floor_natCast]

/-- The concrete Borel mesh record predicate is the queue-empty predicate on
the finite support of the exploration law. -/
theorem meshRecord_interpolation_iff_queue_empty {n : ℕ} (G : Graph n)
    (hn : 0 < n) {j : ℕ} (hj : j ≤ n) :
    meshRecord n j (continuousRawExploration G) ↔
      (explore G j).queue = [] := by
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : 0 < n13 n := Real.rpow_pos_of_pos hnreal _
  have hcmp (l : ℕ) :
      meshValue n j (continuousRawExploration G) <
        meshValue n l (continuousRawExploration G) ↔
      (explore G j).walk < (explore G l).walk := by
    rw [meshValue_interpolation G hn j,
      meshValue_interpolation G hn l,
      div_lt_div_iff_of_pos_right hs]
    exact Int.cast_lt
  unfold meshRecord
  simpa only [hcmp] using! walk_record_iff_queue_empty G hj

/-- Completed strict-record intervals of the public mesh code are exactly
consecutive queue-empty intervals, up to the terminal time `n`. -/
theorem successiveMeshRecords_interpolation_iff {n : ℕ} (G : Graph n)
    (hn : 0 < n) {s t : ℕ} (ht : t ≤ n) :
    successiveMeshRecords n s t (continuousRawExploration G) ↔
      s < t ∧ (explore G s).queue = [] ∧
      (explore G t).queue = [] ∧
      ∀ u, s < u → u < t → (explore G u).queue ≠ [] := by
  constructor
  · intro h
    rcases h with ⟨hst, hs, ht', hinterior⟩
    refine ⟨hst,
      (meshRecord_interpolation_iff_queue_empty G hn (le_trans hst.le ht)).mp hs,
      (meshRecord_interpolation_iff_queue_empty G hn ht).mp ht', ?_⟩
    intro u hsu hut huq
    exact hinterior u hsu hut
      ((meshRecord_interpolation_iff_queue_empty G hn
        (le_trans hut.le ht)).mpr huq)
  · rintro ⟨hst, hs, ht', hinterior⟩
    refine ⟨hst,
      (meshRecord_interpolation_iff_queue_empty G hn (le_trans hst.le ht)).mpr hs,
      (meshRecord_interpolation_iff_queue_empty G hn ht).mpr ht', ?_⟩
    intro u hsu hut hu
    exact hinterior u hsu hut
      ((meshRecord_interpolation_iff_queue_empty G hn
        (le_trans hut.le ht)).mp hu)

/-- A completed mesh block has exactly the scaled difference between the
numbers of vertices processed at its two record boundaries. -/
private theorem active_step_inside {n : ℕ} (G : Graph n)
    (old B seen : Finset (Fin n)) (v : Fin n)
    (rest : List (Fin n)) (z : ℤ)
    (hqueue : ∀ u ∈ v :: rest, u ∈ B)
    (hseen : ∀ u ∈ seen, u ∉ old → u ∈ B)
    (hclosed : ∀ u ∈ B, ∀ w, adj G u w → w ∈ B) :
    (∀ u ∈ (bfsStep G (⟨seen, v :: rest, z⟩ : BFSState n)).queue, u ∈ B) ∧
    (∀ u ∈ (bfsStep G (⟨seen, v :: rest, z⟩ : BFSState n)).seen,
      u ∉ old → u ∈ B) := by
  have hchildren : ∀ u ∈ newChildren G seen v, u ∈ B := by
    intro u hu
    exact hclosed v (hqueue v (by simp)) u
      ((mem_newChildren_iff G seen v u).mp hu).2
  rw [bfsStep_queue_cons]
  constructor
  · intro u hu
    simp only [BFSState.queue, List.mem_append, Finset.mem_toList] at hu
    rcases hu with hu | hu
    · exact hqueue u (by simp [hu])
    · exact hchildren u hu
  · intro u hu hnot
    change u ∈ seen ∪ newChildren G seen v at hu
    rcases Finset.mem_union.mp hu with hu | hu
    · exact hseen u hu hnot
    · exact hchildren u hu

private theorem root_step_inside {n : ℕ} (G : Graph n)
    (seen : Finset (Fin n)) (z : ℤ)
    (hneutral : ((Finset.univ : Finset (Fin n)) \ seen).Nonempty) :
    let v := ((Finset.univ : Finset (Fin n)) \ seen).min' hneutral
    (∀ u ∈ (bfsStep G (⟨seen, [], z⟩ : BFSState n)).queue,
      u ∈ componentOf G v) ∧
    (∀ u ∈ (bfsStep G (⟨seen, [], z⟩ : BFSState n)).seen,
      u ∉ seen → u ∈ componentOf G v) := by
  let v := ((Finset.univ : Finset (Fin n)) \ seen).min' hneutral
  let children := newChildren G (insert v seen) v
  have hchildren : ∀ u ∈ children, u ∈ componentOf G v := by
    intro u hu
    exact adjacent_mem_componentOf (mem_componentOf_self G v)
      ((mem_newChildren_iff G (insert v seen) v u).mp hu).2
  have hv : v ∈ componentOf G v := mem_componentOf_self G v
  rw [bfsStep_queue_nil_of_nonempty G seen z hneutral]
  constructor
  · intro u hu
    exact hchildren u (by simpa [children] using! hu)
  · intro u hu hnot
    change u ∈ insert v seen ∪ children at hu
    rcases Finset.mem_union.mp hu with hu | hu
    · rcases Finset.mem_insert.mp hu with rfl | hu
      · exact hv
      · exact (hnot hu).elim
    · exact hchildren u hu

/-- The vertices processed between consecutive queue-empty times form one
literal connected component.  The root is the least unseen vertex selected by
the public BFS process at the starting boundary. -/
theorem queue_block_is_component {n : ℕ} (G : Graph n)
    {s t : ℕ} (hst : s < t) (ht : t ≤ n)
    (hqs : (explore G s).queue = [])
    (hqt : (explore G t).queue = [])
    (hinterior : ∀ u, s < u → u < t → (explore G u).queue ≠ []) :
    let seen := (explore G s).seen
    let hneutral : ((Finset.univ : Finset (Fin n)) \ seen).Nonempty :=
      (neutral_nonempty_iff seen).mpr
        (seen_ne_univ_of_queue_empty G (lt_of_lt_of_le hst ht) hqs)
    let v := ((Finset.univ : Finset (Fin n)) \ seen).min' hneutral
    processed G t \ processed G s = componentOf G v := by
  let seen := (explore G s).seen
  have hsn : s < n := lt_of_lt_of_le hst ht
  have hneutral : ((Finset.univ : Finset (Fin n)) \ seen).Nonempty :=
    (neutral_nonempty_iff seen).mpr
      (seen_ne_univ_of_queue_empty G hsn hqs)
  let v := ((Finset.univ : Finset (Fin n)) \ seen).min' hneutral
  let B := componentOf G v
  have hvnot : v ∉ seen :=
    (Finset.mem_sdiff.mp (Finset.min'_mem _ hneutral)).2
  have hclosed : ∀ u ∈ B, ∀ w, adj G u w → w ∈ B := by
    intro u hu w huw
    exact adjacent_mem_componentOf hu huw
  have hinside : ∀ j : ℕ, s < j → j ≤ t →
      (∀ u ∈ (explore G j).queue, u ∈ B) ∧
      (∀ u ∈ (explore G j).seen, u ∉ seen → u ∈ B) := by
    intro j
    induction j with
    | zero =>
        intro hs
        omega
    | succ j ih =>
        intro hsj hjt
        by_cases hjs : j = s
        · subst j
          rcases hstate : explore G s with ⟨seen', queue, z⟩
          simp only [hstate, BFSState.queue] at hqs
          subst queue
          have hseen' : seen' = seen := by
            change seen' = (explore G s).seen
            rw [hstate]
          subst seen'
          rw [explore_succ, hstate]
          exact root_step_inside G seen z hneutral
        · have hsj' : s < j := by omega
          have hjt' : j < t := by omega
          obtain ⟨hqueue, hseen⟩ := ih hsj' hjt'.le
          have hq : (explore G j).queue ≠ [] :=
            hinterior j hsj' hjt'
          rcases hstate : explore G j with ⟨seen', queue, z⟩
          cases queue with
          | nil => exact (hq (by simpa [hstate])).elim
          | cons head rest =>
              rw [explore_succ, hstate]
              apply active_step_inside G seen B seen' head rest z
              · intro u hu
                exact hqueue u (by simpa [hstate] using! hu)
              · intro u hu hnot
                exact hseen u (by simpa [hstate] using! hu) hnot
              · exact hclosed
  have hproc_seen_s : processed G s = seen := by
    simp [processed, seen, hqs]
  have hproc_seen_t : processed G t = (explore G t).seen := by
    simp [processed, hqt]
  have hroot_seen : v ∈ (explore G (s + 1)).seen := by
    rcases hstate : explore G s with ⟨seen', queue, z⟩
    simp only [hstate, BFSState.queue] at hqs
    subst queue
    have hseen' : seen' = seen := by
      change seen' = (explore G s).seen
      rw [hstate]
    subst seen'
    rw [explore_succ, hstate,
      bfsStep_queue_nil_of_nonempty G seen z hneutral]
    exact Finset.mem_union_left _ (Finset.mem_insert_self ..)
  have hroot_processed : v ∈ processed G t := by
    rw [hproc_seen_t]
    exact seen_monotone G (Nat.succ_le_of_lt hst) hroot_seen
  have hdisjoint : Disjoint B (processed G s) := by
    rcases component_dichotomy_of_queue_empty G s hqs
        (componentOf_mem_components G v) with hsubset | hdisjoint
    · exact (hvnot (hproc_seen_s ▸ hsubset (mem_componentOf_self G v))).elim
    · exact hdisjoint
  ext u
  constructor
  · intro hu
    have hu' := Finset.mem_sdiff.mp hu
    exact (hinside t hst le_rfl).2 u (hproc_seen_t ▸ hu'.1)
      (hproc_seen_s ▸ hu'.2)
  · intro hu
    exact Finset.mem_sdiff.mpr
      ⟨component_subset_processed_of_queue_empty G t hqt hroot_processed hu,
        fun hus => Finset.disjoint_left.mp hdisjoint hu hus⟩

/-- A consecutive mesh block has the cardinality of its actual connected
component, hence its length uses the public `n23` scaling exactly. -/
theorem meshRecord_interpolation_le_order {n : ℕ} (G : Graph n)
    (hn : 0 < n) {j : ℕ}
    (hrecord : meshRecord n j (continuousRawExploration G)) : j ≤ n := by
  by_contra hle
  have hnj : n < j := Nat.lt_of_not_ge hle
  have hstrict : meshValue n j (continuousRawExploration G) <
      meshValue n n (continuousRawExploration G) := by
    rcases hrecord with hzero | hrecord
    · omega
    · exact hrecord n hnj
  rw [meshValue_interpolation G hn j, meshValue_interpolation G hn n,
    walk_eq_at_order_of_le G hnj.le] at hstrict
  exact (lt_irrefl _) hstrict

/- No end record is appended after the last graph vertex.  Hence the exact
component identity applies to every completed block found by the public
discrete code on an exploration path. -/
end

end Erdos745.WrapUp.Proofs.Internal.W15_CRITICAL_FiniteBlocks


/-!
# Exhaustion of graph components by completed exploration blocks

The queue-empty boundaries from zero through the graph order partition the
processed vertices. Each consecutive pair gives one literal component. The
resulting finite bijection preserves cardinalities, including multiplicities
of equal-sized components, and hence the public rank thresholds.
-/

namespace Erdos745.WrapUp.Proofs.Internal.W15_CRITICAL_FiniteEnumeration

open Erdos745.WrapUp
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_Finite
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_Interpolation
open Erdos745.WrapUp.Proofs.Internal.W15_CRITICAL_Truncated
open Erdos745.WrapUp.Proofs.Internal.W15_CRITICAL_FiniteBlocks

noncomputable section
attribute [local instance] Classical.propDecidable

def queueBoundary {n : ℕ} (G : Graph n) (j : ℕ) : Prop :=
  j ≤ n ∧ (explore G j).queue = []

def queueBoundaries {n : ℕ} (G : Graph n) : Finset ℕ :=
  (Finset.range (n + 1)).filter (queueBoundary G)

def QueueBlock {n : ℕ} (G : Graph n) (z : ℕ × ℕ) : Prop :=
  z.1 < z.2 ∧ queueBoundary G z.1 ∧ queueBoundary G z.2 ∧
    ∀ u, z.1 < u → u < z.2 → ¬ queueBoundary G u

def queueBlocks {n : ℕ} (G : Graph n) : Finset (ℕ × ℕ) :=
  ((Finset.range (n + 1)).product (Finset.range (n + 1))).filter (QueueBlock G)

def blockComponent {n : ℕ} (G : Graph n) (z : ℕ × ℕ) : Finset (Fin n) :=
  processed G z.2 \ processed G z.1

theorem mem_queueBoundaries {n : ℕ} (G : Graph n) (j : ℕ) :
    j ∈ queueBoundaries G ↔ queueBoundary G j := by
  simp [queueBoundaries, queueBoundary]

theorem zero_queueBoundary {n : ℕ} (G : Graph n) : queueBoundary G 0 := by
  simp [queueBoundary, initialState]

theorem order_queueBoundary {n : ℕ} (G : Graph n) : queueBoundary G n := by
  exact ⟨le_rfl, queue_at_order_eq_nil G⟩

theorem mem_queueBlocks {n : ℕ} (G : Graph n) (z : ℕ × ℕ) :
    z ∈ queueBlocks G ↔ QueueBlock G z := by
  constructor
  · intro hz
    exact (Finset.mem_filter.mp hz).2
  · intro hz
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr ?_,
      Finset.mem_range.mpr ?_⟩, hz⟩
    · exact Nat.lt_succ_of_le hz.2.1.1
    · exact Nat.lt_succ_of_le hz.2.2.1.1

theorem queueBlock_iff_meshRecords {n : ℕ} (G : Graph n) (hn : 0 < n)
    (z : ℕ × ℕ) :
    QueueBlock G z ↔
      successiveMeshRecords n z.1 z.2 (continuousRawExploration G) := by
  constructor
  · intro hz
    apply (successiveMeshRecords_interpolation_iff G hn hz.2.2.1.1).mpr
    refine ⟨hz.1, hz.2.1.2, hz.2.2.1.2, ?_⟩
    intro u hsu hut hu
    exact hz.2.2.2 u hsu hut ⟨le_trans hut.le hz.2.2.1.1, hu⟩
  · intro hz
    have ht := meshRecord_interpolation_le_order G hn hz.2.2.1
    obtain ⟨hst, hqs, hqt, hinterior⟩ :=
      (successiveMeshRecords_interpolation_iff G hn ht).mp hz
    refine ⟨hst, ⟨le_trans hst.le ht, hqs⟩, ⟨ht, hqt⟩, ?_⟩
    intro u hsu hut hu
    exact hinterior u hsu hut hu.2

private theorem processed_boundary_mono {n : ℕ} (G : Graph n)
    {s t : ℕ} (hst : s ≤ t)
    (hs : queueBoundary G s) (ht : queueBoundary G t) :
    processed G s ⊆ processed G t := by
  simpa [processed, hs.2, ht.2] using! (seen_monotone G hst)

private theorem queueBlock_component {n : ℕ} (G : Graph n)
    {z : ℕ × ℕ} (hz : QueueBlock G z) :
    ∃ v : Fin n, blockComponent G z = componentOf G v := by
  have hcomponent := queue_block_is_component G hz.1 hz.2.2.1.1
    hz.2.1.2 hz.2.2.1.2
    (by
      intro u hsu hut hu
      exact hz.2.2.2 u hsu hut
        ⟨le_trans hut.le hz.2.2.1.1, hu⟩)
  let seen := (explore G z.1).seen
  have hslt : z.1 < n := lt_of_lt_of_le hz.1 hz.2.2.1.1
  have hnonempty : ((Finset.univ : Finset (Fin n)) \ seen).Nonempty :=
    (neutral_nonempty_iff seen).mpr (by
      intro hseen
      have hp : processed G z.1 = Finset.univ := by
        simp [processed, seen, hz.2.1.2, hseen]
      have hc := processed_card_of_le G z.1 hslt.le
      rw [hp] at hc
      simp at hc
      omega)
  let v := ((Finset.univ : Finset (Fin n)) \ seen).min' hnonempty
  exact ⟨v, hcomponent⟩

/-- Every time before the terminal boundary lies in one and only one
consecutive boundary interval. -/
private theorem bracket_time {n : ℕ} (G : Graph n) {k : ℕ} (hk : k < n) :
    ∃ s t, QueueBlock G (s, t) ∧ s ≤ k ∧ k < t := by
  let left := (queueBoundaries G).filter (fun j => j ≤ k)
  let right := (queueBoundaries G).filter (fun j => k < j)
  have hleft : left.Nonempty := ⟨0, by
    simp [left, mem_queueBoundaries, zero_queueBoundary G]⟩
  have hright : right.Nonempty := ⟨n, by
    simp [right, mem_queueBoundaries, order_queueBoundary G, hk]⟩
  let s := left.max' hleft
  let t := right.min' hright
  have hsleft : s ∈ left := Finset.max'_mem left hleft
  have htright : t ∈ right := Finset.min'_mem right hright
  have hs : queueBoundary G s :=
    (mem_queueBoundaries G s).mp (Finset.mem_filter.mp hsleft).1
  have ht : queueBoundary G t :=
    (mem_queueBoundaries G t).mp (Finset.mem_filter.mp htright).1
  have hsk : s ≤ k := (Finset.mem_filter.mp hsleft).2
  have hkt : k < t := (Finset.mem_filter.mp htright).2
  refine ⟨s, t, ⟨lt_of_le_of_lt hsk hkt, hs, ht, ?_⟩, hsk, hkt⟩
  intro u hsu hut hu
  by_cases huk : u ≤ k
  · have hul : u ∈ left := Finset.mem_filter.mpr
      ⟨(mem_queueBoundaries G u).mpr hu, huk⟩
    have hule := Finset.le_max' left u hul
    omega
  · have hkr : k < u := Nat.lt_of_not_ge huk
    have hur : u ∈ right := Finset.mem_filter.mpr
      ⟨(mem_queueBoundaries G u).mpr hu, hkr⟩
    have htle := Finset.min'_le right u hur
    omega

private theorem block_order {n : ℕ} (G : Graph n)
    {a b : ℕ × ℕ} (ha : QueueBlock G a) (hb : QueueBlock G b)
    (hab : a.1 < b.1) : a.2 ≤ b.1 := by
  by_contra h
  have hinside : b.1 < a.2 := Nat.lt_of_not_ge h
  exact ha.2.2.2 b.1 hab hinside hb.2.1

private theorem block_same_start {n : ℕ} (G : Graph n)
    {a b : ℕ × ℕ} (ha : QueueBlock G a) (hb : QueueBlock G b)
    (hstart : a.1 = b.1) : a = b := by
  have hend : a.2 = b.2 := by
    by_contra h
    rcases lt_or_gt_of_ne h with hlt | hgt
    · have hba : b.1 < a.2 := hstart ▸ ha.1
      exact hb.2.2.2 a.2 hba hlt ha.2.2.1
    · have hab : a.1 < b.2 := hstart.symm ▸ hb.1
      exact ha.2.2.2 b.2 hab hgt hb.2.2.1
  exact Prod.ext hstart hend

/-- Distinct completed blocks occupy disjoint sets of processed vertices. -/
private theorem block_disjoint {n : ℕ} (G : Graph n)
    {a b : ℕ × ℕ} (ha : QueueBlock G a) (hb : QueueBlock G b)
    (hab : a ≠ b) : Disjoint (blockComponent G a) (blockComponent G b) := by
  have hstart : a.1 ≠ b.1 := fun h => hab (block_same_start G ha hb h)
  rcases lt_or_gt_of_ne hstart with hlt | hgt
  · have horder := block_order G ha hb hlt
    have hsub := processed_boundary_mono G horder ha.2.2.1 hb.2.1
    apply Finset.disjoint_left.mpr
    intro v hva hvb
    exact (Finset.mem_sdiff.mp hvb).2
      (hsub (Finset.mem_sdiff.mp hva).1)
  · have horder := block_order G hb ha hgt
    have hsub := processed_boundary_mono G horder hb.2.2.1 ha.2.1
    apply Finset.disjoint_left.mpr
    intro v hva hvb
    exact (Finset.mem_sdiff.mp hva).2
      (hsub (Finset.mem_sdiff.mp hvb).1)

/-- Every vertex enters the processed set during a unique completed block. -/
theorem exists_block_containing_vertex {n : ℕ} (G : Graph n) (v : Fin n) :
    ∃ z ∈ queueBlocks G, v ∈ blockComponent G z := by
  let arrivals := (queueBoundaries G).filter (fun t => v ∈ processed G t)
  have harrivals : arrivals.Nonempty := ⟨n, by
    simp [arrivals, mem_queueBoundaries, order_queueBoundary G,
      processed_at_order_eq_univ G]⟩
  let t := arrivals.min' harrivals
  have htmem : t ∈ arrivals := Finset.min'_mem arrivals harrivals
  have htboundary : queueBoundary G t :=
    (mem_queueBoundaries G t).mp (Finset.mem_filter.mp htmem).1
  have hvt : v ∈ processed G t := (Finset.mem_filter.mp htmem).2
  have htpos : 0 < t := by
    by_contra h
    have ht0 : t = 0 := by omega
    rw [ht0] at hvt
    simp [processed, initialState] at hvt
  have htn : t ≤ n := htboundary.1
  have hk : t - 1 < n := by omega
  obtain ⟨s, u, hblock, hsk, hku⟩ :=
    bracket_time G hk
  have hu : u = t := by
    have htu : t ≤ u := by omega
    have hut : u ≤ t := by
      have hbetween : t < u → False := by
        intro htu'
        have hst : s < t := by omega
        exact hblock.2.2.2 t hst htu' htboundary
      by_contra h
      exact hbetween (Nat.lt_of_not_ge h)
    omega
  subst u
  have hvs : v ∉ processed G s := by
    intro hvs
    have hsarrivals : s ∈ arrivals := Finset.mem_filter.mpr
      ⟨(mem_queueBoundaries G s).mpr hblock.2.1, hvs⟩
    have hmin : t ≤ s := Finset.min'_le arrivals s hsarrivals
    omega
  exact ⟨(s, t), (mem_queueBlocks G _).mpr hblock,
    Finset.mem_sdiff.mpr ⟨hvt, hvs⟩⟩

/-- The processed-vertex increment labels completed blocks injectively. -/
theorem blockComponent_injective {n : ℕ} (G : Graph n)
    {a b : ℕ × ℕ} (ha : a ∈ queueBlocks G) (hb : b ∈ queueBlocks G)
    (heq : blockComponent G a = blockComponent G b) : a = b := by
  by_contra hab
  have hne : (blockComponent G a).Nonempty := by
    obtain ⟨r, hr⟩ := queueBlock_component G ((mem_queueBlocks G a).mp ha)
    rw [hr]
    exact ⟨r, mem_componentOf_self G r⟩
  obtain ⟨v, hv⟩ := hne
  have hdis := block_disjoint G ((mem_queueBlocks G a).mp ha)
    ((mem_queueBlocks G b).mp hb) hab
  exact (Finset.disjoint_left.mp hdis hv) (heq ▸ hv)

/-- The blocks are in bijection with the literal public component family. -/
theorem component_blocks_bijection {n : ℕ} (G : Graph n) :
    (queueBlocks G).image (blockComponent G) = components G := by
  ext S
  constructor
  · intro hS
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hS
    obtain ⟨v, hv⟩ := queueBlock_component G ((mem_queueBlocks G z).mp hz)
    rw [hv]
    exact componentOf_mem_components G v
  · intro hS
    obtain ⟨v, rfl⟩ := (mem_components_iff G _).mp hS
    obtain ⟨z, hz, hvz⟩ := exists_block_containing_vertex G v
    obtain ⟨w, hzw⟩ := queueBlock_component G ((mem_queueBlocks G z).mp hz)
    have hr : reach G w v := (mem_componentOf_iff G w v).mp (hzw ▸ hvz)
    refine Finset.mem_image.mpr ⟨z, hz, ?_⟩
    rw [hzw]
    exact componentOf_eq_of_reach hr

theorem queueBlocks_countGE {n : ℕ} (G : Graph n) (h : ℕ) :
    ((queueBlocks G).filter (fun z => h ≤ (blockComponent G z).card)).card =
      countGE G h := by
  unfold countGE
  apply Finset.card_bij (fun z _ => blockComponent G z)
  · intro z hz
    apply Finset.mem_filter.mpr
    refine ⟨?_, (Finset.mem_filter.mp hz).2⟩
    obtain ⟨v, hv⟩ := queueBlock_component G
      ((mem_queueBlocks G z).mp (Finset.mem_filter.mp hz).1)
    rw [hv]
    exact componentOf_mem_components G v
  · intro a ha b hb heq
    exact blockComponent_injective G
      (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp hb).1 heq
  · intro S hS
    have hcomp : S ∈ components G := (Finset.mem_filter.mp hS).1
    rw [← component_blocks_bijection G] at hcomp
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hcomp
    exact ⟨z, Finset.mem_filter.mpr
      ⟨hz, (Finset.mem_filter.mp hS).2⟩, rfl⟩

/-- A completed block contains exactly the vertices processed between its
two boundary times. -/
theorem blockComponent_card {n : ℕ} (G : Graph n) {z : ℕ × ℕ}
    (hz : QueueBlock G z) :
    (blockComponent G z).card = z.2 - z.1 := by
  have hsub := processed_boundary_mono G hz.1.le hz.2.1 hz.2.2.1
  have hcard : (blockComponent G z).card =
      (processed G z.2).card - (processed G z.1).card := by
    simp [blockComponent, Finset.card_sdiff,
      Finset.inter_eq_left.mpr hsub]
  rw [hcard, processed_card_of_le G z.2 hz.2.2.1.1,
    processed_card_of_le G z.1 hz.2.1.1]

theorem meshBlockLength_eq_blockComponent_card {n : ℕ} (G : Graph n)
    {z : ℕ × ℕ} (hz : QueueBlock G z) :
    meshBlockLength n z.1 z.2 =
      ((blockComponent G z).card : ℝ) / n23 n := by
  rw [blockComponent_card G hz, Nat.cast_sub hz.1.le]
  rfl

/- The public one-based rank is the finite supremum of threshold values
supported by at least that many completed BFS blocks. -/
end

end Erdos745.WrapUp.Proofs.Internal.W15_CRITICAL_FiniteEnumeration


/-!
# Finite support and exact thresholds for the countable discrete rank code

The public discrete code indexes every pair of mesh times by `Nat.unpair`.
On a BFS path its positive candidates are supported on the finite family of
completed queue blocks.  The injection definition of rank therefore has an
exact cardinality threshold description, including ties and zero padding.
-/

namespace Erdos745.WrapUp.Proofs.Internal.W15_CRITICAL_FiniteRank

open Erdos745.WrapUp
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_Interpolation
open Erdos745.WrapUp.Proofs.Internal.W15_CRITICAL_Truncated
open Erdos745.WrapUp.Proofs.Internal.W15_CRITICAL_FiniteBlocks
open Erdos745.WrapUp.Proofs.Internal.W15_CRITICAL_FiniteEnumeration
open scoped ENNReal

noncomputable section
attribute [local instance] Classical.propDecidable

/-- An injection code has no positive contribution from indices outside its
finite support. -/
private theorem rankFromCandidates_eq_finiteSup
    (v : ℕ → BrownianPath → ENNReal) (p : BrownianPath)
    (s : Finset ℕ) (hs : ∀ m ∉ s, v m p = 0)
    (i : ℕ) (hi : i ≠ 0) :
    rankFromCandidates v i p =
      (Finset.univ : Finset (Fin i ↪ s)).sup
        (fun e => ⨅ j : Fin i, v (e j).1 p) := by
  have hformula : rankFromCandidates v i p =
      ⨆ e : Fin i ↪ s, ⨅ j : Fin i, v (e j).1 p := by
    unfold rankFromCandidates
    simp only [hi, if_false]
    apply le_antisymm
    · apply iSup_le
      intro f
      by_cases hf : Function.Injective f
      · by_cases hr : ∀ j : Fin i, f j ∈ s
        · let e : Fin i ↪ s :=
            ⟨fun j => ⟨f j, hr j⟩, by
              intro j k hjk
              exact hf (Subtype.mk.inj hjk)⟩
          simpa only [hf, if_true, e] using!
            (le_iSup_of_le e (le_refl (⨅ j : Fin i, v (f j) p)))
        · obtain ⟨j, hj⟩ := not_forall.mp hr
          have hzero : (⨅ k : Fin i, v (f k) p) = 0 := by
            apply bot_unique
            exact (iInf_le _ j).trans (hs (f j) hj).le
          simp [hf, hzero]
      · simp [hf]
    · apply iSup_le
      intro e
      let f : Fin i → ℕ := fun j => (e j).1
      have hf : Function.Injective f := by
        intro j k hjk
        apply e.injective
        exact Subtype.ext hjk
      have hterm : (⨅ j : Fin i, v (e j).1 p) ≤
          (if Function.Injective f then ⨅ j : Fin i, v (f j) p else 0) := by
        simp [hf, f]
      exact le_iSup_of_le f hterm
  rw [hformula]
  simp [Finset.sup_eq_iSup]

/-- At a positive threshold, the countably coded rank is exactly the number
of supported candidates meeting that threshold. -/
theorem rankFromCandidates_threshold_of_finite_support
    (v : ℕ → BrownianPath → ENNReal) (p : BrownianPath)
    (s : Finset ℕ) (hs : ∀ m ∉ s, v m p = 0)
    (i : ℕ) (hi : 0 < i) (x : ENNReal) (hx : 0 < x) :
    x ≤ rankFromCandidates v i p ↔
      i ≤ (s.filter (fun m => x ≤ v m p)).card := by
  rw [rankFromCandidates_eq_finiteSup v p s hs i (Nat.ne_of_gt hi)]
  constructor
  · intro h
    obtain ⟨e, _, he⟩ := (Finset.le_sup_iff hx).mp h
    let f : Fin i ↪ ℕ := e.trans (Function.Embedding.subtype _)
    have hf : ∀ j : Fin i, f j ∈ s.filter (fun m => x ≤ v m p) := by
      intro j
      apply Finset.mem_filter.mpr
      exact ⟨(e j).2, he.trans (iInf_le _ j)⟩
    have hcard : i ≤ Fintype.card (s.filter (fun m => x ≤ v m p)) := by
      simpa using! Fintype.card_le_of_injective
        (fun j : Fin i => (⟨f j, hf j⟩ : s.filter (fun m => x ≤ v m p)))
        (by intro j k hjk; exact f.injective (Subtype.mk.inj hjk))
    simpa using! hcard
  · intro h
    obtain ⟨f, hf⟩ :=
      Function.Embedding.exists_of_card_le_finset
        (show Fintype.card (Fin i) ≤
          (s.filter (fun m => x ≤ v m p)).card by simpa using! h)
    have hfs : ∀ j : Fin i, f j ∈ s := by
      intro j
      exact (Finset.mem_filter.mp (hf ⟨j, rfl⟩)).1
    let e : Fin i ↪ s :=
      ⟨fun j => ⟨f j, hfs j⟩, by
        intro j k hjk
        exact f.injective (Subtype.mk.inj hjk)⟩
    have hval : x ≤ ⨅ j : Fin i, v (e j).1 p := by
      apply le_iInf
      intro j
      exact (Finset.mem_filter.mp (hf ⟨j, rfl⟩)).2
    exact hval.trans (Finset.le_sup
      (f := fun e : Fin i ↪ s => ⨅ j : Fin i, v (e j).1 p)
      (Finset.mem_univ e))

def blockIndex (z : ℕ × ℕ) : ℕ := Nat.pair z.1 z.2

theorem blockIndex_injective : Function.Injective blockIndex := by
  intro z w h
  have h' := congrArg Nat.unpair h
  simpa [blockIndex, Nat.unpair_pair] using! h'

def codedBlockSupport {n : ℕ} (G : Graph n) : Finset ℕ :=
  (queueBlocks G).image blockIndex

def KeptBlock {n : ℕ} (G : Graph n) (a T U : ℝ) (z : ℕ × ℕ) : Prop :=
  z ∈ queueBlocks G ∧ z.2 ≤ ⌊U * n23 n⌋₊ + 1 ∧
    (meshTime n z.1 : ℝ) < T ∧
    (meshTime n z.2 : ℝ) < U ∧
    a < meshBlockLength n z.1 z.2

def keptBlocks {n : ℕ} (G : Graph n) (a T U : ℝ) : Finset (ℕ × ℕ) :=
  (queueBlocks G).filter fun z =>
    z.2 ≤ ⌊U * n23 n⌋₊ + 1 ∧
    (meshTime n z.1 : ℝ) < T ∧
    (meshTime n z.2 : ℝ) < U ∧
    a < meshBlockLength n z.1 z.2

theorem mem_keptBlocks {n : ℕ} (G : Graph n) (a T U : ℝ)
    (z : ℕ × ℕ) : z ∈ keptBlocks G a T U ↔ KeptBlock G a T U z := by
  simp [keptBlocks, KeptBlock]

theorem discreteKeptLength_of_queueBlock {n : ℕ} (G : Graph n)
    (hn : 0 < n) (a T U : ℝ) {z : ℕ × ℕ}
    (hz : z ∈ queueBlocks G) :
    discreteKeptLength n a T U z (continuousRawExploration G) =
      if z ∈ keptBlocks G a T U then
        ENNReal.ofReal (meshBlockLength n z.1 z.2) else 0 := by
  have hrec := (queueBlock_iff_meshRecords G hn z).mp
    ((mem_queueBlocks G z).mp hz)
  simp [discreteKeptLength, keptBlocks, hz, hrec]

theorem discreteKeptLength_zero_outside_support {n : ℕ} (G : Graph n)
    (hn : 0 < n) (a T U : ℝ) (m : ℕ)
    (hm : m ∉ codedBlockSupport G) :
    discreteKeptLength n a T U (pairCode m)
      (continuousRawExploration G) = 0 := by
  let z := pairCode m
  have hz : z ∉ queueBlocks G := by
    intro hz
    apply hm
    exact Finset.mem_image.mpr ⟨z, hz, by
      simp [z, blockIndex, pairCode, Nat.pair_unpair]⟩
  have hrec : ¬ successiveMeshRecords n z.1 z.2
      (continuousRawExploration G) := by
    intro h
    exact hz ((mem_queueBlocks G z).mpr
      ((queueBlock_iff_meshRecords G hn z).mpr h))
  simp [discreteKeptLength, z, hrec]

/-- The positive-value count in the countable code is literally the finite
count of kept BFS blocks. -/
theorem discrete_candidates_count {n : ℕ} (G : Graph n)
    (hn : 0 < n) (a T U : ℝ) (x : ENNReal) (hx : 0 < x) :
    ((codedBlockSupport G).filter (fun m =>
      x ≤ discreteKeptLength n a T U (pairCode m)
        (continuousRawExploration G))).card =
    ((keptBlocks G a T U).filter (fun z =>
      x ≤ ENNReal.ofReal (meshBlockLength n z.1 z.2))).card := by
  have heq :
      (codedBlockSupport G).filter (fun m =>
        x ≤ discreteKeptLength n a T U (pairCode m)
          (continuousRawExploration G)) =
      ((keptBlocks G a T U).filter (fun z =>
        x ≤ ENNReal.ofReal (meshBlockLength n z.1 z.2))).image blockIndex := by
    ext m
    constructor
    · intro hm
      obtain ⟨z, hz, hmz⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hm).1
      have hpair : pairCode m = z := by
        rw [← hmz]
        simp [pairCode, blockIndex, Nat.unpair_pair]
      have hv := (Finset.mem_filter.mp hm).2
      rw [hpair, discreteKeptLength_of_queueBlock G hn a T U hz] at hv
      have hkept : z ∈ keptBlocks G a T U := by
        by_contra h
        simp [h] at hv
        exact (ne_of_gt hx) hv
      exact Finset.mem_image.mpr ⟨z,
        Finset.mem_filter.mpr ⟨hkept, by simpa [hkept] using! hv⟩, hmz⟩
    · intro hm
      obtain ⟨z, hz, hmz⟩ := Finset.mem_image.mp hm
      have hkeep := (Finset.mem_filter.mp hz).1
      have hblock := (Finset.mem_filter.mp hkeep).1
      apply Finset.mem_filter.mpr
      constructor
      · exact Finset.mem_image.mpr ⟨z, hblock, hmz⟩
      · have hpair : pairCode m = z := by
          rw [← hmz]
          simp [pairCode, blockIndex, Nat.unpair_pair]
        rw [hpair, discreteKeptLength_of_queueBlock G hn a T U hblock]
        simpa [hkeep] using! (Finset.mem_filter.mp hz).2
  rw [heq]
  exact (Finset.card_image_iff.mpr fun z _ w _ h =>
    blockIndex_injective h)

/-- Exact threshold interface between the public countable discrete rank map
and the finite kept component blocks. -/
theorem discreteTruncatedRank_threshold {n : ℕ} (G : Graph n)
    (hn : 0 < n) (a T U : ℝ) (i : ℕ) (hi : 0 < i)
    (x : ENNReal) (hx : 0 < x) :
    x ≤ rankFromCandidates
      (fun m => discreteKeptLength n a T U (pairCode m)) i
      (continuousRawExploration G) ↔
    i ≤ ((keptBlocks G a T U).filter (fun z =>
      x ≤ ENNReal.ofReal (meshBlockLength n z.1 z.2))).card := by
  rw [rankFromCandidates_threshold_of_finite_support
    (fun m => discreteKeptLength n a T U (pairCode m))
    (continuousRawExploration G) (codedBlockSupport G)
    (discreteKeptLength_zero_outside_support G hn a T U) i hi x hx]
  rw [discrete_candidates_count G hn a T U x hx]

end

end Erdos745.WrapUp.Proofs.Internal.W15_CRITICAL_FiniteRank
