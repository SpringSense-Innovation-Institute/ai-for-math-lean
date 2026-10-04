module

import all Mathlib.Basic.Real.Basic
public import Erdos448.dependencies.«DP-MERTENS».stage6.FrozenTaskContracts

public section

set_option backward.isDefEq.respectTransparency false

open Filter Set Asymptotics
open scoped Topology

namespace Erdos448.DPMertens.Tasks.MertFinal

noncomputable section

open Erdos448.DPMertens
open Erdos448.DPMertens.Lowering

@[expose] def strictError (weak : WeakProductOutput corr child) (x : ℝ) : ℝ :=
  (1 + weak.relativeError x) * (endpointFactor x)⁻¹ - 1

lemma endpointInverseEstimates (ends : EndpointOutput) {x : ℝ} (hx : 2 ≤ x) :
    0 ≤ (endpointFactor x)⁻¹ - 1 ∧
      (endpointFactor x)⁻¹ ≤ 2 ∧
      |(endpointFactor x)⁻¹ - 1| ≤ 1 / (x - 1) := by
  rcases ends.endpoint.1 x hx with ⟨hfactor, -, hone, hupp⟩
  have hxpos : 0 < x := by linarith
  have hxone : 1 < x := by linarith
  have hxsub : 0 < x - 1 := by linarith
  have hxinvlt : x⁻¹ < 1 := (inv_lt_one₀ hxpos).2 hxone
  have hdenpos : 0 < 1 - x⁻¹ := sub_pos.2 hxinvlt
  have hxinvhalf : x⁻¹ ≤ (2 : ℝ)⁻¹ :=
    (inv_le_inv₀ hxpos (by norm_num)).2 hx
  have hdenhalf : (2 : ℝ)⁻¹ ≤ 1 - x⁻¹ := by linarith
  have hdeninv : (1 - x⁻¹)⁻¹ ≤ ((2 : ℝ)⁻¹)⁻¹ :=
    (inv_le_inv₀ hdenpos (by positivity)).2 hdenhalf
  have htwo : (endpointFactor x)⁻¹ ≤ 2 := by
    norm_num at hdeninv ⊢
    exact hupp.trans hdeninv
  have hid : (1 - x⁻¹)⁻¹ - 1 = 1 / (x - 1) := by
    field_simp [ne_of_gt hxpos, ne_of_gt hxsub, ne_of_gt hdenpos]
    <;> ring
  have hdelta : (endpointFactor x)⁻¹ - 1 ≤ 1 / (x - 1) := by
    rw [← hid]
    linarith
  have hdeltaNonneg : 0 ≤ (endpointFactor x)⁻¹ - 1 := sub_nonneg.2 hone
  have habs : |(endpointFactor x)⁻¹ - 1| = (endpointFactor x)⁻¹ - 1 :=
    abs_of_nonneg hdeltaNonneg
  exact ⟨hdeltaNonneg, htwo, by simpa only [habs] using hdelta⟩

lemma strictErrorBound (weak : WeakProductOutput corr child)
    (ends : EndpointOutput) {x : ℝ} (hx : 2 ≤ x) :
    |strictError weak x| ≤
      2 * |weak.relativeError x| + 1 / (x - 1) := by
  rcases endpointInverseEstimates ends hx with ⟨hdelta, hetwo, hdeltabound⟩
  have hepos : 0 < (endpointFactor x)⁻¹ := by
    exact inv_pos.2 (ends.endpoint.1 x hx).1
  have hrewrite : strictError weak x =
      weak.relativeError x * (endpointFactor x)⁻¹ + ((endpointFactor x)⁻¹ - 1) := by
    simp only [strictError]
    ring
  rw [hrewrite]
  calc
    |weak.relativeError x * (endpointFactor x)⁻¹ + ((endpointFactor x)⁻¹ - 1)|
        ≤ |weak.relativeError x * (endpointFactor x)⁻¹| +
            |(endpointFactor x)⁻¹ - 1| := abs_add_le _ _
    _ = |weak.relativeError x| * (endpointFactor x)⁻¹ +
          |(endpointFactor x)⁻¹ - 1| := by rw [abs_mul, abs_of_pos hepos]
    _ ≤ 2 * |weak.relativeError x| + 1 / (x - 1) := by
      have hmul : |weak.relativeError x| * (endpointFactor x)⁻¹ ≤
          2 * |weak.relativeError x| := by
        calc
          |weak.relativeError x| * (endpointFactor x)⁻¹ ≤
              |weak.relativeError x| * 2 :=
            mul_le_mul_of_nonneg_left hetwo (abs_nonneg _)
          _ = 2 * |weak.relativeError x| := mul_comm _ _
      exact add_le_add hmul hdeltabound

lemma strictExact (weak : WeakProductOutput corr child)
    (ends : EndpointOutput) :
    ∀ x : ℝ, 2 ≤ x →
      qLT x = mertensMain x * (1 + strictError weak x) := by
  intro x hx
  rcases ends.endpoint.1 x hx with ⟨hfactor, hproduct, -, -⟩
  have htransfer : qLT x = qLE x * (endpointFactor x)⁻¹ := by
    rw [hproduct]
    field_simp [ne_of_gt hfactor]
  rw [htransfer, weak.exact_relative x hx]
  simp only [strictError]
  ring

lemma strictRate (weak : WeakProductOutput corr child)
    (ends : EndpointOutput) :
    ReciprocalLogRate (strictError weak) (2 * weak.CRelative + 1)
      (max weak.XRelative 2) := by
  rcases weak.relative_rate with ⟨hC, hXtwo, hrate⟩
  refine ⟨by linarith, le_max_right _ _, ?_⟩
  intro x hx
  have hxX : weak.XRelative ≤ x := (le_max_left _ _).trans hx
  have hxtwo : 2 ≤ x := (le_max_right _ _).trans hx
  have hxpos : 0 < x := by linarith
  have hxsub : 0 < x - 1 := by linarith
  have hlogpos : 0 < Real.log x := Real.log_pos (by linarith)
  have htail : 1 / (x - 1) ≤ 1 / Real.log x :=
    one_div_le_one_div_of_le hlogpos (Real.log_le_sub_one_of_pos hxpos)
  calc
    |strictError weak x| ≤
        2 * |weak.relativeError x| + 1 / (x - 1) := strictErrorBound weak ends hxtwo
    _ ≤ 2 * (weak.CRelative / Real.log x) + 1 / Real.log x := by
      gcongr
      exact hrate x hxX
    _ = (2 * weak.CRelative + 1) / Real.log x := by ring

lemma strictAsymptotic (weak : WeakProductOutput corr child)
    (ends : EndpointOutput) : StrictMertensAsymptotic := by
  have hend :
      (fun x : ℝ ↦ (endpointFactor x)⁻¹) ~[atTop] (fun _ : ℝ ↦ (1 : ℝ)) := by
    change (fun x : ℝ ↦ (endpointFactor x)⁻¹) ~[atTop]
      (Function.const ℝ (1 : ℝ))
    exact (isEquivalent_const_iff_tendsto one_ne_zero).2 ends.endpoint.2
  have hmul := weak.asymptotic.mul hend
  have htransfer :
      (fun x : ℝ ↦ qLE x * (endpointFactor x)⁻¹) =ᶠ[atTop] qLT := by
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
    rcases ends.endpoint.1 x hx with ⟨hfactor, hproduct, -, -⟩
    rw [hproduct]
    field_simp [ne_of_gt hfactor]
  exact hmul.congr_left htransfer |>.congr_right
    (Filter.Eventually.of_forall (fun x ↦ by simp))

lemma mainTermPos {x : ℝ} (hx : 2 ≤ x) : 0 < mertensMain x := by
  exact div_pos (Real.exp_pos _) (Real.log_pos (by linarith))

lemma intervalComparison (ends : EndpointOutput)
    (hstrict : StrictMertensAsymptotic) : IntervalComparisonContract := by
  rcases hstrict.exists_eq_mul with ⟨phi, hphi, hq⟩
  have hphiBounds : ∀ᶠ x : ℝ in atTop,
      (1 / 2 : ℝ) ≤ phi x ∧ phi x ≤ 2 := by
    exact hphi.eventually (Icc_mem_nhds (by norm_num) (by norm_num))
  have hall : ∀ᶠ x : ℝ in atTop,
      2 ≤ x ∧ ((1 / 2 : ℝ) ≤ phi x ∧ phi x ≤ 2) ∧
        qLT x = phi x * mertensMain x :=
    (eventually_ge_atTop (2 : ℝ)).and (hphiBounds.and hq)
  rcases eventually_atTop.1 hall with ⟨X, hX⟩
  refine ⟨max X 2, 1 / 4, 4, le_max_right _ _, by norm_num, by norm_num, ?_⟩
  intro A B hXA hAB
  have hAall := hX A ((le_max_left X 2).trans hXA)
  have hXB : max X 2 ≤ B := hXA.trans (le_of_lt hAB)
  have hBall := hX B ((le_max_left X 2).trans hXB)
  rcases hAall with ⟨hA2, hphiA, hqA⟩
  rcases hBall with ⟨hB2, hphiB, hqB⟩
  have hmA : 0 < mertensMain A := mainTermPos hA2
  have hmB : 0 < mertensMain B := mainTermPos hB2
  have hAlo : (1 / 2 : ℝ) * mertensMain A ≤ qLT A := by
    rw [hqA]
    exact mul_le_mul_of_nonneg_right hphiA.1 hmA.le
  have hAhi : qLT A ≤ 2 * mertensMain A := by
    rw [hqA]
    exact mul_le_mul_of_nonneg_right hphiA.2 hmA.le
  have hBlo : (1 / 2 : ℝ) * mertensMain B ≤ qLT B := by
    rw [hqB]
    exact mul_le_mul_of_nonneg_right hphiB.1 hmB.le
  have hBhi : qLT B ≤ 2 * mertensMain B := by
    rw [hqB]
    exact mul_le_mul_of_nonneg_right hphiB.2 hmB.le
  have hqApos : 0 < qLT A :=
    (mul_pos (by norm_num) hmA).trans_le hAlo
  have hqBpos : 0 < qLT B :=
    (mul_pos (by norm_num) hmB).trans_le hBlo
  have hlower :
      ((1 / 2 : ℝ) * mertensMain B) / (2 * mertensMain A) ≤ qLT B / qLT A :=
    div_le_div₀ hqBpos.le hBlo hqApos hAhi
  have hupper :
      qLT B / qLT A ≤ (2 * mertensMain B) / ((1 / 2 : ℝ) * mertensMain A) :=
    div_le_div₀ (mul_nonneg (by norm_num) hmB.le) hBhi
      (mul_pos (by norm_num) hmA) hAlo
  have hlogA : 0 < Real.log A := Real.log_pos (by linarith)
  have hlogB : 0 < Real.log B := Real.log_pos (by linarith)
  have hmainRatio : mertensMain B / mertensMain A = Real.log A / Real.log B := by
    simp only [mertensMain]
    field_simp [ne_of_gt hlogA, ne_of_gt hlogB, ne_of_gt (Real.exp_pos _)]
    <;> ring
  have hlowerId :
      ((1 / 2 : ℝ) * mertensMain B) / (2 * mertensMain A) =
        (1 / 4 : ℝ) * (Real.log A / Real.log B) := by
    calc
      ((1 / 2 : ℝ) * mertensMain B) / (2 * mertensMain A) =
          (1 / 4 : ℝ) * (mertensMain B / mertensMain A) := by
            field_simp [ne_of_gt hmA]
            <;> ring
      _ = (1 / 4 : ℝ) * (Real.log A / Real.log B) := by rw [hmainRatio]
  have hupperId :
      (2 * mertensMain B) / ((1 / 2 : ℝ) * mertensMain A) =
        4 * (Real.log A / Real.log B) := by
    calc
      (2 * mertensMain B) / ((1 / 2 : ℝ) * mertensMain A) =
          4 * (mertensMain B / mertensMain A) := by
            field_simp [ne_of_gt hmA]
            <;> ring
      _ = 4 * (Real.log A / Real.log B) := by rw [hmainRatio]
  rw [(ends.interval A B hA2 hAB).1]
  exact ⟨hlowerId ▸ hlower, hupperId ▸ hupper⟩

/-- P-MERT-07/08 and FT-MERTENS, conditional on the two frozen local providers. -/
@[expose] def finalOutput (corr : CorrectionOutput) (child : SumAssemblyOutput corr.H)
    (weak : WeakProductOutput corr child) (ends : EndpointOutput) :
    FinalOutput corr child weak ends := by
  let hstrict : StrictMertensAsymptotic := strictAsymptotic weak ends
  exact
    { strictRelativeError := strictError weak
      CStrict := 2 * weak.CRelative + 1
      XStrict := max weak.XRelative 2
      strict_exact := strictExact weak ends
      strict_rate := strictRate weak ends
      strict_asymptotic := hstrict
      X_M := (intervalComparison ends hstrict).choose
      c_M_minus := (intervalComparison ends hstrict).choose_spec.choose
      c_M_plus := (intervalComparison ends hstrict).choose_spec.choose_spec.choose
      X_M_ge_two := (intervalComparison ends hstrict).choose_spec.choose_spec.choose_spec.1
      c_M_minus_pos := (intervalComparison ends hstrict).choose_spec.choose_spec.choose_spec.2.1
      c_M_plus_pos := (intervalComparison ends hstrict).choose_spec.choose_spec.choose_spec.2.2.1
      interval_comparison :=
        (intervalComparison ends hstrict).choose_spec.choose_spec.choose_spec.2.2.2 }

/-- The exact EXT-002 surface consumed by the parent P-007. -/
@[expose] def parentEXT002Interface (corr : CorrectionOutput) (child : SumAssemblyOutput corr.H)
    (weak : WeakProductOutput corr child) (ends : EndpointOutput) :
    ParentEXT002Interface := by
  let out := finalOutput corr child weak ends
  exact
    { strict_asymptotic := out.strict_asymptotic
      X_M := out.X_M
      c_M_minus := out.c_M_minus
      c_M_plus := out.c_M_plus
      X_M_ge_two := out.X_M_ge_two
      c_M_minus_pos := out.c_M_minus_pos
      c_M_plus_pos := out.c_M_plus_pos
      interval_comparison := out.interval_comparison }

/-- Exact frozen final target, preserving the dependent weak-product package. -/
@[expose] def result : TASK_MERT_FINAL_Target := by
  intro hWeak hEndpoints
  exact
    { corr := hWeak.corr
      child := hWeak.child
      weak := hWeak.weak
      ends := hEndpoints
      final := finalOutput hWeak.corr hWeak.child hWeak.weak hEndpoints }

end

end Erdos448.DPMertens.Tasks.MertFinal

#print axioms Erdos448.DPMertens.Tasks.MertFinal.result
