module

public import Erdos745.WrapUp.Proofs.Internal.Linked.W15_Base
public import Erdos745.WrapUp.Proofs.Internal.Linked.W14_Horizon
public import Erdos745.WrapUp.Proofs.Internal.Linked.W13_Law
public import Erdos745.WrapUp.Proofs.Internal.Linked.W13_Excursions

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local simp] Pi.div_def Pi.mul_def Pi.add_def Pi.sub_def Pi.neg_def Pi.inv_def Function.comp_def Pi.pow_def Pi.smul_def Real.rpow_eq_pow

@[expose] public section


/-!
# Deterministic record geometry of a finite BFS exploration

All statements concern the actual polygonal exploration and completed queue
blocks.  The drift is removed exactly once when the reflected limit is used.
-/

namespace Erdos745.WrapUp.Proofs.Internal.W15_CRITICAL_RecordGeometry

open Erdos745.WrapUp
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_Finite
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_Interpolation
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_CriticalBudget
open Erdos745.WrapUp.Proofs.Internal.W15_CRITICAL_Truncated
open Erdos745.WrapUp.Proofs.Internal.W15_CRITICAL_FiniteBlocks
open Erdos745.WrapUp.Proofs.Internal.W13_BROWNIAN_Ranks
open Filter Set
open scoped Topology

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local simp] Pi.div_def Pi.mul_def Pi.add_def Pi.sub_def Pi.neg_def Pi.inv_def Function.comp_def

def meshStep (n : ℕ) : ℝ := 1 / n23 n
def recordDrop (n : ℕ) : ℝ := 1 / n13 n

theorem n23_tendsto_atTop : Tendsto n23 atTop atTop := by
  exact (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 3)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))

theorem meshStep_tendsto_zero : Tendsto meshStep atTop (𝓝 0) := by
  change Tendsto (fun n => 1 / n23 n) atTop (𝓝 0)
  simpa only [one_div, Pi.inv_apply] using!
    n23_tendsto_atTop.inv_tendsto_atTop

theorem recordDrop_tendsto_zero : Tendsto recordDrop atTop (𝓝 0) := by
  change Tendsto (fun n => 1 / n13 n) atTop (𝓝 0)
  simpa only [one_div, Pi.inv_apply] using!
    n13_tendsto_atTop.inv_tendsto_atTop

theorem meshStep_comp_tendsto_zero {ι : Type*} {l : Filter ι}
    {ns : ι → ℕ} (hns : Tendsto ns l atTop) :
    Tendsto (fun j => meshStep (ns j)) l (𝓝 0) :=
  meshStep_tendsto_zero.comp hns

theorem recordDrop_comp_tendsto_zero {ι : Type*} {l : Filter ι}
    {ns : ι → ℕ} (hns : Tendsto ns l atTop) :
    Tendsto (fun j => recordDrop (ns j)) l (𝓝 0) :=
  recordDrop_tendsto_zero.comp hns

theorem meshStep_pos (n : ℕ) (hn : 0 < n) : 0 < meshStep n := by
  exact one_div_pos.mpr (n23_pos n hn)

def reflectedCenteredPath (lam : ℝ) (p : BrownianPath) : BrownianPath where
  toFun t := reflected (centerPath p lam) lam t
  continuous_toFun :=
    (continuous_reflected_joint lam).comp
      (continuous_const.prodMk continuous_id)

@[simp] theorem reflectedCenteredPath_apply (lam : ℝ) (p : BrownianPath)
    (t : NNReal) :
    reflectedCenteredPath lam p t =
      p t - sInf (p '' Icc 0 t) := by
  exact reflected_centerPath p lam t

theorem continuous_reflectedCenteredPath (lam : ℝ) :
    Continuous (reflectedCenteredPath lam) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact (continuous_reflected_joint lam).comp
    (((continuous_centerPath lam).comp continuous_fst).prodMk continuous_snd)

/-- Compact-open path convergence transfers to locally uniform convergence
of the reflected exploration paths. -/
theorem reflectedCenteredPath_tendstoUniformlyOn
    {ι : Type*} {l : Filter ι} {ps : ι → BrownianPath}
    {p : BrownianPath} (hps : Tendsto ps l (𝓝 p))
    (lam : ℝ) (K : Set NNReal) (hK : IsCompact K) :
    TendstoUniformlyOn (fun j t => reflectedCenteredPath lam (ps j) t)
      (reflectedCenteredPath lam p) l K := by
  apply (ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mp
    ((continuous_reflectedCenteredPath lam).tendsto p |>.comp hps)) K hK

private theorem seen_ne_univ_at_boundary {n : ℕ} (G : Graph n)
    {s : ℕ} (hs : s < n) (hq : (explore G s).queue = []) :
    (explore G s).seen ≠ Finset.univ := by
  intro hseen
  have hp : processed G s = Finset.univ := by
    simp [processed, hq, hseen]
  have hc := processed_card_of_le G s hs.le
  rw [hp] at hc
  simp at hc
  omega

private theorem rootCount_succ_boundary {n : ℕ} (G : Graph n)
    {s : ℕ} (hs : s < n) (hq : (explore G s).queue = []) :
    rootCount G (s + 1) = rootCount G s + 1 := by
  simp [rootCount_succ, rootStarts, hq,
    seen_ne_univ_at_boundary G hs hq]

private theorem rootCount_succ_active {n : ℕ} (G : Graph n)
    {u : ℕ} (hq : (explore G u).queue ≠ []) :
    rootCount G (u + 1) = rootCount G u := by
  simp [rootCount_succ, rootStarts, hq]

/-- The number of discovered roots changes precisely once between consecutive
completed queue boundaries. -/
theorem queueBlock_rootCount {n : ℕ} (G : Graph n) {s t : ℕ}
    (hst : s < t) (ht : t ≤ n)
    (hqs : (explore G s).queue = [])
    (hinterior : ∀ u, s < u → u < t → (explore G u).queue ≠ []) :
    ∀ u, s < u → u ≤ t → rootCount G u = rootCount G s + 1 := by
  intro u
  induction u with
  | zero => intro h; omega
  | succ u ih =>
      intro hsu hut
      by_cases hus : u = s
      · subst u
        exact rootCount_succ_boundary G (lt_of_lt_of_le hst ht) hqs
      · have hsu' : s < u := by omega
        have hut' : u < t := by omega
        rw [rootCount_succ_active G (hinterior u hsu' hut')]
        exact ih hsu' hut'.le

/-- The final mesh record is exactly one integer walk unit below the start. -/
theorem queueBlock_walk_drop {n : ℕ} (G : Graph n) {s t : ℕ}
    (hst : s < t) (ht : t ≤ n)
    (hqs : (explore G s).queue = [])
    (hqt : (explore G t).queue = [])
    (hinterior : ∀ u, s < u → u < t → (explore G u).queue ≠ []) :
    (explore G t).walk = (explore G s).walk - 1 := by
  have hrs := (walk_eq_neg_rootCount_iff G s).mpr hqs
  have hrt := (walk_eq_neg_rootCount_iff G t).mpr hqt
  have hrc := queueBlock_rootCount G hst ht hqs hinterior t hst le_rfl
  omega

/-- Every grid point strictly before completion stays at or above the
starting walk record. -/
theorem queueBlock_walk_ge_start {n : ℕ} (G : Graph n) {s t u : ℕ}
    (hst : s < t) (ht : t ≤ n)
    (hqs : (explore G s).queue = [])
    (hinterior : ∀ k, s < k → k < t → (explore G k).queue ≠ [])
    (hsu : s ≤ u) (hut : u < t) :
    (explore G s).walk ≤ (explore G u).walk := by
  by_cases hus : u = s
  · subst u; exact le_rfl
  have hsu' : s < u := lt_of_le_of_ne hsu (Ne.symm hus)
  have hrc := queueBlock_rootCount G hst ht hqs hinterior u hsu' hut.le
  have hrs := (walk_eq_neg_rootCount_iff G s).mpr hqs
  have hwu := walk_eq_queue_sub_rootCount G u
  have hlen : 0 < (explore G u).queue.length :=
    List.length_pos_of_ne_nil (hinterior u hsu' hut)
  omega

/-- On the whole grid block, including its last endpoint, the walk is never
more than one unit below its starting record. -/
theorem queueBlock_walk_lower {n : ℕ} (G : Graph n) {s t u : ℕ}
    (hst : s < t) (ht : t ≤ n)
    (hqs : (explore G s).queue = [])
    (hqt : (explore G t).queue = [])
    (hinterior : ∀ k, s < k → k < t → (explore G k).queue ≠ [])
    (hsu : s ≤ u) (hut : u ≤ t) :
    (explore G s).walk - 1 ≤ (explore G u).walk := by
  rcases hut.eq_or_lt with rfl | hut'
  · exact le_of_eq (queueBlock_walk_drop G hst ht hqs hqt hinterior).symm
  · have h := queueBlock_walk_ge_start G hst ht hqs hinterior hsu hut'
    omega

theorem queueBlock_meshValue_drop {n : ℕ} (G : Graph n)
    (hn : 0 < n) {s t : ℕ}
    (hblock : successiveMeshRecords n s t (continuousRawExploration G)) :
    meshValue n t (continuousRawExploration G) =
      meshValue n s (continuousRawExploration G) - recordDrop n := by
  have ht := meshRecord_interpolation_le_order G hn hblock.2.2.1
  obtain ⟨hst, hqs, hqt, hinterior⟩ :=
    (successiveMeshRecords_interpolation_iff G hn ht).mp hblock
  have hw := queueBlock_walk_drop G hst ht hqs hqt hinterior
  rw [meshValue_interpolation G hn t, meshValue_interpolation G hn s, hw]
  unfold recordDrop
  simp only [Int.cast_sub, Int.cast_one]
  ring

private theorem linearInterpolation_lower (z : ℕ → ℝ)
    {s t : ℕ} {L : ℝ} (hst : s ≤ t)
    (hgrid : ∀ k, s ≤ k → k ≤ t → L ≤ z k)
    {x : NNReal} (hx0 : (s : NNReal) ≤ x) (hx1 : x ≤ (t : NNReal)) :
    L ≤ linearInterpolation z x := by
  by_cases hxt : x = (t : NNReal)
  · subst x
    have ht : linearInterpolation z (t : NNReal) = z t := by
      simp [linearInterpolation, Nat.floor_natCast]
    rw [ht]
    exact hgrid t hst le_rfl
  · have hreal0 : (s : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx0
    have hreal1 : (x : ℝ) < (t : ℝ) := by
      exact_mod_cast lt_of_le_of_ne hx1 hxt
    let k := ⌊(x : ℝ)⌋₊
    have hk0 : s ≤ k := Nat.le_floor hreal0
    have hk1 : k < t := (Nat.floor_lt (by positivity : (0 : ℝ) ≤ x)).mpr hreal1
    have htheta0 : 0 ≤ (x : ℝ) - k := sub_nonneg.mpr
      (Nat.floor_le (by positivity : (0 : ℝ) ≤ x))
    have htheta1 : (x : ℝ) - k ≤ 1 := by
      have := Nat.lt_floor_add_one (x : ℝ)
      linarith
    have hzk := hgrid k hk0 hk1.le
    have hzk1 := hgrid (k + 1) (hk0.trans (Nat.le_succ k)) (Nat.succ_le_of_lt hk1)
    simp only [linearInterpolation]
    have hconv : (1 - ((x : ℝ) - k)) * (z k - L) +
        ((x : ℝ) - k) * (z (k + 1) - L) ≥ 0 :=
      add_nonneg (mul_nonneg (by linarith) (sub_nonneg.mpr hzk))
        (mul_nonneg htheta0 (sub_nonneg.mpr hzk1))
    nlinarith

theorem meshTime_mul_scale (n j : ℕ) (hn : 0 < n) :
    meshTime n j * explorationScale n = (j : NNReal) := by
  apply NNReal.eq
  have hs := n23_pos n hn
  have hj : (0 : ℝ) ≤ (j : ℝ) / n23 n := div_nonneg (by positivity) hs.le
  simp [meshTime, hj]
  field_simp

theorem meshTime_eq_mul_meshStep (n j : ℕ) (hn : 0 < n) :
    (meshTime n j : ℝ) = (j : ℝ) * meshStep n := by
  have hs := n23_pos n hn
  have hj : (0 : ℝ) ≤ (j : ℝ) / n23 n := div_nonneg (by positivity) hs.le
  simp [meshTime, meshStep, hj]
  ring

/-- A completed BFS block stays above its start record throughout the
polygonal path, except for a possible drop of one record unit in the final
affine cell. -/
theorem queueBlock_affine_lower {n : ℕ} (G : Graph n) (hn : 0 < n)
    {s t : ℕ}
    (hblock : successiveMeshRecords n s t (continuousRawExploration G))
    {u : NNReal} (hus : meshTime n s ≤ u) (hut : u ≤ meshTime n t) :
    meshValue n s (continuousRawExploration G) - recordDrop n ≤
      continuousRawExploration G u := by
  have ht := meshRecord_interpolation_le_order G hn hblock.2.2.1
  obtain ⟨hst, hqs, hqt, hinterior⟩ :=
    (successiveMeshRecords_interpolation_iff G hn ht).mp hblock
  have hspos : 0 < n13 n := Real.rpow_pos_of_pos (by exact_mod_cast hn) _
  have hx0 : (s : NNReal) ≤ u * explorationScale n := by
    rw [← meshTime_mul_scale n s hn]
    exact mul_le_mul_left hus _
  have hx1 : u * explorationScale n ≤ (t : NNReal) := by
    rw [← meshTime_mul_scale n t hn]
    exact mul_le_mul_left hut _
  have hgrid : ∀ k, s ≤ k → k ≤ t →
      (((explore G s).walk : ℝ) - 1) ≤ explorationWalk G k := by
    intro k hsk hkt
    have hw := queueBlock_walk_lower G hst ht hqs hqt hinterior hsk hkt
    have hc : (((explore G s).walk - 1 : ℤ) : ℝ) ≤
        (((explore G k).walk : ℤ) : ℝ) := by exact_mod_cast hw
    simpa only [Int.cast_sub, Int.cast_one, explorationWalk] using! hc
  have hlin := linearInterpolation_lower (explorationWalk G) hst.le hgrid hx0 hx1
  change (((explore G s).walk : ℝ) - 1) ≤
    linearInterpolation (explorationWalk G) (u * explorationScale n) at hlin
  rw [meshValue_interpolation G hn s]
  change ((explore G s).walk : ℝ) / n13 n - 1 / n13 n ≤
    linearInterpolation (explorationWalk G) (u * explorationScale n) / n13 n
  convert div_le_div_of_nonneg_right hlin hspos.le using 1; ring

/- Before the final cell even the one-record error is absent. -/
end

end Erdos745.WrapUp.Proofs.Internal.W15_CRITICAL_RecordGeometry


/-!
# Forward matching of a limiting excursion to one finite BFS block

The selected block is indexed once, by a fixed positive reflected probe.
Both endpoint limits below refer to that same sequence of completed blocks.
-/

namespace Erdos745.WrapUp.Proofs.Internal.W15_CRITICAL_ForwardMatching

open Erdos745.WrapUp
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_Interpolation
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_CriticalBudget
open Erdos745.WrapUp.Proofs.Internal.W15_CRITICAL_Truncated
open Erdos745.WrapUp.Proofs.Internal.W15_CRITICAL_FiniteBlocks
open Erdos745.WrapUp.Proofs.Internal.W15_CRITICAL_FiniteEnumeration
open Erdos745.WrapUp.Proofs.Internal.W15_CRITICAL_RecordGeometry
open Erdos745.WrapUp.Proofs.Internal.W13_BROWNIAN_Ranks
open Erdos745.WrapUp.Proofs.Internal.W13_BROWNIAN_Geometry
open Erdos745.WrapUp.Proofs.Internal.W13_BROWNIAN_Hitting
open Filter Set MeasureTheory
open scoped Topology

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local simp] Pi.div_def Pi.mul_def Pi.add_def Pi.sub_def Pi.neg_def Pi.inv_def Function.comp_def
attribute [local instance] Classical.propDecidable

private theorem lt_midpoint {x y : NNReal} (hxy : x < y) :
    x < (x + y) / 2 := by
  apply NNReal.coe_lt_coe.mp
  have hreal : (x : ℝ) < (y : ℝ) := by exact_mod_cast hxy
  push_cast
  linarith

private theorem midpoint_lt {x y : NNReal} (hxy : x < y) :
    (x + y) / 2 < y := by
  apply NNReal.coe_lt_coe.mp
  have hreal : (x : ℝ) < (y : ℝ) := by exact_mod_cast hxy
  push_cast
  linarith

private theorem positive_between_of_null_occupation (w : BrownianPath)
    (lam : ℝ)
    (hzero : ∀ T : ℝ, 0 < T →
      volume {t : ℝ | 0 ≤ t ∧ t ≤ T ∧
        reflected w lam t.toNNReal = 0} = 0)
    {a b : NNReal} (hab : a < b) :
    ∃ q : NNReal, a < q ∧ q < b ∧ 0 < reflected w lam q := by
  by_contra hnone
  have hsub : Ioo (a : ℝ) (b : ℝ) ⊆
      {t : ℝ | 0 ≤ t ∧ t ≤ (b : ℝ) ∧
        reflected w lam t.toNNReal = 0} := by
    intro t ht
    have ht0 : 0 ≤ t := (NNReal.coe_nonneg a).trans ht.1.le
    have hta : a < t.toNNReal := NNReal.coe_lt_coe.mp (by
      simpa only [Real.coe_toNNReal t ht0] using! ht.1)
    have htb : t.toNNReal < b := NNReal.coe_lt_coe.mp (by
      simpa only [Real.coe_toNNReal t ht0] using! ht.2)
    have hnot : ¬ 0 < reflected w lam t.toNNReal := by
      intro hp
      exact hnone ⟨t.toNNReal, hta, htb, hp⟩
    exact ⟨ht0, ht.2.le,
      le_antisymm (le_of_not_gt hnot) (reflected_nonneg w lam t.toNNReal)⟩
  have hnull := measure_mono_null hsub
    (hzero (b : ℝ) (NNReal.coe_pos.mpr (lt_of_le_of_lt (zero_le) hab)))
  rw [Real.volume_Ioo] at hnull
  have hpos : 0 < (b : ℝ) - (a : ℝ) := sub_pos.mpr (by exact_mod_cast hab)
  exact (ne_of_gt (ENNReal.ofReal_pos.mpr hpos)) hnull

/-- Earlier compact minima are strictly above the starting level of a later
positive excursion.  The zero-occupation clause provides an earlier positive
excursion if equality is assumed. -/
theorem left_level_gap (w : BrownianPath) (lam : ℝ)
    (hgood : GoodExcursionPath w lam)
    {a b r : NNReal} (hab : excursion w lam a b) (hr : r < a) :
    drift w lam a < sInf ((drift w lam) '' Icc 0 r) := by
  have ha_lower : drift w lam a ≤
      sInf ((drift w lam) '' Icc 0 r) := by
    apply le_csInf
    · exact ⟨drift w lam 0, 0, ⟨le_rfl, zero_le⟩, rfl⟩
    · rintro v ⟨u, hu, rfl⟩
      exact drift_le_of_reflected_zero w lam hab.2.1
        (hu.2.trans hr.le)
  by_contra hstrict
  have hreverse : sInf ((drift w lam) '' Icc 0 r) ≤
      drift w lam a := le_of_not_gt hstrict
  obtain ⟨z, hz, hzmin⟩ :=
    (isCompact_Icc : IsCompact (Icc (0 : NNReal) r)).exists_sInf_image_eq
      ⟨0, ⟨le_rfl, zero_le⟩⟩
      (by unfold drift; fun_prop : ContinuousOn (drift w lam) (Icc 0 r))
  have hza : drift w lam z = drift w lam a := by
    have := drift_le_of_reflected_zero w lam hab.2.1 (hz.2.trans hr.le)
    rw [hzmin] at hreverse ha_lower
    exact le_antisymm hreverse this
  have hz0 : reflected w lam z = 0 := by
    have hzinf : drift w lam z =
        sInf ((drift w lam) '' Icc 0 z) := by
      apply le_antisymm
      · apply le_csInf
        · exact ⟨drift w lam z, z, ⟨zero_le, le_rfl⟩, rfl⟩
        · rintro v ⟨u, hu, rfl⟩
          rw [hza]
          exact drift_le_of_reflected_zero w lam hab.2.1
            (hu.2.trans (hz.2.trans hr.le))
      · apply csInf_le
          ((isCompact_Icc.image (by unfold drift; fun_prop)).bddBelow)
        exact ⟨z, ⟨zero_le, le_rfl⟩, rfl⟩
    simp [reflected, hzinf]
  obtain ⟨q, hzq, hqa, hqpos⟩ :=
    positive_between_of_null_occupation w lam hgood.2.1
      (hz.2.trans_lt hr)
  obtain ⟨c, d, hcd, hcq, hqd⟩ :=
    exists_excursion_containing_of_positive w lam
      (exists_future_reflected_zero_of_escape w lam hgood.1) hqpos
  have hzc : z ≤ c := by
    by_contra h
    have hcz : c < z := lt_of_not_ge h
    have hzd : z < d := hzq.trans hqd
    exact (ne_of_gt (hcd.2.2.2 z ⟨hcz, hzd⟩)) hz0
  have hca : c < a := hcq.trans hqa
  have hlevel : drift w lam c = drift w lam a := by
    apply le_antisymm
    · rw [← hza]
      exact drift_le_of_reflected_zero w lam hcd.2.1 hzc
    · exact drift_le_of_reflected_zero w lam hab.2.1 hca.le
  have hstrictlevel := hgood.2.2.1 c d a b hcd hab hca
  exact (ne_of_gt hstrictlevel) hlevel

/-- A positive-order graph has a completed queue block bracketing every
integer time before its terminal queue boundary. -/
theorem finite_bracket_exists {n : ℕ} (G : Graph n) {k : ℕ}
    (hk : k < n) :
    ∃ z : ℕ × ℕ, QueueBlock G z ∧ z.1 ≤ k ∧ k < z.2 := by
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
  refine ⟨(s, t), ⟨lt_of_le_of_lt hsk hkt, hs, ht, ?_⟩,
    hsk, hkt⟩
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

def bracketAt {n : ℕ} (G : Graph n) (k : ℕ) : ℕ × ℕ :=
  if hk : k < n then Classical.choose (finite_bracket_exists G hk) else (0, 0)

theorem bracketAt_spec {n : ℕ} (G : Graph n) {k : ℕ} (hk : k < n) :
    QueueBlock G (bracketAt G k) ∧
      (bracketAt G k).1 ≤ k ∧ k < (bracketAt G k).2 := by
  simp only [bracketAt, dif_pos hk]
  exact Classical.choose_spec (finite_bracket_exists G hk)

private theorem linearInterpolation_lower_initial (z : ℕ → ℝ)
    {k : ℕ} {L : ℝ}
    (hgrid : ∀ j, j ≤ k → L ≤ z j)
    {x : NNReal} (hx : x ≤ (k : NNReal)) :
    L ≤ linearInterpolation z x := by
  by_cases hxk : x = (k : NNReal)
  · subst x
    have hval : linearInterpolation z (k : NNReal) = z k := by
      simp [linearInterpolation, Nat.floor_natCast]
    rw [hval]
    exact hgrid k le_rfl
  · have hxlt : (x : ℝ) < (k : ℝ) := by
      exact_mod_cast lt_of_le_of_ne hx hxk
    let j := ⌊(x : ℝ)⌋₊
    have hjk : j < k := (Nat.floor_lt (by positivity : (0 : ℝ) ≤ x)).mpr hxlt
    have htheta0 : 0 ≤ (x : ℝ) - j := sub_nonneg.mpr
      (Nat.floor_le (by positivity : (0 : ℝ) ≤ x))
    have htheta1 : (x : ℝ) - j ≤ 1 := by
      have := Nat.lt_floor_add_one (x : ℝ)
      linarith
    have hzj := hgrid j hjk.le
    have hzj1 := hgrid (j + 1) (Nat.succ_le_of_lt hjk)
    simp only [linearInterpolation]
    have hconv : (1 - ((x : ℝ) - j)) * (z j - L) +
        ((x : ℝ) - j) * (z (j + 1) - L) ≥ 0 :=
      add_nonneg (mul_nonneg (by linarith) (sub_nonneg.mpr hzj))
        (mul_nonneg htheta0 (sub_nonneg.mpr hzj1))
    nlinarith

/-- A strict mesh record is an actual zero of the continuous reflected
polygonal path; affine cells before it cannot pass below the record value. -/
theorem meshRecord_reflected_zero {n : ℕ} (G : Graph n) (hn : 0 < n)
    {k : ℕ}
    (hk : meshRecord n k (continuousRawExploration G)) :
    reflectedCenteredPath 0 (continuousRawExploration G) (meshTime n k) = 0 := by
  let P := continuousRawExploration G
  have hgrid : ∀ j, j ≤ k →
      ((explore G k).walk : ℝ) ≤ explorationWalk G j := by
    intro j hj
    by_cases hjk : j = k
    · subst j; exact le_rfl
    have hjlt : j < k := lt_of_le_of_ne hj hjk
    have hrec : meshValue n k P < meshValue n j P := by
      rcases hk with hzero | hrecord
      · subst k; omega
      · exact hrecord j hjlt
    rw [meshValue_interpolation G hn k,
      meshValue_interpolation G hn j] at hrec
    have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
    have hspos : 0 < n13 n := Real.rpow_pos_of_pos hnreal _
    have hcast := (div_lt_div_iff_of_pos_right hspos).mp hrec
    change ((explore G k).walk : ℝ) ≤ ((explore G j).walk : ℝ)
    exact hcast.le
  have hmin : ∀ u ∈ Icc (0 : NNReal) (meshTime n k),
      P (meshTime n k) ≤ P u := by
    intro u hu
    have hx : u * explorationScale n ≤ (k : NNReal) := by
      rw [← meshTime_mul_scale n k hn]
      exact mul_le_mul_left hu.2 _
    have hlin := linearInterpolation_lower_initial (explorationWalk G)
      hgrid hx
    change meshValue n k (continuousRawExploration G) ≤
      continuousRawExploration G u
    rw [meshValue_interpolation G hn k]
    change ((explore G k).walk : ℝ) ≤
      linearInterpolation (explorationWalk G) (u * explorationScale n)
      at hlin
    change ((explore G k).walk : ℝ) / n13 n ≤
      linearInterpolation (explorationWalk G) (u * explorationScale n) / n13 n
    exact div_le_div_of_nonneg_right hlin
      (Real.rpow_nonneg (by positivity) _)
  have hcompact : BddBelow (P '' Icc 0 (meshTime n k)) :=
    (isCompact_Icc.image P.continuous).bddBelow
  have hzero : P (meshTime n k) =
      sInf (P '' Icc 0 (meshTime n k)) := by
    apply le_antisymm
    · apply le_csInf
      · exact ⟨P (meshTime n k), meshTime n k,
          ⟨zero_le, le_rfl⟩, rfl⟩
      · rintro v ⟨u, hu, rfl⟩
        exact hmin u hu
    · apply csInf_le hcompact
      exact ⟨meshTime n k, ⟨zero_le, le_rfl⟩, rfl⟩
  rw [reflectedCenteredPath_apply]
  change P (meshTime n k) - sInf (P '' Icc 0 (meshTime n k)) = 0
  rw [hzero]
  ring

def meshIndex (n : ℕ) (q : NNReal) : ℕ :=
  ⌊(q : ℝ) * n23 n⌋₊

private theorem meshIndex_time_bounds (n : ℕ) (hn : 0 < n)
    (q : NNReal) :
    (meshTime n (meshIndex n q) : ℝ) ≤ (q : ℝ) ∧
      (q : ℝ) < (meshTime n (meshIndex n q + 1) : ℝ) := by
  let k := meshIndex n q
  have hs := n23_pos n hn
  have hprod : 0 ≤ (q : ℝ) * n23 n := mul_nonneg q.property hs.le
  have hfloor : (k : ℝ) ≤ (q : ℝ) * n23 n := Nat.floor_le hprod
  have hceil : (q : ℝ) * n23 n < (k : ℝ) + 1 := by
    simpa only [k, meshIndex] using! Nat.lt_floor_add_one ((q : ℝ) * n23 n)
  have htime (j : ℕ) : (meshTime n j : ℝ) = (j : ℝ) / n23 n := by
    rw [meshTime_eq_mul_meshStep n j hn]
    simp [meshStep]
    ring
  constructor
  · rw [htime]
    exact (div_le_iff₀ hs).mpr (by nlinarith)
  · rw [htime]
    exact (lt_div_iff₀ hs).mpr (by push_cast; nlinarith)

private theorem meshIndex_time_tendsto {ι : Type*} {l : Filter ι}
    {ns : ι → ℕ} (hns : Tendsto ns l atTop) (q : NNReal) :
    Tendsto (fun j => meshTime (ns j) (meshIndex (ns j) q)) l (𝓝 q) := by
  have hpos : ∀ᶠ j in l, 0 < ns j := hns.eventually_ge_atTop 1
  have hlow : ∀ᶠ j in l,
      (q : ℝ) - meshStep (ns j) ≤
        (meshTime (ns j) (meshIndex (ns j) q) : ℝ) := by
    filter_upwards [hpos] with j hj
    obtain ⟨_, hupper⟩ := meshIndex_time_bounds (ns j) hj q
    rw [meshTime_eq_mul_meshStep (ns j) (meshIndex (ns j) q + 1) hj]
      at hupper
    rw [meshTime_eq_mul_meshStep (ns j) (meshIndex (ns j) q) hj]
    push_cast at hupper
    nlinarith
  have hhigh : ∀ᶠ j in l,
      (meshTime (ns j) (meshIndex (ns j) q) : ℝ) ≤ (q : ℝ) := by
    filter_upwards [hpos] with j hj
    exact (meshIndex_time_bounds (ns j) hj q).1
  apply NNReal.tendsto_coe.mp
  apply Filter.Tendsto.squeeze'
    (by simpa using! (meshStep_comp_tendsto_zero hns).const_sub (q : ℝ))
    tendsto_const_nhds hlow hhigh

private theorem meshIndex_lt_order_eventually {ι : Type*} {l : Filter ι}
    {ns : ι → ℕ} (hns : Tendsto ns l atTop) (q : NNReal) :
    ∀ᶠ j in l, meshIndex (ns j) q < ns j := by
  have hbudget' : ∀ᶠ j in l,
      8 * ⌊((q : ℝ) + 1) * n23 (ns j)⌋₊ ≤ ns j := by
    exact hns.eventually (eventually_eighth_horizon ((q : ℝ) + 1)
      (by positivity))
  filter_upwards [hbudget', hns.eventually_ge_atTop 1] with j hb hn
  have hs := n23_pos (ns j) hn
  have hfloor : meshIndex (ns j) q ≤
      ⌊((q : ℝ) + 1) * n23 (ns j)⌋₊ := by
    unfold meshIndex
    apply Nat.floor_mono
    nlinarith
  omega

private theorem runningInf_tendsto {ι : Type*} {l : Filter ι}
    {ps : ι → BrownianPath} {p : BrownianPath}
    (hps : Tendsto ps l (𝓝 p)) (r : NNReal) :
    Tendsto (fun j => sInf ((ps j) '' Icc (0 : NNReal) r)) l
      (𝓝 (sInf (p '' Icc 0 r))) := by
  have hcont : Continuous (fun v : BrownianPath =>
      sInf (v '' Icc (0 : NNReal) r)) := by
    apply isCompact_Icc.continuous_sInf
    exact ContinuousEval.continuous_eval
  exact (hcont.tendsto p).comp hps

private theorem eval_tendsto {ι : Type*} {l : Filter ι}
    {ps : ι → BrownianPath} {p : BrownianPath}
    (hps : Tendsto ps l (𝓝 p)) (u : NNReal) :
    Tendsto (fun j => ps j u) l (𝓝 (p u)) := by
  have hpair : Tendsto (fun j => (ps j, u)) l (𝓝 (p, u)) := by
    simpa only [nhds_prod_eq] using! hps.prodMk tendsto_const_nhds
  exact (ContinuousEval.continuous_eval.tendsto (p, u)).comp hpair

private theorem eval_moving_tendsto {ι : Type*} {l : Filter ι}
    {ps : ι → BrownianPath} {p : BrownianPath}
    {us : ι → NNReal} {u : NNReal}
    (hps : Tendsto ps l (𝓝 p)) (hus : Tendsto us l (𝓝 u)) :
    Tendsto (fun j => ps j (us j)) l (𝓝 (p u)) := by
  have hpair : Tendsto (fun j => (ps j, us j)) l (𝓝 (p, u)) := by
    simpa only [nhds_prod_eq] using! hps.prodMk hus
  exact (ContinuousEval.continuous_eval.tendsto (p, u)).comp hpair

private theorem corridor_positive_eventually {ι : Type*} {l : Filter ι}
    {ps : ι → BrownianPath} {p : BrownianPath}
    (hps : Tendsto ps l (𝓝 p)) (lam : ℝ)
    {a b c d : NNReal} (hab : excursion (centerPath p lam) lam a b)
    (hac : a < c) (hcd : c ≤ d) (hdb : d < b) :
    ∀ᶠ j in l, ∀ u ∈ Icc c d,
      0 < reflectedCenteredPath lam (ps j) u := by
  let R := reflectedCenteredPath lam p
  have hcompact : IsCompact (Icc c d) := isCompact_Icc
  obtain ⟨v, hv, hvmin⟩ := hcompact.exists_sInf_image_eq
    ⟨c, ⟨le_rfl, hcd⟩⟩ R.continuous.continuousOn
  have hvpos : 0 < sInf (R '' Icc c d) := by
    rw [hvmin]
    exact hab.2.2.2 v ⟨hac.trans_le hv.1, hv.2.trans_lt hdb⟩
  have hlow : ∀ u ∈ Icc c d, sInf (R '' Icc c d) ≤ R u := by
    intro u hu
    exact csInf_le (hcompact.image R.continuous).bddBelow ⟨u, hu, rfl⟩
  have hunif := reflectedCenteredPath_tendstoUniformlyOn hps lam
    (Icc c d) hcompact
  have hclose := (Metric.tendstoUniformlyOn_iff.mp hunif)
    (sInf (R '' Icc c d) / 2) (half_pos hvpos)
  filter_upwards [hclose] with j hj u hu
  have hd := hj u hu
  rw [Real.dist_eq] at hd
  have hdiff := (abs_lt.mp hd).2
  have hminle := hlow u hu
  dsimp [R] at hminle
  dsimp [R] at hvpos
  linarith

private theorem meshTime_mono {n : ℕ} (hn : 0 < n)
    {i j : ℕ} (hij : i ≤ j) : meshTime n i ≤ meshTime n j := by
  apply NNReal.coe_le_coe.mp
  rw [meshTime_eq_mul_meshStep n i hn,
    meshTime_eq_mul_meshStep n j hn]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hij)
    (meshStep_pos n hn).le

private theorem meshTime_strictMono {n : ℕ} (hn : 0 < n)
    {i j : ℕ} (hij : i < j) : meshTime n i < meshTime n j := by
  apply NNReal.coe_lt_coe.mp
  rw [meshTime_eq_mul_meshStep n i hn,
    meshTime_eq_mul_meshStep n j hn]
  exact mul_lt_mul_of_pos_right (by exact_mod_cast hij)
    (meshStep_pos n hn)

/-- A corridor inside a positive limiting excursion eventually contains no
finite strict record.  The canonical bracket therefore crosses its ends. -/
private theorem bracket_crosses_corridor {ι : Type*} {l : Filter ι}
    {ns : ι → ℕ} {Gs : (j : ι) → Graph (ns j)}
    {p : BrownianPath} (hns : Tendsto ns l atTop)
    (hps : Tendsto (fun j => continuousRawExploration (Gs j)) l (𝓝 p))
    (lam : ℝ) {a b c q d : NNReal}
    (hab : excursion (centerPath p lam) lam a b)
    (hac : a < c) (hcq : c < q) (hqd : q < d) (hdb : d < b) :
    ∀ᶠ j in l,
      meshTime (ns j) (bracketAt (Gs j) (meshIndex (ns j) q)).1 < c ∧
      d < meshTime (ns j) (bracketAt (Gs j) (meshIndex (ns j) q)).2 := by
  have hk := meshIndex_lt_order_eventually hns q
  have hqtime := meshIndex_time_tendsto hns q
  have hkc : ∀ᶠ j in l, c < meshTime (ns j) (meshIndex (ns j) q) :=
    hqtime.eventually_const_lt hcq
  have hkd : ∀ᶠ j in l, meshTime (ns j) (meshIndex (ns j) q) < d :=
    hqtime.eventually_lt_const hqd
  have hpos := corridor_positive_eventually hps lam hab hac
    (le_of_lt (hcq.trans hqd)) hdb
  filter_upwards [hk, hkc, hkd, hpos, hns.eventually_ge_atTop 1]
    with j hj hkc' hkd' hpos' hn
  let z := bracketAt (Gs j) (meshIndex (ns j) q)
  have hz := bracketAt_spec (Gs j) hj
  have hrec : successiveMeshRecords (ns j) z.1 z.2
      (continuousRawExploration (Gs j)) :=
    (queueBlock_iff_meshRecords (Gs j) hn z).mp hz.1
  have hsle : meshTime (ns j) z.1 ≤
      meshTime (ns j) (meshIndex (ns j) q) :=
    meshTime_mono hn hz.2.1
  have htgt : meshTime (ns j) (meshIndex (ns j) q) <
      meshTime (ns j) z.2 := meshTime_strictMono hn hz.2.2
  constructor
  · by_contra h
    have hcs : c ≤ meshTime (ns j) z.1 := le_of_not_gt h
    have hsd : meshTime (ns j) z.1 ≤ d :=
      hsle.trans hkd'.le
    have hzero := meshRecord_reflected_zero (Gs j) hn hrec.2.1
    have hpositive := hpos' (meshTime (ns j) z.1) ⟨hcs, hsd⟩
    exact (ne_of_gt hpositive) (by simpa using! hzero)
  · by_contra h
    have htd : meshTime (ns j) z.2 ≤ d := le_of_not_gt h
    have hct : c ≤ meshTime (ns j) z.2 :=
      hkc'.le.trans htgt.le
    have hzero := meshRecord_reflected_zero (Gs j) hn hrec.2.2.1
    have hpositive := hpos' (meshTime (ns j) z.2) ⟨hct, htd⟩
    exact (ne_of_gt hpositive) (by simpa using! hzero)

/-- One canonical completed BFS block matches each positive limiting
excursion.  Both endpoint limits use this very same sequence `z`. -/
theorem forward_excursion_matching
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {ns : ι → ℕ} {Gs : (j : ι) → Graph (ns j)}
    {p : BrownianPath} (hns : Tendsto ns l atTop)
    (hps : Tendsto (fun j => continuousRawExploration (Gs j)) l (𝓝 p))
    (lam : ℝ) (hgood : GoodExcursionPath (centerPath p lam) lam)
    {a b : NNReal} (hab : excursion (centerPath p lam) lam a b) :
    ∃ z : ι → ℕ × ℕ,
      (∀ᶠ j in l, (z j).1 < (z j).2 ∧ (z j).2 ≤ ns j ∧
        successiveMeshRecords (ns j) (z j).1 (z j).2
          (continuousRawExploration (Gs j))) ∧
      Tendsto (fun j => meshTime (ns j) (z j).1) l (𝓝 a) ∧
      Tendsto (fun j => meshTime (ns j) (z j).2) l (𝓝 b) := by
  let q : NNReal := (a + b) / 2
  have haq : a < q := by dsimp [q]; exact lt_midpoint hab.1
  have hqb : q < b := by dsimp [q]; exact midpoint_lt hab.1
  let k (j : ι) := meshIndex (ns j) q
  let z (j : ι) := bracketAt (Gs j) (k j)
  have hk : ∀ᶠ j in l, k j < ns j := meshIndex_lt_order_eventually hns q
  have hn : ∀ᶠ j in l, 0 < ns j := hns.eventually_ge_atTop 1
  have hblock : ∀ᶠ j in l,
      (z j).1 < (z j).2 ∧ (z j).2 ≤ ns j ∧
        successiveMeshRecords (ns j) (z j).1 (z j).2
          (continuousRawExploration (Gs j)) := by
    filter_upwards [hk, hn] with j hj hnj
    have hz := bracketAt_spec (Gs j) hj
    exact ⟨hz.1.1, hz.1.2.2.1.1,
      (queueBlock_iff_meshRecords (Gs j) hnj (z j)).mp hz.1⟩
  have hktime : Tendsto (fun j => meshTime (ns j) (k j)) l (𝓝 q) :=
    meshIndex_time_tendsto hns q
  have hleftUpper : ∀ r : NNReal, a < r →
      ∀ᶠ j in l, meshTime (ns j) (z j).1 < r := by
    intro r har
    let c : NNReal := (a + min r q) / 2
    let d : NNReal := (q + b) / 2
    have hac : a < c := by
      dsimp [c]
      exact lt_midpoint (lt_min har haq)
    have hcr : c < r := by
      dsimp [c]
      exact (midpoint_lt (lt_min har haq)).trans_le (min_le_left _ _)
    have hcq : c < q := by
      exact (midpoint_lt (lt_min har haq)).trans_le (min_le_right _ _)
    have hqd : q < d := by dsimp [d]; exact lt_midpoint hqb
    have hdb : d < b := by dsimp [d]; exact midpoint_lt hqb
    exact (bracket_crosses_corridor hns hps lam hab hac hcq hqd hdb).mono
      (fun j h => h.1.trans hcr)
  have hleftLower : ∀ r : NNReal, r < a →
      ∀ᶠ j in l, r < meshTime (ns j) (z j).1 := by
    intro r hra
    have hgap := left_level_gap (centerPath p lam) lam hgood hab hra
    have hgap' : p a < sInf (p '' Icc 0 r) := by
      simpa only [drift_centerPath] using! hgap
    have hmin := runningInf_tendsto hps r
    have hea := eval_tendsto hps a
    have hv := recordDrop_comp_tendsto_zero hns
    have hdiff : Tendsto (fun j =>
        sInf ((continuousRawExploration (Gs j)) '' Icc (0 : NNReal) r) -
          continuousRawExploration (Gs j) a - recordDrop (ns j))
        l (𝓝 (sInf (p '' Icc 0 r) - p a - 0)) :=
      (hmin.sub hea).sub hv
    have hpositive : ∀ᶠ j in l,
        0 < sInf ((continuousRawExploration (Gs j)) '' Icc (0 : NNReal) r) -
          continuousRawExploration (Gs j) a - recordDrop (ns j) :=
      hdiff.eventually_const_lt (by linarith)
    have hka : ∀ᶠ j in l, a < meshTime (ns j) (k j) :=
      hktime.eventually_const_lt haq
    filter_upwards [hpositive, hblock, hk, hn, hka] with j hp hb hj hnj hka'
    by_contra h
    have hsr : meshTime (ns j) (z j).1 ≤ r := le_of_not_gt h
    have hsa : meshTime (ns j) (z j).1 ≤ a :=
      hsr.trans hra.le
    have hat : a ≤ meshTime (ns j) (z j).2 := by
      have hkz := (bracketAt_spec (Gs j) hj).2.2
      exact hka'.le.trans (meshTime_mono hnj hkz.le)
    have hlower := queueBlock_affine_lower (Gs j) hnj hb.2.2 hsa hat
    have hminle : sInf ((continuousRawExploration (Gs j)) '' Icc 0 r) ≤
        continuousRawExploration (Gs j) (meshTime (ns j) (z j).1) := by
      apply csInf_le
        ((isCompact_Icc.image (continuousRawExploration (Gs j)).continuous).bddBelow)
      exact ⟨meshTime (ns j) (z j).1, ⟨zero_le, hsr⟩, rfl⟩
    dsimp [meshValue] at hlower
    linarith
  have hstart : Tendsto (fun j => meshTime (ns j) (z j).1) l (𝓝 a) :=
    tendsto_order.mpr ⟨hleftLower, hleftUpper⟩
  have hrightLower : ∀ r : NNReal, r < b →
      ∀ᶠ j in l, r < meshTime (ns j) (z j).2 := by
    intro r hrb
    let c : NNReal := (a + q) / 2
    let d : NNReal := (max r q + b) / 2
    have hac : a < c := by dsimp [c]; exact lt_midpoint haq
    have hcq : c < q := by dsimp [c]; exact midpoint_lt haq
    have hqd : q < d := by
      exact (le_max_right _ _).trans_lt (lt_midpoint (max_lt hrb hqb))
    have hdb : d < b := by dsimp [d]; exact midpoint_lt (max_lt hrb hqb)
    have hrd : r < d :=
      (le_max_left _ _).trans_lt (lt_midpoint (max_lt hrb hqb))
    exact (bracket_crosses_corridor hns hps lam hab hac hcq hqd hdb).mono
      (fun j h => hrd.trans h.2)
  have hrightUpper : ∀ r : NNReal, b < r →
      ∀ᶠ j in l, meshTime (ns j) (z j).2 < r := by
    intro r hbr
    have hdelta : 0 < r - b := tsub_pos_iff_lt.mpr hbr
    obtain ⟨u, hbu, hur, hdescent⟩ :=
      hgood.2.2.2.1 a b hab (r - b) hdelta
    have hur' : u < r := by
      simpa only [add_tsub_cancel_of_le hbr.le] using! hur
    have hdescent' : p u < p a := by
      simpa only [drift_centerPath] using! hdescent
    have hstartEval : Tendsto
        (fun j => continuousRawExploration (Gs j)
          (meshTime (ns j) (z j).1)) l (𝓝 (p a)) :=
      eval_moving_tendsto hps hstart
    have huEval := eval_tendsto hps u
    have hv := recordDrop_comp_tendsto_zero hns
    have hdiff : Tendsto (fun j =>
        continuousRawExploration (Gs j)
          (meshTime (ns j) (z j).1) - recordDrop (ns j) -
            continuousRawExploration (Gs j) u) l
        (𝓝 (p a - 0 - p u)) := (hstartEval.sub hv).sub huEval
    have hpositive : ∀ᶠ j in l,
        0 < continuousRawExploration (Gs j)
          (meshTime (ns j) (z j).1) - recordDrop (ns j) -
            continuousRawExploration (Gs j) u :=
      hdiff.eventually_const_lt (by linarith)
    have hsu : ∀ᶠ j in l,
        meshTime (ns j) (z j).1 < u :=
      hstart.eventually_lt_const (hab.1.trans hbu)
    filter_upwards [hpositive, hsu, hblock, hn] with j hp hs hb hnj
    have htu : meshTime (ns j) (z j).2 < u := by
      by_contra h
      have hut : u ≤ meshTime (ns j) (z j).2 := le_of_not_gt h
      have hlower := queueBlock_affine_lower (Gs j) hnj hb.2.2 hs.le hut
      dsimp [meshValue] at hlower
      linarith
    exact htu.trans hur'
  have hend : Tendsto (fun j => meshTime (ns j) (z j).2) l (𝓝 b) :=
    tendsto_order.mpr ⟨hrightLower, hrightUpper⟩
  exact ⟨z, hblock, hstart, hend⟩

end

end Erdos745.WrapUp.Proofs.Internal.W15_CRITICAL_ForwardMatching


/-!
# Two-way deterministic endpoint matching

Every macroscopic limit of completed finite BFS blocks is one excursion of
the limiting reflected path.  The forward witness from `ForwardMatching` is
kept as the same block sequence for both endpoints.
-/

namespace Erdos745.WrapUp.Proofs.Internal.W15_CRITICAL_EndpointMatching

open Erdos745.WrapUp
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_Interpolation
open Erdos745.WrapUp.Proofs.Internal.W15_CRITICAL_Truncated
open Erdos745.WrapUp.Proofs.Internal.W15_CRITICAL_RecordGeometry
open Erdos745.WrapUp.Proofs.Internal.W15_CRITICAL_ForwardMatching
open Erdos745.WrapUp.Proofs.Internal.W13_BROWNIAN_Ranks
open Erdos745.WrapUp.Proofs.Internal.W13_BROWNIAN_Geometry
open Erdos745.WrapUp.Proofs.Internal.W13_BROWNIAN_Hitting
open Filter Set MeasureTheory
open scoped Topology

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local simp] Pi.div_def Pi.mul_def Pi.add_def Pi.sub_def Pi.neg_def Pi.inv_def Function.comp_def
attribute [local instance] Classical.propDecidable

/-- A single sequence of actual completed blocks with both endpoint limits. -/
def MatchedBlockSequence {ι : Type*} (l : Filter ι)
    (ns : ι → ℕ) (Gs : (j : ι) → Graph (ns j))
    (z : ι → ℕ × ℕ) (s t : NNReal) : Prop :=
  (∀ᶠ j in l, (z j).1 < (z j).2 ∧ (z j).2 ≤ ns j ∧
    successiveMeshRecords (ns j) (z j).1 (z j).2
      (continuousRawExploration (Gs j))) ∧
  Tendsto (fun j => meshTime (ns j) (z j).1) l (𝓝 s) ∧
  Tendsto (fun j => meshTime (ns j) (z j).2) l (𝓝 t)

private theorem eval_moving {ι : Type*} {l : Filter ι}
    {ps : ι → BrownianPath} {p : BrownianPath}
    {us : ι → NNReal} {u : NNReal}
    (hps : Tendsto ps l (𝓝 p)) (hus : Tendsto us l (𝓝 u)) :
    Tendsto (fun j => ps j (us j)) l (𝓝 (p u)) := by
  have hpair : Tendsto (fun j => (ps j, us j)) l (𝓝 (p, u)) := by
    simpa only [nhds_prod_eq] using! hps.prodMk hus
  exact (ContinuousEval.continuous_eval.tendsto (p, u)).comp hpair

private theorem eval_fixed {ι : Type*} {l : Filter ι}
    {ps : ι → BrownianPath} {p : BrownianPath}
    (hps : Tendsto ps l (𝓝 p)) (u : NNReal) :
    Tendsto (fun j => ps j u) l (𝓝 (p u)) :=
  eval_moving hps tendsto_const_nhds

private theorem positive_between (w : BrownianPath) (lam : ℝ)
    (hzero : ∀ T : ℝ, 0 < T →
      volume {t : ℝ | 0 ≤ t ∧ t ≤ T ∧
        reflected w lam t.toNNReal = 0} = 0)
    {a b : NNReal} (hab : a < b) :
    ∃ q : NNReal, a < q ∧ q < b ∧ 0 < reflected w lam q := by
  by_contra hnone
  have hsub : Ioo (a : ℝ) (b : ℝ) ⊆
      {t : ℝ | 0 ≤ t ∧ t ≤ (b : ℝ) ∧
        reflected w lam t.toNNReal = 0} := by
    intro t ht
    have ht0 : 0 ≤ t := (NNReal.coe_nonneg a).trans ht.1.le
    have hta : a < t.toNNReal := NNReal.coe_lt_coe.mp (by
      simpa only [Real.coe_toNNReal t ht0] using! ht.1)
    have htb : t.toNNReal < b := NNReal.coe_lt_coe.mp (by
      simpa only [Real.coe_toNNReal t ht0] using! ht.2)
    have hnot : ¬ 0 < reflected w lam t.toNNReal := by
      intro hp
      exact hnone ⟨t.toNNReal, hta, htb, hp⟩
    exact ⟨ht0, ht.2.le,
      le_antisymm (le_of_not_gt hnot) (reflected_nonneg w lam t.toNNReal)⟩
  have hnull := measure_mono_null hsub
    (hzero (b : ℝ) (NNReal.coe_pos.mpr (lt_of_le_of_lt (zero_le) hab)))
  rw [Real.volume_Ioo] at hnull
  have hpos : 0 < (b : ℝ) - (a : ℝ) := sub_pos.mpr (by exact_mod_cast hab)
  exact (ne_of_gt (ENNReal.ofReal_pos.mpr hpos)) hnull

private theorem reflected_zero_of_eventual_records
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {ns : ι → ℕ} {Gs : (j : ι) → Graph (ns j)}
    {p : BrownianPath} (hns : Tendsto ns l atTop)
    (hps : Tendsto (fun j => continuousRawExploration (Gs j)) l (𝓝 p))
    (lam : ℝ) {ks : ι → ℕ} {u : NNReal}
    (hrecord : ∀ᶠ j in l,
      meshRecord (ns j) (ks j) (continuousRawExploration (Gs j)))
    (hku : Tendsto (fun j => meshTime (ns j) (ks j)) l (𝓝 u)) :
    reflected (centerPath p lam) lam u = 0 := by
  have hpath : Tendsto
      (fun j => reflectedCenteredPath lam (continuousRawExploration (Gs j)))
      l (𝓝 (reflectedCenteredPath lam p)) :=
    ((continuous_reflectedCenteredPath lam).tendsto p).comp hps
  have hvalue : Tendsto (fun j =>
      reflectedCenteredPath lam (continuousRawExploration (Gs j))
        (meshTime (ns j) (ks j))) l
      (𝓝 (reflectedCenteredPath lam p u)) := eval_moving hpath hku
  have hzero : ∀ᶠ j in l,
      reflectedCenteredPath lam (continuousRawExploration (Gs j))
        (meshTime (ns j) (ks j)) = 0 := by
    filter_upwards [hrecord, hns.eventually_ge_atTop 1] with j hj hn
    have hz := meshRecord_reflected_zero (Gs j) hn hj
    simpa only [reflectedCenteredPath_apply] using! hz
  have hzero_tendsto : Tendsto (fun j =>
      reflectedCenteredPath lam (continuousRawExploration (Gs j))
        (meshTime (ns j) (ks j))) l (𝓝 (0 : ℝ)) :=
    tendsto_const_nhds.congr' (hzero.mono fun j hj => hj.symm)
  have heq := tendsto_nhds_unique hvalue hzero_tendsto
  exact heq

/-- Limit of a sequence of completed blocks with macroscopic limiting length
is precisely one excursion; no positive-length spurious block survives. -/
theorem converse_excursion_matching
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {ns : ι → ℕ} {Gs : (j : ι) → Graph (ns j)}
    {p : BrownianPath} (hns : Tendsto ns l atTop)
    (hps : Tendsto (fun j => continuousRawExploration (Gs j)) l (𝓝 p))
    (lam : ℝ) (hgood : GoodExcursionPath (centerPath p lam) lam)
    {z : ι → ℕ × ℕ} {s t : NNReal}
    (hz : MatchedBlockSequence l ns Gs z s t)
    {eta : ℝ} (heta : 0 < eta) (hlength : eta ≤ (t : ℝ) - (s : ℝ)) :
    excursion (centerPath p lam) lam s t := by
  have hst : s < t := NNReal.coe_lt_coe.mp (by linarith)
  have hstartzero : reflected (centerPath p lam) lam s = 0 :=
    reflected_zero_of_eventual_records hns hps lam
      (hz.1.mono fun j hj => hj.2.2.2.1) hz.2.1
  have hendzero : reflected (centerPath p lam) lam t = 0 :=
    reflected_zero_of_eventual_records hns hps lam
      (hz.1.mono fun j hj => hj.2.2.2.2.1) hz.2.2
  have hs_eval : Tendsto (fun j => continuousRawExploration (Gs j)
      (meshTime (ns j) (z j).1)) l (𝓝 (p s)) :=
    eval_moving hps hz.2.1
  have ht_eval : Tendsto (fun j => continuousRawExploration (Gs j)
      (meshTime (ns j) (z j).2)) l (𝓝 (p t)) :=
    eval_moving hps hz.2.2
  have hv : Tendsto (fun j => recordDrop (ns j)) l (𝓝 0) :=
    recordDrop_comp_tendsto_zero hns
  have hdrop : ∀ᶠ j in l,
      continuousRawExploration (Gs j) (meshTime (ns j) (z j).2) =
        continuousRawExploration (Gs j) (meshTime (ns j) (z j).1) -
          recordDrop (ns j) := by
    filter_upwards [hz.1, hns.eventually_ge_atTop 1] with j hj hn
    simpa only [meshValue] using!
      queueBlock_meshValue_drop (Gs j) hn hj.2.2
  have hdrop_limit : Tendsto (fun j =>
      continuousRawExploration (Gs j) (meshTime (ns j) (z j).2))
      l (𝓝 (p s - 0)) :=
    (hs_eval.sub hv).congr' (hdrop.mono fun j hj => hj.symm)
  have hends : p t = p s := by
    have heq := tendsto_nhds_unique ht_eval hdrop_limit
    simpa using! heq
  have hmiddle : ∀ u ∈ Ioo s t, p s ≤ p u := by
    intro u hu
    have hleft : ∀ᶠ j in l, meshTime (ns j) (z j).1 ≤ u :=
      (hz.2.1.eventually_lt_const hu.1).mono fun j h => h.le
    have hright : ∀ᶠ j in l, u ≤ meshTime (ns j) (z j).2 :=
      (hz.2.2.eventually_const_lt hu.2).mono fun j h => h.le
    have hbound : ∀ᶠ j in l,
        continuousRawExploration (Gs j) (meshTime (ns j) (z j).1) -
          recordDrop (ns j) ≤ continuousRawExploration (Gs j) u := by
      filter_upwards [hz.1, hleft, hright, hns.eventually_ge_atTop 1]
        with j hj hle hre hn
      simpa only [meshValue] using!
        queueBlock_affine_lower (Gs j) hn hj.2.2 hle hre
    have hu_eval : Tendsto (fun j => continuousRawExploration (Gs j) u)
        l (𝓝 (p u)) := eval_fixed hps u
    have hle := le_of_tendsto_of_tendsto (hs_eval.sub hv) hu_eval hbound
    simpa using! hle
  have hwithin : ∀ u ∈ Icc s t, p s ≤ p u := by
    intro u hu
    rcases hu.1.eq_or_lt with h | h
    · subst u; exact le_rfl
    rcases hu.2.eq_or_lt with h' | h'
    · subst u; exact hends.ge
    · exact hmiddle u ⟨h, h'⟩
  have hstartlevel : ∀ u : NNReal, u ≤ t → p s ≤ p u := by
    intro u hut
    by_cases hus : u ≤ s
    · simpa only [drift_centerPath] using!
        drift_le_of_reflected_zero (centerPath p lam) lam hstartzero hus
    · exact hwithin u ⟨le_of_not_ge hus, hut⟩
  have hfuture : ∀ q : NNReal, ∃ v : NNReal,
      q < v ∧ reflected (centerPath p lam) lam v = 0 :=
    exists_future_reflected_zero_of_escape (centerPath p lam) lam hgood.1
  have hpositive : ∀ u ∈ Ioo s t,
      0 < reflected (centerPath p lam) lam u := by
    intro u hu
    have hnotzero : reflected (centerPath p lam) lam u ≠ 0 := by
      intro hu0
      obtain ⟨q₁, hsq₁, hq₁u, hq₁pos⟩ :=
        positive_between (centerPath p lam) lam hgood.2.1 hu.1
      obtain ⟨q₂, huq₂, hq₂t, hq₂pos⟩ :=
        positive_between (centerPath p lam) lam hgood.2.1 hu.2
      obtain ⟨a₁, b₁, he₁, ha₁q₁, hq₁b₁⟩ :=
        exists_excursion_containing_of_positive
          (centerPath p lam) lam hfuture hq₁pos
      obtain ⟨a₂, b₂, he₂, ha₂q₂, hq₂b₂⟩ :=
        exists_excursion_containing_of_positive
          (centerPath p lam) lam hfuture hq₂pos
      have hsa₁ : s ≤ a₁ := by
        by_contra h
        have ha₁s : a₁ < s := lt_of_not_ge h
        have hsb₁ : s < b₁ := hsq₁.trans hq₁b₁
        exact (ne_of_gt (he₁.2.2.2 s ⟨ha₁s, hsb₁⟩)) hstartzero
      have hua₂ : u ≤ a₂ := by
        by_contra h
        have ha₂u : a₂ < u := lt_of_not_ge h
        have hub₂ : u < b₂ := huq₂.trans hq₂b₂
        exact (ne_of_gt (he₂.2.2.2 u ⟨ha₂u, hub₂⟩)) hu0
      have ha₁a₂ : a₁ < a₂ := ha₁q₁.trans (hq₁u.trans_le hua₂)
      have ha₁t : a₁ ≤ t := (ha₁q₁.trans (hq₁u.trans hu.2)).le
      have ha₂t : a₂ ≤ t := (ha₂q₂.trans hq₂t).le
      have hlevel₁ : p a₁ = p s := by
        apply le_antisymm
        · simpa only [drift_centerPath] using!
            drift_le_of_reflected_zero (centerPath p lam) lam he₁.2.1 hsa₁
        · exact hstartlevel a₁ ha₁t
      have hlevel₂ : p a₂ = p s := by
        apply le_antisymm
        · simpa only [drift_centerPath] using!
            drift_le_of_reflected_zero (centerPath p lam) lam he₂.2.1
              (hsa₁.trans ha₁a₂.le)
        · exact hstartlevel a₂ ha₂t
      have hstrict := hgood.2.2.1 a₁ b₁ a₂ b₂ he₁ he₂ ha₁a₂
      simp only [drift_centerPath, hlevel₁, hlevel₂] at hstrict
      exact (lt_irrefl _) hstrict
    exact lt_of_le_of_ne (reflected_nonneg (centerPath p lam) lam u)
      (Ne.symm hnotzero)
  exact ⟨hst, hstartzero, hendzero, hpositive⟩

private theorem meshTime_mono {n : ℕ} (hn : 0 < n)
    {i j : ℕ} (hij : i ≤ j) : meshTime n i ≤ meshTime n j := by
  apply NNReal.coe_le_coe.mp
  rw [meshTime_eq_mul_meshStep n i hn,
    meshTime_eq_mul_meshStep n j hn]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hij)
    (meshStep_pos n hn).le

theorem meshBlockLength_eq_meshTimes {n s t : ℕ} (hn : 0 < n) :
    meshBlockLength n s t =
      (meshTime n t : ℝ) - (meshTime n s : ℝ) := by
  rw [meshTime_eq_mul_meshStep n t hn,
    meshTime_eq_mul_meshStep n s hn]
  unfold meshBlockLength meshStep
  ring

/-- In a compact time window, every sequence of completed blocks whose
length stays above a positive cutoff has a subsequential excursion limit. -/
theorem no_spurious_long_blocks_on_compact
    {ns : ℕ → ℕ} {Gs : (j : ℕ) → Graph (ns j)}
    {p : BrownianPath} (hns : Tendsto ns atTop atTop)
    (hps : Tendsto (fun j => continuousRawExploration (Gs j)) atTop (𝓝 p))
    (lam : ℝ) (hgood : GoodExcursionPath (centerPath p lam) lam)
    (z : ℕ → ℕ × ℕ) (U : NNReal) (eta : ℝ) (heta : 0 < eta)
    (hz : ∀ᶠ j : ℕ in atTop,
      (z j).1 < (z j).2 ∧ (z j).2 ≤ ns j ∧
        successiveMeshRecords (ns j) (z j).1 (z j).2
          (continuousRawExploration (Gs j)))
    (hU : ∀ᶠ j : ℕ in atTop, meshTime (ns j) (z j).2 ≤ U)
    (hlong : ∀ᶠ j : ℕ in atTop,
      eta ≤ meshBlockLength (ns j) (z j).1 (z j).2) :
    ∃ s t : NNReal, ∃ φ : ℕ → ℕ,
      StrictMono φ ∧
      MatchedBlockSequence atTop (ns ∘ φ) (fun j => Gs (φ j))
        (z ∘ φ) s t ∧
      eta ≤ (t : ℝ) - (s : ℝ) ∧
      excursion (centerPath p lam) lam s t := by
  let x (j : ℕ) : NNReal × NNReal :=
    (meshTime (ns j) (z j).1, meshTime (ns j) (z j).2)
  have hK : IsCompact (Icc (0 : NNReal × NNReal) (U, U)) := isCompact_Icc
  have hx : ∀ᶠ j : ℕ in atTop, x j ∈ Icc (0 : NNReal × NNReal) (U, U) := by
    filter_upwards [hz, hU, hns.eventually_ge_atTop 1] with j hj hUj hn
    have hstartle : meshTime (ns j) (z j).1 ≤ U :=
      (meshTime_mono hn hj.1.le).trans hUj
    exact ⟨⟨zero_le, zero_le⟩, ⟨hstartle, hUj⟩⟩
  obtain ⟨⟨s, t⟩, _, φ, hφ, hpair⟩ := hK.tendsto_subseq' hx.frequently
  have hφtop : Tendsto φ atTop atTop := hφ.tendsto_atTop
  have hpair' : Tendsto (fun j => x (φ j)) atTop (𝓝 s ×ˢ 𝓝 t) := by
    simpa only [nhds_prod_eq] using! hpair
  have hsconv : Tendsto (fun j => meshTime (ns (φ j)) (z (φ j)).1)
      atTop (𝓝 s) := by simpa only [Function.comp_def, x] using! hpair'.fst
  have htconv : Tendsto (fun j => meshTime (ns (φ j)) (z (φ j)).2)
      atTop (𝓝 t) := by simpa only [Function.comp_def, x] using! hpair'.snd
  have hzφ : ∀ᶠ j : ℕ in atTop,
      (z (φ j)).1 < (z (φ j)).2 ∧ (z (φ j)).2 ≤ ns (φ j) ∧
        successiveMeshRecords (ns (φ j)) (z (φ j)).1 (z (φ j)).2
          (continuousRawExploration (Gs (φ j))) := hφtop.eventually hz
  have hmatch : MatchedBlockSequence atTop (ns ∘ φ)
      (fun j => Gs (φ j)) (z ∘ φ) s t := ⟨hzφ, hsconv, htconv⟩
  have hdiff : Tendsto (fun j =>
      (meshTime (ns (φ j)) (z (φ j)).2 : ℝ) -
        (meshTime (ns (φ j)) (z (φ j)).1 : ℝ)) atTop
      (𝓝 ((t : ℝ) - (s : ℝ))) :=
    ((NNReal.continuous_coe.tendsto t).comp htconv).sub
      ((NNReal.continuous_coe.tendsto s).comp hsconv)
  have hlong' : ∀ᶠ j : ℕ in atTop,
      eta ≤ (meshTime (ns (φ j)) (z (φ j)).2 : ℝ) -
        (meshTime (ns (φ j)) (z (φ j)).1 : ℝ) := by
    filter_upwards [hφtop.eventually hlong, hzφ,
      (hns.comp hφtop).eventually_ge_atTop 1] with j hj hblock hn
    have heq := meshBlockLength_eq_meshTimes
      (n := ns (φ j)) (s := (z (φ j)).1) (t := (z (φ j)).2) hn
    rw [heq] at hj
    exact hj
  have hlimit : eta ≤ (t : ℝ) - (s : ℝ) :=
    ge_of_tendsto hdiff hlong'
  have hexc : excursion (centerPath p lam) lam s t :=
    converse_excursion_matching (hns.comp hφtop) (hps.comp hφtop)
      lam hgood hmatch heta hlimit
  exact ⟨s, t, φ, hφ, hmatch, hlimit, hexc⟩

/-- Two completed record intervals containing the same real interior probe
are the same finite BFS block. -/
theorem completed_block_unique_at_probe {n : ℕ} (G : Graph n)
    (hn : 0 < n) {z w : ℕ × ℕ} {q : NNReal}
    (hz : successiveMeshRecords n z.1 z.2 (continuousRawExploration G))
    (hw : successiveMeshRecords n w.1 w.2 (continuousRawExploration G))
    (hzq : meshTime n z.1 < q ∧ q < meshTime n z.2)
    (hwq : meshTime n w.1 < q ∧ q < meshTime n w.2) : z = w := by
  have hstart : z.1 = w.1 := by
    rcases lt_trichotomy z.1 w.1 with h | h | h
    · have hwt : w.1 < z.2 := by
        by_contra h'
        have hle : z.2 ≤ w.1 := le_of_not_gt h'
        have hm := meshTime_mono hn hle
        exact (not_lt_of_ge hm) (hwq.1.trans hzq.2)
      exact False.elim (hz.2.2.2 w.1 h hwt hw.2.1)
    · exact h
    · have hzt : z.1 < w.2 := by
        by_contra h'
        have hle : w.2 ≤ z.1 := le_of_not_gt h'
        have hm := meshTime_mono hn hle
        exact (not_lt_of_ge hm) (hzq.1.trans hwq.2)
      exact False.elim (hw.2.2.2 z.1 h hzt hz.2.1)
  have hend : z.2 = w.2 := by
    rcases lt_trichotomy z.2 w.2 with h | h | h
    · exact False.elim (hw.2.2.2 z.2 (hstart ▸ hz.1) h hz.2.2.1)
    · exact h
    · exact False.elim (hz.2.2.2 w.2 (hstart.symm ▸ hw.1) h hw.2.2.1)
  exact Prod.ext hstart hend

private theorem lt_midpoint {x y : NNReal} (hxy : x < y) :
    x < (x + y) / 2 := by
  apply NNReal.coe_lt_coe.mp
  have hreal : (x : ℝ) < (y : ℝ) := by exact_mod_cast hxy
  push_cast
  linarith

private theorem midpoint_lt {x y : NNReal} (hxy : x < y) :
    (x + y) / 2 < y := by
  apply NNReal.coe_lt_coe.mp
  have hreal : (x : ℝ) < (y : ℝ) := by exact_mod_cast hxy
  push_cast
  linarith

/-- Forward witnesses for the same limiting excursion are eventually the
same actual completed finite block. -/
theorem matched_blocks_eventually_equal
    {ι : Type*} {l : Filter ι}
    {ns : ι → ℕ} {Gs : (j : ι) → Graph (ns j)}
    (hns : Tendsto ns l atTop)
    {z w : ι → ℕ × ℕ} {a b : NNReal} (hab : a < b)
    (hz : MatchedBlockSequence l ns Gs z a b)
    (hw : MatchedBlockSequence l ns Gs w a b) :
    z =ᶠ[l] w := by
  let q : NNReal := (a + b) / 2
  have haq : a < q := lt_midpoint hab
  have hqb : q < b := midpoint_lt hab
  have hzleft := hz.2.1.eventually_lt_const haq
  have hzright := hz.2.2.eventually_const_lt hqb
  have hwleft := hw.2.1.eventually_lt_const haq
  have hwright := hw.2.2.eventually_const_lt hqb
  filter_upwards [hz.1, hw.1, hzleft, hzright, hwleft, hwright,
    hns.eventually_ge_atTop 1] with j hzj hwj hzl hzr hwl hwr hn
  exact completed_block_unique_at_probe (Gs j) hn hzj.2.2 hwj.2.2
    ⟨hzl, hzr⟩ ⟨hwl, hwr⟩

private theorem eventually_ne_of_distinct_limits
    {ι : Type*} {l : Filter ι} {f g : ι → NNReal}
    {a b : NNReal} (hf : Tendsto f l (𝓝 a))
    (hg : Tendsto g l (𝓝 b)) (hne : a ≠ b) :
    ∀ᶠ j in l, f j ≠ g j := by
  rcases lt_or_gt_of_ne hne with hab | hba
  · let q : NNReal := (a + b) / 2
    have haq : a < q := lt_midpoint hab
    have hqb : q < b := midpoint_lt hab
    filter_upwards [hf.eventually_lt_const haq,
      hg.eventually_const_lt hqb] with j hfj hgj heq
    exact (ne_of_lt (hfj.trans hgj)) heq
  · let q : NNReal := (b + a) / 2
    have hbq : b < q := lt_midpoint hba
    have hqa : q < a := midpoint_lt hba
    filter_upwards [hg.eventually_lt_const hbq,
      hf.eventually_const_lt hqa] with j hgj hfj heq
    exact (ne_of_lt (hgj.trans hfj)) heq.symm

/-- Different limiting excursions cannot be represented by the same finite
block eventually.  This uses their endpoint limits, independent of tie order. -/
theorem matched_blocks_eventually_distinct
    {ι : Type*} {l : Filter ι}
    {ns : ι → ℕ} {Gs : (j : ι) → Graph (ns j)}
    {z w : ι → ℕ × ℕ} {a b c d : NNReal}
    (hz : MatchedBlockSequence l ns Gs z a b)
    (hw : MatchedBlockSequence l ns Gs w c d)
    (hne : (a, b) ≠ (c, d)) :
    ∀ᶠ j in l, z j ≠ w j := by
  by_cases hac : a = c
  · have hbd : b ≠ d := by
      intro h
      exact hne (Prod.ext hac h)
    exact (eventually_ne_of_distinct_limits hz.2.2 hw.2.2 hbd).mono
      (fun j h heq => h (congrArg (fun v : ℕ × ℕ => meshTime (ns j) v.2) heq))
  · exact (eventually_ne_of_distinct_limits hz.2.1 hw.2.1 hac).mono
      (fun j h heq => h (congrArg (fun v : ℕ × ℕ => meshTime (ns j) v.1) heq))

/- B03 interface: one B02F witness per limiting excursion, unique among
all completed-block witnesses with those endpoint limits, and the converse
for every positive-length limit of completed blocks. -/
end

end Erdos745.WrapUp.Proofs.Internal.W15_CRITICAL_EndpointMatching
