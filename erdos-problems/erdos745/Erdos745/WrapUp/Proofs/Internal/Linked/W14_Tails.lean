module

public import Erdos745.WrapUp.Proofs.Internal.Linked.W14_Weak
public import Erdos745.WrapUp.Proofs.Internal.Linked.W14_Base
public import Mathlib.MeasureTheory.Measure.Portmanteau
public import Mathlib.MeasureTheory.Integral.Indicator
public import Mathlib.Topology.Order.Compact
public import Erdos745.WrapUp.Proofs.Internal.Linked.W14_Drift
public import Erdos745.WrapUp.Proofs.Internal.Linked.W14_Queue
public import Erdos745.WrapUp.Proofs.Internal.Linked.W01_Pruefer
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.WalkCounting
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.Order.Field.GeomSum

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local simp] Pi.div_def Pi.mul_def Pi.add_def Pi.sub_def Pi.neg_def Pi.inv_def Function.comp_def Pi.pow_def Pi.smul_def Real.rpow_eq_pow

@[expose] public section


/-! Escape, open descent events, and completion of the actual early BFS components. -/
namespace Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_CompletionTail

open Erdos745.WrapUp
open W14_EXPLORATION_PathWeak W14_EXPLORATION_Interpolation W14_EXPLORATION_FiniteLaw
open W14_EXPLORATION_Finite W14_EXPLORATION_QueueControl W14_EXPLORATION_TailsFinite
open W14_EXPLORATION_CriticalBudget W14_EXPLORATION_Drift
open Filter Topology MeasureTheory Set NNReal
open scoped ENNReal

noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1000000
local instance : MeasurableSpace BrownianPath := borel BrownianPath
local instance : BorelSpace BrownianPath := ⟨rfl⟩
local instance : MetricSpace BrownianPath := UniformSpace.metricSpace BrownianPath
local instance : TopologicalSpace (ProbabilityMeasure BrownianPath) :=
  ProbabilityMeasure.instTopologicalSpace

private theorem compact_interval (R : NNReal) : IsCompact (Icc 0 R) := by
  apply IsCompact.of_isClosed_subset (isCompact_closedBall (0 : NNReal) (R : ℝ)) isClosed_Icc
  intro x hx
  simpa [Metric.mem_closedBall, dist_nndist, NNReal.nndist_zero_eq_val'] using! hx.2

/-- Minimum on a compact time window in the actual compact-open path space. -/
def compactMinimum (R : NNReal) (w : BrownianPath) : ℝ :=
  sInf (w '' Icc 0 R)

theorem continuous_compactMinimum (R : NNReal) : Continuous (compactMinimum R) :=
  (compact_interval R).continuous_sInf continuous_eval

theorem compactMinimum_le (R : NNReal) (w : BrownianPath) (t : NNReal)
    (ht : t ≤ R) : compactMinimum R w ≤ w t :=
  csInf_le ((compact_interval R).image w.continuous).bddBelow
    (mem_image_of_mem w ⟨zero_le, ht⟩)

/-- Strict one-unit descent below all earlier compact-window values. -/
def descentEvent (R V : NNReal) : Set BrownianPath :=
  {w | w V < compactMinimum R w - 1}

theorem isOpen_descentEvent (R V : NNReal) : IsOpen (descentEvent R V) :=
  isOpen_lt (continuous_eval_const V) ((continuous_compactMinimum R).sub continuous_const)

/-- The pushforward of the supplied Brownian law, retaining that same witness. -/
def driftProbabilityLaw (mu : PathLaw) (hmu : BrownianLaw mu) (lam : ℝ) :
    ProbabilityMeasure BrownianPath := by
  letI : IsProbabilityMeasure mu := hmu.1
  exact ⟨Measure.map (fun w => driftPath w lam) mu,
    Measure.isProbabilityMeasure_map (continuous_driftPath lam).measurable.aemeasurable⟩

/-- B08's bounded-continuous law in the library's probability weak topology. -/
theorem critical_probability_tendsto (hfinite : FiniteEnumerationStatement)
    (M : NatSeq) (lam : ℝ) (hcritical : criticalWindow M lam)
    (mu : PathLaw) (hmu : BrownianLaw mu) :
    Tendsto (fun n => (⟨criticalPathLaw M n, inferInstance⟩ : ProbabilityMeasure BrownianPath))
      atTop (@nhds (ProbabilityMeasure BrownianPath) ProbabilityMeasure.instTopologicalSpace
        (driftProbabilityLaw mu hmu lam)) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro f
  have hw := critical_weakExploration hfinite M lam hcritical mu hmu f f.continuous
    ⟨‖f‖, fun w => by simpa only [Real.norm_eq_abs] using! f.norm_coe_le_norm w⟩
  change Tendsto (fun n => ∫ w, f w ∂criticalPathLaw M n) atTop
    (𝓝 (∫ w, f w ∂Measure.map (fun w => driftPath w lam) mu))
  rw [integral_map (continuous_driftPath lam).measurable.aemeasurable
    f.continuous.aestronglyMeasurable]
  apply hw.congr'
  filter_upwards [hcritical.1] with n hn
  rw [criticalPathLaw, dif_pos hn, explorationPathMeasure_integral n (M n) hn f f.continuous]

private theorem choose_descent_time (hfoundation : BrownianFoundationStatement)
    (mu : PathLaw) (hmu : BrownianLaw mu) (lam : ℝ) (R : NNReal)
    (d : ℝ) (hd : 0 < d) :
    ∃ V : ℕ, (R : ℝ) < V ∧
      ENNReal.ofReal (1 - d) < mu {w | driftPath w lam ∈ descentEvent R (V : NNReal)} := by
  letI : IsProbabilityMeasure mu := hmu.1
  let A : ℕ → Set BrownianPath := fun V =>
    {w | driftPath w lam ∈ descentEvent R (V : NNReal)}
  have hmeas (V : ℕ) : MeasurableSet (A V) :=
    ((isOpen_descentEvent R V).preimage (continuous_driftPath lam)).measurableSet
  have hae : ∀ᵐ w ∂mu, ∀ᶠ V : ℕ in atTop, w ∈ A V ↔ w ∈ (univ : Set BrownianPath) := by
    filter_upwards [(hfoundation.2 mu hmu lam).1] with w hw
    have hh : Tendsto (fun V : ℕ => drift w lam (V : NNReal)) atTop atBot :=
      hw.1.comp (NNReal.tendsto_coe_atTop.mp (by
        simpa only [NNReal.coe_natCast] using! (tendsto_natCast_atTop_atTop (R := ℝ))))
    have hb := tendsto_atBot.mp hh (compactMinimum R (driftPath w lam) - 2)
    filter_upwards [hb] with V hV
    simp only [A, mem_setOf_eq, mem_univ, iff_true, descentEvent]
    change drift w lam (V : NNReal) < compactMinimum R (driftPath w lam) - 1
    linarith
  have hlim : Tendsto (fun V => mu (A V)) atTop (𝓝 (1 : ℝ≥0∞)) := by
    simpa only [measure_univ] using!
      tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure atTop
        MeasurableSet.univ hmeas hae
  have hhigh : ∀ᶠ V in atTop, ENNReal.ofReal (1 - d) < mu (A V) :=
    hlim.eventually (lt_mem_nhds (ENNReal.ofReal_lt_one.mpr (by linarith)))
  have hlarge : ∀ᶠ V : ℕ in atTop, (R : ℝ) < V :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_gt_atTop _
  obtain ⟨V, hV, hmass⟩ := (hlarge.and hhigh).exists
  exact ⟨V, hV, hmass⟩

private theorem strict_drop_queue_empty {n : ℕ} (G : Graph n) (k : ℕ)
    (hk : k + 1 ≤ n) (hdrop : (explore G (k + 1)).walk < walkMinimum G k) :
    (explore G (k + 1)).queue = [] := by
  by_contra hq
  have hlen : 0 < (explore G (k + 1)).queue.length := List.length_pos_of_ne_nil hq
  have hm := walkMinimum_rootCount G k (by omega)
  have hw := walk_eq_queue_sub_rootCount G (k + 1)
  have hr := rootCount_succ G k
  by_cases hprev : (explore G k).queue = []
  · simp only [hprev, if_pos, add_zero] at hm
    by_cases hs : (explore G k).seen = Finset.univ
    · simp only [rootStarts, hprev, hs, ne_eq, not_true_eq_false, and_false, if_false, add_zero] at hr
      omega
    · simp only [rootStarts, hprev, hs, ne_eq, not_false_eq_true, and_self, if_true] at hr
      omega
  · simp [hprev] at hm
    simp only [rootStarts, hprev, false_and, if_false, add_zero] at hr
    omega

/-- A value below the early running minimum forces an empty queue before the deadline. -/
theorem low_walk_completes {n : ℕ} (G : Graph n) (j q k : ℕ)
    (hq : q ≤ n) (hkq : k ≤ q) (hlow : (explore G k).walk < walkMinimum G j) :
    ∃ r, j < r ∧ r ≤ q ∧ (explore G r).queue = [] := by
  have hex : ∃ r, (explore G r).walk < walkMinimum G j := ⟨k, hlow⟩
  let r := Nat.find hex
  have hr : (explore G r).walk < walkMinimum G j := Nat.find_spec hex
  have hrq : r ≤ q := (Nat.find_min' hex hlow).trans hkq
  have hjr : j < r := by
    by_contra h
    have hle := walkMinimum_le G (show r ≤ j by omega)
    omega
  have hr0 : 0 < r := by omega
  obtain ⟨i, hi, heq⟩ := walkMinimum_attained G (r - 1)
  have hprev : walkMinimum G j ≤ (explore G i).walk := by
    by_contra h
    have hlt : (explore G i).walk < walkMinimum G j := by omega
    have hri : r ≤ i := Nat.find_min' hex hlt
    omega
  have hdrop : (explore G r).walk < walkMinimum G (r - 1) := by omega
  have hqueue := strict_drop_queue_empty G (r - 1) (by omega)
    (by simpa only [Nat.sub_add_cancel hr0] using! hdrop)
  exact ⟨r, hjr, hrq, by simpa only [Nat.sub_add_cancel hr0] using! hqueue⟩

private theorem interpolation_mesh {n : ℕ} (G : Graph n) (k : ℕ)
    (ha : 0 < n23 n) :
    explorationInterpolation n G (NNReal.mk ((k : ℝ) / n23 n) (by positivity)) =
      ((explore G k).walk : ℝ) / n13 n := by
  rw [explorationInterpolation_isInterpolation]
  simp [rawExploration, NNReal.coe_mk, div_mul_cancel₀ _ (ne_of_gt ha), Nat.floor_natCast]

/-- The low affine value uses either endpoint, with one unit of time for floor slack. -/
theorem descent_completes {n : ℕ} (G : Graph n) (T : ℝ) (hT : 0 < T)
    (V : ℕ) (_hV : T + 1 < V) (ha : 1 ≤ n23 n) (hn : 0 < n)
    (hq : ⌊((V : ℝ) + 1) * n23 n⌋₊ ≤ n)
    (hdescent : explorationInterpolation n G ∈
      descentEvent ⟨T + 1, by linarith⟩ (V : NNReal)) :
    ¬ unfinishedEarly G T ((V : ℝ) + 1) := by
  let j := ⌊T * n23 n⌋₊
  let l := ⌊(V : ℝ) * n23 n⌋₊
  let q := ⌊((V : ℝ) + 1) * n23 n⌋₊
  have ha0 : 0 < n23 n := by linarith
  have hb : 0 < n13 n := Real.rpow_pos_of_pos (by exact_mod_cast hn) _
  obtain ⟨i, hij, hi⟩ := walkMinimum_attained G j
  let t : NNReal := NNReal.mk ((i : ℝ) / n23 n) (by positivity)
  have hicast : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
  have hit : (i : ℝ) ≤ T * n23 n :=
    hicast.trans (Nat.floor_le (by positivity))
  have ht : t ≤ (⟨T + 1, by linarith⟩ : NNReal) := by
    change (i : ℝ) / n23 n ≤ T + 1
    apply (div_le_iff₀ ha0).mpr
    nlinarith
  have hmin := compactMinimum_le ⟨T + 1, by linarith⟩ (explorationInterpolation n G) t ht
  dsimp only [t] at hmin
  rw [interpolation_mesh G i ha0] at hmin
  have hlow : explorationInterpolation n G (V : NNReal) <
      (walkMinimum G j : ℝ) / n13 n := by
    have hd : explorationInterpolation n G (V : NNReal) <
        compactMinimum ⟨T + 1, by linarith⟩ (explorationInterpolation n G) - 1 := hdescent
    rw [hi]
    linarith
  have hguard := horizon_endpoint_guard n (V : ℝ) (V : NNReal)
    (by positivity) (by simp) ha
  have hlq : l + 1 ≤ q := by simpa only [l, q, NNReal.coe_natCast] using! hguard.2
  let theta : ℝ := (V : ℝ) * n23 n - l
  have htheta0 : 0 ≤ theta := by
    dsimp [theta, l]
    exact sub_nonneg.mpr (Nat.floor_le (by positivity))
  have htheta1 : theta ≤ 1 := by
    dsimp [theta, l]
    have hf := Nat.lt_floor_add_one ((V : ℝ) * n23 n)
    linarith
  have haff : explorationInterpolation n G (V : NNReal) =
      ((1 - theta) * ((explore G l).walk : ℝ) +
        theta * ((explore G (l + 1)).walk : ℝ)) / n13 n := by
    rw [explorationInterpolation_isInterpolation]
    rfl
  have hend : (explore G l).walk < walkMinimum G j ∨
      (explore G (l + 1)).walk < walkMinimum G j := by
    by_contra h
    push_neg at h
    have h0 : (walkMinimum G j : ℝ) ≤ (explore G l).walk := by exact_mod_cast h.1
    have h1 : (walkMinimum G j : ℝ) ≤ (explore G (l + 1)).walk := by exact_mod_cast h.2
    have hm0 := mul_le_mul_of_nonneg_left h0 (show 0 ≤ 1 - theta by linarith)
    have hm1 := mul_le_mul_of_nonneg_left h1 htheta0
    rw [haff] at hlow
    have hlt := (div_lt_div_iff_of_pos_right hb).mp hlow
    nlinarith
  have hex : ∃ r, j < r ∧ r ≤ q ∧ (explore G r).queue = [] := by
    rcases hend with h | h
    · exact low_walk_completes G j q l hq (by omega) h
    · exact low_walk_completes G j q (l + 1) hq hlq h
  obtain ⟨r, hrj, hrq, hrqueue⟩ := hex
  exact queue_empty_between_not_unfinishedEarly G T ((V : ℝ) + 1) hrj.le hrq hrqueue

/-- The exact second tail, under the supplied foundation and the same Brownian law. -/
theorem unfinishedEarly_eventual_bound (hfinite : FiniteEnumerationStatement)
    (hfoundation : BrownianFoundationStatement) (M : NatSeq) (lam : ℝ)
    (hcritical : criticalWindow M lam) (mu : PathLaw) (hmu : BrownianLaw mu) :
    ∀ T d : ℝ, 0 < T → 0 < d → ∃ U : ℝ, T < U ∧
      ∀ᶠ n in atTop, probM n (M n) (fun G => unfinishedEarly G T U) ≤ d := by
  intro T d hT hd
  letI : IsProbabilityMeasure mu := hmu.1
  by_cases hd1 : 1 ≤ d
  · refine ⟨T + 1, by linarith, ?_⟩
    filter_upwards [hcritical.1] with n hn
    rw [← fixedMeasure_apply_toReal n (M n) hn]
    exact (measureReal_le_one (μ := fixedMeasure n (M n) hn)).trans hd1
  have hdlt : d < 1 := lt_of_not_ge hd1
  let R : NNReal := NNReal.mk (T + 1) (by linarith)
  obtain ⟨V, hV, hmass⟩ := choose_descent_time hfoundation mu hmu lam R (d / 2) (by positivity)
  let ν := driftProbabilityLaw mu hmu lam
  have hν : ENNReal.ofReal (1 - d) < (ν : PathLaw) (descentEvent R V) := by
    change ENNReal.ofReal (1 - d) < Measure.map (fun w => driftPath w lam) mu (descentEvent R V)
    rw [Measure.map_apply (continuous_driftPath lam).measurable (isOpen_descentEvent R V).measurableSet]
    exact (ENNReal.ofReal_lt_ofReal_iff (by linarith : 0 < 1 - d / 2)).mpr (by linarith) |>.trans hmass
  have hport := ProbabilityMeasure.le_liminf_measure_open_of_tendsto
    (critical_probability_tendsto hfinite M lam hcritical mu hmu) (isOpen_descentEvent R V)
  have hevent : ∀ᶠ n in atTop,
      ENNReal.ofReal (1 - d) < criticalPathLaw M n (descentEvent R V) :=
    eventually_lt_of_lt_liminf (hν.trans_le hport)
  have haevent : ∀ᶠ n : ℕ in atTop, 1 ≤ n23 n :=
    ((_root_.tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 3)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop 1
  have hbudget := eventually_eighth_horizon ((V : ℝ) + 1) (by positivity)
  refine ⟨(V : ℝ) + 1, by dsimp [R] at hV; linarith, ?_⟩
  filter_upwards [hevent, hcritical.1, haevent, hbudget, eventually_ge_atTop (1 : ℕ)]
    with n hmassn hM ha hnq hn
  let O := descentEvent R (V : NNReal)
  have hO : MeasurableSet O := (isOpen_descentEvent R V).measurableSet
  have hgood : 1 - d < (criticalPathLaw M n O).toReal :=
    (ENNReal.ofReal_lt_iff_lt_toReal (by linarith) (measure_ne_top _ _)).mp hmassn
  have hbad : (criticalPathLaw M n Oᶜ).toReal ≤ d := by
    have hsum := measureReal_add_measureReal_compl (μ := criticalPathLaw M n) hO
    simp only [measureReal_def, measure_univ, ENNReal.toReal_one] at hsum
    linarith
  have hpath : (criticalPathLaw M n Oᶜ).toReal =
      probM n (M n) (fun G => explorationInterpolation n G ∉ O) := by
    rw [criticalPathLaw, dif_pos hM]
    unfold explorationPathMeasure
    rw [Measure.map_apply (measurable_explorationInterpolation n) hO.compl]
    exact fixedMeasure_apply_toReal n (M n) hM _
  have hsubset : {G : Graph n | unfinishedEarly G T ((V : ℝ) + 1)} ⊆
      {G : Graph n | explorationInterpolation n G ∉ O} := by
    intro G hG hmem
    exact descent_completes G T hT V hV ha (by omega) (by omega) hmem hG
  have hmono := measure_mono (μ := fixedMeasure n (M n) hM) hsubset
  have htoreal := ENNReal.toReal_mono (measure_ne_top _ _) hmono
  simp only [fixedMeasure_apply_toReal] at htoreal
  rw [← hpath] at htoreal
  exact htoreal.trans hbad

end
end Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_CompletionTail


/-! Neutral paths are conditioned on the *whole* realized reveal atom.  The
all-positive hypergeometric law, rather than independent edge trials, bounds
each simple path.  The exceptional pool event is retained through averaging. -/
namespace Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_LateTail

open Erdos745.WrapUp
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_Finite
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_Reveal
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_Conditional
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_FiniteHorizon
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_FiniteAtoms
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_PoolUniform
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_Horizon
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_CriticalBudget
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_PoolConcentration
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_QueueControl
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_Drift
open Erdos745.WrapUp.Proofs.Internal.W01_ENUM_Pruefer
open Filter
open scoped BigOperators Topology Sym2

noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local simp] Pi.div_def Pi.mul_def Pi.add_def Pi.sub_def Pi.neg_def Pi.inv_def Function.comp_def

/-- The original vertices not yet discovered by the original BFS. -/
def neutralVertices {n : ℕ} (G : Graph n) (j : ℕ) : Finset (Fin n) :=
  Finset.univ \ (explore G j).seen

/-- An arbitrary neutral edge query is fresh, not just the next BFS query. -/
theorem neutral_edges_unrevealed {n : ℕ} (G : Graph n) (j : ℕ)
    (query : Graph n)
    (hquery : ∀ e ∈ query, e.val.1 ∈ neutralVertices G j ∧
      e.val.2 ∈ neutralVertices G j) :
    Disjoint query ((revealTrace G j).yes ∪ (revealTrace G j).no) := by
  apply Finset.disjoint_left.mpr
  intro e heq hea
  have ht := answeredEdges_subset_edgesTouching_processed G j hea
  rw [mem_edgesTouching_iff] at ht
  have he := hquery e heq
  have h1 := (Finset.mem_sdiff.mp he.1).2
  have h2 := (Finset.mem_sdiff.mp he.2).2
  exact ht.elim (fun h => h1 (processed_subset_seen G j h))
    (fun h => h2 (processed_subset_seen G j h))

theorem neutral_card_add {n : ℕ} (G : Graph n) (j : ℕ) (hj : j ≤ n) :
    (neutralVertices G j).card + j + (explore G j).queue.length = n := by
  have hp := processed_card_add_queue_length G j
  rw [processed_card_of_le G j hj] at hp
  have hs := Finset.card_sdiff_add_card_eq_card
    (Finset.subset_univ (explore G j).seen)
  simpa [neutralVertices, hp, Nat.add_assoc] using! hs

theorem neutral_card_le {n : ℕ} (G : Graph n) (j : ℕ) (hj : j ≤ n) :
    ((neutralVertices G j).card : ℝ) ≤ (n : ℝ) - j := by
  have h := neutral_card_add G j hj
  have hh : (neutralVertices G j).card + j ≤ n := by omega
  exact_mod_cast (show (neutralVertices G j).card ≤ n - j by omega)

private theorem average_indicator {n M : ℕ} (hM : M ≤ capacity n)
    (G : Graph n) (j : ℕ) (hG : G.card = M) (A : Graph n → Prop) :
    historyAverage M G j (fun H => if A H then 1 else 0) =
      conditionalProbM n M (fun H => revealTrace H j = revealTrace G j) A := by
  have hF : ((fixedGraphs n M).card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_ne_zero.mpr
      (Erdos745.WrapUp.Proofs.Internal.W01_ENUM_Finite.fixedGraphs_nonempty hM))
  have hA : ((historyAtom M G j).card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_ne_zero.mpr (historyAtom_nonempty G j hG))
  unfold historyAverage conditionalProbM probM
  rw [Finset.sum_boole]
  have heq : ((historyAtom M G j).filter A) =
      (fixedGraphs n M).filter
        (fun H => revealTrace H j = revealTrace G j ∧ A H) := by
    ext H
    simp [historyAtom, and_assoc]
  rw [heq]
  change _ / ((historyAtom M G j).card : ℝ) =
    (_ / ((fixedGraphs n M).card : ℝ)) /
      (((historyAtom M G j).card : ℝ) / ((fixedGraphs n M).card : ℝ))
  field_simp

private theorem query_card_le_pool {n : ℕ} (G : Graph n) (j : ℕ)
    (q : Graph n) (hfresh : Disjoint q
      ((revealTrace G j).yes ∪ (revealTrace G j).no)) :
    q.card ≤ poolEdgeCount G j := by
  have hcard := Finset.card_union_of_disjoint hfresh.symm
  have hcap : (((revealTrace G j).yes ∪ (revealTrace G j).no) ∪ q).card ≤ capacity n := by
    calc
      _ ≤ (Finset.univ : Finset (Edge n)).card := Finset.card_le_card (Finset.subset_univ _)
      _ = capacity n := by simp [Erdos745.WrapUp.Proofs.Internal.W01_ENUM_Finite.card_edge]
  unfold poolEdgeCount answeredCount
  omega

/-- Exact conditional law on every positive realized atom, for any fresh query. -/
theorem conditional_neutral_query_eq_hypergeom
    (hfinite : FiniteEnumerationStatement) {n M : ℕ} (hM : M ≤ capacity n)
    (G : Graph n) (j : ℕ) (hG : G.card = M) (q : Graph n)
    (hfresh : Disjoint q ((revealTrace G j).yes ∪ (revealTrace G j).no)) :
    conditionalProbM n M (fun H => revealTrace H j = revealTrace G j)
      (fun H => q ⊆ H) =
      hypergeomMass (poolEdgeCount G j) (poolSuccessCount M G j) q.card q.card := by
  have hfiber : (fun H : Graph n => revealTrace H j = revealTrace G j) =
      patternEvent (revealTrace G j).yes (revealTrace G j).no := by
    funext H
    exact propext (history_fiber_eq_patternEvent G H j)
  have hpos := historyAtom_probability_pos G j hG
  rw [hfiber] at hpos ⊢
  have hevent : (fun H : Graph n => q ⊆ H) =
      (fun H => (H ∩ q).card = q.card) := by
    funext H
    apply propext
    constructor
    · intro h
      rw [Finset.inter_eq_right.mpr h]
    · intro h
      exact Finset.inter_eq_right.mp
        (Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by omega))
  rw [hevent]
  have hlaw := hfinite.2.1 n M (revealTrace G j).yes (revealTrace G j).no
    q hM (revealTrace_yes_no_disjoint G j) hfresh hpos q.card
  simpa [poolEdgeCount, answeredCount, poolSuccessCount,
    Finset.card_union_of_disjoint (revealTrace_yes_no_disjoint G j), Nat.sub_sub] using! hlaw

/-- The falling-factorial ratio includes the zero case when there are too few successes. -/
theorem hypergeom_all_positive_eq_ratio (E R l : ℕ) (hR : R ≤ E) (hl : l ≤ E) :
    hypergeomMass E R l l = (R.descFactorial l : ℝ) / (E.descFactorial l : ℝ) := by
  simp only [hypergeomMass, hR, hl, le_refl, and_self, if_true,
    Nat.sub_self, Nat.choose_zero_right, Nat.cast_one, mul_one]
  rw [Nat.descFactorial_eq_factorial_mul_choose,
    Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul, Nat.cast_mul]
  have hf : (l.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero l
  field_simp

private theorem factorial_ratio_le_pow (E R l : ℕ)
    (hE : 0 < E) (hR : R ≤ E) (hl : l ≤ E) :
    (R.descFactorial l : ℝ) / (E.descFactorial l : ℝ) ≤
      ((R : ℝ) / E) ^ l := by
  induction l with
  | zero => simp
  | succ l ih =>
      by_cases hRl : l + 1 ≤ R
      · have hlE : l < E := by omega
        have hlR : l ≤ R := by omega
        have hEl : (0 : ℝ) < (E - l : ℕ) := by exact_mod_cast (by omega : 0 < E - l)
        have hEr : (0 : ℝ) < E := by exact_mod_cast hE
        have hfac : (0 : ℝ) < E.descFactorial l := by
          exact_mod_cast (Nat.descFactorial_pos.mpr (by omega : l ≤ E))
        have hf : ((R - l : ℕ) : ℝ) / ((E - l : ℕ) : ℝ) ≤ (R : ℝ) / E := by
          rw [div_le_div_iff₀ hEl hEr, Nat.cast_sub hlR,
            Nat.cast_sub (by omega : l ≤ E)]
          have hh : (R : ℝ) ≤ E := by exact_mod_cast hR
          have hl0 : (0 : ℝ) ≤ l := Nat.cast_nonneg _
          nlinarith
        have heq : (R.descFactorial (l + 1) : ℝ) /
            (E.descFactorial (l + 1) : ℝ) =
            (((R - l : ℕ) : ℝ) / ((E - l : ℕ) : ℝ)) *
              ((R.descFactorial l : ℝ) / (E.descFactorial l : ℝ)) := by
          rw [Nat.descFactorial_succ, Nat.descFactorial_succ, Nat.cast_mul, Nat.cast_mul]
          field_simp
        rw [heq, pow_succ]
        calc
          _ ≤ (((R - l : ℕ) : ℝ) / ((E - l : ℕ) : ℝ)) * ((R : ℝ) / E) ^ l :=
            mul_le_mul_of_nonneg_left (ih (by omega)) (by positivity)
          _ ≤ ((R : ℝ) / E) * ((R : ℝ) / E) ^ l :=
            mul_le_mul_of_nonneg_right hf (pow_nonneg (by positivity) l)
          _ = _ := by ring
      · rw [Nat.descFactorial_eq_zero_iff_lt.mpr (by omega : R < l + 1)]
        simp only [Nat.cast_zero, zero_div]
        positivity

theorem conditional_prescribed_path_bound
    (hfinite : FiniteEnumerationStatement) {n M : ℕ} (hM : M ≤ capacity n)
    (G : Graph n) (j : ℕ) (hG : G.card = M) (hE : 0 < poolEdgeCount G j)
    (q : Graph n)
    (hfresh : Disjoint q ((revealTrace G j).yes ∪ (revealTrace G j).no)) :
    historyAverage M G j (fun H => if q ⊆ H then 1 else 0) ≤
      poolDensity M G j ^ q.card := by
  have havg : historyAverage M G j (fun H => if q ⊆ H then 1 else 0) =
      conditionalProbM n M (fun H => revealTrace H j = revealTrace G j) (fun H => q ⊆ H) := by
    convert average_indicator hM G j hG (fun H => q ⊆ H) using 1
    apply congrArg (historyAverage M G j)
    funext H
    by_cases h : q ⊆ H <;> simp [h]
  rw [havg,
    conditional_neutral_query_eq_hypergeom hfinite hM G j hG q hfresh,
    hypergeom_all_positive_eq_ratio _ _ _ (poolSuccessCount_le_poolEdgeCount G j hG)
      (query_card_le_pool G j q hfresh)]
  exact factorial_ratio_le_pow _ _ _ hE (poolSuccessCount_le_poolEdgeCount G j hG)
    (query_card_le_pool G j q hfresh)

/-! Finite simple-path enumeration on the neutral vertex subtype. -/

def neutralGraph {n : ℕ} (N : Finset (Fin n)) (H : Graph n) : SimpleGraph N where
  Adj u v := adj H u.val v.val
  symm := ⟨fun _ _ h => adj_symmetric H h⟩
  loopless := ⟨fun u => W01_ENUM_Trees.adj_irrefl H u.val⟩

def neutralComponent {n : ℕ} (N : Finset (Fin n)) (H : Graph n) (u : N) : Finset N :=
  Finset.univ.filter (fun v => (neutralGraph N H).Reachable u v)

def neutralSquareMass {n : ℕ} (N : Finset (Fin n)) (H : Graph n) : ℝ :=
  ∑ u : N, ((neutralComponent N H u).card : ℝ)

abbrev NeutralPath {n : ℕ} (N : Finset (Fin n)) (u : N) :=
  Σ v : N, (⊤ : SimpleGraph N).Path u v

private def neutralEmbedding {n : ℕ} (N : Finset (Fin n)) :
    (⊤ : SimpleGraph N) →g (⊤ : SimpleGraph (Fin n)) where
  toFun := Subtype.val
  map_rel' := by
    intro u v h
    exact fun heq => h (Subtype.ext heq)

private def pathWalk {n : ℕ} {N : Finset (Fin n)} {u : N} (p : NeutralPath N u) :=
  p.2.val.map (neutralEmbedding N)

/-- The distinct unordered original edges of a prescribed neutral simple path. -/
def pathQuery {n : ℕ} {N : Finset (Fin n)} {u : N} (p : NeutralPath N u) : Graph n :=
  Finset.univ.filter (fun e => edgeSym2 e ∈ (pathWalk p).edges)

private theorem edgeSym2_edgeOf {n : ℕ} (u v : Fin n) (h : u ≠ v) :
    edgeSym2 (edgeOf u v h) = s(u, v) := by
  unfold edgeOf edgeSym2
  split
  · rfl
  · exact Sym2.eq_swap

private theorem walk_query_card {n : ℕ} {u v : Fin n}
    (w : (⊤ : SimpleGraph (Fin n)).Walk u v) (hw : w.IsPath) :
    (Finset.univ.filter (fun e : Edge n => edgeSym2 e ∈ w.edges)).card = w.length := by
  calc
    _ = w.edges.toFinset.card := by
      apply Finset.card_bij (fun e _ => edgeSym2 e)
      · intro e he
        exact List.mem_toFinset.mpr (Finset.mem_filter.mp he).2
      · intro e _ f _ hef
        exact edgeSym2_injective hef
      · intro b hb
        induction b using Sym2.inductionOn with
        | _ x y =>
          have hmem := List.mem_toFinset.mp hb
          have hne : x ≠ y := w.adj_of_mem_edges hmem
          refine ⟨edgeOf x y hne, ?_, edgeSym2_edgeOf x y hne⟩
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          simpa [edgeSym2_edgeOf] using! hmem
    _ = w.edges.length := List.toFinset_card_of_nodup hw.isTrail.edges_nodup
    _ = w.length := w.length_edges

theorem pathQuery_card {n : ℕ} {N : Finset (Fin n)} {u : N} (p : NeutralPath N u) :
    (pathQuery p).card = p.2.val.length := by
  exact (walk_query_card (pathWalk p)
    (SimpleGraph.Walk.map_isPath_of_injective Subtype.val_injective p.2.property)).trans
      (SimpleGraph.Walk.length_map _ _)

theorem pathQuery_neutral {n : ℕ} {N : Finset (Fin n)} {u : N}
    (p : NeutralPath N u) (e : Edge n) (he : e ∈ pathQuery p) :
    e.val.1 ∈ N ∧ e.val.2 ∈ N := by
  have hm := (Finset.mem_filter.mp he).2
  have h1 := (pathWalk p).fst_mem_support_of_mem_edges hm
  have h2 := (pathWalk p).snd_mem_support_of_mem_edges hm
  rw [pathWalk, SimpleGraph.Walk.support_map] at h1 h2
  obtain ⟨v, _, hv⟩ := List.mem_map.mp h1
  obtain ⟨w, _, hw⟩ := List.mem_map.mp h2
  exact ⟨hv ▸ v.property, hw ▸ w.property⟩

private theorem pathQuery_subset_of_edges {n : ℕ} {N : Finset (Fin n)} {u : N}
    (p : NeutralPath N u) (H : Graph n)
    (h : ∀ x y : N, s(x, y) ∈ p.2.val.edges → adj H x.val y.val) :
    pathQuery p ⊆ H := by
  intro e he
  have hm := (Finset.mem_filter.mp he).2
  rw [pathWalk, SimpleGraph.Walk.edges_map] at hm
  obtain ⟨b, hb, hbe⟩ := List.mem_map.mp hm
  induction b using Sym2.inductionOn with
  | _ x y =>
    have hadj := h x y hb
    obtain ⟨f, hf, hend⟩ := hadj
    have hfe : edgeSym2 f = s(x.val, y.val) := by
      rcases hend with hend | hend
      · simp [edgeSym2, hend.1, hend.2]
      · unfold edgeSym2
        rw [hend.1, hend.2]
        exact Sym2.eq_swap
    have hsame : edgeSym2 f = edgeSym2 e := hfe.trans hbe
    exact edgeSym2_injective hsame ▸ hf

private theorem reachable_path_query {n : ℕ} {N : Finset (Fin n)} {H : Graph n}
    {u v : N} (h : (neutralGraph N H).Reachable u v) :
    ∃ p : (⊤ : SimpleGraph N).Path u v, pathQuery ⟨v, p⟩ ⊆ H := by
  obtain ⟨w, hw⟩ := h.exists_isPath
  let p : (⊤ : SimpleGraph N).Path u v :=
    ⟨w.mapLe le_top, hw.mapLe le_top⟩
  refine ⟨p, pathQuery_subset_of_edges ⟨v, p⟩ H ?_⟩
  intro x y he
  have hm : s(x, y) ∈ w.edges := by
    simpa [p, SimpleGraph.Walk.edges_mapLe_eq_edges] using! he
  exact w.adj_of_mem_edges hm

private theorem path_tail_injective {n : ℕ} {N : Finset (Fin n)} {u : N} :
    Function.Injective (fun p : NeutralPath N u => p.2.val.support.tail) := by
  rintro ⟨v, p⟩ ⟨w, q⟩ h
  change p.val.support.tail = q.val.support.tail at h
  have hs : p.val.support = q.val.support := by
    rw [p.val.support_eq_cons, q.val.support_eq_cons, h]
  have hvw : v = w := by
    simpa using! List.getLast_congr p.val.support_ne_nil q.val.support_ne_nil hs
  subst w
  have hpq : p = q := Subtype.ext (SimpleGraph.Walk.support_injective hs)
  subst q
  rfl

private theorem path_length_count {n : ℕ} {N : Finset (Fin n)} (u : N) (l : ℕ) :
    ((Finset.univ : Finset (NeutralPath N u)).filter
      (fun p => p.2.val.length = l)).card ≤ N.card ^ l := by
  let s := (Finset.univ : Finset (NeutralPath N u)).filter (fun p => p.2.val.length = l)
  let f := fun p : NeutralPath N u => p.2.val.support.tail
  have hlen : ∀ p ∈ s, (f p).length = l := by
    intro p hp
    have hh := (Finset.mem_filter.mp hp).2
    dsimp [f]
    rw [List.length_tail, SimpleGraph.Walk.length_support, hh]
    omega
  have hsub : s.image f ⊆ ((s.image f).filter (fun a => a.length = l)) := by
    intro a ha
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ha
    exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨p, hp, rfl⟩, hlen p hp⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective s path_tail_injective] at hcard
  exact hcard.trans (by simpa using!
    (Finset.card_filter_length_eq_le (T := s.image f) (s := l)))

private theorem path_power_sum {n : ℕ} {N : Finset (Fin n)} (u : N)
    (p : ℝ) (hp : 0 ≤ p) :
    (∑ q : NeutralPath N u, p ^ q.2.val.length) ≤
      ∑ l ∈ Finset.range N.card, ((N.card : ℝ) * p) ^ l := by
  have hmaps : ∀ q ∈ (Finset.univ : Finset (NeutralPath N u)),
      q.2.val.length ∈ Finset.range N.card := by
    intro q _
    simpa using! q.2.property.length_lt
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  apply Finset.sum_le_sum
  intro l hl
  calc
    (∑ q ∈ (Finset.univ : Finset (NeutralPath N u)) with q.2.val.length = l,
      p ^ q.2.val.length) =
      (((Finset.univ : Finset (NeutralPath N u)).filter
        (fun q => q.2.val.length = l)).card : ℝ) * p ^ l := by
      calc
        _ = ∑ q ∈ (Finset.univ : Finset (NeutralPath N u)) with q.2.val.length = l, p ^ l := by
          apply Finset.sum_congr rfl
          intro q hq
          rw [(Finset.mem_filter.mp hq).2]
        _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (N.card : ℝ) ^ l * p ^ l := by
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg hp l)
      exact_mod_cast path_length_count u l
    _ = ((N.card : ℝ) * p) ^ l := (mul_pow _ _ _).symm

/-- Finite neutral susceptibility; all edge dependence remains in the atom law. -/
theorem conditional_neutral_susceptibility
    (hfinite : FiniteEnumerationStatement) {n M : ℕ} (hM : M ≤ capacity n)
    (G : Graph n) (j : ℕ) (hG : G.card = M) (hE : 0 < poolEdgeCount G j)
    (u : neutralVertices G j)
    (hsub : ((neutralVertices G j).card : ℝ) * poolDensity M G j < 1) :
    historyAverage M G j (fun H =>
      ((neutralComponent (neutralVertices G j) H u).card : ℝ)) ≤
      1 / (1 - ((neutralVertices G j).card : ℝ) * poolDensity M G j) := by
  let N := neutralVertices G j
  let p := poolDensity M G j
  have hp : 0 ≤ p := by dsimp [p, poolDensity]; positivity
  have hcover (H : Graph n) :
      ((neutralComponent N H u).card : ℝ) ≤
        ∑ q : NeutralPath N u, if pathQuery q ⊆ H then (1 : ℝ) else 0 := by
    rw [Fintype.sum_sigma]
    rw [neutralComponent, ← Finset.sum_boole]
    apply Finset.sum_le_sum
    intro v _
    by_cases hr : (neutralGraph N H).Reachable u v
    · obtain ⟨q, hq⟩ := reachable_path_query hr
      rw [if_pos hr]
      calc
        (1 : ℝ) = (if pathQuery ⟨v, q⟩ ⊆ H then 1 else 0) := by simp [hq]
        _ ≤ ∑ r : (⊤ : SimpleGraph N).Path u v,
            if pathQuery ⟨v, r⟩ ⊆ H then 1 else 0 :=
          Finset.single_le_sum
            (f := fun r : (⊤ : SimpleGraph N).Path u v =>
              if pathQuery ⟨v, r⟩ ⊆ H then (1 : ℝ) else 0)
            (fun r _ => by split_ifs <;> norm_num) (Finset.mem_univ q)
    · simp only [if_neg hr]
      exact Finset.sum_nonneg (fun _ _ => by positivity)
  have hsum := Finset.sum_le_sum (fun H (_ : H ∈ historyAtom M G j) => hcover H)
  have hden : (0 : ℝ) < (historyAtom M G j).card := by
    exact_mod_cast Finset.card_pos.mpr (historyAtom_nonempty G j hG)
  unfold historyAverage
  calc
    _ ≤ (∑ H ∈ historyAtom M G j,
        ∑ q : NeutralPath N u, if pathQuery q ⊆ H then (1 : ℝ) else 0) /
          (historyAtom M G j).card := div_le_div_of_nonneg_right hsum hden.le
    _ = ∑ q : NeutralPath N u, historyAverage M G j
        (fun H => if pathQuery q ⊆ H then 1 else 0) := by
      rw [Finset.sum_comm, Finset.sum_div]
      rfl
    _ ≤ ∑ q : NeutralPath N u, p ^ q.2.val.length := by
      apply Finset.sum_le_sum
      intro q _
      have hf := neutral_edges_unrevealed G j (pathQuery q) (pathQuery_neutral q)
      simpa [p, pathQuery_card] using!
        conditional_prescribed_path_bound hfinite hM G j hG hE (pathQuery q) hf
    _ ≤ ∑ l ∈ Finset.range N.card, ((N.card : ℝ) * p) ^ l := path_power_sum u p hp
    _ ≤ 1 / (1 - (N.card : ℝ) * p) := by
      have hg := geom_sum_mul_neg ((N.card : ℝ) * p) N.card
      apply (le_div_iff₀ (sub_pos.mpr hsub)).mpr
      rw [hg]
      have hpow := pow_nonneg (mul_nonneg (Nat.cast_nonneg N.card) hp) N.card
      linarith

theorem conditional_neutral_square_bound
    (hfinite : FiniteEnumerationStatement) {n M : ℕ} (hM : M ≤ capacity n)
    (G : Graph n) (j : ℕ) (hG : G.card = M) (hE : 0 < poolEdgeCount G j)
    (hsub : ((neutralVertices G j).card : ℝ) * poolDensity M G j < 1) :
    historyAverage M G j (neutralSquareMass (neutralVertices G j)) ≤
      (n : ℝ) / (1 - ((neutralVertices G j).card : ℝ) * poolDensity M G j) := by
  let N := neutralVertices G j
  have hsum := Finset.sum_le_sum (fun u (_ : u ∈ (Finset.univ : Finset N)) =>
    conditional_neutral_susceptibility hfinite hM G j hG hE u hsub)
  have hN : (N.card : ℝ) ≤ n := by
    have hh : N.card ≤ n := by simpa using! Finset.card_le_card (Finset.subset_univ N)
    exact_mod_cast hh
  calc
    _ = ∑ u : N, historyAverage M G j
      (fun H => ((neutralComponent N H u).card : ℝ)) := by
        unfold historyAverage neutralSquareMass
        rw [Finset.sum_comm, Finset.sum_div]
    _ ≤ ∑ _u : N, 1 / (1 - (N.card : ℝ) * poolDensity M G j) := hsum
    _ = (N.card : ℝ) / (1 - (N.card : ℝ) * poolDensity M G j) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
      ring
    _ ≤ (n : ℝ) / (1 - (N.card : ℝ) * poolDensity M G j) :=
      div_le_div_of_nonneg_right hN (sub_pos.mpr hsub).le

private theorem component_neutral_reachable {n : ℕ} (N : Finset (Fin n))
    (H : Graph n) (u : N) (hc : componentOf H u.val ⊆ N) :
    ∀ {v : Fin n} (_h : reach H u.val v) (hv : v ∈ N),
      (neutralGraph N H).Reachable u ⟨v, hv⟩ := by
  intro v h
  induction h with
  | refl => intro hv; exact ⟨SimpleGraph.Walk.nil⟩
  | @tail v w h hvw ih =>
    intro hw
    have hv : v ∈ N := hc ((mem_componentOf_iff H u.val v).mpr h)
    have hadj : (neutralGraph N H).Adj ⟨v, hv⟩ ⟨w, hw⟩ := hvw
    exact (ih hv).trans ⟨SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil⟩

/-- Every original component disjoint from seen lies in one neutral component. -/
theorem late_component_subset_neutral_component {n : ℕ}
    (H : Graph n) (j : ℕ) (S : Finset (Fin n)) (hS : S ∈ components H)
    (hdis : Disjoint S (explore H j).seen) (v : neutralVertices H j) (hv : v.val ∈ S) :
    S ⊆ (neutralComponent (neutralVertices H j) H v).image Subtype.val := by
  have hN : S ⊆ neutralVertices H j := by
    intro x hx
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, Finset.disjoint_left.mp hdis hx⟩
  obtain ⟨r, hr⟩ := mem_components_iff H S |>.mp hS
  have hrv : reach H r v.val := (mem_componentOf_iff H r v.val).mp (hr ▸ hv)
  have hvS : componentOf H v.val = S := (componentOf_eq_of_reach hrv).symm.trans hr
  intro w hw
  have hwN := hN hw
  refine Finset.mem_image.mpr ⟨⟨w, hwN⟩, ?_, rfl⟩
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  exact component_neutral_reachable _ H v (hvS ▸ hN)
    ((mem_componentOf_iff H v.val w).mp (hvS ▸ hw)) hwN

private theorem neutral_mass_ge_component_square {n : ℕ}
    (H : Graph n) (j : ℕ) (S : Finset (Fin n)) (hS : S ∈ components H)
    (hdis : Disjoint S (explore H j).seen) :
    (S.card : ℝ) ^ 2 ≤ neutralSquareMass (neutralVertices H j) H := by
  let N := neutralVertices H j
  let V : Finset N := Finset.univ.filter (fun v => v.val ∈ S)
  have hN : S ⊆ N := by
    intro v hv
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, Finset.disjoint_left.mp hdis hv⟩
  have hV : V.card = S.card := by
    apply Finset.card_bij (fun v _ => v.val)
    · intro v hv; exact (Finset.mem_filter.mp hv).2
    · intro v _ w _ h; exact Subtype.ext h
    · intro w hw
      exact ⟨⟨w, hN hw⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw⟩, rfl⟩
  have hbound : ∀ v ∈ V,
      (S.card : ℝ) ≤ (neutralComponent N H v).card := by
    intro v hv
    have hh := late_component_subset_neutral_component H j S hS hdis v
      (Finset.mem_filter.mp hv).2
    have hc := Finset.card_le_card hh
    rw [Finset.card_image_of_injective _ Subtype.val_injective] at hc
    exact_mod_cast hc
  calc
    (S.card : ℝ) ^ 2 = ∑ _v ∈ V, (S.card : ℝ) := by rw [Finset.sum_const, hV]; simp [pow_two]
    _ ≤ ∑ v ∈ V, ((neutralComponent N H v).card : ℝ) := Finset.sum_le_sum hbound
    _ ≤ ∑ v : N, ((neutralComponent N H v).card : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ V) (fun _ _ _ => by positivity)
    _ = neutralSquareMass N H := rfl

/-- This is literally the sum of squared neutral component orders. -/
private theorem seen_on_history {n : ℕ} (G H : Graph n) (j : ℕ)
    (h : revealTrace H j = revealTrace G j) : explore H j = explore G j := by
  simpa [revealTrace_bfs] using! congrArg RevealState.bfs h

/-- Conditional Markov on a good positive atom, with the stronger constant two. -/
theorem conditional_lateLarge_bound
    (hfinite : FiniteEnumerationStatement) {n M : ℕ} (hM : M ≤ capacity n)
    (G : Graph n) (hG : G.card = M) (hn : 0 < n) (eta T g : ℝ)
    (heta : 0 < eta) (hg : 0 < g)
    (hE : 0 < poolEdgeCount G ⌊T * n23 n⌋₊)
    (hgap : ((neutralVertices G ⌊T * n23 n⌋₊).card : ℝ) *
      poolDensity M G ⌊T * n23 n⌋₊ ≤ 1 - g / (2 * n13 n)) :
    historyAverage M G ⌊T * n23 n⌋₊
      (fun H => if lateLarge H T eta then 1 else 0) ≤ 2 / (eta ^ 2 * g) := by
  let j := ⌊T * n23 n⌋₊
  let N := neutralVertices G j
  let b := n13 n
  let a := n23 n
  let θ := (eta * a) ^ 2
  have hb : 0 < b := by
    dsimp [b, n13]
    exact Real.rpow_pos_of_pos (by exact_mod_cast hn) _
  have ha : 0 < a := n23_pos n hn
  have hθ : 0 < θ := pow_pos (mul_pos heta ha) _
  have hden : 0 < 1 - (N.card : ℝ) * poolDensity M G j := by
    have h : 0 < g / (2 * b) := div_pos hg (mul_pos (by norm_num) hb)
    change (N.card : ℝ) * poolDensity M G j ≤ 1 - g / (2 * b) at hgap
    linarith
  have hsub : (N.card : ℝ) * poolDensity M G j < 1 := by linarith
  have hs := conditional_neutral_square_bound hfinite hM G j hG hE hsub
  have hgeom : (n : ℝ) / (1 - (N.card : ℝ) * poolDensity M G j) ≤
      2 * b ^ 4 / g := by
    have hl : g / (2 * b) ≤ 1 - (N.card : ℝ) * poolDensity M G j := by linarith [hgap]
    have hh := div_le_div_of_nonneg_left (Nat.cast_nonneg n)
      (div_pos hg (mul_pos (by norm_num) hb)) hl
    have hcub : b ^ 3 = (n : ℝ) := n13_cube n hn
    calc
      _ ≤ (n : ℝ) / (g / (2 * b)) := hh
      _ = 2 * b ^ 4 / g := by rw [← hcub]; field_simp
  have hmass : historyAverage M G j (neutralSquareMass N) ≤ 2 * b ^ 4 / g := hs.trans hgeom
  have hpoint : ∀ H ∈ historyAtom M G j,
      θ * (if lateLarge H T eta then 1 else 0) ≤ neutralSquareMass N H := by
    intro H hH
    have ht := (Finset.mem_filter.mp hH).2
    have hseen := seen_on_history G H j ht
    by_cases hlate : lateLarge H T eta
    · simp only [if_pos hlate, mul_one]
      obtain ⟨S, hS, hdis, hsize⟩ := hlate
      have hsq : θ ≤ (S.card : ℝ) ^ 2 := by
        dsimp [θ, a]
        nlinarith [mul_pos heta ha]
      have hmassH := neutral_mass_ge_component_square H j S hS hdis
      have hN : neutralVertices H j = N := by simp [neutralVertices, hseen, N]
      rw [hN] at hmassH
      exact hsq.trans hmassH
    · simp only [if_neg hlate, mul_zero]
      unfold neutralSquareMass
      exact Finset.sum_nonneg (fun _ _ => by positivity)
  have hsum := Finset.sum_le_sum hpoint
  have hcard : (0 : ℝ) < (historyAtom M G j).card := by
    exact_mod_cast Finset.card_pos.mpr (historyAtom_nonempty G j hG)
  have hmarkov : θ * historyAverage M G j
      (fun H => if lateLarge H T eta then 1 else 0) ≤ 2 * b ^ 4 / g := by
    have hh := div_le_div_of_nonneg_right hsum hcard.le
    rw [← Finset.mul_sum] at hh
    have hh' : θ * historyAverage M G j
        (fun H => if lateLarge H T eta then 1 else 0) ≤ historyAverage M G j (neutralSquareMass N) := by
      simpa only [historyAverage, mul_div_assoc] using! hh
    exact hh'.trans hmass
  have haeq : a = b ^ 2 := n23_eq_n13_square n hn
  have hid : (2 / (eta ^ 2 * g)) * θ = 2 * b ^ 4 / g := by
    dsimp [θ]
    rw [haeq]
    field_simp
  have hc : historyAverage M G j (fun H => if lateLarge H T eta then 1 else 0) ≤
      (2 * b ^ 4 / g) / θ := (le_div_iff₀ hθ).mpr (by simpa only [mul_comm] using! hmarkov)
  have hquot : (2 * b ^ 4 / g) / θ = 2 / (eta ^ 2 * g) := by
    apply (div_eq_iff (ne_of_gt hθ)).mpr
    exact hid.symm
  exact hc.trans_eq hquot

/-- Average good-atom bounds and charge an explicit history-measurable bad event. -/
private theorem probability_of_atom_bounds {n M : ℕ} (hM : M ≤ capacity n)
    (j : ℕ) (A bad : Graph n → Prop) (c : ℝ) (hc : 0 ≤ c)
    (hbad : ∀ G H : Graph n, revealTrace H j = revealTrace G j → (bad H ↔ bad G))
    (hatom : ∀ G : Graph n, G.card = M → ¬ bad G →
      historyAverage M G j (fun H => if A H then 1 else 0) ≤ c) :
    probM n M A ≤ c + probM n M bad := by
  let s := fixedGraphs n M
  let trace := fun G : Graph n => revealTrace G j
  let f := fun H : Graph n => if A H ∧ ¬ bad H then (1 : ℝ) else 0
  have hmaps : ∀ G ∈ s, trace G ∈ s.image trace :=
    fun G hG => Finset.mem_image.mpr ⟨G, hG, rfl⟩
  have hfiber : ∀ G ∈ s,
      (∑ H ∈ s with trace H = trace G, f H) ≤
        c * (((s.filter (fun H => trace H = trace G)).card : ℝ)) := by
    intro G hGs
    have hGc : G.card = M := (Finset.mem_filter.mp hGs).2
    by_cases hb : bad G
    · have hz : (∑ H ∈ s with trace H = trace G, f H) = 0 := by
        apply Finset.sum_eq_zero
        intro H hH
        have ht := (Finset.mem_filter.mp hH).2
        have hbH := (hbad G H ht).mpr hb
        simp [f, hbH]
      rw [hz]
      positivity
    · have hh := hatom G hGc hb
      have hcard : (0 : ℝ) < (historyAtom M G j).card := by
        exact_mod_cast Finset.card_pos.mpr (historyAtom_nonempty G j hGc)
      have hbound := (div_le_iff₀ hcard).mp hh
      have hsmall : (∑ H ∈ historyAtom M G j, f H) ≤
          ∑ H ∈ historyAtom M G j, if A H then (1 : ℝ) else 0 := by
        apply Finset.sum_le_sum
        intro H _
        dsimp [f]
        split_ifs <;> simp_all
      exact hsmall.trans hbound
  have hsum : (∑ H ∈ s, f H) ≤ c * (s.card : ℝ) := by
    calc
      _ = ∑ v ∈ s.image trace, ∑ H ∈ s with trace H = v, f H :=
        (Finset.sum_fiberwise_of_maps_to hmaps f).symm
      _ ≤ ∑ v ∈ s.image trace, c * (((s.filter (fun H => trace H = v)).card : ℝ)) := by
        apply Finset.sum_le_sum
        intro v hv
        obtain ⟨G, hG, rfl⟩ := Finset.mem_image.mp hv
        exact hfiber G hG
      _ = c * (s.card : ℝ) := by
        rw [← Finset.mul_sum]
        have hh : (∑ v ∈ s.image trace, (s.filter (fun H => trace H = v)).card) = s.card := by
          calc
            _ = ∑ v ∈ s.image trace, ∑ H ∈ s with trace H = v, (1 : ℕ) := by simp
            _ = ∑ H ∈ s, (1 : ℕ) := Finset.sum_fiberwise_of_maps_to hmaps _
            _ = s.card := by simp
        exact congrArg (c * ·) (by exact_mod_cast hh)
  have hsplit : (∑ H ∈ s, if A H then (1 : ℝ) else 0) ≤
      (∑ H ∈ s, f H) + ∑ H ∈ s, if bad H then (1 : ℝ) else 0 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro H _
    dsimp [f]
    split_ifs <;> simp_all
  have hF : (0 : ℝ) < s.card := by
    exact_mod_cast Finset.card_pos.mpr
      (Erdos745.WrapUp.Proofs.Internal.W01_ENUM_Finite.fixedGraphs_nonempty hM)
  have htotal := hsplit.trans (show (∑ H ∈ s, f H) +
      (∑ H ∈ s, if bad H then (1 : ℝ) else 0) ≤ c * (s.card : ℝ) +
      (∑ H ∈ s, if bad H then (1 : ℝ) else 0) from add_le_add hsum le_rfl)
  rw [Finset.sum_boole, Finset.sum_boole] at htotal
  unfold probM
  change _ / (s.card : ℝ) ≤ c + _ / (s.card : ℝ)
  apply (div_le_iff₀ hF).mpr
  have heq : (c + (((s.filter bad).card : ℝ) / s.card)) * s.card =
      c * s.card + (s.filter bad).card := by field_simp
  rw [heq]
  exact htotal

/-! The critical density expansion retains `capacity n = n(n-1)/2`. -/

def latePoolBad {n : ℕ} (M : ℕ) (G : Graph n) (T δ : ℝ) : Prop :=
  δ / n13 n ^ 4 ≤ |poolDensity M G ⌊T * n23 n⌋₊ - (M : ℝ) / capacity n|

private theorem latePoolBad_on_history {n M : ℕ} (G H : Graph n) (T δ : ℝ)
    (h : revealTrace H ⌊T * n23 n⌋₊ = revealTrace G ⌊T * n23 n⌋₊) :
    latePoolBad M H T δ ↔ latePoolBad M G T δ := by
  simp [latePoolBad, poolDensity, poolSuccessCount, poolEdgeCount, answeredCount, h]

private theorem critical_late_initial_gap (M : NatSeq) (lam T : ℝ)
    (hcritical : criticalWindow M lam) (hT : 0 ≤ T) :
    Tendsto (fun n => n13 n *
      (((n : ℝ) - ⌊T * n23 n⌋₊) * ((M n : ℝ) / capacity n) - 1))
      atTop (𝓝 (lam - T)) := by
  have ha : Tendsto n23 atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 3)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have hJ := (tendsto_nat_floor_mul_div_atTop hT).comp ha
  have hp := critical_initial_density_tendsto_one M lam hcritical
  have hprod : Tendsto (fun n => n13 n * (⌊T * n23 n⌋₊ : ℝ) *
      ((M n : ℝ) / capacity n)) atTop (𝓝 T) := by
    have hh := hJ.mul hp
    have heq : (fun n => ((⌊T * n23 n⌋₊ : ℝ) / n23 n) *
        ((n : ℝ) * ((M n : ℝ) / capacity n))) =ᶠ[atTop]
        (fun n => n13 n * (⌊T * n23 n⌋₊ : ℝ) * ((M n : ℝ) / capacity n)) := by
      filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
      have hpow := n23_mul_n13 n hn
      have hne := ne_of_gt (n23_pos n hn)
      rw [div_mul_eq_mul_div]
      apply (div_eq_iff hne).mpr
      rw [← hpow]
      ring
    simpa only [mul_one] using! hh.congr' heq
  have hh := (critical_initial_drift_tendsto M lam hcritical).sub hprod
  convert hh using 1
  ext n
  ring

/-- The gap holds eventually outside a specified pool event, not on every history. -/
theorem eventual_neutral_subcritical_gap
    (M : NatSeq) (lam T : ℝ) (hcritical : criticalWindow M lam)
    (hT : 0 < T) (hgap : 0 < T - lam) :
    ∀ᶠ n in atTop, ∀ G : Graph n, G.card = M n →
      ¬ latePoolBad (M n) G T ((T - lam) / 4) →
      ((neutralVertices G ⌊T * n23 n⌋₊).card : ℝ) *
        poolDensity (M n) G ⌊T * n23 n⌋₊ ≤ 1 - (T - lam) / (2 * n13 n) := by
  let g := T - lam
  have hmain := (critical_late_initial_gap M lam T hcritical hT.le).eventually_le_const
    (show lam - T < -(3 * g / 4) by dsimp [g]; linarith)
  filter_upwards [hmain, eventually_eighth_horizon T hT.le,
    eventually_ge_atTop (1 : ℕ)] with n hnmain hJ hn
  intro G hG hgood
  let j := ⌊T * n23 n⌋₊
  let b := n13 n
  let p := poolDensity (M n) G j
  let p0 := (M n : ℝ) / capacity n
  let U := ((neutralVertices G j).card : ℝ)
  let e := |p - p0|
  have hb : 0 < b := by
    dsimp [b, n13]
    exact Real.rpow_pos_of_pos (by exact_mod_cast hn) _
  have hcub : b ^ 3 = (n : ℝ) := n13_cube n hn
  have hj : j ≤ n := by dsimp [j]; omega
  have hnj : 0 ≤ (n : ℝ) - j := by
    have hh : (j : ℝ) ≤ n := by exact_mod_cast hj
    linarith
  have hU : U ≤ (n : ℝ) - j := neutral_card_le G j hj
  have hp : 0 ≤ p := by dsimp [p, poolDensity]; positivity
  have he0 : 0 ≤ e := abs_nonneg _
  have hdiff : p - p0 ≤ e := le_abs_self _
  have he : b ^ 4 * e < g / 4 := by
    have hlt' : e < g / 4 / b ^ 4 := lt_of_not_ge hgood
    have hh := (lt_div_iff₀ (pow_pos hb 4)).mp hlt'
    nlinarith [hh]
  have hupper : U * p ≤ ((n : ℝ) - j) * p0 + (n : ℝ) * e := by
    have h1 := mul_le_mul_of_nonneg_right hU hp
    have h2 := mul_le_mul_of_nonneg_left hdiff hnj
    have h3 : ((n : ℝ) - j) * e ≤ (n : ℝ) * e := by
      exact mul_le_mul_of_nonneg_right (by linarith [show (0 : ℝ) ≤ j from Nat.cast_nonneg j]) he0
    linarith
  have hscaled := mul_le_mul_of_nonneg_left hupper hb.le
  have hbe : b * (n : ℝ) * e < g / 4 := by
    rw [← hcub]
    nlinarith [he]
  change b * (((n : ℝ) - j) * p0 - 1) ≤ -(3 * g / 4) at hnmain
  have hfinal : b * (U * p - 1) ≤ -g / 2 := by nlinarith
  have hdiv : U * p - 1 ≤ (-g / 2) / b := (le_div_iff₀ hb).mpr (by nlinarith)
  change U * p ≤ 1 - g / (2 * b)
  have hid : (-g / 2) / b = -(g / (2 * b)) := by ring
  rw [hid] at hdiv
  linarith

/-- The exact first clause consumed by B10; no Brownian premise is used. -/
theorem lateLarge_eventual_bound
    (hfinite : FiniteEnumerationStatement) (M : NatSeq) (lam : ℝ)
    (hcritical : criticalWindow M lam) :
    ∀ eta T d : ℝ, 0 < eta → 0 < T → lam + 1 < T → 0 < d →
      ∀ᶠ n in atTop, probM n (M n) (fun G => lateLarge G T eta) ≤
        4 / (eta ^ 2 * (T - lam)) + d := by
  intro eta T d heta hT hlam hd
  have hg : 0 < T - lam := by linarith
  let δ := (T - lam) / 4
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hpool := (critical_poolDensity_concentration hfinite M lam T δ hcritical hT.le hδ).eventually_le_const hd
  filter_upwards [hpool, eventual_neutral_subcritical_gap M lam T hcritical hT hg,
    eventually_horizonBudget M lam T hcritical hT.le, hcritical.1,
    eventually_ge_atTop (1 : ℕ)] with n hnPool hnGap hnBudget hnM hn
  let bad := fun G : Graph n => latePoolBad (M n) G T δ
  have hbadprob : probM n (M n) bad ≤ d := by
    have hsub : ((fixedGraphs n (M n)).filter bad) ⊆
        (fixedGraphs n (M n)).filter (fun G => ∃ k ≤ ⌊T * n23 n⌋₊,
          δ / n13 n ^ 4 ≤ |poolDensity (M n) G k - poolDensity (M n) G 0|) := by
      intro G hG
      obtain ⟨hGs, hb⟩ := Finset.mem_filter.mp hG
      refine Finset.mem_filter.mpr ⟨hGs, ⌊T * n23 n⌋₊, le_rfl, ?_⟩
      simpa [bad, latePoolBad, poolDensity, poolSuccessCount_initial,
        poolEdgeCount_initial] using! hb
    have hprob : probM n (M n) bad ≤ probM n (M n) (fun G => ∃ k ≤ ⌊T * n23 n⌋₊,
        δ / n13 n ^ 4 ≤ |poolDensity (M n) G k - poolDensity (M n) G 0|) := by
      unfold probM
      apply div_le_div_of_nonneg_right _ (by positivity)
      have hh : (((fixedGraphs n (M n)).filter bad).card : ℝ) ≤
          (((fixedGraphs n (M n)).filter (fun G => ∃ k ≤ ⌊T * n23 n⌋₊,
            δ / n13 n ^ 4 ≤ |poolDensity (M n) G k - poolDensity (M n) G 0|)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
      convert hh using 1
      apply congrArg (fun t : Finset (Graph n) => (t.card : ℝ))
      ext G
      simp only [Finset.mem_filter]
    exact hprob.trans hnPool
  have hatom : ∀ G : Graph n, G.card = M n → ¬ bad G →
      historyAverage (M n) G ⌊T * n23 n⌋₊
        (fun H => if lateLarge H T eta then 1 else 0) ≤ 2 / (eta ^ 2 * (T - lam)) := by
    intro G hG hgood
    have hE := poolEdgeCount_ge_eight G ⌊T * n23 n⌋₊ hnBudget le_rfl
    exact conditional_lateLarge_bound hfinite hnM G hG hn eta T (T - lam) heta hg
      (by omega) (hnGap G hG hgood)
  have hglobal := probability_of_atom_bounds hnM ⌊T * n23 n⌋₊
    (fun G => lateLarge G T eta) bad (2 / (eta ^ 2 * (T - lam))) (by positivity)
    (fun G H h => latePoolBad_on_history G H T δ h) hatom
  have hweak : 2 / (eta ^ 2 * (T - lam)) ≤ 4 / (eta ^ 2 * (T - lam)) := by
    apply div_le_div_of_nonneg_right (by norm_num) (by positivity)
  exact hglobal.trans (add_le_add hweak hbadprob)

end
end Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_LateTail
