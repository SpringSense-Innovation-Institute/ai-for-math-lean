module

public import Erdos745.WrapUp.Proofs.Internal.Linked.W15_Base
public import Erdos745.WrapUp.Proofs.Internal.Linked.W15_Code
public import Erdos745.WrapUp.Proofs.Internal.Linked.W15_Geometry
public import Erdos745.WrapUp.Proofs.Internal.Linked.W14_Base
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Topology.Algebra.Module.Cardinality

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local simp] Pi.div_def Pi.mul_def Pi.add_def Pi.sub_def Pi.neg_def Pi.inv_def Function.comp_def Pi.pow_def Pi.smul_def Real.rpow_eq_pow

@[expose] public section


/-!
# Exact scaled ranks of finite BFS blocks

The finite code uses the actual `pairCode` index of consecutive strict mesh
records.  Its full version is represented by the equivalent finite queue-block
family.  The limiting dense `codeTime`/`retainedCode` construction and the
single `centerPath` drift convention are inherited unchanged from `Truncated`
and `CodeComplete`.
-/

namespace Erdos745.WrapUp.Proofs.Internal.W15_CRITICAL_ScaledRanks

open Erdos745.WrapUp
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_Interpolation
open Erdos745.WrapUp.Proofs.Internal.W15_CRITICAL_Truncated
open Erdos745.WrapUp.Proofs.Internal.W15_CRITICAL_FiniteEnumeration
open Erdos745.WrapUp.Proofs.Internal.W15_CRITICAL_FiniteRank
open scoped ENNReal

noncomputable section
attribute [local instance] Classical.propDecidable

private theorem scale_pos {n : ℕ} (hn : 0 < n) : 0 < n23 n := by
  exact Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn) _

private theorem block_length_nonneg {n : ℕ} (G : Graph n) (hn : 0 < n)
    {z : ℕ × ℕ} (hz : z ∈ queueBlocks G) :
    0 ≤ meshBlockLength n z.1 z.2 := by
  rw [meshBlockLength_eq_blockComponent_card G ((mem_queueBlocks G z).mp hz)]
  exact div_nonneg (Nat.cast_nonneg _) (le_of_lt (scale_pos hn))

private theorem block_length_le_total {n : ℕ} (G : Graph n) (hn : 0 < n)
    {z : ℕ × ℕ} (hz : z ∈ queueBlocks G) :
    meshBlockLength n z.1 z.2 ≤ (n : ℝ) / n23 n := by
  rw [meshBlockLength_eq_blockComponent_card G ((mem_queueBlocks G z).mp hz)]
  apply div_le_div_of_nonneg_right _ (le_of_lt (scale_pos hn))
  exact_mod_cast (by simpa using! Finset.card_le_univ (blockComponent G z))

/-- The full pair code is the strict-record code on every positive-order BFS
path.  Only the finite support is stored here. -/
def untruncatedCodeLength {n : ℕ} (G : Graph n) (m : ℕ) : ENNReal :=
  if pairCode m ∈ queueBlocks G then
    ENNReal.ofReal (meshBlockLength n (pairCode m).1 (pairCode m).2)
  else 0

theorem untruncatedCodeLength_eq_records {n : ℕ} (G : Graph n)
    (hn : 0 < n) (m : ℕ) :
    untruncatedCodeLength G m =
      if successiveMeshRecords n (pairCode m).1 (pairCode m).2
          (continuousRawExploration G) then
        ENNReal.ofReal (meshBlockLength n (pairCode m).1 (pairCode m).2)
      else 0 := by
  simp only [untruncatedCodeLength,
    mem_queueBlocks G (pairCode m), queueBlock_iff_meshRecords G hn (pairCode m)]

def untruncatedCodeRank {n : ℕ} (G : Graph n) (i : ℕ) : ENNReal :=
  rankFromCandidates (fun m _ => untruncatedCodeLength G m) i
    (continuousRawExploration G)

private theorem untruncated_zero_outside {n : ℕ} (G : Graph n)
    {m : ℕ} (hm : m ∉ codedBlockSupport G) :
    untruncatedCodeLength G m = 0 := by
  have hz : pairCode m ∉ queueBlocks G := by
    intro hz
    apply hm
    exact Finset.mem_image.mpr ⟨pairCode m, hz, by
      simp [blockIndex, pairCode, Nat.pair_unpair]⟩
  simp [untruncatedCodeLength, hz]

private theorem untruncated_candidates_count {n : ℕ} (G : Graph n)
    (x : ENNReal) :
    ((codedBlockSupport G).filter (fun m =>
      x ≤ untruncatedCodeLength G m)).card =
    ((queueBlocks G).filter (fun z =>
      x ≤ ENNReal.ofReal (meshBlockLength n z.1 z.2))).card := by
  have heq :
      (codedBlockSupport G).filter (fun m =>
        x ≤ untruncatedCodeLength G m) =
      ((queueBlocks G).filter (fun z =>
        x ≤ ENNReal.ofReal (meshBlockLength n z.1 z.2))).image blockIndex := by
    ext m
    constructor
    · intro hm
      obtain ⟨z, hz, hmz⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hm).1
      have hp : pairCode m = z := by
        rw [← hmz]
        simp [pairCode, blockIndex, Nat.unpair_pair]
      have hv := (Finset.mem_filter.mp hm).2
      simp only [untruncatedCodeLength, hp, hz, if_true] at hv
      exact Finset.mem_image.mpr ⟨z, Finset.mem_filter.mpr ⟨hz, hv⟩, hmz⟩
    · intro hm
      obtain ⟨z, hz, hmz⟩ := Finset.mem_image.mp hm
      have hb := (Finset.mem_filter.mp hz).1
      have hp : pairCode m = z := by
        rw [← hmz]
        simp [pairCode, blockIndex, Nat.unpair_pair]
      apply Finset.mem_filter.mpr
      constructor
      · exact Finset.mem_image.mpr ⟨z, hb, hmz⟩
      · simpa [untruncatedCodeLength, hp, hb] using! (Finset.mem_filter.mp hz).2
  rw [heq]
  exact (Finset.card_image_iff.mpr fun z _ w _ h =>
    blockIndex_injective h)

/-- Exact positive threshold count for the full countable pair code. -/
theorem untruncatedCodeRank_threshold {n : ℕ} (G : Graph n)
    (i : ℕ) (hi : 0 < i) (x : ENNReal) (hx : 0 < x) :
    x ≤ untruncatedCodeRank G i ↔
      i ≤ ((queueBlocks G).filter (fun z =>
        x ≤ ENNReal.ofReal (meshBlockLength n z.1 z.2))).card := by
  unfold untruncatedCodeRank
  rw [rankFromCandidates_threshold_of_finite_support
    (fun m _ => untruncatedCodeLength G m)
    (continuousRawExploration G) (codedBlockSupport G)
    (fun m hm => untruncated_zero_outside G hm) i hi x hx]
  exact untruncated_candidates_count G x ▸ Iff.rfl

private theorem countGE_antitone {n : ℕ} (G : Graph n)
    {h q : ℕ} (hhq : h ≤ q) : countGE G q ≤ countGE G h := by
  unfold countGE
  apply Finset.card_le_card
  intro S hS
  exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hS).1,
    le_trans hhq (Finset.mem_filter.mp hS).2⟩

/-- The public finite supremum has the exact threshold property, also with
ties and with zero padding when `i` exceeds the number of components. -/
theorem rankSize_threshold {n : ℕ} (G : Graph n)
    (i h : ℕ) (hi : 0 < i) (hh : 0 < h) :
    h ≤ rankSize G i ↔ i ≤ countGE G h := by
  rw [rankSize, if_neg (Nat.ne_of_gt hi)]
  constructor
  · intro hle
    obtain ⟨q, _, hq⟩ := (Finset.le_sup_iff hh).mp hle
    by_cases hcount : i ≤ countGE G q
    · simp only [hcount, if_true] at hq
      exact le_trans hcount (countGE_antitone G hq)
    · simp only [hcount, if_false] at hq
      exact False.elim (lt_irrefl (0 : ℕ) (lt_of_lt_of_le hh hq))
  · intro hcount
    have hpos : 0 < countGE G h := lt_of_lt_of_le hi hcount
    obtain ⟨S, hS⟩ := Finset.card_pos.mp hpos
    have hle : h ≤ n := by
      exact le_trans (Finset.mem_filter.mp hS).2
        (by simpa using! Finset.card_le_univ S)
    have hmem : h ∈ Finset.range (n + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hle)
    simpa only [hcount, if_true] using!
      (Finset.le_sup (f := fun q => if i ≤ countGE G q then q else 0) hmem)

private theorem threshold_ceil {n : ℕ} (G : Graph n) (hn : 0 < n)
    (x : ENNReal) (hx_top : x ≠ ⊤) :
    ((queueBlocks G).filter (fun z =>
      x ≤ ENNReal.ofReal (meshBlockLength n z.1 z.2))).card =
      countGE G ⌈x.toReal * n23 n⌉₊ := by
  have hf : (queueBlocks G).filter (fun z =>
        x ≤ ENNReal.ofReal (meshBlockLength n z.1 z.2)) =
      (queueBlocks G).filter (fun z =>
        ⌈x.toReal * n23 n⌉₊ ≤ (blockComponent G z).card) := by
    ext z
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hz, hx⟩
      have hlen := block_length_nonneg G hn hz
      rw [meshBlockLength_eq_blockComponent_card G ((mem_queueBlocks G z).mp hz)] at hx
      have hreal := (ENNReal.le_ofReal_iff_toReal_le hx_top
        (div_nonneg (Nat.cast_nonneg _) (le_of_lt (scale_pos hn)))).mp hx
      exact ⟨hz, Nat.ceil_le.mpr ((le_div_iff₀ (scale_pos hn)).mp hreal)⟩
    · rintro ⟨hz, hx⟩
      rw [meshBlockLength_eq_blockComponent_card G ((mem_queueBlocks G z).mp hz)]
      refine ⟨hz, ?_⟩
      apply (ENNReal.le_ofReal_iff_toReal_le hx_top
        (div_nonneg (Nat.cast_nonneg _) (le_of_lt (scale_pos hn)))).mpr
      exact (le_div_iff₀ (scale_pos hn)).mpr (Nat.ceil_le.mp hx)
  rw [hf]
  exact queueBlocks_countGE G _

private theorem target_threshold {n : ℕ} (G : Graph n) (hn : 0 < n)
    (i : ℕ) (hi : 0 < i) (x : ENNReal)
    (hx : 0 < x) (hx_top : x ≠ ⊤) :
    x ≤ ENNReal.ofReal ((rankSize G i : ℝ) / n23 n) ↔
      i ≤ countGE G ⌈x.toReal * n23 n⌉₊ := by
  have ha := scale_pos hn
  have hr : 0 ≤ (rankSize G i : ℝ) / n23 n :=
    div_nonneg (Nat.cast_nonneg _) ha.le
  rw [ENNReal.le_ofReal_iff_toReal_le hx_top hr]
  rw [le_div_iff₀ ha]
  rw [← Nat.ceil_le]
  exact rankSize_threshold G i _ hi
    (Nat.ceil_pos.mpr (mul_pos (ENNReal.toReal_pos (ne_of_gt hx) hx_top) ha))

/-- Every full finite code rank is bounded before any `toReal` conversion. -/
theorem untruncatedCodeRank_le_total {n : ℕ} (G : Graph n)
    (hn : 0 < n) (i : ℕ) :
    untruncatedCodeRank G i ≤ ENNReal.ofReal ((n : ℝ) / n23 n) := by
  unfold untruncatedCodeRank rankFromCandidates
  by_cases hi : i = 0
  · simp [hi]
  · simp only [hi, if_false]
    apply iSup_le
    intro f
    by_cases hf : Function.Injective f
    · rw [if_pos hf]
      let hidx : Fin i := ⟨0, Nat.pos_of_ne_zero hi⟩
      refine (iInf_le _ hidx).trans ?_
      unfold untruncatedCodeLength
      split_ifs with hz
      · exact ENNReal.ofReal_le_ofReal (block_length_le_total G hn hz)
      · exact bot_le
    · rw [if_neg hf]
      exact bot_le

theorem untruncatedCodeRank_ne_top {n : ℕ} (G : Graph n)
    (hn : 0 < n) (i : ℕ) : untruncatedCodeRank G i ≠ ⊤ := by
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (untruncatedCodeRank_le_total G hn i)

/-- Positive threshold and ceiling comparison identifies the countable full
code rank with the literal scaled, zero-padded public component rank. -/
theorem untruncatedCodeRank_eq_rankSize {n : ℕ} (G : Graph n)
    (hn : 0 < n) (i : ℕ) :
    untruncatedCodeRank G i =
      ENNReal.ofReal ((rankSize G i : ℝ) / n23 n) := by
  by_cases hi : i = 0
  · subst i
    simp [untruncatedCodeRank, rankFromCandidates, rankSize]
  have hi' := Nat.pos_of_ne_zero hi
  let R := untruncatedCodeRank G i
  let V := ENNReal.ofReal ((rankSize G i : ℝ) / n23 n)
  have hRtop : R ≠ ⊤ := untruncatedCodeRank_ne_top G hn i
  have hVtop : V ≠ ⊤ := ENNReal.ofReal_ne_top
  have hthresh (x : ENNReal) (hx : 0 < x) (hx_top : x ≠ ⊤) :
      x ≤ R ↔ x ≤ V := by
    rw [untruncatedCodeRank_threshold G i hi' x hx,
      threshold_ceil G hn x hx_top]
    exact (target_threshold G hn i hi' x hx hx_top).symm
  change R = V
  apply le_antisymm
  · by_cases hR : R = 0
    · rw [hR]
      exact bot_le
    · exact (hthresh R (pos_iff_ne_zero.mpr hR) hRtop).mp le_rfl
  · by_cases hV : V = 0
    · rw [hV]
      exact bot_le
    · exact (hthresh V (pos_iff_ne_zero.mpr hV) hVtop).mpr le_rfl

theorem untruncatedCodeRank_toReal_eq_rankSize_div {n : ℕ}
    (G : Graph n) (hn : 0 < n) (i : ℕ) :
    (untruncatedCodeRank G i).toReal =
      (rankSize G i : ℝ) / n23 n := by
  rw [untruncatedCodeRank_eq_rankSize G hn i]
  exact ENNReal.toReal_ofReal
    (div_nonneg (Nat.cast_nonneg _) (scale_pos hn).le)

private theorem rankFromCandidates_mono
    (v w : ℕ → BrownianPath → ENNReal) (p : BrownianPath)
    (hvw : ∀ m, v m p ≤ w m p) (i : ℕ) :
    rankFromCandidates v i p ≤ rankFromCandidates w i p := by
  unfold rankFromCandidates
  by_cases hi : i = 0
  · simp [hi]
  · simp only [hi, if_false]
    apply iSup_le
    intro f
    by_cases hf : Function.Injective f
    · rw [if_pos hf]
      apply le_iSup_of_le f
      rw [if_pos hf]
      exact iInf_mono fun j => hvw (f j)
    · rw [if_neg hf]
      exact bot_le

private theorem kept_candidate_le_full {n : ℕ} (G : Graph n)
    (hn : 0 < n) (a_cut T U : ℝ) (m : ℕ) :
    discreteKeptLength n a_cut T U (pairCode m)
        (continuousRawExploration G) ≤ untruncatedCodeLength G m := by
  by_cases hz : pairCode m ∈ queueBlocks G
  · rw [discreteKeptLength_of_queueBlock G hn a_cut T U hz]
    unfold untruncatedCodeLength
    rw [if_pos hz]
    split_ifs <;> simp
  · have hm : m ∉ codedBlockSupport G := by
      intro hm
      obtain ⟨z, hzb, hmz⟩ := Finset.mem_image.mp hm
      apply hz
      have hp : pairCode m = z := by
        rw [← hmz]
        simp [pairCode, blockIndex, Nat.unpair_pair]
      exact hp ▸ hzb
    rw [discreteKeptLength_zero_outside_support G hn a_cut T U m hm,
      untruncated_zero_outside G hm]

/-- The kept rank is finite, with the same explicit ENNReal bound as the full
rank.  This precedes all real-coordinate statements below. -/
theorem keptCodeRank_eq_full_above_cutoff {n : ℕ} (G : Graph n)
    (hn : 0 < n) (a_cut T U : ℝ) (hcut : 0 ≤ a_cut)
    (hretain : ∀ z ∈ queueBlocks G,
      a_cut < meshBlockLength n z.1 z.2 →
        z ∈ keptBlocks G a_cut T U)
    (i : ℕ) (hi : 0 < i)
    (hrank : a_cut < (rankSize G i : ℝ) / n23 n) :
    rankFromCandidates
        (fun m => discreteKeptLength n a_cut T U (pairCode m)) i
        (continuousRawExploration G) = untruncatedCodeRank G i := by
  let R := untruncatedCodeRank G i
  have hR : R = ENNReal.ofReal ((rankSize G i : ℝ) / n23 n) :=
    untruncatedCodeRank_eq_rankSize G hn i
  have hRpos : 0 < R := by
    rw [hR]
    exact ENNReal.ofReal_pos.mpr (lt_of_le_of_lt hcut hrank)
  have hsub :
      (queueBlocks G).filter (fun z =>
        R ≤ ENNReal.ofReal (meshBlockLength n z.1 z.2)) ⊆
      (keptBlocks G a_cut T U).filter (fun z =>
        R ≤ ENNReal.ofReal (meshBlockLength n z.1 z.2)) := by
    intro z hz
    obtain ⟨hb, hlen⟩ := Finset.mem_filter.mp hz
    have hreal : (rankSize G i : ℝ) / n23 n ≤
        meshBlockLength n z.1 z.2 := by
      rw [hR] at hlen
      exact (ENNReal.ofReal_le_ofReal_iff (block_length_nonneg G hn hb)).mp hlen
    exact Finset.mem_filter.mpr
      ⟨hretain z hb (lt_of_lt_of_le hrank hreal), hlen⟩
  have hfull : i ≤ ((queueBlocks G).filter (fun z =>
      R ≤ ENNReal.ofReal (meshBlockLength n z.1 z.2))).card :=
    (untruncatedCodeRank_threshold G i hi R hRpos).mp le_rfl
  have hkept : R ≤ rankFromCandidates
      (fun m => discreteKeptLength n a_cut T U (pairCode m)) i
      (continuousRawExploration G) :=
    (discreteTruncatedRank_threshold G hn a_cut T U i hi R hRpos).mpr
      (le_trans hfull (Finset.card_le_card hsub))
  exact le_antisymm
    (rankFromCandidates_mono _ _ _
      (kept_candidate_le_full G hn a_cut T U) i) hkept

/-- The exported real coordinate uses the original truncated rank map. -/
theorem discreteTruncatedRank_eq_rankSize_div {n : ℕ} (G : Graph n)
    (hn : 0 < n) (a_cut T U : ℝ) (hcut : 0 ≤ a_cut)
    (hretain : ∀ z ∈ queueBlocks G,
      a_cut < meshBlockLength n z.1 z.2 →
        z ∈ keptBlocks G a_cut T U)
    (k : ℕ) (r : Fin k)
    (hrank : a_cut < (rankSize G (r.val + 1) : ℝ) / n23 n) :
    discreteTruncatedRank n a_cut T U k (continuousRawExploration G) r =
      (rankSize G (r.val + 1) : ℝ) / n23 n := by
  simp only [discreteTruncatedRank]
  rw [keptCodeRank_eq_full_above_cutoff G hn a_cut T U hcut hretain
    (r.val + 1) (Nat.zero_lt_succ _) hrank]
  exact untruncatedCodeRank_toReal_eq_rankSize_div G hn _

end

end Erdos745.WrapUp.Proofs.Internal.W15_CRITICAL_ScaledRanks


/-!
# Stable retained blocks on the actual BFS supports

The finite lists below use the literal strict guards of `discreteKeptLength`
and `limitKeptLength`.  A limiting excursion is represented by the single
completed block sequence supplied by forward matching.
-/

namespace Erdos745.WrapUp.Proofs.Internal.W15_CRITICAL_SupportMatching

open Erdos745.WrapUp
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_Interpolation
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_CriticalBudget
open Erdos745.WrapUp.Proofs.Internal.W15_CRITICAL_Truncated
open Erdos745.WrapUp.Proofs.Internal.W15_CRITICAL_FiniteEnumeration
open Erdos745.WrapUp.Proofs.Internal.W15_CRITICAL_FiniteRank
open Erdos745.WrapUp.Proofs.Internal.W15_CRITICAL_Code
open Erdos745.WrapUp.Proofs.Internal.W15_CRITICAL_CodeComplete
open Erdos745.WrapUp.Proofs.Internal.W15_CRITICAL_RecordGeometry
open Erdos745.WrapUp.Proofs.Internal.W15_CRITICAL_ForwardMatching
open Erdos745.WrapUp.Proofs.Internal.W15_CRITICAL_EndpointMatching
open Filter Set
open scoped Topology ENNReal

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local simp] Pi.div_def Pi.mul_def Pi.add_def Pi.sub_def Pi.neg_def Pi.inv_def Function.comp_def
attribute [local instance] Classical.propDecidable

def excursionLength (e : NNReal × NNReal) : ℝ := (e.2 : ℝ) - (e.1 : ℝ)

def LimitKept (p : BrownianPath) (lam a T U : ℝ) (e : NNReal × NNReal) : Prop :=
  excursion (centerPath p lam) lam e.1 e.2 ∧
    a < excursionLength e ∧ (e.1 : ℝ) < T ∧ (e.2 : ℝ) < U

/-- The finite limiting list is taken from the GoodExcursionPath finite-long-
excursion clause and then filtered by all three literal strict guards. -/
def limitKeptExcursions (p : BrownianPath) (lam a T U : ℝ)
    (hgood : GoodExcursionPath (centerPath p lam) lam) (ha : 0 < a) :
    Finset (NNReal × NNReal) :=
  ((hgood.2.2.2.2.1 a ha).toFinset).filter (LimitKept p lam a T U)

theorem mem_limitKeptExcursions (p : BrownianPath) (lam a T U : ℝ)
    (hgood : GoodExcursionPath (centerPath p lam) lam) (ha : 0 < a)
    (e : NNReal × NNReal) :
    e ∈ limitKeptExcursions p lam a T U hgood ha ↔
      LimitKept p lam a T U e := by
  simp only [limitKeptExcursions, Finset.mem_filter, Set.Finite.mem_toFinset]
  constructor
  · exact And.right
  · intro he
    exact ⟨⟨he.1, le_of_lt he.2.1⟩, he⟩

/-- Exclusion of cutoff atoms is stated for actual limiting excursions, not
for arbitrary pairs of times. -/
def CutoffAvoidance (p : BrownianPath) (lam a T U : ℝ) : Prop :=
  ∀ e : NNReal × NNReal,
    excursion (centerPath p lam) lam e.1 e.2 →
      excursionLength e ≠ a ∧ (e.1 : ℝ) ≠ T ∧ (e.2 : ℝ) ≠ U

private theorem meshTime_lt_floor_guard {n t : ℕ} (hn : 0 < n)
    {U : ℝ} (h : (meshTime n t : ℝ) < U) :
    t ≤ ⌊U * n23 n⌋₊ + 1 := by
  have hs : 0 < n23 n := n23_pos n hn
  have ht : (t : ℝ) / n23 n < U := by
    rw [meshTime_eq_mul_meshStep n t hn] at h
    simpa only [meshStep, mul_one_div] using! h
  have hcast : (t : ℝ) ≤ U * n23 n := (div_lt_iff₀ hs).mp ht |>.le
  exact (Nat.le_floor hcast).trans (Nat.le_succ _)

private theorem matched_length_tendsto
    {ns : ℕ → ℕ} {Gs : (j : ℕ) → Graph (ns j)}
    (hns : Tendsto ns atTop atTop)
    {z : ℕ → ℕ × ℕ} {e : NNReal × NNReal}
    (hz : MatchedBlockSequence atTop ns Gs z e.1 e.2) :
    Tendsto (fun j => meshBlockLength (ns j) (z j).1 (z j).2)
      atTop (𝓝 (excursionLength e)) := by
  have ht := (NNReal.continuous_coe.tendsto e.2).comp hz.2.2
  have hs := (NNReal.continuous_coe.tendsto e.1).comp hz.2.1
  have hd := ht.sub hs
  apply hd.congr'
  filter_upwards [hns.eventually_ge_atTop 1] with j hn
  exact (meshBlockLength_eq_meshTimes (n := ns j) (s := (z j).1)
    (t := (z j).2) hn).symm

/-- The same completed forward witness eventually passes every strict finite
guard of a kept limiting excursion. -/
theorem matched_eventually_kept
    {ns : ℕ → ℕ} {Gs : (j : ℕ) → Graph (ns j)}
    (hns : Tendsto ns atTop atTop)
    {p : BrownianPath} {lam a T U : ℝ}
    {e : NNReal × NNReal} (he : LimitKept p lam a T U e)
    {z : ℕ → ℕ × ℕ}
    (hz : MatchedBlockSequence atTop ns Gs z e.1 e.2) :
    ∀ᶠ j : ℕ in atTop, z j ∈ keptBlocks (Gs j) a T U := by
  have hl := matched_length_tendsto hns hz
  have hs := (NNReal.continuous_coe.tendsto e.1).comp hz.2.1
  have ht := (NNReal.continuous_coe.tendsto e.2).comp hz.2.2
  filter_upwards [hz.1, hns.eventually_ge_atTop 1,
      hl.eventually_const_lt he.2.1,
      hs.eventually_lt_const he.2.2.1,
      ht.eventually_lt_const he.2.2.2] with j hb hn hlen hstart hend
  apply (mem_keptBlocks (Gs j) a T U (z j)).mpr
  exact ⟨(mem_queueBlocks (Gs j) (z j)).mpr
      ((queueBlock_iff_meshRecords (Gs j) hn (z j)).mpr hb.2.2),
    meshTime_lt_floor_guard hn hend, hstart, hend, hlen⟩

abbrev KeptExcursion (p : BrownianPath) (lam a T U : ℝ)
    (hgood : GoodExcursionPath (centerPath p lam) lam) (ha : 0 < a) :=
  {e : NNReal × NNReal // e ∈ limitKeptExcursions p lam a T U hgood ha}

/-- One B02F witness is selected once for each element of the finite limiting
list.  All later uses, including both endpoint limits, refer to this choice. -/
def selectedBlock
    {ns : ℕ → ℕ} {Gs : (j : ℕ) → Graph (ns j)}
    {p : BrownianPath} (hns : Tendsto ns atTop atTop)
    (hps : Tendsto (fun j => continuousRawExploration (Gs j)) atTop (𝓝 p))
    (lam a T U : ℝ)
    (hgood : GoodExcursionPath (centerPath p lam) lam) (ha : 0 < a)
    (e : KeptExcursion p lam a T U hgood ha) : ℕ → ℕ × ℕ :=
  Classical.choose (forward_excursion_matching hns hps lam hgood
    ((mem_limitKeptExcursions p lam a T U hgood ha e.1).mp e.2).1)

theorem selectedBlock_spec
    {ns : ℕ → ℕ} {Gs : (j : ℕ) → Graph (ns j)}
    {p : BrownianPath} (hns : Tendsto ns atTop atTop)
    (hps : Tendsto (fun j => continuousRawExploration (Gs j)) atTop (𝓝 p))
    (lam a T U : ℝ)
    (hgood : GoodExcursionPath (centerPath p lam) lam) (ha : 0 < a)
    (e : KeptExcursion p lam a T U hgood ha) :
    MatchedBlockSequence atTop ns Gs
      (selectedBlock hns hps lam a T U hgood ha e) e.1.1 e.1.2 := by
  exact Classical.choose_spec (forward_excursion_matching hns hps lam hgood
    ((mem_limitKeptExcursions p lam a T U hgood ha e.1).mp e.2).1)

private theorem eventually_selected_kept
    {ns : ℕ → ℕ} {Gs : (j : ℕ) → Graph (ns j)}
    {p : BrownianPath} (hns : Tendsto ns atTop atTop)
    (hps : Tendsto (fun j => continuousRawExploration (Gs j)) atTop (𝓝 p))
    (lam a T U : ℝ)
    (hgood : GoodExcursionPath (centerPath p lam) lam) (ha : 0 < a) :
    ∀ᶠ j : ℕ in atTop,
      ∀ e : KeptExcursion p lam a T U hgood ha,
        selectedBlock hns hps lam a T U hgood ha e j ∈
          keptBlocks (Gs j) a T U := by
  have hpoint (e : KeptExcursion p lam a T U hgood ha) :
      ∀ᶠ j : ℕ in atTop,
        selectedBlock hns hps lam a T U hgood ha e j ∈
          keptBlocks (Gs j) a T U :=
    matched_eventually_kept hns
      ((mem_limitKeptExcursions p lam a T U hgood ha e.1).mp e.2)
      (selectedBlock_spec hns hps lam a T U hgood ha e)
  simpa only [Finset.mem_univ, forall_true_left] using!
    (Filter.eventually_all_finset
      (I := (Finset.univ : Finset (KeptExcursion p lam a T U hgood ha)))).2
      (fun e _ => hpoint e)

private theorem eventually_selected_injective
    {ns : ℕ → ℕ} {Gs : (j : ℕ) → Graph (ns j)}
    {p : BrownianPath} (hns : Tendsto ns atTop atTop)
    (hps : Tendsto (fun j => continuousRawExploration (Gs j)) atTop (𝓝 p))
    (lam a T U : ℝ)
    (hgood : GoodExcursionPath (centerPath p lam) lam) (ha : 0 < a) :
    ∀ᶠ j : ℕ in atTop,
      Function.Injective (fun e : KeptExcursion p lam a T U hgood ha =>
        selectedBlock hns hps lam a T U hgood ha e j) := by
  let H := KeptExcursion p lam a T U hgood ha
  have hpair (e f : H) : ∀ᶠ j : ℕ in atTop,
      e ≠ f → selectedBlock hns hps lam a T U hgood ha e j ≠
        selectedBlock hns hps lam a T U hgood ha f j := by
    by_cases hef : e = f
    · exact Filter.Eventually.of_forall (fun _ h => (h hef).elim)
    · have hne : e.1 ≠ f.1 := by
        intro h
        exact hef (Subtype.ext h)
      exact (matched_blocks_eventually_distinct
        (selectedBlock_spec hns hps lam a T U hgood ha e)
        (selectedBlock_spec hns hps lam a T U hgood ha f) hne).mono
          (fun _ h _ => h)
  have hforall : ∀ᶠ j : ℕ in atTop,
      ∀ e ∈ (Finset.univ : Finset H), ∀ f ∈ (Finset.univ : Finset H),
        e ≠ f → selectedBlock hns hps lam a T U hgood ha e j ≠
          selectedBlock hns hps lam a T U hgood ha f j := by
    apply (Filter.eventually_all_finset
      (I := (Finset.univ : Finset H))).2
    intro e _
    apply (Filter.eventually_all_finset
      (I := (Finset.univ : Finset H))).2
    intro f _
    exact hpair e f
  filter_upwards [hforall] with j hj e f hef
  by_contra hne
  exact (hj e (Finset.mem_univ _) f (Finset.mem_univ _)
    hne) hef

def selectedBlocks
    {ns : ℕ → ℕ} {Gs : (j : ℕ) → Graph (ns j)}
    {p : BrownianPath} (hns : Tendsto ns atTop atTop)
    (hps : Tendsto (fun j => continuousRawExploration (Gs j)) atTop (𝓝 p))
    (lam a T U : ℝ)
    (hgood : GoodExcursionPath (centerPath p lam) lam) (ha : 0 < a)
    (j : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.univ : Finset (KeptExcursion p lam a T U hgood ha)).image
    (fun e => selectedBlock hns hps lam a T U hgood ha e j)

/-- There are eventually no additional finite kept blocks.  A hypothetical
rogue subsequence has a compact macroscopic endpoint limit. -/
private theorem eventually_no_extra_blocks
    {ns : ℕ → ℕ} {Gs : (j : ℕ) → Graph (ns j)}
    {p : BrownianPath} (hns : Tendsto ns atTop atTop)
    (hps : Tendsto (fun j => continuousRawExploration (Gs j)) atTop (𝓝 p))
    (lam a T U : ℝ) (ha : 0 < a) (hT : 0 < T) (hTU : T < U)
    (hgood : GoodExcursionPath (centerPath p lam) lam)
    (havoid : CutoffAvoidance p lam a T U) :
    ∀ᶠ j : ℕ in atTop,
      keptBlocks (Gs j) a T U ⊆
        selectedBlocks hns hps lam a T U hgood ha j := by
  let P (j : ℕ) : Prop := ∃ z : ℕ × ℕ,
    z ∈ keptBlocks (Gs j) a T U ∧
      z ∉ selectedBlocks hns hps lam a T U hgood ha j
  let rogue (j : ℕ) : ℕ × ℕ :=
    if h : P j then Classical.choose h else (0, 0)
  have hrogue {j : ℕ} (hj : P j) :
      rogue j ∈ keptBlocks (Gs j) a T U ∧
      rogue j ∉ selectedBlocks hns hps lam a T U hgood ha j := by
    simp only [rogue, dif_pos hj]
    exact Classical.choose_spec hj
  by_contra hnot
  have hfrequent : ∃ᶠ j : ℕ in atTop, P j := by
    have hf := (Filter.not_eventually).mp hnot
    apply hf.mono
    intro j hj
    exact (Finset.not_subset.mp hj)
  obtain ⟨φ, hφ, hφP⟩ := Nat.exists_strictMono_subsequence (by
    intro N
    obtain ⟨j, hj, hPj⟩ := (Filter.frequently_atTop.mp hfrequent) (N + 1)
    exact ⟨j, by omega, hPj⟩)
  have hφtop : Tendsto φ atTop atTop := hφ.tendsto_atTop
  let zs : ℕ → ℕ × ℕ := rogue ∘ φ
  have hzkeep (j : ℕ) : zs j ∈ keptBlocks (Gs (φ j)) a T U :=
    (hrogue (hφP j)).1
  have hznot (j : ℕ) : zs j ∉
      selectedBlocks hns hps lam a T U hgood ha (φ j) :=
    (hrogue (hφP j)).2
  have hUpos : 0 < U := hT.trans hTU
  have hzblock : ∀ᶠ j : ℕ in atTop,
      (zs j).1 < (zs j).2 ∧ (zs j).2 ≤ ns (φ j) ∧
      successiveMeshRecords (ns (φ j)) (zs j).1 (zs j).2
        (continuousRawExploration (Gs (φ j))) := by
    filter_upwards [(hns.comp hφtop).eventually_ge_atTop 1] with j hn
    have hk := (mem_keptBlocks (Gs (φ j)) a T U (zs j)).mp (hzkeep j)
    have hb := (mem_queueBlocks (Gs (φ j)) (zs j)).mp hk.1
    exact ⟨hb.1, hb.2.2.1.1,
      (queueBlock_iff_meshRecords (Gs (φ j)) hn (zs j)).mp hb⟩
  have hzU : ∀ᶠ j : ℕ in atTop,
      meshTime (ns (φ j)) (zs j).2 ≤ Real.toNNReal U := by
    apply Filter.Eventually.of_forall
    intro j
    have hu := ((mem_keptBlocks (Gs (φ j)) a T U (zs j)).mp (hzkeep j)).2.2.2.1
    apply NNReal.coe_le_coe.mp
    rw [Real.coe_toNNReal U hUpos.le]
    exact hu.le
  have hzlong : ∀ᶠ j : ℕ in atTop,
      a ≤ meshBlockLength (ns (φ j)) (zs j).1 (zs j).2 := by
    apply Filter.Eventually.of_forall
    intro j
    exact ((mem_keptBlocks (Gs (φ j)) a T U (zs j)).mp
      (hzkeep j)).2.2.2.2.le
  obtain ⟨s, t, ψ, hψ, hmatch, hlength, hexc⟩ :=
    no_spurious_long_blocks_on_compact (hns.comp hφtop)
      (hps.comp hφtop) lam hgood zs (Real.toNNReal U) a ha
      hzblock hzU hzlong
  have hψtop : Tendsto ψ atTop atTop := hψ.tendsto_atTop
  have hsreal : Tendsto (fun j =>
      (meshTime (ns (φ (ψ j))) (zs (ψ j)).1 : ℝ)) atTop (𝓝 (s : ℝ)) :=
    (NNReal.continuous_coe.tendsto s).comp hmatch.2.1
  have htreal : Tendsto (fun j =>
      (meshTime (ns (φ (ψ j))) (zs (ψ j)).2 : ℝ)) atTop (𝓝 (t : ℝ)) :=
    (NNReal.continuous_coe.tendsto t).comp hmatch.2.2
  have hstartBound : (s : ℝ) ≤ T := by
    apply le_of_tendsto_of_tendsto hsreal tendsto_const_nhds
    apply Filter.Eventually.of_forall
    intro j
    exact (((mem_keptBlocks (Gs (φ (ψ j))) a T U (zs (ψ j))).mp
      (hzkeep (ψ j))).2.2.1).le
  have hendBound : (t : ℝ) ≤ U := by
    apply le_of_tendsto_of_tendsto htreal tendsto_const_nhds
    apply Filter.Eventually.of_forall
    intro j
    exact (((mem_keptBlocks (Gs (φ (ψ j))) a T U (zs (ψ j))).mp
      (hzkeep (ψ j))).2.2.2.1).le
  have hav := havoid (s, t) hexc
  have hlenStrict : a < excursionLength (s, t) := by
    change a < (t : ℝ) - (s : ℝ)
    exact lt_of_le_of_ne hlength (Ne.symm hav.1)
  have hsStrict : (s : ℝ) < T := lt_of_le_of_ne hstartBound hav.2.1
  have htStrict : (t : ℝ) < U := lt_of_le_of_ne hendBound hav.2.2
  have he : (s, t) ∈ limitKeptExcursions p lam a T U hgood ha :=
    (mem_limitKeptExcursions p lam a T U hgood ha (s, t)).mpr
      ⟨hexc, hlenStrict, hsStrict, htStrict⟩
  let e : KeptExcursion p lam a T U hgood ha := ⟨(s, t), he⟩
  let ws (j : ℕ) := selectedBlock hns hps lam a T U hgood ha e (φ (ψ j))
  have hselected := selectedBlock_spec hns hps lam a T U hgood ha e
  have hwmatch : MatchedBlockSequence atTop
      (ns ∘ φ ∘ ψ) (fun j => Gs (φ (ψ j))) ws s t := by
    refine ⟨(hφtop.comp hψtop).eventually hselected.1, ?_, ?_⟩
    · exact hselected.2.1.comp (hφtop.comp hψtop)
    · exact hselected.2.2.comp (hφtop.comp hψtop)
  have heq := matched_blocks_eventually_equal
    (hns.comp (hφtop.comp hψtop)) hexc.1 hmatch hwmatch
  obtain ⟨j, hj⟩ := heq.exists
  have hmem : ws j ∈ selectedBlocks hns hps lam a T U hgood ha (φ (ψ j)) := by
    exact Finset.mem_image.mpr ⟨e, Finset.mem_univ _, rfl⟩
  have hbad : zs (ψ j) ∈
      selectedBlocks hns hps lam a T U hgood ha (φ (ψ j)) := by
    rw [show zs (ψ j) = ws j from hj]
    exact hmem
  exact (hznot (ψ j)) hbad

/-- Eventual equality of the literal finite kept BFS list with the image of
the finite limiting kept-excursion list.  The image map is injective, so this
is an eventual bijection with multiplicity retained. -/
theorem eventual_kept_bijection
    {ns : ℕ → ℕ} {Gs : (j : ℕ) → Graph (ns j)}
    {p : BrownianPath} (hns : Tendsto ns atTop atTop)
    (hps : Tendsto (fun j => continuousRawExploration (Gs j)) atTop (𝓝 p))
    (lam a T U : ℝ) (ha : 0 < a) (hT : 0 < T) (hTU : T < U)
    (hgood : GoodExcursionPath (centerPath p lam) lam)
    (havoid : CutoffAvoidance p lam a T U) :
    ∀ᶠ j : ℕ in atTop,
      keptBlocks (Gs j) a T U =
        selectedBlocks hns hps lam a T U hgood ha j ∧
      Function.Injective (fun e : KeptExcursion p lam a T U hgood ha =>
        selectedBlock hns hps lam a T U hgood ha e j) := by
  filter_upwards [eventually_selected_kept hns hps lam a T U hgood ha,
      eventually_selected_injective hns hps lam a T U hgood ha,
      eventually_no_extra_blocks hns hps lam a T U ha hT hTU hgood havoid]
    with j hkeep hinj hsubset
  constructor
  · apply Finset.Subset.antisymm hsubset
    intro z hz
    obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp hz
    exact hkeep e
  · exact hinj

/-- The least dense probe of a kept excursion. -/
def selectedCode (p : BrownianPath) (lam a T U : ℝ)
    (hgood : GoodExcursionPath (centerPath p lam) lam) (ha : 0 < a)
    (e : KeptExcursion p lam a T U hgood ha) : ℕ :=
  Classical.choose (retainedCode_represents_excursion p lam
    ((mem_limitKeptExcursions p lam a T U hgood ha e.1).mp e.2).1)

private theorem selectedCode_spec (p : BrownianPath) (lam a T U : ℝ)
    (hgood : GoodExcursionPath (centerPath p lam) lam) (ha : 0 < a)
    (e : KeptExcursion p lam a T U hgood ha) :
    retainedCode lam (selectedCode p lam a T U hgood ha e) p ∧
    codeTime (selectedCode p lam a T U hgood ha e) ∈ Ioo e.1.1 e.1.2 := by
  have hs := (Classical.choose_spec (retainedCode_represents_excursion p lam
    ((mem_limitKeptExcursions p lam a T U hgood ha e.1).mp e.2).1)).1
  exact ⟨hs.1, hs.2.1⟩

private theorem selectedCode_pair (p : BrownianPath) (lam a T U : ℝ)
    (hgood : GoodExcursionPath (centerPath p lam) lam) (ha : 0 < a)
    (e : KeptExcursion p lam a T U hgood ha) :
    codedExcursionPair lam (selectedCode p lam a T U hgood ha e) p = e.1 := by
  have hs := Classical.choose_spec (retainedCode_represents_excursion p lam
    ((mem_limitKeptExcursions p lam a T U hgood ha e.1).mp e.2).1)
  have hleft : codedLeft lam
      (codeTime (selectedCode p lam a T U hgood ha e)) p = (e.1.1 : ENNReal) :=
    hs.1.2.2.1
  have hright : codedRight lam
      (codeTime (selectedCode p lam a T U hgood ha e)) p = (e.1.2 : ENNReal) :=
    hs.1.2.2.2.1
  simp [codedExcursionPair, hleft, hright]

private theorem selectedCode_injective (p : BrownianPath) (lam a T U : ℝ)
    (hgood : GoodExcursionPath (centerPath p lam) lam) (ha : 0 < a) :
    Function.Injective (selectedCode p lam a T U hgood ha) := by
  intro e f hef
  apply Subtype.ext
  have he := selectedCode_pair p lam a T U hgood ha e
  have hf := selectedCode_pair p lam a T U hgood ha f
  rw [hef] at he
  exact he.symm.trans hf

def selectedCodeSupport (p : BrownianPath) (lam a T U : ℝ)
    (hgood : GoodExcursionPath (centerPath p lam) lam) (ha : 0 < a) :
    Finset ℕ :=
  (Finset.univ : Finset (KeptExcursion p lam a T U hgood ha)).image
    (selectedCode p lam a T U hgood ha)

private theorem selectedCode_value (p : BrownianPath) (lam a T U : ℝ)
    (hgood : GoodExcursionPath (centerPath p lam) lam) (ha : 0 < a)
    (e : KeptExcursion p lam a T U hgood ha) :
    limitKeptLength lam a T U (selectedCode p lam a T U hgood ha e) p =
      ENNReal.ofReal (excursionLength e.1) := by
  have he := (mem_limitKeptExcursions p lam a T U hgood ha e.1).mp e.2
  rw [limitKeptLength_eq_of_excursion p lam a T U he.1
    (selectedCode_spec p lam a T U hgood ha e).1
    (selectedCode_spec p lam a T U hgood ha e).2]
  rw [if_pos (show a < (e.1.2 : ℝ) - (e.1.1 : ℝ) ∧
      (e.1.1 : ℝ) < T ∧ (e.1.2 : ℝ) < U from he.2)]
  rfl

/-- All positive limit candidates lie on the finite list of least probes.
In particular the countable dense code contributes no duplicate candidate. -/
theorem limitKeptLength_zero_outside_support (p : BrownianPath)
    (lam a T U : ℝ) (hgood : GoodExcursionPath (centerPath p lam) lam)
    (ha : 0 < a) (m : ℕ)
    (hm : m ∉ selectedCodeSupport p lam a T U hgood ha) :
    limitKeptLength lam a T U m p = 0 := by
  by_cases hret : retainedCode lam m p
  · obtain ⟨hexc, hq, _⟩ :=
      retainedCode_excursion_of_escape p lam hgood.1 hret
    let e := codedExcursionPair lam m p
    by_cases hkept : LimitKept p lam a T U e
    · have he : e ∈ limitKeptExcursions p lam a T U hgood ha :=
        (mem_limitKeptExcursions p lam a T U hgood ha e).mpr hkept
      let ee : KeptExcursion p lam a T U hgood ha := ⟨e, he⟩
      have hcode : m = selectedCode p lam a T U hgood ha ee :=
        retainedCode_unique_in_excursion p lam hexc hret
          (selectedCode_spec p lam a T U hgood ha ee).1 hq
          (selectedCode_spec p lam a T U hgood ha ee).2
      exact False.elim (hm (Finset.mem_image.mpr
        ⟨ee, Finset.mem_univ _, hcode.symm⟩))
    · rw [limitKeptLength_eq_of_excursion p lam a T U hexc hret hq]
      have hguard : ¬ (a < excursionLength e ∧ (e.1 : ℝ) < T ∧
          (e.2 : ℝ) < U) := by
        intro hg
        exact hkept ⟨hexc, hg⟩
      change (if a < excursionLength e ∧ (e.1 : ℝ) < T ∧
        (e.2 : ℝ) < U then ENNReal.ofReal (excursionLength e) else 0) = 0
      exact if_neg hguard
  · have hzero := codedLength_eq_zero_of_not_retained p lam hret
    simp [limitKeptLength, hzero]

/-- Exact positive threshold count for the limiting countable code, reduced
to the finite excursion list. -/
theorem limit_rank_threshold (p : BrownianPath) (lam a T U : ℝ)
    (hgood : GoodExcursionPath (centerPath p lam) lam) (ha : 0 < a)
    (i : ℕ) (hi : 0 < i) (x : ENNReal) (hx : 0 < x) :
    x ≤ rankFromCandidates (limitKeptLength lam a T U) i p ↔
      i ≤ ((Finset.univ : Finset (KeptExcursion p lam a T U hgood ha)).filter
        (fun e => x ≤ ENNReal.ofReal (excursionLength e.1))).card := by
  rw [rankFromCandidates_threshold_of_finite_support
    (limitKeptLength lam a T U) p
    (selectedCodeSupport p lam a T U hgood ha)
    (limitKeptLength_zero_outside_support p lam a T U hgood ha)
    i hi x hx]
  have hsets :
      (selectedCodeSupport p lam a T U hgood ha).filter
        (fun m => x ≤ limitKeptLength lam a T U m p) =
      ((Finset.univ : Finset (KeptExcursion p lam a T U hgood ha)).filter
        (fun e => x ≤ ENNReal.ofReal (excursionLength e.1))).image
          (selectedCode p lam a T U hgood ha) := by
    ext m
    constructor
    · intro hm
      obtain ⟨e, _, heq⟩ := Finset.mem_image.mp
        (Finset.mem_filter.mp hm).1
      have hv := (Finset.mem_filter.mp hm).2
      rw [← heq, selectedCode_value] at hv
      exact Finset.mem_image.mpr ⟨e,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩, heq⟩
    · intro hm
      obtain ⟨e, he, heq⟩ := Finset.mem_image.mp hm
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_image.mpr ⟨e, Finset.mem_univ _, heq⟩, ?_⟩
      rw [← heq, selectedCode_value]
      exact (Finset.mem_filter.mp he).2
  rw [hsets]
  rw [Finset.card_image_iff.mpr (fun e _ f _ hef =>
    selectedCode_injective p lam a T U hgood ha hef)]

private theorem eventual_discrete_rank_threshold
    {ns : ℕ → ℕ} {Gs : (j : ℕ) → Graph (ns j)}
    {p : BrownianPath} (hns : Tendsto ns atTop atTop)
    (hps : Tendsto (fun j => continuousRawExploration (Gs j)) atTop (𝓝 p))
    (lam a T U : ℝ) (ha : 0 < a) (hT : 0 < T) (hTU : T < U)
    (hgood : GoodExcursionPath (centerPath p lam) lam)
    (havoid : CutoffAvoidance p lam a T U)
    (i : ℕ) (hi : 0 < i) :
    ∀ᶠ j : ℕ in atTop, ∀ x : ENNReal, 0 < x →
      (x ≤ rankFromCandidates
        (fun m => discreteKeptLength (ns j) a T U (pairCode m)) i
        (continuousRawExploration (Gs j)) ↔
        i ≤ ((Finset.univ : Finset (KeptExcursion p lam a T U hgood ha)).filter
          (fun e => x ≤ ENNReal.ofReal
            (meshBlockLength (ns j)
              (selectedBlock hns hps lam a T U hgood ha e j).1
              (selectedBlock hns hps lam a T U hgood ha e j).2))).card) := by
  filter_upwards [eventual_kept_bijection hns hps lam a T U ha hT hTU
      hgood havoid, hns.eventually_ge_atTop 1] with j hj hn x hx
  rw [discreteTruncatedRank_threshold (Gs j) hn a T U i hi x hx,
    hj.1]
  have hsets :
      ((selectedBlocks hns hps lam a T U hgood ha j).filter
        (fun z => x ≤ ENNReal.ofReal (meshBlockLength (ns j) z.1 z.2))) =
      ((Finset.univ : Finset (KeptExcursion p lam a T U hgood ha)).filter
        (fun e => x ≤ ENNReal.ofReal
          (meshBlockLength (ns j)
            (selectedBlock hns hps lam a T U hgood ha e j).1
            (selectedBlock hns hps lam a T U hgood ha e j).2))).image
        (fun e => selectedBlock hns hps lam a T U hgood ha e j) := by
    ext z
    simp only [selectedBlocks, Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨⟨e, _, rfl⟩, hv⟩
      exact ⟨e, ⟨Finset.mem_univ _, hv⟩, rfl⟩
    · rintro ⟨e, ⟨_, hv⟩, rfl⟩
      exact ⟨⟨e, Finset.mem_univ _, rfl⟩, hv⟩
  rw [hsets]
  rw [Finset.card_image_iff.mpr (fun e _ f _ hef => hj.2 hef)]

/-- Finite threshold counts are a continuous sorting interface.  The proof
uses only cardinal inequalities, so equal values keep their multiplicity and
missing ranks are automatically zero. -/
private theorem finite_threshold_rank_tendsto
    {α : Type*} [DecidableEq α] (H : Finset α)
    (u : α → ENNReal) (us : ℕ → α → ENNReal)
    (i : ℕ) (hi : 0 < i)
    (hu : ∀ e ∈ H, Tendsto (fun j => us j e) atTop (𝓝 (u e)))
    (hutop : ∀ e ∈ H, u e ≠ ⊤)
    (R : ENNReal) (Rs : ℕ → ENNReal)
    (hR : ∀ x : ENNReal, 0 < x →
      (x ≤ R ↔ i ≤ (H.filter (fun e => x ≤ u e)).card))
    (hRs : ∀ᶠ j : ℕ in atTop, ∀ x : ENNReal, 0 < x →
      (x ≤ Rs j ↔ i ≤ (H.filter (fun e => x ≤ us j e)).card)) :
    R ≠ ⊤ ∧ Tendsto Rs atTop (𝓝 R) := by
  have hRtop : R ≠ ⊤ := by
    intro htop
    have hcount := (hR ⊤ (by simp)).mp (by simp [htop])
    have hempty : H.filter (fun e => (⊤ : ENNReal) ≤ u e) = ∅ := by
      ext e
      by_cases he : e ∈ H
      · simp [he, hutop e he]
      · simp [he]
    rw [hempty] at hcount
    simp at hcount
    omega
  refine ⟨hRtop, (tendsto_order.mpr ⟨?_, ?_⟩)⟩
  · intro r hr
    obtain ⟨x, hrx, hxR⟩ := exists_between hr
    obtain ⟨y, hxy, hyR⟩ := exists_between hxR
    have hxpos : 0 < x := lt_of_le_of_lt bot_le hrx
    have hypos : 0 < y := hxpos.trans hxy
    have hcount : i ≤ (H.filter (fun e => y ≤ u e)).card :=
      (hR y hypos).mp hyR.le
    have hpoint : ∀ e ∈ H, ∀ᶠ j : ℕ in atTop,
        y ≤ u e → x ≤ us j e := by
      intro e he
      by_cases hy : y ≤ u e
      · exact ((hu e he).eventually_const_le (hxy.trans_le hy)).mono
          (fun _ hj _ => hj)
      · exact Filter.Eventually.of_forall (fun _ h => False.elim (hy h))
    have hall : ∀ᶠ j : ℕ in atTop,
        ∀ e ∈ H, y ≤ u e → x ≤ us j e :=
      (Filter.eventually_all_finset (I := H)).2 hpoint
    filter_upwards [hRs, hall] with j hrank hj
    have hsub : H.filter (fun e => y ≤ u e) ⊆
        H.filter (fun e => x ≤ us j e) := by
      intro e he
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp he).1,
        hj e (Finset.mem_filter.mp he).1 (Finset.mem_filter.mp he).2⟩
    have hx : x ≤ Rs j := (hrank x hxpos).mpr
      (hcount.trans (Finset.card_le_card hsub))
    exact hrx.trans_le hx
  · intro r hr
    obtain ⟨y, hRy, hyr⟩ := exists_between hr
    obtain ⟨x, hyx, hxr⟩ := exists_between hyr
    have hypos : 0 < y := lt_of_le_of_lt bot_le hRy
    have hxpos : 0 < x := hypos.trans hyx
    have hcount : (H.filter (fun e => y ≤ u e)).card < i := by
      by_contra h
      have hge : i ≤ (H.filter (fun e => y ≤ u e)).card := by omega
      exact (not_le_of_gt hRy) ((hR y hypos).mpr hge)
    have hpoint : ∀ e ∈ H, ∀ᶠ j : ℕ in atTop,
        x ≤ us j e → y ≤ u e := by
      intro e he
      by_cases hy : y ≤ u e
      · exact Filter.Eventually.of_forall (fun _ _ => hy)
      · have hlt : u e < x := (lt_of_not_ge hy).trans hyx
        exact ((hu e he).eventually_lt_const hlt).mono (fun j hj hx =>
          False.elim ((not_le_of_gt hj) hx))
    have hall : ∀ᶠ j : ℕ in atTop,
        ∀ e ∈ H, x ≤ us j e → y ≤ u e :=
      (Filter.eventually_all_finset (I := H)).2 hpoint
    filter_upwards [hRs, hall] with j hrank hj
    have hsub : H.filter (fun e => x ≤ us j e) ⊆
        H.filter (fun e => y ≤ u e) := by
      intro e he
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp he).1,
        hj e (Finset.mem_filter.mp he).1 (Finset.mem_filter.mp he).2⟩
    have hnot : ¬ x ≤ Rs j := by
      intro hx
      have hc := (hrank x hxpos).mp hx
      have hc' := hc.trans (Finset.card_le_card hsub)
      omega
    exact (lt_of_not_ge hnot).trans hxr

/-- For every coordinate, the literal discrete kept rank on actual BFS paths
converges to the dense-code limiting kept rank.  Ties and zero padding are
covered by the finite threshold lemma. -/
theorem truncated_rank_on_bfs_tendsto
    {ns : ℕ → ℕ} {Gs : (j : ℕ) → Graph (ns j)}
    {p : BrownianPath} (hns : Tendsto ns atTop atTop)
    (hps : Tendsto (fun j => continuousRawExploration (Gs j)) atTop (𝓝 p))
    (lam a T U : ℝ) (ha : 0 < a) (hT : 0 < T) (hTU : T < U)
    (hgood : GoodExcursionPath (centerPath p lam) lam)
    (havoid : CutoffAvoidance p lam a T U) (k : ℕ) :
    Tendsto (fun j => discreteTruncatedRank (ns j) a T U k
      (continuousRawExploration (Gs j))) atTop
      (𝓝 (limitTruncatedRank lam a T U k p)) := by
  apply tendsto_pi_nhds.mpr
  intro r
  let H := (Finset.univ : Finset (KeptExcursion p lam a T U hgood ha))
  let v (e : KeptExcursion p lam a T U hgood ha) : ENNReal :=
    ENNReal.ofReal (excursionLength e.1)
  let vs (j : ℕ) (e : KeptExcursion p lam a T U hgood ha) : ENNReal :=
    ENNReal.ofReal (meshBlockLength (ns j)
      (selectedBlock hns hps lam a T U hgood ha e j).1
      (selectedBlock hns hps lam a T U hgood ha e j).2)
  let i := r.val + 1
  let R := rankFromCandidates (limitKeptLength lam a T U) i p
  let Rs (j : ℕ) := rankFromCandidates
    (fun m => discreteKeptLength (ns j) a T U (pairCode m)) i
    (continuousRawExploration (Gs j))
  have hv (e : KeptExcursion p lam a T U hgood ha) :
      Tendsto (fun j => vs j e) atTop (𝓝 (v e)) :=
    (ENNReal.continuous_ofReal.tendsto _).comp
      (matched_length_tendsto hns
        (selectedBlock_spec hns hps lam a T U hgood ha e))
  have hthlim : ∀ x : ENNReal, 0 < x →
      (x ≤ R ↔ i ≤ (H.filter (fun e => x ≤ v e)).card) := by
    intro x hx
    exact limit_rank_threshold p lam a T U hgood ha i
      (Nat.zero_lt_succ _) x hx
  have hthdisc : ∀ᶠ j : ℕ in atTop, ∀ x : ENNReal, 0 < x →
      (x ≤ Rs j ↔ i ≤ (H.filter (fun e => x ≤ vs j e)).card) :=
    eventual_discrete_rank_threshold hns hps lam a T U ha hT hTU
      hgood havoid i (Nat.zero_lt_succ _)
  obtain ⟨hRtop, hRconv⟩ := finite_threshold_rank_tendsto H v vs i
    (Nat.zero_lt_succ _) (fun e _ => hv e)
    (fun e _ => ENNReal.ofReal_ne_top) R Rs hthlim hthdisc
  have hreal := (ENNReal.tendsto_toReal hRtop).comp hRconv
  simpa only [discreteTruncatedRank, limitTruncatedRank, i, R, Rs]
    using! hreal

/-- The support used by B04 consists exactly of continuous interpolations of
actual finite BFS exploration paths. -/
def actualBFSSupport (n : ℕ) : Set BrownianPath :=
  {p | ∃ G : Graph n, p = continuousRawExploration G}

/-- The B04 `hmatching` implication has the required arbitrary index sequence
quantifier and no extra premise beyond GoodExcursionPath and cutoff avoidance. -/
theorem supportStableAt_actualBFS
    (p : BrownianPath) (lam a T U : ℝ)
    (ha : 0 < a) (hT : 0 < T) (hTU : T < U)
    (hgood : GoodExcursionPath (centerPath p lam) lam)
    (havoid : CutoffAvoidance p lam a T U) (k : ℕ) :
    SupportStableAt actualBFSSupport
      (fun n => discreteTruncatedRank n a T U k)
      (limitTruncatedRank lam a T U k) p := by
  intro ns ps hns hmem hps
  let Gs (j : ℕ) : Graph (ns j) := Classical.choose (hmem j)
  have hrepr (j : ℕ) : ps j = continuousRawExploration (Gs j) :=
    Classical.choose_spec (hmem j)
  have hpaths : Tendsto (fun j => continuousRawExploration (Gs j))
      atTop (𝓝 p) := hps.congr' (Filter.Eventually.of_forall
        (fun j => hrepr j))
  have hresult := truncated_rank_on_bfs_tendsto hns hpaths lam a T U
    ha hT hTU hgood havoid k
  exact hresult.congr' (Filter.Eventually.of_forall
    (fun j => congrArg (discreteTruncatedRank (ns j) a T U k)
      (hrepr j).symm))

end

end Erdos745.WrapUp.Proofs.Internal.W15_CRITICAL_SupportMatching


/-!
# Weak convergence of the actual truncated BFS ranks

The limiting path law here is the pushforward of the Brownian law by the
critical drift.  The code in `Truncated` centers that path before extracting
excursions.  The finite laws are defined at every index, including indices at
which the fixed-edge model is inadmissible.
-/

namespace Erdos745.WrapUp.Proofs.Internal.W15_CRITICAL_KeptWeak

open Erdos745.WrapUp
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_Interpolation
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_FiniteLaw
open Erdos745.WrapUp.Proofs.Internal.W15_CRITICAL_Truncated
open Erdos745.WrapUp.Proofs.Internal.W15_CRITICAL_Code
open Erdos745.WrapUp.Proofs.Internal.W15_CRITICAL_SupportMatching
open Filter MeasureTheory Set
open scoped Topology ENNReal

noncomputable section
attribute [local instance] Classical.propDecidable
local instance : MeasurableSpace BrownianPath := borel BrownianPath
local instance : BorelSpace BrownianPath := ⟨rfl⟩
local instance graphMeasurableSpace (n : ℕ) : MeasurableSpace (Graph n) := ⊤

/-- The two deterministic path corrections cancel.  In particular the
excursion drift is applied exactly once. -/
@[simp] theorem centerPath_driftPath (w : BrownianPath) (lam : ℝ) :
    centerPath (driftPath w lam) lam = w := by
  ext t
  simp [centerPath, centerCorrection, driftPath, drift]

theorem continuous_driftPath (lam : ℝ) :
    Continuous (fun w : BrownianPath ↦ driftPath w lam) := by
  have h : (fun w : BrownianPath ↦ driftPath w lam) =
      (fun w : BrownianPath ↦ w - centerCorrection lam) := by
    funext w
    ext t
    simp [driftPath, drift, centerCorrection]
    ring
  rw [h]
  fun_prop

theorem measurable_driftPath (lam : ℝ) :
    Measurable (fun w : BrownianPath ↦ driftPath w lam) :=
  (continuous_driftPath lam).measurable

def driftedPathLaw (mu : PathLaw) (lam : ℝ) : PathLaw :=
  Measure.map (fun w : BrownianPath ↦ driftPath w lam) mu

theorem driftedPathLaw_probability (mu : PathLaw) (lam : ℝ)
    [IsProbabilityMeasure mu] : IsProbabilityMeasure (driftedPathLaw mu lam) := by
  unfold driftedPathLaw
  exact Measure.isProbabilityMeasure_map (measurable_driftPath lam).aemeasurable

def driftedProbability (mu : PathLaw) (hmu : IsProbabilityMeasure mu)
    (lam : ℝ) : ProbabilityMeasure BrownianPath := by
  letI := hmu
  exact ⟨driftedPathLaw mu lam, driftedPathLaw_probability mu lam⟩

theorem centerPath_map_driftedPathLaw (mu : PathLaw) (lam : ℝ) :
    Measure.map (fun p : BrownianPath ↦ centerPath p lam)
      (driftedPathLaw mu lam) = mu := by
  rw [driftedPathLaw, Measure.map_map
    (measurable_centerPath lam) (measurable_driftPath lam)]
  have hfun : (fun p : BrownianPath ↦ centerPath p lam) ∘
      (fun w : BrownianPath ↦ driftPath w lam) = id := by
    funext w
    exact centerPath_driftPath w lam
  rw [hfun, Measure.map_id]

/-- The public Brownian a.e. theorem transfers without asserting that the
whole good-path proposition is Borel. -/
theorem ae_good_centered_drift (hBrownian : BrownianFoundationStatement)
    (mu : PathLaw) (hmu : BrownianLaw mu) (lam : ℝ) :
    ∀ᵐ p ∂driftedPathLaw mu lam,
      GoodExcursionPath (centerPath p lam) lam := by
  have hgood : ∀ᵐ w ∂mu, GoodExcursionPath w lam :=
    (hBrownian.2 mu hmu lam).1
  have hmap : ∀ᵐ w ∂Measure.map (fun p : BrownianPath ↦ centerPath p lam)
      (driftedPathLaw mu lam), GoodExcursionPath w lam := by
    rw [centerPath_map_driftedPathLaw]
    exact hgood
  exact ae_of_ae_map (measurable_centerPath lam).aemeasurable hmap

def lengthValue (lam : ℝ) (m : ℕ) (p : BrownianPath) : ℝ :=
  (codedLength lam m p).toReal

def startValue (lam : ℝ) (m : ℕ) (p : BrownianPath) : ℝ :=
  (codedLeft lam (codeTime m) p).toReal

def endValue (lam : ℝ) (m : ℕ) (p : BrownianPath) : ℝ :=
  (codedRight lam (codeTime m) p).toReal

private theorem measurable_lengthValue (lam : ℝ) (m : ℕ) :
    Measurable (lengthValue lam m) :=
  (measurable_codedLength lam m).ennreal_toReal

private theorem measurable_startValue (lam : ℝ) (m : ℕ) :
    Measurable (startValue lam m) :=
  (measurable_codedLeft lam (codeTime m)).ennreal_toReal

private theorem measurable_endValue (lam : ℝ) (m : ℕ) :
    Measurable (endValue lam m) :=
  (measurable_codedRight lam (codeTime m)).ennreal_toReal

private theorem boundaryMeasure_eq (mu : PathLaw) (lam : ℝ)
    (v : BrownianPath → ℝ) (hv : Measurable v) (x : ℝ) :
    driftedPathLaw mu lam {p | v p = x} =
      mu {w | v (driftPath w lam) = x} := by
  change (Measure.map (fun w : BrownianPath ↦ driftPath w lam) mu)
    (v ⁻¹' {x}) = mu ((v ∘ fun w : BrownianPath ↦ driftPath w lam) ⁻¹' {x})
  exact Measure.map_apply (measurable_driftPath lam)
    (hv (measurableSet_singleton x))

def lengthAtoms (nu : PathLaw) (lam : ℝ) : Set ℝ :=
  ⋃ m : ℕ, {x | 0 < nu {p | lengthValue lam m p = x}}

def startAtoms (nu : PathLaw) (lam : ℝ) : Set ℝ :=
  ⋃ m : ℕ, {x | 0 < nu {p | startValue lam m p = x}}

def endAtoms (nu : PathLaw) (lam : ℝ) : Set ℝ :=
  ⋃ m : ℕ, {x | 0 < nu {p | endValue lam m p = x}}

theorem countable_lengthAtoms (nu : PathLaw) [IsProbabilityMeasure nu]
    (lam : ℝ) : (lengthAtoms nu lam).Countable := by
  unfold lengthAtoms
  exact Set.countable_iUnion (fun m =>
    Measure.countable_meas_level_set_pos (measurable_lengthValue lam m))

theorem countable_startAtoms (nu : PathLaw) [IsProbabilityMeasure nu]
    (lam : ℝ) : (startAtoms nu lam).Countable := by
  unfold startAtoms
  exact Set.countable_iUnion (fun m =>
    Measure.countable_meas_level_set_pos (measurable_startValue lam m))

theorem countable_endAtoms (nu : PathLaw) [IsProbabilityMeasure nu]
    (lam : ℝ) : (endAtoms nu lam).Countable := by
  unfold endAtoms
  exact Set.countable_iUnion (fun m =>
    Measure.countable_meas_level_set_pos (measurable_endValue lam m))

/-- This is the exact public boundary condition, expressed on the original
Brownian law.  Its variables are the code variables of the once-drifted path. -/
def CodedBoundaryNull (mu : PathLaw) (lam a T U : ℝ) : Prop :=
  (∀ m, mu {w | lengthValue lam m (driftPath w lam) = a} = 0) ∧
  (∀ m, mu {w | startValue lam m (driftPath w lam) = T} = 0) ∧
  (∀ m, mu {w | endValue lam m (driftPath w lam) = U} = 0)

theorem codedBoundaryNull_of_not_atoms (mu : PathLaw) (lam a T U : ℝ)
    (ha : a ∉ lengthAtoms (driftedPathLaw mu lam) lam)
    (hT : T ∉ startAtoms (driftedPathLaw mu lam) lam)
    (hU : U ∉ endAtoms (driftedPathLaw mu lam) lam) :
    CodedBoundaryNull mu lam a T U := by
  refine ⟨fun m => ?_, fun m => ?_, fun m => ?_⟩
  · have hzero : driftedPathLaw mu lam {p | lengthValue lam m p = a} = 0 := by
      apply le_antisymm _ bot_le
      exact not_lt.mp (fun hpos => ha (Set.mem_iUnion_of_mem m hpos))
    rw [boundaryMeasure_eq mu lam (lengthValue lam m)
      (measurable_lengthValue lam m) a] at hzero
    exact hzero
  · have hzero : driftedPathLaw mu lam {p | startValue lam m p = T} = 0 := by
      apply le_antisymm _ bot_le
      exact not_lt.mp (fun hpos => hT (Set.mem_iUnion_of_mem m hpos))
    rw [boundaryMeasure_eq mu lam (startValue lam m)
      (measurable_startValue lam m) T] at hzero
    exact hzero
  · have hzero : driftedPathLaw mu lam {p | endValue lam m p = U} = 0 := by
      apply le_antisymm _ bot_le
      exact not_lt.mp (fun hpos => hU (Set.mem_iUnion_of_mem m hpos))
    rw [boundaryMeasure_eq mu lam (endValue lam m)
      (measurable_endValue lam m) U] at hzero
    exact hzero

private theorem ae_no_coded_equalities (mu : PathLaw) (lam a T U : ℝ)
    (hnull : CodedBoundaryNull mu lam a T U) :
    ∀ᵐ p ∂driftedPathLaw mu lam, ∀ m,
      lengthValue lam m p ≠ a ∧ startValue lam m p ≠ T ∧
        endValue lam m p ≠ U := by
  apply ae_all_iff.mpr
  intro m
  have hl : driftedPathLaw mu lam
      {p | lengthValue lam m p = a} = 0 := by
    rw [boundaryMeasure_eq mu lam (lengthValue lam m)
      (measurable_lengthValue lam m) a]
    exact hnull.1 m
  have hs : driftedPathLaw mu lam
      {p | startValue lam m p = T} = 0 := by
    rw [boundaryMeasure_eq mu lam (startValue lam m)
      (measurable_startValue lam m) T]
    exact hnull.2.1 m
  have ht : driftedPathLaw mu lam
      {p | endValue lam m p = U} = 0 := by
    rw [boundaryMeasure_eq mu lam (endValue lam m)
      (measurable_endValue lam m) U]
    exact hnull.2.2 m
  filter_upwards [(measure_eq_zero_iff_ae_notMem).mp hl,
      (measure_eq_zero_iff_ae_notMem).mp hs,
      (measure_eq_zero_iff_ae_notMem).mp ht] with p hlen hstart hend
  exact ⟨hlen, hstart, hend⟩

theorem ae_cutoffAvoidance (mu : PathLaw) (lam a T U : ℝ)
    (hgood : ∀ᵐ p ∂driftedPathLaw mu lam,
      GoodExcursionPath (centerPath p lam) lam)
    (hnull : CodedBoundaryNull mu lam a T U) :
    ∀ᵐ p ∂driftedPathLaw mu lam, CutoffAvoidance p lam a T U := by
  filter_upwards [hgood, ae_no_coded_equalities mu lam a T U hnull]
    with p hp hc
  intro e he
  obtain ⟨m, hm, _⟩ := retainedCode_represents_excursion p lam he
  rcases hm with ⟨_, _, hleft, hright, hlength⟩
  have hnonneg : 0 ≤ (e.2 : ℝ) - (e.1 : ℝ) := by
    exact sub_nonneg.mpr (mod_cast he.1.le)
  have hlen : lengthValue lam m p = excursionLength e := by
    change (codedLength lam m p).toReal = (e.2 : ℝ) - (e.1 : ℝ)
    rw [hlength, ENNReal.toReal_ofReal hnonneg]
  have hstart : startValue lam m p = (e.1 : ℝ) := by
    simp [startValue, hleft]
  have hend : endValue lam m p = (e.2 : ℝ) := by
    simp [endValue, hright]
  exact ⟨fun h => (hc m).1 (hlen.trans h),
    fun h => (hc m).2.1 (hstart.trans h),
    fun h => (hc m).2.2 (hend.trans h)⟩

/-- Countable atom avoidance permits choices in any prescribed positive open
intervals; the length choice also avoids twice every length atom for B05. -/
def finitePathProbability (M : NatSeq) (n : ℕ) :
    ProbabilityMeasure BrownianPath :=
  if h : M n ≤ capacity n then
    ⟨explorationPathMeasure n (M n) h, inferInstance⟩
  else
    ⟨Measure.dirac (continuousRawExploration (∅ : Graph n)), inferInstance⟩

theorem finitePathProbability_support (M : NatSeq) (n : ℕ) :
    ∀ᵐ p ∂(finitePathProbability M n : Measure BrownianPath),
      p ∈ actualBFSSupport n := by
  unfold finitePathProbability
  split_ifs with h
  · change ∀ᵐ p ∂explorationPathMeasure n (M n) h,
      p ∈ actualBFSSupport n
    unfold explorationPathMeasure
    have hrepr : actualBFSSupport n =
        Set.range (fun G : Graph n => explorationInterpolation n G) := by
      ext p
      simp [actualBFSSupport, explorationInterpolation, eq_comm]
    rw [hrepr]
    exact ae_map_mem_range
      (by simpa [actualBFSSupport, explorationInterpolation] using!
        (Set.finite_range (fun G : Graph n => continuousRawExploration G)).measurableSet)
      (measurable_explorationInterpolation n).aemeasurable
  · change ∀ᵐ p ∂Measure.dirac (continuousRawExploration (∅ : Graph n)),
        p ∈ actualBFSSupport n
    rw [ae_dirac_eq]
    exact ⟨(∅ : Graph n), rfl⟩

theorem finitePathProbability_tendsto (hExploration : ExplorationStatement)
    (M : NatSeq) (lam : ℝ) (mu : PathLaw)
    (hwindow : criticalWindow M lam) (hmu : BrownianLaw mu) :
    Tendsto (finitePathProbability M) atTop
      (𝓝 (driftedProbability mu hmu.1 lam)) := by
  obtain ⟨Phi, hPhi, hWeak⟩ := hExploration
  have hpath (n : ℕ) (G : Graph n) : Phi n G = explorationInterpolation n G := by
    apply ContinuousMap.ext
    intro t
    exact (hPhi n G t).trans
      (explorationInterpolation_isInterpolation n G t).symm
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro F
  obtain ⟨C, hC⟩ := F.bounded
  have hbounded : ∃ D : ℝ, ∀ p : BrownianPath, |F p| ≤ D := by
    refine ⟨C + |F (0 : BrownianPath)|, ?_⟩
    intro p
    calc
      |F p| ≤ |F p - F (0 : BrownianPath)| + |F (0 : BrownianPath)| := by
        simpa only [sub_add_cancel] using!
          (abs_add_le (F p - F (0 : BrownianPath)) (F (0 : BrownianPath)))
      _ ≤ C + |F (0 : BrownianPath)| := by
        gcongr
        simpa [Real.dist_eq] using! hC p 0
  have hweak := (hWeak M lam mu hwindow hmu).1 F F.continuous hbounded
  have hfinite : (fun n => ∫ p, F p ∂(finitePathProbability M n : Measure BrownianPath)) =ᶠ[atTop]
      (fun n => expectM n (M n) (fun G => F (Phi n G))) := by
    filter_upwards [hwindow.1] with n hn
    simp only [finitePathProbability, dif_pos hn]
    change (∫ p, F p ∂explorationPathMeasure n (M n) hn) = _
    rw [explorationPathMeasure_integral n (M n) hn F F.continuous]
    congr 1
    funext G
    rw [hpath n G]
  have hlimit : (∫ p, F p ∂(driftedProbability mu hmu.1 lam : Measure BrownianPath)) =
      ∫ w, F (driftPath w lam) ∂mu := by
    change (∫ p, F p ∂driftedPathLaw mu lam) = _
    unfold driftedPathLaw
    exact MeasureTheory.integral_map (measurable_driftPath lam).aemeasurable
      F.continuous.aestronglyMeasurable
  rw [hlimit]
  exact hweak.congr' hfinite.symm

/-- The public truncated weak law has only Brownian foundation, exploration,
critical-window and measurable coded-boundary premises. -/
theorem truncated_rank_weak_of_public
    (hBrownian : BrownianFoundationStatement)
    (hExploration : ExplorationStatement)
    (M : NatSeq) (lam : ℝ) (mu : PathLaw)
    (hwindow : criticalWindow M lam) (hmu : BrownianLaw mu)
    (a T U : ℝ) (ha : 0 < a) (hT : 0 < T) (hTU : T < U)
    (hnull : CodedBoundaryNull mu lam a T U) (k : ℕ) :
    Tendsto (fun n => (finitePathProbability M n).map (discreteTruncatedRank n a T U k)) atTop
      (𝓝 ((driftedProbability mu hmu.1 lam).map (limitTruncatedRank lam a T U k))) := by
  have hgood := ae_good_centered_drift hBrownian mu hmu lam
  have havoid := ae_cutoffAvoidance mu lam a T U hgood hnull
  have hmatching : ∀ᵐ p ∂driftedPathLaw mu lam,
      SupportStableAt actualBFSSupport
        (fun n => discreteTruncatedRank n a T U k)
        (limitTruncatedRank lam a T U k) p := by
    filter_upwards [hgood, havoid] with p hp hav
    exact supportStableAt_actualBFS p lam a T U ha hT hTU hp hav k
  exact truncated_rank_weak_convergence
    (finitePathProbability M)
    (driftedProbability mu hmu.1 lam)
    actualBFSSupport lam a T U k
    (finitePathProbability_tendsto hExploration M lam mu hwindow hmu)
    (finitePathProbability_support M) hmatching

end

end Erdos745.WrapUp.Proofs.Internal.W15_CRITICAL_KeptWeak
