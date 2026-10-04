module

public import Erdos745.WrapUp.Proofs.Internal.Linked.W15_Base
public import Erdos745.WrapUp.Proofs.Internal.Linked.W15_Matching
public import Mathlib.MeasureTheory.Measure.Portmanteau
public import Erdos745.WrapUp.Contracts
public import Erdos745.WrapUp.Compat

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local simp] Pi.div_def Pi.mul_def Pi.add_def Pi.sub_def Pi.neg_def Pi.inv_def Function.comp_def Pi.pow_def Pi.smul_def Real.rpow_eq_pow

@[expose] public section


/-!
# Exact strict-window omission for completed finite exploration blocks

The tail deadline is strictly earlier than the code endpoint.  This slack
turns completion by the tail deadline into a strict end guard in the finite
code, including a block ending exactly at that deadline.
-/

namespace Erdos745.WrapUp.Proofs.Internal.W15_CRITICAL_Window

open Erdos745.WrapUp
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_Finite
open Erdos745.WrapUp.Proofs.Internal.W15_CRITICAL_Truncated
open Erdos745.WrapUp.Proofs.Internal.W15_CRITICAL_FiniteEnumeration
open Erdos745.WrapUp.Proofs.Internal.W15_CRITICAL_FiniteRank

noncomputable section
attribute [local instance] Classical.propDecidable

private theorem processed_step_subset {n : ℕ} (G : Graph n)
    {j : ℕ} (hj : j < n) : processed G j ⊆ processed G (j + 1) := by
  have hwell := explore_queueWellFormed G j
  have hcard := processed_card_of_le G j hj.le
  change stateProcessed (explore G j) ⊆
    stateProcessed (explore G (j + 1))
  rw [explore_succ]
  rcases hstate : explore G j with ⟨seen, queue, z⟩
  change (stateProcessed (explore G j)).card = j at hcard
  rw [hstate] at hwell hcard
  cases queue with
  | cons v rest =>
      have hstep := stateProcessed_active G seen v rest z hwell.1 hwell.2
      rw [hstep]
      exact Finset.subset_insert v _
  | nil =>
      have hseenlt : seen.card < n := by
        simp [stateProcessed] at hcard
        omega
      have hneutral :
          ((Finset.univ : Finset (Fin n)) \ seen).Nonempty := by
        apply Finset.sdiff_nonempty_of_card_lt_card
        simpa using! hseenlt
      rw [stateProcessed_root G seen z hneutral]
      exact Finset.subset_insert _ _

private theorem processed_mono_to_order {n : ℕ} (G : Graph n)
    {s t : ℕ} (hst : s ≤ t) (ht : t ≤ n) :
    processed G s ⊆ processed G t := by
  induction hst with
  | refl => exact Finset.Subset.rfl
  | @step t hst ih =>
      exact ih (Nat.le_of_lt ht) |>.trans
        (processed_step_subset G (Nat.lt_of_succ_le ht))

private theorem blockComponent_disjoint_start {n : ℕ} (G : Graph n)
    {z : ℕ × ℕ} (hz : QueueBlock G z) :
    Disjoint (blockComponent G z) (explore G z.1).seen := by
  rw [Finset.disjoint_left]
  intro v hv hvseen
  exact (Finset.mem_sdiff.mp hv).2
    (by simpa [processed, hz.2.1.2] using! hvseen)

private theorem block_end_le_of_processed {n : ℕ} (G : Graph n)
    {z : ℕ × ℕ} (hz : QueueBlock G z) (j : ℕ)
    (hsubset : blockComponent G z ⊆ processed G j) : z.2 ≤ j := by
  by_cases hjn : n ≤ j
  · exact le_trans hz.2.2.1.1 hjn
  have hj : j ≤ n := (Nat.lt_of_not_ge hjn).le
  have hnonempty : (blockComponent G z).Nonempty := by
    apply Finset.card_pos.mp
    rw [blockComponent_card G hz]
    have hst : z.1 < z.2 := hz.1
    omega
  by_cases hjs : j < z.1
  · have hjproc : processed G j ⊆ processed G z.1 :=
      processed_mono_to_order G hjs.le hz.2.1.1
    obtain ⟨v, hv⟩ := hnonempty
    exact False.elim ((Finset.mem_sdiff.mp hv).2 (hjproc (hsubset hv)))
  · have hsj : z.1 ≤ j := Nat.le_of_not_gt hjs
    have hsproc : processed G z.1 ⊆ processed G j :=
      processed_mono_to_order G hsj hj
    have hstproc : processed G z.1 ⊆ processed G z.2 :=
      processed_mono_to_order G hz.1.le hz.2.2.1.1
    have htproc : processed G z.2 ⊆ processed G j := by
      have hjoin : processed G z.1 ∪ blockComponent G z =
          processed G z.2 := by
        exact Finset.union_sdiff_of_subset hstproc
      rw [← hjoin]
      exact Finset.union_subset hsproc hsubset
    have hcardle := Finset.card_le_card htproc
    rw [processed_card_of_le G z.2 hz.2.2.1.1,
      processed_card_of_le G j hj] at hcardle
    exact hcardle

private theorem meshTime_eq_div {n j : ℕ} (hn : 0 < n) :
    (meshTime n j : ℝ) = (j : ℝ) / n23 n := by
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hscale : 0 < n23 n := Real.rpow_pos_of_pos hnreal _
  exact Real.coe_toNNReal _
    (div_nonneg (Nat.cast_nonneg _) hscale.le)

private theorem meshTime_lt_of_lt_floor {n s : ℕ} (hn : 0 < n)
    {T : ℝ} (hT : 0 ≤ T) (hs : s < ⌊T * n23 n⌋₊) :
    (meshTime n s : ℝ) < T := by
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hscale : 0 < n23 n := Real.rpow_pos_of_pos hnreal _
  rw [meshTime_eq_div hn]
  have hfloor : (⌊T * n23 n⌋₊ : ℝ) ≤ T * n23 n :=
    Nat.floor_le (mul_nonneg hT hscale.le)
  have hsreal : (s : ℝ) < T * n23 n := by
    exact (by exact_mod_cast hs : (s : ℝ) < (⌊T * n23 n⌋₊ : ℝ)).trans_le hfloor
  exact (div_lt_iff₀ hscale).2 (by nlinarith)

private theorem meshTime_le_of_le_floor {n t : ℕ} (hn : 0 < n)
    {U : ℝ} (hU : 0 ≤ U) (ht : t ≤ ⌊U * n23 n⌋₊) :
    (meshTime n t : ℝ) ≤ U := by
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hscale : 0 < n23 n := Real.rpow_pos_of_pos hnreal _
  rw [meshTime_eq_div hn]
  have hfloor : (⌊U * n23 n⌋₊ : ℝ) ≤ U * n23 n :=
    Nat.floor_le (mul_nonneg hU hscale.le)
  have htreal : (t : ℝ) ≤ U * n23 n :=
    (by exact_mod_cast ht : (t : ℝ) ≤ (⌊U * n23 n⌋₊ : ℝ)).trans hfloor
  exact (div_le_iff₀ hscale).2 (by nlinarith)

/-- A large component omitted from the literal strict finite code belongs to
one of the two public graph-tail events.  The event deadline is `Utail`, and
the code endpoint `U` is strictly later. -/
theorem large_block_omission_subset_tails {n : ℕ} (G : Graph n)
    (hn : 0 < n) (a T Utail U : ℝ)
    (hT : 0 < T) (hUtail : 0 ≤ Utail) (hslack : Utail < U)
    {z : ℕ × ℕ} (hz : z ∈ queueBlocks G)
    (hlarge : a < meshBlockLength n z.1 z.2)
    (homit : z ∉ keptBlocks G a T U) :
    lateLarge G T a ∨ unfinishedEarly G T Utail := by
  let S := blockComponent G z
  have hb : QueueBlock G z := (mem_queueBlocks G z).mp hz
  have hcomp : S ∈ components G := by
    rw [← component_blocks_bijection G]
    exact Finset.mem_image.mpr ⟨z, hz, rfl⟩
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hscale : 0 < n23 n := Real.rpow_pos_of_pos hnreal _
  have hsize : a * n23 n ≤ (S.card : ℝ) := by
    rw [meshBlockLength_eq_blockComponent_card G hb] at hlarge
    exact le_of_lt ((lt_div_iff₀ hscale).mp hlarge)
  let jT := ⌊T * n23 n⌋₊
  let jU := ⌊Utail * n23 n⌋₊
  by_cases hlate : Disjoint S (explore G jT).seen
  · exact Or.inl ⟨S, hcomp, hlate, hsize⟩
  · right
    refine ⟨S, hcomp, hlate, ?_⟩
    intro hdone
    have hstartdis := blockComponent_disjoint_start G hb
    have hstart : z.1 < jT := by
      by_contra h
      have hjle : jT ≤ z.1 := Nat.le_of_not_gt h
      have hseen := seen_monotone G hjle
      apply hlate
      exact Finset.disjoint_left.mpr (by
        intro v hv hvseen
        exact Finset.disjoint_left.mp hstartdis hv (hseen hvseen))
    have hTguard : (meshTime n z.1 : ℝ) < T :=
      meshTime_lt_of_lt_floor hn hT.le hstart
    have hend : z.2 ≤ jU := block_end_le_of_processed G hb jU hdone
    have hUguard : (meshTime n z.2 : ℝ) < U :=
      (meshTime_le_of_le_floor hn hUtail hend).trans_lt hslack
    have hfloorU : z.2 ≤ ⌊U * n23 n⌋₊ + 1 := by
      have hreal : (z.2 : ℝ) ≤ U * n23 n := by
        rw [meshTime_eq_div hn] at hUguard
        exact le_of_lt ((div_lt_iff₀ hscale).mp hUguard)
      exact le_trans (Nat.le_floor hreal) (Nat.le_succ _)
    apply homit
    exact Finset.mem_filter.mpr
      ⟨hz, hfloorU, hTguard, hUguard, hlarge⟩

/-- Outside the two public graph-tail events, every completed block whose
exact scaled component length exceeds the cutoff passes the strict code. -/
theorem large_blocks_kept_of_no_tails {n : ℕ} (G : Graph n)
    (hn : 0 < n) (a T Utail U : ℝ)
    (hT : 0 < T) (hUtail : 0 ≤ Utail) (hslack : Utail < U)
    (hlate : ¬ lateLarge G T a)
    (hunfinished : ¬ unfinishedEarly G T Utail) :
    ∀ z ∈ queueBlocks G,
      a < meshBlockLength n z.1 z.2 → z ∈ keptBlocks G a T U := by
  intro z hz hlarge
  by_contra homit
  rcases large_block_omission_subset_tails G hn a T Utail U
      hT hUtail hslack hz hlarge homit with h | h
  · exact hlate h
  · exact hunfinished h

end

end Erdos745.WrapUp.Proofs.Internal.W15_CRITICAL_Window


/-!
# Removal of the strict excursion window

The cutoffs are chosen in the order length, start, graph completion deadline,
and code end.  The code end is strictly later than the completion deadline.
All finite laws, including their exceptional initial indices, remain the
actual BFS path laws from `KeptWeak`.
-/

namespace Erdos745.WrapUp.Proofs.Internal.W15_CRITICAL_RankLimit

open Erdos745.WrapUp
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_FiniteLaw
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_Interpolation
open Erdos745.WrapUp.Proofs.Internal.W15_CRITICAL_Truncated
open Erdos745.WrapUp.Proofs.Internal.W15_CRITICAL_Code
open Erdos745.WrapUp.Proofs.Internal.W15_CRITICAL_CodeComplete
open Erdos745.WrapUp.Proofs.Internal.W15_CRITICAL_KeptWeak
open Erdos745.WrapUp.Proofs.Internal.W15_CRITICAL_ScaledRanks
open Erdos745.WrapUp.Proofs.Internal.W15_CRITICAL_FiniteEnumeration
open Erdos745.WrapUp.Proofs.Internal.W15_CRITICAL_Window
open Filter MeasureTheory Set
open scoped Topology ENNReal

noncomputable section
attribute [local instance] Classical.propDecidable
local instance : MeasurableSpace BrownianPath := borel BrownianPath
local instance : BorelSpace BrownianPath := ⟨rfl⟩
local instance graphMeasurableSpace (n : ℕ) : MeasurableSpace (Graph n) := ⊤

/-! ## Candidate ranks above a positive cutoff -/

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

/-- Values below the cutoff cannot affect a rank strictly above it. -/
private theorem rankFromCandidates_eq_above
    (v w : ℕ → BrownianPath → ENNReal) (p : BrownianPath)
    (c : ENNReal) (hvw : ∀ m, v m p ≤ w m p)
    (hhigh : ∀ m, c < w m p → v m p = w m p)
    (i : ℕ) (hrank : c < rankFromCandidates w i p) :
    rankFromCandidates v i p = rankFromCandidates w i p := by
  have hle := rankFromCandidates_mono v w p hvw i
  have hmax : rankFromCandidates w i p ≤
      max c (rankFromCandidates v i p) := by
    unfold rankFromCandidates
    by_cases hi : i = 0
    · simp [hi]
    · simp only [hi, if_false]
      apply iSup_le
      intro f
      by_cases hf : Function.Injective f
      · rw [if_pos hf]
        by_cases hsmall : (⨅ j : Fin i, w (f j) p) ≤ c
        · exact hsmall.trans (le_max_left _ _)
        · have heq (j : Fin i) : w (f j) p = v (f j) p := by
            exact (hhigh (f j) ((lt_of_not_ge hsmall).trans_le
              (iInf_le (fun j : Fin i => w (f j) p) j))).symm
          simp_rw [heq]
          have hle :
              (if Function.Injective f then ⨅ j : Fin i, v (f j) p else 0) ≤
                max c (⨆ g : Fin i → ℕ,
                  if Function.Injective g then ⨅ j : Fin i, v (g j) p else 0) :=
            (le_iSup (fun g : Fin i → ℕ =>
              if Function.Injective g then ⨅ j : Fin i, v (g j) p else 0) f).trans
              (le_max_right _ _)
          simpa only [hf, if_true] using! hle
      · rw [if_neg hf]
        exact bot_le
  apply le_antisymm hle
  by_cases hc : c ≤ rankFromCandidates v i p
  · calc
      rankFromCandidates w i p ≤ max c (rankFromCandidates v i p) := hmax
      _ = rankFromCandidates v i p := max_eq_right hc
  · have hcontra : rankFromCandidates w i p ≤ c := by
      calc
        rankFromCandidates w i p ≤ max c (rankFromCandidates v i p) := hmax
        _ = c := max_eq_left (le_of_not_ge hc)
    exact False.elim ((not_le_of_gt hrank) hcontra)

private theorem codedLength_ne_top_of_good (p : BrownianPath) (lam : ℝ)
    (hgood : GoodExcursionPath (centerPath p lam) lam) (m : ℕ) :
    codedLength lam m p ≠ ⊤ := by
  by_cases hm : retainedCode lam m p
  · obtain ⟨_, _, hlen⟩ := retainedCode_excursion_of_escape p lam hgood.1 hm
    rw [hlen]
    exact ENNReal.ofReal_ne_top
  · simp [codedLength, hm]

/-- All coded excursions exceeding `a` pass the two strict endpoint guards. -/
def NoLongCodeOmission (p : BrownianPath) (lam a T U : ℝ) : Prop :=
  ∀ m, a < lengthValue lam m p →
    startValue lam m p < T ∧ endValue lam m p < U

private theorem limitKeptLength_le_codedLength (lam a T U : ℝ)
    (m : ℕ) (p : BrownianPath) :
    limitKeptLength lam a T U m p ≤ codedLength lam m p := by
  unfold limitKeptLength
  split_ifs
  · exact le_rfl
  · exact bot_le

private theorem limitKeptLength_eq_codedLength_of_long
    (p : BrownianPath) (lam a T U : ℝ) (ha : 0 ≤ a)
    (hgood : GoodExcursionPath (centerPath p lam) lam)
    (hnomit : NoLongCodeOmission p lam a T U) (m : ℕ)
    (hm : ENNReal.ofReal a < codedLength lam m p) :
    limitKeptLength lam a T U m p = codedLength lam m p := by
  have hlen : a < lengthValue lam m p :=
    (ENNReal.ofReal_lt_iff_lt_toReal ha
      (codedLength_ne_top_of_good p lam hgood m)).mp hm
  obtain ⟨hs, he⟩ := hnomit m hlen
  change (if a < lengthValue lam m p ∧ startValue lam m p < T ∧
    endValue lam m p < U then codedLength lam m p else 0) = codedLength lam m p
  rw [if_pos ⟨hlen, hs, he⟩]

private theorem excursionRankExtended_antitone
    (w : BrownianPath) (lam : ℝ) {i j : ℕ}
    (hi : 0 < i) (hij : i ≤ j) :
    excursionRankExtended w lam j ≤ excursionRankExtended w lam i := by
  have hj : 0 < j := hi.trans_le hij
  rw [excursionRankExtended, if_neg (Nat.ne_of_gt hj),
    excursionRankExtended, if_neg (Nat.ne_of_gt hi)]
  apply sSup_le
  intro x hx
  obtain ⟨e, heinj, he⟩ := hx
  apply le_sSup
  refine ⟨fun r : Fin i => e (Fin.castLE hij r),
    heinj.comp (Fin.castLE_injective hij), ?_⟩
  intro r
  exact he (Fin.castLE hij r)

/-- On a good path, a window retaining every code longer than `a` has every
full rank above `a` exactly, including ties and zero padding. -/
theorem limitTruncatedRank_eq_full_above
    (p : BrownianPath) (lam a T U : ℝ) (ha : 0 < a)
    (hgood : GoodExcursionPath (centerPath p lam) lam)
    (hnomit : NoLongCodeOmission p lam a T U)
    (k : ℕ) (r : Fin k)
    (hfinite : excursionRankExtended (centerPath p lam) lam (r.val + 1) ≠ ⊤)
    (hrank : a < excursionRank (centerPath p lam) lam (r.val + 1)) :
    limitTruncatedRank lam a T U k p r =
      excursionRank (centerPath p lam) lam (r.val + 1) := by
  let i := r.val + 1
  have hfull := rankFromCodedLength_eq_excursionRankExtended p lam hgood.1 i
  have hcut : ENNReal.ofReal a < rankFromCandidates (codedLength lam) i p := by
    rw [hfull]
    exact (ENNReal.ofReal_lt_iff_lt_toReal ha.le hfinite).mpr hrank
  have heq := rankFromCandidates_eq_above
    (limitKeptLength lam a T U) (codedLength lam) p (ENNReal.ofReal a)
    (fun m => limitKeptLength_le_codedLength lam a T U m p)
    (fun m hm => limitKeptLength_eq_codedLength_of_long p lam a T U
      ha.le hgood hnomit m hm) i hcut
  change (rankFromCandidates (limitKeptLength lam a T U) i p).toReal = _
  rw [heq]
  exact rankFromCodedLength_toReal_eq_excursionRank p lam hgood.1 i

/-! ## Measurable long-code tails -/

def lateCode (lam a T : ℝ) : Set BrownianPath :=
  {p | ∃ m : ℕ, a < lengthValue lam m p ∧ T ≤ startValue lam m p}

def longCode (lam a U : ℝ) : Set BrownianPath :=
  {p | ∃ m : ℕ, a < lengthValue lam m p ∧ U ≤ endValue lam m p}

private theorem measurable_lengthValue (lam : ℝ) (m : ℕ) :
    Measurable (lengthValue lam m) :=
  (measurable_codedLength lam m).ennreal_toReal

private theorem measurable_startValue (lam : ℝ) (m : ℕ) :
    Measurable (startValue lam m) :=
  (measurable_codedLeft lam (codeTime m)).ennreal_toReal

private theorem measurable_endValue (lam : ℝ) (m : ℕ) :
    Measurable (endValue lam m) :=
  (measurable_codedRight lam (codeTime m)).ennreal_toReal

theorem measurableSet_lateCode (lam a T : ℝ) :
    MeasurableSet (lateCode lam a T) := by
  rw [show lateCode lam a T = ⋃ m : ℕ,
    {p : BrownianPath | a < lengthValue lam m p ∧
      T ≤ startValue lam m p} by ext p; simp [lateCode]]
  apply MeasurableSet.iUnion
  intro m
  exact (measurableSet_lt measurable_const
    (measurable_lengthValue lam m)).inter
    (measurableSet_le measurable_const (measurable_startValue lam m))

theorem measurableSet_longCode (lam a U : ℝ) :
    MeasurableSet (longCode lam a U) := by
  rw [show longCode lam a U = ⋃ m : ℕ,
    {p : BrownianPath | a < lengthValue lam m p ∧
      U ≤ endValue lam m p} by ext p; simp [longCode]]
  apply MeasurableSet.iUnion
  intro m
  exact (measurableSet_lt measurable_const
    (measurable_lengthValue lam m)).inter
    (measurableSet_le measurable_const (measurable_endValue lam m))

private theorem longCodes_finite (p : BrownianPath) (lam a : ℝ)
    (ha : 0 < a) (hgood : GoodExcursionPath (centerPath p lam) lam) :
    {m : ℕ | a < lengthValue lam m p}.Finite := by
  let S : Set ℕ := {m | a < lengthValue lam m p}
  let E : Set (NNReal × NNReal) :=
    {e | excursion (centerPath p lam) lam e.1 e.2 ∧
      a ≤ (e.2 : ℝ) - (e.1 : ℝ)}
  have hE : E.Finite := hgood.2.2.2.2.1 a ha
  have hmap : (fun m => codedExcursionPair lam m p) '' S ⊆ E := by
    rintro e ⟨m, hm, rfl⟩
    have hret : retainedCode lam m p := by
      by_contra hnot
      have hzero := codedLength_eq_zero_of_not_retained p lam hnot
      have : lengthValue lam m p = 0 := by simp [lengthValue, hzero]
      exact (not_lt_of_ge ha.le) (this ▸ hm)
    obtain ⟨hexc, _, hlen⟩ :=
      retainedCode_excursion_of_escape p lam hgood.1 hret
    refine ⟨hexc, ?_⟩
    have hnonneg : 0 ≤ ((codedExcursionPair lam m p).2 : ℝ) -
      ((codedExcursionPair lam m p).1 : ℝ) :=
      sub_nonneg.mpr (mod_cast hexc.1.le)
    have hv : lengthValue lam m p =
        ((codedExcursionPair lam m p).2 : ℝ) -
          ((codedExcursionPair lam m p).1 : ℝ) := by
      simp [lengthValue, hlen, ENNReal.toReal_ofReal hnonneg]
    change a < lengthValue lam m p at hm
    rw [hv] at hm
    exact hm.le
  have hinj : InjOn (fun m => codedExcursionPair lam m p) S := by
    intro j hj m hm hpair
    have hret (q : ℕ) (hq : q ∈ S) : retainedCode lam q p := by
      by_contra hnot
      have hzero := codedLength_eq_zero_of_not_retained p lam hnot
      have : lengthValue lam q p = 0 := by simp [lengthValue, hzero]
      exact (not_lt_of_ge ha.le) (this ▸ hq)
    exact retainedCode_pair_injective p lam hgood.1
      (hret j hj) (hret m hm) hpair
  exact (hE.subset hmap).of_finite_image hinj

private theorem eventually_no_lateCode (p : BrownianPath) (lam a : ℝ)
    (ha : 0 < a) (hgood : GoodExcursionPath (centerPath p lam) lam) :
    ∀ᶠ N : ℕ in atTop, p ∉ lateCode lam a N := by
  let S : Set ℕ := {m | a < lengthValue lam m p}
  have hS : S.Finite := longCodes_finite p lam a ha hgood
  obtain ⟨B, hB⟩ := (hS.image (fun m => startValue lam m p)).bddAbove
  obtain ⟨N, hN⟩ := exists_nat_gt B
  filter_upwards [eventually_ge_atTop N] with q hq
  rintro ⟨m, hm, hlate⟩
  have hb : startValue lam m p ≤ B := hB ⟨m, hm, rfl⟩
  have hNq : (N : ℝ) ≤ q := by exact_mod_cast hq
  linarith

private theorem eventually_no_longCode (p : BrownianPath) (lam a : ℝ)
    (ha : 0 < a) (hgood : GoodExcursionPath (centerPath p lam) lam) :
    ∀ᶠ N : ℕ in atTop, p ∉ longCode lam a N := by
  let S : Set ℕ := {m | a < lengthValue lam m p}
  have hS : S.Finite := longCodes_finite p lam a ha hgood
  obtain ⟨B, hB⟩ := (hS.image (fun m => endValue lam m p)).bddAbove
  obtain ⟨N, hN⟩ := exists_nat_gt B
  filter_upwards [eventually_ge_atTop N] with q hq
  rintro ⟨m, hm, hlate⟩
  have hb : endValue lam m p ≤ B := hB ⟨m, hm, rfl⟩
  have hNq : (N : ℝ) ≤ q := by exact_mod_cast hq
  linarith

private theorem noLongCodeOmission_of_no_tails (p : BrownianPath)
    (lam a T U : ℝ) (hT : p ∉ lateCode lam a T)
    (hU : p ∉ longCode lam a U) :
    NoLongCodeOmission p lam a T U := by
  intro m hm
  exact ⟨lt_of_not_ge (fun h => hT ⟨m, hm, h⟩),
    lt_of_not_ge (fun h => hU ⟨m, hm, h⟩)⟩

private theorem measure_lateCode_tendsto_zero (nu : PathLaw)
    [IsProbabilityMeasure nu] (lam a : ℝ) (ha : 0 < a)
    (hgood : ∀ᵐ p ∂nu, GoodExcursionPath (centerPath p lam) lam) :
    Tendsto (fun N : ℕ => nu (lateCode lam a N)) atTop (𝓝 0) := by
  let E : ℕ → Set BrownianPath := fun N => lateCode lam a N
  have hE : Antitone E := by
    intro n m hnm p hp
    obtain ⟨j, hj, hlate⟩ := hp
    exact ⟨j, hj, le_trans (by exact_mod_cast hnm) hlate⟩
  have hnull : nu (⋂ N, E N) = 0 := by
    apply (measure_eq_zero_iff_ae_notMem).mpr
    filter_upwards [hgood] with p hp hmem
    obtain ⟨N, hN⟩ := (eventually_no_lateCode p lam a ha hp).exists
    exact hN (Set.mem_iInter.mp hmem N)
  have ht := tendsto_measure_iInter_atTop
    (μ := nu) (s := E)
    (fun N => (measurableSet_lateCode lam a N).nullMeasurableSet)
    hE ⟨0, measure_ne_top _ _⟩
  simpa only [Function.comp_def, hnull] using! ht

private theorem measure_longCode_tendsto_zero (nu : PathLaw)
    [IsProbabilityMeasure nu] (lam a : ℝ) (ha : 0 < a)
    (hgood : ∀ᵐ p ∂nu, GoodExcursionPath (centerPath p lam) lam) :
    Tendsto (fun N : ℕ => nu (longCode lam a N)) atTop (𝓝 0) := by
  let E : ℕ → Set BrownianPath := fun N => longCode lam a N
  have hE : Antitone E := by
    intro n m hnm p hp
    obtain ⟨j, hj, hlate⟩ := hp
    exact ⟨j, hj, le_trans (by exact_mod_cast hnm) hlate⟩
  have hnull : nu (⋂ N, E N) = 0 := by
    apply (measure_eq_zero_iff_ae_notMem).mpr
    filter_upwards [hgood] with p hp hmem
    obtain ⟨N, hN⟩ := (eventually_no_longCode p lam a ha hp).exists
    exact hN (Set.mem_iInter.mp hmem N)
  have ht := tendsto_measure_iInter_atTop
    (μ := nu) (s := E)
    (fun N => (measurableSet_longCode lam a N).nullMeasurableSet)
    hE ⟨0, measure_ne_top _ _⟩
  simpa only [Function.comp_def, hnull] using! ht

/-! ## The full finite and limiting vector maps -/

def fullDiscreteLength (n m : ℕ) (p : BrownianPath) : ENNReal :=
  if successiveMeshRecords n (pairCode m).1 (pairCode m).2 p then
    ENNReal.ofReal (meshBlockLength n (pairCode m).1 (pairCode m).2)
  else 0

theorem measurable_fullDiscreteLength (n m : ℕ) :
    Measurable (fullDiscreteLength n m) := by
  unfold fullDiscreteLength
  exact Measurable.ite
    (measurableSet_successiveMeshRecords n (pairCode m).1 (pairCode m).2)
    measurable_const measurable_const

def fullDiscreteRank (n k : ℕ) (p : BrownianPath) : Fin k → ℝ :=
  fun r => (rankFromCandidates (fullDiscreteLength n) (r.val + 1) p).toReal

theorem measurable_fullDiscreteRank (n k : ℕ) :
    Measurable (fullDiscreteRank n k) := by
  apply measurable_pi_lambda
  intro r
  exact (measurable_rankFromCandidates (fullDiscreteLength n)
    (measurable_fullDiscreteLength n) (r.val + 1)).ennreal_toReal

def fullLimitRank (lam : ℝ) (k : ℕ) (p : BrownianPath) : Fin k → ℝ :=
  fun r => excursionRank (centerPath p lam) lam (r.val + 1)

theorem measurable_fullLimitRank (hBrownian : BrownianFoundationStatement)
    (mu : PathLaw) (hmu : BrownianLaw mu) (lam : ℝ) (k : ℕ) :
    Measurable (fullLimitRank lam k) := by
  apply measurable_pi_lambda
  intro r
  exact (((hBrownian.2 mu hmu lam).2 (r.val + 1)
    (Nat.zero_lt_succ _)).1.comp (measurable_centerPath lam)).ennreal_toReal

private theorem rankFromCandidates_congr_at
    (v w : ℕ → BrownianPath → ENNReal) (p : BrownianPath)
    (h : ∀ m, v m p = w m p) (i : ℕ) :
    rankFromCandidates v i p = rankFromCandidates w i p := by
  unfold rankFromCandidates
  by_cases hi : i = 0
  · simp [hi]
  · simp only [hi, if_false]
    apply iSup_congr
    intro f
    by_cases hf : Function.Injective f
    · simp only [hf, if_true]
      apply iInf_congr
      intro j
      exact h (f j)
    · simp [hf]

theorem fullDiscreteRank_on_BFS {n : ℕ} (G : Graph n) (hn : 0 < n)
    (k : ℕ) (r : Fin k) :
    fullDiscreteRank n k (continuousRawExploration G) r =
      (rankSize G (r.val + 1) : ℝ) / n23 n := by
  have hcode (m : ℕ) :
      fullDiscreteLength n m (continuousRawExploration G) =
        untruncatedCodeLength G m :=
    (untruncatedCodeLength_eq_records G hn m).symm
  have hrank : rankFromCandidates (fullDiscreteLength n) (r.val + 1)
      (continuousRawExploration G) = untruncatedCodeRank G (r.val + 1) := by
    unfold untruncatedCodeRank
    exact rankFromCandidates_congr_at _ _ _ hcode _
  change (rankFromCandidates (fullDiscreteLength n) (r.val + 1)
    (continuousRawExploration G)).toReal = _
  rw [hrank]
  exact untruncatedCodeRank_toReal_eq_rankSize_div G hn _

private theorem keptLength_le_fullLength (n : ℕ) (a T U : ℝ)
    (m : ℕ) (p : BrownianPath) :
    discreteKeptLength n a T U (pairCode m) p ≤
      fullDiscreteLength n m p := by
  unfold discreteKeptLength fullDiscreteLength
  split_ifs with hkeep hfull
  · exact le_rfl
  · exact False.elim (hfull hkeep.1)
  · exact bot_le
  · exact bot_le

private theorem keptRank_le_fullRank (n : ℕ) (a T U : ℝ)
    (i : ℕ) (p : BrownianPath) :
    rankFromCandidates
      (fun m => discreteKeptLength n a T U (pairCode m)) i p ≤
      rankFromCandidates (fullDiscreteLength n) i p :=
  rankFromCandidates_mono _ _ p
    (fun m => keptLength_le_fullLength n a T U m p) i

private theorem rankSize_antitone {n : ℕ} (G : Graph n)
    {i j : ℕ} (hi : 0 < i) (hij : i ≤ j) :
    rankSize G j ≤ rankSize G i := by
  have hj : 0 < j := hi.trans_le hij
  simp only [rankSize, if_neg (Nat.ne_of_gt hi),
    if_neg (Nat.ne_of_gt hj)]
  apply Finset.sup_le
  intro h hh
  by_cases hcount : j ≤ countGE G h
  · have hicount : i ≤ countGE G h := hij.trans hcount
    simpa only [hcount, hicount, if_true] using!
      (Finset.le_sup (f := fun q => if i ≤ countGE G q then q else 0) hh)
  · simp [hcount]

/-- The kth kept coordinate is a lower bound for the kth exact component
rank on an actual positive-size BFS path. -/
private theorem kept_kth_le_full {n : ℕ} (G : Graph n) (hn : 0 < n)
    (a T U : ℝ) (k : ℕ) (hk : 0 < k) :
    discreteTruncatedRank n a T U k (continuousRawExploration G)
        ⟨k - 1, by omega⟩ ≤
      (rankSize G k : ℝ) / n23 n := by
  let r : Fin k := ⟨k - 1, by omega⟩
  have hr : r.val + 1 = k := by simp [r]; omega
  have hbound := keptRank_le_fullRank n a T U k
    (continuousRawExploration G)
  have htop : rankFromCandidates (fullDiscreteLength n) k
      (continuousRawExploration G) ≠ ⊤ := by
    have heq : rankFromCandidates (fullDiscreteLength n) k
        (continuousRawExploration G) = untruncatedCodeRank G k := by
      unfold untruncatedCodeRank
      exact rankFromCandidates_congr_at _ _ _
        (fun m => (untruncatedCodeLength_eq_records G hn m).symm) _
    rw [heq]
    exact untruncatedCodeRank_ne_top G hn k
  have hreal := ENNReal.toReal_mono htop hbound
  have hfull := fullDiscreteRank_on_BFS G hn k r
  change (rankFromCandidates
      (fun m => discreteKeptLength n a T U (pairCode m)) k
        (continuousRawExploration G)).toReal ≤
    (rankFromCandidates (fullDiscreteLength n) k
      (continuousRawExploration G)).toReal at hreal
  have hfullk : (rankFromCandidates (fullDiscreteLength n) k
      (continuousRawExploration G)).toReal = (rankSize G k : ℝ) / n23 n := by
    simpa only [fullDiscreteRank, hr] using! hfull
  have hlast : k - 1 + 1 = k := by omega
  simpa only [discreteTruncatedRank, hlast] using! hreal.trans_eq hfullk

/-- A sufficiently high kept kth coordinate, together with the two absent
graph-tail events, identifies all first `k` exact ranks. -/
theorem fullDiscreteRank_eq_kept_of_no_tails {n : ℕ}
    (G : Graph n) (hn : 0 < n) (_lam a T Utail U : ℝ)
    (ha : 0 < a) (hT : 0 < T) (hUtail : 0 ≤ Utail)
    (hslack : Utail < U) (k : ℕ) (hk : 0 < k)
    (hlate : ¬ lateLarge G T a)
    (hearly : ¬ unfinishedEarly G T Utail)
    (hkth : 3 * a < discreteTruncatedRank n a T U k
      (continuousRawExploration G) ⟨k - 1, by omega⟩) :
    fullDiscreteRank n k (continuousRawExploration G) =
      discreteTruncatedRank n a T U k (continuousRawExploration G) := by
  funext r
  have hretain := large_blocks_kept_of_no_tails G hn a T Utail U
    hT hUtail hslack hlate hearly
  have hK : a < (rankSize G k : ℝ) / n23 n := by
    have hle := kept_kth_le_full G hn a T U k hk
    linarith
  have hri : (rankSize G k : ℝ) / n23 n ≤
      (rankSize G (r.val + 1) : ℝ) / n23 n := by
    have hr : r.val + 1 ≤ k := r.isLt
    have hmono := rankSize_antitone G (Nat.zero_lt_succ r.val) hr
    have hscale : 0 ≤ n23 n :=
      (Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn) _).le
    exact div_le_div_of_nonneg_right (by exact_mod_cast hmono) hscale
  have heq := discreteTruncatedRank_eq_rankSize_div G hn a T U ha.le
    hretain k r (lt_of_lt_of_le hK hri)
  exact (fullDiscreteRank_on_BFS G hn k r).trans heq.symm

/-! ## A common cutoff witness and the public graph tails -/

private theorem small_rank_measure_tendsto_zero
    (nu : PathLaw) [IsProbabilityMeasure nu]
    (R : BrownianPath → ℝ) (hR : Measurable R)
    (hpos : ∀ᵐ p ∂nu, 0 < R p) :
    Tendsto (fun N : ℕ => nu {p | R p ≤ 1 / ((N : ℝ) + 1)})
      atTop (𝓝 0) := by
  let E : ℕ → Set BrownianPath :=
    fun N => {p | R p ≤ 1 / ((N : ℝ) + 1)}
  have hE : Antitone E := by
    intro n m hnm p hp
    have hcast : (n : ℝ) ≤ m := by exact_mod_cast hnm
    change R p ≤ 1 / ((m : ℝ) + 1) at hp
    change R p ≤ 1 / ((n : ℝ) + 1)
    exact hp.trans (by gcongr)
  have hnull : nu (⋂ N, E N) = 0 := by
    apply (measure_eq_zero_iff_ae_notMem).mpr
    filter_upwards [hpos] with p hp hmem
    have ht : Tendsto (fun N : ℕ => (1 : ℝ) / ((N : ℝ) + 1))
        atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    obtain ⟨N, hN⟩ := (ht.eventually_lt_const hp).exists
    exact (not_le_of_gt hN) (Set.mem_iInter.mp hmem N)
  have ht := tendsto_measure_iInter_atTop
    (μ := nu) (s := E)
    (fun N => (measurableSet_le hR measurable_const).nullMeasurableSet)
    hE ⟨0, measure_ne_top _ _⟩
  simpa only [Function.comp_def, hnull] using! ht

private theorem probM_mono {n M : ℕ} (A B : Graph n → Prop)
    (hAB : ∀ G, A G → B G) : probM n M A ≤ probM n M B := by
  unfold probM
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast Finset.card_le_card (show
    (fixedGraphs n M).filter A ⊆ (fixedGraphs n M).filter B by
      intro G hG
      exact Finset.mem_filter.mpr
        ⟨(Finset.mem_filter.mp hG).1, hAB G (Finset.mem_filter.mp hG).2⟩)

private theorem probM_or_le {n M : ℕ} (hM : M ≤ capacity n)
    (A B : Graph n → Prop) :
    probM n M (fun G => A G ∨ B G) ≤ probM n M A + probM n M B := by
  letI : IsProbabilityMeasure (fixedMeasure n M hM) :=
    fixedMeasure_probability n M hM
  rw [← fixedMeasure_apply_toReal n M hM (fun G => A G ∨ B G),
    ← fixedMeasure_apply_toReal n M hM A,
    ← fixedMeasure_apply_toReal n M hM B]
  have hset : {G : Graph n | A G ∨ B G} =
      {G : Graph n | A G} ∪ {G : Graph n | B G} := by
    ext G
    simp
  rw [hset]
  have hA : fixedMeasure n M hM {G | A G} ≠ ⊤ := measure_ne_top _ _
  have hB : fixedMeasure n M hM {G | B G} ≠ ⊤ := measure_ne_top _ _
  have h := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hA, hB⟩)
    (measure_union_le {G : Graph n | A G} {G : Graph n | B G})
  simpa only [ENNReal.toReal_add hA hB] using! h

private theorem finitePathProbability_event (M : NatSeq) (n : ℕ)
    (hn : M n ≤ capacity n) (A : Set BrownianPath)
    (hA : MeasurableSet A) :
    ((finitePathProbability M n : Measure BrownianPath) A).toReal =
      probM n (M n) (fun G => continuousRawExploration G ∈ A) := by
  simp only [finitePathProbability, dif_pos hn]
  change (explorationPathMeasure n (M n) hn A).toReal = _
  rw [explorationPathMeasure, Measure.map_apply
    (measurable_explorationInterpolation n) hA]
  exact fixedMeasure_apply_toReal n (M n) hn _

private theorem measure_union_toReal_le (nu : PathLaw)
    [IsProbabilityMeasure nu] (A B : Set BrownianPath) :
    (nu (A ∪ B)).toReal ≤ (nu A).toReal + (nu B).toReal := by
  have hA : nu A ≠ ⊤ := measure_ne_top _ _
  have hB : nu B ≠ ⊤ := measure_ne_top _ _
  have h := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hA, hB⟩)
    (measure_union_le A B)
  simpa only [ENNReal.toReal_add hA hB] using! h

structure CutoffWitness (M : NatSeq) (lam : ℝ) (mu : PathLaw)
    (k : ℕ) (δ : ℝ) where
  a : ℝ
  T : ℝ
  Utail : ℝ
  U : ℝ
  ha : 0 < a
  hT : 0 < T
  hTlam : lam + 1 < T
  hTUtail : T < Utail
  htailU : Utail < U
  hnull : CodedBoundaryNull mu lam a T U
  hnullHalf : CodedBoundaryNull mu lam (a / 2) T U
  hrank : ((driftedPathLaw mu lam)
    {p | excursionRank (centerPath p lam) lam k ≤ 4 * a}).toReal < δ
  hstart : ((driftedPathLaw mu lam) (lateCode lam a T)).toReal < δ
  hend : ((driftedPathLaw mu lam) (longCode lam a U)).toReal < δ
  hlateGraph : ∀ᶠ n : ℕ in atTop,
    probM n (M n) (fun G => lateLarge G T a) < 2 * δ
  hearlyGraph : ∀ᶠ n : ℕ in atTop,
    probM n (M n) (fun G => unfinishedEarly G T Utail) ≤ δ

/-- The corrected C5 witness order.  The graph completion deadline is fixed
before choosing the strict code endpoint. -/
theorem exists_cutoffWitness
    (hBrownian : BrownianFoundationStatement)
    (hExploration : ExplorationStatement)
    (M : NatSeq) (lam : ℝ) (mu : PathLaw)
    (hwindow : criticalWindow M lam) (hmu : BrownianLaw mu)
    (k : ℕ) (hk : 0 < k) (δ : ℝ) (hδ : 0 < δ) :
    Nonempty (CutoffWitness M lam mu k δ) := by
  letI : IsProbabilityMeasure mu := hmu.1
  let nu := driftedPathLaw mu lam
  haveI : IsProbabilityMeasure nu := driftedPathLaw_probability mu lam
  have hgood : ∀ᵐ p ∂nu, GoodExcursionPath (centerPath p lam) lam :=
    ae_good_centered_drift hBrownian mu hmu lam
  let R : BrownianPath → ℝ :=
    fun p => excursionRank (centerPath p lam) lam k
  have hRmeas : Measurable R :=
    (((hBrownian.2 mu hmu lam).2 k hk).1.comp
      (measurable_centerPath lam)).ennreal_toReal
  have hrankμ := ((hBrownian.2 mu hmu lam).2 k hk).2
  have hrankν : ∀ᵐ p ∂nu,
      0 < excursionRankExtended (centerPath p lam) lam k ∧
        excursionRankExtended (centerPath p lam) lam k < ⊤ := by
    have hmap : ∀ᵐ w ∂Measure.map
        (fun p : BrownianPath => centerPath p lam) nu,
        0 < excursionRankExtended w lam k ∧
          excursionRankExtended w lam k < ⊤ := by
      rw [show Measure.map (fun p : BrownianPath => centerPath p lam) nu = mu
        from centerPath_map_driftedPathLaw mu lam]
      exact hrankμ
    exact ae_of_ae_map (measurable_centerPath lam).aemeasurable hmap
  have hRpos : ∀ᵐ p ∂nu, 0 < R p := by
    filter_upwards [hrankν] with p hp
    exact ENNReal.toReal_pos (ne_of_gt hp.1) hp.2.ne
  have hsmall := small_rank_measure_tendsto_zero nu R hRmeas hRpos
  obtain ⟨Nrank, hNrank⟩ :=
    (hsmall.eventually (eventually_lt_nhds
      (ENNReal.ofReal_pos.mpr hδ))).exists
  have hupper : 0 < 1 / (4 * ((Nrank : ℝ) + 1)) := by positivity
  have hbad : (lengthAtoms nu lam ∪
      (fun x : ℝ => 2 * x) '' lengthAtoms nu lam).Countable :=
    (countable_lengthAtoms nu lam).union
      ((countable_lengthAtoms nu lam).image _)
  obtain ⟨a, haI, hanot⟩ := (hbad.dense_compl ℝ).inter_open_nonempty
    (Ioo 0 (1 / (4 * ((Nrank : ℝ) + 1))))
    isOpen_Ioo (nonempty_Ioo.mpr hupper)
  have ha : 0 < a := haI.1
  have hrankSmall : (nu {p | R p ≤ 4 * a}).toReal < δ := by
    have hsub : {p | R p ≤ 4 * a} ⊆
        {p | R p ≤ 1 / ((Nrank : ℝ) + 1)} := by
      intro p hp
      have hh : 4 * a < 1 / ((Nrank : ℝ) + 1) := by
        have hN : 0 < (Nrank : ℝ) + 1 := by positivity
        have := haI.2
        field_simp at this ⊢
        nlinarith
      exact hp.trans hh.le
    have hNreal :
        (nu {p | R p ≤ 1 / ((Nrank : ℝ) + 1)}).toReal < δ := by
      have := (ENNReal.toReal_lt_toReal (measure_ne_top _ _)
        ENNReal.ofReal_ne_top).mpr hNrank
      simpa [ENNReal.toReal_ofReal hδ.le] using! this
    exact (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub)).trans_lt
      hNreal
  have hstartT := measure_lateCode_tendsto_zero nu lam a ha hgood
  obtain ⟨Nstart, hNstart⟩ :=
    (hstartT.eventually (eventually_lt_nhds
      (ENNReal.ofReal_pos.mpr hδ))).exists
  let L : ℝ := max (Nstart : ℝ)
    (max (lam + 2) (lam + 8 / (a ^ 2 * δ) + 2))
  have hstartAtoms := countable_startAtoms nu lam
  obtain ⟨T, hTI, hTnot⟩ :=
    (hstartAtoms.dense_compl ℝ).inter_open_nonempty
      (Ioo L (L + 1)) isOpen_Ioo (nonempty_Ioo.mpr (by linarith))
  have hT : 0 < T := by
    have hL : (Nstart : ℝ) ≤ L := le_max_left _ _
    have hN : (0 : ℝ) ≤ Nstart := Nat.cast_nonneg _
    linarith [hTI.1]
  have hTlam : lam + 1 < T := by
    have hL : lam + 2 ≤ L := (le_max_left _ _).trans (le_max_right _ _)
    linarith [hTI.1]
  have hcoeff : 4 / (a ^ 2 * (T - lam)) < δ := by
    have hsq : 0 < a ^ 2 := sq_pos_of_pos ha
    have hprod : 0 < a ^ 2 * δ := mul_pos hsq hδ
    have hL : lam + 8 / (a ^ 2 * δ) + 2 ≤ L :=
      (le_max_right _ _).trans (le_max_right _ _)
    have hden : 0 < T - lam := by linarith
    apply (div_lt_iff₀ (mul_pos hsq hden)).mpr
    have hx : 8 < (a ^ 2 * δ) * (T - lam) := by
      have := hTI.1
      have hbound : 8 / (a ^ 2 * δ) < T - lam := by linarith
      simpa only [mul_comm] using! (div_lt_iff₀ hprod).mp hbound
    nlinarith
  have hstartSmall : (nu (lateCode lam a T)).toReal < δ := by
    have hsub : lateCode lam a T ⊆ lateCode lam a Nstart := by
      rintro p ⟨m, hm, hlate⟩
      have hN : (Nstart : ℝ) ≤ T :=
        (le_max_left _ _).trans hTI.1.le
      exact ⟨m, hm, hN.trans hlate⟩
    have hNreal : (nu (lateCode lam a Nstart)).toReal < δ := by
      have := (ENNReal.toReal_lt_toReal (measure_ne_top _ _)
        ENNReal.ofReal_ne_top).mpr hNstart
      simpa [ENNReal.toReal_ofReal hδ.le] using! this
    exact (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub)).trans_lt
      hNreal
  obtain ⟨Phi, hPhi, hExp⟩ := hExploration
  have htails : ExplorationTails M lam :=
    (hExp M lam mu hwindow hmu).2
  obtain ⟨Utail, hTUtail, hearly⟩ := htails.2 T δ hT hδ
  have hendT := measure_longCode_tendsto_zero nu lam a ha hgood
  obtain ⟨Nend, hNend⟩ :=
    (hendT.eventually (eventually_lt_nhds
      (ENNReal.ofReal_pos.mpr hδ))).exists
  let Lend : ℝ := max Utail (Nend : ℝ) + 1
  have hendAtoms := countable_endAtoms nu lam
  obtain ⟨U, hUI, hUnot⟩ :=
    (hendAtoms.dense_compl ℝ).inter_open_nonempty
      (Ioo Lend (Lend + 1)) isOpen_Ioo
      (nonempty_Ioo.mpr (by linarith))
  have htailU : Utail < U := by
    have : Utail ≤ max Utail (Nend : ℝ) := le_max_left _ _
    linarith [hUI.1]
  have hendSmall : (nu (longCode lam a U)).toReal < δ := by
    have hsub : longCode lam a U ⊆ longCode lam a Nend := by
      rintro p ⟨m, hm, hend⟩
      have hN : (Nend : ℝ) ≤ U := by
        have : (Nend : ℝ) ≤ max Utail (Nend : ℝ) := le_max_right _ _
        linarith [hUI.1]
      exact ⟨m, hm, hN.trans hend⟩
    have hNreal : (nu (longCode lam a Nend)).toReal < δ := by
      have := (ENNReal.toReal_lt_toReal (measure_ne_top _ _)
        ENNReal.ofReal_ne_top).mpr hNend
      simpa [ENNReal.toReal_ofReal hδ.le] using! this
    exact (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub)).trans_lt
      hNreal
  have hnull : CodedBoundaryNull mu lam a T U :=
    codedBoundaryNull_of_not_atoms mu lam a T U
      (fun h => hanot (Or.inl h)) hTnot hUnot
  have hnullHalf : CodedBoundaryNull mu lam (a / 2) T U := by
    apply codedBoundaryNull_of_not_atoms mu lam (a / 2) T U
    · intro hhalf
      apply hanot (Or.inr ?_)
      exact ⟨a / 2, hhalf, by ring⟩
    · exact hTnot
    · exact hUnot
  have hlate := htails.1 a T δ ha hT hTlam hδ
  have hlate' : ∀ᶠ n : ℕ in atTop,
      probM n (M n) (fun G => lateLarge G T a) < 2 * δ := by
    filter_upwards [hlate] with n hn
    linarith [hcoeff]
  exact ⟨⟨a, T, Utail, U, ha, hT, hTlam, hTUtail, htailU,
    hnull, hnullHalf, hrankSmall, hstartSmall, hendSmall, hlate', hearly⟩⟩

/-! ## Three Brownian errors and seven finite errors -/

private theorem ae_finite_ranks_centered
    (hBrownian : BrownianFoundationStatement)
    (mu : PathLaw) (hmu : BrownianLaw mu) (lam : ℝ) :
    ∀ᵐ p ∂driftedPathLaw mu lam,
      ∀ i : ℕ, 0 < i →
        excursionRankExtended (centerPath p lam) lam i ≠ ⊤ := by
  have hμ : ∀ᵐ w ∂mu, ∀ i : ℕ, 0 < i →
      excursionRankExtended w lam i ≠ ⊤ := by
    apply ae_all_iff.mpr
    intro i
    by_cases hi : 0 < i
    · filter_upwards [((hBrownian.2 mu hmu lam).2 i hi).2]
        with w hw hpos
      exact hw.2.ne
    · exact Filter.Eventually.of_forall (fun w hpos => False.elim (hi hpos))
  have hmap : ∀ᵐ w ∂Measure.map
      (fun p : BrownianPath => centerPath p lam)
      (driftedPathLaw mu lam),
      ∀ i : ℕ, 0 < i → excursionRankExtended w lam i ≠ ⊤ := by
    rw [centerPath_map_driftedPathLaw]
    exact hμ
  exact ae_of_ae_map (measurable_centerPath lam).aemeasurable hmap

private theorem fullLimitRank_eq_kept_of_no_tails
    (p : BrownianPath) (lam a T U : ℝ) (ha : 0 < a)
    (k : ℕ) (_hk : 0 < k)
    (hgood : GoodExcursionPath (centerPath p lam) lam)
    (hfinite : ∀ i : ℕ, 0 < i →
      excursionRankExtended (centerPath p lam) lam i ≠ ⊤)
    (hstart : p ∉ lateCode lam a T) (hend : p ∉ longCode lam a U)
    (hkth : 4 * a < excursionRank (centerPath p lam) lam k) :
    fullLimitRank lam k p = limitTruncatedRank lam a T U k p := by
  have hnomit := noLongCodeOmission_of_no_tails p lam a T U hstart hend
  funext r
  have hr : r.val + 1 ≤ k := r.isLt
  have hanti := excursionRankExtended_antitone (centerPath p lam) lam
    (Nat.zero_lt_succ r.val) hr
  have hreal : excursionRank (centerPath p lam) lam k ≤
      excursionRank (centerPath p lam) lam (r.val + 1) :=
    ENNReal.toReal_mono (hfinite _ (Nat.zero_lt_succ _)) hanti
  have hrank : a < excursionRank (centerPath p lam) lam (r.val + 1) := by
    linarith
  exact (limitTruncatedRank_eq_full_above p lam a T U ha hgood hnomit
    k r (hfinite _ (Nat.zero_lt_succ _)) hrank).symm

private theorem limit_kept_kth_small_probability
    (hBrownian : BrownianFoundationStatement)
    (mu : PathLaw) (hmu : BrownianLaw mu) (lam : ℝ)
    (M : NatSeq) (k : ℕ) (hk : 0 < k) (δ : ℝ) (_hδ : 0 < δ)
    (c : CutoffWitness M lam mu k δ) :
    ((driftedPathLaw mu lam)
      {p | limitTruncatedRank lam c.a c.T c.U k p
        ⟨k - 1, by omega⟩ ≤ 3 * c.a}).toReal < 3 * δ := by
  letI : IsProbabilityMeasure mu := hmu.1
  let nu := driftedPathLaw mu lam
  haveI : IsProbabilityMeasure nu := driftedPathLaw_probability mu lam
  let last : Fin k := ⟨k - 1, by omega⟩
  let A : Set BrownianPath :=
    {p | limitTruncatedRank lam c.a c.T c.U k p last ≤ 3 * c.a}
  let B : Set BrownianPath :=
    {p | excursionRank (centerPath p lam) lam k ≤ 4 * c.a}
  let L := lateCode lam c.a c.T
  let E := longCode lam c.a c.U
  have hae : ∀ᵐ p ∂nu, p ∈ A → p ∈ B ∪ L ∪ E := by
    filter_upwards [ae_good_centered_drift hBrownian mu hmu lam,
      ae_finite_ranks_centered hBrownian mu hmu lam] with p hp hf hpA
    by_cases hB : p ∈ B
    · exact Or.inl (Or.inl hB)
    by_cases hL : p ∈ L
    · exact Or.inl (Or.inr hL)
    by_cases hE : p ∈ E
    · exact Or.inr hE
    have hR : 4 * c.a < excursionRank (centerPath p lam) lam k :=
      lt_of_not_ge hB
    have heq := fullLimitRank_eq_kept_of_no_tails p lam c.a c.T c.U
      c.ha k hk hp hf hL hE hR
    have hlast : last.val + 1 = k := by simp [last]; omega
    have : excursionRank (centerPath p lam) lam k ≤ 3 * c.a := by
      change limitTruncatedRank lam c.a c.T c.U k p last ≤ 3 * c.a at hpA
      rw [← heq] at hpA
      simpa only [fullLimitRank, hlast] using! hpA
    have ha := c.ha
    linarith
  have hmono : (nu A).toReal ≤ (nu (B ∪ L ∪ E)).toReal :=
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hae)
  have hunion : (nu (B ∪ L ∪ E)).toReal ≤
      (nu B).toReal + (nu L).toReal + (nu E).toReal := by
    calc
      _ ≤ (nu (B ∪ L)).toReal + (nu E).toReal :=
        measure_union_toReal_le nu (B ∪ L) E
      _ ≤ _ := by
        simpa only [add_comm, add_left_comm, add_assoc] using!
          (add_le_add_right (measure_union_toReal_le nu B L) (nu E).toReal)
  exact lt_of_le_of_lt (hmono.trans hunion) (by
    have hB := c.hrank
    have hL := c.hstart
    have hE := c.hend
    dsimp [B, L, E, nu] at hB hL hE ⊢
    linarith)

/-! A version of the limit comparison with the actual `M` in the witness. -/
private theorem limit_mismatch_probability'
    (hBrownian : BrownianFoundationStatement)
    (mu : PathLaw) (hmu : BrownianLaw mu) (lam : ℝ)
    (M : NatSeq) (k : ℕ) (hk : 0 < k) (δ : ℝ) (_hδ : 0 < δ)
    (c : CutoffWitness M lam mu k δ) :
    ((driftedPathLaw mu lam)
      {p | fullLimitRank lam k p ≠
        limitTruncatedRank lam c.a c.T c.U k p}).toReal < 3 * δ := by
  letI : IsProbabilityMeasure mu := hmu.1
  let nu := driftedPathLaw mu lam
  haveI : IsProbabilityMeasure nu := driftedPathLaw_probability mu lam
  let A : Set BrownianPath :=
    {p | fullLimitRank lam k p ≠ limitTruncatedRank lam c.a c.T c.U k p}
  let B : Set BrownianPath :=
    {p | excursionRank (centerPath p lam) lam k ≤ 4 * c.a}
  let L := lateCode lam c.a c.T
  let E := longCode lam c.a c.U
  have hae : ∀ᵐ p ∂nu, p ∈ A → p ∈ B ∪ L ∪ E := by
    filter_upwards [ae_good_centered_drift hBrownian mu hmu lam,
      ae_finite_ranks_centered hBrownian mu hmu lam] with p hp hf hpA
    by_cases hB : p ∈ B
    · exact Or.inl (Or.inl hB)
    by_cases hL : p ∈ L
    · exact Or.inl (Or.inr hL)
    by_cases hE : p ∈ E
    · exact Or.inr hE
    have hR : 4 * c.a < excursionRank (centerPath p lam) lam k :=
      lt_of_not_ge hB
    exact False.elim (hpA
      (fullLimitRank_eq_kept_of_no_tails p lam c.a c.T c.U c.ha
        k hk hp hf hL hE hR))
  have hmono : (nu A).toReal ≤ (nu (B ∪ L ∪ E)).toReal :=
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hae)
  have hunion : (nu (B ∪ L ∪ E)).toReal ≤
      (nu B).toReal + (nu L).toReal + (nu E).toReal := by
    calc
      _ ≤ (nu (B ∪ L)).toReal + (nu E).toReal :=
        measure_union_toReal_le nu (B ∪ L) E
      _ ≤ _ := by
        simpa only [add_comm, add_left_comm, add_assoc] using!
          (add_le_add_right (measure_union_toReal_le nu B L) (nu E).toReal)
  exact lt_of_le_of_lt (hmono.trans hunion) (by
    have hB := c.hrank
    have hL := c.hstart
    have hE := c.hend
    dsimp [B, L, E, nu] at hB hL hE ⊢
    linarith)

/-- Closed-set Portmanteau adds one unit of slack to the limiting three-unit
lower-tail estimate. -/
theorem eventually_kept_kth_small_probability
    (hBrownian : BrownianFoundationStatement)
    (hExploration : ExplorationStatement)
    (M : NatSeq) (lam : ℝ) (mu : PathLaw)
    (hwindow : criticalWindow M lam) (hmu : BrownianLaw mu)
    (k : ℕ) (hk : 0 < k) (δ : ℝ) (hδ : 0 < δ)
    (c : CutoffWitness M lam mu k δ) :
    ∀ᶠ n : ℕ in atTop,
      probM n (M n) (fun G =>
        discreteTruncatedRank n c.a c.T c.U k
          (continuousRawExploration G) ⟨k - 1, by omega⟩ ≤ 3 * c.a) <
        4 * δ := by
  letI : IsProbabilityMeasure mu := hmu.1
  letI : IsProbabilityMeasure (driftedPathLaw mu lam) :=
    driftedPathLaw_probability mu lam
  let last : Fin k := ⟨k - 1, by omega⟩
  let C : Set (Fin k → ℝ) := {v | v last ≤ 3 * c.a}
  have hCclosed : IsClosed C := by
    exact isClosed_le (continuous_apply last) continuous_const
  have hweak := truncated_rank_weak_of_public hBrownian hExploration
    M lam mu hwindow hmu c.a c.T c.U c.ha c.hT
    (c.hTUtail.trans c.htailU) c.hnull k
  have hlimsup := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto
    hweak hCclosed
  have hlim : (((driftedProbability mu hmu.1 lam).map
      (limitTruncatedRank lam c.a c.T c.U k) :
      ProbabilityMeasure (Fin k → ℝ)) : Measure (Fin k → ℝ)) C <
      ENNReal.ofReal (4 * δ) := by
    have hmeasure : (((driftedProbability mu hmu.1 lam).map
        (limitTruncatedRank lam c.a c.T c.U k) :
        ProbabilityMeasure (Fin k → ℝ)) : Measure (Fin k → ℝ)) C =
        driftedPathLaw mu lam
          {p | limitTruncatedRank lam c.a c.T c.U k p last ≤ 3 * c.a} := by
      rw [ProbabilityMeasure.map_apply' _
        (measurable_limitTruncatedRank lam c.a c.T c.U k).aemeasurable hCclosed.measurableSet]
      rfl
    rw [hmeasure]
    apply (ENNReal.lt_ofReal_iff_toReal_lt (measure_ne_top _ _)).mpr
    have hsmall := limit_kept_kth_small_probability hBrownian mu hmu
      lam M k hk δ hδ c
    dsimp [last] at hsmall ⊢
    linarith
  have hevent : ∀ᶠ n : ℕ in atTop,
      (((finitePathProbability M n).map
        (discreteTruncatedRank n c.a c.T c.U k) :
        ProbabilityMeasure (Fin k → ℝ)) : Measure (Fin k → ℝ)) C <
        ENNReal.ofReal (4 * δ) :=
    eventually_lt_of_limsup_lt (hlimsup.trans_lt hlim)
  filter_upwards [hevent, hwindow.1] with n hn hnM
  have hmeasure : (((finitePathProbability M n).map
      (discreteTruncatedRank n c.a c.T c.U k) :
      ProbabilityMeasure (Fin k → ℝ)) : Measure (Fin k → ℝ)) C =
      (finitePathProbability M n : Measure BrownianPath)
        {p | discreteTruncatedRank n c.a c.T c.U k p last ≤ 3 * c.a} := by
    rw [ProbabilityMeasure.map_apply' _
      (measurable_discreteTruncatedRank n c.a c.T c.U k).aemeasurable hCclosed.measurableSet]
    rfl
  rw [hmeasure] at hn
  have hreal := (ENNReal.toReal_lt_toReal
    (measure_ne_top _ _) ENNReal.ofReal_ne_top).mpr hn
  rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ 4 * δ)] at hreal
  have hset : MeasurableSet
      {p | discreteTruncatedRank n c.a c.T c.U k p last ≤ 3 * c.a} :=
    measurableSet_le
      ((measurable_discreteTruncatedRank n c.a c.T c.U k).eval)
      measurable_const
  rw [finitePathProbability_event M n hnM _ hset] at hreal
  simpa only [last] using! hreal

/-- The corrected graph budget is `2δ + δ + 4δ = 7δ`: the lower-tail
Portmanteau slack is counted separately. -/
theorem eventually_full_kept_mismatch_probability
    (hBrownian : BrownianFoundationStatement)
    (hExploration : ExplorationStatement)
    (M : NatSeq) (lam : ℝ) (mu : PathLaw)
    (hwindow : criticalWindow M lam) (hmu : BrownianLaw mu)
    (k : ℕ) (hk : 0 < k) (δ : ℝ) (hδ : 0 < δ)
    (c : CutoffWitness M lam mu k δ) :
    ∀ᶠ n : ℕ in atTop,
      probM n (M n) (fun G =>
        fullDiscreteRank n k (continuousRawExploration G) ≠
          discreteTruncatedRank n c.a c.T c.U k
            (continuousRawExploration G)) < 7 * δ := by
  have hsmall := eventually_kept_kth_small_probability
    hBrownian hExploration M lam mu hwindow hmu k hk δ hδ c
  filter_upwards [hsmall, c.hlateGraph, c.hearlyGraph,
    eventually_ge_atTop 1, hwindow.1] with n hnsmall hnlate hnearly hn hnM
  let A : Graph n → Prop := fun G => lateLarge G c.T c.a
  let B : Graph n → Prop := fun G => unfinishedEarly G c.T c.Utail
  let D : Graph n → Prop := fun G =>
    discreteTruncatedRank n c.a c.T c.U k
      (continuousRawExploration G) ⟨k - 1, by omega⟩ ≤ 3 * c.a
  have hsub : ∀ G : Graph n,
      fullDiscreteRank n k (continuousRawExploration G) ≠
        discreteTruncatedRank n c.a c.T c.U k
          (continuousRawExploration G) → (A G ∨ B G) ∨ D G := by
    intro G hneq
    by_cases hA : A G
    · exact Or.inl (Or.inl hA)
    by_cases hB : B G
    · exact Or.inl (Or.inr hB)
    by_cases hD : D G
    · exact Or.inr hD
    have hK : 3 * c.a < discreteTruncatedRank n c.a c.T c.U k
        (continuousRawExploration G) ⟨k - 1, by omega⟩ :=
      lt_of_not_ge hD
    exact False.elim (hneq (fullDiscreteRank_eq_kept_of_no_tails
      G hn lam c.a c.T c.Utail c.U c.ha c.hT
      (c.hT.le.trans c.hTUtail.le) c.htailU k hk hA hB hK))
  have hmono := probM_mono (M := M n)
    (fun G : Graph n => fullDiscreteRank n k (continuousRawExploration G) ≠
      discreteTruncatedRank n c.a c.T c.U k (continuousRawExploration G))
    (fun G => (A G ∨ B G) ∨ D G) hsub
  have hunion := probM_or_le (n := n) (M := M n) hnM
    (fun G => A G ∨ B G) D
  have hab := probM_or_le (n := n) (M := M n) hnM A B
  dsimp [A, B, D] at hnsmall hnlate hnearly hmono hunion hab
  linarith

/-! ## Bounded continuous tests and full vector weak convergence -/

private theorem abs_integral_sub_le_bad
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] (f g : X → ℝ)
    (hf : Integrable f μ) (hg : Integrable g μ)
    (C : ℝ) (hC : 0 < C)
    (hfb : ∀ x, |f x| ≤ C) (hgb : ∀ x, |g x| ≤ C)
    (A : Set X) (heq : ∀ x ∉ A, f x = g x) :
    |(∫ x, f x ∂μ) - (∫ x, g x ∂μ)| ≤
      2 * C * (μ A).toReal := by
  have hd : 0 < 2 * C := by positivity
  have htop : μ A ≠ ⊤ := measure_ne_top _ _
  have hplus : ((∫ x, f x ∂μ) - (∫ x, g x ∂μ)) / (2 * C) ≤
      (μ A).toReal := by
    have h := integral_le_measure (μ := μ)
      (f := fun x => (f x - g x) / (2 * C)) (s := A)
      (fun x _ => by
        apply (div_le_one hd).mpr
        have hf' := hfb x
        have hg' := hgb x
        rw [abs_le] at hf' hg'
        linarith)
      (fun x hx => by
        have he := heq x hx
        simp [he])
    rw [integral_div, integral_sub hf hg] at h
    exact (ENNReal.ofReal_le_iff_le_toReal htop).mp h
  have hminus : ((∫ x, g x ∂μ) - (∫ x, f x ∂μ)) / (2 * C) ≤
      (μ A).toReal := by
    have h := integral_le_measure (μ := μ)
      (f := fun x => (g x - f x) / (2 * C)) (s := A)
      (fun x _ => by
        apply (div_le_one hd).mpr
        have hf' := hfb x
        have hg' := hgb x
        rw [abs_le] at hf' hg'
        linarith)
      (fun x hx => by
        have he := heq x hx
        simp [he])
    rw [integral_div, integral_sub hg hf] at h
    exact (ENNReal.ofReal_le_iff_le_toReal htop).mp h
  apply abs_le.mpr
  constructor
  · have := (div_le_iff₀ hd).mp hminus
    nlinarith
  · have := (div_le_iff₀ hd).mp hplus
    nlinarith

private theorem bounded_test_bound
    {k : ℕ} (F : BoundedContinuousFunction (Fin k → ℝ) ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ y, |F y| ≤ C := by
  obtain ⟨C, hC⟩ := F.bounded
  let y₀ : Fin k → ℝ := 0
  refine ⟨C + |F y₀| + 1, ?_, ?_⟩
  · have hC0 : 0 ≤ C := by
      have h := hC y₀ y₀
      simpa using! (le_trans (dist_nonneg : 0 ≤ dist
        (F y₀) (F y₀)) h)
    positivity
  · intro y
    have hdist := hC y y₀
    have htri := abs_add_le (F y - F y₀) (F y₀)
    have : |F y| ≤ |F y - F y₀| + |F y₀| := by
      simpa only [sub_add_cancel] using! htri
    have : |F y - F y₀| ≤ C := by
      simpa only [Real.dist_eq] using! hdist
    linarith

private theorem integrable_bounded_comp
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsFiniteMeasure μ] {k : ℕ} (F : BoundedContinuousFunction (Fin k → ℝ) ℝ)
    (f : X → Fin k → ℝ) (hf : Measurable f)
    (C : ℝ) (hbound : ∀ y, |F y| ≤ C) :
    Integrable (fun x => F (f x)) μ := by
  apply Integrable.of_bound
    ((F.continuous.measurable.comp hf).aestronglyMeasurable) C
  exact Filter.Eventually.of_forall (fun x => by
    simpa only [Real.norm_eq_abs] using! hbound (f x))

private theorem twenty_budget (C gap δ : ℝ)
    (hC : 0 < C) (hgap : 0 < gap)
    (hδ : δ = gap / (40 * (C + 1))) :
    20 * C * δ < gap := by
  have hden : 0 < 40 * (C + 1) := by positivity
  have hδpos : 0 < δ := by rw [hδ]; positivity
  have heq : δ * (40 * (C + 1)) = gap := by
    rw [hδ]
    field_simp
  have hstrict : 0 < δ * (20 * C + 40) := by positivity
  nlinarith

/-- Every positive-rank finite vector has the exact full weak law under the
two public task assumptions.  No CDF continuity premise occurs here. -/
theorem full_rank_vector_weak_pos
    (hBrownian : BrownianFoundationStatement)
    (hExploration : ExplorationStatement)
    (M : NatSeq) (lam : ℝ) (mu : PathLaw)
    (hwindow : criticalWindow M lam) (hmu : BrownianLaw mu)
    (k : ℕ) (hk : 0 < k) :
    Tendsto (fun n => (finitePathProbability M n).map
      (fullDiscreteRank n k)) atTop
      (𝓝 ((driftedProbability mu hmu.1 lam).map
        (fullLimitRank lam k))) := by
  letI : IsProbabilityMeasure mu := hmu.1
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro F
  obtain ⟨C, hC, hbound⟩ := bounded_test_bound F
  let Ifull (n : ℕ) : ℝ :=
    ∫ p, F (fullDiscreteRank n k p) ∂(finitePathProbability M n : Measure BrownianPath)
  let Ilimit : ℝ :=
    ∫ p, F (fullLimitRank lam k p) ∂driftedPathLaw mu lam
  have hmapFull (n : ℕ) :
      (∫ v, F v ∂(((finitePathProbability M n).map
        (fullDiscreteRank n k) :
        ProbabilityMeasure (Fin k → ℝ)) : Measure (Fin k → ℝ))) = Ifull n := by
    exact integral_map (measurable_fullDiscreteRank n k).aemeasurable
      F.continuous.aestronglyMeasurable
  have hmapLimit :
      (∫ v, F v ∂(((driftedProbability mu hmu.1 lam).map
        (fullLimitRank lam k) :
        ProbabilityMeasure (Fin k → ℝ)) : Measure (Fin k → ℝ))) = Ilimit := by
    exact integral_map
      (measurable_fullLimitRank hBrownian mu hmu lam k).aemeasurable
      F.continuous.aestronglyMeasurable
  simp_rw [hmapFull, hmapLimit]
  apply tendsto_order.mpr
  constructor
  · intro b hb
    let δ : ℝ := (Ilimit - b) / (40 * (C + 1))
    have hδ : 0 < δ := by
      have : 0 < Ilimit - b := sub_pos.mpr hb
      dsimp [δ]
      positivity
    obtain ⟨c⟩ := exists_cutoffWitness hBrownian hExploration
      M lam mu hwindow hmu k hk δ hδ
    have hweak := truncated_rank_weak_of_public hBrownian hExploration
      M lam mu hwindow hmu c.a c.T c.U c.ha c.hT
      (c.hTUtail.trans c.htailU) c.hnull k
    have hkept := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp
      hweak) F
    have hlimitBad := limit_mismatch_probability' hBrownian mu hmu
      lam M k hk δ hδ c
    have hfiniteBad := eventually_full_kept_mismatch_probability
      hBrownian hExploration M lam mu hwindow hmu k hk δ hδ c
    have happroxLimit :
        |Ilimit - ∫ p, F (limitTruncatedRank lam c.a c.T c.U k p)
          ∂driftedPathLaw mu lam| ≤ 6 * C * δ := by
      haveI : IsProbabilityMeasure (driftedPathLaw mu lam) :=
        driftedPathLaw_probability mu lam
      have hfint : Integrable (fun p => F (fullLimitRank lam k p))
          (driftedPathLaw mu lam) :=
        integrable_bounded_comp (driftedPathLaw mu lam) F
          (fun p => fullLimitRank lam k p) (measurable_fullLimitRank hBrownian mu hmu lam k) C hbound
      have hgint : Integrable (fun p => F (limitTruncatedRank lam c.a c.T c.U k p))
          (driftedPathLaw mu lam) :=
        integrable_bounded_comp (driftedPathLaw mu lam) F
          (fun p => limitTruncatedRank lam c.a c.T c.U k p) (measurable_limitTruncatedRank lam c.a c.T c.U k) C hbound
      have h := abs_integral_sub_le_bad (driftedPathLaw mu lam)
        (fun p => F (fullLimitRank lam k p))
        (fun p => F (limitTruncatedRank lam c.a c.T c.U k p))
        hfint hgint C hC (fun p => hbound _)
        (fun p => hbound _)
        {p | fullLimitRank lam k p ≠ limitTruncatedRank lam c.a c.T c.U k p}
        (fun p hp => congrArg F (of_not_not hp))
      dsimp [Ilimit] at h ⊢
      nlinarith
    have hkept' : Tendsto (fun n =>
        ∫ p, F (discreteTruncatedRank n c.a c.T c.U k p)
          ∂(finitePathProbability M n : Measure BrownianPath)) atTop
        (𝓝 (∫ p, F (limitTruncatedRank lam c.a c.T c.U k p)
          ∂driftedPathLaw mu lam)) := by
      have hmapK (n : ℕ) :
          (∫ v, F v ∂(((finitePathProbability M n).map
            (discreteTruncatedRank n c.a c.T c.U k) :
            ProbabilityMeasure (Fin k → ℝ)) : Measure (Fin k → ℝ))) =
          ∫ p, F (discreteTruncatedRank n c.a c.T c.U k p)
            ∂(finitePathProbability M n : Measure BrownianPath) := by
        exact integral_map
          (measurable_discreteTruncatedRank n c.a c.T c.U k).aemeasurable
          F.continuous.aestronglyMeasurable
      have hmapL :
          (∫ v, F v ∂(((driftedProbability mu hmu.1 lam).map
            (limitTruncatedRank lam c.a c.T c.U k) :
            ProbabilityMeasure (Fin k → ℝ)) : Measure (Fin k → ℝ))) =
          ∫ p, F (limitTruncatedRank lam c.a c.T c.U k p)
            ∂driftedPathLaw mu lam := by
        exact integral_map
          (measurable_limitTruncatedRank lam c.a c.T c.U k).aemeasurable
          F.continuous.aestronglyMeasurable
      simpa only [hmapK, hmapL] using! hkept
    have hevent := hkept'.eventually_const_lt
      (show b + 14 * C * δ <
        (∫ p, F (limitTruncatedRank lam c.a c.T c.U k p)
          ∂driftedPathLaw mu lam) from by
        have hbudget : 20 * C * δ < Ilimit - b :=
          twenty_budget C (Ilimit - b) δ hC (sub_pos.mpr hb) rfl
        rcases abs_le.mp happroxLimit with ⟨hlo, hhi⟩
        linarith)
    filter_upwards [hevent, hfiniteBad, hwindow.1] with n hnkept hnbad hnM
    have happroxFinite :
        |Ifull n - ∫ p, F (discreteTruncatedRank n c.a c.T c.U k p)
          ∂(finitePathProbability M n : Measure BrownianPath)| ≤ 14 * C * δ := by
      have hfint : Integrable (fun p => F (fullDiscreteRank n k p))
          (finitePathProbability M n : Measure BrownianPath) :=
        integrable_bounded_comp (finitePathProbability M n : Measure BrownianPath) F
          (fun p => fullDiscreteRank n k p) (measurable_fullDiscreteRank n k) C hbound
      have hgint : Integrable (fun p => F (discreteTruncatedRank n c.a c.T c.U k p))
          (finitePathProbability M n : Measure BrownianPath) :=
        integrable_bounded_comp (finitePathProbability M n : Measure BrownianPath) F
          (fun p => discreteTruncatedRank n c.a c.T c.U k p) (measurable_discreteTruncatedRank n c.a c.T c.U k) C hbound
      have hA : MeasurableSet {p : BrownianPath |
          fullDiscreteRank n k p ≠ discreteTruncatedRank n c.a c.T c.U k p} :=
        (measurableSet_eq_fun (measurable_fullDiscreteRank n k)
          (measurable_discreteTruncatedRank n c.a c.T c.U k)).compl
      have hprob := finitePathProbability_event M n hnM _ hA
      have h := abs_integral_sub_le_bad
        (finitePathProbability M n : Measure BrownianPath)
        (fun p => F (fullDiscreteRank n k p))
        (fun p => F (discreteTruncatedRank n c.a c.T c.U k p))
        hfint hgint C hC (fun p => hbound _) (fun p => hbound _)
        {p | fullDiscreteRank n k p ≠ discreteTruncatedRank n c.a c.T c.U k p}
        (fun p hp => congrArg F (of_not_not hp))
      rw [hprob] at h
      dsimp [Ifull] at h ⊢
      nlinarith
    have : b < Ifull n := by
      have := happroxFinite
      rw [abs_le] at this
      linarith
    exact this
  · intro b hb
    let δ : ℝ := (b - Ilimit) / (40 * (C + 1))
    have hδ : 0 < δ := by
      have : 0 < b - Ilimit := sub_pos.mpr hb
      dsimp [δ]
      positivity
    obtain ⟨c⟩ := exists_cutoffWitness hBrownian hExploration
      M lam mu hwindow hmu k hk δ hδ
    have hweak := truncated_rank_weak_of_public hBrownian hExploration
      M lam mu hwindow hmu c.a c.T c.U c.ha c.hT
      (c.hTUtail.trans c.htailU) c.hnull k
    have hkept := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp
      hweak) F
    have hlimitBad := limit_mismatch_probability' hBrownian mu hmu
      lam M k hk δ hδ c
    have hfiniteBad := eventually_full_kept_mismatch_probability
      hBrownian hExploration M lam mu hwindow hmu k hk δ hδ c
    have happroxLimit :
        |Ilimit - ∫ p, F (limitTruncatedRank lam c.a c.T c.U k p)
          ∂driftedPathLaw mu lam| ≤ 6 * C * δ := by
      haveI : IsProbabilityMeasure (driftedPathLaw mu lam) :=
        driftedPathLaw_probability mu lam
      have hfint : Integrable (fun p => F (fullLimitRank lam k p))
          (driftedPathLaw mu lam) :=
        integrable_bounded_comp (driftedPathLaw mu lam) F
          (fun p => fullLimitRank lam k p) (measurable_fullLimitRank hBrownian mu hmu lam k) C hbound
      have hgint : Integrable (fun p => F (limitTruncatedRank lam c.a c.T c.U k p))
          (driftedPathLaw mu lam) :=
        integrable_bounded_comp (driftedPathLaw mu lam) F
          (fun p => limitTruncatedRank lam c.a c.T c.U k p) (measurable_limitTruncatedRank lam c.a c.T c.U k) C hbound
      have h := abs_integral_sub_le_bad (driftedPathLaw mu lam)
        (fun p => F (fullLimitRank lam k p))
        (fun p => F (limitTruncatedRank lam c.a c.T c.U k p))
        hfint hgint C hC (fun p => hbound _)
        (fun p => hbound _)
        {p | fullLimitRank lam k p ≠ limitTruncatedRank lam c.a c.T c.U k p}
        (fun p hp => congrArg F (of_not_not hp))
      dsimp [Ilimit] at h ⊢
      nlinarith
    have hkept' : Tendsto (fun n =>
        ∫ p, F (discreteTruncatedRank n c.a c.T c.U k p)
          ∂(finitePathProbability M n : Measure BrownianPath)) atTop
        (𝓝 (∫ p, F (limitTruncatedRank lam c.a c.T c.U k p)
          ∂driftedPathLaw mu lam)) := by
      have hmapK (n : ℕ) :
          (∫ v, F v ∂(((finitePathProbability M n).map
            (discreteTruncatedRank n c.a c.T c.U k) :
            ProbabilityMeasure (Fin k → ℝ)) : Measure (Fin k → ℝ))) =
          ∫ p, F (discreteTruncatedRank n c.a c.T c.U k p)
            ∂(finitePathProbability M n : Measure BrownianPath) := by
        exact integral_map
          (measurable_discreteTruncatedRank n c.a c.T c.U k).aemeasurable
          F.continuous.aestronglyMeasurable
      have hmapL :
          (∫ v, F v ∂(((driftedProbability mu hmu.1 lam).map
            (limitTruncatedRank lam c.a c.T c.U k) :
            ProbabilityMeasure (Fin k → ℝ)) : Measure (Fin k → ℝ))) =
          ∫ p, F (limitTruncatedRank lam c.a c.T c.U k p)
            ∂driftedPathLaw mu lam := by
        exact integral_map
          (measurable_limitTruncatedRank lam c.a c.T c.U k).aemeasurable
          F.continuous.aestronglyMeasurable
      simpa only [hmapK, hmapL] using! hkept
    have hevent := hkept'.eventually_lt_const
      (show (∫ p, F (limitTruncatedRank lam c.a c.T c.U k p)
          ∂driftedPathLaw mu lam) < b - 14 * C * δ from by
        have hbudget : 20 * C * δ < b - Ilimit :=
          twenty_budget C (b - Ilimit) δ hC (sub_pos.mpr hb) rfl
        rcases abs_le.mp happroxLimit with ⟨hlo, hhi⟩
        linarith)
    filter_upwards [hevent, hfiniteBad, hwindow.1] with n hnkept hnbad hnM
    have happroxFinite :
        |Ifull n - ∫ p, F (discreteTruncatedRank n c.a c.T c.U k p)
          ∂(finitePathProbability M n : Measure BrownianPath)| ≤ 14 * C * δ := by
      have hfint : Integrable (fun p => F (fullDiscreteRank n k p))
          (finitePathProbability M n : Measure BrownianPath) :=
        integrable_bounded_comp (finitePathProbability M n : Measure BrownianPath) F
          (fun p => fullDiscreteRank n k p) (measurable_fullDiscreteRank n k) C hbound
      have hgint : Integrable (fun p => F (discreteTruncatedRank n c.a c.T c.U k p))
          (finitePathProbability M n : Measure BrownianPath) :=
        integrable_bounded_comp (finitePathProbability M n : Measure BrownianPath) F
          (fun p => discreteTruncatedRank n c.a c.T c.U k p) (measurable_discreteTruncatedRank n c.a c.T c.U k) C hbound
      have hA : MeasurableSet {p : BrownianPath |
          fullDiscreteRank n k p ≠ discreteTruncatedRank n c.a c.T c.U k p} :=
        (measurableSet_eq_fun (measurable_fullDiscreteRank n k)
          (measurable_discreteTruncatedRank n c.a c.T c.U k)).compl
      have hprob := finitePathProbability_event M n hnM _ hA
      have h := abs_integral_sub_le_bad
        (finitePathProbability M n : Measure BrownianPath)
        (fun p => F (fullDiscreteRank n k p))
        (fun p => F (discreteTruncatedRank n c.a c.T c.U k p))
        hfint hgint C hC (fun p => hbound _) (fun p => hbound _)
        {p | fullDiscreteRank n k p ≠ discreteTruncatedRank n c.a c.T c.U k p}
        (fun p hp => congrArg F (of_not_not hp))
      rw [hprob] at h
      dsimp [Ifull] at h ⊢
      nlinarith
    have : Ifull n < b := by
      have := happroxFinite
      rw [abs_le] at this
      linarith
    exact this

/-- The exported all-ranks weak law includes the empty vector. -/
theorem full_rank_vector_weak
    (hBrownian : BrownianFoundationStatement)
    (hExploration : ExplorationStatement)
    (M : NatSeq) (lam : ℝ) (mu : PathLaw)
    (hwindow : criticalWindow M lam) (hmu : BrownianLaw mu)
    (k : ℕ) :
    Tendsto (fun n => (finitePathProbability M n).map
      (fullDiscreteRank n k)) atTop
      (𝓝 ((driftedProbability mu hmu.1 lam).map
        (fullLimitRank lam k))) := by
  by_cases hk : 0 < k
  · exact full_rank_vector_weak_pos hBrownian hExploration M lam mu
      hwindow hmu k hk
  · have hzero : k = 0 := by omega
    subst k
    apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
    intro F
    have hconst (v : Fin 0 → ℝ) : F v = F (fun i => Fin.elim0 i) := by
      congr 1
      exact Subsingleton.elim _ _
    have hleft (n : ℕ) :
        (∫ v, F v ∂(((finitePathProbability M n).map
          (fullDiscreteRank n 0) :
          ProbabilityMeasure (Fin 0 → ℝ)) : Measure (Fin 0 → ℝ))) =
          F (fun i => Fin.elim0 i) := by
      haveI : IsProbabilityMeasure
          (Measure.map (fullDiscreteRank n 0)
            (finitePathProbability M n : Measure BrownianPath)) :=
        Measure.isProbabilityMeasure_map
          (measurable_fullDiscreteRank n 0).aemeasurable
      simp_rw [hconst]
      simp
    have hright :
        (∫ v, F v ∂(((driftedProbability mu hmu.1 lam).map
          (fullLimitRank lam 0) :
          ProbabilityMeasure (Fin 0 → ℝ)) : Measure (Fin 0 → ℝ))) =
          F (fun i => Fin.elim0 i) := by
      haveI : IsProbabilityMeasure
          (Measure.map (fullLimitRank lam 0)
            (driftedProbability mu hmu.1 lam : Measure BrownianPath)) :=
        Measure.isProbabilityMeasure_map
          (measurable_fullLimitRank hBrownian mu hmu lam 0).aemeasurable
      simp_rw [hconst]
      simp
    simpa only [hleft, hright] using!
      (tendsto_const_nhds : Tendsto
        (fun _ : ℕ => F (fun i => Fin.elim0 i)) atTop
        (𝓝 (F (fun i => Fin.elim0 i))))

/-- The exact graph vector in the original public rank convention. -/
def graphRankVector {n : ℕ} (G : Graph n) (k : ℕ) : Fin k → ℝ :=
  fun r => (rankSize G (r.val + 1) : ℝ) / n23 n

/-- The limiting vector is evaluated on the original Brownian path. -/
def brownianRankVector (w : BrownianPath) (lam : ℝ)
    (k : ℕ) : Fin k → ℝ :=
  fun r => excursionRank w lam (r.val + 1)

theorem fullLimitRank_on_driftPath (w : BrownianPath) (lam : ℝ)
    (k : ℕ) :
    fullLimitRank lam k (driftPath w lam) = brownianRankVector w lam k := by
  funext r
  simp [fullLimitRank, brownianRankVector, centerPath_driftPath]

/- Bounded continuous tests of the literal finite component ranks converge
to tests of the one-drift Brownian excursion ranks.  This is the direct B06
consumer form of the full vector weak law. -/
end

end Erdos745.WrapUp.Proofs.Internal.W15_CRITICAL_RankLimit


/-! Strict distribution functions of the exact critical component ranks. -/

namespace Erdos745.WrapUp.Proofs.Internal.W15_CRITICAL_PublicTransfer

open Erdos745.WrapUp
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_FiniteLaw
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_Interpolation
open Erdos745.WrapUp.Proofs.Internal.W15_CRITICAL_RankLimit
open Erdos745.WrapUp.Proofs.Internal.W15_CRITICAL_KeptWeak
open Filter MeasureTheory Set
open scoped Topology ENNReal

noncomputable section
attribute [local instance] Classical.propDecidable
local instance : MeasurableSpace BrownianPath := borel BrownianPath
local instance : BorelSpace BrownianPath := ⟨rfl⟩
local instance graphMeasurableSpace (n : ℕ) : MeasurableSpace (Graph n) := ⊤

/-- Continuity of a strict distribution function rules out an atom at its
threshold.  The decreasing events are the strict cuts at `x + 1/(n+1)`. -/
theorem strictCDF_no_atom (μ : PathLaw) [IsProbabilityMeasure μ]
    (R : BrownianPath → ℝ) (hR : Measurable R) (x : ℝ)
    (hcont : ContinuousAt (fun y => (μ {w | R w < y}).toReal) x) :
    μ {w | R w = x} = 0 := by
  let e : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  let S : ℕ → Set BrownianPath := fun n => {w | R w < x + e n}
  have hepos (n : ℕ) : 0 < e n := by dsimp [e]; positivity
  have he : Tendsto e atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hant : Antitone S := by
    intro n m hnm w hw
    change R w < x + e m at hw
    have hcast : (n : ℝ) ≤ m := by exact_mod_cast hnm
    have hemono : e m ≤ e n := by
      dsimp [e]
      gcongr
    exact lt_of_lt_of_le hw (add_le_add_right hemono x)
  have hinter : (⋂ n, S n) = {w | R w ≤ x} := by
    ext w
    constructor
    · intro hw
      by_contra hn
      have hpos : 0 < R w - x := sub_pos.mpr (lt_of_not_ge hn)
      obtain ⟨n, hn⟩ := (he.eventually_lt_const hpos).exists
      have hw' := Set.mem_iInter.mp hw n
      change R w < x + e n at hw'
      linarith
    · intro hw
      change R w ≤ x at hw
      apply Set.mem_iInter.mpr
      intro n
      change R w < x + e n
      linarith [hepos n]
  have ht := tendsto_measure_iInter_atTop (μ := μ) (s := S)
    (fun n => (measurableSet_lt hR measurable_const).nullMeasurableSet)
    hant ⟨0, measure_ne_top _ _⟩
  rw [hinter] at ht
  have hreal : Tendsto (fun n => (μ (S n)).toReal) atTop
      (𝓝 ((μ {w | R w ≤ x}).toReal)) :=
    (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp
      (by simpa only [Function.comp_def] using! ht)
  have hx : Tendsto (fun n => x + e n) atTop (𝓝 x) := by
    simpa using! tendsto_const_nhds.add he
  have hcont' : Tendsto (fun n => (μ (S n)).toReal) atTop
      (𝓝 ((μ {w | R w < x}).toReal)) := by
    simpa only [S] using! hcont.tendsto.comp hx
  have hmeasure : μ {w | R w ≤ x} = μ {w | R w < x} := by
    apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _)
      (measure_ne_top _ _)).mp
    exact tendsto_nhds_unique hreal hcont'
  have hdiff : {w | R w ≤ x} \ {w | R w < x} = {w | R w = x} := by
    ext w
    simp only [mem_diff, mem_setOf_eq, not_lt]
    exact le_antisymm_iff.symm
  rw [← hdiff, measure_diff (by intro w hw; exact (show R w < x from hw).le)
    (measurableSet_lt hR measurable_const).nullMeasurableSet
    (measure_ne_top _ _), hmeasure, tsub_self]

/-- The strict lower rectangle has no boundary mass if each coordinate
hyperplane has no mass.  This includes the empty rectangle at `k = 0`. -/
theorem null_frontier_lowerRectangle {k : ℕ}
    (ν : Measure (Fin k → ℝ)) (x : Fin k → ℝ)
    (hnull : ∀ r : Fin k, ν {v | v r = x r} = 0) :
    ν (frontier {v : Fin k → ℝ | ∀ r, v r < x r}) = 0 := by
  let A : Set (Fin k → ℝ) := {v | ∀ r, v r < x r}
  have hA : A = Set.univ.pi (fun r : Fin k => Iio (x r)) := by
    ext v
    simp [A, Set.mem_pi]
  have hopen : IsOpen A := by
    rw [hA]
    exact isOpen_set_pi Set.finite_univ (fun r _ => isOpen_Iio)
  have hsub : frontier A ⊆ ⋃ r : Fin k, {v | v r = x r} := by
    intro v hv
    by_contra hbad
    have hle (r : Fin k) : v r ≤ x r := by
      have hc : v ∈ closure A := frontier_subset_closure hv
      rw [hA] at hc
      have hr := (mem_closure_pi.mp hc) r (Set.mem_univ r)
      simpa only [closure_Iio, mem_Iic] using! hr
    have hlt (r : Fin k) : v r < x r := by
      have hne : v r ≠ x r := by
        intro heq
        exact hbad (Set.mem_iUnion_of_mem r heq)
      exact lt_of_le_of_ne (hle r) hne
    have hvA : v ∈ A := hlt
    have hnot : v ∉ A := by
      change v ∈ closure A \ interior A at hv
      rw [hopen.interior_eq] at hv
      exact hv.2
    exact hnot hvA
  apply measure_mono_null hsub
  exact measure_iUnion_null hnull

private theorem measurable_rank (hBrownian : BrownianFoundationStatement)
    (mu : PathLaw) (hmu : BrownianLaw mu) (lam : ℝ)
    (i : ℕ) (hi : 0 < i) :
    Measurable (fun w : BrownianPath => excursionRank w lam i) :=
  (((hBrownian.2 mu hmu lam).2 i hi).1).ennreal_toReal

private theorem limit_vector_event (hBrownian : BrownianFoundationStatement)
    (mu : PathLaw) (hmu : BrownianLaw mu) (lam : ℝ) (k : ℕ)
    (A : Set (Fin k → ℝ)) (hA : MeasurableSet A) :
    ((((driftedProbability mu hmu.1 lam).map
      (fullLimitRank lam k) :
      ProbabilityMeasure (Fin k → ℝ)) : Measure (Fin k → ℝ)) A) =
      mu {w | brownianRankVector w lam k ∈ A} := by
  rw [ProbabilityMeasure.map_apply' _
    (measurable_fullLimitRank hBrownian mu hmu lam k).aemeasurable hA]
  change driftedPathLaw mu lam
    {p | fullLimitRank lam k p ∈ A} = _
  unfold driftedPathLaw
  change (Measure.map (fun w : BrownianPath => driftPath w lam) mu)
    (fullLimitRank lam k ⁻¹' A) = _
  rw [Measure.map_apply (measurable_driftPath lam)
    (hA.preimage (measurable_fullLimitRank hBrownian mu hmu lam k))]
  congr 1
  ext w
  simp only [mem_preimage, mem_setOf_eq, fullLimitRank_on_driftPath]

private theorem finite_vector_event (M : NatSeq) (n k : ℕ)
    (hnM : M n ≤ capacity n) (hn : 0 < n)
    (A : Set (Fin k → ℝ)) (hA : MeasurableSet A) :
    (((((finitePathProbability M n).map
      (fullDiscreteRank n k) :
      ProbabilityMeasure (Fin k → ℝ)) : Measure (Fin k → ℝ)) A)).toReal =
      probM n (M n) (fun G => graphRankVector G k ∈ A) := by
  rw [ProbabilityMeasure.map_apply' _
    (measurable_fullDiscreteRank n k).aemeasurable hA]
  simp only [finitePathProbability, dif_pos hnM]
  change (explorationPathMeasure n (M n) hnM
    {p | fullDiscreteRank n k p ∈ A}).toReal = _
  rw [explorationPathMeasure]
  change ((Measure.map (fun G : Graph n => explorationInterpolation n G)
    (fixedMeasure n (M n) hnM)) (fullDiscreteRank n k ⁻¹' A)).toReal = _
  rw [Measure.map_apply
    (measurable_explorationInterpolation n)
    (hA.preimage (measurable_fullDiscreteRank n k))]
  change (fixedMeasure n (M n) hnM
    {G | fullDiscreteRank n k (explorationInterpolation n G) ∈ A}).toReal = _
  rw [fixedMeasure_apply_toReal]
  congr 1
  funext G
  congr 1
  funext r
  exact fullDiscreteRank_on_BFS G hn k r

/-- Coordinatewise continuity of the public strict CDF gives convergence of
the literal finite lower-rectangle probabilities. -/
theorem joint_strict_CDF_convergence
    (hBrownian : BrownianFoundationStatement)
    (hExploration : ExplorationStatement)
    (M : NatSeq) (lam : ℝ) (mu : PathLaw)
    (hwindow : criticalWindow M lam) (hmu : BrownianLaw mu)
    (k : ℕ) (x : Fin k → ℝ)
    (hcont : ∀ r : Fin k, ContinuousAt
      (rankCDF mu lam (r.val + 1)) (x r)) :
    Tendsto (fun n => probM n (M n) (fun G =>
      ∀ r : Fin k, (rankSize G (r.val + 1) : ℝ) / n23 n < x r))
      atTop (𝓝 (jointCDF mu lam k x)) := by
  letI : IsProbabilityMeasure mu := hmu.1
  let A : Set (Fin k → ℝ) := {v | ∀ r, v r < x r}
  have hA : MeasurableSet A := by
    have hopen : IsOpen A := by
      have hEq : A = Set.univ.pi (fun r : Fin k => Iio (x r)) := by
        ext v
        simp [A, Set.mem_pi]
      rw [hEq]
      exact isOpen_set_pi Set.finite_univ (fun r _ => isOpen_Iio)
    exact hopen.measurableSet
  have hatom (r : Fin k) :
      mu {w | excursionRank w lam (r.val + 1) = x r} = 0 := by
    exact strictCDF_no_atom mu (fun w => excursionRank w lam (r.val + 1))
      (measurable_rank hBrownian mu hmu lam _ (Nat.zero_lt_succ _))
      (x r) (hcont r)
  let ν : ProbabilityMeasure (Fin k → ℝ) :=
    (driftedProbability mu hmu.1 lam).map
      (fullLimitRank lam k)
  have hnull (r : Fin k) :
      (ν : Measure (Fin k → ℝ)) {v | v r = x r} = 0 := by
    have hset : MeasurableSet {v : Fin k → ℝ | v r = x r} :=
      (continuous_apply r).measurable (measurableSet_singleton _)
    rw [show (ν : Measure (Fin k → ℝ)) {v | v r = x r} =
      mu {w | brownianRankVector w lam k ∈ {v | v r = x r}} from
      limit_vector_event hBrownian mu hmu lam k _ hset]
    simpa only [brownianRankVector, mem_setOf_eq] using! hatom r
  have hbdry : (ν : Measure (Fin k → ℝ)) (frontier A) = 0 :=
    null_frontier_lowerRectangle (ν : Measure (Fin k → ℝ)) x hnull
  have hweak := full_rank_vector_weak hBrownian hExploration M lam mu
    hwindow hmu k
  have hport := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'
    hweak hbdry
  have hreal : Tendsto (fun n =>
      (((((finitePathProbability M n).map
        (fullDiscreteRank n k) :
        ProbabilityMeasure (Fin k → ℝ)) : Measure (Fin k → ℝ)) A)).toReal)
      atTop (𝓝 (((ν : Measure (Fin k → ℝ)) A).toReal)) :=
    (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp hport
  have hfinite : (fun n =>
      (((((finitePathProbability M n).map
        (fullDiscreteRank n k) :
        ProbabilityMeasure (Fin k → ℝ)) : Measure (Fin k → ℝ)) A)).toReal)
      =ᶠ[atTop] (fun n => probM n (M n) (fun G =>
        ∀ r : Fin k, (rankSize G (r.val + 1) : ℝ) / n23 n < x r)) := by
    filter_upwards [hwindow.1, eventually_ge_atTop 1] with n hnM hn
    simpa only [A, graphRankVector, mem_setOf_eq] using!
      finite_vector_event M n k hnM hn A hA
  have hlimit : ((ν : Measure (Fin k → ℝ)) A).toReal =
      jointCDF mu lam k x := by
    rw [limit_vector_event hBrownian mu hmu lam k A hA]
    rfl
  rw [hlimit] at hreal
  exact hreal.congr' hfinite

/-- Rank two is a separate one-coordinate projection.  Its proof invokes
only continuity of `criticalCDF`, with no condition on the first rank. -/
theorem rank_two_strict_CDF_convergence
    (hBrownian : BrownianFoundationStatement)
    (hExploration : ExplorationStatement)
    (M : NatSeq) (lam : ℝ) (mu : PathLaw)
    (hwindow : criticalWindow M lam) (hmu : BrownianLaw mu)
    (x : ℝ) (hcont : ContinuousAt (criticalCDF mu lam) x) :
    Tendsto (fun n => probM n (M n) (fun G =>
      (rankSize G 2 : ℝ) / n23 n < x)) atTop
      (𝓝 (criticalCDF mu lam x)) := by
  letI : IsProbabilityMeasure mu := hmu.1
  let r : Fin 2 := ⟨1, by omega⟩
  let A : Set (Fin 2 → ℝ) := {v | v r < x}
  have hA : MeasurableSet A :=
    (isOpen_lt (continuous_apply r) continuous_const).measurableSet
  have hatom : mu {w | excursionRank w lam 2 = x} = 0 :=
    strictCDF_no_atom mu (fun w => excursionRank w lam 2)
      (measurable_rank hBrownian mu hmu lam 2 (by omega)) x hcont
  let ν : ProbabilityMeasure (Fin 2 → ℝ) :=
    (driftedProbability mu hmu.1 lam).map
      (fullLimitRank lam 2)
  have hnull : (ν : Measure (Fin 2 → ℝ)) (frontier A) = 0 := by
    have hsub : frontier A ⊆ {v : Fin 2 → ℝ | v r = x} :=
      frontier_lt_subset_eq (continuous_apply r) continuous_const
    apply measure_mono_null hsub
    have hset : MeasurableSet {v : Fin 2 → ℝ | v r = x} :=
      (continuous_apply r).measurable (measurableSet_singleton _)
    rw [limit_vector_event hBrownian mu hmu lam 2 _ hset]
    simpa only [brownianRankVector, r, mem_setOf_eq] using! hatom
  have hweak := full_rank_vector_weak hBrownian hExploration M lam mu
    hwindow hmu 2
  have hport := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'
    hweak hnull
  have hreal : Tendsto (fun n =>
      (((((finitePathProbability M n).map
        (fullDiscreteRank n 2) :
        ProbabilityMeasure (Fin 2 → ℝ)) : Measure (Fin 2 → ℝ)) A)).toReal)
      atTop (𝓝 (((ν : Measure (Fin 2 → ℝ)) A).toReal)) :=
    (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp hport
  have hfinite : (fun n =>
      (((((finitePathProbability M n).map
        (fullDiscreteRank n 2) :
        ProbabilityMeasure (Fin 2 → ℝ)) : Measure (Fin 2 → ℝ)) A)).toReal)
      =ᶠ[atTop] (fun n => probM n (M n) (fun G =>
        (rankSize G 2 : ℝ) / n23 n < x)) := by
    filter_upwards [hwindow.1, eventually_ge_atTop 1] with n hnM hn
    simpa only [A, graphRankVector, r, mem_setOf_eq] using!
      finite_vector_event M n 2 hnM hn A hA
  have hlimit : ((ν : Measure (Fin 2 → ℝ)) A).toReal =
      criticalCDF mu lam x := by
    rw [limit_vector_event hBrownian mu hmu lam 2 A hA]
    rfl
  rw [hlimit] at hreal
  exact hreal.congr' hfinite

/-- The public critical statement uses exactly the two advertised inputs. -/
theorem criticalLaw_of_public
    (hBrownian : BrownianFoundationStatement)
    (hExploration : ExplorationStatement) : CriticalStatement := by
  change criticalLaw
  refine ⟨hBrownian.1.exists, ?_⟩
  intro mu hmu lam
  refine ⟨fun i hi => ((hBrownian.2 mu hmu lam).2 i hi).2, ?_⟩
  intro M hwindow
  constructor
  · intro x hx
    exact rank_two_strict_CDF_convergence hBrownian hExploration M lam mu
      hwindow hmu x hx
  · intro k x hx
    exact joint_strict_CDF_convergence hBrownian hExploration M lam mu
      hwindow hmu k x hx

end

end Erdos745.WrapUp.Proofs.Internal.W15_CRITICAL_PublicTransfer
