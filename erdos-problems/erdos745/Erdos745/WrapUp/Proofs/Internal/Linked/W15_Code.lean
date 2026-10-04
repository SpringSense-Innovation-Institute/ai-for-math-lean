module

public import Erdos745.WrapUp.Proofs.Internal.Linked.W15_Base
public import Erdos745.WrapUp.Proofs.Internal.Linked.W13_Excursions

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local simp] Pi.div_def Pi.mul_def Pi.add_def Pi.sub_def Pi.neg_def Pi.inv_def Function.comp_def Pi.pow_def Pi.smul_def Real.rpow_eq_pow

@[expose] public section


namespace Erdos745.WrapUp.Proofs.Internal.W15_CRITICAL_Code

open Erdos745.WrapUp
open Erdos745.WrapUp.Proofs.Internal.W13_BROWNIAN_Ranks
open Erdos745.WrapUp.Proofs.Internal.W15_CRITICAL_Truncated
open Set
open scoped ENNReal Topology

noncomputable section
attribute [local instance] Classical.propDecidable

private def unitNNReal (x : unitInterval) : NNReal :=
  NNReal.mk ((x : ℝ)) (x.property.1)

private def scaleToTime (t : NNReal) (x : unitInterval) : NNReal :=
  t * unitNNReal x

private lemma scaleToTime_image (t : NNReal) :
    scaleToTime t '' univ = Icc 0 t := by
  ext u
  constructor
  · rintro ⟨x, _, rfl⟩
    exact ⟨zero_le, mul_le_of_le_one_right (zero_le) (by
      exact_mod_cast x.property.2)⟩
  · intro hu
    by_cases ht : t = 0
    · subst t
      have hu0 : u = 0 := le_antisymm hu.2 hu.1
      subst u
      refine ⟨(0 : unitInterval), mem_univ _, ?_⟩
      simp [scaleToTime, unitNNReal]
    · have htpos : 0 < (t : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr ht)
      let x : unitInterval :=
        ⟨(u : ℝ) / (t : ℝ), by
          constructor
          · positivity
          · exact (div_le_one htpos).2 (by exact_mod_cast hu.2)⟩
      refine ⟨x, mem_univ _, ?_⟩
      apply NNReal.eq
      simp only [scaleToTime, unitNNReal, NNReal.coe_mul, NNReal.coe_mk, x]
      field_simp

private def intervalTime (a b : NNReal) (x : unitInterval) : NNReal :=
  a + (b - a) * unitNNReal x

private lemma intervalTime_image {a b : NNReal} (hab : a ≤ b) :
    intervalTime a b '' univ = Icc a b := by
  ext u
  constructor
  · rintro ⟨x, _, rfl⟩
    constructor
    · exact le_add_of_nonneg_right (zero_le)
    · calc
        intervalTime a b x ≤ a + (b - a) := by
          unfold intervalTime
          gcongr
          exact mul_le_of_le_one_right (zero_le) (by
            exact_mod_cast x.property.2)
        _ = b := add_tsub_cancel_of_le hab
  · intro hu
    have hv : u - a ∈ Icc (0 : NNReal) (b - a) := by
      exact ⟨zero_le, tsub_le_tsub_right hu.2 a⟩
    rw [← scaleToTime_image (b - a)] at hv
    rcases hv with ⟨x, _, hx⟩
    refine ⟨x, mem_univ _, ?_⟩
    unfold intervalTime
    change a + scaleToTime (b - a) x = u
    rw [hx, add_tsub_cancel_of_le hu.1]

theorem leftCodeCondition_iff_of_excursion
    (p : BrownianPath) (lam : ℝ) {a b q : NNReal}
    (hab : excursion (centerPath p lam) lam a b)
    (hq : q ∈ Ioo a b) (j : ℕ) :
    leftCodeCondition lam q j p ↔ codeTime j ≤ a := by
  constructor
  · rintro ⟨hjq, hzero⟩
    rcases (reflectedIntervalInf_eq_zero_iff (centerPath p lam) lam
      (codeTime j) q).mp hzero with ⟨x, hxzero⟩
    have htime : intervalTime (codeTime j) q x ∈ Icc (codeTime j) q := by
      rw [← intervalTime_image hjq]
      exact ⟨x, mem_univ _, rfl⟩
    have hle : intervalTime (codeTime j) q x ≤ a := by
      by_contra h
      have hpos := hab.2.2.2 (intervalTime (codeTime j) q x)
        ⟨lt_of_not_ge h, htime.2.trans_lt hq.2⟩
      exact (ne_of_gt hpos) hxzero
    exact htime.1.trans hle
  · intro hja
    have hjq : codeTime j ≤ q := hja.trans hq.1.le
    refine ⟨hjq, (reflectedIntervalInf_eq_zero_iff
      (centerPath p lam) lam (codeTime j) q).2 ?_⟩
    have ha : a ∈ Icc (codeTime j) q := ⟨hja, hq.1.le⟩
    rw [← intervalTime_image hjq] at ha
    rcases ha with ⟨x, _, hxa⟩
    refine ⟨x, ?_⟩
    change reflected (centerPath p lam) lam (intervalTime (codeTime j) q x) = 0
    rw [hxa, hab.2.1]

theorem rightCodeCondition_iff_of_excursion
    (p : BrownianPath) (lam : ℝ) {a b q : NNReal}
    (hab : excursion (centerPath p lam) lam a b)
    (hq : q ∈ Ioo a b) (j : ℕ) :
    rightCodeCondition lam q j p ↔ b ≤ codeTime j := by
  constructor
  · rintro ⟨hqj, hzero⟩
    rcases (reflectedIntervalInf_eq_zero_iff (centerPath p lam) lam
      q (codeTime j)).mp hzero with ⟨x, hxzero⟩
    have htime : intervalTime q (codeTime j) x ∈ Icc q (codeTime j) := by
      rw [← intervalTime_image hqj]
      exact ⟨x, mem_univ _, rfl⟩
    have hle : b ≤ intervalTime q (codeTime j) x := by
      by_contra h
      have hpos := hab.2.2.2 (intervalTime q (codeTime j) x)
        ⟨hq.1.trans_le htime.1, lt_of_not_ge h⟩
      exact (ne_of_gt hpos) hxzero
    exact hle.trans htime.2
  · intro hbj
    have hqj : q ≤ codeTime j := hq.2.le.trans hbj
    refine ⟨hqj, (reflectedIntervalInf_eq_zero_iff
      (centerPath p lam) lam q (codeTime j)).2 ?_⟩
    have hb : b ∈ Icc q (codeTime j) := ⟨hq.2.le, hbj⟩
    rw [← intervalTime_image hqj] at hb
    rcases hb with ⟨x, _, hxb⟩
    refine ⟨x, ?_⟩
    change reflected (centerPath p lam) lam (intervalTime q (codeTime j) x) = 0
    rw [hxb, hab.2.2.1]

theorem codedLeft_eq_of_excursion
    (p : BrownianPath) (lam : ℝ) {a b q : NNReal}
    (hab : excursion (centerPath p lam) lam a b)
    (hq : q ∈ Ioo a b) : codedLeft lam q p = (a : ENNReal) := by
  unfold codedLeft
  apply le_antisymm
  · apply iSup_le
    intro j
    split_ifs with hj
    · exact_mod_cast (leftCodeCondition_iff_of_excursion p lam hab hq j).mp hj
    · exact bot_le
  · by_cases ha : a = 0
    · subst a
      exact bot_le
    · have h0a : (0 : NNReal) < a := pos_iff_ne_zero.mpr ha
      have hdense : Dense (range codeTime) :=
        TopologicalSpace.denseRange_denseSeq NNReal
      rcases hdense.exists_seq_strictMono_tendsto_of_lt h0a with
        ⟨u, _, hu_mem, hu_tendsto⟩
      choose indices hind using fun j ↦ (hu_mem j).2
      have hprobe (j : ℕ) : leftCodeCondition lam q (indices j) p := by
        apply (leftCodeCondition_iff_of_excursion p lam hab hq (indices j)).2
        rw [hind]
        exact (hu_mem j).1.2.le
      have hseq_le : (⨆ j : ℕ, (u j : ENNReal)) ≤
          ⨆ j : ℕ, if leftCodeCondition lam q j p then
            (codeTime j : ENNReal) else 0 := by
        apply iSup_le
        intro j
        apply le_iSup_of_le (indices j)
        simpa only [hprobe j, if_true, hind j] using!
          (le_refl (u j : ENNReal))
      have hseq_eq : (⨆ j : ℕ, (u j : ENNReal)) = (a : ENNReal) := by
        apply iSup_eq_of_forall_le_of_tendsto (F := Filter.atTop)
        · intro j
          exact_mod_cast (hu_mem j).1.2.le
        · exact ENNReal.tendsto_coe.mpr hu_tendsto
      rwa [hseq_eq] at hseq_le

theorem codedRight_eq_of_excursion
    (p : BrownianPath) (lam : ℝ) {a b q : NNReal}
    (hab : excursion (centerPath p lam) lam a b)
    (hq : q ∈ Ioo a b) : codedRight lam q p = (b : ENNReal) := by
  unfold codedRight
  apply le_antisymm
  · have hdense : Dense (range codeTime) :=
      TopologicalSpace.denseRange_denseSeq NNReal
    rcases hdense.exists_seq_strictAnti_tendsto b with
      ⟨u, _, hu_mem, hu_tendsto⟩
    choose indices hind using fun j ↦ (hu_mem j).2
    have hprobe (j : ℕ) : rightCodeCondition lam q (indices j) p := by
      apply (rightCodeCondition_iff_of_excursion p lam hab hq (indices j)).2
      rw [hind]
      exact (hu_mem j).1.le
    have hfull_le : (⨅ j : ℕ, if rightCodeCondition lam q j p then
          (codeTime j : ENNReal) else ⊤) ≤
        ⨅ j : ℕ, (u j : ENNReal) := by
      apply le_iInf
      intro j
      apply iInf_le_of_le (indices j)
      simpa only [hprobe j, if_true, hind j] using!
        (le_refl (u j : ENNReal))
    have hseq_eq : (⨅ j : ℕ, (u j : ENNReal)) = (b : ENNReal) := by
      apply iInf_eq_of_forall_le_of_tendsto (F := Filter.atTop)
      · intro j
        exact_mod_cast (hu_mem j).1.le
      · exact ENNReal.tendsto_coe.mpr hu_tendsto
    rwa [hseq_eq] at hfull_le
  · apply le_iInf
    intro j
    split_ifs with hj
    · exact_mod_cast (rightCodeCondition_iff_of_excursion p lam hab hq j).mp hj
    · exact le_top

theorem sameCodedExcursion_of_mem_excursion
    (p : BrownianPath) (lam : ℝ) {a b : NNReal}
    (hab : excursion (centerPath p lam) lam a b)
    {j m : ℕ} (hj : codeTime j ∈ Ioo a b)
    (hm : codeTime m ∈ Ioo a b) :
    sameCodedExcursion lam j m p := by
  refine ⟨hab.2.2.2 (codeTime j) hj,
    hab.2.2.2 (codeTime m) hm, ?_⟩
  have hmin : a < min (codeTime j) (codeTime m) :=
    lt_min hj.1 hm.1
  have hmax : max (codeTime j) (codeTime m) < b :=
    max_lt hj.2 hm.2
  have hnonzero : reflectedIntervalInf lam
      (min (codeTime j) (codeTime m))
      (max (codeTime j) (codeTime m)) (centerPath p lam) ≠ 0 := by
    intro hz
    rcases (reflectedIntervalInf_eq_zero_iff (centerPath p lam) lam
      (min (codeTime j) (codeTime m))
      (max (codeTime j) (codeTime m))).mp hz with ⟨x, hx⟩
    change reflected (centerPath p lam) lam
      (intervalTime (min (codeTime j) (codeTime m))
        (max (codeTime j) (codeTime m)) x) = 0 at hx
    have htime : intervalTime (min (codeTime j) (codeTime m))
        (max (codeTime j) (codeTime m)) x ∈
        Icc (min (codeTime j) (codeTime m))
          (max (codeTime j) (codeTime m)) := by
      rw [← intervalTime_image (a := min (codeTime j) (codeTime m))
        (b := max (codeTime j) (codeTime m))
        (le_trans (min_le_left _ _) (le_max_left _ _))]
      exact ⟨x, mem_univ _, rfl⟩
    exact (ne_of_gt (hab.2.2.2 _
      ⟨hmin.trans_le htime.1, htime.2.trans_lt hmax⟩)) hx
  exact lt_of_le_of_ne
    (reflectedIntervalInf_nonneg (centerPath p lam) lam _ _) (Ne.symm hnonzero)

theorem retainedCode_of_first_probe
    (p : BrownianPath) (lam : ℝ) {a b : NNReal}
    (hab : excursion (centerPath p lam) lam a b) :
    ∃ m, retainedCode lam m p ∧ codeTime m ∈ Ioo a b := by
  have hdense : Dense (range codeTime) :=
    TopologicalSpace.denseRange_denseSeq NNReal
  rcases hdense.exists_between hab.1 with ⟨q, ⟨m, hm⟩, hq⟩
  have hex : ∃ m, codeTime m ∈ Ioo a b := ⟨m, by rwa [hm]⟩
  let first := Nat.find hex
  have hfirst : codeTime first ∈ Ioo a b := Nat.find_spec hex
  refine ⟨first, ⟨hab.2.2.2 _ hfirst, ?_⟩, hfirst⟩
  intro j hj hsame
  apply Nat.find_min hex hj
  have hja : a < codeTime j := by
    by_contra h
    have hja : codeTime j ≤ a := le_of_not_gt h
    have hzero := (leftCodeCondition_iff_of_excursion p lam hab hfirst j).2 hja
    have hmin : min (codeTime j) (codeTime first) = codeTime j :=
      min_eq_left (hja.trans hfirst.1.le)
    have hmax : max (codeTime j) (codeTime first) = codeTime first :=
      max_eq_right (hja.trans hfirst.1.le)
    exact (ne_of_gt hsame.2.2) (by simpa [hmin, hmax] using! hzero.2)
  have hjb : codeTime j < b := by
    by_contra h
    have hjb : b ≤ codeTime j := le_of_not_gt h
    have hzero := (rightCodeCondition_iff_of_excursion p lam hab hfirst j).2 hjb
    have hmin : min (codeTime j) (codeTime first) = codeTime first :=
      min_eq_right (hfirst.2.le.trans hjb)
    have hmax : max (codeTime j) (codeTime first) = codeTime j :=
      max_eq_left (hfirst.2.le.trans hjb)
    exact (ne_of_gt hsame.2.2) (by simpa [hmin, hmax] using! hzero.2)
  exact ⟨hja, hjb⟩

theorem codedLength_eq_of_excursion
    (p : BrownianPath) (lam : ℝ) {a b : NNReal}
    (hab : excursion (centerPath p lam) lam a b)
    {m : ℕ} (hm : retainedCode lam m p)
    (hq : codeTime m ∈ Ioo a b) :
    codedLength lam m p = ENNReal.ofReal ((b : ℝ) - (a : ℝ)) := by
  have hleft := codedLeft_eq_of_excursion p lam hab hq
  have hright := codedRight_eq_of_excursion p lam hab hq
  unfold codedLength
  rw [if_pos ⟨hm, by rw [hright]; exact ENNReal.coe_lt_top⟩]
  rw [hleft, hright]
  calc
    (b : ENNReal) - (a : ENNReal) = (b - a : NNReal) :=
      ENNReal.coe_sub.symm
    _ = ENNReal.ofReal ((b : ℝ) - (a : ℝ)) := by
      rw [← NNReal.coe_sub hab.1.le, ENNReal.ofReal_coe_nnreal]

theorem retainedCode_unique_in_excursion
    (p : BrownianPath) (lam : ℝ) {a b : NNReal}
    (hab : excursion (centerPath p lam) lam a b)
    {j m : ℕ} (hj : retainedCode lam j p)
    (hm : retainedCode lam m p)
    (hjq : codeTime j ∈ Ioo a b)
    (hmq : codeTime m ∈ Ioo a b) : j = m := by
  rcases lt_trichotomy j m with hlt | heq | hgt
  · exact (hm.2 j hlt
      (sameCodedExcursion_of_mem_excursion p lam hab hjq hmq)).elim
  · exact heq
  · exact (hj.2 m hgt
      (sameCodedExcursion_of_mem_excursion p lam hab hmq hjq)).elim

theorem retainedCode_represents_excursion
    (p : BrownianPath) (lam : ℝ) {a b : NNReal}
    (hab : excursion (centerPath p lam) lam a b) :
    ∃! m : ℕ, retainedCode lam m p ∧ codeTime m ∈ Ioo a b ∧
      codedLeft lam (codeTime m) p = (a : ENNReal) ∧
      codedRight lam (codeTime m) p = (b : ENNReal) ∧
      codedLength lam m p = ENNReal.ofReal ((b : ℝ) - (a : ℝ)) := by
  rcases retainedCode_of_first_probe p lam hab with ⟨m, hm, hmq⟩
  refine ⟨m, ⟨hm, hmq, codedLeft_eq_of_excursion p lam hab hmq,
    codedRight_eq_of_excursion p lam hab hmq,
    codedLength_eq_of_excursion p lam hab hm hmq⟩, ?_⟩
  intro j hj
  exact retainedCode_unique_in_excursion p lam hab hj.1 hm hj.2.1 hmq

end

end Erdos745.WrapUp.Proofs.Internal.W15_CRITICAL_Code


namespace Erdos745.WrapUp.Proofs.Internal.W15_CRITICAL_CodeComplete

open Erdos745.WrapUp
open Erdos745.WrapUp.Proofs.Internal.W13_BROWNIAN_Hitting
open Erdos745.WrapUp.Proofs.Internal.W13_BROWNIAN_Geometry
open Erdos745.WrapUp.Proofs.Internal.W15_CRITICAL_Truncated
open Erdos745.WrapUp.Proofs.Internal.W15_CRITICAL_Code
open Set Filter
open scoped ENNReal Topology

noncomputable section
attribute [local instance] Classical.propDecidable

def codedExcursionPair (lam : ℝ) (m : ℕ) (p : BrownianPath) :
    NNReal × NNReal :=
  ((codedLeft lam (codeTime m) p).toNNReal,
    (codedRight lam (codeTime m) p).toNNReal)

theorem retainedCode_excursion_of_escape
    (p : BrownianPath) (lam : ℝ)
    (hescape : Tendsto (drift (centerPath p lam) lam) atTop atBot)
    {m : ℕ} (hm : retainedCode lam m p) :
    excursion (centerPath p lam) lam
      (codedExcursionPair lam m p).1 (codedExcursionPair lam m p).2 ∧
    codeTime m ∈ Ioo (codedExcursionPair lam m p).1
      (codedExcursionPair lam m p).2 ∧
    codedLength lam m p = ENNReal.ofReal
      (((codedExcursionPair lam m p).2 : ℝ) -
        ((codedExcursionPair lam m p).1 : ℝ)) := by
  have hfuture : ∀ q : NNReal, ∃ t : NNReal,
      q < t ∧ reflected (centerPath p lam) lam t = 0 :=
    exists_future_reflected_zero_of_escape (centerPath p lam) lam hescape
  obtain ⟨a, b, hab, haq, hqb⟩ :=
    exists_excursion_containing_of_positive (centerPath p lam) lam
      hfuture hm.1
  obtain ⟨r, hr, hunique⟩ := retainedCode_represents_excursion p lam hab
  have hmr : m = r :=
    retainedCode_unique_in_excursion p lam hab hm hr.1 ⟨haq, hqb⟩ hr.2.1
  subst r
  have hpair : codedExcursionPair lam m p = (a, b) := by
    simp [codedExcursionPair, hr.2.2.1, hr.2.2.2.1]
  rw [hpair]
  exact ⟨hab, ⟨haq, hqb⟩, hr.2.2.2.2⟩

theorem retainedCode_pair_injective
    (p : BrownianPath) (lam : ℝ)
    (hescape : Tendsto (drift (centerPath p lam) lam) atTop atBot)
    {j m : ℕ} (hj : retainedCode lam j p) (hm : retainedCode lam m p)
    (hpair : codedExcursionPair lam j p = codedExcursionPair lam m p) :
    j = m := by
  obtain ⟨hja, hjq, _⟩ := retainedCode_excursion_of_escape p lam hescape hj
  obtain ⟨_, hmq, _⟩ := retainedCode_excursion_of_escape p lam hescape hm
  rw [← hpair] at hmq
  exact retainedCode_unique_in_excursion p lam hja hj hm hjq hmq

theorem codedLength_eq_zero_of_not_retained
    (p : BrownianPath) (lam : ℝ) {m : ℕ}
    (hm : ¬ retainedCode lam m p) : codedLength lam m p = 0 := by
  simp [codedLength, hm]

theorem limitKeptLength_eq_of_excursion
    (p : BrownianPath) (lam cutoff T U : ℝ) {a b : NNReal}
    (hab : excursion (centerPath p lam) lam a b)
    {m : ℕ} (hm : retainedCode lam m p)
    (hq : codeTime m ∈ Ioo a b) :
    limitKeptLength lam cutoff T U m p =
      if cutoff < (b : ℝ) - (a : ℝ) ∧ (a : ℝ) < T ∧ (b : ℝ) < U then
        ENNReal.ofReal ((b : ℝ) - (a : ℝ)) else 0 := by
  have hleft := codedLeft_eq_of_excursion p lam hab hq
  have hright := codedRight_eq_of_excursion p lam hab hq
  have hlength := codedLength_eq_of_excursion p lam hab hm hq
  simp only [limitKeptLength, hleft, hright, hlength]
  rw [ENNReal.toReal_ofReal (sub_nonneg.mpr (mod_cast hab.1.le))]
  simp

theorem rankFromCodedLength_eq_excursionRankExtended
    (p : BrownianPath) (lam : ℝ)
    (hescape : Tendsto (drift (centerPath p lam) lam) atTop atBot)
    (i : ℕ) :
    rankFromCandidates (codedLength lam) i p =
      excursionRankExtended (centerPath p lam) lam i := by
  classical
  by_cases hi : i = 0
  · simp [rankFromCandidates, excursionRankExtended, hi]
  · rw [show rankFromCandidates (codedLength lam) i p =
        ⨆ f : Fin i → ℕ,
          if Function.Injective f then ⨅ j : Fin i, codedLength lam (f j) p else 0 by
      unfold rankFromCandidates
      rw [if_neg hi],
      show excursionRankExtended (centerPath p lam) lam i =
        sSup {r : ENNReal |
          ∃ e : Fin i → NNReal × NNReal, Function.Injective e ∧
            ∀ j, excursion (centerPath p lam) lam (e j).1 (e j).2 ∧
              r ≤ ENNReal.ofReal (((e j).2 : ℝ) - ((e j).1 : ℝ))} by
      rw [excursionRankExtended, if_neg hi]]
    apply le_antisymm
    · apply iSup_le
      intro f
      by_cases hf : Function.Injective f
      · rw [if_pos hf]
        by_cases hall : ∀ j : Fin i, retainedCode lam (f j) p
        · let e : Fin i → NNReal × NNReal :=
            fun j ↦ codedExcursionPair lam (f j) p
          have he_injective : Function.Injective e := by
            intro j k hjk
            apply hf
            exact retainedCode_pair_injective p lam hescape (hall j) (hall k) hjk
          apply le_sSup
          refine ⟨e, he_injective, ?_⟩
          intro j
          obtain ⟨hex, _, hlength⟩ :=
            retainedCode_excursion_of_escape p lam hescape (hall j)
          refine ⟨hex, ?_⟩
          calc
            (⨅ k : Fin i, codedLength lam (f k) p) ≤
                codedLength lam (f j) p := iInf_le _ j
            _ = ENNReal.ofReal (((e j).2 : ℝ) - ((e j).1 : ℝ)) := hlength
        · push_neg at hall
          obtain ⟨j, hj⟩ := hall
          calc
            (⨅ k : Fin i, codedLength lam (f k) p) ≤
                codedLength lam (f j) p := iInf_le _ j
            _ = 0 := codedLength_eq_zero_of_not_retained p lam hj
            _ ≤ sSup {r : ENNReal |
              ∃ e : Fin i → NNReal × NNReal, Function.Injective e ∧
                ∀ j, excursion (centerPath p lam) lam (e j).1 (e j).2 ∧
                  r ≤ ENNReal.ofReal (((e j).2 : ℝ) - ((e j).1 : ℝ))} := bot_le
      · rw [if_neg hf]
        exact bot_le
    · apply sSup_le
      intro r hr
      obtain ⟨e, he_injective, he⟩ := hr
      choose f hf using fun j ↦
        (retainedCode_represents_excursion p lam (he j).1).exists
      have heq (j : Fin i) : e j = codedExcursionPair lam (f j) p := by
        obtain ⟨_, _, hleft, hright, _⟩ := hf j
        exact Prod.ext (by simp [codedExcursionPair, hleft])
          (by simp [codedExcursionPair, hright])
      have hf_injective : Function.Injective f := by
        intro j k hjk
        apply he_injective
        calc
          e j = codedExcursionPair lam (f j) p := heq j
          _ = codedExcursionPair lam (f k) p := by rw [hjk]
          _ = e k := (heq k).symm
      apply le_trans _ (le_iSup (fun f : Fin i → ℕ ↦
        if Function.Injective f then
          ⨅ j : Fin i, codedLength lam (f j) p else 0) f)
      rw [if_pos hf_injective]
      apply le_iInf
      intro j
      rw [(hf j).2.2.2.2]
      exact (he j).2

theorem rankFromCodedLength_toReal_eq_excursionRank
    (p : BrownianPath) (lam : ℝ)
    (hescape : Tendsto (drift (centerPath p lam) lam) atTop atBot)
    (i : ℕ) :
    (rankFromCandidates (codedLength lam) i p).toReal =
      excursionRank (centerPath p lam) lam i := by
  exact congrArg ENNReal.toReal
    (rankFromCodedLength_eq_excursionRankExtended p lam hescape i)

end

end Erdos745.WrapUp.Proofs.Internal.W15_CRITICAL_CodeComplete
