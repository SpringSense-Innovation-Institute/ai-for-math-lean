module

public import Erdos745.WrapUp.Proofs.Internal.Linked.W13_Law

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local simp] Pi.div_def Pi.mul_def Pi.add_def Pi.sub_def Pi.neg_def Pi.inv_def Function.comp_def Pi.pow_def Pi.smul_def Real.rpow_eq_pow

@[expose] public section


namespace Erdos745.WrapUp.Proofs.Internal.W13_BROWNIAN_LongExcursions

noncomputable section

/-- Distinct excursions are ordered by their endpoints, not just their starts. -/
theorem excursion_end_le_start_of_start_lt
    (w : BrownianPath) (lam : ℝ) {a b c d : NNReal}
    (hab : excursion w lam a b) (hcd : excursion w lam c d) (hac : a < c) :
    b ≤ c := by
  by_contra hbc
  have hcb : c < b := lt_of_not_ge hbc
  have hpositive := hab.2.2.2 c ⟨hac, hcb⟩
  exact (ne_of_gt hpositive) hcd.2.1

/-- An excursion's right endpoint is determined by its left endpoint. -/
theorem excursion_end_unique
    (w : BrownianPath) (lam : ℝ) {a b d : NNReal}
    (hab : excursion w lam a b) (had : excursion w lam a d) : b = d := by
  rcases lt_trichotomy b d with hbd | hbd | hdb
  · have hpositive := had.2.2.2 b ⟨hab.1, hbd⟩
    exact ((ne_of_gt hpositive) hab.2.2.1).elim
  · exact hbd
  · have hpositive := hab.2.2.2 d ⟨had.1, hdb⟩
    exact ((ne_of_gt hpositive) had.2.2.1).elim

/-- Long excursions have correspondingly separated starting times. -/
theorem excursion_start_separated
    (w : BrownianPath) (lam : ℝ) {a b c d : NNReal}
    (hab : excursion w lam a b) (hcd : excursion w lam c d)
    (hac : a < c) {eta : ℝ} (heta : eta ≤ (b : ℝ) - (a : ℝ)) :
    eta ≤ (c : ℝ) - (a : ℝ) := by
  have hbc := excursion_end_le_start_of_start_lt w lam hab hcd hac
  exact heta.trans (sub_le_sub_right (NNReal.coe_le_coe.mpr hbc) _)

/-- Only finitely many excursions of a given minimum length start in a
bounded interval.  No stochastic assumptions are needed for this part of the
long-excursion argument. -/
theorem finite_long_excursions_before
    (w : BrownianPath) (lam eta : ℝ) (heta : 0 < eta) (K : NNReal) :
    Set.Finite {e : NNReal × NNReal | excursion w lam e.1 e.2 ∧
      eta ≤ (e.2 : ℝ) - (e.1 : ℝ) ∧ e.1 ≤ K} := by
  let candidates : Set (NNReal × NNReal) :=
    {e | excursion w lam e.1 e.2 ∧
      eta ≤ (e.2 : ℝ) - (e.1 : ℝ) ∧ e.1 ≤ K}
  let cell : NNReal × NNReal → ℕ := fun e ↦ ⌊(e.1 : ℝ) / eta⌋₊
  have hbounded : BddAbove (cell '' candidates) := by
    refine ⟨⌊(K : ℝ) / eta⌋₊, ?_⟩
    rintro j ⟨e, he, rfl⟩
    apply Nat.floor_mono
    exact div_le_div_of_nonneg_right (NNReal.coe_le_coe.mpr he.2.2) heta.le
  have hinj : Set.InjOn cell candidates := by
    intro e he f hf heq
    have hstart : e.1 = f.1 := by
      rcases lt_trichotomy e.1 f.1 with hlt | hequal | hgt
      · have hsep := excursion_start_separated w lam he.1 hf.1 hlt he.2.1
        have hlower : (⌊(e.1 : ℝ) / eta⌋₊ : ℝ) ≤ (e.1 : ℝ) / eta :=
          Nat.floor_le (div_nonneg (NNReal.coe_nonneg _) heta.le)
        have hupper : (f.1 : ℝ) / eta < (⌊(f.1 : ℝ) / eta⌋₊ : ℝ) + 1 :=
          Nat.lt_floor_add_one _
        have hdiv : ((f.1 : ℝ) - (e.1 : ℝ)) / eta < 1 := by
          rw [sub_div]
          dsimp [cell] at heq
          rw [← heq] at hupper
          linarith
        have hgap : (f.1 : ℝ) - (e.1 : ℝ) < eta :=
          (div_lt_one heta).mp hdiv
        exact (not_lt_of_ge hsep hgap).elim
      · exact hequal
      · have hsep := excursion_start_separated w lam hf.1 he.1 hgt hf.2.1
        have hlower : (⌊(f.1 : ℝ) / eta⌋₊ : ℝ) ≤ (f.1 : ℝ) / eta :=
          Nat.floor_le (div_nonneg (NNReal.coe_nonneg _) heta.le)
        have hupper : (e.1 : ℝ) / eta < (⌊(e.1 : ℝ) / eta⌋₊ : ℝ) + 1 :=
          Nat.lt_floor_add_one _
        have hdiv : ((e.1 : ℝ) - (f.1 : ℝ)) / eta < 1 := by
          rw [sub_div]
          dsimp [cell] at heq
          rw [heq] at hupper
          linarith
        have hgap : (e.1 : ℝ) - (f.1 : ℝ) < eta :=
          (div_lt_one heta).mp hdiv
        exact (not_lt_of_ge hsep hgap).elim
    cases e with
    | mk a b =>
      cases f with
      | mk c d =>
        dsimp at hstart
        subst c
        have hend := excursion_end_unique w lam he.1 hf.1
        cases hend
        rfl
  exact (Set.Finite.of_finite_image (Set.finite_iff_bddAbove.mpr hbounded)
    hinj : candidates.Finite)

/-- The probabilistic late-tail estimate can be supplied independently of
the deterministic compact-start argument. -/
theorem finite_long_excursions_of_late_exclusion
    (w : BrownianPath) (lam : ℝ)
    (hlate : ∀ eta : ℝ, 0 < eta → ∃ K : NNReal,
      ∀ a b : NNReal, excursion w lam a b →
        eta ≤ (b : ℝ) - (a : ℝ) → a ≤ K) :
    ∀ eta : ℝ, 0 < eta →
      Set.Finite {e : NNReal × NNReal | excursion w lam e.1 e.2 ∧
        eta ≤ (e.2 : ℝ) - (e.1 : ℝ)} := by
  intro eta heta
  obtain ⟨K, hK⟩ := hlate eta heta
  exact (finite_long_excursions_before w lam eta heta K).subset (by
    intro e he
    exact ⟨he.1, he.2, hK e.1 e.2 he.1 he.2⟩)

end

end Erdos745.WrapUp.Proofs.Internal.W13_BROWNIAN_LongExcursions


namespace Erdos745.WrapUp.Proofs.Internal.W13_BROWNIAN_Geometry

noncomputable section
-- Reconcile the definitionally equal NNReal order structures used by compactness
-- and the metric topology on this pinned Mathlib version.
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local simp] Pi.div_def Pi.mul_def Pi.add_def Pi.sub_def Pi.neg_def Pi.inv_def Function.comp_def
open Filter MeasureTheory
open W13_BROWNIAN_Ranks W13_BROWNIAN_Hitting W13_BROWNIAN_LongExcursions

private theorem continuous_drift (w : BrownianPath) (lam : ℝ) :
    Continuous (drift w lam) := by
  unfold drift
  fun_prop

private theorem continuous_reflected (w : BrownianPath) (lam : ℝ) :
    Continuous (reflected w lam) := by
  exact (continuous_reflected_joint lam).comp
    (continuous_const.prodMk continuous_id)

private theorem compact_drift_image (w : BrownianPath) (lam : ℝ) (t : NNReal) :
    IsCompact ((drift w lam) '' Set.Icc 0 t) :=
  isCompact_Icc.image (continuous_drift w lam)

theorem reflected_zero_origin (w : BrownianPath) (lam : ℝ) :
    reflected w lam 0 = 0 := by
  simp [reflected]

theorem drift_le_of_reflected_zero (w : BrownianPath) (lam : ℝ)
    {a t : NNReal} (ha : reflected w lam a = 0) (hta : t ≤ a) :
    drift w lam a ≤ drift w lam t := by
  have hmin : drift w lam a = sInf ((drift w lam) '' Set.Icc 0 a) := by
    simpa only [reflected, sub_eq_zero] using! ha
  rw [hmin]
  apply csInf_le (compact_drift_image w lam a).bddBelow
  exact ⟨t, ⟨zero_le, hta⟩, rfl⟩

private theorem reflected_zero_of_minimizer (w : BrownianPath) (lam : ℝ)
    {x T : NNReal} (hx : x ∈ Set.Icc 0 T)
    (hmin : IsMinOn (drift w lam) (Set.Icc 0 T) x) :
    reflected w lam x = 0 := by
  have heq : drift w lam x = sInf ((drift w lam) '' Set.Icc 0 x) := by
    apply le_antisymm
    · apply le_csInf
      · exact ⟨drift w lam x, ⟨x, ⟨zero_le, le_rfl⟩, rfl⟩⟩
      · rintro y ⟨u, ⟨hu0, hux⟩, rfl⟩
        exact hmin ⟨hu0, hux.trans hx.2⟩
    · apply csInf_le (compact_drift_image w lam x).bddBelow
      exact ⟨x, ⟨zero_le, le_rfl⟩, rfl⟩
  simp [reflected, heq]

private theorem exists_zero_between_of_drift_lt (w : BrownianPath) (lam : ℝ)
    {a t : NNReal} (ha : reflected w lam a = 0) (hat : a ≤ t)
    (hlt : drift w lam t < drift w lam a) :
    ∃ x : NNReal, a < x ∧ x ≤ t ∧ reflected w lam x = 0 := by
  obtain ⟨x, hx, hmin⟩ :=
    (isCompact_Icc : IsCompact (Set.Icc (0 : NNReal) t)).exists_isMinOn
      ⟨t, ⟨zero_le, le_rfl⟩⟩ (continuous_drift w lam).continuousOn
  have hxt : drift w lam x ≤ drift w lam t :=
    hmin ⟨zero_le, le_rfl⟩
  have hax : a < x := by
    by_contra h
    have hxa : x ≤ a := le_of_not_gt h
    have hax' := drift_le_of_reflected_zero w lam ha hxa
    linarith
  exact ⟨x, hax, hx.2, reflected_zero_of_minimizer w lam hx hmin⟩

theorem excursion_drift_start_le_interior (w : BrownianPath) (lam : ℝ)
    {a b t : NNReal} (hab : excursion w lam a b) (ht : t ∈ Set.Ioo a b) :
    drift w lam a ≤ drift w lam t := by
  by_contra h
  obtain ⟨x, hax, hxt, hxzero⟩ :=
    exists_zero_between_of_drift_lt w lam hab.2.1 ht.1.le (lt_of_not_ge h)
  exact (ne_of_gt (hab.2.2.2 x ⟨hax, hxt.trans_lt ht.2⟩)) hxzero

theorem excursion_drift_end_eq_start (w : BrownianPath) (lam : ℝ)
    {a b : NNReal} (hab : excursion w lam a b) :
    drift w lam b = drift w lam a := by
  have hba : drift w lam b ≤ drift w lam a :=
    drift_le_of_reflected_zero w lam hab.2.2.1 hab.1.le
  by_contra hne
  have hlt : drift w lam b < drift w lam a := lt_of_le_of_ne hba hne
  let y : ℝ := (drift w lam a + drift w lam b) / 2
  have hby : drift w lam b ≤ y := by dsimp [y]; linarith
  have hya : y ≤ drift w lam a := by dsimp [y]; linarith
  obtain ⟨t, ht, hty⟩ :=
    (intermediate_value_Icc' hab.1.le (continuous_drift w lam).continuousOn)
      ⟨hby, hya⟩
  have hat : a < t := lt_of_le_of_ne ht.1 (by
    intro heq
    subst t
    dsimp [y] at hty
    linarith)
  have htb : t < b := lt_of_le_of_ne ht.2 (by
    intro heq
    subst t
    dsimp [y] at hty
    linarith)
  have hbound := excursion_drift_start_le_interior w lam hab ⟨hat, htb⟩
  dsimp [y] at hty
  linarith

theorem strict_records_of_postend_descent (w : BrownianPath) (lam : ℝ)
    (hpost : ∀ a b : NNReal, excursion w lam a b → ∀ delta : NNReal,
      0 < delta → ∃ t : NNReal, b < t ∧ t < b + delta ∧
        drift w lam t < drift w lam a) :
    ∀ a b c d : NNReal, excursion w lam a b → excursion w lam c d →
      a < c → drift w lam c < drift w lam a := by
  intro a b c d hab hcd hac
  have hbc : b ≤ c := excursion_end_le_start_of_start_lt w lam hab hcd hac
  have hbc' : b < c := by
    rcases hbc.eq_or_lt with heq | hlt
    · have hdelta : 0 < d - c := tsub_pos_iff_lt.mpr hcd.1
      obtain ⟨t, hbt, htd, htdrift⟩ := hpost a b hab (d - c) hdelta
      have htcd : t ∈ Set.Ioo c d := by
        subst c
        exact ⟨hbt, by simpa only [add_tsub_cancel_of_le hcd.1.le] using! htd⟩
      have hlevel := excursion_drift_start_le_interior w lam hcd htcd
      rw [← excursion_drift_end_eq_start w lam hab] at htdrift
      rw [heq] at htdrift
      exact (not_lt_of_ge hlevel htdrift).elim
    · exact hlt
  have hdelta : 0 < c - b := tsub_pos_iff_lt.mpr hbc'
  obtain ⟨t, hbt, htc, htdrift⟩ := hpost a b hab (c - b) hdelta
  have htc' : t ≤ c :=
    (by simpa only [add_tsub_cancel_of_le hbc'.le] using! htc.le)
  exact (drift_le_of_reflected_zero w lam hcd.2.1 htc').trans_lt htdrift

private theorem closed_reflected_zero (w : BrownianPath) (lam : ℝ) :
    IsClosed {t : NNReal | reflected w lam t = 0} :=
  isClosed_eq (continuous_reflected w lam) continuous_const

theorem exists_excursion_containing_of_positive (w : BrownianPath) (lam : ℝ)
    (hfuture : ∀ q : NNReal, ∃ t : NNReal, q < t ∧ reflected w lam t = 0)
    {q : NNReal} (hq : 0 < reflected w lam q) :
    ∃ a b : NNReal, excursion w lam a b ∧ a < q ∧ q < b := by
  let Z : Set NNReal := {t | reflected w lam t = 0}
  have hZ : IsClosed Z := closed_reflected_zero w lam
  have hleftcompact : IsCompact (Set.Icc (0 : NNReal) q ∩ Z) :=
    isCompact_Icc.inter_right hZ
  have hleftne : (Set.Icc (0 : NNReal) q ∩ Z).Nonempty :=
    ⟨0, ⟨le_rfl, zero_le⟩, reflected_zero_origin w lam⟩
  obtain ⟨a, ha, hmax⟩ :=
    hleftcompact.exists_isMaxOn hleftne (continuous_id : Continuous (id : NNReal → NNReal)).continuousOn
  obtain ⟨T, hqT, hTzero⟩ := hfuture q
  have hrightcompact : IsCompact (Set.Icc q T ∩ Z) :=
    isCompact_Icc.inter_right hZ
  have hrightne : (Set.Icc q T ∩ Z).Nonempty :=
    ⟨T, ⟨hqT.le, le_rfl⟩, hTzero⟩
  obtain ⟨b, hb, hmin⟩ :=
    hrightcompact.exists_isMinOn hrightne (continuous_id : Continuous (id : NNReal → NNReal)).continuousOn
  have haq : a < q := lt_of_le_of_ne ha.1.2 (by
    intro heq
    subst a
    exact (ne_of_gt hq) ha.2)
  have hqb : q < b := lt_of_le_of_ne hb.1.1 (by
    intro heq
    subst b
    exact (ne_of_gt hq) hb.2)
  refine ⟨a, b, ⟨haq.trans hqb, ha.2, hb.2, ?_⟩, haq, hqb⟩
  intro t ht
  have htne : reflected w lam t ≠ 0 := by
    intro hzero
    by_cases htq : t ≤ q
    · have hat : t ≤ a := hmax ⟨⟨zero_le, htq⟩, hzero⟩
      exact (not_lt_of_ge hat) ht.1
    · have hqt : q ≤ t := le_of_not_ge htq
      have hbt : b ≤ t := hmin ⟨⟨hqt, ht.2.le.trans hb.1.2⟩, hzero⟩
      exact (not_lt_of_ge hbt) ht.2
  exact lt_of_le_of_ne (reflected_nonneg w lam t) (Ne.symm htne)

theorem exists_positive_reflected_after_of_zeroOccupation
    (w : BrownianPath) (lam : ℝ)
    (hzero : ∀ T : ℝ, 0 < T →
      volume {t : ℝ | 0 ≤ t ∧ t ≤ T ∧ reflected w lam t.toNNReal = 0} = 0)
    (K : NNReal) :
    ∃ q : NNReal, K < q ∧ q < K + 1 ∧ 0 < reflected w lam q := by
  by_contra hnone
  have hsub : Set.Ioo (K : ℝ) ((K : ℝ) + 1) ⊆
      {t : ℝ | 0 ≤ t ∧ t ≤ (K : ℝ) + 1 ∧
        reflected w lam t.toNNReal = 0} := by
    intro t ht
    have ht0 : 0 ≤ t := K.property.trans ht.1.le
    have hKq : K < t.toNNReal := NNReal.coe_lt_coe.mp (by
      simpa only [Real.coe_toNNReal t ht0] using! ht.1)
    have hqK : t.toNNReal < K + 1 := NNReal.coe_lt_coe.mp (by
      simpa only [Real.coe_toNNReal t ht0, NNReal.coe_add, NNReal.coe_one] using! ht.2)
    have hnpos : ¬0 < reflected w lam t.toNNReal := by
      intro hpos
      exact hnone ⟨t.toNNReal, hKq, hqK, hpos⟩
    exact ⟨ht0, ht.2.le, le_antisymm (le_of_not_gt hnpos)
      (reflected_nonneg w lam t.toNNReal)⟩
  have hnull := measure_mono_null hsub (hzero ((K : ℝ) + 1) (by positivity))
  rw [Real.volume_Ioo] at hnull
  have hpos : 0 < ((K : ℝ) + 1) - (K : ℝ) := by linarith
  exact (ne_of_gt (ENNReal.ofReal_pos.mpr hpos)) hnull

/-- Every bound is exceeded by a finite excursion endpoint. -/
theorem exists_excursion_end_gt_of_escape_zeroOccupation
    (w : BrownianPath) (lam : ℝ)
    (hescape : Tendsto (drift w lam) atTop atBot)
    (hzero : ∀ T : ℝ, 0 < T →
      volume {t : ℝ | 0 ≤ t ∧ t ≤ T ∧ reflected w lam t.toNNReal = 0} = 0)
    (K : NNReal) :
    ∃ a b : NNReal, excursion w lam a b ∧ K < b := by
  obtain ⟨q, hKq, _, hq⟩ :=
    exists_positive_reflected_after_of_zeroOccupation w lam hzero K
  obtain ⟨a, b, hab, _, hqb⟩ := exists_excursion_containing_of_positive w lam
    (exists_future_reflected_zero_of_escape w lam hescape) hq
  exact ⟨a, b, hab, hKq.trans hqb⟩

/-- Escape and zero occupation imply the infinitude clause of the public
good-path predicate without any immediate-oscillation premise. -/
theorem infinite_excursions_of_escape_zeroOccupation
    (w : BrownianPath) (lam : ℝ)
    (hescape : Tendsto (drift w lam) atTop atBot)
    (hzero : ∀ T : ℝ, 0 < T →
      volume {t : ℝ | 0 ≤ t ∧ t ≤ T ∧ reflected w lam t.toNNReal = 0} = 0) :
    Set.Infinite {e : NNReal × NNReal | excursion w lam e.1 e.2} := by
  intro hfinite
  obtain ⟨K, hK⟩ := (hfinite.image Prod.snd).bddAbove
  obtain ⟨a, b, hab, hKb⟩ :=
    exists_excursion_end_gt_of_escape_zeroOccupation w lam hescape hzero K
  exact (not_lt_of_ge (hK ⟨(a, b), hab, rfl⟩)) hKb

/-- Deterministic assembly: strict records and infinitude are consequences,
so they need no separate stochastic premises. -/
theorem goodExcursionPath_of_escape_zeroOccupation_postend_late
    (w : BrownianPath) (lam : ℝ)
    (hescape : Tendsto (drift w lam) atTop atBot)
    (hzero : ∀ T : ℝ, 0 < T →
      volume {t : ℝ | 0 ≤ t ∧ t ≤ T ∧ reflected w lam t.toNNReal = 0} = 0)
    (hpost : ∀ a b : NNReal, excursion w lam a b → ∀ delta : NNReal,
      0 < delta → ∃ t : NNReal, b < t ∧ t < b + delta ∧
        drift w lam t < drift w lam a)
    (hlate : ∀ eta : ℝ, 0 < eta → ∃ K : NNReal,
      ∀ a b : NNReal, excursion w lam a b →
        eta ≤ (b : ℝ) - (a : ℝ) → a ≤ K) :
    GoodExcursionPath w lam := by
  exact ⟨hescape, hzero, strict_records_of_postend_descent w lam hpost,
    hpost, finite_long_excursions_of_late_exclusion w lam hlate,
    infinite_excursions_of_escape_zeroOccupation w lam hescape hzero⟩

local instance : MeasurableSpace BrownianPath := borel BrownianPath
local instance : BorelSpace BrownianPath := ⟨rfl⟩

/-- Brownian regularity reduced to fixed-time nullity, post-end descent,
and late exclusion. Escape is already unconditional under BrownianLaw. -/
theorem ae_goodExcursionPath_of_fixedTime_null_postend_late
    (mu : PathLaw) (hmu : BrownianLaw mu) (lam : ℝ)
    (hfixed : ∀ t : ℝ, 0 < t →
      mu {w : BrownianPath | reflected w lam t.toNNReal = 0} = 0)
    (hpost : ∀ᵐ w ∂mu, ∀ a b : NNReal, excursion w lam a b →
      ∀ delta : NNReal, 0 < delta → ∃ t : NNReal,
        b < t ∧ t < b + delta ∧ drift w lam t < drift w lam a)
    (hlate : ∀ᵐ w ∂mu, ∀ eta : ℝ, 0 < eta → ∃ K : NNReal,
      ∀ a b : NNReal, excursion w lam a b →
        eta ≤ (b : ℝ) - (a : ℝ) → a ≤ K) :
    ∀ᵐ w ∂mu, GoodExcursionPath w lam := by
  filter_upwards [W13_BROWNIAN_Regularity.ae_drift_escape mu hmu lam,
    W13_BROWNIAN_Regularity.ae_zeroOccupation_of_fixedTime_null mu hmu.1 lam hfixed,
    hpost, hlate] with w hwescape hwzero hwpost hwlate
  exact goodExcursionPath_of_escape_zeroOccupation_postend_late w lam
    hwescape hwzero hwpost hwlate

end

end Erdos745.WrapUp.Proofs.Internal.W13_BROWNIAN_Geometry


namespace Erdos745.WrapUp.Proofs.Internal.W13_BROWNIAN_LateExcursions

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local simp] Pi.div_def Pi.mul_def Pi.add_def Pi.sub_def Pi.neg_def Pi.inv_def Function.comp_def
open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology
open W13_BROWNIAN_Law W13_BROWNIAN_Geometry W13_BROWNIAN_LongExcursions

local instance : MeasurableSpace BrownianPath := borel BrownianPath
local instance : BorelSpace BrownianPath := ⟨rfl⟩

/-- A measurable unit-block version of sublinear local increments. -/
def UnitIncrementSmall (w : BrownianPath) (eps : ℝ) : Prop :=
  ∀ᶠ j : ℕ in atTop, ∀ x : unitInterval,
    |w (unitTime j x) - w (j : NNReal)| ≤ eps * ((j : ℝ) + 1)

private theorem measurableSet_unitIncrementSmall (eps : ℝ) :
    MeasurableSet {w : BrownianPath | UnitIncrementSmall w eps} := by
  have hclosed (j : ℕ) : IsClosed {w : BrownianPath | ∀ x : unitInterval,
      |w (unitTime j x) - w (j : NNReal)| ≤ eps * ((j : ℝ) + 1)} := by
    rw [Set.setOf_forall]
    apply isClosed_iInter
    intro x
    apply isClosed_le _ continuous_const
    exact ((ContinuousEvalConst.continuous_eval_const _).sub
      (ContinuousEvalConst.continuous_eval_const _)).abs
  simp only [UnitIncrementSmall, eventually_atTop, Set.setOf_exists, Set.setOf_forall]
  apply MeasurableSet.iUnion
  intro N
  apply MeasurableSet.iInter
  intro j
  apply MeasurableSet.iInter
  intro _hj
  simpa only [Set.setOf_forall] using! (hclosed j).measurableSet

/-- Every Brownian law has arbitrarily small linear bounds for its late
unit-interval increments.  Uniqueness transfers the concrete source estimate. -/
theorem ae_unitIncrementSmall (mu : PathLaw) (hmu : BrownianLaw mu)
    (eps : ℝ) (heps : 0 < eps) : ∀ᵐ w ∂mu, UnitIncrementSmall w eps := by
  rw [brownianLaw_unique mu brownianCandidate hmu brownianCandidate_brownianLaw]
  rw [brownianCandidate, ae_map_iff aeMeasurable_globalPath
    (measurableSet_unitIncrementSmall eps)]
  exact ae_globalPath_unitIncrement_small eps heps

/-- The countable reciprocal cutoffs give all positive cutoffs on a single
full-measure set, without any uncountable intersection. -/
theorem ae_all_unitIncrementSmall (mu : PathLaw) (hmu : BrownianLaw mu) :
    ∀ᵐ w ∂mu, ∀ eps : ℝ, 0 < eps → UnitIncrementSmall w eps := by
  have hcount : ∀ᵐ w ∂mu, ∀ n : ℕ, UnitIncrementSmall w (1 / ((n : ℝ) + 1)) := by
    rw [ae_all_iff]
    intro n
    exact ae_unitIncrementSmall mu hmu _ (by positivity)
  filter_upwards [hcount] with w hw
  intro eps heps
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt heps
  filter_upwards [hw n] with j hj
  intro x
  exact (hj x).trans (mul_le_mul_of_nonneg_right hn.le (by positivity))

private theorem unit_bound_on_Icc (w : BrownianPath) (eps : ℝ) (j : ℕ)
    (h : ∀ x : unitInterval,
      |w (unitTime j x) - w (j : NNReal)| ≤ eps * ((j : ℝ) + 1))
    (t : NNReal) (ht : (j : NNReal) ≤ t ∧ t ≤ (j : NNReal) + 1) :
    |w t - w (j : NNReal)| ≤ eps * ((j : ℝ) + 1) := by
  have ht0 : (j : ℝ) ≤ t := by exact_mod_cast ht.1
  have ht1 : (t : ℝ) ≤ (j : ℝ) + 1 := by exact_mod_cast ht.2
  let x : unitInterval := ⟨(t : ℝ) - j, by constructor <;> linarith⟩
  have heq : unitTime j x = t := by ext; simp [unitTime, x]
  simpa only [heq] using! h x

private theorem short_increment_bound (w : BrownianPath) (eps : ℝ)
    (heps : 0 ≤ eps) {N : ℕ}
    (h : ∀ j ≥ N, ∀ x : unitInterval,
      |w (unitTime j x) - w (j : NNReal)| ≤ eps * ((j : ℝ) + 1))
    (a u : NNReal) (hNa : (N : NNReal) ≤ a)
    (hau : a ≤ u) (hua : u ≤ a + 1) :
    |w u - w a| ≤ 3 * eps * ((a : ℝ) + 2) := by
  let j : ℕ := ⌊(a : ℝ)⌋₊
  have hjN : N ≤ j := Nat.le_floor (by exact_mod_cast hNa)
  have hja : (j : NNReal) ≤ a := by
    exact_mod_cast (Nat.floor_le a.property : (j : ℝ) ≤ a)
  have haj : a ≤ (j : NNReal) + 1 := by
    have hh := Nat.lt_floor_add_one (a : ℝ)
    change (a : ℝ) ≤ (j : ℝ) + 1
    exact hh.le
  have hju : (j : NNReal) ≤ u := hja.trans hau
  have huj : u ≤ (j : NNReal) + 1 + 1 := hua.trans (add_le_add haj le_rfl)
  have ha := unit_bound_on_Icc w eps j (h j hjN) a ⟨hja, haj⟩
  have hja' : (j : ℝ) ≤ a := by exact_mod_cast hja
  by_cases hu : u ≤ (j : NNReal) + 1
  · have hb := unit_bound_on_Icc w eps j (h j hjN) u ⟨hju, hu⟩
    calc
      |w u - w a| ≤ |w u - w (j : NNReal)| + |w a - w (j : NNReal)| :=
        by simpa only [abs_sub_comm (w (j : NNReal)) (w a)] using!
          abs_sub_le (w u) (w (j : NNReal)) (w a)
      _ ≤ eps * ((j : ℝ) + 1) + eps * ((j : ℝ) + 1) := add_le_add hb ha
      _ ≤ 3 * eps * ((a : ℝ) + 2) := by
        nlinarith [mul_nonneg heps (sub_nonneg.mpr hja'), mul_nonneg heps a.property]
  · have hub : ((j + 1 : ℕ) : NNReal) ≤ u := by
      simpa only [Nat.cast_add, Nat.cast_one] using! (le_of_not_ge hu)
    have huu : u ≤ ((j + 1 : ℕ) : NNReal) + 1 := by
      simpa only [Nat.cast_add, Nat.cast_one] using! huj
    have hb := unit_bound_on_Icc w eps (j + 1) (h (j + 1) (by omega)) u ⟨hub, huu⟩
    have hc := unit_bound_on_Icc w eps j (h j hjN) ((j + 1 : ℕ) : NNReal)
      ⟨by simp, by simp⟩
    have htriangle : |w u - w a| ≤
        |w u - w ((j + 1 : ℕ) : NNReal)| +
          |w ((j + 1 : ℕ) : NNReal) - w (j : NNReal)| +
            |w a - w (j : NNReal)| := by
      calc
        |w u - w a| ≤ |w u - w (j : NNReal)| + |w a - w (j : NNReal)| := by
          simpa only [abs_sub_comm (w (j : NNReal)) (w a)] using!
            abs_sub_le (w u) (w (j : NNReal)) (w a)
        _ ≤ _ := add_le_add (abs_sub_le (w u) (w ((j + 1 : ℕ) : NNReal))
          (w (j : NNReal))) le_rfl
    refine htriangle.trans ((add_le_add (add_le_add hb hc) ha).trans ?_)
    push_cast
    nlinarith [mul_nonneg heps (sub_nonneg.mpr hja')]

/-- Sublinear local increments force bounded starting times for every fixed
positive excursion length, because the parabolic drift has an eventually
negative slope of linear magnitude. -/
theorem late_exclusion_of_unitIncrementSmall (w : BrownianPath) (lam : ℝ)
    (hw : ∀ eps : ℝ, 0 < eps → UnitIncrementSmall w eps) :
    ∀ eta : ℝ, 0 < eta → ∃ K : NNReal,
      ∀ a b : NNReal, excursion w lam a b →
        eta ≤ (b : ℝ) - (a : ℝ) → a ≤ K := by
  intro eta heta
  let h : ℝ := min (eta / 2) (1 / 2)
  have hh : 0 < h := lt_min (by linarith) (by norm_num)
  have hheta : h < eta := (min_le_left _ _).trans_lt (by linarith)
  have hh1 : h ≤ 1 := (min_le_right _ _).trans (by norm_num)
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hw (h / 16) (by positivity))
  let K : NNReal := max (N : NNReal) ⟨4 * |lam| + 4, by positivity⟩
  refine ⟨K, ?_⟩
  intro a b hab hlen
  by_contra haK
  have hKa : K < a := lt_of_not_ge haK
  have hNa : (N : NNReal) ≤ a := (le_max_left _ _).trans hKa.le
  have halam : 4 * |lam| + 4 < (a : ℝ) := by
    have : (⟨4 * |lam| + 4, by positivity⟩ : NNReal) < a :=
      (le_max_right _ _).trans_lt hKa
    exact this
  let u : NNReal := a + ⟨h, hh.le⟩
  have hu : (u : ℝ) = (a : ℝ) + h := rfl
  have hau : a < u := by change (a : ℝ) < (a : ℝ) + h; linarith
  have hub : u < b := by change (u : ℝ) < b; rw [hu]; linarith
  have hua : u ≤ a + 1 := by change (a : ℝ) + h ≤ (a : ℝ) + 1; linarith
  have hinc := short_increment_bound w (h / 16) (by positivity) hN a u hNa hau.le hua
  have hinc' : w u - w a ≤ 3 * (h / 16) * ((a : ℝ) + 2) :=
    (le_abs_self _).trans hinc
  have hdrift := excursion_drift_start_le_interior w lam hab ⟨hau, hub⟩
  have hlarge : (a : ℝ) / 2 < (a : ℝ) - lam := by linarith [le_abs_self lam, abs_nonneg lam]
  have hmul := mul_lt_mul_of_pos_right hlarge hh
  have hsmall : 3 * (h / 16) * ((a : ℝ) + 2) < (a : ℝ) / 2 * h := by
    have ha4 : 4 < (a : ℝ) := by linarith [abs_nonneg lam]
    nlinarith [mul_pos hh (sub_pos.mpr ha4)]
  unfold drift at hdrift
  rw [hu] at hdrift
  nlinarith [sq_nonneg h]

/-- The late-exclusion premise in the public Brownian assembly, with no
additional stochastic assumptions. -/
theorem ae_late_exclusion (mu : PathLaw) (hmu : BrownianLaw mu) (lam : ℝ) :
    ∀ᵐ w ∂mu, ∀ eta : ℝ, 0 < eta → ∃ K : NNReal,
      ∀ a b : NNReal, excursion w lam a b →
        eta ≤ (b : ℝ) - (a : ℝ) → a ≤ K := by
  filter_upwards [ae_all_unitIncrementSmall mu hmu] with w hw
  exact late_exclusion_of_unitIncrementSmall w lam hw

/- In particular, only finitely many excursions have any given positive
minimum length, almost surely under every Brownian law. -/
end
end Erdos745.WrapUp.Proofs.Internal.W13_BROWNIAN_LateExcursions


/-!
A positive deterministic gap supplies an independent atomless Gaussian increment.
Consequently the drifted minima on separated compact intervals are distinct.
Countable exhaustion gives uniqueness of compact minima and descent immediately
after every excursion endpoint, without a stopping-time theorem.
-/
namespace Erdos745.WrapUp.Proofs.Internal.W13_BROWNIAN_Minima

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local simp] Pi.div_def Pi.mul_def Pi.add_def Pi.sub_def Pi.neg_def Pi.inv_def Function.comp_def
open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal Topology
open W13_BROWNIAN_Law W13_BROWNIAN_Regularity W13_BROWNIAN_Geometry

local instance : MeasurableSpace BrownianPath := borel BrownianPath
local instance : BorelSpace BrownianPath := ⟨rfl⟩

private def selectedSum {m : ℕ} (S : Finset (Fin m)) (l u : ℕ)
    (z : S → ℝ) : ℝ :=
  ∑ j : S, if l ≤ (j : Fin m).val ∧ (j : Fin m).val < u then z j else 0

private lemma measurable_selectedSum {m : ℕ} (S : Finset (Fin m)) (l u : ℕ) :
    Measurable (selectedSum S l u) := by
  classical
  unfold selectedSum
  apply Finset.measurable_sum
  intro j hj
  split_ifs <;> fun_prop

private lemma selectedSum_increments {m : ℕ} (S : Finset (Fin m))
    (l u : ℕ) (hlu : l ≤ u) (hum : u ≤ m)
    (hS : ∀ j : Fin m, l ≤ j.val → j.val < u → j ∈ S)
    (t : ℕ → NNReal) (w : BrownianPath) :
    selectedSum S l u (fun j ↦ brownianIncrementVector m t w j) =
      w (t u) - w (t l) := by
  classical
  unfold selectedSum
  rw [Finset.sum_coe_sort S (fun j : Fin m ↦
    if l ≤ j.val ∧ j.val < u then brownianIncrementVector m t w j else 0),
    ← Finset.sum_filter]
  have hfilter : S.filter (fun j ↦ l ≤ j.val ∧ j.val < u) =
      Finset.univ.filter (fun j : Fin m ↦ l ≤ j.val ∧ j.val < u) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨And.right, fun h ↦ ⟨hS j h.1 h.2, h⟩⟩
  rw [hfilter]
  calc
    _ = ∑ k ∈ Finset.Ico l u, (w (t (k + 1)) - w (t k)) := by
      apply Finset.sum_bij (fun j _ ↦ j.val)
      · intro j hj
        simpa only [Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_Ico] using! hj
      · intro i hi j hj hij
        exact Fin.ext hij
      · intro k hk
        have hk' := Finset.mem_Ico.mp hk
        refine ⟨⟨k, hk'.2.trans_le hum⟩, ?_, rfl⟩
        simpa using! hk'
      · intro j hj
        rfl
    _ = w (t u) - w (t l) := by
      rw [Finset.sum_Ico_eq_sub _ hlu, Finset.sum_range_sub (fun k ↦ w (t k)) u,
        Finset.sum_range_sub (fun k ↦ w (t k)) l]
      ring

/-- A gap increment is independent of any finite family of forward increments
whose intervals lie entirely before or entirely after the gap. -/
theorem indepFun_gap_finite_increments
    (mu : PathLaw) (hmu : BrownianLaw mu) (q r : NNReal) (hqr : q < r)
    {ι : Type*} [Fintype ι] (a b : ι → NNReal)
    (hab : ∀ i, a i ≤ b i) (hout : ∀ i, b i ≤ q ∨ r ≤ a i) :
    IndepFun (fun w : BrownianPath ↦ w r - w q)
      (fun w : BrownianPath ↦ fun i ↦ w (b i) - w (a i)) mu := by
  classical
  let s : Finset NNReal := insert q (insert r
    ((Finset.univ.image a) ∪ (Finset.univ.image b)))
  have hq : q ∈ s := by simp [s]
  have hr : r ∈ s := by simp [s]
  have ha (i : ι) : a i ∈ s := by simp [s]
  have hb (i : ι) : b i ∈ s := by simp [s]
  let m := s.card - 1
  have hs : s.card = m + 1 := by
    have := Finset.card_pos.mpr ⟨q, hq⟩
    omega
  let e : Fin (m + 1) ≃o s := s.orderIsoOfFin hs
  let idx : s → Fin (m + 1) := e.symm
  let t : ℕ → NNReal := fun n ↦ if hn : n < m + 1 then (e ⟨n, hn⟩).val else 0
  have ht : ∀ j < m, t j < t (j + 1) := by
    intro j hj
    have h0 : j < m + 1 := by omega
    have h1 : j + 1 < m + 1 := by omega
    simp only [t, dif_pos h0, dif_pos h1]
    exact e.lt_iff_lt.mpr (by simp)
  have htime (x : s) : t (idx x) = x.val := by
    dsimp only [t]
    rw [dif_pos (idx x).isLt]
    exact congrArg Subtype.val (e.apply_symm_apply x)
  have horder {x y : s} (h : x.val ≤ y.val) :
      (idx x).val ≤ (idx y).val := e.symm.monotone h
  let Q := idx ⟨q, hq⟩
  let R := idx ⟨r, hr⟩
  let A (i : ι) := idx ⟨a i, ha i⟩
  let B (i : ι) := idx ⟨b i, hb i⟩
  have hQR : Q.val ≤ R.val := horder hqr.le
  have hAB (i : ι) : (A i).val ≤ (B i).val := horder (hab i)
  have hQBRA (i : ι) : (B i).val ≤ Q.val ∨ R.val ≤ (A i).val :=
    (hout i).imp horder horder
  let S : Finset (Fin m) := Finset.univ.filter
    (fun j ↦ Q.val ≤ j.val ∧ j.val < R.val)
  let U : Finset (Fin m) := Sᶜ
  have hSU : Disjoint S U := by
    apply Finset.disjoint_left.mpr
    intro j hj
    simpa [U] using! hj
  have hind := indepFun_brownianIncrementGroups mu hmu m t ht S U hSU
  let f : (S → ℝ) → ℝ := selectedSum S Q.val R.val
  let g : (U → ℝ) → ι → ℝ := fun z i ↦ selectedSum U (A i).val (B i).val z
  have hf : Measurable f := measurable_selectedSum _ _ _
  have hg : Measurable g := Measurable.of_eval fun i ↦ measurable_selectedSum _ _ _
  have heqf (w : BrownianPath) :
      f (fun j ↦ brownianIncrementVector m t w j) = w r - w q := by
    dsimp [f]
    rw [selectedSum_increments S _ _ hQR (by have := R.isLt; omega)]
    · simp [Q, R, htime]
    · intro j hj0 hj1
      simp [S, hj0, hj1]
  have heqg (w : BrownianPath) :
      g (fun j ↦ brownianIncrementVector m t w j) =
        fun i ↦ w (b i) - w (a i) := by
    funext i
    dsimp [g]
    rw [selectedSum_increments U _ _ (hAB i) (by have := (B i).isLt; omega)]
    · simp [A, B, htime]
    · intro j hj0 hj1
      simp only [U, Finset.mem_compl, S, Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hQBRA i with hi | hi <;> omega
  exact (hind.comp hf hg).congr
    (Eventually.of_forall heqf) (Eventually.of_forall heqg)

/-- The finite increment factorization extends to the full outside process. -/
theorem indepFun_gap_increments
    (mu : PathLaw) (hmu : BrownianLaw mu) (q r : NNReal) (hqr : q < r)
    {ι : Type*} (a b : ι → NNReal)
    (hab : ∀ i, a i ≤ b i) (hout : ∀ i, b i ≤ q ∨ r ≤ a i) :
    IndepFun (fun w : BrownianPath ↦ w r - w q)
      (fun w : BrownianPath ↦ fun i ↦ w (b i) - w (a i)) mu := by
  letI : IsProbabilityMeasure mu := hmu.1
  have hm (u v : NNReal) : Measurable (fun w : BrownianPath ↦ w v - w u) :=
    (ContinuousEvalConst.continuous_eval_const v).measurable.sub
      (ContinuousEvalConst.continuous_eval_const u).measurable
  apply IndepFun.indepFun_process (hm q r) (fun i ↦ hm (a i) (b i))
  intro I
  exact indepFun_gap_finite_increments mu hmu q r hqr
    (fun i : I ↦ a i) (fun i : I ↦ b i) (fun i ↦ hab i) (fun i ↦ hout i)

private lemma gap_law (mu : PathLaw) (hmu : BrownianLaw mu)
    (q r : NNReal) (hqr : q < r) :
    mu.map (fun w : BrownianPath ↦ w r - w q) =
      gaussianReal 0 ((r : ℝ) - (q : ℝ)).toNNReal := by
  let t : ℕ → NNReal := fun n ↦ if n = 0 then q else r
  have ht : ∀ j < 1, t j < t (j + 1) := by
    intro j hj
    have : j = 0 := by omega
    subst j
    simpa [t] using! hqr
  simpa [brownianIncrementVector, t] using!
    brownianIncrementCoordinate_law mu hmu 1 t ht (0 : Fin 1)

private lemma ae_ne_of_indep_noAtoms {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) [IsProbabilityMeasure mu] {X Y : Ω → ℝ}
    (hX : Measurable X) (hY : Measurable Y) (h : IndepFun X Y mu)
    [NullSingletonClass (mu.map X)] : ∀ᵐ w ∂mu, X w ≠ Y w := by
  have hp : ∀ᵐ p ∂(mu.map Y).prod (mu.map X), p.2 ≠ p.1 := by
    apply (Measure.ae_prod_iff_ae_ae
      (measurableSet_eq_fun measurable_snd measurable_fst).compl).2
    exact Eventually.of_forall fun y ↦ (mu.map X).ae_ne y
  have hm := (indepFun_iff_map_prod_eq_prod_map_map hY.aemeasurable hX.aemeasurable).1 h.symm
  rw [← hm] at hp
  exact (ae_map_iff (hY.prodMk hX).aemeasurable
    (measurableSet_eq_fun measurable_snd measurable_fst).compl).1 hp

private lemma denseInf_eq_min {K : Type*} [TopologicalSpace K]
    [CompactSpace K] [TopologicalSpace.SeparableSpace K] [Nonempty K]
    (f : K → ℝ) (hf : Continuous f) (x : K) (hx : ∀ y, f x ≤ f y) :
    (⨅ n : ℕ, f (TopologicalSpace.denseSeq K n)) = f x := by
  have hb : BddBelow (Set.range (fun n : ℕ ↦ f (TopologicalSpace.denseSeq K n))) :=
    (isCompact_range hf).bddBelow.mono (Set.range_comp_subset_range _ _)
  apply le_antisymm
  · exact (TopologicalSpace.denseRange_denseSeq K).induction_on x
      (isClosed_le continuous_const hf) (fun n ↦ ciInf_le hb n)
  · exact le_ciInf fun n ↦ hx _

private lemma continuous_drift (w : BrownianPath) (lam : ℝ) :
    Continuous (drift w lam) := by unfold drift; fun_prop

/-- Minima on compact intervals separated by a positive gap have different
values, almost surely. The conclusion includes every minimizer in each interval. -/
theorem ae_separated_minima
    (mu : PathLaw) (hmu : BrownianLaw mu) (lam : ℝ)
    (q r T : NNReal) (hqr : q < r) (hrT : r ≤ T) :
    ∀ᵐ w ∂mu, ∀ a ∈ Set.Icc 0 q, ∀ b ∈ Set.Icc r T,
      IsMinOn (drift w lam) (Set.Icc 0 q) a →
      IsMinOn (drift w lam) (Set.Icc r T) b →
      drift w lam a ≠ drift w lam b := by
  letI : IsProbabilityMeasure mu := hmu.1
  let L := Set.Icc (0 : NNReal) q
  let R := Set.Icc r T
  letI : Nonempty L := ⟨⟨0, by simp [L]⟩⟩
  letI : Nonempty R := ⟨⟨r, by simp [R, hrT]⟩⟩
  let l (n : ℕ) : NNReal := (TopologicalSpace.denseSeq L n).val
  let u (n : ℕ) : NNReal := (TopologicalSpace.denseSeq R n).val
  have hl (n : ℕ) : l n ≤ q := (TopologicalSpace.denseSeq L n).property.2
  have hu (n : ℕ) : r ≤ u n := (TopologicalSpace.denseSeq R n).property.1
  let a : ℕ ⊕ ℕ → NNReal := Sum.elim l (fun _ ↦ r)
  let b : ℕ ⊕ ℕ → NNReal := Sum.elim (fun _ ↦ q) u
  let outside (w : BrownianPath) (i : ℕ ⊕ ℕ) := w (b i) - w (a i)
  have hind := indepFun_gap_increments mu hmu q r hqr a b
    (by intro i; cases i with | inl n => exact hl n | inr n => exact hu n)
    (by intro i; cases i with | inl n => exact Or.inl le_rfl | inr n => exact Or.inr le_rfl)
  let d (t : NNReal) : ℝ := lam * (t : ℝ) - (t : ℝ) ^ 2 / 2
  let F (z : (ℕ ⊕ ℕ) → ℝ) : ℝ :=
    (⨅ n : ℕ, -z (.inl n) + d (l n)) - (⨅ n : ℕ, z (.inr n) + d (u n))
  have hF : Measurable F := by
    exact (Measurable.iInf fun n ↦ (measurable_pi_apply (Sum.inl n : ℕ ⊕ ℕ)).neg.add measurable_const).sub
      (Measurable.iInf fun n ↦ (measurable_pi_apply (Sum.inr n : ℕ ⊕ ℕ)).add measurable_const)
  have houtside : Measurable outside := by
    apply measurable_pi_lambda
    intro i
    exact (ContinuousEvalConst.continuous_eval_const (b i)).measurable.sub
      (ContinuousEvalConst.continuous_eval_const (a i)).measurable
  have hgap : Measurable (fun w : BrownianPath ↦ w r - w q) :=
    (ContinuousEvalConst.continuous_eval_const r).measurable.sub
      (ContinuousEvalConst.continuous_eval_const q).measurable
  have hv : ((r : ℝ) - (q : ℝ)).toNNReal ≠ 0 := by
    apply ne_of_gt
    exact Real.toNNReal_pos.mpr (sub_pos.mpr (NNReal.coe_lt_coe.mpr hqr))
  letI : NullSingletonClass (mu.map (fun w : BrownianPath ↦ w r - w q)) := by
    rw [gap_law mu hmu q r hqr]
    exact nullSingletonClass_gaussianReal hv
  have hne := ae_ne_of_indep_noAtoms mu hgap (hF.comp houtside)
    (hind.comp measurable_id hF)
  filter_upwards [hne] with w hw
  intro x hx y hy hxmin hymin heq
  have hL : (⨅ n : ℕ, -(outside w (.inl n)) + d (l n)) = drift w lam x - w q := by
    convert denseInf_eq_min (fun z : L ↦ drift w lam z.val - w q)
      ((continuous_drift w lam).comp continuous_subtype_val |>.sub continuous_const)
      ⟨x, hx⟩ (fun z ↦ sub_le_sub_right (hxmin z.property) _) using 1
    congr 1
    funext n
    dsimp [outside, a, b, drift, d]
    ring
  have hR : (⨅ n : ℕ, outside w (.inr n) + d (u n)) = drift w lam y - w r := by
    convert denseInf_eq_min (fun z : R ↦ drift w lam z.val - w r)
      ((continuous_drift w lam).comp continuous_subtype_val |>.sub continuous_const)
      ⟨y, hy⟩ (fun z ↦ sub_le_sub_right (hymin z.property) _) using 1
    congr 1
    funext n
    dsimp [outside, a, b, drift, d]
    ring
  apply hw
  change w r - w q = F (outside w)
  dsimp [F]
  rw [hL, hR, heq]
  ring

/-- On any fixed compact initial interval the drifted Brownian path has a
unique minimizer, almost surely. -/
theorem ae_unique_minimizer_on_Icc
    (mu : PathLaw) (hmu : BrownianLaw mu) (lam : ℝ) (T : NNReal) :
    ∀ᵐ w ∂mu, ∀ a ∈ Set.Icc 0 T, ∀ b ∈ Set.Icc 0 T,
      IsMinOn (drift w lam) (Set.Icc 0 T) a →
      IsMinOn (drift w lam) (Set.Icc 0 T) b → a = b := by
  let v := TopologicalSpace.denseSeq NNReal
  have hd : DenseRange v := TopologicalSpace.denseRange_denseSeq NNReal
  have hsep : ∀ᵐ w ∂mu, ∀ i j : ℕ, ∀ h : v i < v j, ∀ h' : v j ≤ T,
      ∀ a ∈ Set.Icc 0 (v i), ∀ b ∈ Set.Icc (v j) T,
        IsMinOn (drift w lam) (Set.Icc 0 (v i)) a →
        IsMinOn (drift w lam) (Set.Icc (v j) T) b →
        drift w lam a ≠ drift w lam b := by
    apply ae_all_iff.mpr
    intro i
    apply ae_all_iff.mpr
    intro j
    apply ae_all_iff.mpr
    intro h
    apply ae_all_iff.mpr
    intro h'
    exact ae_separated_minima mu hmu lam _ _ T h h'
  filter_upwards [hsep] with w hw
  have hnot (a b : NNReal) (ha : a ∈ Set.Icc 0 T) (hb : b ∈ Set.Icc 0 T)
      (hminA : IsMinOn (drift w lam) (Set.Icc 0 T) a)
      (hminB : IsMinOn (drift w lam) (Set.Icc 0 T) b) : ¬a < b := by
    intro hab
    obtain ⟨i, hai, hib⟩ := hd.exists_mem_open isOpen_Ioo (Set.nonempty_Ioo.mpr hab)
    obtain ⟨j, hij, hjb⟩ := hd.exists_mem_open isOpen_Ioo (Set.nonempty_Ioo.mpr hib)
    apply hw i j hij (hjb.le.trans hb.2) a ⟨ha.1, hai.le⟩ b ⟨hjb.le, hb.2⟩
    · intro t ht
      exact hminA ⟨ht.1, ht.2.trans (hib.le.trans hb.2)⟩
    · intro t ht
      exact hminB ⟨zero_le, ht.2⟩
    · exact le_antisymm (hminA hb) (hminB ha)
  intro a ha b hb hminA hminB
  exact le_antisymm (le_of_not_gt (hnot b a hb ha hminB hminA))
    (le_of_not_gt (hnot a b ha hb hminA hminB))

/-- Every excursion endpoint is followed immediately by a strict descent below
its starting level. Only countably many deterministic compact minima are used. -/
theorem ae_postend_descent (mu : PathLaw) (hmu : BrownianLaw mu) (lam : ℝ) :
    ∀ᵐ w ∂mu, ∀ a b : NNReal, excursion w lam a b →
      ∀ delta : NNReal, 0 < delta → ∃ t : NNReal,
        b < t ∧ t < b + delta ∧ drift w lam t < drift w lam a := by
  let v := TopologicalSpace.denseSeq NNReal
  have hd : DenseRange v := TopologicalSpace.denseRange_denseSeq NNReal
  have hall := ae_all_iff.mpr (fun n : ℕ ↦ ae_unique_minimizer_on_Icc mu hmu lam (v n))
  filter_upwards [hall] with w hw
  intro a b hab delta hdelta
  by_contra hn
  push_neg at hn
  obtain ⟨n, hbn, hnend⟩ := hd.exists_mem_open isOpen_Ioo
    (Set.nonempty_Ioo.mpr (lt_add_of_pos_right b hdelta))
  have hval := excursion_drift_end_eq_start w lam hab
  have hminB : IsMinOn (drift w lam) (Set.Icc 0 (v n)) b := by
    intro t ht
    by_cases htb : t ≤ b
    · exact drift_le_of_reflected_zero w lam hab.2.2.1 htb
    · rw [hval]
      exact hn t (lt_of_not_ge htb) (ht.2.trans_lt hnend)
  have hminA : IsMinOn (drift w lam) (Set.Icc 0 (v n)) a := by
    intro t ht
    rw [← hval]
    exact hminB ht
  have heq := hw n a ⟨zero_le, hab.1.le.trans hbn.le⟩ b
    ⟨zero_le, hbn.le⟩ hminA hminB
  exact (ne_of_lt hab.1) heq

end
end Erdos745.WrapUp.Proofs.Internal.W13_BROWNIAN_Minima
