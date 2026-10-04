module

public import Erdos745.WrapUp.Proofs.Internal.Linked.W08_Analytic

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local simp] Pi.div_def Pi.mul_def Pi.add_def Pi.sub_def Pi.neg_def Pi.inv_def Function.comp_def Pi.pow_def Pi.smul_def Real.rpow_eq_pow

@[expose] public section


namespace Erdos745.WrapUp.Proofs.Internal.W08_CYCLIC_FixedMass

noncomputable section
open Filter
open scoped BigOperators Topology
open Erdos745.WrapUp.Proofs.Internal.W08_CYCLIC_Finite
open Erdos745.WrapUp.Proofs.Internal.W08_CYCLIC_Bounds
open Erdos745.WrapUp.Proofs.Internal.W04_TUPLES_Foundation

local instance : ContinuousInv₀ ℝ := IsTopologicalDivisionRing.toContinuousInv₀

def unicyclicLimitTerm (lam : ℝ) (k : ℕ) : ℝ :=
  if 3 ≤ k then (lam * Real.exp (-lam)) ^ k / 2 *
    (Finset.range (k - 2)).sum (fun m => (k : ℝ) ^ m / (m.factorial : ℝ)) else 0

lemma unicyclicLimit_eq_tsum (lam : ℝ) :
    unicyclicLimit lam = ∑' k, unicyclicLimitTerm lam k := rfl

lemma fixed_edges_div_tendsto
    {M : NatSeq} {lam : ℝ} (hdeg : Tendsto (degree M) atTop (𝓝 lam)) :
    Tendsto (fun n => (M n : ℝ) / n) atTop (𝓝 (lam / 2)) := by
  have ht : Tendsto (fun n => degree M n / 2) atTop (𝓝 (lam / 2)) := hdeg.div_const 2
  apply ht.congr'
  filter_upwards with n
  dsimp [degree]
  ring

/-- Fixed natural subtractions contribute only a vanishing error after division by n. -/
lemma fixed_complement_numerator_tendsto
    {M : NatSeq} {lam : ℝ} (hdeg : Tendsto (degree M) atTop (𝓝 lam))
    (k : ℕ) :
    Tendsto (fun n => ((M n - k + 1 : ℕ) : ℝ) / n) atTop (𝓝 (lam / 2)) := by
  have hm := fixed_edges_div_tendsto hdeg
  have hk := tendsto_const_div_atTop_nhds_zero_nat (k : ℝ)
  have h1 := tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (by simpa using! hm.sub hk) (by simpa using hm.add h1)
  · filter_upwards with n
    have hnat : M n ≤ (M n - k + 1) + k := by omega
    have hreal : (M n : ℝ) - k ≤ (M n - k + 1 : ℕ) := by
      have hc : (M n : ℝ) ≤ (M n - k + 1 : ℕ) + (k : ℝ) := by exact_mod_cast hnat
      linarith
    simpa [sub_div] using! div_le_div_of_nonneg_right hreal (Nat.cast_nonneg n)
  · filter_upwards with n
    have hreal : ((M n - k + 1 : ℕ) : ℝ) ≤ (M n : ℝ) + 1 := by
      exact_mod_cast (show M n - k + 1 ≤ M n + 1 by omega)
    simpa [add_div] using! div_le_div_of_nonneg_right hreal (Nat.cast_nonneg n)

lemma fixed_complement_capacity_tendsto (k : ℕ) :
    Tendsto (fun n : ℕ => (((n - k).choose 2 : ℕ) : ℝ) / (n : ℝ) ^ 2)
      atTop (𝓝 (1 / 2)) := by
  have hfirst : Tendsto (fun n : ℕ => ((n - k : ℕ) : ℝ) / n) atTop (𝓝 1) := by
    have ht : Tendsto (fun n : ℕ => 1 - (k : ℝ) / n) atTop (𝓝 1) := by
      simpa using! tendsto_const_nhds.sub (tendsto_const_div_atTop_nhds_zero_nat (k : ℝ))
    apply ht.congr'
    filter_upwards [eventually_ge_atTop (max k 1)] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    rw [Nat.cast_sub (by omega : k ≤ n)]
    field_simp
  have hsecond : Tendsto (fun n : ℕ => (((n - k : ℕ) : ℝ) - 1) / n)
      atTop (𝓝 1) := by
    simpa [sub_div] using! hfirst.sub (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ))
  convert (hfirst.mul hsecond).div_const 2 using 1
  · funext n
    rw [Nat.cast_choose_two]
    ring
  · norm_num

lemma fixed_complement_eventually
    {M : NatSeq} {lam : ℝ} (hdeg : Tendsto (degree M) atTop (𝓝 lam)) (k : ℕ) :
    ∀ᶠ n in atTop, M n - k + 1 ≤ (n - k).choose 2 := by
  have hsmall : Tendsto (fun n => ((M n - k + 1 : ℕ) : ℝ) / (n : ℝ) ^ 2)
      atTop (𝓝 0) := by
    simpa [div_div, pow_two] using!
      (fixed_complement_numerator_tendsto hdeg k).div_atTop
        (tendsto_natCast_atTop_atTop (R := ℝ))
  have hbig := fixed_complement_capacity_tendsto k
  filter_upwards [(tendsto_order.1 hsmall).2 (1 / 4) (by norm_num),
    (tendsto_order.1 hbig).1 (1 / 4) (by norm_num),
    eventually_ge_atTop (1 : ℕ)] with n hs hq hn
  have hnpos : 0 < (n : ℝ) := by positivity
  have hlt : ((M n - k + 1 : ℕ) : ℝ) < ((n - k).choose 2 : ℕ) :=
    (div_lt_div_iff_of_pos_right (sq_pos_of_pos hnpos)).1 (hs.trans hq)
  exact_mod_cast hlt.le

lemma fixed_complement_scaled_tendsto
    {M : NatSeq} {lam : ℝ} (hdeg : Tendsto (degree M) atTop (𝓝 lam))
    (k : ℕ) :
    Tendsto (fun n : ℕ => (n : ℝ) *
      (((M n - k + 1 : ℕ) : ℝ) /
        (((n - k).choose 2 - (M n - k + 1) + 1 : ℕ) : ℝ)))
      atTop (𝓝 lam) := by
  have hnum := fixed_complement_numerator_tendsto hdeg k
  have hmain := fixed_complement_capacity_tendsto k
  have hsmall : Tendsto (fun n =>
      ((((M n - k + 1 : ℕ) : ℝ) - 1) / (n : ℝ) ^ 2)) atTop (𝓝 0) := by
    have ht := (hnum.sub (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ))).div_atTop
      (tendsto_natCast_atTop_atTop (R := ℝ))
    simpa only [Pi.sub_apply, ← sub_div, div_div, ← pow_two] using! ht
  have hden : Tendsto (fun n =>
      (((n - k).choose 2 - (M n - k + 1) + 1 : ℕ) : ℝ) / (n : ℝ) ^ 2)
      atTop (𝓝 (1 / 2)) := by
    have ht : Tendsto (fun n => (((n - k).choose 2 : ℕ) : ℝ) / (n : ℝ) ^ 2 -
        ((((M n - k + 1 : ℕ) : ℝ) - 1) / (n : ℝ) ^ 2)) atTop (𝓝 (1 / 2)) := by
      simpa using! hmain.sub hsmall
    apply ht.congr'
    filter_upwards [fixed_complement_eventually hdeg k] with n hs
    simp only [Nat.cast_add, Nat.cast_sub hs, Nat.cast_one]
    ring
  have ht : Tendsto (fun n =>
      (((M n - k + 1 : ℕ) : ℝ) / n) /
        ((((n - k).choose 2 - (M n - k + 1) + 1 : ℕ) : ℝ) / (n : ℝ) ^ 2))
      atTop (𝓝 lam) := by
    simpa using! hnum.div hden (by norm_num : (1 / 2 : ℝ) ≠ 0)
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  field_simp [hn0]

lemma fixed_edges_tendsto_atTop
    {M : NatSeq} {lam : ℝ} (hlam : 0 < lam)
    (hdeg : Tendsto (degree M) atTop (𝓝 lam)) :
    Tendsto (fun n => (M n : ℝ)) atTop atTop := by
  have ht := (fixed_edges_div_tendsto hdeg).pos_mul_atTop (by positivity : 0 < lam / 2)
    (tendsto_natCast_atTop_atTop (R := ℝ))
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  exact div_mul_cancel₀ _ (by positivity : (n : ℝ) ≠ 0)

lemma fixed_tree_ratio_tendsto_one
    (hT : TupleEstimatesStatement) {M : NatSeq} {lam : ℝ}
    (hadm : admissible M) (hlam : 0 < lam)
    (hdeg : Tendsto (degree M) atTop (𝓝 lam)) (k : ℕ) (hk : 0 < k) :
    Tendsto (fun n => treeMomentOne n (M n) k / treeLeading n (M n) k)
      atTop (𝓝 1) := by
  obtain ⟨C, hC, n0, hlocal⟩ := hT.2.2.1 (lam / 2) (lam + 1) 1 1
    (by positivity) (by linarith) (by norm_num) (by omega)
  have hevlo : ∀ᶠ n in atTop, lam / 2 ≤ degree M n :=
    ((tendsto_order.1 hdeg).1 (lam / 2) (by linarith)).mono fun _ h => h.le
  have hevhi : ∀ᶠ n in atTop, degree M n ≤ lam + 1 :=
    ((tendsto_order.1 hdeg).2 (lam + 1) (by linarith)).mono fun _ h => h.le
  have hevlog : ∀ᶠ n : ℕ in atTop, (k : ℝ) ≤ Real.log n :=
    (tendsto_atTop.1 (Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop (R := ℝ)))) k
  have hloc : ∀ᶠ n in atTop, 0 < treeMomentOne n (M n) k ∧
      |Real.log (treeMomentOne n (M n) k / treeLeading n (M n) k)| ≤
        C * (k : ℝ) ^ 2 / n := by
    filter_upwards [hadm, hevlo, hevhi, hevlog, eventually_ge_atTop n0]
      with n hm hlo hhi hlog hn
    simpa [treeMomentOne, tupleLeading] using!
      hlocal n (M n) (fun _ => k) hn hm hlo hhi (fun _ => hk) (by simpa using! hlog)
  have hlogzero : Tendsto (fun n => Real.log
      (treeMomentOne n (M n) k / treeLeading n (M n) k)) atTop (𝓝 0) := by
    apply squeeze_zero_norm'
    · exact hloc.mono fun n h => by simpa only [Real.norm_eq_abs] using! h.2
    · exact tendsto_const_div_atTop_nhds_zero_nat (C * (k : ℝ) ^ 2)
  have hexp : Tendsto (fun n => Real.exp (Real.log
      (treeMomentOne n (M n) k / treeLeading n (M n) k))) atTop (𝓝 1) := by
    simpa using! hlogzero.rexp
  apply hexp.congr'
  filter_upwards [hloc, hevlo, eventually_ge_atTop (1 : ℕ)] with n hn hlo hn1
  have hlead : 0 < treeLeading n (M n) k := by
    have ht := tupleLeading_pos n (M n) 1 (fun _ => k) (by omega)
      (lt_of_lt_of_le (by positivity : 0 < lam / 2) hlo) (fun _ => hk)
    simpa [tupleLeading] using! ht
  exact Real.exp_log (div_pos hn.1 hlead)

lemma fixed_tree_scaled_tendsto
    (hT : TupleEstimatesStatement) {M : NatSeq} {lam : ℝ}
    (hadm : admissible M) (hlam : 0 < lam)
    (hdeg : Tendsto (degree M) atTop (𝓝 lam)) (k : ℕ) (hk : 0 < k) :
    Tendsto (fun n => treeMomentOne n (M n) k / n)
      atTop (𝓝 (lam⁻¹ * ((cayley k : ℝ) / (k.factorial : ℝ)) *
        (lam * Real.exp (-lam)) ^ k)) := by
  have hlead : Tendsto (fun n => treeLeading n (M n) k / n)
      atTop (𝓝 (lam⁻¹ * ((cayley k : ℝ) / (k.factorial : ℝ)) *
        (lam * Real.exp (-lam)) ^ k)) := by
    have ht := ((hdeg.inv₀ hlam.ne').mul_const
      ((cayley k : ℝ) / (k.factorial : ℝ))).mul ((hdeg.mul hdeg.neg.rexp).pow k)
    apply ht.congr'
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by positivity
    simp only [treeLeading, if_neg hk.ne', degreeAt, degree]
    field_simp [hn0]
  have ht : Tendsto (fun n => (treeMomentOne n (M n) k / treeLeading n (M n) k) *
      (treeLeading n (M n) k / n)) atTop
      (𝓝 (lam⁻¹ * ((cayley k : ℝ) / (k.factorial : ℝ)) *
        (lam * Real.exp (-lam)) ^ k)) := by
    simpa using! (fixed_tree_ratio_tendsto_one hT hadm hlam hdeg k hk).mul hlead
  apply ht.congr'
  filter_upwards [(tendsto_order.1 hdeg).1 0 hlam,
    eventually_ge_atTop (1 : ℕ)] with n hd hn
  have hp : 0 < treeLeading n (M n) k := by
    simpa [tupleLeading] using! tupleLeading_pos n (M n) 1 (fun _ => k)
      (by omega) hd (fun _ => hk)
  field_simp [hp.ne']

lemma connectedCount_small_diagonal {k : ℕ} (hk : k ≤ 2) :
    connectedCount k k = 0 := by
  classical
  by_cases hk0 : k = 0
  · subst k
    simp [connectedCount]
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
    have hmax : Fintype.card (Edge k) < k := by
      interval_cases k <;> decide
    have hempty : fixedGraphs k k = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro G hG
      have hc := (Finset.mem_filter.mp hG).2
      have hle := Finset.card_le_univ G
      omega
    simp [connectedCount, hempty]

lemma cyclicFormula_small {n M k : ℕ} (hk : k ≤ 2) :
    cyclicFormula n M k = 0 := by
  simp [cyclicFormula, componentFormula, connectedCount_small_diagonal hk]

lemma fixed_cyclic_term_tendsto
    (hF : FiniteEnumerationStatement) (hT : TupleEstimatesStatement)
    {M : NatSeq} {lam : ℝ} (hadm : admissible M) (hlam : 0 < lam)
    (hdeg : Tendsto (degree M) atTop (𝓝 lam)) (k : ℕ) :
    Tendsto (fun n => if k ≤ n then (k : ℝ) * cyclicFormula n (M n) k else 0)
      atTop (𝓝 (unicyclicLimitTerm lam k)) := by
  by_cases hk3 : 3 ≤ k
  · have htree := fixed_tree_scaled_tendsto hT hadm hlam hdeg k (by omega)
    have hcomp := fixed_complement_scaled_tendsto hdeg k
    have hcay : (cayley k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (cayley_pos (by omega)).ne'
    have hk0 : (k : ℝ) ≠ 0 := by positivity
    have hfac : (k.factorial : ℝ) = (k : ℝ) * ((k - 1).factorial : ℝ) := by
      have heq : k = (k - 1) + 1 := by omega
      conv_lhs => rw [heq, Nat.factorial_succ]
      push_cast
      congr 1
      exact_mod_cast heq.symm
    have hlim :
        (k : ℝ) * ((lam⁻¹ * ((cayley k : ℝ) / (k.factorial : ℝ)) *
          (lam * Real.exp (-lam)) ^ k) * ((connectedCount k k : ℝ) / cayley k) * lam) =
          unicyclicLimitTerm lam k := by
      rw [unicyclicLimitTerm, if_pos hk3, enum_unicyclic_exact hF k hk3, hfac]
      field_simp [hcay, hk0, hlam.ne', show ((k - 1).factorial : ℝ) ≠ 0 by positivity]
      <;> ring
    have ht := ((htree.mul_const ((connectedCount k k : ℝ) / cayley k)).mul hcomp).const_mul (k : ℝ)
    rw [hlim] at ht
    apply ht.congr'
    filter_upwards [hadm, fixed_complement_eventually hdeg k,
      (tendsto_atTop.1 (fixed_edges_tendsto_atTop hlam hdeg)) (k : ℝ),
      eventually_ge_atTop (max k 1)] with n hm hs hmk hn
    have hkn : k ≤ n := by omega
    have hkM : k ≤ M n := by exact_mod_cast hmk
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    rw [if_pos hkn, component_ratio_unicyclic_eq hF hm hk3 hkn hkM hs]
    field_simp [hn0]
  · have hz : ∀ n, cyclicFormula n (M n) k = 0 := fun n => cyclicFormula_small (by omega)
    simpa [unicyclicLimitTerm, hk3, hz] using!
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))

lemma unicyclicLimitTerm_nonneg (lam : ℝ) (hlam : 0 < lam) (k : ℕ) :
    0 ≤ unicyclicLimitTerm lam k := by
  unfold unicyclicLimitTerm
  split_ifs <;> positivity

/- The finite part of the eventual sum-interchange argument, with the exact public normalization. -/
end
end Erdos745.WrapUp.Proofs.Internal.W08_CYCLIC_FixedMass


namespace Erdos745.WrapUp.Proofs.Internal.W08_CYCLIC_Near

noncomputable section
open Filter
open scoped BigOperators Topology
open Erdos745.WrapUp.Proofs.Internal.W08_CYCLIC_Finite
open Erdos745.WrapUp.Proofs.Internal.W08_CYCLIC_Analytic
open Erdos745.WrapUp.Proofs.Internal.W08_CYCLIC_Bounds
open Erdos745.WrapUp.Proofs.W06_POISSON

local instance : ContinuousInv₀ ℝ := IsTopologicalDivisionRing.toContinuousInv₀

lemma global_one_bound
    (hT : TupleEstimatesStatement) :
    ∃ C kappa : ℝ, 0 < C ∧ 0 < kappa ∧ ∃ n0 : ℕ,
      ∀ n M k : ℕ, n0 ≤ n → M ≤ capacity n →
        1 / 2 ≤ degreeAt n M → degreeAt n M ≤ 3 / 2 → 0 < k →
        treeMomentOne n M k ≤ C * n *
          Real.rpow (k : ℝ) (-5 / 2 : ℝ) *
          Real.exp (-kappa * ((degreeAt n M - 1) ^ 2 * k +
            (k : ℝ) ^ 3 / (n : ℝ) ^ 2)) := by
  obtain ⟨C, kappa, hC, hk, n0, hbound⟩ := hT.1 1 (by omega)
  refine ⟨C, kappa, hC, hk, n0, ?_⟩
  intro n M k hn hM hlo hhi hkpos
  have h := (hbound n M (fun _ => k) hn hM hlo hhi (fun _ => hkpos)).1
  simpa [treeMomentOne, tupleGlobalBound] using! h

private lemma cyclic_mass_term_bound
    (hF : FiniteEnumerationStatement) (CU C kappa : ℝ)
    (hCU : 0 < CU) (hC : 0 < C) (hkappa : 0 < kappa)
    (hCUb : ∀ k : ℕ, 3 ≤ k → (connectedCount k k : ℝ) ≤
      CU * Real.rpow (k : ℝ) ((k : ℝ) - 1 / 2))
    {n M k : ℕ} (hn : 16 ≤ n) (hM : M ≤ capacity n)
    (hlo : 1 / 2 ≤ degreeAt n M) (hhi : degreeAt n M ≤ 3 / 2)
    (hk : 3 ≤ k) (hkn : k ≤ n)
    (htree : treeMomentOne n M k ≤ C * n *
      Real.rpow (k : ℝ) (-5 / 2 : ℝ) *
      Real.exp (-kappa * ((degreeAt n M - 1) ^ 2 * k +
        (k : ℝ) ^ 3 / (n : ℝ) ^ 2))) :
    (k : ℝ) * cyclicFormula n M k ≤
      (8 * CU * C) * Real.exp (-kappa * (degreeAt n M - 1) ^ 2 * k) := by
  by_cases hkM : k ≤ M
  · obtain ⟨hsQ, hratio⟩ := near_complement_ratio hn hlo hhi hkM
    have hc := component_ratio_unicyclic hF CU hCUb hM hk hkn hkM hsQ
    have hnpos : 0 < (n : ℝ) := by positivity
    have hkpos : 0 < (k : ℝ) := by positivity
    have hexp : Real.exp (-kappa *
        ((degreeAt n M - 1) ^ 2 * k + (k : ℝ) ^ 3 / (n : ℝ) ^ 2)) ≤
        Real.exp (-kappa * (degreeAt n M - 1) ^ 2 * k) := by
      apply Real.exp_le_exp.mpr
      have hnonneg : 0 ≤ (k : ℝ) ^ 3 / (n : ℝ) ^ 2 := by positivity
      nlinarith
    have hrpow : Real.rpow (k : ℝ) (-5 / 2 : ℝ) *
        Real.rpow (k : ℝ) (3 / 2 : ℝ) * k = 1 := by
      simp only [Real.rpow_eq_pow]
      rw [← Real.rpow_add hkpos]
      norm_num [Real.rpow_neg_one, hkpos.ne']
    calc
      (k : ℝ) * cyclicFormula n M k ≤
          k * (treeMomentOne n M k *
            (CU * Real.rpow (k : ℝ) (3 / 2 : ℝ)) *
              ((M - k + 1 : ℕ) : ℝ) /
                (((n - k).choose 2 - (M - k + 1) + 1 : ℕ) : ℝ)) := by
        gcongr
      _ = k * (treeMomentOne n M k *
          (CU * Real.rpow (k : ℝ) (3 / 2 : ℝ)) *
          (((M - k + 1 : ℕ) : ℝ) /
            (((n - k).choose 2 - (M - k + 1) + 1 : ℕ) : ℝ))) := by ring
      _ ≤ k * ((C * n * Real.rpow (k : ℝ) (-5 / 2 : ℝ) *
            Real.exp (-kappa * ((degreeAt n M - 1) ^ 2 * k +
              (k : ℝ) ^ 3 / (n : ℝ) ^ 2))) *
            (CU * Real.rpow (k : ℝ) (3 / 2 : ℝ)) * (8 / n)) := by
        gcongr <;> simp only [Real.rpow_eq_pow] <;> positivity
      _ = (8 * CU * C) * Real.exp (-kappa *
            ((degreeAt n M - 1) ^ 2 * k + (k : ℝ) ^ 3 / (n : ℝ) ^ 2)) := by
        calc
          _ = (8 * CU * C) * Real.exp (-kappa *
              ((degreeAt n M - 1) ^ 2 * k + (k : ℝ) ^ 3 / (n : ℝ) ^ 2)) *
              (Real.rpow (k : ℝ) (-5 / 2 : ℝ) *
                Real.rpow (k : ℝ) (3 / 2 : ℝ) * k) := by
            field_simp [hnpos.ne']
            <;> ring
          _ = _ := by rw [hrpow, mul_one]
      _ ≤ _ := mul_le_mul_of_nonneg_left hexp (by positivity)
  · have hz : cyclicFormula n M k = 0 := by
      unfold cyclicFormula componentFormula
      simp [Nat.lt_of_not_ge hkM]
    rw [hz, mul_zero]
    positivity

/-- Finite sums with a vanishing zeroth term are controlled by the positive-index series. -/
lemma sum_range_le_tsum_succ (f g : ℕ → ℝ) (D : ℝ) (n : ℕ)
    (hD : 0 ≤ D) (hzero : f 0 = 0) (hg : ∀ j, 0 ≤ g j)
    (hs : Summable g)
    (hbound : ∀ j, j < n → f (j + 1) ≤ D * g j) :
    (∑ k ∈ Finset.range (n + 1), f k) ≤ D * ∑' j, g j := by
  rw [Finset.sum_range_succ', hzero, add_zero]
  calc
    (∑ j ∈ Finset.range n, f (j + 1)) ≤
        ∑ j ∈ Finset.range n, D * g j :=
      Finset.sum_le_sum fun j hj => hbound j (Finset.mem_range.mp hj)
    _ = D * ∑ j ∈ Finset.range n, g j := (Finset.mul_sum _ _ _).symm
    _ ≤ D * ∑' j, g j :=
      mul_le_mul_of_nonneg_left (hs.sum_le_tsum _ (fun j _ => hg j)) hD

lemma barely_unicyclic_bounded
    (hF : FiniteEnumerationStatement) (hT : TupleEstimatesStatement)
    (hA : AnalyticSumsStatement) (M : NatSeq)
    (hbare : bareSub M ∨ bareSuper M) :
    boundedBy (fun n => expectM n (M n) unicyclicMass)
      (fun n => (epsilon M n)⁻¹ ^ 2) := by
  obtain ⟨CU, hCU, hCUb⟩ := enum_unicyclic_bound hF
  obtain ⟨C, kappa, hC, hkappa, nT, htree⟩ := global_one_bound hT
  obtain ⟨S, hS, hsum⟩ := analytic_power_bound hA 0 (by norm_num)
  refine ⟨max 1 ((8 * CU * C * S) * Real.rpow kappa (-1)), by
    exact lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  have hadm := bare_admissible hbare
  have hdeg := bare_degree_tendsto_one hbare
  have hepos := bare_epsilon_pos hbare
  have hulo : ∀ᶠ n in atTop, 1 / 2 ≤ degree M n :=
    ((tendsto_order.1 hdeg).1 (1 / 2) (by norm_num)).mono fun _ h => h.le
  have huhi : ∀ᶠ n in atTop, degree M n ≤ 3 / 2 :=
    ((tendsto_order.1 hdeg).2 (3 / 2) (by norm_num)).mono fun _ h => h.le
  have huone : ∀ᶠ n in atTop, kappa * epsilon M n ^ 2 ≤ 1 := by
    have he := bare_epsilon_tendsto_zero hbare
    have he2 : Tendsto (fun n => kappa * epsilon M n ^ 2) atTop (𝓝 0) := by
      simpa using! (he.pow 2).const_mul kappa
    exact ((tendsto_order.1 he2).2 1 zero_lt_one).mono fun _ h => h.le
  filter_upwards [hadm, hulo, huhi, hepos, huone,
    eventually_ge_atTop (max 16 nT)] with n hMn hlo hhi he hu hn
  have hn16 : 16 ≤ n := (le_max_left _ _).trans hn
  have hnT : nT ≤ n := (le_max_right _ _).trans hn
  rw [abs_of_nonneg (expect_unicyclicMass_nonneg n (M n)),
    expect_unicyclicMass_eq hF hMn]
  let u := kappa * epsilon M n ^ 2
  have hu0 : 0 < u := mul_pos hkappa (sq_pos_of_pos he)
  have hterm : ∀ k ∈ Finset.range (n + 1),
      (k : ℝ) * cyclicFormula n (M n) k ≤
        if 3 ≤ k then (8 * CU * C) * Real.exp (-u * k) else 0 := by
    intro k hkn
    by_cases hk3 : 3 ≤ k
    · simp only [hk3, if_true]
      have htr := htree n (M n) k hnT hMn hlo hhi (by omega)
      have hd : (degreeAt n (M n) - 1) ^ 2 = epsilon M n ^ 2 := by
        simp [epsilon, degree, degreeAt, sq_abs]
      simpa [u, hd, mul_assoc] using! cyclic_mass_term_bound hF CU C kappa hCU hC hkappa hCUb
        hn16 hMn hlo hhi hk3 (Nat.le_of_lt_succ (Finset.mem_range.mp hkn)) htr
    · have hk : k ≤ 2 := by omega
      have hz : cyclicFormula n (M n) k = 0 :=
        W08_CYCLIC_FixedMass.cyclicFormula_small hk
      simp [hk3, hz]
  calc
    (∑ k ∈ Finset.range (n + 1), (k : ℝ) * cyclicFormula n (M n) k) ≤
        ∑ k ∈ Finset.range (n + 1),
          if 3 ≤ k then (8 * CU * C) * Real.exp (-u * k) else 0 :=
      Finset.sum_le_sum hterm
    _ ≤ (8 * CU * C) *
        (∑' j : ℕ, Real.rpow ((j + 1 : ℕ) : ℝ) 0 *
          Real.exp (-u * (j + 1))) := by
      apply sum_range_le_tsum_succ _ _ _ n (by positivity) (by simp)
        (fun j => by simp only [Real.rpow_eq_pow]; positivity) (hsum u hu0 hu).1
      intro j hj
      split_ifs <;> simp only [Real.rpow_eq_pow, Real.rpow_zero, one_mul, Nat.cast_add, Nat.cast_one]
      · exact le_rfl
      · positivity
    _ ≤ (8 * CU * C) * (S * Real.rpow u (-1)) := by
      gcongr
      simpa using! (hsum u hu0 hu).2
    _ = (8 * CU * C * S * Real.rpow kappa (-1)) *
          (epsilon M n)⁻¹ ^ 2 := by
      dsimp [u]
      simp only [Real.rpow_eq_pow, Real.rpow_neg_one]
      field_simp [hkappa.ne', he.ne']
      <;> ring
    _ ≤ max 1 ((8 * CU * C * S) * Real.rpow kappa (-1)) *
          (epsilon M n)⁻¹ ^ 2 := by
      gcongr
      exact le_max_right _ _

lemma barely_cyclic_tail
    (hF : FiniteEnumerationStatement) (hRate : RateStatement)
    (hMass : ∀ M : NatSeq, bareSub M ∨ bareSuper M →
      boundedBy (fun n => expectM n (M n) unicyclicMass)
        (fun n => (epsilon M n)⁻¹ ^ 2))
    (M : NatSeq) (hbare : bareSub M ∨ bareSuper M) (r : ℝ) :
    Tendsto (fun n => probM n (M n)
      (fun G => cyclicAbove G (nearThreshold M n r))) atTop (𝓝 0) := by
  obtain ⟨C, hC, hmass⟩ := hMass M hbare
  have hadm := bare_admissible hbare
  have he := bare_epsilon_pos hbare
  have hrate := near_rate_eventually_pos hRate hbare
  have hnum := nearNumerator_tendsto_atTop hbare r
  have hthreshold : Tendsto (nearThreshold M · r) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    have hnumLarge := (tendsto_atTop.1 hnum) (max 1 b)
    have hrateSmall := ((tendsto_order.1 (near_rate_tendsto_zero hRate hbare)).2 1
      zero_lt_one).mono fun _ h => h.le
    filter_upwards [hnumLarge, hrate, hrateSmall] with n hn hp hs
    unfold nearThreshold
    have hnpos : 0 < nearNumerator M n r := zero_lt_one.trans_le
      ((le_max_left _ _).trans hn)
    apply (le_div_iff₀ hp).2
    have hb : b * rate (degree M n) ≤ nearNumerator M n r := by
      by_cases hb0 : b ≤ 0
      · exact le_trans (mul_nonpos_of_nonpos_of_nonneg hb0 hp.le) hnpos.le
      · have : b * rate (degree M n) ≤ b := mul_le_of_le_one_right (le_of_not_ge hb0) hs
        exact this.trans ((le_max_right _ _).trans hn)
    exact hb
  have hscale : Tendsto (fun n =>
      (epsilon M n)⁻¹ ^ 2 / nearThreshold M n r) atTop (𝓝 0) := by
    have hprod : Tendsto (fun n => epsilon M n ^ 2 * nearThreshold M n r)
        atTop atTop := by
      have hratio := rate_over_epsilon_sq_tendsto hRate hbare
      have hnumTop := nearNumerator_tendsto_atTop hbare r
      have hinv : Tendsto (fun n => epsilon M n ^ 2 / rate (degree M n))
          atTop (𝓝 2) := by
        have := hratio.inv₀ (by norm_num : (1 / 2 : ℝ) ≠ 0)
        simpa [one_div_div] using! this
      simpa only [nearThreshold, div_mul_eq_mul_div, mul_div_assoc] using!
        hinv.pos_mul_atTop (by norm_num : (0 : ℝ) < 2) hnumTop
    have hinv := tendsto_inv_atTop_zero.comp hprod
    apply hinv.congr'
    filter_upwards [he, (tendsto_atTop.1 hthreshold) 1] with n hen hh
    dsimp only [Function.comp_apply]
    field_simp [hen.ne', (zero_lt_one.trans_le hh).ne']
  apply squeeze_zero'
  · filter_upwards with n
    unfold probM
    positivity
  · have hbound : ∀ᶠ n in atTop,
        probM n (M n) (fun G => cyclicAbove G (nearThreshold M n r)) ≤
          C * ((epsilon M n)⁻¹ ^ 2 / nearThreshold M n r) := by
      filter_upwards [hadm, hmass, (tendsto_atTop.1 hthreshold) 1] with n hMn hm hh
      have htpos : 0 < nearThreshold M n r := zero_lt_one.trans_le hh
      calc
        probM n (M n) (fun G => cyclicAbove G (nearThreshold M n r)) ≤
            expectM n (M n) unicyclicMass / nearThreshold M n r :=
          prob_cyclicAbove_le_mass_div hF hMn htpos
        _ ≤ (C * (epsilon M n)⁻¹ ^ 2) / nearThreshold M n r := by
          gcongr
          simpa [abs_of_nonneg (expect_unicyclicMass_nonneg n (M n))] using! hm
        _ = C * ((epsilon M n)⁻¹ ^ 2 / nearThreshold M n r) := by ring
    exact hbound
  · simpa using! hscale.const_mul C

end
end Erdos745.WrapUp.Proofs.Internal.W08_CYCLIC_Near


namespace Erdos745.WrapUp.Proofs.Internal.W08_CYCLIC_Cutoff

noncomputable section
open Filter
open scoped Topology

lemma cutoff_geometry :
    ∀ᶠ n : ℕ in atTop, 0 < n ∧ ∀ k : ℕ, k < largeCutoff n →
      k ≤ n / 2 ∧ Real.rpow (k : ℝ) (3 / 2 : ℝ) / n ≤ 2 := by
  have hratio : Tendsto (fun n : ℕ => n23 n / (n : ℝ)) atTop (𝓝 0) := by
    have hpow := (tendsto_rpow_neg_atTop (by norm_num : 0 < (1 / 3 : ℝ))).comp
      tendsto_natCast_atTop_atTop
    apply hpow.congr'
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hnpos : 0 < (n : ℝ) := by positivity
    unfold n23
    simp only [Real.rpow_eq_pow, Function.comp_apply]
    rw [show (2 / 3 : ℝ) = 1 + (-1 / 3 : ℝ) by ring,
      Real.rpow_add hnpos]
    rw [Real.rpow_one]
    field_simp [hnpos.ne']
  have hevent : ∀ᶠ n : ℕ in atTop, n23 n / n ≤ 1 / 2 :=
    ((tendsto_order.1 hratio).2 (1 / 2) (by norm_num)).mono fun _ h => h.le
  filter_upwards [hevent, eventually_ge_atTop (1 : ℕ)] with n hhalf hn
  refine ⟨by omega, ?_⟩
  intro k hk
  have hkr : (k : ℝ) < n23 n := by
    exact Nat.lt_ceil.mp hk
  have hnpos : 0 < (n : ℝ) := by positivity
  have hn23 : n23 n ≤ (n : ℝ) / 2 := by
    have hh := (div_le_iff₀ hnpos).1 hhalf
    linarith
  have hkhalfR : (k : ℝ) < (n : ℝ) / 2 := hkr.trans_le hn23
  have hkhalf : k ≤ n / 2 := by
    apply (Nat.le_div_iff_mul_le (by omega : 0 < 2)).2
    have hr : (k : ℝ) * 2 ≤ n := by linarith
    exact_mod_cast hr
  refine ⟨hkhalf, ?_⟩
  have hk0 : 0 ≤ (k : ℝ) := by positivity
  have hn0 : 0 ≤ (n : ℝ) := by positivity
  have hrpow : Real.rpow (k : ℝ) (3 / 2 : ℝ) ≤
      Real.rpow (n23 n) (3 / 2 : ℝ) :=
    Real.rpow_le_rpow hk0 hkr.le (by norm_num)
  have hn23pow : Real.rpow (n23 n) (3 / 2 : ℝ) = (n : ℝ) := by
    unfold n23
    simp only [Real.rpow_eq_pow]
    rw [← Real.rpow_mul hn0]
    norm_num
  rw [hn23pow] at hrpow
  exact (div_le_iff₀ hnpos).2 (by nlinarith)

end
end Erdos745.WrapUp.Proofs.Internal.W08_CYCLIC_Cutoff
