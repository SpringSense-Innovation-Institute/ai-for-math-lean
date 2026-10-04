module

public import Erdos745.WrapUp.Proofs.Internal.Linked.W08_Near
public import Erdos745.WrapUp.Proofs.Internal.Linked.W06_P02

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local simp] Pi.div_def Pi.mul_def Pi.add_def Pi.sub_def Pi.neg_def Pi.inv_def Function.comp_def Pi.pow_def Pi.smul_def Real.rpow_eq_pow

@[expose] public section


namespace Erdos745.WrapUp.Proofs.Internal.W08_CYCLIC_FixedLocal

noncomputable section
open Filter
open scoped BigOperators Topology
open Erdos745.WrapUp.Proofs.Internal.W08_CYCLIC_Finite
open Erdos745.WrapUp.Proofs.W06_POISSON

lemma fixed_compact_data (hRate : RateStatement) {M : NatSeq} {lam : ℝ}
    (hlam : 0 < lam) (hlam1 : lam ≠ 1)
    (hdeg : Tendsto (degree M) atTop (𝓝 lam)) :
    ∃ lo hi a : ℝ, 0 < lo ∧ lo ≤ hi ∧ 0 < a ∧
      ∀ᶠ n in atTop, lo ≤ degree M n ∧ degree M n ≤ hi ∧
        a ≤ rate (degree M n) := by
  let lo := lam / 2
  let hi := lam + 1
  let a := rate lam / 2
  have hlo : 0 < lo := by dsimp [lo]; positivity
  have hlohi : lo ≤ hi := by dsimp [lo, hi]; linarith
  have hra : 0 < rate lam := hRate.1 lam hlam hlam1
  have ha : 0 < a := by dsimp [a]; linarith
  have hrate := tendsto_rate_of_tendsto hlam hdeg
  have hevlo : ∀ᶠ n in atTop, lo ≤ degree M n :=
    ((tendsto_order.1 hdeg).1 lo (by dsimp [lo]; linarith)).mono fun _ h => h.le
  have hevhi : ∀ᶠ n in atTop, degree M n ≤ hi :=
    ((tendsto_order.1 hdeg).2 hi (by dsimp [hi]; linarith)).mono fun _ h => h.le
  have heva : ∀ᶠ n in atTop, a ≤ rate (degree M n) :=
    ((tendsto_order.1 hrate).1 a (by dsimp [a]; linarith)).mono fun _ h => h.le
  exact ⟨lo, hi, a, hlo, hlohi, ha, hevlo.and (hevhi.and heva)⟩

lemma fixed_local_tree_bound
    (hT : TupleEstimatesStatement) (hRate : RateStatement)
    {M : NatSeq} {lam B : ℝ} (hlam : 0 < lam) (hlam1 : lam ≠ 1)
    (hB : 0 < B) (hadm : admissible M)
    (hdeg : Tendsto (degree M) atTop (𝓝 lam)) :
    ∃ D a : ℝ, 0 < D ∧ 0 < a ∧ ∃ n0 : ℕ, ∀ n k : ℕ,
      n0 ≤ n → k ≤ n → 0 < k → (k : ℝ) ≤ B * Real.log n →
      treeMomentOne n (M n) k ≤
        D * (n : ℝ) * Real.rpow (k : ℝ) (-5 / 2 : ℝ) *
          Real.exp (-a * k) := by
  obtain ⟨lo, hi, a0, hlo, hlohi, ha0, hcompact⟩ :=
    fixed_compact_data hRate hlam hlam1 hdeg
  obtain ⟨C, hC, nT, hlocal⟩ := hT.2.2.1 lo hi B 1 hlo hlohi hB (by omega)
  obtain ⟨R, hR, hRbound⟩ := cayleyStirlingRatio_bddAbove
  let a := a0 / 2
  let D := Real.exp 1 * (R / (lo * Real.sqrt (2 * Real.pi)))
  have ha : 0 < a := by dsimp [a]; linarith
  have hD : 0 < D := by dsimp [D]; positivity
  have hlogsmall : ∀ᶠ n : ℕ in atTop,
      C * (B * Real.log n) ^ 2 / n ≤ 1 := by
    have hlittle := isLittleO_log_rpow_atTop (r := (1 / 2 : ℝ)) (by norm_num)
    have ht := hlittle.tendsto_div_nhds_zero
    have htN := ht.comp tendsto_natCast_atTop_atTop
    have hsquare : Tendsto (fun n : ℕ => C * (B * Real.log n) ^ 2 / n)
        atTop (𝓝 0) := by
      have hmul := (htN.mul htN).const_mul (C * B ^ 2)
      convert hmul using 1
      · funext n
        simp only [Function.comp_apply]
        have hp : (((n : ℝ) ^ (1 / 2 : ℝ))) ^ 2 = (n : ℝ) := by
          have h := Real.rpow_mul_natCast (show 0 ≤ (n : ℝ) by positivity) (1 / 2 : ℝ) 2
          calc
            _ = (n : ℝ) ^ ((1 / 2 : ℝ) * (2 : ℕ)) := h.symm
            _ = (n : ℝ) ^ (1 : ℝ) := by congr 1; norm_num
            _ = n := Real.rpow_one _
        rw [show Real.log (n : ℝ) / ((n : ℝ) ^ (1 / 2 : ℝ)) *
            (Real.log (n : ℝ) / ((n : ℝ) ^ (1 / 2 : ℝ))) =
            (Real.log (n : ℝ)) ^ 2 / (((n : ℝ) ^ (1 / 2 : ℝ))) ^ 2 by ring, hp]
        ring
      · simp
    exact ((tendsto_order.1 hsquare).2 1 zero_lt_one).mono fun _ h => h.le
  rw [Filter.eventually_atTop] at hcompact hlogsmall
  obtain ⟨nl, hnl⟩ := hlogsmall
  obtain ⟨nd, hnd⟩ := hcompact
  rw [admissible, Filter.eventually_atTop] at hadm
  obtain ⟨nm, hnm⟩ := hadm
  refine ⟨D, a, hD, ha, max 1 (max nT (max nl (max nd nm))), ?_⟩
  intro n k hn hkn hk hklog
  have hn1 : 1 ≤ n := by omega
  have hnT : nT ≤ n := by omega
  have hnl' : nl ≤ n := by omega
  have hnd' : nd ≤ n := by omega
  have hnm' : nm ≤ n := by omega
  obtain ⟨hlodeg, hhideg, hratedeg⟩ := hnd n hnd'
  have hloc := hlocal n (M n) (fun _ => k) hnT (hnm n hnm') hlodeg hhideg
      (fun _ => hk) (by simpa using! hklog)
  have hleadEq : tupleLeading n (M n) 1 (fun _ => k) = treeLeading n (M n) k := by
    simp [tupleLeading, treeLeading, Nat.ne_of_gt hk]
  simp only [hleadEq, Fin.sum_univ_one] at hloc
  have herr : C * (k : ℝ) ^ 2 / n ≤ 1 := by
    calc
      C * (k : ℝ) ^ 2 / n ≤ C * (B * Real.log n) ^ 2 / n := by gcongr
      _ ≤ 1 := hnl n hnl'
  have hleadpos : 0 < treeLeading n (M n) k := by
    rw [← hleadEq]
    exact W04_TUPLES_Foundation.tupleLeading_pos n (M n) 1 (fun _ => k)
      (by omega) (lt_of_lt_of_le hlo hlodeg) (fun _ => hk)
  have hmoment := le_exp_mul_of_abs_log_div_le hloc.1 hleadpos (hloc.2.trans herr)
  have hlead := treeLeading_eq_cayleyKernel n (M n) k hk (lt_of_lt_of_le hlo hlodeg)
  have hkern := cayleyKernel_eq_stirling k hk
  have hratio : cayleyStirlingRatio k ≤ R := hRbound k
  have hdegInv : (degree M n)⁻¹ ≤ lo⁻¹ := by
    exact inv_anti₀ hlo hlodeg
  have hrateExp : Real.exp (-rate (degree M n) * k) ≤ Real.exp (-a0 * k) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hstir : 0 ≤ cayleyStirlingRatio k := (cayleyStirlingRatio_pos k hk).le
  simp only [Real.rpow_eq_pow] at *
  calc
    treeMomentOne n (M n) k ≤ Real.exp 1 * treeLeading n (M n) k := hmoment
    _ = Real.exp 1 * ((n : ℝ) / degree M n *
        (cayleyStirlingRatio k / Real.sqrt (2 * Real.pi) *
          Real.rpow (k : ℝ) (-5 / 2 : ℝ)) *
        Real.exp (-rate (degree M n) * k)) := by rw [hlead, hkern]; simp only [degree, Real.rpow_eq_pow]; congr 3 <;> congr 1 <;> ring
    _ ≤ Real.exp 1 * ((n : ℝ) / lo *
        (R / Real.sqrt (2 * Real.pi) * Real.rpow (k : ℝ) (-5 / 2 : ℝ)) *
        Real.exp (-a0 * k)) := by
      simp only [Real.rpow_eq_pow]
      gcongr
    _ ≤ D * (n : ℝ) * Real.rpow (k : ℝ) (-5 / 2 : ℝ) *
        Real.exp (-a * k) := by
      dsimp [D, a]
      have hexp : Real.exp (-a0 * k) ≤ Real.exp (-(a0 / 2) * k) := by
        apply Real.exp_le_exp.mpr
        nlinarith
      calc
        Real.exp 1 * ((n : ℝ) / lo *
            (R / Real.sqrt (2 * Real.pi) * Real.rpow (k : ℝ) (-5 / 2 : ℝ)) *
            Real.exp (-a0 * k)) ≤
          Real.exp 1 * ((n : ℝ) / lo *
            (R / Real.sqrt (2 * Real.pi) * Real.rpow (k : ℝ) (-5 / 2 : ℝ)) *
            Real.exp (-(a0 / 2) * k)) := by
            simp only [Real.rpow_eq_pow]
            gcongr
        _ = _ := by simp only [Real.rpow_eq_pow]; ring

end
end Erdos745.WrapUp.Proofs.Internal.W08_CYCLIC_FixedLocal


namespace Erdos745.WrapUp.Proofs.Internal.W08_CYCLIC_Complex

noncomputable section
open Filter
open scoped BigOperators Topology
open Erdos745.WrapUp.Proofs.Internal.W08_CYCLIC_Finite
open Erdos745.WrapUp.Proofs.Internal.W08_CYCLIC_Analytic
open Erdos745.WrapUp.Proofs.Internal.W08_CYCLIC_Bounds
open Erdos745.WrapUp.Proofs.Internal.W08_CYCLIC_Cutoff
open Erdos745.WrapUp.Proofs.Internal.W08_CYCLIC_Near
open Erdos745.WrapUp.Proofs.W06_POISSON

lemma connectedCount_eq_zero_of_capacity_lt {k e : ℕ} (he : capacity k < e) :
    connectedCount k e = 0 := by
  classical
  have hcard : Fintype.card (Edge k) ≤ capacity k := by
    let f : Edge k → {a : Sym2 (Fin k) // ¬ a.IsDiag} := fun e =>
      ⟨s(e.1.1, e.1.2), by simpa [Sym2.mk_isDiag_iff] using! ne_of_lt e.2⟩
    have hf : Function.Injective f := by
      intro e e' h
      apply Subtype.ext
      simp only [f, Subtype.mk.injEq] at h
      rw [Sym2.eq_iff] at h
      rcases h with h | h
      · exact Prod.ext h.1 h.2
      · have hback : e.1.2 < e.1.1 := by rw [h.2, h.1]; exact e'.2
        exact (lt_asymm e.2 hback).elim
    calc
      Fintype.card (Edge k) ≤ Fintype.card {a : Sym2 (Fin k) // ¬ a.IsDiag} :=
        Fintype.card_le_of_injective f hf
      _ = capacity k := by
        simpa only [capacity, Fintype.card_fin] using!
          (Sym2.card_subtype_not_diag (α := Fin k))
  have hempty : fixedGraphs k e = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro G hG
    have hc := (Finset.mem_filter.mp hG).2
    have hle := Finset.card_le_univ G
    omega
  simp [connectedCount, hempty]

lemma excess_sum_capacity_eq {n M k : ℕ} (hkn : k ≤ n) :
    (∑ r ∈ Finset.Icc 1 (capacity n), excessFormula n M k r) =
      ∑ r ∈ Finset.Icc 1 (capacity k), excessFormula n M k r := by
  symm
  apply Finset.sum_subset
  · intro r hr
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hr).1,
      (Finset.mem_Icc.mp hr).2.trans (Nat.choose_le_choose 2 hkn)⟩
  · intro r hr hnot
    have hrcap : capacity k < r := by
      have hrpos := (Finset.mem_Icc.mp hr).1
      simp only [Finset.mem_Icc, not_and_or, not_le] at hnot
      omega
    have hz := connectedCount_eq_zero_of_capacity_lt (k := k) (e := k + r)
      (by omega)
    simp [excessFormula, componentFormula, hz]

lemma small_complex_sum_bound
    (hF : FiniteEnumerationStatement) (A K : ℝ) (hA : 1 < A) (hK : 0 < K)
    (hKeq : K = 64 * A * excessKernelConstant (8 * A))
    (hbound : ∀ k r : ℕ, 0 < k → 0 < r →
      (connectedCount k (k + r) : ℝ) ≤ A ^ r *
        Real.rpow (r : ℝ) (-(r : ℝ) / 2) *
        Real.rpow (k : ℝ) ((k : ℝ) + (3 * (r : ℝ) - 1) / 2))
    {n M : ℕ} (hn : 16 ≤ n) (hM : M ≤ capacity n)
    (hdeglo : 1 / 2 ≤ degreeAt n M) (hdeghi : degreeAt n M ≤ 3 / 2)
    (hcut : ∀ k, k < largeCutoff n → k ≤ n / 2 ∧
      Real.rpow (k : ℝ) (3 / 2 : ℝ) / n ≤ 2) :
    expectM n M (fun G => (smallComplexCount G (largeCutoff n) : ℝ)) ≤
      ∑ k ∈ Finset.range (n + 1),
        if 3 ≤ k ∧ k < largeCutoff n then
          treeMomentOne n M k * K *
            (Real.rpow (k : ℝ) 3 / (n : ℝ) ^ 2) else 0 := by
  rw [expect_smallComplexCount_eq hF hM]
  apply Finset.sum_le_sum
  intro k hk
  by_cases hgood : 3 ≤ k ∧ k < largeCutoff n
  · simp only [if_pos hgood, if_pos hgood.2]
    by_cases hkM : k ≤ M
    · obtain ⟨hsQ, hratio⟩ := near_complement_ratio hn hdeglo hdeghi hkM
      have hkhalf := (hcut k hgood.2).1
      have hsum := excess_sum_le_tree hF A K hA hK hbound hM (by omega)
        hgood.1 (Nat.le_of_lt_succ (Finset.mem_range.mp hk)) hkhalf hratio hsQ
        (hcut k hgood.2).2
      rw [excess_sum_capacity_eq (Nat.le_of_lt_succ (Finset.mem_range.mp hk))]
      simpa only [hKeq] using! hsum
    · have hz : ∀ r, excessFormula n M k r = 0 := by
        intro r
        unfold excessFormula componentFormula
        have : M < k + r := by omega
        simp [this]
      simp only [hz, Finset.sum_const_zero]
      have ht0 := Erdos745.WrapUp.Proofs.W06_POISSON.tupleMoment_nonneg
        n M 1 (fun _ => k)
      change 0 ≤ treeMomentOne n M k at ht0
      simp only [Real.rpow_eq_pow]
      positivity
  · by_cases hkh : k < largeCutoff n
    · have hklt : k < 3 := by omega
      simp only [if_neg hgood, if_pos hkh]
      apply le_of_eq
      apply Finset.sum_eq_zero
      intro r hr
      have hz : connectedCount k (k + r) = 0 := by
        classical
        by_cases hk0 : k = 0
        · subst k
          simp [connectedCount]
        · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
          have hmax : Fintype.card (Edge k) < k := by
            interval_cases k <;> decide
          have hempty : fixedGraphs k (k + r) = ∅ := by
            apply Finset.eq_empty_iff_forall_notMem.mpr
            intro G hG
            have hc := (Finset.mem_filter.mp hG).2
            have hle := Finset.card_le_univ G
            omega
          simp [connectedCount, hempty]
      unfold excessFormula componentFormula
      split_ifs <;> simp [hz]
    · simp [hkh]

lemma barely_small_complex_bounded
    (hF : FiniteEnumerationStatement) (hKern : KernelBoundStatement)
    (hT : TupleEstimatesStatement) (hA : AnalyticSumsStatement)
    (M : NatSeq) (hbare : bareSub M ∨ bareSuper M) :
    boundedBy (fun n => expectM n (M n)
      (fun G => (smallComplexCount G (largeCutoff n) : ℝ)))
      (fun n => (widthParameter M n)⁻¹) := by
  obtain ⟨A, hAone, hKbound⟩ := hKern
  let K := 64 * A * excessKernelConstant (8 * A)
  have hK : 0 < K := by
    have hE := excessKernelConstant_pos (8 * A)
    dsimp [K]
    positivity
  obtain ⟨C, kappa, hC, hkappa, nT, htree⟩ :=
    W08_CYCLIC_Near.global_one_bound hT
  obtain ⟨S, hS, hsum⟩ := analytic_power_bound hA (1 / 2) (by norm_num)
  let D := K * C * S * Real.rpow kappa (-3 / 2 : ℝ)
  refine ⟨max 1 D, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  have hadm := bare_admissible hbare
  have hdeg := bare_degree_tendsto_one hbare
  have hepos := bare_epsilon_pos hbare
  have hgeom := cutoff_geometry
  have hlo : ∀ᶠ n in atTop, 1 / 2 ≤ degree M n :=
    ((tendsto_order.1 hdeg).1 (1 / 2) (by norm_num)).mono fun _ h => h.le
  have hhi : ∀ᶠ n in atTop, degree M n ≤ 3 / 2 :=
    ((tendsto_order.1 hdeg).2 (3 / 2) (by norm_num)).mono fun _ h => h.le
  have hu : ∀ᶠ n in atTop, kappa * epsilon M n ^ 2 ≤ 1 := by
    have ht : Tendsto (fun n => kappa * epsilon M n ^ 2) atTop (𝓝 0) := by
      simpa using! (bare_epsilon_tendsto_zero hbare).pow 2 |>.const_mul kappa
    exact ((tendsto_order.1 ht).2 1 zero_lt_one).mono fun _ h => h.le
  filter_upwards [hadm, hlo, hhi, hepos, hgeom, hu,
    eventually_ge_atTop (max 16 nT)] with n hMn hdnlo hdnhi hen hgeo hun hn
  have hn16 : 16 ≤ n := (le_max_left _ _).trans hn
  have hnT : nT ≤ n := (le_max_right _ _).trans hn
  rw [abs_of_nonneg (expect_smallComplexCount_nonneg n (M n) (largeCutoff n))]
  have hbase := small_complex_sum_bound hF A K hAone hK rfl hKbound hn16 hMn
    hdnlo hdnhi hgeo.2
  let u := kappa * epsilon M n ^ 2
  have hu0 : 0 < u := mul_pos hkappa (sq_pos_of_pos hen)
  calc
    expectM n (M n) (fun G => (smallComplexCount G (largeCutoff n) : ℝ)) ≤
        ∑ k ∈ Finset.range (n + 1),
          if 3 ≤ k ∧ k < largeCutoff n then treeMomentOne n (M n) k * K *
            (Real.rpow (k : ℝ) 3 / (n : ℝ) ^ 2) else 0 := hbase
    _ ≤ (K * C / n) *
        (∑' j : ℕ, Real.rpow ((j + 1 : ℕ) : ℝ) (1 / 2 : ℝ) *
          Real.exp (-u * (j + 1))) := by
      apply sum_range_le_tsum_succ _ _ _ n (by positivity) (by simp)
        (fun j => by simp only [Real.rpow_eq_pow]; positivity) (hsum u hu0 hun).1
      intro j hj
      let k := j + 1
      change (if 3 ≤ k ∧ k < largeCutoff n then _ else _) ≤ _
      split_ifs with hgood
      · have ht := htree n (M n) k hnT hMn hdnlo hdnhi (by omega)
        have hkpos : 0 < (k : ℝ) := by dsimp [k]; positivity
        have hnpos : 0 < (n : ℝ) := by positivity
        have hrpow : Real.rpow (k : ℝ) (-5 / 2 : ℝ) *
            Real.rpow (k : ℝ) 3 = Real.rpow (k : ℝ) (1 / 2 : ℝ) := by
          simp only [Real.rpow_eq_pow]
          rw [← Real.rpow_add hkpos]
          norm_num
        have hd : (degreeAt n (M n) - 1) ^ 2 = epsilon M n ^ 2 := by
          simp [epsilon, degree, degreeAt, sq_abs]
        have hexp : Real.exp (-kappa *
            ((degreeAt n (M n) - 1) ^ 2 * k +
              (k : ℝ) ^ 3 / (n : ℝ) ^ 2)) ≤ Real.exp (-u * k) := by
          apply Real.exp_le_exp.mpr
          rw [hd]
          dsimp [u]
          have hnn : 0 ≤ (k : ℝ) ^ 3 / (n : ℝ) ^ 2 := by positivity
          nlinarith
        calc
          treeMomentOne n (M n) k * K *
              (Real.rpow (k : ℝ) 3 / (n : ℝ) ^ 2) ≤
            (C * n * Real.rpow (k : ℝ) (-5 / 2 : ℝ) *
              Real.exp (-kappa * ((degreeAt n (M n) - 1) ^ 2 * k +
                (k : ℝ) ^ 3 / (n : ℝ) ^ 2))) * K *
              (Real.rpow (k : ℝ) 3 / (n : ℝ) ^ 2) := by gcongr <;> simp only [Real.rpow_eq_pow] <;> positivity
          _ = (K * C / n) * (Real.rpow (k : ℝ) (1 / 2 : ℝ) *
              Real.exp (-kappa * ((degreeAt n (M n) - 1) ^ 2 * k +
                (k : ℝ) ^ 3 / (n : ℝ) ^ 2))) := by
            calc
              _ = (K * C / n) *
                  (Real.rpow (k : ℝ) (-5 / 2 : ℝ) * Real.rpow (k : ℝ) 3) *
                  Real.exp (-kappa * ((degreeAt n (M n) - 1) ^ 2 * k +
                    (k : ℝ) ^ 3 / (n : ℝ) ^ 2)) := by
                field_simp [hnpos.ne']
                <;> ring
              _ = _ := by rw [hrpow]; ring
          _ ≤ (K * C / n) * (Real.rpow (k : ℝ) (1 / 2 : ℝ) *
              Real.exp (-u * k)) := by gcongr <;> simp only [Real.rpow_eq_pow] <;> positivity
          _ = _ := by simp only [k, Nat.cast_add, Nat.cast_one]
      · simp only [Real.rpow_eq_pow]
        positivity
    _ ≤ (K * C / n) * (S * Real.rpow u (-3 / 2 : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      convert (hsum u hu0 hun).2 using 1 <;> congr 2 <;> ring
    _ = D * (widthParameter M n)⁻¹ := by
      dsimp [D, u, widthParameter]
      have hn0 : (n : ℝ) ≠ 0 := by positivity
      have he0 : epsilon M n ≠ 0 := hen.ne'
      rw [Real.mul_rpow hkappa.le (sq_nonneg _)]
      have hp : (epsilon M n ^ 2) ^ (-3 / 2 : ℝ) =
          (epsilon M n ^ 3)⁻¹ := by
        rw [← Real.rpow_two, ← Real.rpow_mul hen.le]
        norm_num [Real.rpow_neg, Real.rpow_ofNat]
      rw [hp]
      field_simp [hn0, he0]
      <;> ring
    _ ≤ max 1 D * (widthParameter M n)⁻¹ := by
      exact mul_le_mul_of_nonneg_right (le_max_right _ _) (by
        unfold widthParameter
        positivity)

/- The entire barely-critical clause of the cyclic structure contract. -/
end
end Erdos745.WrapUp.Proofs.Internal.W08_CYCLIC_Complex


namespace Erdos745.WrapUp.Proofs.Internal.W08_CYCLIC_Complex

noncomputable section
open Filter
open scoped BigOperators Topology
open Erdos745.WrapUp.Proofs.Internal.W08_CYCLIC_Finite
open Erdos745.WrapUp.Proofs.Internal.W08_CYCLIC_Analytic
open Erdos745.WrapUp.Proofs.Internal.W08_CYCLIC_Bounds
open Erdos745.WrapUp.Proofs.Internal.W08_CYCLIC_Cutoff
open Erdos745.WrapUp.Proofs.Internal.W08_CYCLIC_FixedLocal
open Erdos745.WrapUp.Proofs.Internal.W08_CYCLIC_Near
open Erdos745.WrapUp.Proofs.W06_POISSON

lemma bounded_degree_complement_ratio
    {n M k : ℕ} {U : ℝ} (hU : 1 ≤ U)
    (hn : 32 * (U + 1) ≤ (n : ℝ)) (hM : (M : ℝ) ≤ U * n)
    (hkhalf : k ≤ n / 2) :
    M - k + 1 ≤ (n - k).choose 2 ∧
    (((M - k + 1 : ℕ) : ℝ) /
      (((n - k).choose 2 - (M - k + 1) + 1 : ℕ) : ℝ)) ≤
        (32 * (U + 1)) / n := by
  let t := n - k
  let s := M - k + 1
  have hn1 : (1 : ℝ) ≤ n := by linarith
  have hnpos : (0 : ℝ) < n := by linarith
  have hn4 : 4 ≤ n := by exact_mod_cast (show (4 : ℝ) ≤ n by linarith)
  have ht2 : 2 ≤ t := by dsimp [t]; omega
  have hnt : n ≤ 2 * t := by dsimp [t]; omega
  have htR : (2 : ℝ) ≤ t := by exact_mod_cast ht2
  have hntR : (n : ℝ) ≤ 2 * t := by exact_mod_cast hnt
  have hQ : ((t.choose 2 : ℕ) : ℝ) = t * (t - 1) / 2 := by
    rw [Nat.cast_choose_two]
  have hQlarge : (n : ℝ) ^ 2 ≤ 16 * (t.choose 2 : ℝ) := by
    rw [hQ]
    nlinarith [mul_nonneg (show 0 ≤ 2 * (t : ℝ) - n by linarith)
      (show 0 ≤ 2 * (t : ℝ) + n by positivity),
      mul_nonneg (show 0 ≤ (t : ℝ) by positivity) (show 0 ≤ (t : ℝ) - 2 by linarith)]
  have hsM : (s : ℝ) ≤ M + 1 := by
    exact_mod_cast (show s ≤ M + 1 by dsimp [s]; omega)
  have hs : (s : ℝ) ≤ (U + 1) * n := by nlinarith
  have hquad : 32 * ((U + 1) * n) ≤ (n : ℝ) ^ 2 := by
    nlinarith [mul_nonneg hnpos.le (sub_nonneg.mpr hn)]
  have hsQ : s ≤ t.choose 2 := by
    exact_mod_cast (show (s : ℝ) ≤ (t.choose 2 : ℝ) by nlinarith)
  have hdenlower : (n : ℝ) ^ 2 ≤ 32 * ((t.choose 2 : ℝ) - s + 1) := by
    nlinarith
  have hden : (0 : ℝ) < (t.choose 2 - s + 1 : ℕ) := by positivity
  have hcast : ((t.choose 2 - s + 1 : ℕ) : ℝ) =
      (t.choose 2 : ℝ) - s + 1 := by
    rw [Nat.cast_add, Nat.cast_sub hsQ]
    norm_num
  refine ⟨hsQ, ?_⟩
  change (s : ℝ) / (t.choose 2 - s + 1 : ℕ) ≤ (32 * (U + 1)) / n
  apply (div_le_div_iff₀ hden hnpos).2
  rw [hcast]
  have h1 := mul_le_mul_of_nonneg_right hs hnpos.le
  have h2 := mul_le_mul_of_nonneg_left hdenlower (show 0 ≤ U + 1 by linarith)
  nlinarith

private lemma sum_Icc_le_tsum_shift (f : ℕ → ℝ) (N : ℕ)
    (hf : ∀ r, 0 ≤ f r) (hs : Summable f) :
    (∑ r ∈ Finset.Icc 1 N, f r) ≤ ∑' j : ℕ, f (j + 1) := by
  have hset : (Finset.range N).image (fun j => j + 1) = Finset.Icc 1 N := by
    ext r
    simp only [Finset.mem_image, Finset.mem_range, Finset.mem_Icc]
    constructor
    · rintro ⟨j, hj, rfl⟩
      omega
    · intro hr
      exact ⟨r - 1, by omega, by omega⟩
  rw [← hset, Finset.sum_image (by intro a _ b _ hab; exact Nat.add_right_cancel hab)]
  exact ((summable_nat_add_iff 1).2 hs).sum_le_tsum _ (fun j _ => hf (j + 1))

lemma excess_sum_le_tree_compact
    (hF : FiniteEnumerationStatement) (A c : ℝ) (hA : 1 < A) (hc : 0 < c)
    (hbound : ∀ k r : ℕ, 0 < k → 0 < r →
      (connectedCount k (k + r) : ℝ) ≤ A ^ r *
        Real.rpow (r : ℝ) (-(r : ℝ) / 2) *
        Real.rpow (k : ℝ) ((k : ℝ) + (3 * (r : ℝ) - 1) / 2))
    {n M k : ℕ} (hM : M ≤ capacity n) (hn : 0 < n) (hk : 3 ≤ k)
    (hkn : k ≤ n)
    (hratio : (((M - k + 1 : ℕ) : ℝ) /
      (((n - k).choose 2 - (M - k + 1) + 1 : ℕ) : ℝ)) ≤ c / n)
    (hsQ : M - k + 1 ≤ (n - k).choose 2)
    (hy : Real.rpow (k : ℝ) (3 / 2 : ℝ) / n ≤ 2) :
    (∑ r ∈ Finset.Icc 1 (capacity k), excessFormula n M k r) ≤
      treeMomentOne n M k *
        (c ^ 2 * A * excessKernelConstant (c * A)) *
        (Real.rpow (k : ℝ) (3 : ℝ) / (n : ℝ) ^ 2) := by
  let y : ℝ := Real.rpow (k : ℝ) (3 / 2 : ℝ) / n
  have hy0 : 0 ≤ y := by dsimp [y]; positivity
  have hD : 0 ≤ c * A := by positivity
  have hseries := excess_series_le (c * A) y hD hy0 hy
  have htree0 : 0 ≤ treeMomentOne n M k := by
    exact Erdos745.WrapUp.Proofs.W06_POISSON.tupleMoment_nonneg n M 1 (fun _ => k)
  have hterm : ∀ r ∈ Finset.Icc 1 (capacity k),
      excessFormula n M k r ≤
        treeMomentOne n M k * (c * y) *
          ((c * A * y) ^ r *
            Real.rpow (r : ℝ) (-(r : ℝ) / 2)) := by
    intro r hr
    have hrpos : 0 < r := (Finset.mem_Icc.mp hr).1
    by_cases hfeas : k + r ≤ M
    · have hc := component_ratio_excess_of_bound hF A hA hbound hM hk hrpos
        hkn hfeas hsQ
      have hkpos : 0 < (k : ℝ) := by positivity
      have hnpos : 0 < (n : ℝ) := by positivity
      have hkrpow : Real.rpow (k : ℝ) ((3 * (r : ℝ) + 3) / 2) =
          Real.rpow (k : ℝ) (3 / 2 : ℝ) ^ (r + 1) := by
        have hp := Real.rpow_mul_natCast hkpos.le (3 / 2 : ℝ) (r + 1)
        calc
          Real.rpow (k : ℝ) ((3 * (r : ℝ) + 3) / 2) =
              Real.rpow (k : ℝ) ((3 / 2 : ℝ) * (r + 1)) := by
                congr 1
                push_cast
                ring
          _ = Real.rpow (k : ℝ) (3 / 2 : ℝ) ^ (r + 1) := by
                simpa only [Real.rpow_eq_pow, Nat.cast_add, Nat.cast_one] using! hp
      calc
        excessFormula n M k r ≤ treeMomentOne n M k *
            (A ^ r * Real.rpow (r : ℝ) (-(r : ℝ) / 2) *
              Real.rpow (k : ℝ) ((3 * (r : ℝ) + 3) / 2)) *
            (((M - k + 1 : ℕ) : ℝ) /
              (((n - k).choose 2 - (M - k + 1) + 1 : ℕ) : ℝ)) ^ (r + 1) := hc
        _ ≤ treeMomentOne n M k *
            (A ^ r * Real.rpow (r : ℝ) (-(r : ℝ) / 2) *
              Real.rpow (k : ℝ) ((3 * (r : ℝ) + 3) / 2)) *
            (c / n) ^ (r + 1) := by
          gcongr
          exact mul_nonneg htree0 (mul_nonneg (mul_nonneg (pow_nonneg (by linarith : 0 ≤ A) r)
            (Real.rpow_nonneg (by positivity) _)) (Real.rpow_nonneg hkpos.le _))
        _ = treeMomentOne n M k * (c * y) *
            ((c * A * y) ^ r * Real.rpow (r : ℝ) (-(r : ℝ) / 2)) := by
          rw [hkrpow]
          dsimp [y]
          rw [pow_succ, pow_succ, mul_pow, mul_pow]
          field_simp [ne_of_gt hnpos]
          ring
    · have hz : excessFormula n M k r = 0 := by
        unfold excessFormula componentFormula
        simp [Nat.lt_of_not_ge hfeas]
      rw [hz]
      exact mul_nonneg (mul_nonneg htree0 (mul_nonneg hc.le hy0))
        (mul_nonneg (pow_nonneg (mul_nonneg hD hy0) r)
          (Real.rpow_nonneg (by positivity) _))
  calc
    (∑ r ∈ Finset.Icc 1 (capacity k), excessFormula n M k r) ≤
        ∑ r ∈ Finset.Icc 1 (capacity k),
          treeMomentOne n M k * (c * y) *
            ((c * A * y) ^ r * Real.rpow (r : ℝ) (-(r : ℝ) / 2)) :=
      Finset.sum_le_sum hterm
    _ ≤ treeMomentOne n M k * (c * y) *
        (∑' j : ℕ, (c * A * y) ^ (j + 1) *
          Real.rpow ((j + 1 : ℕ) : ℝ) (-((j + 1 : ℕ) : ℝ) / 2)) := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left
        (sum_Icc_le_tsum_shift _ _ (fun r =>
          mul_nonneg (pow_nonneg (mul_nonneg hD hy0) r)
            (Real.rpow_nonneg (by positivity) _)) hseries.1)
        (mul_nonneg htree0 (mul_nonneg hc.le hy0))
    _ ≤ treeMomentOne n M k * (c * y) *
        (y * (c * A) * excessKernelConstant (c * A)) :=
      mul_le_mul_of_nonneg_left hseries.2
        (mul_nonneg htree0 (mul_nonneg hc.le hy0))
    _ = treeMomentOne n M k *
        (c ^ 2 * A * excessKernelConstant (c * A)) *
        (Real.rpow (k : ℝ) 3 / (n : ℝ) ^ 2) := by
      dsimp [y]
      have hk0 : 0 ≤ (k : ℝ) := by positivity
      have hp : (k : ℝ) ^ (3 : ℝ) = ((k : ℝ) ^ (3 / 2 : ℝ)) ^ (2 : ℕ) := by
        have ht := Real.rpow_mul_natCast hk0 (3 / 2 : ℝ) 2
        norm_num at ht
        simpa only [Real.rpow_ofNat] using ht
      simp only [Real.rpow_ofNat] at hp ⊢
      rw [hp]
      ring

lemma small_complex_sum_bound_compact
    (hF : FiniteEnumerationStatement) (A c K : ℝ) (hA : 1 < A) (hc : 0 < c) (hK : 0 < K)
    (hKeq : K = c ^ 2 * A * excessKernelConstant (c * A))
    (hbound : ∀ k r : ℕ, 0 < k → 0 < r →
      (connectedCount k (k + r) : ℝ) ≤ A ^ r *
        Real.rpow (r : ℝ) (-(r : ℝ) / 2) *
        Real.rpow (k : ℝ) ((k : ℝ) + (3 * (r : ℝ) - 1) / 2))
    {n M : ℕ} (hn : 0 < n) (hM : M ≤ capacity n)
    (hratios : ∀ k, 3 ≤ k → k < largeCutoff n → k ≤ M →
      M - k + 1 ≤ (n - k).choose 2 ∧
      (((M - k + 1 : ℕ) : ℝ) /
        (((n - k).choose 2 - (M - k + 1) + 1 : ℕ) : ℝ)) ≤ c / n)
    (hcut : ∀ k, k < largeCutoff n → k ≤ n / 2 ∧
      Real.rpow (k : ℝ) (3 / 2 : ℝ) / n ≤ 2) :
    expectM n M (fun G => (smallComplexCount G (largeCutoff n) : ℝ)) ≤
      ∑ k ∈ Finset.range (n + 1),
        if 3 ≤ k ∧ k < largeCutoff n then
          treeMomentOne n M k * K *
            (Real.rpow (k : ℝ) 3 / (n : ℝ) ^ 2) else 0 := by
  rw [expect_smallComplexCount_eq hF hM]
  apply Finset.sum_le_sum
  intro k hk
  by_cases hgood : 3 ≤ k ∧ k < largeCutoff n
  · simp only [if_pos hgood, if_pos hgood.2]
    by_cases hkM : k ≤ M
    · obtain ⟨hsQ, hratio⟩ := hratios k hgood.1 hgood.2 hkM
      have hkhalf := (hcut k hgood.2).1
      have hsum := excess_sum_le_tree_compact hF A c hA hc hbound hM hn
        hgood.1 (Nat.le_of_lt_succ (Finset.mem_range.mp hk)) hratio hsQ
        (hcut k hgood.2).2
      rw [excess_sum_capacity_eq (Nat.le_of_lt_succ (Finset.mem_range.mp hk))]
      simpa only [hKeq] using! hsum
    · have hz : ∀ r, excessFormula n M k r = 0 := by
        intro r
        unfold excessFormula componentFormula
        have : M < k + r := by omega
        simp [this]
      simp only [hz, Finset.sum_const_zero]
      have ht0 := Erdos745.WrapUp.Proofs.W06_POISSON.tupleMoment_nonneg
        n M 1 (fun _ => k)
      change 0 ≤ treeMomentOne n M k at ht0
      simp only [Real.rpow_eq_pow]
      positivity
  · by_cases hkh : k < largeCutoff n
    · have hklt : k < 3 := by omega
      simp only [if_neg hgood, if_pos hkh]
      apply le_of_eq
      apply Finset.sum_eq_zero
      intro r hr
      have hz : connectedCount k (k + r) = 0 := by
        classical
        by_cases hk0 : k = 0
        · subst k
          simp [connectedCount]
        · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
          have hmax : Fintype.card (Edge k) < k := by
            interval_cases k <;> decide
          have hempty : fixedGraphs k (k + r) = ∅ := by
            apply Finset.eq_empty_iff_forall_notMem.mpr
            intro G hG
            have hc := (Finset.mem_filter.mp hG).2
            have hle := Finset.card_le_univ G
            omega
          simp [connectedCount, hempty]
      unfold excessFormula componentFormula
      split_ifs <;> simp [hz]
    · simp [hkh]

lemma weighted_small_tree_sum_bound
    {n M : ℕ} {K D a B : ℝ} (hn : 0 < n) (hK : 0 < K)
    (hD : 0 < D) (ha : 0 < a)
    (hlocal : ∀ k, k ≤ n → 0 < k → (k : ℝ) ≤ B * Real.log n →
      treeMomentOne n M k ≤ D * n * ((k : ℝ) ^ (-5 / 2 : ℝ)) *
        Real.exp (-a * k))
    (hcut : ∀ k, k < largeCutoff n →
      ((k : ℝ) ^ (3 / 2 : ℝ)) / n ≤ 2) :
    (∑ k ∈ Finset.range (n + 1),
      if 3 ≤ k ∧ k < largeCutoff n then treeMomentOne n M k * K *
        (((k : ℝ) ^ (3 : ℝ)) / (n : ℝ) ^ 2) else 0) ≤
      (K * D / n) * (∑' k : ℕ, (k : ℝ) * Real.exp (-a * k)) +
        (4 * K) * treeTailOne n M 0 B := by
  classical
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  let g : ℕ → ℝ := fun k => (k : ℝ) * Real.exp (-a * k)
  let t : ℕ → ℝ := fun k =>
    if 0 < k ∧ B * Real.log n < (k : ℝ) then treeMomentOne n M k else 0
  have hg : ∀ k, 0 ≤ g k := by intro k; dsimp [g]; positivity
  have ht : ∀ k, 0 ≤ t k := by
    intro k
    dsimp [t]
    split_ifs
    · exact tupleMoment_nonneg n M 1 (fun _ => k)
    · positivity
  have hs : Summable g := by
    simpa [g] using! Real.summable_pow_mul_exp_neg_nat_mul 1 ha
  have hpoint : ∀ k ∈ Finset.range (n + 1),
      (if 3 ≤ k ∧ k < largeCutoff n then treeMomentOne n M k * K *
        (((k : ℝ) ^ (3 : ℝ)) / (n : ℝ) ^ 2) else 0) ≤
      (K * D / n) * g k + (4 * K) * t k := by
    intro k hk
    have ht0 : 0 ≤ treeMomentOne n M k := tupleMoment_nonneg n M 1 (fun _ => k)
    by_cases hgood : 3 ≤ k ∧ k < largeCutoff n
    · rw [if_pos hgood]
      have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
      have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
      by_cases hsmall : (k : ℝ) ≤ B * Real.log n
      · have hl := hlocal k hkn (by omega) hsmall
        have hp : ((k : ℝ) ^ (-5 / 2 : ℝ)) * ((k : ℝ) ^ (3 : ℝ)) ≤ k := by
          calc
            ((k : ℝ) ^ (-5 / 2 : ℝ)) * ((k : ℝ) ^ (3 : ℝ)) =
                ((k : ℝ) ^ (1 / 2 : ℝ)) := by
              rw [← Real.rpow_add hkpos]
              norm_num
            _ ≤ ((k : ℝ) ^ (1 : ℝ)) :=
              Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ k by omega))
                (by norm_num)
            _ = k := Real.rpow_one _
        have hb : treeMomentOne n M k * K *
            (((k : ℝ) ^ (3 : ℝ)) / (n : ℝ) ^ 2) ≤ (K * D / n) * g k := by
          calc
            treeMomentOne n M k * K * (((k : ℝ) ^ (3 : ℝ)) / (n : ℝ) ^ 2) ≤
                (D * n * ((k : ℝ) ^ (-5 / 2 : ℝ)) * Real.exp (-a * k)) *
                  K * (((k : ℝ) ^ (3 : ℝ)) / (n : ℝ) ^ 2) := by gcongr
            _ = (K * D / n * Real.exp (-a * k)) *
                (((k : ℝ) ^ (-5 / 2 : ℝ)) * ((k : ℝ) ^ (3 : ℝ))) := by
              field_simp [hnpos.ne'] <;> ring
            _ ≤ (K * D / n * Real.exp (-a * k)) * k := by gcongr
            _ = (K * D / n) * g k := by dsimp [g]; ring
        exact hb.trans (le_add_of_nonneg_right (mul_nonneg (by positivity) (ht k)))
      · have hfar : 0 < k ∧ B * Real.log n < (k : ℝ) := ⟨by omega, lt_of_not_ge hsmall⟩
        have hy := hcut k hgood.2
        have hy0 : 0 ≤ ((k : ℝ) ^ (3 / 2 : ℝ)) := Real.rpow_nonneg hkpos.le _
        have hy' := (div_le_iff₀ hnpos).1 hy
        have hp : ((k : ℝ) ^ (3 : ℝ)) / (n : ℝ) ^ 2 ≤ 4 := by
          apply (div_le_iff₀ (sq_pos_of_pos hnpos)).2
          have hp : (k : ℝ) ^ (3 : ℝ) = ((k : ℝ) ^ (3 / 2 : ℝ)) ^ (2 : ℕ) := by
            calc
              (k : ℝ) ^ (3 : ℝ) = (k : ℝ) ^ ((3 / 2 : ℝ) * (2 : ℕ)) := by
                congr 1
                norm_num
              _ = _ := Real.rpow_mul_natCast hkpos.le (3 / 2 : ℝ) 2
          rw [hp]
          nlinarith
        have hb : treeMomentOne n M k * K *
            (((k : ℝ) ^ (3 : ℝ)) / (n : ℝ) ^ 2) ≤ (4 * K) * t k := by
          dsimp [t]
          rw [if_pos hfar]
          nlinarith [mul_le_mul_of_nonneg_left hp (mul_nonneg ht0 hK.le)]
        exact hb.trans (le_add_of_nonneg_left (mul_nonneg (by positivity) (hg k)))
    · rw [if_neg hgood]
      exact add_nonneg (mul_nonneg (by positivity) (hg k))
        (mul_nonneg (by positivity) (ht k))
  have htail : (∑ k ∈ Finset.range (n + 1), t k) = treeTailOne n M 0 B := by
    simpa only [treeTailOne, t, pow_zero, one_mul] using!
      (Fin.sum_univ_eq_sum_range t (n + 1)).symm
  calc
    _ ≤ ∑ k ∈ Finset.range (n + 1), ((K * D / n) * g k + (4 * K) * t k) :=
      Finset.sum_le_sum hpoint
    _ = (K * D / n) * (∑ k ∈ Finset.range (n + 1), g k) +
        (4 * K) * treeTailOne n M 0 B := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, htail]
    _ ≤ _ := by
      gcongr
      exact hs.sum_le_tsum _ (fun k _ => hg k)

end
end Erdos745.WrapUp.Proofs.Internal.W08_CYCLIC_Complex


namespace Erdos745.WrapUp.Proofs.Internal.W08_CYCLIC_Complex

noncomputable section
open Filter
open scoped BigOperators Topology
open Erdos745.WrapUp.Proofs.Internal.W08_CYCLIC_Finite
open Erdos745.WrapUp.Proofs.Internal.W08_CYCLIC_Analytic
open Erdos745.WrapUp.Proofs.Internal.W08_CYCLIC_Cutoff
open Erdos745.WrapUp.Proofs.Internal.W08_CYCLIC_FixedLocal
open Erdos745.WrapUp.Proofs.W06_POISSON

lemma fixed_small_complex_bounded
    (hF : FiniteEnumerationStatement) (hKern : KernelBoundStatement)
    (hRate : RateStatement) (hT : TupleEstimatesStatement)
    (M : NatSeq) (lam : ℝ) (hadm : admissible M) (hlam : 0 < lam)
    (hlam1 : lam ≠ 1) (hdeg : Tendsto (degree M) atTop (𝓝 lam)) :
    boundedBy (fun n => expectM n (M n)
      (fun G => (smallComplexCount G (largeCutoff n) : ℝ)))
      (fun n => (n : ℝ)⁻¹) := by
  obtain ⟨A, hAone, hKbound⟩ := hKern
  obtain ⟨lo, hi, a0, hlo, hlohi, ha0, hcompact⟩ :=
    fixed_compact_data hRate hlam hlam1 hdeg
  let U := max 1 hi
  let c := 32 * (U + 1)
  let K := c ^ 2 * A * excessKernelConstant (c * A)
  have hU : 1 ≤ U := le_max_left _ _
  have hc : 0 < c := by dsimp [c]; linarith
  have hK : 0 < K := mul_pos (mul_pos (sq_pos_of_pos hc) (by linarith))
    (excessKernelConstant_pos _)
  let delta := |lam - 1| / 2
  have habs : 0 < |lam - 1| := abs_pos.mpr (sub_ne_zero.mpr hlam1)
  have hdelta : 0 < delta := by dsimp [delta]; positivity
  have hsep : ∀ᶠ n in atTop, delta ≤ |degree M n - 1| := by
    have ht : Tendsto (fun n => |degree M n - 1|) atTop (𝓝 |lam - 1|) := by
      simpa using! (hdeg.sub_const 1).abs
    exact ((tendsto_order.1 ht).1 delta (by dsimp [delta]; linarith)).mono fun _ h => h.le
  obtain ⟨B, hB, nTail, htail⟩ :=
    hT.2.2.2 lo hi delta 2 1 0 hlo hlohi hdelta (by norm_num) (by omega)
  obtain ⟨D, a, hD, ha, nLocal, hlocal⟩ :=
    fixed_local_tree_bound hT hRate hlam hlam1 hB hadm hdeg
  let S := ∑' k : ℕ, (k : ℝ) * Real.exp (-a * k)
  have hS : 0 ≤ S := tsum_nonneg (fun k => by positivity)
  let C0 := K * D * S + 4 * K
  have hC0 : 0 < C0 := by dsimp [C0]; positivity
  refine ⟨C0, hC0, ?_⟩
  have hnlarge : ∀ᶠ n : ℕ in atTop, c ≤ (n : ℝ) :=
    (tendsto_atTop.1 tendsto_natCast_atTop_atTop) c
  filter_upwards [hadm, hcompact, hsep, cutoff_geometry, hnlarge,
    eventually_ge_atTop (max 1 (max nTail nLocal))] with n hMn hcomp hsepn hgeo hnc hn
  have hnpos : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hMnU : (M n : ℝ) ≤ U * n := by
    have hdeghi : degree M n ≤ U := hcomp.2.1.trans (le_max_right _ _)
    unfold degree at hdeghi
    have h := (div_le_iff₀ hnR).1 hdeghi
    have hM0 : (0 : ℝ) ≤ M n := by positivity
    linarith
  have hratios := fun k (_ : 3 ≤ k) (hkcut : k < largeCutoff n) (_ : k ≤ M n) =>
    bounded_degree_complement_ratio hU hnc hMnU (hgeo.2 k hkcut).1
  have hbase := small_complex_sum_bound_compact hF A c K hAone hc hK rfl hKbound
    hnpos hMn hratios hgeo.2
  have hsum := weighted_small_tree_sum_bound hnpos hK hD ha
    (fun k hk hkpos hklog => hlocal n k (by omega) hk hkpos hklog)
    (fun k hk => (hgeo.2 k hk).2)
  have hfar : treeTailOne n (M n) 0 B ≤ Real.rpow (n : ℝ) (-2) := by
    rw [← tupleTail_one_eq]
    exact htail n (M n) (by omega) hMn hcomp.1 hcomp.2.1 hsepn
  have hpow : Real.rpow (n : ℝ) (-2) ≤ (n : ℝ)⁻¹ := by
    simp only [Real.rpow_eq_pow]
    rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num, Real.rpow_neg hnR.le, Real.rpow_two]
    apply inv_anti₀ hnR
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hnpos
    nlinarith
  change |expectM n (M n) (fun G => (smallComplexCount G (largeCutoff n) : ℝ))| ≤
    C0 * (n : ℝ)⁻¹
  rw [abs_of_nonneg (expect_smallComplexCount_nonneg n (M n) (largeCutoff n))]
  calc
    _ ≤ (K * D / n) * S + (4 * K) * treeTailOne n (M n) 0 B := hbase.trans hsum
    _ ≤ (K * D / n) * S + (4 * K) * (n : ℝ)⁻¹ := by
      gcongr
      exact hfar.trans hpow
    _ = C0 * (n : ℝ)⁻¹ := by dsimp [C0]; ring

end
end Erdos745.WrapUp.Proofs.Internal.W08_CYCLIC_Complex
