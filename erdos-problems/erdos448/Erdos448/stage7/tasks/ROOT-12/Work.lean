module

import all Mathlib.Basic.Real.Basic
import all Mathlib.Analysis.Normed.Group.Real
public import Erdos448.stage6.TaskContracts

public section

set_option backward.isDefEq.respectTransparency false

namespace Erdos448.Stage7.ROOT12.Work

open Filter Finset Set Asymptotics
open scoped BigOperators Topology

open Erdos448.Stage4
open Erdos448.Stage4.Contracts
open Erdos448.Stage6.TaskContracts

noncomputable section

lemma safeLog_nonneg (t : ℝ) : 0 ≤ safeLog t := by
  unfold safeLog
  exact le_trans zero_le_one (le_max_left _ _)

lemma rpow_add_pos {x : ℝ} (hx : 0 < x) (a b : ℝ) :
    x.rpow (a + b) = x.rpow a * x.rpow b :=
  Real.rpow_add hx a b

lemma rpow_mul_nonneg {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (x * y).rpow z = x.rpow z * y.rpow z := by
  change (x * y) ^ z = x ^ z * y ^ z
  exact Real.mul_rpow hx hy

lemma rpow_div_nonneg {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (x / y).rpow z = x.rpow z / y.rpow z := by
  change (x / y) ^ z = x ^ z / y ^ z
  exact Real.div_rpow hx hy z

lemma rpow_neg_nonneg {x z : ℝ} (hx : 0 ≤ x) :
    x.rpow (-z) = (x.rpow z)⁻¹ := by
  change x ^ (-z) = (x ^ z)⁻¹
  exact Real.rpow_neg hx z

@[expose] def localP4Parameters
    (q : P102Parameters) (sigma xi : ℝ)
    (hsigma : q.theta ≤ sigma) (hxi : 1 < xi) : Lemma4Parameters :=
  { epsilonInt := q.epsilonInt
    epsilonInt_pos := q.epsilonInt_pos
    epsilonInt_le_tenth := q.epsilonInt_le_tenth
    xi := xi
    xi_gt_one := hxi
    sigma := sigma
    sigma_ge_two := q.theta_ge_two.trans hsigma
    theta := q.theta
    theta_ge_two := q.theta_ge_two
    sigma_ge_theta := hsigma }

@[expose] def localMean
    (q : P102Parameters) (sigma xi x : ℝ)
    (hsigma : q.theta ≤ sigma) (hxi : 1 < xi) : ℝ :=
  let l4 := localP4Parameters q sigma xi hsigma hxi
  ∑ n ∈ positiveNatsBelow x,
    if hn : 0 < n then normalizedClosePair l4 ⟨n, hn⟩ else 0

@[expose] def localTail
    (q : P102Parameters) (sigma xi x : ℝ)
    (hsigma : q.theta ≤ sigma) (hxi : 1 < xi) : ℝ :=
  let l4 := localP4Parameters q sigma xi hsigma hxi
  let U0 := Real.exp (Real.log xi * Real.log sigma)
  ∑ n ∈ positiveNatsBelow x,
    if hn : 0 < n then
      if U0 < n then normalizedClosePair l4 ⟨n, hn⟩ else 0
    else 0

@[expose] def localInitial
    (q : P102Parameters) (sigma xi x : ℝ)
    (hsigma : q.theta ≤ sigma) (hxi : 1 < xi) : ℝ :=
  let l4 := localP4Parameters q sigma xi hsigma hxi
  let U0 := Real.exp (Real.log xi * Real.log sigma)
  ∑ n ∈ positiveNatsBelow x,
    if hn : 0 < n then
      if (n : ℝ) ≤ U0 then normalizedClosePair l4 ⟨n, hn⟩ else 0
    else 0

@[expose] def initialConstant
    (q : P102Parameters) (sigma xi : ℝ)
    (hsigma : q.theta ≤ sigma) (hxi : 1 < xi) : ℝ :=
  let l4 := localP4Parameters q sigma xi hsigma hxi
  let U0 := Real.exp (Real.log xi * Real.log sigma)
  ∑ n ∈ Finset.range (Nat.ceil U0 + 1),
    if hn : 0 < n then
      if (n : ℝ) ≤ U0 then normalizedClosePair l4 ⟨n, hn⟩ else 0
    else 0

@[expose] def localCutoff (q : P102Parameters) (x : ℝ) (hx : 0 < x) : ℤ :=
  movingCutoff
    { theta := q.theta, theta_ge_two := q.theta_ge_two, x := x, x_pos := hx }

@[expose] def localSharp
    (q : P102Parameters) (sigma : ℝ) (hsigma : q.theta ≤ sigma) (k : ℕ) :
    SharpParameters :=
  { y := q.y, y_pos := q.y_pos, y_lt_one := q.y_lt_one, k := k,
    theta := q.theta, theta_ge_two := q.theta_ge_two,
    sigma := sigma, sigma_ge_theta := hsigma }

@[expose] def localSharpSubject
    (q : P102Parameters) (sigma x : ℝ) (hsigma : q.theta ≤ sigma) (k : ℕ) : ℝ :=
  ∑ n ∈ positiveNatsBelow x,
    if hn : 0 < n then fkSharp (localSharp q sigma hsigma k) ⟨n, hn⟩ else 0

@[expose] def localWeight
    (q : P102Parameters) (sigma : ℝ) (hsigma : q.theta ≤ sigma)
    (k : ℕ) (hk : 1 ≤ k) : WeightParameters :=
  { theta := q.theta, theta_ge_two := q.theta_ge_two,
    y := q.y, y_pos := q.y_pos, y_lt_one := q.y_lt_one,
    k := k, k_pos := hk, sigma := sigma, sigma_ge_theta := hsigma }

@[expose] def localP092
    (q : P102Parameters) (sigma xi x : ℝ)
    (hsigma : q.theta ≤ sigma) (hxi : 1 < xi)
    (hx : Real.exp (Real.log xi * Real.log sigma) < x) : P092Parameters :=
  { epsilonInt := q.epsilonInt
    epsilonInt_pos := q.epsilonInt_pos
    epsilonInt_le_tenth := q.epsilonInt_le_tenth
    xi := xi
    xi_gt_one := hxi
    sigma := sigma
    theta := q.theta
    theta_ge_two := q.theta_ge_two
    sigma_ge_theta := hsigma
    y := q.y
    y_pos := q.y_pos
    y_lt_one := q.y_lt_one
    x := x
    x_gt_U0 := hx }

@[expose] def localMovingLogSum
    (q : P102Parameters) (sigma exponent x : ℝ)
    (hsigma : q.theta ≤ sigma) : ℝ :=
  if hx : 0 < x then
    ∑ k ∈ Finset.Icc (lowerBinIndex sigma q.theta) (localCutoff q x hx).toNat,
      (k : ℝ).rpow ((q.y - 3) / 2 + P102APow q) *
        (safeLog (2 * x * q.theta ^ (1 - (2 : ℤ) * k))).rpow exponent
  else 0

@[expose] def localMainSum
    (q : P102Parameters) (sigma x : ℝ) (hx : 0 < x) : ℝ :=
  ∑ k ∈ Finset.Icc (lowerBinIndex sigma q.theta) (localCutoff q x hx).toNat,
    (k : ℝ).rpow (q.y - 2 + P102APow q)

@[expose] def tailFactor (q : P102Parameters) : ℝ :=
  1 + 1 / (1 - q.y - P102APow q)

@[expose] def scaleFactor (q : P102Parameters) : ℝ :=
  (2 : ℝ).rpow (P102APow q) *
    (1 / 2 : ℝ).rpow (q.y - 1 + P102APow q) *
    (Real.log q.theta).rpow (P102APow q) /
      (Real.log q.theta).rpow (q.y - 1 + P102APow q)

@[expose] def mainCoefficient (q : P102Parameters) (C3 : ℝ) : ℝ :=
  (C3 / q.y) * tailFactor q * scaleFactor q

lemma normalizedClosePair_nonneg
    (l4 : Lemma4Parameters) (n : PosNat) :
    0 ≤ normalizedClosePair l4 n := by
  unfold normalizedClosePair closePairSum
  apply div_nonneg
  · apply mul_nonneg
    · positivity
    · apply Finset.sum_nonneg
      intro d hd
      apply Finset.sum_nonneg
      intro d' hd'
      split_ifs <;> positivity
  · positivity

lemma localMean_eq_tail_add_initial
    (q : P102Parameters) (sigma xi x : ℝ)
    (hsigma : q.theta ≤ sigma) (hxi : 1 < xi) :
    localMean q sigma xi x hsigma hxi =
      localTail q sigma xi x hsigma hxi +
        localInitial q sigma xi x hsigma hxi := by
  classical
  simp only [localMean, localTail, localInitial]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hnpos : 0 < n
  · simp only [hnpos, dite_true]
    by_cases hU : Real.exp (Real.log xi * Real.log sigma) < (n : ℝ)
    · simp [hU, not_le_of_gt hU]
    · simp [hU, le_of_not_gt hU]
  · simp [hnpos]

lemma localInitial_le_constant
    (q : P102Parameters) (sigma xi x : ℝ)
    (hsigma : q.theta ≤ sigma) (hxi : 1 < xi) :
    localInitial q sigma xi x hsigma hxi ≤
      initialConstant q sigma xi hsigma hxi := by
  classical
  unfold localInitial initialConstant
  let U0 := Real.exp (Real.log xi * Real.log sigma)
  let f : ℕ → ℝ := fun n =>
    if hn : 0 < n then if (n : ℝ) ≤ U0 then
      normalizedClosePair (localP4Parameters q sigma xi hsigma hxi) ⟨n, hn⟩ else 0
    else 0
  have hrewrite :
      (∑ n ∈ positiveNatsBelow x,
        if hn : 0 < n then if (n : ℝ) ≤ U0 then
          normalizedClosePair (localP4Parameters q sigma xi hsigma hxi) ⟨n, hn⟩ else 0
        else 0) =
      ∑ n ∈ (positiveNatsBelow x).filter (fun n : ℕ => (n : ℝ) ≤ U0), f n := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hnpos : 0 < n <;> by_cases hnU : (n : ℝ) ≤ U0 <;>
      simp [f, hnpos, hnU]
  rw [hrewrite]
  change (∑ n ∈ (positiveNatsBelow x).filter (fun n : ℕ => (n : ℝ) ≤ U0), f n) ≤
    ∑ n ∈ Finset.range (Nat.ceil U0 + 1), f n
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro n hn
    have hnU : (n : ℝ) ≤ U0 := (Finset.mem_filter.1 hn).2
    have hnceilReal : (n : ℝ) ≤ (Nat.ceil U0 : ℝ) := hnU.trans (Nat.le_ceil U0)
    have hnceil : n ≤ Nat.ceil U0 := by exact_mod_cast hnceilReal
    exact Finset.mem_range.2 (Nat.lt_succ_iff.2 hnceil)
  · intro n hn _
    dsimp [f]
    split_ifs <;> try exact normalizedClosePair_nonneg _ _
    all_goals exact le_rfl

lemma initialConstant_littleO
    (q : P102Parameters) (sigma xi : ℝ)
    (hsigma : q.theta ≤ sigma) (hxi : 1 < xi) :
    (fun _ : ℝ => initialConstant q sigma xi hsigma hxi) =o[atTop]
      (fun x : ℝ => x) := by
  have h := isLittleO_const_id_atTop (initialConstant q sigma xi hsigma hxi)
  rw [isLittleO_iff] at h ⊢
  simpa only [Real.norm_eq_abs, id_eq] using h

lemma lowerBinIndex_pos (sigma theta : ℝ) :
    1 ≤ lowerBinIndex sigma theta := by
  unfold lowerBinIndex
  exact le_max_left _ _

lemma cutoff_support
    (q : P102Parameters) (sigma x : ℝ) (hx : 0 < x) (k : ℕ)
    (hk : k ∈ Finset.Icc (lowerBinIndex sigma q.theta) (localCutoff q x hx).toNat) :
    q.theta ^ (2 * k - 1) < x := by
  have hkpos : 1 ≤ k := (lowerBinIndex_pos sigma q.theta).trans (Finset.mem_Icc.1 hk).1
  have hcut_nat_pos : 1 ≤ (localCutoff q x hx).toNat :=
    hkpos.trans (Finset.mem_Icc.1 hk).2
  have hcut_nonneg : 0 ≤ localCutoff q x hx := by
    by_contra h
    have hneg : localCutoff q x hx < 0 := lt_of_not_ge h
    have hz : (localCutoff q x hx).toNat = 0 := Int.toNat_of_nonpos hneg.le
    omega
  have hkcut : (k : ℤ) ≤ localCutoff q x hx := by
    rw [← Int.toNat_of_nonneg hcut_nonneg]
    exact_mod_cast (Finset.mem_Icc.1 hk).2
  have hkceil : (k : ℤ) < Int.ceil
      ((1 / 2 : ℝ) * (1 + Real.log x / Real.log q.theta)) := by
    have hkcut' : (k : ℤ) ≤
        Int.ceil ((1 / 2 : ℝ) * (1 + Real.log x / Real.log q.theta)) - 1 := by
      simpa [localCutoff, movingCutoff, movingCutoffReal] using hkcut
    clear hkcut
    omega
  have hkreal : (k : ℝ) <
      (1 / 2 : ℝ) * (1 + Real.log x / Real.log q.theta) := by
    exact Int.lt_ceil.mp hkceil
  have hlogtheta : 0 < Real.log q.theta :=
    Real.log_pos (lt_of_lt_of_le one_lt_two q.theta_ge_two)
  have hexponent : ((2 * k - 1 : ℕ) : ℝ) < Real.log x / Real.log q.theta := by
    rw [Nat.cast_sub (by omega : 1 ≤ 2 * k)]
    norm_num
    nlinarith
  have htheta : 1 < q.theta := lt_of_lt_of_le one_lt_two q.theta_ge_two
  have hpow := Real.rpow_lt_rpow_of_exponent_lt htheta hexponent
  rw [Real.rpow_natCast] at hpow
  have htheta_pos : 0 < q.theta := lt_trans zero_lt_one htheta
  have hrhs : q.theta.rpow (Real.log x / Real.log q.theta) = x := by
    change q.theta ^ (Real.log x / Real.log q.theta) = x
    rw [Real.rpow_def_of_pos htheta_pos]
    have hlog_ne : Real.log q.theta ≠ 0 := ne_of_gt hlogtheta
    congr 1
    field_simp
    exact Real.exp_log hx
  change q.theta ^ (Real.log x / Real.log q.theta) = x at hrhs
  exact hpow.trans_eq hrhs

lemma p3_weighted_bound
    (q : P102Parameters) (C3 sigma x : ℝ) (hsigma : q.theta ≤ sigma)
    (hx : 0 < x)
    (hP3 : ∀ w : WeightParameters, w.theta = q.theta → ∀ z : ℝ,
      w.theta ^ (2 * w.k - 1) < z →
        proposition3Subject w z ≤ (C3 / w.y) * proposition3Envelope w z)
    (k : ℕ)
    (hk : k ∈ Finset.Icc (lowerBinIndex sigma q.theta) (localCutoff q x hx).toNat) :
    (k : ℝ).rpow (P102APow q) *
        localSharpSubject q sigma x hsigma k ≤
      (k : ℝ).rpow (P102APow q) *
        ((C3 / q.y) * proposition3Envelope
          (localWeight q sigma hsigma k
            ((lowerBinIndex_pos sigma q.theta).trans (Finset.mem_Icc.1 hk).1)) x) := by
  change (k : ℝ).rpow (P102APow q) *
      proposition3Subject (localWeight q sigma hsigma k
        ((lowerBinIndex_pos sigma q.theta).trans (Finset.mem_Icc.1 hk).1)) x ≤ _
  apply mul_le_mul_of_nonneg_left
  · exact hP3 _ rfl _ (cutoff_support q sigma x hx k hk)
  · exact Real.rpow_nonneg (by positivity) _

lemma p3_term_identity
    (q : P102Parameters) (C3 sigma x : ℝ) (hsigma : q.theta ≤ sigma)
    (k : ℕ) (hk : 1 ≤ k) :
    (k : ℝ).rpow (P102APow q) *
        ((C3 / q.y) * proposition3Envelope (localWeight q sigma hsigma k hk) x) =
      (C3 / q.y) * x * (Real.log sigma).rpow (-q.y) *
        ((k : ℝ).rpow (q.y - 2 + P102APow q) +
          (k : ℝ).rpow ((q.y - 3) / 2 + P102APow q) *
            (safeLog (2 * x * q.theta ^ (1 - (2 : ℤ) * k))).rpow ((q.y - 1) / 2) +
          (Real.log sigma).rpow (q.y / 2) *
            ((k : ℝ).rpow ((q.y - 3) / 2 + P102APow q) *
              (safeLog (2 * x * q.theta ^ (1 - (2 : ℤ) * k))).rpow (-1 / 2))) := by
  have hkreal : 0 < (k : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
  have hslog : 0 ≤ safeLog (2 * x * q.theta ^ (1 - (2 : ℤ) * k)) := safeLog_nonneg _
  unfold proposition3Envelope proposition3Braces
  have hmain :
      (k : ℝ) ^ (P102APow q) *
          ((k : ℝ) ^ ((q.y - 3) / 2) * (k : ℝ) ^ ((q.y - 1) / 2)) =
        (k : ℝ) ^ (q.y - 2 + P102APow q) := by
    rw [← Real.rpow_add hkreal, ← Real.rpow_add hkreal]
    congr 1
    ring
  have hrest :
      (k : ℝ) ^ (P102APow q) * (k : ℝ) ^ ((q.y - 3) / 2) =
        (k : ℝ) ^ ((q.y - 3) / 2 + P102APow q) := by
    rw [add_comm, Real.rpow_add hkreal]
  have hnegHalf : (-1 / 2 : ℝ) = -(1 / 2 : ℝ) := by ring
  dsimp [localWeight]
  rw [hnegHalf, Real.rpow_neg hslog]
  rw [← hmain, ← hrest]
  ring

lemma p092_ksum_bound
    (q : P102Parameters) (C3 sigma xi x : ℝ)
    (hsigma : q.theta ≤ sigma) (hxi : 1 < xi)
    (hxU : Real.exp (Real.log xi * Real.log sigma) < x)
    (hP3 : ∀ w : WeightParameters, w.theta = q.theta → ∀ z : ℝ,
      w.theta ^ (2 * w.k - 1) < z →
        proposition3Subject w z ≤ (C3 / w.y) * proposition3Envelope w z) :
    P092KSum (localP092 q sigma xi x hsigma hxi hxU) ≤
      (C3 / q.y) * x * (Real.log sigma).rpow (-q.y) *
        (localMainSum q sigma x (Real.exp_pos _ |>.trans hxU) +
          localMovingLogSum q sigma ((q.y - 1) / 2) x hsigma +
          (Real.log sigma).rpow (q.y / 2) *
            localMovingLogSum q sigma (-1 / 2) x hsigma) := by
  classical
  let hx : 0 < x := Real.exp_pos _ |>.trans hxU
  unfold P092KSum
  change (∑ k ∈ Finset.Icc (lowerBinIndex sigma q.theta) (localCutoff q x hx).toNat,
      (k : ℝ).rpow (P102APow q) *
        localSharpSubject q sigma x hsigma k) ≤ _
  calc
    _ ≤ ∑ k ∈ Finset.Icc (lowerBinIndex sigma q.theta) (localCutoff q x hx).toNat,
        (C3 / q.y) * x * (Real.log sigma).rpow (-q.y) *
          ((k : ℝ).rpow (q.y - 2 + P102APow q) +
            (k : ℝ).rpow ((q.y - 3) / 2 + P102APow q) *
              (safeLog (2 * x * q.theta ^ (1 - (2 : ℤ) * k))).rpow ((q.y - 1) / 2) +
            (Real.log sigma).rpow (q.y / 2) *
              ((k : ℝ).rpow ((q.y - 3) / 2 + P102APow q) *
                (safeLog (2 * x * q.theta ^ (1 - (2 : ℤ) * k))).rpow (-1 / 2))) := by
          apply Finset.sum_le_sum
          intro k hk
          calc
            (k : ℝ).rpow (P102APow q) * localSharpSubject q sigma x hsigma k ≤
                (k : ℝ).rpow (P102APow q) *
                  ((C3 / q.y) * proposition3Envelope
                    (localWeight q sigma hsigma k
                      ((lowerBinIndex_pos sigma q.theta).trans (Finset.mem_Icc.1 hk).1)) x) :=
              p3_weighted_bound q C3 sigma x hsigma hx hP3 k hk
            _ = _ := p3_term_identity q C3 sigma x hsigma k
              ((lowerBinIndex_pos sigma q.theta).trans (Finset.mem_Icc.1 hk).1)
    _ = _ := by
      unfold localMainSum localMovingLogSum
      simp only [hx, dite_true]
      rw [← Finset.mul_sum]
      apply congrArg ((C3 / q.y) * x * (Real.log sigma).rpow (-q.y) * ·)
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      rw [Finset.mul_sum]

lemma main_scale_identity
    (q : P102Parameters) (sigma xi : ℝ)
    (hsigma : q.theta ≤ sigma) (hxi : 1 < xi) :
    (2 * Real.log xi * Real.log q.theta / Real.log sigma).rpow (P102APow q) *
        (Real.log sigma).rpow (-q.y) *
        ((1 / 2) * (Real.log sigma / Real.log q.theta)).rpow
          (q.y - 1 + P102APow q) =
      scaleFactor q * (Real.log xi).rpow (P102APow q) *
        (Real.log sigma).rpow (-1) := by
  have htheta : 0 < Real.log q.theta :=
    Real.log_pos (lt_of_lt_of_le one_lt_two q.theta_ge_two)
  have hsigmaLog : 0 < Real.log sigma :=
    Real.log_pos (lt_of_lt_of_le one_lt_two (q.theta_ge_two.trans hsigma))
  have hxiLog : 0 < Real.log xi := Real.log_pos hxi
  have htwo : 0 ≤ (2 : ℝ) := by norm_num
  have hhalf : 0 ≤ (1 / 2 : ℝ) := by norm_num
  have hA :
      (2 * Real.log xi * Real.log q.theta / Real.log sigma).rpow (P102APow q) =
        (2 : ℝ).rpow (P102APow q) *
          (Real.log xi).rpow (P102APow q) *
          (Real.log q.theta).rpow (P102APow q) /
          (Real.log sigma).rpow (P102APow q) := by
    calc
      _ = (2 * Real.log xi * Real.log q.theta).rpow (P102APow q) /
          (Real.log sigma).rpow (P102APow q) :=
        rpow_div_nonneg (mul_nonneg (mul_nonneg htwo hxiLog.le) htheta.le) hsigmaLog.le
      _ = ((2 * Real.log xi).rpow (P102APow q) *
          (Real.log q.theta).rpow (P102APow q)) /
          (Real.log sigma).rpow (P102APow q) := by
        exact congrArg (fun z => z / (Real.log sigma).rpow (P102APow q))
          (rpow_mul_nonneg (mul_nonneg htwo hxiLog.le) htheta.le)
      _ = _ := by
        rw [show (2 * Real.log xi).rpow (P102APow q) =
            (2 : ℝ).rpow (P102APow q) * (Real.log xi).rpow (P102APow q) from
          rpow_mul_nonneg htwo hxiLog.le]
  have hB :
      ((1 / 2) * (Real.log sigma / Real.log q.theta)).rpow
          (q.y - 1 + P102APow q) =
        (1 / 2 : ℝ).rpow (q.y - 1 + P102APow q) *
          (Real.log sigma).rpow (q.y - 1 + P102APow q) /
          (Real.log q.theta).rpow (q.y - 1 + P102APow q) := by
    calc
      _ = (1 / 2 : ℝ).rpow (q.y - 1 + P102APow q) *
          (Real.log sigma / Real.log q.theta).rpow
            (q.y - 1 + P102APow q) :=
        rpow_mul_nonneg hhalf (div_nonneg hsigmaLog.le htheta.le)
      _ = _ := by
        rw [show (Real.log sigma / Real.log q.theta).rpow
              (q.y - 1 + P102APow q) =
            (Real.log sigma).rpow (q.y - 1 + P102APow q) /
              (Real.log q.theta).rpow (q.y - 1 + P102APow q) from
          rpow_div_nonneg hsigmaLog.le htheta.le]
        rw [mul_div_assoc]
  have hsig :
      ((Real.log sigma).rpow (P102APow q))⁻¹ *
          (Real.log sigma).rpow (-q.y) *
          (Real.log sigma).rpow (q.y - 1 + P102APow q) =
        (Real.log sigma).rpow (-1) := by
    calc
      _ = (Real.log sigma).rpow (-P102APow q) *
          (Real.log sigma).rpow (-q.y) *
          (Real.log sigma).rpow (q.y - 1 + P102APow q) := by
        rw [show ((Real.log sigma).rpow (P102APow q))⁻¹ =
            (Real.log sigma).rpow (-P102APow q) from
          (rpow_neg_nonneg (z := P102APow q) hsigmaLog.le).symm]
      _ = (Real.log sigma).rpow
          ((-P102APow q) + (-q.y) + (q.y - 1 + P102APow q)) := by
        rw [← rpow_add_pos hsigmaLog (-P102APow q) (-q.y)]
        rw [← rpow_add_pos hsigmaLog
          ((-P102APow q) + (-q.y)) (q.y - 1 + P102APow q)]
      _ = _ := by congr 1 <;> ring
  rw [hA, hB]
  unfold scaleFactor
  rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
  simp only [one_mul]
  calc
    _ = (2 : ℝ).rpow (P102APow q) *
          ((2 : ℝ)⁻¹).rpow (q.y - 1 + P102APow q) *
          (Real.log q.theta).rpow (P102APow q) *
          ((Real.log q.theta).rpow (q.y - 1 + P102APow q))⁻¹ *
          (Real.log xi).rpow (P102APow q) *
          (((Real.log sigma).rpow (P102APow q))⁻¹ *
            (Real.log sigma).rpow (-q.y) *
            (Real.log sigma).rpow (q.y - 1 + P102APow q)) := by ac_rfl
    _ = _ := by rw [hsig, div_eq_mul_inv]

lemma mainSum_bound
    (q : P102Parameters) (sigma x : ℝ) (hsigma : q.theta ≤ sigma)
    (hx : 0 < x) (ha : 0 < P102APow q ∧ P102APow q < 1 - q.y)
    (p097 : P097Statement) :
    localMainSum q sigma x hx ≤
      tailFactor q *
        ((1 / 2) * (Real.log sigma / Real.log q.theta)).rpow
          (q.y - 1 + P102APow q) := by
  let K0 := lowerBinIndex sigma q.theta
  let e := q.y - 1 + P102APow q
  have hK0 : 1 ≤ K0 := lowerBinIndex_pos sigma q.theta
  have he : e < 0 := by dsimp [e]; nlinarith [ha.2]
  have hseries : Summable (fun k : ℕ => (k : ℝ).rpow (q.y - 2 + P102APow q)) := by
    apply Real.summable_nat_rpow.mpr
    nlinarith [ha.2]
  have htail : Summable
      (fun k : ℕ => if K0 ≤ k then (k : ℝ).rpow (q.y - 2 + P102APow q) else 0) := by
    apply (hseries.indicator {k : ℕ | K0 ≤ k}).congr
    intro k
    simp only [Set.indicator_apply, Set.mem_setOf_eq]
  have hfinite : localMainSum q sigma x hx ≤
      ∑' k : ℕ, if K0 ≤ k then (k : ℝ).rpow (q.y - 2 + P102APow q) else 0 := by
    unfold localMainSum
    calc
      (∑ k ∈ Finset.Icc K0 (localCutoff q x hx).toNat,
          (k : ℝ).rpow (q.y - 2 + P102APow q)) =
          ∑ k ∈ Finset.Icc K0 (localCutoff q x hx).toNat,
            if K0 ≤ k then (k : ℝ).rpow (q.y - 2 + P102APow q) else 0 := by
        apply Finset.sum_congr rfl
        intro k hk
        simp [(Finset.mem_Icc.1 hk).1]
      _ ≤ ∑' k : ℕ, if K0 ≤ k then
          (k : ℝ).rpow (q.y - 2 + P102APow q) else 0 := by
        exact htail.sum_le_tsum _ (by
          intro k hk
          split_ifs
          · exact Real.rpow_nonneg (by positivity) _
          · exact le_rfl)
  have hp := p097 q.y (P102APow q) q.y_pos q.y_lt_one ha.1 ha.2 K0 hK0
  have hKbound := hp.2 sigma q.theta q.theta_ge_two hsigma rfl
  have hthetaLog : 0 < Real.log q.theta :=
    Real.log_pos (lt_of_lt_of_le one_lt_two q.theta_ge_two)
  have hsigmaLog : 0 < Real.log sigma :=
    Real.log_pos (lt_of_lt_of_le one_lt_two (q.theta_ge_two.trans hsigma))
  have hbase : 0 < (1 / 2 : ℝ) * (Real.log sigma / Real.log q.theta) := by positivity
  have hpow : (K0 : ℝ).rpow e ≤
      ((1 / 2) * (Real.log sigma / Real.log q.theta)).rpow e := by
    apply Real.rpow_le_rpow_of_nonpos hbase
    · simpa [K0] using hKbound.1
    · exact he.le
  have hfactor : 0 ≤ tailFactor q := by
    unfold tailFactor
    have : 0 < 1 - q.y - P102APow q := by nlinarith [ha.2]
    positivity
  calc
    localMainSum q sigma x hx ≤
        ∑' k : ℕ, if K0 ≤ k then (k : ℝ).rpow (q.y - 2 + P102APow q) else 0 := hfinite
    _ ≤ tailFactor q * (K0 : ℝ).rpow e := by simpa [tailFactor, e] using hp.1
    _ ≤ tailFactor q *
        ((1 / 2) * (Real.log sigma / Real.log q.theta)).rpow e :=
      mul_le_mul_of_nonneg_left hpow hfactor

@[expose] def movingRemainder
    (q : P102Parameters) (C3 sigma xi x : ℝ)
    (hsigma : q.theta ≤ sigma) (hxi : 1 < xi) : ℝ :=
  initialConstant q sigma xi hsigma hxi +
    (2 * Real.log xi * Real.log q.theta / Real.log sigma).rpow (P102APow q) *
      ((C3 / q.y) * x * (Real.log sigma).rpow (-q.y) *
        (localMovingLogSum q sigma ((q.y - 1) / 2) x hsigma +
          (Real.log sigma).rpow (q.y / 2) *
            localMovingLogSum q sigma (-1 / 2) x hsigma))

lemma movingRemainder_littleO
    (q : P102Parameters) (C3 sigma xi : ℝ)
    (hsigma : q.theta ≤ sigma) (hxi : 1 < xi)
    (ha : 0 < P102APow q ∧ P102APow q < 1 - q.y)
    (p100 : P100Statement) (p101 : P101Statement) :
    (fun x : ℝ => movingRemainder q C3 sigma xi x hsigma hxi) =o[atTop]
      (fun x : ℝ => x) := by
  have hm := p100 q.theta sigma q.theta_ge_two hsigma q.y (P102APow q)
    q.y_pos q.y_lt_one ha.1 ha.2
  have ht := p101 q.theta sigma q.theta_ge_two hsigma q.y (P102APow q)
    q.y_pos q.y_lt_one ha.1 ha.2
  change (fun x : ℝ => localMovingLogSum q sigma ((q.y - 1) / 2) x hsigma) =o[atTop]
      (fun _ : ℝ => (1 : ℝ)) at hm
  change (fun x : ℝ => localMovingLogSum q sigma (-1 / 2) x hsigma) =o[atTop]
      (fun _ : ℝ => (1 : ℝ)) at ht
  have hmx : (fun x : ℝ => x * localMovingLogSum q sigma ((q.y - 1) / 2) x hsigma)
      =o[atTop] (fun x : ℝ => x) := by
    simpa using (isBigO_refl (fun x : ℝ => x) atTop).mul_isLittleO hm
  have htx : (fun x : ℝ => x * localMovingLogSum q sigma (-1 / 2) x hsigma)
      =o[atTop] (fun x : ℝ => x) := by
    simpa using (isBigO_refl (fun x : ℝ => x) atTop).mul_isLittleO ht
  have hmiddle := hmx.const_mul_left
    ((2 * Real.log xi * Real.log q.theta / Real.log sigma).rpow (P102APow q) *
      (C3 / q.y) * (Real.log sigma).rpow (-q.y))
  have hterminal := htx.const_mul_left
    ((2 * Real.log xi * Real.log q.theta / Real.log sigma).rpow (P102APow q) *
      (C3 / q.y) * (Real.log sigma).rpow (-q.y) *
        (Real.log sigma).rpow (q.y / 2))
  have hsum := (initialConstant_littleO q sigma xi hsigma hxi).add
    (hmiddle.add hterminal)
  simpa only [movingRemainder] using hsum.congr'
    (Filter.Eventually.of_forall (by intro x; ring))
    (Filter.Eventually.of_forall (by intro x; rfl))

theorem result : Erdos448.Stage6.TaskContracts.ROOT12Target := by
  intro p089 p092 p096 p097 p100 p101 q
  let C3 := (p089 q.theta q.theta_ge_two).choose
  have hC3 : 0 < C3 := (p089 q.theta q.theta_ge_two).choose_spec.1
  have ha : 0 < P102APow q ∧ P102APow q < 1 - q.y := by
    exact p096 q.y q.epsilonInt q.y_pos q.y_lt_one q.epsilonInt_pos q.admissible
  refine ⟨{
    coefficient := mainCoefficient q C3
    coefficient_pos := ?_
    fixed_parameter_remainder := ?_ }⟩
  · unfold mainCoefficient tailFactor scaleFactor
    have hden : 0 < 1 - q.y - P102APow q := by nlinarith [ha.2]
    have hlog : 0 < Real.log q.theta :=
      Real.log_pos (lt_of_lt_of_le one_lt_two q.theta_ge_two)
    apply mul_pos
    · apply mul_pos
      · exact div_pos hC3 q.y_pos
      · positivity
    · apply div_pos
      · exact mul_pos (mul_pos (Real.rpow_pos_of_pos (by norm_num) _)
          (Real.rpow_pos_of_pos (by norm_num) _))
          (Real.rpow_pos_of_pos hlog _)
      · exact Real.rpow_pos_of_pos hlog _
  · intro sigma hsigma xi hxi
    refine {
      remainder := fun x => movingRemainder q C3 sigma xi x hsigma hxi
      littleO := movingRemainder_littleO q C3 sigma xi hsigma hxi ha p100 p101
      eventual_bound := ?_ }
    filter_upwards [eventually_gt_atTop
      (Real.exp (Real.log xi * Real.log sigma))] with x hxU
    have hx : 0 < x := Real.exp_pos _ |>.trans hxU
    have hp092 := (p092 (localP092 q sigma xi x hsigma hxi hxU)).1
    change localTail q sigma xi x hsigma hxi ≤
      (2 * Real.log xi * Real.log q.theta / Real.log sigma).rpow (P102APow q) *
        P092KSum (localP092 q sigma xi x hsigma hxi hxU) at hp092
    have hksum := p092_ksum_bound q C3 sigma xi x hsigma hxi hxU
      (p089 q.theta q.theta_ge_two).choose_spec.2
    have hmain := mainSum_bound q sigma x hsigma hx ha p097
    have hpref : 0 ≤
        (2 * Real.log xi * Real.log q.theta / Real.log sigma).rpow (P102APow q) := by
      apply (Real.rpow_pos_of_pos _ _).le
      have hlogTheta : 0 < Real.log q.theta :=
        Real.log_pos (lt_of_lt_of_le one_lt_two q.theta_ge_two)
      have hlogSigma : 0 < Real.log sigma :=
        Real.log_pos (lt_of_lt_of_le one_lt_two (q.theta_ge_two.trans hsigma))
      exact div_pos (mul_pos (mul_pos (by norm_num) (Real.log_pos hxi)) hlogTheta) hlogSigma
    have hcommon : 0 ≤ (C3 / q.y) * x * (Real.log sigma).rpow (-q.y) := by
      exact mul_nonneg (mul_nonneg (div_nonneg hC3.le q.y_pos.le) hx.le)
        (Real.rpow_nonneg (Real.log_nonneg
          (le_trans (by norm_num : (1 : ℝ) ≤ 2) (q.theta_ge_two.trans hsigma))) _)
    have htail : localTail q sigma xi x hsigma hxi ≤
        mainCoefficient q C3 * x * (Real.log xi).rpow (P102APow q) *
            (Real.log sigma).rpow (-1) +
          (2 * Real.log xi * Real.log q.theta / Real.log sigma).rpow (P102APow q) *
            ((C3 / q.y) * x * (Real.log sigma).rpow (-q.y) *
              (localMovingLogSum q sigma ((q.y - 1) / 2) x hsigma +
                (Real.log sigma).rpow (q.y / 2) *
                  localMovingLogSum q sigma (-1 / 2) x hsigma)) := by
      calc
        localTail q sigma xi x hsigma hxi ≤
            (2 * Real.log xi * Real.log q.theta / Real.log sigma).rpow (P102APow q) *
              P092KSum (localP092 q sigma xi x hsigma hxi hxU) := hp092
        _ ≤ (2 * Real.log xi * Real.log q.theta / Real.log sigma).rpow (P102APow q) *
              ((C3 / q.y) * x * (Real.log sigma).rpow (-q.y) *
                (localMainSum q sigma x hx +
                  localMovingLogSum q sigma ((q.y - 1) / 2) x hsigma +
                  (Real.log sigma).rpow (q.y / 2) *
                    localMovingLogSum q sigma (-1 / 2) x hsigma)) :=
          mul_le_mul_of_nonneg_left hksum hpref
        _ ≤ (2 * Real.log xi * Real.log q.theta / Real.log sigma).rpow (P102APow q) *
              ((C3 / q.y) * x * (Real.log sigma).rpow (-q.y) *
                (tailFactor q *
                    ((1 / 2) * (Real.log sigma / Real.log q.theta)).rpow
                      (q.y - 1 + P102APow q) +
                  localMovingLogSum q sigma ((q.y - 1) / 2) x hsigma +
                  (Real.log sigma).rpow (q.y / 2) *
                    localMovingLogSum q sigma (-1 / 2) x hsigma)) := by
          gcongr
        _ = _ := by
          have hscale := main_scale_identity q sigma xi hsigma hxi
          calc
            _ = (C3 / q.y) * tailFactor q * x *
                  ((2 * Real.log xi * Real.log q.theta / Real.log sigma).rpow (P102APow q) *
                    (Real.log sigma).rpow (-q.y) *
                    ((1 / 2) * (Real.log sigma / Real.log q.theta)).rpow
                      (q.y - 1 + P102APow q)) +
                (2 * Real.log xi * Real.log q.theta / Real.log sigma).rpow (P102APow q) *
                  ((C3 / q.y) * x * (Real.log sigma).rpow (-q.y) *
                    (localMovingLogSum q sigma ((q.y - 1) / 2) x hsigma +
                      (Real.log sigma).rpow (q.y / 2) *
                        localMovingLogSum q sigma (-1 / 2) x hsigma)) := by ring
            _ = _ := by rw [hscale]; unfold mainCoefficient; ring
    change localMean q sigma xi x hsigma hxi ≤ _
    rw [localMean_eq_tail_add_initial]
    have hi := localInitial_le_constant q sigma xi x hsigma hxi
    unfold movingRemainder
    nlinarith

end

end Erdos448.Stage7.ROOT12.Work
