module

import all Mathlib.Basic.Real.Basic
public import Erdos448.stage6.TaskContracts

public section

set_option backward.isDefEq.respectTransparency false

namespace Erdos448.Stage7.ROOT10.Work

open Finset
open Erdos448.Stage4
open Erdos448.Stage4.Contracts
open Erdos448.Stage6.TaskContracts

noncomputable section

lemma explicit_rpow_add {x a b : ℝ} (hx : 0 < x) :
    Real.rpow x (a + b) = Real.rpow x a * Real.rpow x b := by
  change x ^ (a + b) = x ^ a * x ^ b
  exact Real.rpow_add hx a b

lemma explicit_div_rpow {x y a : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.rpow (x / y) a = Real.rpow x a / Real.rpow y a := by
  change (x / y) ^ a = x ^ a / y ^ a
  exact Real.div_rpow hx hy a

lemma explicit_rpow_neg {x a : ℝ} (hx : 0 ≤ x) :
    Real.rpow x (-a) = (Real.rpow x a)⁻¹ := by
  change x ^ (-a) = (x ^ a)⁻¹
  exact Real.rpow_neg hx a

lemma safeLog_nonneg (t : ℝ) : 0 ≤ safeLog t := by
  unfold safeLog
  exact le_trans zero_le_one (le_max_left _ _)

lemma parameter_log_pos (q : WeightParameters) : 0 < Real.log q.sigma :=
  Real.log_pos (lt_of_lt_of_le one_lt_two (q.theta_ge_two.trans q.sigma_ge_theta))

lemma ratio_rpow_le
    {c k L a A : ℝ}
    (hc : 0 < c) (hk : 1 ≤ k) (hL : c * k ≤ L)
    (ha : 0 ≤ a) (haA : a ≤ A) :
    (k / L).rpow a ≤ max 1 ((1 / c).rpow A) := by
  have hkpos : 0 < k := lt_of_lt_of_le zero_lt_one hk
  have hLpos : 0 < L := (mul_pos hc hkpos).trans_le hL
  have hratio_nonneg : 0 ≤ k / L := (div_nonneg hkpos.le hLpos.le)
  have hratio : k / L ≤ 1 / c := by
    rw [div_le_div_iff₀ hLpos hc]
    nlinarith
  have hbase := Real.rpow_le_rpow hratio_nonneg hratio ha
  by_cases hc_one : c ≤ 1
  · have hone : 1 ≤ 1 / c := (le_div_iff₀ hc).2 (by nlinarith)
    have hexp := Real.rpow_le_rpow_of_exponent_le hone haA
    exact hbase.trans (hexp.trans (le_max_right _ _))
  · have hquot : 1 / c ≤ 1 := (div_le_one hc).2 (le_of_not_ge hc_one)
    have hone := Real.rpow_le_one (by positivity : 0 ≤ 1 / c) hquot ha
    exact hbase.trans (hone.trans (le_max_left _ _))

lemma high_scale_identity
    {k L y : ℝ} (hk : 0 < k) (hL : 0 < L) :
    L.rpow (-1 / 2) * L.rpow (-1) * k.rpow (-1 / 2) =
      (L.rpow (-y) * k.rpow ((y - 3) / 2) * k.rpow ((y - 1) / 2)) *
        (k / L).rpow (3 / 2 - y) := by
  have hdiv : (k / L).rpow (3 / 2 - y) =
      k.rpow (3 / 2 - y) * L.rpow (-(3 / 2 - y)) := by
    rw [explicit_div_rpow hk.le hL.le, div_eq_mul_inv, ← explicit_rpow_neg hL.le]
  rw [hdiv]
  calc
    L.rpow (-1 / 2) * L.rpow (-1) * k.rpow (-1 / 2) =
        L.rpow ((-1 / 2) + (-1)) * k.rpow (-1 / 2) := by
          rw [explicit_rpow_add hL]
    _ = L.rpow (-3 / 2) * k.rpow (-1 / 2) := by ring_nf
    _ = L.rpow ((-y) + (-(3 / 2 - y))) *
          k.rpow (((y - 3) / 2 + (y - 1) / 2) + (3 / 2 - y)) := by
          congr 1 <;> ring_nf
    _ = (L.rpow (-y) * L.rpow (-(3 / 2 - y))) *
          ((k.rpow ((y - 3) / 2) * k.rpow ((y - 1) / 2)) *
            k.rpow (3 / 2 - y)) := by
          rw [explicit_rpow_add hL, explicit_rpow_add hk, explicit_rpow_add hk]
    _ = (L.rpow (-y) * k.rpow ((y - 3) / 2) * k.rpow ((y - 1) / 2)) *
          (k.rpow (3 / 2 - y) * L.rpow (-(3 / 2 - y))) := by ring

lemma low_scale_identity
    {k L y : ℝ} (hk : 0 < k) (hL : 0 < L) :
    L.rpow (-1) * k.rpow (-1 / 2) =
      (L.rpow (-y / 2) * k.rpow ((y - 3) / 2)) *
        (k / L).rpow (1 - y / 2) := by
  have hdiv : (k / L).rpow (1 - y / 2) =
      k.rpow (1 - y / 2) * L.rpow (-(1 - y / 2)) := by
    rw [explicit_div_rpow hk.le hL.le, div_eq_mul_inv, ← explicit_rpow_neg hL.le]
  rw [hdiv]
  calc
    L.rpow (-1) * k.rpow (-1 / 2) =
        L.rpow ((-y / 2) + (-(1 - y / 2))) *
          k.rpow ((y - 3) / 2 + (1 - y / 2)) := by
          congr 1 <;> ring_nf
    _ = (L.rpow (-y / 2) * L.rpow (-(1 - y / 2))) *
          (k.rpow ((y - 3) / 2) * k.rpow (1 - y / 2)) := by
          rw [explicit_rpow_add hL, explicit_rpow_add hk]
    _ = (L.rpow (-y / 2) * k.rpow ((y - 3) / 2)) *
          (k.rpow (1 - y / 2) * L.rpow (-(1 - y / 2))) := by ring

lemma high_scale_le
    {c k L y : ℝ}
    (hc : 0 < c) (hk : 1 ≤ k) (hL : c * k ≤ L)
    (hy0 : 0 < y) (hy1 : y < 1) :
    L.rpow (-1 / 2) * L.rpow (-1) * k.rpow (-1 / 2) ≤
      max 1 ((1 / c).rpow (3 / 2)) *
        (L.rpow (-y) * k.rpow ((y - 3) / 2) * k.rpow ((y - 1) / 2)) := by
  have hkpos : 0 < k := lt_of_lt_of_le zero_lt_one hk
  have hLpos : 0 < L := (mul_pos hc hkpos).trans_le hL
  have ha0 : 0 ≤ 3 / 2 - y := by nlinarith
  have haA : 3 / 2 - y ≤ (3 / 2 : ℝ) := by nlinarith
  have hr := ratio_rpow_le hc hk hL ha0 haA
  rw [high_scale_identity hkpos hLpos]
  have hcore : 0 ≤ L.rpow (-y) * k.rpow ((y - 3) / 2) *
      k.rpow ((y - 1) / 2) := by
    exact mul_nonneg
      (mul_nonneg (Real.rpow_nonneg hLpos.le _) (Real.rpow_nonneg hkpos.le _))
      (Real.rpow_nonneg hkpos.le _)
  simpa [mul_comm] using mul_le_mul_of_nonneg_left hr hcore

lemma low_scale_le
    {c k L y : ℝ}
    (hc : 0 < c) (hk : 1 ≤ k) (hL : c * k ≤ L)
    (hy0 : 0 < y) (hy1 : y < 1) :
    L.rpow (-1) * k.rpow (-1 / 2) ≤
      max 1 ((1 / c).rpow 1) *
        (L.rpow (-y / 2) * k.rpow ((y - 3) / 2)) := by
  have hkpos : 0 < k := lt_of_lt_of_le zero_lt_one hk
  have hLpos : 0 < L := (mul_pos hc hkpos).trans_le hL
  have ha0 : 0 ≤ 1 - y / 2 := by nlinarith
  have haA : 1 - y / 2 ≤ (1 : ℝ) := by nlinarith
  have hr := ratio_rpow_le hc hk hL ha0 haA
  rw [low_scale_identity hkpos hLpos]
  have hcore : 0 ≤ L.rpow (-y / 2) * k.rpow ((y - 3) / 2) := by
    exact mul_nonneg (Real.rpow_nonneg hLpos.le _) (Real.rpow_nonneg hkpos.le _)
  simpa [mul_comm] using mul_le_mul_of_nonneg_left hr hcore

lemma envelope_nonneg (q : WeightParameters) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ proposition3Envelope q x := by
  have hlog := (parameter_log_pos q).le
  have hk : 0 ≤ (q.k : ℝ) := by positivity
  have hs := safeLog_nonneg (2 * x * q.theta ^ (1 - (2 : ℤ) * q.k))
  unfold proposition3Envelope proposition3Braces
  exact mul_nonneg
    (mul_nonneg (mul_nonneg hx (Real.rpow_nonneg hlog _)) (Real.rpow_nonneg hk _))
    (add_nonneg
      (add_nonneg (Real.rpow_nonneg hk _) (Real.rpow_nonneg hs _))
      (div_nonneg (Real.rpow_nonneg hlog _) (Real.rpow_nonneg hs _)))

lemma upper_nonneg (q : WeightParameters) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ upperAssemblyEnvelope q x := by
  have hlog := (parameter_log_pos q).le
  have hk : 0 ≤ (q.k : ℝ) := by positivity
  unfold upperAssemblyEnvelope
  exact mul_nonneg
    (mul_nonneg (mul_nonneg hx (Real.rpow_nonneg hlog _)) (Real.rpow_nonneg hk _))
    (Real.rpow_nonneg hk _)

lemma terminal_nonneg (q : WeightParameters) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ terminalAssemblyEnvelope q x := by
  have hlog := (parameter_log_pos q).le
  have hk : 0 ≤ (q.k : ℝ) := by positivity
  have hs := safeLog_nonneg (2 * x * q.theta ^ (1 - (2 : ℤ) * q.k))
  unfold terminalAssemblyEnvelope
  exact mul_nonneg
    (mul_nonneg (mul_nonneg hx (Real.rpow_nonneg hlog _)) (Real.rpow_nonneg hk _))
    (div_nonneg (Real.rpow_nonneg hlog _) (Real.rpow_nonneg hs _))

lemma upper_le_envelope (q : WeightParameters) {x : ℝ} (hx : 0 ≤ x) :
    upperAssemblyEnvelope q x ≤ proposition3Envelope q x := by
  have hlog := (parameter_log_pos q).le
  have hk : 0 ≤ (q.k : ℝ) := by positivity
  have hs := safeLog_nonneg (2 * x * q.theta ^ (1 - (2 : ℤ) * q.k))
  unfold upperAssemblyEnvelope proposition3Envelope proposition3Braces
  have hfac : 0 ≤ x * (Real.log q.sigma).rpow (-q.y) *
      (q.k : ℝ).rpow ((q.y - 3) / 2) := by
    exact mul_nonneg (mul_nonneg hx (Real.rpow_nonneg hlog _)) (Real.rpow_nonneg hk _)
  have hmid : 0 ≤ (safeLog (2 * x * q.theta ^ (1 - (2 : ℤ) * q.k))).rpow
      ((q.y - 1) / 2) := Real.rpow_nonneg hs _
  have hterm : 0 ≤ (Real.log q.sigma).rpow (q.y / 2) /
      (safeLog (2 * x * q.theta ^ (1 - (2 : ℤ) * q.k))).rpow (1 / 2) := by
    exact div_nonneg (Real.rpow_nonneg hlog _) (Real.rpow_nonneg hs _)
  let F := x * (Real.log q.sigma).rpow (-q.y) *
    (q.k : ℝ).rpow ((q.y - 3) / 2)
  let U := (q.k : ℝ).rpow ((q.y - 1) / 2)
  let V := (safeLog (2 * x * q.theta ^ (1 - (2 : ℤ) * q.k))).rpow
    ((q.y - 1) / 2)
  let T := (Real.log q.sigma).rpow (q.y / 2) /
    (safeLog (2 * x * q.theta ^ (1 - (2 : ℤ) * q.k))).rpow (1 / 2)
  change F * U ≤ F * (U + V + T)
  have hV : 0 ≤ V := by exact hmid
  have hT : 0 ≤ T := by exact hterm
  exact mul_le_mul_of_nonneg_left (by nlinarith) hfac

lemma terminal_le_envelope (q : WeightParameters) {x : ℝ} (hx : 0 ≤ x) :
    terminalAssemblyEnvelope q x ≤ proposition3Envelope q x := by
  have hlog := (parameter_log_pos q).le
  have hk : 0 ≤ (q.k : ℝ) := by positivity
  have hs := safeLog_nonneg (2 * x * q.theta ^ (1 - (2 : ℤ) * q.k))
  unfold terminalAssemblyEnvelope proposition3Envelope proposition3Braces
  have hfac : 0 ≤ x * (Real.log q.sigma).rpow (-q.y) *
      (q.k : ℝ).rpow ((q.y - 3) / 2) := by
    exact mul_nonneg (mul_nonneg hx (Real.rpow_nonneg hlog _)) (Real.rpow_nonneg hk _)
  have hu : 0 ≤ (q.k : ℝ).rpow ((q.y - 1) / 2) := Real.rpow_nonneg hk _
  have hm : 0 ≤ (safeLog (2 * x * q.theta ^ (1 - (2 : ℤ) * q.k))).rpow
      ((q.y - 1) / 2) := Real.rpow_nonneg hs _
  let F := x * (Real.log q.sigma).rpow (-q.y) *
    (q.k : ℝ).rpow ((q.y - 3) / 2)
  let U := (q.k : ℝ).rpow ((q.y - 1) / 2)
  let V := (safeLog (2 * x * q.theta ^ (1 - (2 : ℤ) * q.k))).rpow
    ((q.y - 1) / 2)
  let T := (Real.log q.sigma).rpow (q.y / 2) /
    (safeLog (2 * x * q.theta ^ (1 - (2 : ℤ) * q.k))).rpow (1 / 2)
  change F * T ≤ F * (U + V + T)
  have hU : 0 ≤ U := by exact hu
  have hV : 0 ≤ V := by exact hm
  exact mul_le_mul_of_nonneg_left (by nlinarith) hfac

lemma transition_high_assembly
    (h070 : P070Statement) (h081 : P081Statement)
    (h082 : P082Statement) (h084 : P084Statement) : P085Statement := by
  intro theta htheta
  rcases h070 with ⟨family⟩
  rcases h081 theta htheta with ⟨scale⟩
  rcases h082 theta htheta with ⟨CtrH, hCtrH, hH⟩
  rcases h084 theta htheta with ⟨CtrOut, hCtrOut, hOut⟩
  let C4 : ℝ := p070C4
    { Cfam := family.Cfam, Cfam_pos := family.Cfam_pos,
      theta := theta, theta_ge_two := htheta }
  let M : ℝ := max 1 ((1 / scale.comparison.lower).rpow (3 / 2))
  refine ⟨CtrH * CtrOut * C4 * M, ?_, ?_⟩
  · have hC4 : 0 < C4 := family.c4_positive theta htheta
    have hM : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    positivity
  · intro q hq x hx
    have htheta_pos : 0 < q.theta := by rw [hq]; nlinarith
    have hxpos : 0 < x := lt_of_le_of_lt (by positivity : 0 ≤ q.theta ^ (2 * q.k - 1)) hx
    let sq : P081ScaleParameters :=
      { theta := q.theta, theta_ge_two := q.theta_ge_two, k := q.k,
        k_pos := q.k_pos, sigma := q.sigma,
        sigma_gt_bin := q.sigma_gt_bin, sigma_lt_next_bin := q.sigma_lt_next_bin }
    have hscale := scale.asymptotic_bounds sq (by simpa [sq] using hq)
    have hlog : 0 < Real.log q.sigma :=
      (mul_pos scale.comparison.lower_pos
        (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one q.k_pos))).trans_le hscale.1
    have hs : Real.log q.sigma ^ (-1 / 2 : ℝ) * Real.log q.sigma ^ (-1 : ℝ) *
        (q.k : ℝ) ^ (-1 / 2 : ℝ) ≤
        M * (Real.log q.sigma ^ (-q.y) *
          (q.k : ℝ) ^ ((q.y - 3) / 2) * (q.k : ℝ) ^ ((q.y - 1) / 2)) := by
      exact high_scale_le scale.comparison.lower_pos (by exact_mod_cast q.k_pos)
        hscale.1 q.y_pos q.y_lt_one
    have hWindow : w4WindowSum q.toWeightParameters ≤
        C4 * q.theta ^ q.k * (q.k : ℝ).rpow (-1 / 2) := by
      simpa [C4, hq] using family.window q.toWeightParameters
    have h1 := hH q hq x hx
    have h2 := hOut q hq
    have hpow : q.theta ^ (2 * q.k) = q.theta ^ q.k * q.theta ^ q.k := by
      rw [show 2 * q.k = q.k + q.k by omega, pow_add]
    calc
      transitionTransported .high q x ≤
          CtrH * (Real.log q.sigma).rpow (-1 / 2) *
            (x / q.theta ^ (2 * q.k)) * transitionOuter q := h1
      _ ≤ CtrH * (Real.log q.sigma).rpow (-1 / 2) *
            (x / q.theta ^ (2 * q.k)) *
              (CtrOut * q.theta ^ q.k * (Real.log q.sigma).rpow (-1) *
                w4WindowSum q.toWeightParameters) := by
          simpa only [mul_assoc, Real.rpow_eq_pow] using mul_le_mul_of_nonneg_left h2
            (mul_nonneg
              (mul_nonneg hCtrH.le (Real.rpow_nonneg hlog.le _))
              (div_nonneg hxpos.le (pow_pos htheta_pos _).le))
      _ ≤ CtrH * (Real.log q.sigma).rpow (-1 / 2) *
            (x / q.theta ^ (2 * q.k)) *
              (CtrOut * q.theta ^ q.k * (Real.log q.sigma).rpow (-1) *
                (C4 * q.theta ^ q.k * (q.k : ℝ).rpow (-1 / 2))) := by
          have hcoef : 0 ≤ CtrH * (Real.log q.sigma).rpow (-1 / 2) *
              (x / q.theta ^ (2 * q.k)) *
                (CtrOut * q.theta ^ q.k * (Real.log q.sigma).rpow (-1)) := by
            exact mul_nonneg
              (mul_nonneg
                (mul_nonneg hCtrH.le (Real.rpow_nonneg hlog.le _))
                (div_nonneg hxpos.le (pow_pos htheta_pos _).le))
              (mul_nonneg (mul_nonneg hCtrOut.le (pow_nonneg htheta_pos.le _))
                (Real.rpow_nonneg hlog.le _))
          simpa only [mul_assoc, Real.rpow_eq_pow] using mul_le_mul_of_nonneg_left hWindow hcoef
      _ = (CtrH * CtrOut * C4) * x *
            ((Real.log q.sigma).rpow (-1 / 2) *
              (Real.log q.sigma).rpow (-1) * (q.k : ℝ).rpow (-1 / 2)) := by
          rw [hpow]
          field_simp [ne_of_gt (pow_pos htheta_pos q.k)]
      _ ≤ (CtrH * CtrOut * C4) * x *
            (M * ((Real.log q.sigma).rpow (-q.y) *
              (q.k : ℝ).rpow ((q.y - 3) / 2) *
                (q.k : ℝ).rpow ((q.y - 1) / 2))) := by
          simpa only [mul_assoc, Real.rpow_eq_pow] using mul_le_mul_of_nonneg_left hs
            (mul_nonneg (mul_nonneg (mul_nonneg hCtrH.le hCtrOut.le)
              (family.c4_positive theta htheta).le) hxpos.le)
      _ = (CtrH * CtrOut * C4 * M) * upperAssemblyEnvelope q.toWeightParameters x := by
          unfold upperAssemblyEnvelope
          ring

lemma transition_low_assembly
    (h070 : P070Statement) (h081 : P081Statement)
    (h083 : P083Statement) (h084 : P084Statement) : P086Statement := by
  intro theta htheta
  rcases h070 with ⟨family⟩
  rcases h081 theta htheta with ⟨scale⟩
  rcases h083 theta htheta with ⟨CtrL, hCtrL, hL⟩
  rcases h084 theta htheta with ⟨CtrOut, hCtrOut, hOut⟩
  let C4 : ℝ := p070C4
    { Cfam := family.Cfam, Cfam_pos := family.Cfam_pos,
      theta := theta, theta_ge_two := htheta }
  let M : ℝ := max 1 ((1 / scale.comparison.lower).rpow 1)
  refine ⟨CtrL * CtrOut * C4 * M, ?_, ?_⟩
  · have hC4 : 0 < C4 := family.c4_positive theta htheta
    have hM : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    positivity
  · intro q hq x hx
    have htheta_pos : 0 < q.theta := by rw [hq]; nlinarith
    have hxpos : 0 < x := lt_of_le_of_lt (by positivity : 0 ≤ q.theta ^ (2 * q.k - 1)) hx
    let sq : P081ScaleParameters :=
      { theta := q.theta, theta_ge_two := q.theta_ge_two, k := q.k,
        k_pos := q.k_pos, sigma := q.sigma,
        sigma_gt_bin := q.sigma_gt_bin, sigma_lt_next_bin := q.sigma_lt_next_bin }
    have hscale := scale.asymptotic_bounds sq (by simpa [sq] using hq)
    have hlog : 0 < Real.log q.sigma :=
      (mul_pos scale.comparison.lower_pos
        (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one q.k_pos))).trans_le hscale.1
    have hs : Real.log q.sigma ^ (-1 : ℝ) * (q.k : ℝ) ^ (-1 / 2 : ℝ) ≤
        M * (Real.log q.sigma ^ (-q.y / 2) *
          (q.k : ℝ) ^ ((q.y - 3) / 2)) := by
      exact low_scale_le scale.comparison.lower_pos (by exact_mod_cast q.k_pos)
        hscale.1 q.y_pos q.y_lt_one
    have hWindow : w4WindowSum q.toWeightParameters ≤
        C4 * q.theta ^ q.k * (q.k : ℝ).rpow (-1 / 2) := by
      simpa [C4, hq] using family.window q.toWeightParameters
    have h1 := hL q hq x hx
    have h2 := hOut q hq
    have hpow : q.theta ^ (2 * q.k) = q.theta ^ q.k * q.theta ^ q.k := by
      rw [show 2 * q.k = q.k + q.k by omega, pow_add]
    calc
      transitionTransported .low q x ≤
          CtrL * (x / q.theta ^ (2 * q.k)) *
            (safeLog (2 * x * q.theta ^ (1 - (2 : ℤ) * q.k))).rpow (-1 / 2) *
              transitionOuter q := h1
      _ ≤ CtrL * (x / q.theta ^ (2 * q.k)) *
            (safeLog (2 * x * q.theta ^ (1 - (2 : ℤ) * q.k))).rpow (-1 / 2) *
              (CtrOut * q.theta ^ q.k * (Real.log q.sigma).rpow (-1) *
                w4WindowSum q.toWeightParameters) := by
          simpa only [mul_assoc, Real.rpow_eq_pow] using mul_le_mul_of_nonneg_left h2
            (mul_nonneg
              (mul_nonneg hCtrL.le (div_nonneg hxpos.le (pow_pos htheta_pos _).le))
              (Real.rpow_nonneg (safeLog_nonneg _) _))
      _ ≤ CtrL * (x / q.theta ^ (2 * q.k)) *
            (safeLog (2 * x * q.theta ^ (1 - (2 : ℤ) * q.k))).rpow (-1 / 2) *
              (CtrOut * q.theta ^ q.k * (Real.log q.sigma).rpow (-1) *
                (C4 * q.theta ^ q.k * (q.k : ℝ).rpow (-1 / 2))) := by
          have hcoef : 0 ≤ CtrL * (x / q.theta ^ (2 * q.k)) *
              (safeLog (2 * x * q.theta ^ (1 - (2 : ℤ) * q.k))).rpow (-1 / 2) *
                (CtrOut * q.theta ^ q.k * (Real.log q.sigma).rpow (-1)) := by
            exact mul_nonneg
              (mul_nonneg
                (mul_nonneg hCtrL.le (div_nonneg hxpos.le (pow_pos htheta_pos _).le))
                (Real.rpow_nonneg (safeLog_nonneg _) _))
              (mul_nonneg (mul_nonneg hCtrOut.le (pow_nonneg htheta_pos.le _))
                (Real.rpow_nonneg hlog.le _))
          simpa only [mul_assoc, Real.rpow_eq_pow] using mul_le_mul_of_nonneg_left hWindow hcoef
      _ = (CtrL * CtrOut * C4) * x *
            ((Real.log q.sigma).rpow (-1) * (q.k : ℝ).rpow (-1 / 2)) *
              (safeLog (2 * x * q.theta ^ (1 - (2 : ℤ) * q.k))).rpow (-1 / 2) := by
          rw [hpow]
          field_simp [ne_of_gt (pow_pos htheta_pos q.k)]
      _ ≤ (CtrL * CtrOut * C4) * x *
            (M * ((Real.log q.sigma).rpow (-q.y / 2) *
              (q.k : ℝ).rpow ((q.y - 3) / 2))) *
                (safeLog (2 * x * q.theta ^ (1 - (2 : ℤ) * q.k))).rpow (-1 / 2) := by
          simpa only [mul_assoc, Real.rpow_eq_pow] using mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hs <|
              mul_nonneg (mul_nonneg (mul_nonneg hCtrL.le hCtrOut.le)
                (family.c4_positive theta htheta).le) hxpos.le)
            (Real.rpow_nonneg (safeLog_nonneg _) _)
      _ = (CtrL * CtrOut * C4 * M) * terminalAssemblyEnvelope q.toWeightParameters x := by
          unfold terminalAssemblyEnvelope
          have hlogid : (Real.log q.sigma).rpow (-q.y / 2) =
              (Real.log q.sigma).rpow (-q.y) *
                (Real.log q.sigma).rpow (q.y / 2) := by
            rw [← explicit_rpow_add hlog]
            congr 1
            ring
          have hsafe0 : 0 ≤ safeLog
              (2 * x * q.theta ^ (1 - (2 : ℤ) * q.k)) := by
            unfold safeLog
            exact le_trans zero_le_one (le_max_left _ _)
          have hsafeid : (safeLog
              (2 * x * q.theta ^ (1 - (2 : ℤ) * q.k))).rpow (-1 / 2) =
              1 / (safeLog
                (2 * x * q.theta ^ (1 - (2 : ℤ) * q.k))).rpow (1 / 2) := by
            rw [show (-1 / 2 : ℝ) = -(1 / 2) by ring, explicit_rpow_neg hsafe0]
            simp only [one_div]
          rw [hlogid, hsafeid]
          ring

lemma transition_envelope
    (h075 : P075Statement) (h076 : P076Statement)
    (h077 : P077Statement) (h078 : P078Statement)
    (h079 : P079Statement) (h080 : P080Statement)
    (h085 : P085Statement) (h086 : P086Statement) : P087Statement := by
  intro theta htheta
  rcases h075 theta htheta with ⟨CtrSm, hCtrSm, hSm⟩
  rcases h077 theta htheta with ⟨CtrHigh, hCtrHigh, hHigh⟩
  rcases h085 theta htheta with ⟨CtrA, hCtrA, hA⟩
  rcases h086 theta htheta with ⟨CtrC, hCtrC, hC⟩
  refine ⟨CtrSm * (CtrHigh * CtrA + CtrC), by positivity, ?_⟩
  intro q hq x hx
  have htheta_pos : 0 < q.theta := lt_of_lt_of_le zero_lt_two q.theta_ge_two
  have hxpos : 0 < x := lt_of_le_of_lt (pow_nonneg htheta_pos.le _) hx
  have hsm := hSm q hq x hx
  have hpart := h076 q x hx
  have hh0 := hHigh q hq x hx
  have hh1 := h078 q x hx
  have hh2 := hA q hq x hx
  have hl0 := h079 q x hx
  have hl1 := h080 q x hx
  have hl2 := hC q hq x hx
  have hupper0 := upper_nonneg q.toWeightParameters hxpos.le
  have hterminal0 := terminal_nonneg q.toWeightParameters hxpos.le
  have hupper := upper_le_envelope q.toWeightParameters hxpos.le
  have hterminal := terminal_le_envelope q.toWeightParameters hxpos.le
  have henv0 := envelope_nonneg q.toWeightParameters hxpos.le
  have hhigh : transitionRestricted .high q x ≤
      CtrHigh * CtrA * upperAssemblyEnvelope q.toWeightParameters x := by
    calc
      transitionRestricted .high q x ≤
          CtrHigh * transitionSubstituted .high q x := hh0
      _ ≤ CtrHigh * transitionTransported .high q x := by gcongr
      _ ≤ CtrHigh * (CtrA * upperAssemblyEnvelope q.toWeightParameters x) := by gcongr
      _ = CtrHigh * CtrA * upperAssemblyEnvelope q.toWeightParameters x := by ring
  have hlow : transitionRestricted .low q x ≤
      CtrC * terminalAssemblyEnvelope q.toWeightParameters x := hl0.trans (hl1.trans hl2)
  rw [hpart] at hsm
  calc
    proposition3Subject q.toWeightParameters x ≤
        CtrSm * (transitionRestricted .high q x + transitionRestricted .low q x) := hsm
    _ ≤ CtrSm *
        (CtrHigh * CtrA * upperAssemblyEnvelope q.toWeightParameters x +
          CtrC * terminalAssemblyEnvelope q.toWeightParameters x) := by gcongr
    _ ≤ CtrSm * (CtrHigh * CtrA + CtrC) *
        proposition3Envelope q.toWeightParameters x := by
      apply le_trans (mul_le_mul_of_nonneg_left
        (add_le_add
          (mul_le_mul_of_nonneg_left hupper (mul_nonneg hCtrHigh.le hCtrA.le))
          (mul_le_mul_of_nonneg_left hterminal hCtrC.le)) hCtrSm.le)
      ring_nf
      exact le_rfl

lemma empty_bin : P088Statement := by
  intro q x hx hbin
  unfold proposition3Subject
  apply Finset.sum_eq_zero
  intro n hn
  split_ifs with hnpos
  · unfold fkSharp
    apply mul_eq_zero_of_right
    apply Finset.sum_eq_zero
    intro d hd
    apply Finset.sum_eq_zero
    intro d' hd'
    apply Finset.sum_eq_zero
    intro t ht
    split_ifs with hdpos hd'pos hidx
    · have htheta_one : 1 < q.theta := lt_of_lt_of_le one_lt_two q.theta_ge_two
      have hk_ne : q.k ≠ 0 := Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one q.k_pos)
      have hpow_one : 1 < q.theta ^ q.k := one_lt_pow₀ htheta_one hk_ne
      have hd_one : d ≠ 1 := by
        intro heq
        subst d
        norm_num at hidx
        nlinarith
      obtain ⟨p, hpprime, hpdvd⟩ := Nat.exists_prime_and_dvd hd_one
      have hpd : p ≤ d := Nat.le_of_dvd hdpos hpdvd
      have hp_sigma : (p : ℝ) < q.sigma := by
        have hdnext : (d : ℝ) < q.theta ^ (q.k + 1) := hidx.2.2.1
        have hpdr : (p : ℝ) ≤ (d : ℝ) := by exact_mod_cast hpd
        exact hpdr.trans_lt (hdnext.trans_le hbin)
      have hrough : roughIndicator d q.sigma = 0 := by
        have hnrough : ¬ IsRough d q.sigma := by
          intro hr
          exact (not_lt_of_ge (hr p hpprime hpdvd)) hp_sigma
        simp [roughIndicator, hnrough]
      rw [hrough]
      simp
    · rfl
    · rfl
    · rfl
  · rfl

theorem result : ROOT10Target := by
  intro h070 h074 h075 h076 h077 h078 h079 h080 h081 h082 h083 h084
  have h085 : P085Statement := transition_high_assembly h070 h081 h082 h084
  have h086 : P086Statement := transition_low_assembly h070 h081 h083 h084
  have h087 : P087Statement :=
    transition_envelope h075 h076 h077 h078 h079 h080 h085 h086
  have h088 : P088Statement := empty_bin
  intro theta htheta
  rcases h074 theta htheta with ⟨Creg, hCreg, hreg⟩
  rcases h087 theta htheta with ⟨Ctr, hCtr, htr⟩
  let C3 : ℝ := max Creg Ctr
  refine ⟨C3, lt_of_lt_of_le hCreg (le_max_left _ _), ?_⟩
  intro q hq x hx
  have htheta_pos : 0 < q.theta := lt_of_lt_of_le zero_lt_two q.theta_ge_two
  have hxpos : 0 < x := lt_of_le_of_lt (pow_nonneg htheta_pos.le _) hx
  have henv0 := envelope_nonneg q hxpos.le
  by_cases hregular : q.sigma ≤ q.theta ^ q.k
  · have h := hreg q hq hregular x hx
    have hconst : Creg / q.y ≤ C3 / q.y := by
      exact div_le_div_of_nonneg_right (le_max_left _ _) q.y_pos.le
    exact h.trans (mul_le_mul_of_nonneg_right hconst henv0)
  · by_cases htransition : q.sigma < q.theta ^ (q.k + 1)
    · let tq : TransitionParameters :=
        { toWeightParameters := q,
          sigma_gt_bin := lt_of_not_ge hregular,
          sigma_lt_next_bin := htransition }
      have h := htr tq (by simpa [tq] using hq) x (by simpa [tq] using hx)
      have hconst : Ctr ≤ C3 / q.y := by
        have hCtrC3 : Ctr ≤ C3 := le_max_right _ _
        have hC3pos : 0 < C3 := lt_of_lt_of_le hCreg (le_max_left _ _)
        have hC3scale : C3 ≤ C3 / q.y := by
          rw [le_div_iff₀ q.y_pos]
          exact mul_le_of_le_one_right hC3pos.le (le_of_lt q.y_lt_one)
        exact hCtrC3.trans hC3scale
      simpa [tq] using h.trans (mul_le_mul_of_nonneg_right hconst henv0)
    · have hempty := h088 q x hxpos (le_of_not_gt htransition)
      rw [hempty]
      have hC3 : 0 < C3 := lt_of_lt_of_le hCreg (le_max_left _ _)
      exact mul_nonneg (div_nonneg hC3.le q.y_pos.le) henv0

end

end Erdos448.Stage7.ROOT10.Work
