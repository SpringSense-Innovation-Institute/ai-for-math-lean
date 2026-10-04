module

import all Mathlib.Basic.Real.Basic
public import Erdos448.stage6.TaskContracts

public section

set_option backward.isDefEq.respectTransparency false

namespace Erdos448.Stage7.ROOT08.Work

open Finset
open scoped BigOperators

open Erdos448.Stage4
open Erdos448.Stage4.Contracts
open Erdos448.Stage6.TaskContracts

noncomputable section

lemma safeLog_pos (z : ℝ) : 0 < safeLog z := by
  simp only [safeLog]
  exact lt_of_lt_of_le (by norm_num) (le_max_left 1 (Real.log z))

lemma safeLog_rpow_neg_half (z : ℝ) :
    (safeLog z).rpow (-1 / 2) = 1 / (safeLog z).rpow (1 / 2) := by
  simpa only [one_div, neg_div, Real.rpow_eq_pow] using
    (Real.rpow_neg (le_of_lt (safeLog_pos z)) (1 / 2 : ℝ))

lemma log_sigma_pos (q : WeightParameters) : 0 < Real.log q.sigma := by
  apply Real.log_pos
  nlinarith [q.theta_ge_two, q.sigma_ge_theta]

lemma convolutionA_nonneg (q : WeightParameters) (x : ℝ) (hx : 0 ≤ x) :
    0 ≤ convolutionA q x := by
  unfold convolutionA
  apply mul_nonneg
  · exact mul_nonneg
      (div_nonneg hx (pow_nonneg (le_trans (by norm_num) q.theta_ge_two) _))
      (Real.rpow_nonneg (by exact_mod_cast Nat.zero_le q.k) _)
  · apply Finset.sum_nonneg
    intro m hm
    exact mul_nonneg
      (div_nonneg (Real.rpow_nonneg (le_of_lt (safeLog_pos _)) _) (by positivity))
      (Real.rpow_nonneg (le_of_lt (safeLog_pos _)) _)

lemma convolutionBEnlarged_nonneg
    (q : WeightParameters) (x : ℝ) (hx : 0 ≤ x) :
    0 ≤ convolutionBEnlarged q x := by
  unfold convolutionBEnlarged
  apply mul_nonneg
    (div_nonneg hx (pow_nonneg (le_trans (by norm_num) q.theta_ge_two) _))
  apply Finset.sum_nonneg
  intro m hm
  split_ifs
  · exact mul_nonneg
      (div_nonneg (Real.rpow_nonneg (le_of_lt (safeLog_pos _)) _) (by positivity))
      (Real.rpow_nonneg (le_of_lt (safeLog_pos _)) _)
  · positivity

lemma upperEnvelope_nonneg (q : WeightParameters) (x : ℝ) (hx : 0 ≤ x) :
    0 ≤ upperAssemblyEnvelope q x := by
  unfold upperAssemblyEnvelope
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg hx (Real.rpow_nonneg (le_of_lt (log_sigma_pos q)) _))
      (Real.rpow_nonneg (by exact_mod_cast Nat.zero_le q.k) _))
    (Real.rpow_nonneg (by exact_mod_cast Nat.zero_le q.k) _)

lemma middleEnvelope_nonneg (q : WeightParameters) (x : ℝ) (hx : 0 ≤ x) :
    0 ≤ middleAssemblyEnvelope q x := by
  unfold middleAssemblyEnvelope
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg hx (Real.rpow_nonneg (le_of_lt (log_sigma_pos q)) _))
      (Real.rpow_nonneg (by exact_mod_cast Nat.zero_le q.k) _))
    (Real.rpow_nonneg (le_of_lt (safeLog_pos _)) _)

lemma terminalEnvelope_nonneg (q : WeightParameters) (x : ℝ) (hx : 0 ≤ x) :
    0 ≤ terminalAssemblyEnvelope q x := by
  unfold terminalAssemblyEnvelope
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg hx (Real.rpow_nonneg (le_of_lt (log_sigma_pos q)) _))
      (Real.rpow_nonneg (by exact_mod_cast Nat.zero_le q.k) _))
    (div_nonneg (Real.rpow_nonneg (le_of_lt (log_sigma_pos q)) _)
      (Real.rpow_nonneg (le_of_lt (safeLog_pos _)) _))

lemma log_rpow_halves (q : WeightParameters) :
    (Real.log q.sigma).rpow (-q.y / 2) *
        (Real.log q.sigma).rpow (-q.y / 2) =
      (Real.log q.sigma).rpow (-q.y) := by
  have hlog : 0 < Real.log q.sigma := log_sigma_pos q
  calc
    (Real.log q.sigma).rpow (-q.y / 2) *
          (Real.log q.sigma).rpow (-q.y / 2) =
        (Real.log q.sigma).rpow (-q.y / 2 + -q.y / 2) :=
      (Real.rpow_add hlog _ _).symm
    _ = (Real.log q.sigma).rpow (-q.y) := by congr 1 <;> ring

lemma k_rpow_assembly (q : WeightParameters) :
    (q.k : ℝ).rpow (q.y / 2 - 1) * (q.k : ℝ).rpow (-1 / 2) =
      (q.k : ℝ).rpow ((q.y - 3) / 2) := by
  have hk : 0 < (q.k : ℝ) := by exact_mod_cast q.k_pos
  calc
    (q.k : ℝ).rpow (q.y / 2 - 1) * (q.k : ℝ).rpow (-1 / 2) =
        (q.k : ℝ).rpow ((q.y / 2 - 1) + (-1 / 2)) :=
      (Real.rpow_add hk _ _).symm
    _ = (q.k : ℝ).rpow ((q.y - 3) / 2) := by congr 1 <;> ring

lemma theta_pow_cancel (q : WeightParameters) :
    q.theta ^ q.k * q.theta ^ q.k / q.theta ^ (2 * q.k) = 1 := by
  have htheta : q.theta ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num) q.theta_ge_two)
  rw [show 2 * q.k = q.k + q.k by omega, pow_add]
  field_simp

theorem p071
    (h058 : P058Statement) (h068 : P068Statement) (h070 : P070Statement) :
    P071Statement := by
  obtain ⟨CA, hCA, hAbound⟩ := h068
  obtain ⟨family⟩ := h070
  intro theta htheta
  obtain ⟨Cout, hCout, hOuter⟩ := h058 theta htheta
  let C4 : ℝ := p070C4
    { Cfam := family.Cfam, Cfam_pos := family.Cfam_pos,
      theta := theta, theta_ge_two := htheta }
  have hC4 : 0 < C4 := family.c4_positive theta htheta
  refine ⟨Cout * C4 * CA, by positivity, ?_⟩
  intro q hq hSigma x hx
  have hxpos : 0 ≤ x := by
    have htheta_pos : 0 < q.theta := lt_of_lt_of_le (by norm_num) q.theta_ge_two
    have : 0 < q.theta ^ (2 * q.k - 1) := pow_pos htheta_pos _
    linarith
  have hconv_nonneg := convolutionA_nonneg q x hxpos
  have hlog_nonneg : 0 ≤ (Real.log q.sigma).rpow (-q.y / 2) :=
    Real.rpow_nonneg (le_of_lt (log_sigma_pos q)) _
  have hOuterCoeff :
      0 ≤ Cout * q.theta ^ q.k * (Real.log q.sigma).rpow (-q.y / 2) *
        (q.k : ℝ).rpow (q.y / 2 - 1) := by
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (le_of_lt hCout)
          (pow_nonneg (le_trans (by norm_num) q.theta_ge_two) _))
        hlog_nonneg)
      (Real.rpow_nonneg (by exact_mod_cast Nat.zero_le q.k) _)
  have hWindowBound :
      0 ≤ C4 * q.theta ^ q.k * (q.k : ℝ).rpow (-1 / 2) := by
    exact mul_nonneg
      (mul_nonneg (le_of_lt hC4)
        (pow_nonneg (le_trans (by norm_num) q.theta_ge_two) _))
      (Real.rpow_nonneg (by exact_mod_cast Nat.zero_le q.k) _)
  have hout := hOuter q hq hSigma
  have hwindow := family.window q
  have hconv := hAbound q x hx
  have hC4eq :
      p070C4
          { Cfam := family.Cfam, Cfam_pos := family.Cfam_pos,
            theta := q.theta, theta_ge_two := q.theta_ge_two } = C4 := by
    simp [C4, p070C4, hq]
  rw [hC4eq] at hwindow
  rw [regularA]
  calc
    (Real.log q.sigma).rpow (-q.y / 2) * regularOuter q * convolutionA q x
        ≤ (Real.log q.sigma).rpow (-q.y / 2) *
            (Cout * q.theta ^ q.k * (Real.log q.sigma).rpow (-q.y / 2) *
              (q.k : ℝ).rpow (q.y / 2 - 1) * w4WindowSum q) *
            convolutionA q x := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hout hlog_nonneg) hconv_nonneg
    _ ≤ (Real.log q.sigma).rpow (-q.y / 2) *
            (Cout * q.theta ^ q.k * (Real.log q.sigma).rpow (-q.y / 2) *
              (q.k : ℝ).rpow (q.y / 2 - 1) *
              (C4 * q.theta ^ q.k * (q.k : ℝ).rpow (-1 / 2))) *
            convolutionA q x := by
          apply mul_le_mul_of_nonneg_right _ hconv_nonneg
          apply mul_le_mul_of_nonneg_left _ hlog_nonneg
          exact mul_le_mul_of_nonneg_left hwindow hOuterCoeff
    _ ≤ (Real.log q.sigma).rpow (-q.y / 2) *
            (Cout * q.theta ^ q.k * (Real.log q.sigma).rpow (-q.y / 2) *
              (q.k : ℝ).rpow (q.y / 2 - 1) *
              (C4 * q.theta ^ q.k * (q.k : ℝ).rpow (-1 / 2))) *
            (CA * (x / q.theta ^ (2 * q.k)) *
              (q.k : ℝ).rpow ((q.y - 1) / 2)) := by
          exact mul_le_mul_of_nonneg_left hconv
            (mul_nonneg hlog_nonneg (mul_nonneg hOuterCoeff hWindowBound))
    _ = (Cout * C4 * CA) * upperAssemblyEnvelope q x := by
      rw [upperAssemblyEnvelope]
      calc
        _ = ((Real.log q.sigma).rpow (-q.y / 2) *
              (Real.log q.sigma).rpow (-q.y / 2)) *
            ((q.k : ℝ).rpow (q.y / 2 - 1) * (q.k : ℝ).rpow (-1 / 2)) *
            (q.theta ^ q.k * q.theta ^ q.k / q.theta ^ (2 * q.k)) *
            (Cout * C4 * CA * x * (q.k : ℝ).rpow ((q.y - 1) / 2)) := by ring
        _ = _ := by
          rw [log_rpow_halves q, k_rpow_assembly q, theta_pow_cancel q]
          ring

theorem p072
    (h058 : P058Statement) (h069 : P069Statement) (h070 : P070Statement) :
    P072Statement := by
  obtain ⟨Cmc, hCmc, hBbound⟩ := h069
  obtain ⟨family⟩ := h070
  intro theta htheta
  obtain ⟨Cout, hCout, hOuter⟩ := h058 theta htheta
  let C4 : ℝ := p070C4
    { Cfam := family.Cfam, Cfam_pos := family.Cfam_pos,
      theta := theta, theta_ge_two := htheta }
  have hC4 : 0 < C4 := family.c4_positive theta htheta
  refine ⟨Cout * C4 * Cmc, by positivity, ?_⟩
  intro q hq hSigma x hx
  have hxpos : 0 ≤ x := by
    have htheta_pos : 0 < q.theta := lt_of_lt_of_le (by norm_num) q.theta_ge_two
    have : 0 < q.theta ^ (2 * q.k - 1) := pow_pos htheta_pos _
    linarith
  have hconv_nonneg := convolutionBEnlarged_nonneg q x hxpos
  have hlog_nonneg : 0 ≤ (Real.log q.sigma).rpow (-q.y / 2) :=
    Real.rpow_nonneg (le_of_lt (log_sigma_pos q)) _
  have hOuterCoeff :
      0 ≤ Cout * q.theta ^ q.k * (Real.log q.sigma).rpow (-q.y / 2) *
        (q.k : ℝ).rpow (q.y / 2 - 1) := by
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (le_of_lt hCout)
          (pow_nonneg (le_trans (by norm_num) q.theta_ge_two) _))
        hlog_nonneg)
      (Real.rpow_nonneg (by exact_mod_cast Nat.zero_le q.k) _)
  have hWindowBound :
      0 ≤ C4 * q.theta ^ q.k * (q.k : ℝ).rpow (-1 / 2) := by
    exact mul_nonneg
      (mul_nonneg (le_of_lt hC4)
        (pow_nonneg (le_trans (by norm_num) q.theta_ge_two) _))
      (Real.rpow_nonneg (by exact_mod_cast Nat.zero_le q.k) _)
  have hout := hOuter q hq hSigma
  have hwindow := family.window q
  have hconv := hBbound.enlarged q x hx
  have hC4eq :
      p070C4
          { Cfam := family.Cfam, Cfam_pos := family.Cfam_pos,
            theta := q.theta, theta_ge_two := q.theta_ge_two } = C4 := by
    simp [C4, p070C4, hq]
  rw [hC4eq] at hwindow
  rw [regularB]
  calc
    (Real.log q.sigma).rpow (-q.y / 2) * regularOuter q *
          convolutionBEnlarged q x
        ≤ (Real.log q.sigma).rpow (-q.y / 2) *
            (Cout * q.theta ^ q.k * (Real.log q.sigma).rpow (-q.y / 2) *
              (q.k : ℝ).rpow (q.y / 2 - 1) * w4WindowSum q) *
            convolutionBEnlarged q x := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hout hlog_nonneg) hconv_nonneg
    _ ≤ (Real.log q.sigma).rpow (-q.y / 2) *
            (Cout * q.theta ^ q.k * (Real.log q.sigma).rpow (-q.y / 2) *
              (q.k : ℝ).rpow (q.y / 2 - 1) *
              (C4 * q.theta ^ q.k * (q.k : ℝ).rpow (-1 / 2))) *
            convolutionBEnlarged q x := by
          apply mul_le_mul_of_nonneg_right _ hconv_nonneg
          apply mul_le_mul_of_nonneg_left _ hlog_nonneg
          exact mul_le_mul_of_nonneg_left hwindow hOuterCoeff
    _ ≤ (Real.log q.sigma).rpow (-q.y / 2) *
            (Cout * q.theta ^ q.k * (Real.log q.sigma).rpow (-q.y / 2) *
              (q.k : ℝ).rpow (q.y / 2 - 1) *
              (C4 * q.theta ^ q.k * (q.k : ℝ).rpow (-1 / 2))) *
            ((Cmc / q.y) * (x / q.theta ^ (2 * q.k)) *
              (safeLog (2 * x * q.theta ^ (1 - (2 : ℤ) * q.k))).rpow
                ((q.y - 1) / 2)) := by
          exact mul_le_mul_of_nonneg_left hconv
            (mul_nonneg hlog_nonneg (mul_nonneg hOuterCoeff hWindowBound))
    _ = ((Cout * C4 * Cmc) / q.y) * middleAssemblyEnvelope q x := by
      rw [middleAssemblyEnvelope]
      calc
        _ = ((Real.log q.sigma).rpow (-q.y / 2) *
              (Real.log q.sigma).rpow (-q.y / 2)) *
            ((q.k : ℝ).rpow (q.y / 2 - 1) * (q.k : ℝ).rpow (-1 / 2)) *
            (q.theta ^ q.k * q.theta ^ q.k / q.theta ^ (2 * q.k)) *
            ((Cout * C4 * Cmc / q.y) * x *
              (safeLog (2 * x * q.theta ^ (1 - (2 : ℤ) * q.k))).rpow
                ((q.y - 1) / 2)) := by ring
        _ = _ := by
          rw [log_rpow_halves q, k_rpow_assembly q, theta_pow_cancel q]
          ring

theorem p073
    (h058 : P058Statement) (h070 : P070Statement) : P073Statement := by
  obtain ⟨family⟩ := h070
  intro theta htheta
  obtain ⟨Cout, hCout, hOuter⟩ := h058 theta htheta
  let C4 : ℝ := p070C4
    { Cfam := family.Cfam, Cfam_pos := family.Cfam_pos,
      theta := theta, theta_ge_two := htheta }
  have hC4 : 0 < C4 := family.c4_positive theta htheta
  refine ⟨Cout * C4, by positivity, ?_⟩
  intro q hq hSigma x hx
  have hxpos : 0 ≤ x := by
    have htheta_pos : 0 < q.theta := lt_of_lt_of_le (by norm_num) q.theta_ge_two
    have : 0 < q.theta ^ (2 * q.k - 1) := pow_pos htheta_pos _
    linarith
  have hlog_nonneg : 0 ≤ (Real.log q.sigma).rpow (-q.y / 2) :=
    Real.rpow_nonneg (le_of_lt (log_sigma_pos q)) _
  have hOuterCoeff :
      0 ≤ Cout * q.theta ^ q.k * (Real.log q.sigma).rpow (-q.y / 2) *
        (q.k : ℝ).rpow (q.y / 2 - 1) := by
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (le_of_lt hCout)
          (pow_nonneg (le_trans (by norm_num) q.theta_ge_two) _))
        hlog_nonneg)
      (Real.rpow_nonneg (by exact_mod_cast Nat.zero_le q.k) _)
  have hWindowBound :
      0 ≤ C4 * q.theta ^ q.k * (q.k : ℝ).rpow (-1 / 2) := by
    exact mul_nonneg
      (mul_nonneg (le_of_lt hC4)
        (pow_nonneg (le_trans (by norm_num) q.theta_ge_two) _))
      (Real.rpow_nonneg (by exact_mod_cast Nat.zero_le q.k) _)
  have hTail_nonneg :
      0 ≤ x / q.theta ^ (2 * q.k) * (Real.log q.sigma).rpow (q.y / 2) *
        (safeLog (2 * x * q.theta ^ (1 - (2 : ℤ) * q.k))).rpow (-1 / 2) := by
    exact mul_nonneg
      (mul_nonneg (div_nonneg hxpos
          (pow_nonneg (le_trans (by norm_num) q.theta_ge_two) _))
        (Real.rpow_nonneg (le_of_lt (log_sigma_pos q)) _))
      (Real.rpow_nonneg (le_of_lt (safeLog_pos _)) _)
  have hout := hOuter q hq hSigma
  have hwindow := family.window q
  have hC4eq :
      p070C4
          { Cfam := family.Cfam, Cfam_pos := family.Cfam_pos,
            theta := q.theta, theta_ge_two := q.theta_ge_two } = C4 := by
    simp [C4, p070C4, hq]
  rw [hC4eq] at hwindow
  rw [regularC, convolutionC]
  calc
    (Real.log q.sigma).rpow (-q.y / 2) * regularOuter q *
          (x / q.theta ^ (2 * q.k) * (Real.log q.sigma).rpow (q.y / 2) *
            (safeLog (2 * x * q.theta ^ (1 - (2 : ℤ) * q.k))).rpow (-1 / 2))
        ≤ (Real.log q.sigma).rpow (-q.y / 2) *
            (Cout * q.theta ^ q.k * (Real.log q.sigma).rpow (-q.y / 2) *
              (q.k : ℝ).rpow (q.y / 2 - 1) * w4WindowSum q) *
            (x / q.theta ^ (2 * q.k) * (Real.log q.sigma).rpow (q.y / 2) *
              (safeLog (2 * x * q.theta ^ (1 - (2 : ℤ) * q.k))).rpow
                (-1 / 2)) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hout hlog_nonneg) hTail_nonneg
    _ ≤ (Real.log q.sigma).rpow (-q.y / 2) *
            (Cout * q.theta ^ q.k * (Real.log q.sigma).rpow (-q.y / 2) *
              (q.k : ℝ).rpow (q.y / 2 - 1) *
              (C4 * q.theta ^ q.k * (q.k : ℝ).rpow (-1 / 2))) *
            (x / q.theta ^ (2 * q.k) * (Real.log q.sigma).rpow (q.y / 2) *
              (safeLog (2 * x * q.theta ^ (1 - (2 : ℤ) * q.k))).rpow
                (-1 / 2)) := by
          apply mul_le_mul_of_nonneg_right _ hTail_nonneg
          apply mul_le_mul_of_nonneg_left _ hlog_nonneg
          exact mul_le_mul_of_nonneg_left hwindow hOuterCoeff
    _ = (Cout * C4) * terminalAssemblyEnvelope q x := by
      rw [terminalAssemblyEnvelope, safeLog_rpow_neg_half]
      calc
        _ = ((Real.log q.sigma).rpow (-q.y / 2) *
              (Real.log q.sigma).rpow (-q.y / 2)) *
            ((q.k : ℝ).rpow (q.y / 2 - 1) * (q.k : ℝ).rpow (-1 / 2)) *
            (q.theta ^ q.k * q.theta ^ q.k / q.theta ^ (2 * q.k)) *
            (Cout * C4 * x * (Real.log q.sigma).rpow (q.y / 2) *
              (1 / (safeLog
                (2 * x * q.theta ^ (1 - (2 : ℤ) * q.k))).rpow (1 / 2))) := by ring
        _ = _ := by
          rw [log_rpow_halves q, k_rpow_assembly q, theta_pow_cancel q]
          ring

theorem result : ROOT08Target := by
  intro h058 h060 h061 h062 h063 h064 h065 h066 h067 h068 h069 h070
  have h071 : P071Statement := p071 h058 h068 h070
  have h072 : P072Statement := p072 h058 h069 h070
  have h073 : P073Statement := p073 h058 h070
  intro theta htheta
  obtain ⟨Csm, hCsm, hSmooth⟩ := h060 theta htheta
  obtain ⟨Cup, hCup, hUpperSub⟩ := h062 theta htheta
  obtain ⟨CA, hCA, hUpperTransport⟩ := h063 theta htheta
  obtain ⟨Cmid, hCmid, hMiddleSub⟩ := h064 theta htheta
  obtain ⟨CB, hCB, hMiddleTransport⟩ := h065 theta htheta
  obtain ⟨CC, hCC, hTerminalTransport⟩ := h067 theta htheta
  obtain ⟨CAasm, hCAasm, hUpperAssembly⟩ := h071 theta htheta
  obtain ⟨CBasm, hCBasm, hMiddleAssembly⟩ := h072 theta htheta
  obtain ⟨CCasm, hCCasm, hTerminalAssembly⟩ := h073 theta htheta
  let Kupper : ℝ := Csm * Cup * CA * CAasm
  let Kmiddle : ℝ := Csm * Cmid * CB * CBasm
  let Kterminal : ℝ := Csm * CC * CCasm
  let Creg : ℝ := Kupper + Kmiddle + Kterminal
  have hKupper : 0 < Kupper := by positivity
  have hKmiddle : 0 < Kmiddle := by positivity
  have hKterminal : 0 < Kterminal := by positivity
  have hCreg : 0 < Creg := by positivity
  refine ⟨Creg, hCreg, ?_⟩
  intro q hq hSigma x hx
  have hxpos : 0 ≤ x := by
    have htheta_pos : 0 < q.theta := lt_of_lt_of_le (by norm_num) q.theta_ge_two
    have : 0 < q.theta ^ (2 * q.k - 1) := pow_pos htheta_pos _
    linarith
  have hUpperEnv : 0 ≤ upperAssemblyEnvelope q x := upperEnvelope_nonneg q x hxpos
  have hMiddleEnv : 0 ≤ middleAssemblyEnvelope q x := middleEnvelope_nonneg q x hxpos
  have hTerminalEnv : 0 ≤ terminalAssemblyEnvelope q x :=
    terminalEnvelope_nonneg q x hxpos
  have hUpper :
      Csm * smoothedRegular .upper q x ≤ Kupper * upperAssemblyEnvelope q x := by
    calc
      Csm * smoothedRegular .upper q x
          ≤ Csm * (Cup * substitutedRegular .upper q x) := by
            gcongr
            exact hUpperSub q hq hSigma x hx
      _ ≤ Csm * (Cup * (CA * regularA q x)) := by
            gcongr
            exact hUpperTransport q hq hSigma x hx
      _ ≤ Csm * (Cup * (CA * (CAasm * upperAssemblyEnvelope q x))) := by
            gcongr
            exact hUpperAssembly q hq hSigma x hx
      _ = Kupper * upperAssemblyEnvelope q x := by ring
  have hMiddle :
      Csm * smoothedRegular .middle q x ≤
        (Kmiddle / q.y) * middleAssemblyEnvelope q x := by
    calc
      Csm * smoothedRegular .middle q x
          ≤ Csm * (Cmid * substitutedRegular .middle q x) := by
            gcongr
            exact hMiddleSub q hq hSigma x hx
      _ ≤ Csm * (Cmid * (CB * regularB q x)) := by
            gcongr
            exact hMiddleTransport q hq hSigma x hx
      _ ≤ Csm * (Cmid * (CB * ((CBasm / q.y) * middleAssemblyEnvelope q x))) := by
            gcongr
            exact hMiddleAssembly q hq hSigma x hx
      _ = (Kmiddle / q.y) * middleAssemblyEnvelope q x := by ring
  have hTerminal :
      Csm * smoothedRegular .terminal q x ≤
        Kterminal * terminalAssemblyEnvelope q x := by
    calc
      Csm * smoothedRegular .terminal q x
          ≤ Csm * substitutedRegular .terminal q x := by
            gcongr
            exact h066 q hSigma x hx
      _ ≤ Csm * (CC * regularC q x) := by
            gcongr
            exact hTerminalTransport q hq hSigma x hx
      _ ≤ Csm * (CC * (CCasm * terminalAssemblyEnvelope q x)) := by
            gcongr
            exact hTerminalAssembly q hq hSigma x hx
      _ = Kterminal * terminalAssemblyEnvelope q x := by ring
  have hKupper_le : Kupper ≤ Creg / q.y := by
    apply (le_div_iff₀ q.y_pos).2
    have hy : q.y ≤ 1 := le_of_lt q.y_lt_one
    have : Kupper ≤ Creg := by
      dsimp [Creg]
      nlinarith [le_of_lt hKmiddle, le_of_lt hKterminal]
    nlinarith
  have hKmiddle_le : Kmiddle / q.y ≤ Creg / q.y := by
    apply div_le_div_of_nonneg_right
    · dsimp [Creg]
      nlinarith [le_of_lt hKupper, le_of_lt hKterminal]
    · exact le_of_lt q.y_pos
  have hKterminal_le : Kterminal ≤ Creg / q.y := by
    apply (le_div_iff₀ q.y_pos).2
    have hy : q.y ≤ 1 := le_of_lt q.y_lt_one
    have : Kterminal ≤ Creg := by
      dsimp [Creg]
      nlinarith [le_of_lt hKupper, le_of_lt hKmiddle]
    nlinarith
  calc
    proposition3Subject q x
        ≤ Csm * smoothedRegular .whole q x := hSmooth q hq hSigma x hx
    _ = Csm * (smoothedRegular .upper q x + smoothedRegular .middle q x +
          smoothedRegular .terminal q x) := by rw [h061 q hSigma x hx]
    _ = Csm * smoothedRegular .upper q x +
          Csm * smoothedRegular .middle q x +
          Csm * smoothedRegular .terminal q x := by ring
    _ ≤ Kupper * upperAssemblyEnvelope q x +
          (Kmiddle / q.y) * middleAssemblyEnvelope q x +
          Kterminal * terminalAssemblyEnvelope q x := by gcongr
    _ ≤ (Creg / q.y) * upperAssemblyEnvelope q x +
          (Creg / q.y) * middleAssemblyEnvelope q x +
          (Creg / q.y) * terminalAssemblyEnvelope q x := by gcongr
    _ = (Creg / q.y) * proposition3Envelope q x := by
      rw [proposition3Envelope, proposition3Braces, upperAssemblyEnvelope,
        middleAssemblyEnvelope, terminalAssemblyEnvelope]
      ring

end

end Erdos448.Stage7.ROOT08.Work
