module

import all Mathlib.Basic.Real.Basic
public import Erdos448.dependencies.«DP-MEAN».stage6.shared.TaskInterfaces

public section

set_option backward.isDefEq.respectTransparency false

namespace Erdos448.DPMean.TaskT09

@[expose] abbrev PublicTarget : Prop := Erdos448.DPMean.S6.T09Target

theorem nat_lt_iff_le_strictCutoff
    {X : ℝ} (hX : 0 < X) (n : ℕ) :
    (n : ℝ) < X ↔ n ≤ strictCutoff X := by
  rw [← Nat.lt_ceil]
  unfold strictCutoff
  have hceil : 0 < Nat.ceil X := Nat.ceil_pos.mpr hX
  omega

theorem strict_factor_comparison
    {X : ℝ} (hX : 2 < X) : DEF024Interface X := by
  let N : ℕ := strictCutoff X
  have hXpos : 0 < X := by linarith
  have hN : 2 ≤ N := by
    dsimp [N, strictCutoff]
    have hceil : 2 < Nat.ceil X := Nat.lt_ceil.mpr hX
    omega
  have hNreal : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hNX : (N : ℝ) < X :=
    (nat_lt_iff_le_strictCutoff hXpos N).2 le_rfl
  have hceil_eq : Nat.ceil X = N + 1 := by
    dsimp [N, strictCutoff]
    have hceil : 0 < Nat.ceil X := Nat.ceil_pos.mpr hXpos
    omega
  have hN_sq : (N : ℝ) + 1 ≤ (N : ℝ) ^ 2 := by
    nlinarith [sq_nonneg ((N : ℝ) - 1)]
  have hXNsq : X ≤ (N : ℝ) ^ 2 := by
    calc
      X ≤ (Nat.ceil X : ℝ) := Nat.le_ceil X
      _ = (N : ℝ) + 1 := by rw [hceil_eq, Nat.cast_add, Nat.cast_one]
      _ ≤ (N : ℝ) ^ 2 := hN_sq
  have hlogNpos : 0 < Real.log (N : ℝ) := Real.log_pos (by linarith)
  have hlogXpos : 0 < Real.log X := Real.log_pos (by linarith)
  have hlog_le : Real.log X ≤ 2 * Real.log (N : ℝ) := by
    calc
      Real.log X ≤ Real.log ((N : ℝ) ^ 2) :=
        Real.log_le_log hXpos hXNsq
      _ = 2 * Real.log (N : ℝ) := by rw [Real.log_pow]; norm_num
  have hmul : (N : ℝ) * Real.log X ≤
      2 * X * Real.log (N : ℝ) := by
    calc
      (N : ℝ) * Real.log X ≤ X * Real.log X :=
        mul_le_mul_of_nonneg_right (le_of_lt hNX) hlogXpos.le
      _ ≤ X * (2 * Real.log (N : ℝ)) :=
        mul_le_mul_of_nonneg_left hlog_le hXpos.le
      _ = 2 * X * Real.log (N : ℝ) := by ring
  dsimp [DEF024Interface, DEF005Interface]
  change (N : ℝ) / Real.log (N : ℝ) ≤ 2 * (X / Real.log X)
  rw [div_le_iff₀ hlogNpos]
  calc
    (N : ℝ) ≤ (2 * X * Real.log (N : ℝ)) / Real.log X :=
      (le_div_iff₀ hlogXpos).2 hmul
    _ = 2 * (X / Real.log X) * Real.log (N : ℝ) := by ring

theorem constructed : PublicTarget := by
  intro X hX
  have hXpos : 0 < X := by linarith
  have hcutoff_one_nat : 1 ≤ strictCutoff X := by
    unfold strictCutoff
    have hceil : 1 < Nat.ceil X :=
      Nat.lt_ceil.mpr (lt_of_lt_of_le (by norm_num) hX)
    omega
  refine {
    integer_endpoint_transport := ?_
    prime_endpoint_transport := ?_
    cutoff_at_least_one := ?_
    strict_cutoff_at_least_two := ?_
    strict_factor_comparison := ?_
  }
  · dsimp [DEF021Interface, DEF005Interface]
    intro n _hn
    constructor
    · intro hn
      exact_mod_cast (nat_lt_iff_le_strictCutoff hXpos n).1 hn
    · intro hn
      exact (nat_lt_iff_le_strictCutoff hXpos n).2 (by exact_mod_cast hn)
  · dsimp [DEF022Interface, DEF005Interface]
    intro p hp
    constructor
    · intro hpX
      exact_mod_cast (nat_lt_iff_le_strictCutoff hXpos p).1 hpX
    · intro hpN
      exact (nat_lt_iff_le_strictCutoff hXpos p).2 (by exact_mod_cast hpN)
  · dsimp [DEF023Interface, DEF005Interface]
    exact_mod_cast hcutoff_one_nat
  · intro hXstrict
    dsimp [DEF005Interface]
    have hcutoff_two_nat : 2 ≤ strictCutoff X := by
      unfold strictCutoff
      have hceil : 2 < Nat.ceil X := Nat.lt_ceil.mpr hXstrict
      omega
    exact_mod_cast hcutoff_two_nat
  · exact strict_factor_comparison

end Erdos448.DPMean.TaskT09
