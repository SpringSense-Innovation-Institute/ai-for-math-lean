module

import all Mathlib.Basic.Real.Basic
public import Erdos448.stage4.contracts.GroupB

public section

set_option backward.isDefEq.respectTransparency false

namespace Erdos448.Stage7.Shared
open Erdos448.Stage4 Erdos448.Stage4.Contracts
open Finset
open scoped BigOperators

/-- The exponent-zero term supplies a family-uniform floor. -/
theorem localEulerFactor_ge_one
    {w b : ArithmeticWeight} {p : ℕ} (hp : p.Prime)
    (hw : NonnegativeMultiplicativeWeight w) (hw1 : w 1 = 1)
    (hb : ModifierSpec b)
    (hs : Summable (fun j : ℕ => w (p ^ j) * b (p ^ j) / (p : ℝ) ^ j)) :
    1 ≤ localEulerFactor w b p := by
  have hnonneg : ∀ j : ℕ, 0 ≤ w (p ^ j) * b (p ^ j) / (p : ℝ) ^ j := by
    intro j
    exact div_nonneg
      (mul_nonneg (hw.nonnegative _ (Nat.pow_pos hp.pos))
        (hb.prime_power_bounds p hp j).1)
      (pow_nonneg (Nat.cast_nonneg p) j)
  have h := hs.sum_le_tsum {0} (fun j _ => hnonneg j)
  simpa [localEulerFactor, hw1, hb.normalized] using h

end Erdos448.Stage7.Shared
