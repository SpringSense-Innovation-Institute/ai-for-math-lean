module

import all Mathlib.Basic.Real.Basic
public import Erdos448.stage7.tasks.«ROOT-04».Helpers

public section

set_option backward.isDefEq.respectTransparency false

namespace Erdos448.Stage7.ROOT04.FiniteSupport

open Erdos448.Stage4
open Erdos448.Stage4.Contracts
open Finset
open scoped BigOperators

noncomputable section

instance (p : Prop) : Decidable p := Classical.propDecidable p

lemma fkSharp_eq_zero_of_lt_pow (q : SharpParameters) (n : PosNat)
    (hpow : (n.1 : ℝ) < q.theta ^ q.k) : fkSharp q n = 0 := by
  unfold fkSharp
  apply mul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro d hd
  have hdle : d ≤ n.1 := by
    simp only [positiveNatsUpTo, Finset.mem_filter, Finset.mem_range] at hd
    omega
  apply Finset.sum_eq_zero
  intro d' hd'
  apply Finset.sum_eq_zero
  intro t ht
  split_ifs with hd0 hd'0 hcond
  · have hdn : (d : ℝ) ≤ n.1 := by exact_mod_cast hdle
    exfalso
    exact (not_le_of_gt (hpow.trans_le' hdn)) hcond.2.1
  all_goals rfl

lemma majorant_summable
    (q : Lemma4Parameters) (y : ℝ) (hy0 : 0 < y) (hy1 : y < 1) (n : PosNat) :
    Summable fun k : ℕ =>
      if lowerBinIndex q.sigma q.theta ≤ k then
        (k : ℝ).rpow (-(1 / 2 + q.epsilonInt) * Real.log y) *
          fkSharp (sharpParametersOf q y hy0 hy1 k) n
      else 0 := by
  have htheta : 1 < q.theta := lt_of_lt_of_le (by norm_num) q.theta_ge_two
  obtain ⟨K, hK⟩ := pow_unbounded_of_one_lt (n.1 : ℝ) htheta
  refine summable_of_ne_finset_zero (s := Finset.range K) ?_
  intro k hk
  have hKk : K ≤ k := by simpa using hk
  have hpmono : q.theta ^ K ≤ q.theta ^ k :=
    pow_le_pow_right₀ (le_of_lt htheta) hKk
  have hnk : (n.1 : ℝ) < q.theta ^ k := hK.trans_le hpmono
  have hzero : fkSharp (sharpParametersOf q y hy0 hy1 k) n = 0 := by
    apply fkSharp_eq_zero_of_lt_pow
    simpa [sharpParametersOf] using hnk
  simp [hzero]

end

end Erdos448.Stage7.ROOT04.FiniteSupport
