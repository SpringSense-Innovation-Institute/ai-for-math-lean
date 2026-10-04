module

import all Mathlib.Basic.Real.Basic
public import Erdos448.stage7.tasks.«ROOT-01».Elementary
public import Mathlib.NumberTheory.EulerProduct.Basic

public section

set_option backward.isDefEq.respectTransparency false

namespace Erdos448.Stage7.ROOT01

open Erdos448.Stage4
open Erdos448.Stage4.Contracts
open Finset Nat
open scoped BigOperators

noncomputable section

@[expose] def localCoefficientProduct
    (a : ℕ → ℕ → ℝ) (s : Finset ℕ) (n : ℕ) : ℝ :=
  ∏ p ∈ s, a p (n.factorization p)

lemma factorization_pow_mul_at_head
    {s : Finset ℕ} {p e m : ℕ} (hp : p.Prime) (hps : p ∉ s)
    (hm : m ∈ factoredNumbers s) :
    (p ^ e * m).factorization p = e := by
  rw [Nat.factorization_mul_apply_of_coprime
    ((hp.factoredNumbers_coprime hps hm).pow_left e)]
  simp [hp.factorization_pow,
    Nat.factorization_eq_zero_of_not_dvd
      (hp.coprime_iff_not_dvd.mp (hp.factoredNumbers_coprime hps hm))]

lemma factorization_pow_mul_at_tail
    {s : Finset ℕ} {p q e m : ℕ} (hp : p.Prime) (hps : p ∉ s)
    (hq : q ∈ s) (hm : m ∈ factoredNumbers s) :
    (p ^ e * m).factorization q = m.factorization q := by
  have hpq : p ≠ q := by
    intro hpq
    exact hps (hpq ▸ hq)
  rw [Nat.factorization_mul_apply_of_coprime
    ((hp.factoredNumbers_coprime hps hm).pow_left e)]
  rw [hp.factorization_pow]
  simp [hpq]

lemma localCoefficientProduct_insert
    (a : ℕ → ℕ → ℝ) {s : Finset ℕ} {p e : ℕ}
    (hp : p.Prime) (hps : p ∉ s) (m : factoredNumbers s) :
    localCoefficientProduct a (insert p s) (p ^ e * m.1) =
      a p e * localCoefficientProduct a s m.1 := by
  rw [localCoefficientProduct, Finset.prod_insert hps,
    factorization_pow_mul_at_head hp hps m.2]
  congr 1
  apply Finset.prod_congr rfl
  intro q hq
  rw [factorization_pow_mul_at_tail hp hps hq m.2]

set_option maxHeartbeats 1000000 in
lemma finiteEulerExpansion
    (a : ℕ → ℕ → ℝ) (s : Finset ℕ)
    (hsPrime : ∀ p ∈ s, p.Prime)
    (haNonneg : ∀ p ∈ s, ∀ e : ℕ, 0 ≤ a p e)
    (haSum : ∀ p ∈ s, Summable (a p)) :
    Summable (fun n : factoredNumbers s =>
      localCoefficientProduct a s n.1) ∧
    HasSum (fun n : factoredNumbers s =>
      localCoefficientProduct a s n.1)
      (∏ p ∈ s, ∑' e : ℕ, a p e) := by
  induction s using Finset.induction with
  | empty =>
      rw [factoredNumbers_empty]
      simp only [notMem_empty, IsEmpty.forall_iff, forall_const,
        localCoefficientProduct, prod_empty]
      exact ⟨(Set.finite_singleton 1).summable (fun _ => (1 : ℝ)),
        hasSum_singleton 1 (fun _ => (1 : ℝ))⟩
  | @insert p s hps ih =>
      have hp : p.Prime := hsPrime p (Finset.mem_insert_self p s)
      have hsPrime' : ∀ q ∈ s, q.Prime := fun q hq =>
        hsPrime q (Finset.mem_insert_of_mem hq)
      have haNonneg' : ∀ q ∈ s, ∀ e : ℕ, 0 ≤ a q e := fun q hq =>
        haNonneg q (Finset.mem_insert_of_mem hq)
      have haSum' : ∀ q ∈ s, Summable (a q) := fun q hq =>
        haSum q (Finset.mem_insert_of_mem hq)
      have hi := ih hsPrime' haNonneg' haSum'
      have hpSum : Summable (a p) := haSum p (Finset.mem_insert_self p s)
      have hpNonneg : ∀ e : ℕ, 0 ≤ a p e := fun e =>
        haNonneg p (Finset.mem_insert_self p s) e
      have hcoeff : (fun x : ℕ × factoredNumbers s =>
          localCoefficientProduct a (insert p s)
            ((equivProdNatFactoredNumbers hp hps x).1)) =
          fun x => a p x.1 * localCoefficientProduct a s x.2.1 := by
        funext x
        rw [equivProdNatFactoredNumbers_apply',
          localCoefficientProduct_insert a hp hps x.2]
      have hprodSum : Summable (fun x : ℕ × factoredNumbers s =>
          a p x.1 * localCoefficientProduct a s x.2.1) :=
        Summable.mul_of_nonneg hpSum hi.1 hpNonneg
          (fun n => Finset.prod_nonneg fun q hq => haNonneg' q hq _)
      constructor
      · rw [← (equivProdNatFactoredNumbers hp hps).summable_iff]
        change Summable (fun x : ℕ × factoredNumbers s =>
          localCoefficientProduct a (insert p s)
            ((equivProdNatFactoredNumbers hp hps x).1))
        rw [hcoeff]
        exact hprodSum
      · rw [Finset.prod_insert hps,
          ← (equivProdNatFactoredNumbers hp hps).hasSum_iff]
        change HasSum (fun x : ℕ × factoredNumbers s =>
          localCoefficientProduct a (insert p s)
            ((equivProdNatFactoredNumbers hp hps x).1)) _
        rw [hcoeff]
        exact hpSum.hasSum.mul hi.2 hprodSum

end

end Erdos448.Stage7.ROOT01
