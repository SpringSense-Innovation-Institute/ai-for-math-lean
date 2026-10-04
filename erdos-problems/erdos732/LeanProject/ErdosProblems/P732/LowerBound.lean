module

public import LeanProject.ErdosProblems.P732.Asymptotics
public import LeanProject.ErdosProblems.P732.Counting
public import LeanProject.ErdosProblems.P732.Monotonicity
public import LeanProject.ErdosProblems.P732.ProjectivePlanePrimePower

@[expose] public section

noncomputable section
open scoped Filter
open Filter

namespace ErdosProblems
namespace P732

/-!
This file packages the exact lower bound from Theorem 2.3 and the final
asymptotic Erdős #732 statement.
-/

theorem AlonList_injective_on_admissible {q : ℕ} :
    Set.InjOn (AlonList q) {ys : List ℕ | AdmissibleHead q ys} := by
  intro ys hys zs hzs heq
  have htake :
      (AlonList q ys).take ys.length = (AlonList q zs).take ys.length := by
    rw [heq]
  rw [AlonList, List.take_left, AlonList] at htake
  · have hlen : zs.length = ys.length := by
      rw [(show zs.length = q ^ 2 + q + 1 from hzs.length_eq),
        (show ys.length = q ^ 2 + q + 1 from hys.length_eq)]
    simpa [hlen] using htake

theorem AlonList_mapsTo_blockCompatibleSequence
    (q : ℕ) (π : ProjectivePlane q) :
    Set.MapsTo (AlonList q) {ys : List ℕ | AdmissibleHead q ys}
      {xs : List ℕ | BlockCompatibleSequence (q ^ 2 + q + 1) xs} := by
  intro ys hys
  exact theorem_2_3 q π ys hys

theorem PairwiseBalancedDesign.length_le_choose_two {α : Type} [Fintype α]
    [DecidableEq α] {m : ℕ} (D : PairwiseBalancedDesign α m) :
    m ≤ Nat.choose (Fintype.card α) 2 := by
  classical
  let pickPair : Fin m → Set.powersetCard α 2 := fun i =>
    ⟨Classical.choose (Finset.exists_subset_card_eq
        (s := D.block i) (n := 2) (D.block_card_ge_two i)),
      by
        exact (Classical.choose_spec (Finset.exists_subset_card_eq
          (s := D.block i) (n := 2) (D.block_card_ge_two i))).2⟩
  have hpick_subset : ∀ i, (pickPair i : Finset α) ⊆ D.block i := by
    intro i
    exact (Classical.choose_spec (Finset.exists_subset_card_eq
      (s := D.block i) (n := 2) (D.block_card_ge_two i))).1
  have hpick_inj : Function.Injective pickPair := by
    intro i j hij
    have hcard : (pickPair i : Finset α).card = 2 := (pickPair i).2
    rcases Finset.one_lt_card.1 (by omega : 1 < (pickPair i : Finset α).card) with
      ⟨a, ha, b, hb, hab⟩
    have hi_mem : a ∈ D.block i ∧ b ∈ D.block i :=
      ⟨hpick_subset i ha, hpick_subset i hb⟩
    have hj_mem : a ∈ D.block j ∧ b ∈ D.block j := by
      rw [hij] at ha hb
      exact ⟨hpick_subset j ha, hpick_subset j hb⟩
    rcases D.pair_unique hab with ⟨_, _, huniq⟩
    exact Fin.ext <| congrArg Fin.val ((huniq i hi_mem).trans (huniq j hj_mem).symm)
  calc
    m = Fintype.card (Fin m) := by simp
    _ ≤ Fintype.card (Set.powersetCard α 2) :=
        Fintype.card_le_of_injective pickPair hpick_inj
    _ = Nat.choose (Fintype.card α) 2 := by
        rw [Fintype.card_eq_nat_card, Set.powersetCard.card, Nat.card_eq_fintype_card]

theorem BlockCompatibleSequence.length_le_choose_two {n : ℕ} {xs : List ℕ}
    (hxs : BlockCompatibleSequence n xs) :
    xs.length ≤ Nat.choose n 2 := by
  rcases hxs.2 with ⟨α, instF, instD, hcard, D, _hblocks⟩
  letI : Fintype α := instF
  letI : DecidableEq α := instD
  calc
    xs.length ≤ Nat.choose (Fintype.card α) 2 :=
      PairwiseBalancedDesign.length_le_choose_two D
    _ = Nat.choose n 2 := by rw [hcard]

theorem blockCompatibleSequence_set_finite (n : ℕ) :
    {xs : List ℕ | BlockCompatibleSequence n xs}.Finite := by
  let A : Type := Set.Icc 2 n
  have hfinite :
      ({ys : List A | ys.length ≤ Nat.choose n 2} : Set (List A)).Finite :=
    List.finite_length_le A (Nat.choose n 2)
  refine (hfinite.image fun ys => ys.map fun y : A => (y : ℕ)).subset ?_
  intro xs hxs
  refine ⟨xs.attach.map (fun x : {x // x ∈ xs} =>
    (⟨x.1, ?_⟩ : A)), ?_, ?_⟩
  · rcases List.mem_iff_get.mp x.2 with ⟨i, hi⟩
    rw [← hi]
    exact hxs.1.2 i
  · simp [A, BlockCompatibleSequence.length_le_choose_two hxs]
  · simp

theorem alon_exact_lower_bound_of_plane
    (q : ℕ) (hq : 2 ≤ q) (hπ : Nonempty (ProjectivePlane q)) :
    Nat.choose ((q ^ 2 + q + 1) + q - 2) (q - 2)
      ≤ Set.ncard {xs : List ℕ |
          BlockCompatibleSequence (q ^ 2 + q + 1) xs} := by
  rcases hπ with ⟨π⟩
  rw [← admissibleHead_ncard q hq]
  exact Set.ncard_le_ncard_of_injOn (ht := blockCompatibleSequence_set_finite (q ^ 2 + q + 1))
    (AlonList q)
    (AlonList_mapsTo_blockCompatibleSequence q π)
    AlonList_injective_on_admissible

theorem alon_exact_lower_bound_primePower
    (q : ℕ) (hq : PrimePower q) :
    Nat.choose ((q ^ 2 + q + 1) + q - 2) (q - 2)
      ≤ Set.ncard {xs : List ℕ |
          BlockCompatibleSequence (q ^ 2 + q + 1) xs} := by
  exact alon_exact_lower_bound_of_plane q hq.two_le (projectivePlane_of_primePower hq)

theorem erdos732_yes :
    ∃ c : ℝ, 0 < c ∧
      ∀ᶠ n : ℕ in Filter.atTop,
        Real.exp (c * Real.sqrt (n : ℝ) * Real.log (n : ℝ))
          ≤ (Set.ncard {xs : List ℕ | BlockCompatibleSequence n xs} : ℝ) := by
  rcases eventually_exists_primePower_lower_bound with ⟨c, hcpos, hevent⟩
  refine ⟨c, hcpos, ?_⟩
  filter_upwards [hevent] with n hn
  rcases hn with ⟨q, hq, hgeom, hexp⟩
  have hq2 := hq.two_le
  have hN2 : 2 ≤ n := by
    omega
  have hmono :
      Set.ncard {xs : List ℕ | BlockCompatibleSequence (q ^ 2 + q + 1) xs}
        ≤ Set.ncard {xs : List ℕ | BlockCompatibleSequence n xs} :=
    blockCompatibleSequence_ncard_mono hgeom hN2
  have hplane :
      Nat.choose ((q ^ 2 + q + 1) + q - 2) (q - 2)
        ≤ Set.ncard {xs : List ℕ |
          BlockCompatibleSequence (q ^ 2 + q + 1) xs} :=
    alon_exact_lower_bound_primePower q hq
  exact hexp.trans (by
    exact_mod_cast hplane.trans hmono)

end P732
end ErdosProblems
