import Erdos751.Critical

namespace Erdos751

open Classical

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

namespace Main

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem lift_cycle_from_induce_preserve_length
    {S : Finset V}
    (C : BV.Cycle (G := G.induce (fun v : V => v ∈ S))) :
    ∃ C' : BV.Cycle (G := G),
      BV.Cycle.length (G := G) C' =
        BV.Cycle.length (G := G.induce (fun v : V => v ∈ S)) C := by
  classical
  let f : (G.induce (fun v : V => v ∈ S)) →g G :=
    { toFun := fun v => v.1
      map_rel' := by
        intro v w h
        simpa using h }
  have hinj : Function.Injective f := by
    intro v w h
    apply Subtype.ext
    exact h
  let C' : BV.Cycle (G := G) :=
    { base := C.base.1
      walk := C.walk.map f
      isCycle := by
        simpa using (C.isCycle.map hinj)
      len_ge_three := by
        simpa using C.len_ge_three }
  refine ⟨C', ?_⟩
  simp [BV.Cycle.length, C', SimpleGraph.Walk.length_map]

theorem erdos_751_strong
    (hχ : (4 : ℕ∞) ≤ G.chromaticNumber) :
    ∃ C1 C2 : BV.Cycle (G := G),
      (Nat.dist (BV.Cycle.length (G := G) C1) (BV.Cycle.length (G := G) C2) = 1) ∨
      (Nat.dist (BV.Cycle.length (G := G) C1) (BV.Cycle.length (G := G) C2) = 2) := by
  classical
  let W := Critical.exists_witness_of_chromaticNumber_ge_4 (G := G) hχ

  -- IMPORTANT: match the exact subtype `Fintype` instance used inside `W.hδ3` and `W.hcard4`.
  -- Do NOT use `Subtype.fintype ...` here.
  letI : Fintype {v : V // v ∈ W.S} := Critical.instSub (V := V) W.S

  have hBV :
      ∃ D1 D2 : BV.Cycle (G := Critical.H (G := G) W),
        (Nat.dist (BV.Cycle.length (G := Critical.H (G := G) W) D1)
                  (BV.Cycle.length (G := Critical.H (G := G) W) D2) = 1) ∨
        (Nat.dist (BV.Cycle.length (G := Critical.H (G := G) W) D1)
                  (BV.Cycle.length (G := Critical.H (G := G) W) D2) = 2) :=
    BV.exists_two_cycles_length_dist_1_or_2
      (G := Critical.H (G := G) W)
      (by simpa [Critical.H] using W.h2)
      (by convert W.hδ3 using 1)
      (by simpa using W.hcard4)

  rcases hBV with ⟨D1, D2, hdist⟩
  rcases lift_cycle_from_induce_preserve_length (G := G) (S := W.S) D1 with ⟨C1, hlen1⟩
  rcases lift_cycle_from_induce_preserve_length (G := G) (S := W.S) D2 with ⟨C2, hlen2⟩
  refine ⟨C1, C2, ?_⟩
  simpa [hlen1, hlen2] using hdist

end Main
end Erdos751
