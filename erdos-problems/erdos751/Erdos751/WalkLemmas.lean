import Erdos751.Basic

namespace Erdos751

open Classical

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

namespace BV

/-!
Stable engineering layer (v4.23.0-safe):
Downstream files should rely only on these wrappers for IsPath / reachability.
-/

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem exists_walk_of_reachable {x y : V} (h : G.Reachable x y) :
    ∃ _ : G.Walk x y, True := by
  classical
  rcases h with ⟨p⟩
  exact ⟨p, trivial⟩

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem exists_walk_of_connected (hconn : G.Connected) (x y : V) :
    ∃ _ : G.Walk x y, True := by
  classical
  have hr : G.Reachable x y := hconn x y
  exact exists_walk_of_reachable (G := G) hr

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Reduce a walk to a simple path (IsPath) with the same endpoints. -/
theorem reduce_to_isPath {x y : V} (p : G.Walk x y) :
    ∃ q : G.Walk x y, q.IsPath := by
  classical
  have hr : G.Reachable x y := p.reachable
  exact hr.exists_isPath

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem exists_isPath_of_reachable {x y : V} (h : G.Reachable x y) :
    ∃ p : G.Walk x y, p.IsPath := by
  classical
  rcases exists_walk_of_reachable (G := G) h with ⟨p, _⟩
  exact reduce_to_isPath (G := G) p

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem exists_isPath_of_connected (hconn : G.Connected) (x y : V) :
    ∃ p : G.Walk x y, p.IsPath := by
  classical
  rcases exists_walk_of_connected (G := G) hconn x y with ⟨p, _⟩
  exact reduce_to_isPath (G := G) p

end BV
end Erdos751
