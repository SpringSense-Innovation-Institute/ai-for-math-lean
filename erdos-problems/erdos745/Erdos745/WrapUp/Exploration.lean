module

public import Erdos745.WrapUp.Core

@[expose] public section

namespace Erdos745.WrapUp
noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable
local instance : MeasurableSpace BrownianPath := borel BrownianPath

structure BFSState (n : ℕ) where
  seen : Finset (Fin n)
  queue : List (Fin n)
  walk : ℤ

def initialState (n : ℕ) : BFSState n := ⟨∅, [], 0⟩

def selectRoot {n : ℕ} (s : BFSState n) :
    Option (Fin n × List (Fin n) × Finset (Fin n)) :=
  match s.queue with
  | v :: rest => some (v, rest, s.seen)
  | [] =>
    let neutral := (Finset.univ : Finset (Fin n)) \ s.seen
    if h : neutral.Nonempty then
      let v := neutral.min' h
      some (v, [], insert v s.seen)
    else none

def bfsStep {n : ℕ} (G : Graph n) (s : BFSState n) : BFSState n :=
  match selectRoot s with
  | none => s
  | some (v, rest, discovered) =>
    let children := (Finset.univ : Finset (Fin n)).filter
      (fun u => u ∉ discovered ∧ adj G v u)
    ⟨discovered ∪ children, rest ++ children.toList,
      s.walk + (children.card : ℤ) - 1⟩

def explore {n : ℕ} (G : Graph n) : ℕ → BFSState n
  | 0 => initialState n
  | j + 1 => bfsStep G (explore G j)

def processed {n : ℕ} (G : Graph n) (j : ℕ) : Finset (Fin n) :=
  (explore G j).seen \ (explore G j).queue.toFinset

def rawExploration {n : ℕ} (G : Graph n) (t : NNReal) : ℝ :=
  let x := (t : ℝ) * n23 n
  let j : ℕ := ⌊x⌋₊
  let theta := x - (j : ℝ)
  ((1 - theta) * ((explore G j).walk : ℝ) +
    theta * ((explore G (j + 1)).walk : ℝ)) / n13 n

abbrev ExplorationPaths := (n : ℕ) → Graph n → BrownianPath

def IsInterpolation (Phi : ExplorationPaths) : Prop :=
  ∀ n (G : Graph n) t, Phi n G t = rawExploration G t

def driftPath (w : BrownianPath) (lam : ℝ) : BrownianPath :=
  ⟨drift w lam, by unfold drift; fun_prop⟩

def WeakExploration (M : NatSeq) (Phi : ExplorationPaths) (lam : ℝ)
    (mu : PathLaw) : Prop :=
  ∀ F : BrownianPath → ℝ, Continuous F →
    (∃ C : ℝ, ∀ w, |F w| ≤ C) →
    Tendsto (fun n => expectM n (M n) (fun G => F (Phi n G))) atTop
      (𝓝 (∫ w, F (driftPath w lam) ∂mu))

def lateLarge {n : ℕ} (G : Graph n) (T eta : ℝ) : Prop :=
  ∃ S ∈ components G, Disjoint S (explore G ⌊T * n23 n⌋₊).seen ∧
    eta * n23 n ≤ (S.card : ℝ)

def unfinishedEarly {n : ℕ} (G : Graph n) (T U : ℝ) : Prop :=
  ∃ S ∈ components G,
    ¬ Disjoint S (explore G ⌊T * n23 n⌋₊).seen ∧
    ¬ S ⊆ processed G ⌊U * n23 n⌋₊

def ExplorationTails (M : NatSeq) (lam : ℝ) : Prop :=
  (∀ eta T d : ℝ, 0 < eta → 0 < T → lam + 1 < T → 0 < d →
    ∀ᶠ n in atTop, probM n (M n) (fun G => lateLarge G T eta) ≤
      4 / (eta ^ 2 * (T - lam)) + d) ∧
  (∀ T d : ℝ, 0 < T → 0 < d → ∃ U : ℝ, T < U ∧
    ∀ᶠ n in atTop, probM n (M n) (fun G => unfinishedEarly G T U) ≤ d)

def GoodExcursionPath (w : BrownianPath) (lam : ℝ) : Prop :=
  Tendsto (drift w lam) atTop atBot ∧
  (∀ T : ℝ, 0 < T →
    volume {t : ℝ | 0 ≤ t ∧ t ≤ T ∧ reflected w lam t.toNNReal = 0} = 0) ∧
  (∀ a b c d : NNReal, excursion w lam a b → excursion w lam c d →
    a < c → drift w lam c < drift w lam a) ∧
  (∀ a b : NNReal, excursion w lam a b → ∀ delta : NNReal, 0 < delta →
    ∃ t : NNReal, b < t ∧ t < b + delta ∧ drift w lam t < drift w lam a) ∧
  (∀ eta : ℝ, 0 < eta →
    Set.Finite {e : NNReal × NNReal | excursion w lam e.1 e.2 ∧
      eta ≤ (e.2 : ℝ) - (e.1 : ℝ)}) ∧
  Set.Infinite {e : NNReal × NNReal | excursion w lam e.1 e.2}

end
end Erdos745.WrapUp
