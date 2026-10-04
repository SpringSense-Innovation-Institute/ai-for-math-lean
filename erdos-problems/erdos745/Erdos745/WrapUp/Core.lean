module

public import Mathlib

@[expose] public section

/-!
Finite labelled random graphs, component ranks, and the five-regime sparse
evolution statement. Probability expressions use finite graph laws or explicitly
characterized probability measures on continuous paths.
-/
namespace Erdos745.WrapUp

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable

abbrev NatSeq := ℕ → ℕ
abbrev RealSeq := ℕ → ℝ
abbrev Edge (n : ℕ) := {e : Fin n × Fin n // e.1 < e.2}
abbrev Graph (n : ℕ) := Finset (Edge n)

def capacity (n : ℕ) : ℕ := n.choose 2

def allGraphs (n : ℕ) : Finset (Graph n) :=
  (Finset.univ : Finset (Edge n)).powerset

def fixedGraphs (n M : ℕ) : Finset (Graph n) :=
  (allGraphs n).filter (fun G => G.card = M)

def adj {n : ℕ} (G : Graph n) (u v : Fin n) : Prop :=
  ∃ e ∈ G, (e.val.1 = u ∧ e.val.2 = v) ∨ (e.val.1 = v ∧ e.val.2 = u)

def reach {n : ℕ} (G : Graph n) (u v : Fin n) : Prop :=
  Relation.ReflTransGen (adj G) u v

def componentOf {n : ℕ} (G : Graph n) (v : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun u => reach G v u)

def components {n : ℕ} (G : Graph n) : Finset (Finset (Fin n)) :=
  Finset.univ.image (componentOf G)

def edgesInside {n : ℕ} (G : Graph n) (S : Finset (Fin n)) : ℕ :=
  (G.filter (fun e => e.val.1 ∈ S ∧ e.val.2 ∈ S)).card

def isTree {n : ℕ} (G : Graph n) (S : Finset (Fin n)) : Prop :=
  S ∈ components G ∧ edgesInside G S + 1 = S.card

def isUnicyclic {n : ℕ} (G : Graph n) (S : Finset (Fin n)) : Prop :=
  S ∈ components G ∧ edgesInside G S = S.card

def countGE {n : ℕ} (G : Graph n) (h : ℕ) : ℕ :=
  ((components G).filter (fun S => h ≤ S.card)).card

/-- One-based ranks, zero-padded. A finite supremum avoids an opaque sorting API. -/
def rankSize {n : ℕ} (G : Graph n) (i : ℕ) : ℕ :=
  if i = 0 then 0 else
    (Finset.range (n + 1)).sup (fun h => if i ≤ countGE G h then h else 0)

def treeCountGE {n : ℕ} (G : Graph n) (h : ℕ) : ℕ :=
  ((components G).filter (fun S => isTree G S ∧ h ≤ S.card)).card

def componentCount {n : ℕ} (G : Graph n) (k e : ℕ) : ℕ :=
  ((components G).filter (fun S => S.card = k ∧ edgesInside G S = e)).card

def treeMassBelow {n : ℕ} (G : Graph n) (h : ℕ) : ℝ :=
  (components G).sum (fun S => if isTree G S ∧ S.card < h then (S.card : ℝ) else 0)

def unicyclicMass {n : ℕ} (G : Graph n) : ℝ :=
  (components G).sum (fun S => if isUnicyclic G S then (S.card : ℝ) else 0)

def largeMass {n : ℕ} (G : Graph n) (h : ℕ) : ℝ :=
  (components G).sum (fun S => if h ≤ S.card then (S.card : ℝ) else 0)

def smallComplexCount {n : ℕ} (G : Graph n) (h : ℕ) : ℕ :=
  ((components G).filter (fun S => S.card < h ∧ S.card < edgesInside G S)).card

def probM (n M : ℕ) (A : Graph n → Prop) : ℝ :=
  (((fixedGraphs n M).filter A).card : ℝ) / ((fixedGraphs n M).card : ℝ)

def expectM (n M : ℕ) (f : Graph n → ℝ) : ℝ :=
  (fixedGraphs n M).sum f / ((fixedGraphs n M).card : ℝ)

def varianceM (n M : ℕ) (f : Graph n → ℝ) : ℝ :=
  expectM n M (fun G => (f G - expectM n M f) ^ 2)


def falling (n q : ℕ) : ℕ := (Finset.range q).prod (fun j => n - j)

def cayley (k : ℕ) : ℕ := if k = 0 then 0 else if k = 1 then 1 else k ^ (k - 2)

def connectedCount (k e : ℕ) : ℕ :=
  ((fixedGraphs k e).filter (fun G => 0 < k ∧ ∀ u v : Fin k, reach G u v)).card

def treeTupleCount {n : ℕ} (G : Graph n) (q : ℕ) (ks : Fin q → ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin q → Finset (Fin n))).filter
    (fun C => Function.Injective C ∧ ∀ i, isTree G (C i) ∧ (C i).card = ks i)).card

def tupleMoment (n M q : ℕ) (ks : Fin q → ℕ) : ℝ :=
  expectM n M (fun G => (treeTupleCount G q ks : ℝ))

/-- M+q-K is guarded before natural subtraction. M-K+q would be wrong. -/
def tupleFormula (n M q : ℕ) (ks : Fin q → ℕ) : ℝ :=
  let K := ∑ i, ks i
  if (∀ i, 0 < ks i) ∧ K ≤ n ∧ K ≤ M + q then
    (falling n K : ℝ) * (∏ i, (cayley (ks i) : ℝ) / ((ks i).factorial : ℝ)) *
      (((n - K).choose 2).choose (M + q - K) : ℝ) / ((capacity n).choose M : ℝ)
  else 0

def componentFormula (n M k e : ℕ) : ℝ :=
  if k ≤ n ∧ e ≤ M then
    (n.choose k : ℝ) * (connectedCount k e : ℝ) *
      (((n - k).choose 2).choose (M - e) : ℝ) / ((capacity n).choose M : ℝ)
  else 0

def admissible (M : NatSeq) : Prop := ∀ᶠ n in atTop, M n ≤ capacity n

def degree (M : NatSeq) (n : ℕ) : ℝ := 2 * (M n : ℝ) / (n : ℝ)
def degreeAt (n M : ℕ) : ℝ := 2 * (M : ℝ) / (n : ℝ)
def rate (x : ℝ) : ℝ := x - 1 - Real.log x

def conjugate (lam : ℝ) : ℝ :=
  sSup {x : ℝ | 0 ≤ x ∧ x ≤ 1 ∧ x * Real.exp (-x) ≤ lam * Real.exp (-lam)}

def giantFraction (lam : ℝ) : ℝ := 1 - conjugate lam / lam

def epsilon (M : NatSeq) (n : ℕ) : ℝ := |degree M n - 1|
def widthParameter (M : NatSeq) (n : ℕ) : ℝ := (n : ℝ) * epsilon M n ^ 3

def n23 (n : ℕ) : ℝ := Real.rpow (n : ℝ) (2 / 3 : ℝ)
def n13 (n : ℕ) : ℝ := Real.rpow (n : ℝ) (1 / 3 : ℝ)
def largeCutoff (n : ℕ) : ℕ := ⌈n23 n⌉₊

def center (M : NatSeq) (n : ℕ) : ℝ :=
  (Real.log (n : ℝ) - (5 / 2 : ℝ) * Real.log (Real.log (n : ℝ))) / rate (degree M n)

def nearNumerator (M : NatSeq) (n : ℕ) (r : ℝ) : ℝ :=
  let z := widthParameter M n / 8
  Real.log z - (5 / 2 : ℝ) * Real.log (Real.log z) + r

def nearThreshold (M : NatSeq) (n : ℕ) (r : ℝ) : ℝ :=
  nearNumerator M n r / rate (degree M n)


def latticeRate (lam ell : ℝ) : ℝ :=
  Real.rpow (rate lam) (5 / 2 : ℝ) * Real.exp (-rate lam * ell) /
    (lam * Real.sqrt (2 * Real.pi) * (1 - Real.exp (-rate lam)))

def nearRate (r : ℝ) : ℝ := 2 * Real.exp (-r) / Real.sqrt Real.pi

def poissonCDF (nu : ℝ) (q : ℕ) : ℝ :=
  Real.exp (-nu) * (Finset.range (q + 1)).sum
    (fun j => nu ^ j / (j.factorial : ℝ))

def fixedCDF (n M i : ℕ) (h : ℝ) : ℝ :=
  probM n M (fun G => (rankSize G i : ℝ) < h)

def countCDF (n M h q : ℕ) : ℝ :=
  probM n M (fun G => treeCountGE G h ≤ q)

def bareSub (M : NatSeq) : Prop :=
  admissible M ∧ (∀ᶠ n in atTop, 0 < degree M n ∧ degree M n < 1) ∧
    Tendsto (degree M) atTop (𝓝 1) ∧ Tendsto (widthParameter M) atTop atTop

def bareSuper (M : NatSeq) : Prop :=
  admissible M ∧ (∀ᶠ n in atTop, 1 < degree M n) ∧
    Tendsto (degree M) atTop (𝓝 1) ∧ Tendsto (widthParameter M) atTop atTop

def criticalWindow (M : NatSeq) (lam : ℝ) : Prop :=
  admissible M ∧
    Tendsto (fun n => (2 * (M n : ℝ) - (n : ℝ)) / n23 n) atTop (𝓝 lam)

def boundedBy (f g : RealSeq) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ᶠ n in atTop, |f n| ≤ C * g n

def tightScaled (M : NatSeq) (X : (n : ℕ) → Graph n → ℝ)
    (c s : RealSeq) : Prop :=
  ∀ d : ℝ, 0 < d → ∃ K : ℝ, 0 < K ∧
    ∀ᶠ n in atTop, probM n (M n) (fun G => |X n G - c n| > K * s n) ≤ d

def giantCenter (M : NatSeq) (n : ℕ) : ℝ := (n : ℝ) * giantFraction (degree M n)
def displacement (M : NatSeq) (n : ℕ) : ℝ := (n : ℝ) * epsilon M n / 2

def conjugateDisplacement (M : NatSeq) (n : ℕ) : ℝ :=
  (n : ℝ) * (1 - conjugate (degree M n)) / 2

def separatedStructure {n : ℕ} (G : Graph n) : Prop :=
  countGE G (largeCutoff n) = 1 ∧
  (∀ S ∈ components G, S.card < largeCutoff n → edgesInside G S ≤ S.card) ∧
  (∀ S ∈ components G, largeCutoff n ≤ S.card → S.card < edgesInside G S)

def fixedSubcriticalLaw : Prop :=
  ∀ (M : NatSeq) (lam : ℝ), admissible M → 0 < lam → lam < 1 →
    Tendsto (degree M) atTop (𝓝 lam) →
    tightScaled M (fun _ G => (rankSize G 2 : ℝ)) (center M) (fun _ => 1) ∧
    ∀ (ns h : NatSeq) (ell : ℝ), StrictMono ns →
      Tendsto (fun j => (h j : ℝ) - center M (ns j)) atTop (𝓝 ell) →
      Tendsto (fun j => fixedCDF (ns j) (M (ns j)) 2 (h j)) atTop
        (𝓝 (poissonCDF (latticeRate lam ell) 1))

def fixedSupercriticalLaw : Prop :=
  ∀ (M : NatSeq) (lam : ℝ), admissible M → 1 < lam →
    Tendsto (degree M) atTop (𝓝 lam) →
    tightScaled M (fun _ G => (rankSize G 2 : ℝ)) (center M) (fun _ => 1) ∧
    tightScaled M (fun _ G => (rankSize G 1 : ℝ)) (giantCenter M)
      (fun n => Real.sqrt (n : ℝ)) ∧
    Tendsto (fun n => probM n (M n) separatedStructure) atTop (𝓝 1) ∧
    ∀ (ns h : NatSeq) (ell : ℝ), StrictMono ns →
      Tendsto (fun j => (h j : ℝ) - center M (ns j)) atTop (𝓝 ell) →
      Tendsto (fun j => fixedCDF (ns j) (M (ns j)) 2 (h j)) atTop
        (𝓝 (poissonCDF (latticeRate lam ell) 0))

def barelySubcriticalLaw : Prop :=
  ∀ M : NatSeq, bareSub M →
    (∀ r : ℝ, Tendsto (fun n => fixedCDF n (M n) 2 (nearThreshold M n r))
      atTop (𝓝 (poissonCDF (nearRate r) 1))) ∧
    Tendsto (fun n => probM n (M n) (fun G =>
      ∀ S ∈ components G, edgesInside G S ≤ S.card)) atTop (𝓝 1)

def barelySupercriticalLaw : Prop :=
  (∃ C : ℝ, 0 < C ∧ ∀ M : NatSeq, bareSuper M →
    ∀ᶠ n in atTop, |giantCenter M n - 4 * displacement M n| ≤
      C * (displacement M n ^ 2 / n)) ∧
  ∀ M : NatSeq, bareSuper M →
    (∀ r : ℝ, Tendsto (fun n => fixedCDF n (M n) 2 (nearThreshold M n r))
      atTop (𝓝 (poissonCDF (nearRate r) 0))) ∧
    Tendsto (fun n => probM n (M n) separatedStructure) atTop (𝓝 1) ∧
    (∀ᶠ n in atTop,
      0 < conjugateDisplacement M n ∧ conjugateDisplacement M n < (n : ℝ) / 2 ∧
      (1 - 2 * conjugateDisplacement M n / n) *
        Real.exp (2 * conjugateDisplacement M n / n) =
      (1 + 2 * displacement M n / n) * Real.exp (-2 * displacement M n / n)) ∧
    ∀ omega : RealSeq, (∀ᶠ n in atTop, 0 < omega n) → Tendsto omega atTop atTop →
      Tendsto (fun n => probM n (M n) (fun G =>
        |(rankSize G 1 : ℝ) - giantCenter M n| <
          omega n * (n : ℝ) / Real.sqrt (displacement M n))) atTop (𝓝 1)

/-- The topology is compact-uniform; paths are continuous by construction. -/
abbrev BrownianPath := ContinuousMap NNReal ℝ
local instance : MeasurableSpace BrownianPath := borel BrownianPath

abbrev PathLaw := Measure BrownianPath

def normalCDF (v x : ℝ) : ℝ :=
  if v ≤ 0 then (if 0 ≤ x then 1 else 0) else
    ∫ y in Set.Iic x, Real.exp (-(y ^ 2) / (2 * v)) / Real.sqrt (2 * Real.pi * v)

def BrownianLaw (mu : PathLaw) : Prop :=
  IsProbabilityMeasure mu ∧ mu {w | w 0 = 0} = 1 ∧
    ∀ (m : ℕ) (t : ℕ → NNReal) (u : ℕ → ℝ),
      (∀ j < m, t j < t (j + 1)) →
      mu {w | ∀ j < m, w (t (j + 1)) - w (t j) ≤ u j} =
        ENNReal.ofReal ((Finset.range m).prod (fun j =>
          normalCDF ((t (j + 1) : ℝ) - (t j : ℝ)) (u j)))

def drift (w : BrownianPath) (lam : ℝ) (t : NNReal) : ℝ :=
  w t + lam * (t : ℝ) - (t : ℝ) ^ 2 / 2

def reflected (w : BrownianPath) (lam : ℝ) (t : NNReal) : ℝ :=
  drift w lam t - sInf ((drift w lam) '' Set.Icc 0 t)

def excursion (w : BrownianPath) (lam : ℝ) (a b : NNReal) : Prop :=
  a < b ∧ reflected w lam a = 0 ∧ reflected w lam b = 0 ∧
    ∀ t ∈ Set.Ioo a b, 0 < reflected w lam t

def excursionRankExtended (w : BrownianPath) (lam : ℝ) (i : ℕ) : ENNReal :=
  if i = 0 then 0 else sSup {r : ENNReal |
    ∃ e : Fin i → NNReal × NNReal, Function.Injective e ∧
      ∀ j, excursion w lam (e j).1 (e j).2 ∧
        r ≤ ENNReal.ofReal (((e j).2 : ℝ) - ((e j).1 : ℝ))}

def excursionRank (w : BrownianPath) (lam : ℝ) (i : ℕ) : ℝ :=
  (excursionRankExtended w lam i).toReal

def criticalCDF (mu : PathLaw) (lam x : ℝ) : ℝ :=
  (mu {w | excursionRank w lam 2 < x}).toReal

def rankCDF (mu : PathLaw) (lam : ℝ) (i : ℕ) (x : ℝ) : ℝ :=
  (mu {w | excursionRank w lam i < x}).toReal

def jointCDF (mu : PathLaw) (lam : ℝ) (k : ℕ) (x : Fin k → ℝ) : ℝ :=
  (mu {w | ∀ i : Fin k, excursionRank w lam (i.val + 1) < x i}).toReal

/-- Joint weak convergence, expressed through continuity rectangles, plus the
explicit rank-two projection and positive finite limiting ranks. -/
def criticalLaw : Prop :=
  (∃ mu : PathLaw, BrownianLaw mu) ∧
  ∀ (mu : PathLaw), BrownianLaw mu → ∀ lam : ℝ,
    (∀ i : ℕ, 0 < i → ∀ᵐ w ∂mu,
      0 < excursionRankExtended w lam i ∧ excursionRankExtended w lam i < ⊤) ∧
    ∀ M : NatSeq, criticalWindow M lam →
      (∀ x : ℝ, ContinuousAt (criticalCDF mu lam) x →
        Tendsto (fun n => probM n (M n) (fun G =>
          (rankSize G 2 : ℝ) / n23 n < x)) atTop (𝓝 (criticalCDF mu lam x))) ∧
      (∀ (k : ℕ) (x : Fin k → ℝ),
        (∀ i : Fin k, ContinuousAt (rankCDF mu lam (i.val + 1)) (x i)) →
        Tendsto (fun n => probM n (M n) (fun G =>
          ∀ i : Fin k, (rankSize G (i.val + 1) : ℝ) / n23 n < x i))
          atTop (𝓝 (jointCDF mu lam k x)))

def AtlasStatement : Prop :=
  fixedSubcriticalLaw ∧ fixedSupercriticalLaw ∧ barelySubcriticalLaw ∧
    barelySupercriticalLaw ∧ criticalLaw


end
end Erdos745.WrapUp
