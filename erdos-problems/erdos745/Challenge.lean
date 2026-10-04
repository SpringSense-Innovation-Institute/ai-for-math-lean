module

public import Mathlib

@[expose] public section

/-!
Public statement of the corrected five-regime sparse random-graph atlas.
Only Mathlib is imported. All definitions below retain exactly the mathematical
representation of the certified MathMiner statement layer. Logs and division are
Lean real operations; regime hypotheses ensure their eventual relevant domains.
The near-critical normalization corrects the quadratic-rate discrepancy described
in Erdos745/Mathematics/QuadraticNormalization.md and stage8/CLAIM_LEDGER.md.
-/
namespace Erdos745.WrapUp
noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable
/-- Edge-count sequences indexed by the number of labelled vertices. -/
abbrev NatSeq := ℕ → ℕ
/-- Real-valued sequences indexed by the number of labelled vertices. -/
abbrev RealSeq := ℕ → ℝ
/-- Unordered simple edges, represented by ordered distinct endpoints in Fin n. -/
abbrev Edge (n : ℕ) := {e : Fin n × Fin n // e.1 < e.2}
/-- Simple labelled graphs on n vertices, represented by finite edge sets. -/
abbrev Graph (n : ℕ) := Finset (Edge n)
/-- Maximum possible edge count, n choose 2. -/
def capacity (n : ℕ) : ℕ := n.choose 2
/-- All simple labelled graphs on n vertices, including the empty graph. -/
def allGraphs (n : ℕ) : Finset (Graph n) :=
  (Finset.univ : Finset (Edge n)).powerset
/-- All labelled graphs with exactly M edges; empty for inadmissible M. -/
def fixedGraphs (n M : ℕ) : Finset (Graph n) :=
  (allGraphs n).filter (fun G => G.card = M)
/-- Symmetric adjacency of two vertices. -/
def adj {n : ℕ} (G : Graph n) (u v : Fin n) : Prop :=
  ∃ e ∈ G, (e.val.1 = u ∧ e.val.2 = v) ∨ (e.val.1 = v ∧ e.val.2 = u)
/-- Connectivity, including the length-zero path. -/
def reach {n : ℕ} (G : Graph n) (u v : Fin n) : Prop :=
  Relation.ReflTransGen (adj G) u v
/-- The vertex set of the component containing v. -/
def componentOf {n : ℕ} (G : Graph n) (v : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun u => reach G v u)
/-- Distinct component vertex sets, with isolated vertices included. -/
def components {n : ℕ} (G : Graph n) : Finset (Finset (Fin n)) :=
  Finset.univ.image (componentOf G)
/-- Number of edges with both endpoints in the given vertex set. -/
def edgesInside {n : ℕ} (G : Graph n) (S : Finset (Fin n)) : ℕ :=
  (G.filter (fun e => e.val.1 ∈ S ∧ e.val.2 ∈ S)).card
/-- Number of components of size at least h. -/
def countGE {n : ℕ} (G : Graph n) (h : ℕ) : ℕ :=
  ((components G).filter (fun S => h ≤ S.card)).card
/-- One-based decreasing component-size ranks, zero padded; rank zero is zero. -/
def rankSize {n : ℕ} (G : Graph n) (i : ℕ) : ℕ :=
  if i = 0 then 0 else
    (Finset.range (n + 1)).sup (fun h => if i ≤ countGE G h then h else 0)
/-- Uniform probability in G(n,M). Empty denominators use real division by zero (zero). -/
def probM (n M : ℕ) (A : Graph n → Prop) : ℝ :=
  (((fixedGraphs n M).filter A).card : ℝ) / ((fixedGraphs n M).card : ℝ)
/-- Edge counts are feasible for all sufficiently large n. -/
def admissible (M : NatSeq) : Prop := ∀ᶠ n in atTop, M n ≤ capacity n
/-- Mean degree 2M(n)/n, with natural numbers coerced to real numbers. -/
def degree (M : NatSeq) (n : ℕ) : ℝ := 2 * (M n : ℝ) / (n : ℝ)
/-- Exact exponential rate x - 1 - log x; no quadratic approximation. -/
def rate (x : ℝ) : ℝ := x - 1 - Real.log x
/-- The subcritical conjugate of lambda > 1, selected in [0,1] by a supremum. -/
def conjugate (lam : ℝ) : ℝ :=
  sSup {x : ℝ | 0 ≤ x ∧ x ≤ 1 ∧ x * Real.exp (-x) ≤ lam * Real.exp (-lam)}
/-- Fraction 1 - conjugate(lambda)/lambda for the supercritical giant. -/
def giantFraction (lam : ℝ) : ℝ := 1 - conjugate lam / lam
/-- Distance of the mean degree from one. -/
def epsilon (M : NatSeq) (n : ℕ) : ℝ := |degree M n - 1|
/-- Barely-critical width n epsilon cubed. -/
def widthParameter (M : NatSeq) (n : ℕ) : ℝ := (n : ℝ) * epsilon M n ^ 3
/-- Critical component-size scale n to the power 2/3. -/
def n23 (n : ℕ) : ℝ := Real.rpow (n : ℝ) (2 / 3 : ℝ)
/-- Ceiling of the critical component-size scale. -/
def largeCutoff (n : ℕ) : ℕ := ⌈n23 n⌉₊
/-- Fixed-regime lattice center using the actual mean degree at each n. -/
def center (M : NatSeq) (n : ℕ) : ℝ :=
  (Real.log (n : ℝ) - (5 / 2 : ℝ) * Real.log (Real.log (n : ℝ))) / rate (degree M n)
/-- Barely-critical centering log(w/8) - (5/2) log log(w/8) + r. -/
def nearNumerator (M : NatSeq) (n : ℕ) (r : ℝ) : ℝ :=
  let z := widthParameter M n / 8
  Real.log z - (5 / 2 : ℝ) * Real.log (Real.log z) + r
/-- Barely-critical threshold divided by the exact rate of the mean degree. -/
def nearThreshold (M : NatSeq) (n : ℕ) (r : ℝ) : ℝ :=
  nearNumerator M n r / rate (degree M n)
/-- Poisson intensity for lattice offsets at limiting mean degree lambda. -/
def latticeRate (lam ell : ℝ) : ℝ :=
  Real.rpow (rate lam) (5 / 2 : ℝ) * Real.exp (-rate lam * ell) /
    (lam * Real.sqrt (2 * Real.pi) * (1 - Real.exp (-rate lam)))
/-- Barely-critical Poisson intensity 2 exp(-r)/sqrt(pi). -/
def nearRate (r : ℝ) : ℝ := 2 * Real.exp (-r) / Real.sqrt Real.pi
/-- Probability that a Poisson variable of intensity nu is at most q. -/
def poissonCDF (nu : ℝ) (q : ℕ) : ℝ :=
  Real.exp (-nu) * (Finset.range (q + 1)).sum
    (fun j => nu ^ j / (j.factorial : ℝ))
/-- Strict component-rank distribution: probability that rank i is less than h. -/
def fixedCDF (n M i : ℕ) (h : ℝ) : ℝ :=
  probM n M (fun G => (rankSize G i : ℝ) < h)
/-- Eventually positive subcritical mean degrees tending to one, with n epsilon cubed diverging. -/
def bareSub (M : NatSeq) : Prop :=
  admissible M ∧ (∀ᶠ n in atTop, 0 < degree M n ∧ degree M n < 1) ∧
    Tendsto (degree M) atTop (𝓝 1) ∧ Tendsto (widthParameter M) atTop atTop
/-- Eventually supercritical mean degrees tending to one, with n epsilon cubed diverging. -/
def bareSuper (M : NatSeq) : Prop :=
  admissible M ∧ (∀ᶠ n in atTop, 1 < degree M n) ∧
    Tendsto (degree M) atTop (𝓝 1) ∧ Tendsto (widthParameter M) atTop atTop
/-- Feasible sequences whose (2M-n)/n^(2/3) tends to lambda. -/
def criticalWindow (M : NatSeq) (lam : ℝ) : Prop :=
  admissible M ∧
    Tendsto (fun n => (2 * (M n : ℝ) - (n : ℝ)) / n23 n) atTop (𝓝 lam)
/-- Uniform eventual tail control: for every positive tolerance choose a positive bound. -/
def tightScaled (M : NatSeq) (X : (n : ℕ) → Graph n → ℝ)
    (c s : RealSeq) : Prop :=
  ∀ d : ℝ, 0 < d → ∃ K : ℝ, 0 < K ∧
    ∀ᶠ n in atTop, probM n (M n) (fun G => |X n G - c n| > K * s n) ≤ d
/-- Exact supercritical giant center n times the giant fraction. -/
def giantCenter (M : NatSeq) (n : ℕ) : ℝ := (n : ℝ) * giantFraction (degree M n)
/-- Half the absolute edge-count displacement from n/2. -/
def displacement (M : NatSeq) (n : ℕ) : ℝ := (n : ℝ) * epsilon M n / 2
/-- Subcritical conjugate displacement n(1-conjugate(mean degree))/2. -/
def conjugateDisplacement (M : NatSeq) (n : ℕ) : ℝ :=
  (n : ℝ) * (1 - conjugate (degree M n)) / 2
/-- Exactly one component above the ceiling cutoff; others have at most one cycle, the large one more. -/
def separatedStructure {n : ℕ} (G : Graph n) : Prop :=
  countGE G (largeCutoff n) = 1 ∧
  (∀ S ∈ components G, S.card < largeCutoff n → edgesInside G S ≤ S.card) ∧
  (∀ S ∈ components G, largeCutoff n ≤ S.card → S.card < edgesInside G S)
/-- Fixed subcritical rank-two tightness and lattice subsequence distribution limits. -/
def fixedSubcriticalLaw : Prop :=
  ∀ (M : NatSeq) (lam : ℝ), admissible M → 0 < lam → lam < 1 →
    Tendsto (degree M) atTop (𝓝 lam) →
    tightScaled M (fun _ G => (rankSize G 2 : ℝ)) (center M) (fun _ => 1) ∧
    ∀ (ns h : NatSeq) (ell : ℝ), StrictMono ns →
      Tendsto (fun j => (h j : ℝ) - center M (ns j)) atTop (𝓝 ell) →
      Tendsto (fun j => fixedCDF (ns j) (M (ns j)) 2 (h j)) atTop
        (𝓝 (poissonCDF (latticeRate lam ell) 1))
/-- Fixed supercritical rank-two lattice limits, square-root giant tightness, and component separation. -/
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
/-- Barely subcritical rank-two limits and asymptotic absence of components with more than one cycle. -/
def barelySubcriticalLaw : Prop :=
  ∀ M : NatSeq, bareSub M →
    (∀ r : ℝ, Tendsto (fun n => fixedCDF n (M n) 2 (nearThreshold M n r))
      atTop (𝓝 (poissonCDF (nearRate r) 1))) ∧
    Tendsto (fun n => probM n (M n) (fun G =>
      ∀ S ∈ components G, edgesInside G S ≤ S.card)) atTop (𝓝 1)
/-- Barely supercritical rank-two limits, separation, exact conjugacy, one absolute center-error constant for all sequences, and giant concentration. -/
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

/-- Continuous real paths on nonnegative time, with compact-uniform topology and its Borel sigma algebra. -/
abbrev BrownianPath := ContinuousMap NNReal ℝ

local instance : MeasurableSpace BrownianPath := borel BrownianPath
/-- Measures on continuous paths with the Borel measurable structure. -/
abbrev PathLaw := Measure BrownianPath
/-- Centered Gaussian CDF of variance v; nonpositive variance uses the point mass at zero. -/
def normalCDF (v x : ℝ) : ℝ :=
  if v ≤ 0 then (if 0 ≤ x then 1 else 0) else
    ∫ y in Set.Iic x, Real.exp (-(y ^ 2) / (2 * v)) / Real.sqrt (2 * Real.pi * v)
/-- Probability law starting at zero with independent centered Gaussian increments of time-increment variance. -/
def BrownianLaw (mu : PathLaw) : Prop :=
  IsProbabilityMeasure mu ∧ mu {w | w 0 = 0} = 1 ∧
    ∀ (m : ℕ) (t : ℕ → NNReal) (u : ℕ → ℝ),
      (∀ j < m, t j < t (j + 1)) →
      mu {w | ∀ j < m, w (t (j + 1)) - w (t j) ≤ u j} =
        ENNReal.ofReal ((Finset.range m).prod (fun j =>
          normalCDF ((t (j + 1) : ℝ) - (t j : ℝ)) (u j)))
/-- Brownian path plus lambda t minus t squared / 2. -/
def drift (w : BrownianPath) (lam : ℝ) (t : NNReal) : ℝ :=
  w t + lam * (t : ℝ) - (t : ℝ) ^ 2 / 2
/-- Drifted path reflected above its running minimum on the closed interval [0,t]. -/
def reflected (w : BrownianPath) (lam : ℝ) (t : NNReal) : ℝ :=
  drift w lam t - sInf ((drift w lam) '' Set.Icc 0 t)
/-- A positive open excursion with finite nonnegative endpoints and zeros at both endpoints. -/
def excursion (w : BrownianPath) (lam : ℝ) (a b : NNReal) : Prop :=
  a < b ∧ reflected w lam a = 0 ∧ reflected w lam b = 0 ∧
    ∀ t ∈ Set.Ioo a b, 0 < reflected w lam t
/-- One-based ranked excursion lengths in extended nonnegative reals, using distinct excursions; rank zero is zero. -/
def excursionRankExtended (w : BrownianPath) (lam : ℝ) (i : ℕ) : ENNReal :=
  if i = 0 then 0 else sSup {r : ENNReal |
    ∃ e : Fin i → NNReal × NNReal, Function.Injective e ∧
      ∀ j, excursion w lam (e j).1 (e j).2 ∧
        r ≤ ENNReal.ofReal (((e j).2 : ℝ) - ((e j).1 : ℝ))}
/-- Real-valued excursion rank; the theorem separately asserts positive finite extended ranks almost surely. -/
def excursionRank (w : BrownianPath) (lam : ℝ) (i : ℕ) : ℝ :=
  (excursionRankExtended w lam i).toReal
/-- Strict rank-two excursion-length distribution. -/
def criticalCDF (mu : PathLaw) (lam x : ℝ) : ℝ :=
  (mu {w | excursionRank w lam 2 < x}).toReal
/-- Strict excursion-length distribution for the specified rank. -/
def rankCDF (mu : PathLaw) (lam : ℝ) (i : ℕ) (x : ℝ) : ℝ :=
  (mu {w | excursionRank w lam i < x}).toReal
/-- Joint strict distribution of the first k excursion lengths; k=0 gives the whole path space. -/
def jointCDF (mu : PathLaw) (lam : ℝ) (k : ℕ) (x : Fin k → ℝ) : ℝ :=
  (mu {w | ∀ i : Fin k, excursionRank w lam (i.val + 1) < x i}).toReal
/-- Existence of a Brownian law, finite positive ranks, and critical rank-two and finite-rank rectangle convergence at continuity points. -/
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
/-- The conjunction of all five sparse-regime statements, pointwise for every feasible edge-count sequence. -/
def AtlasStatement : Prop :=
  fixedSubcriticalLaw ∧ fixedSupercriticalLaw ∧ barelySubcriticalLaw ∧
    barelySupercriticalLaw ∧ criticalLaw

end
end Erdos745.WrapUp
/-- Corrected sparse evolution atlas for uniform labelled graphs G(n,M). -/
theorem Erdos745.Palomar.sparseEvolution : Erdos745.WrapUp.AtlasStatement := by
  sorry
