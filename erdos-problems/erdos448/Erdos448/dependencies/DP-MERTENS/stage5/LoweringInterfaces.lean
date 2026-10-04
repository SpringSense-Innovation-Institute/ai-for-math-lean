module

import all Mathlib.Basic.Real.Basic
public import Erdos448.dependencies.«DP-MERTENS».stage4.DP_Mertens_Design

public section

set_option backward.isDefEq.respectTransparency false

/-!
Declaration-only interfaces for the executable S5 lowering record.

The content-addressed lowering library imports the frozen S4 declaration asset
before this file.  No declaration below asserts a theorem or contains a proof
body; task workers must construct the package values.
-/

open Filter Finset MeasureTheory Set
open scoped BigOperators Topology

namespace Erdos448.DPMertens.Lowering

noncomputable section

open Erdos448.DPMertens

/-! ## Closed task packages -/

structure ChebyshevOutput where
  increment : forall n : Nat, 0 < n ->
    theta (2 * n) - theta n <= (n : Real) * Real.log 4
  C_vartheta : Real
  C_vartheta_pos : 0 < C_vartheta
  weak_bound : forall t : Real, 2 <= t -> theta t <= C_vartheta * t

structure FirstLemmaOutput where
  C_V : Real
  C_V_nonneg : 0 <= C_V
  prime_power_bound : forall n : Nat, 2 <= n ->
    |primePowerSum n - Real.log n| <= C_V
  C_A : Real
  C_A_pos : 0 < C_A
  first_lemma : forall t : Real, 2 <= t ->
    |weightedPrimeSum t - Real.log t| <= C_A

structure CorrectionOutput where
  H : Real
  localCorrection : LocalCorrectionContract
  convergence : CorrectionConvergenceContract H
  tail : forall x : Real, 2 <= x ->
    0 <= H - correctionLE x /\ H - correctionLE x <= 2 / (x - 1)

@[expose] def ZetaPoleNormalization : Prop :=
  Tendsto (fun rho : Real => zetaOnePlus rho - rho ^ (-1 : Int))
      rhoDownZero (nhds Real.eulerMascheroniConstant) /\
    Tendsto (fun rho : Real =>
      Real.log (zetaOnePlus rho) - Real.log (rho ^ (-1 : Int)))
      rhoDownZero (nhds 0)

structure PrimeZetaOutput (H : Real) where
  pole_normalization : ZetaPoleNormalization
  epsilon0 : Real -> Real
  formula : forall rho : Real, 0 < rho ->
    primeZetaOnePlus rho = Real.log (rho ^ (-1 : Int)) - H + epsilon0 rho
  epsilon0_tendsto : Tendsto epsilon0 rhoDownZero (nhds 0)

/-- Closed lowering package for P-MSC-03A/B.  The correction convergence,
analytic bridge, and public prime-zeta output all use this package's one `H`.
The task target consumes a local `corr : CorrectionOutput`, from which this
single witness is constructed. -/
structure ZetaTaskOutput where
  corr : CorrectionOutput
  analytic_bridge : PrimeZetaAnalyticBridge corr.H
  pole : ZetaPoleNormalization
  prime_zeta : PrimeZetaOutput corr.H

@[expose] def primeTailIntegral (G rho : Real) : Real :=
  integral (volume.restrict (Ioi G))
    (fun t : Real => 1 / (Real.rpow t (1 + rho) * Real.log t))

structure PrimeTailOutputOf (C_A : Real) where
  mathcalE : Nat -> Real -> Real
  formula : forall G : Nat, 2 <= G -> forall rho : Real, 0 < rho ->
    (tsum fun p : Nat =>
      if p.Prime /\ G < p then Real.rpow p (-(1 + rho)) else 0) =
      primeTailIntegral G rho + mathcalE G rho
  uniform_bound : forall G : Nat, 2 <= G -> forall rho : Real, 0 < rho ->
    |mathcalE G rho| <= 2 * C_A / Real.log G

/-- The tail theorem carries the exact first-lemma package whose `C_A`
indexes its output. No independent tail constant can be selected. -/
structure TailTaskOutput where
  first : FirstLemmaOutput
  tail : PrimeTailOutputOf first.C_A

structure ExpIntegralOutput where
  epsilonG : Real -> Real -> Real
  formula : forall G : Real, 2 <= G -> forall rho : Real, 0 < rho ->
    primeTailIntegral G rho = Real.log (rho ^ (-1 : Int)) -
      Real.log (Real.log G) - Real.eulerMascheroniConstant + epsilonG G rho
  epsilonG_tendsto : forall G : Real, 2 <= G ->
    Tendsto (epsilonG G) rhoDownZero (nhds 0)

structure SumAssemblyOutput (H : Real) where
  data : SumConstantInterface
  same_H : data.H = H

/-- Closed carrier retaining the exact zeta/correction package used to build
the child output. -/
structure AssemblyTaskOutput where
  zeta : ZetaTaskOutput
  assembly : SumAssemblyOutput zeta.corr.H

structure WeakProductOutput (corr : CorrectionOutput)
    (child : SumAssemblyOutput corr.H) where
  finite_log : FiniteProductLogContract
  E : Real -> Real
  CE : Real
  XE : Real
  E_definition : forall x : Real, 2 <= x ->
    E x = (child.data.H - correctionLE x) - child.data.R x
  log_cancellation : forall x : Real, 2 <= x ->
    Real.log (qLE x) =
      -Real.log (Real.log x) - Real.eulerMascheroniConstant + E x
  E_rate : ReciprocalLogRate E CE XE
  E_tendsto : Tendsto E atTop (nhds 0)
  relativeError : Real -> Real
  CRelative : Real
  XRelative : Real
  relativeError_definition : forall x : Real, 2 <= x ->
    relativeError x = Real.exp (E x) - 1
  exact_exponential : forall x : Real, 2 <= x ->
    qLE x = mertensMain x * Real.exp (E x)
  exact_relative : forall x : Real, 2 <= x ->
    qLE x = mertensMain x * (1 + relativeError x)
  relative_rate : ReciprocalLogRate relativeError CRelative XRelative
  asymptotic : AtTopEquivalent qLE mertensMain

/-- Closed carrier preserving the dependent correction/child/weak-product
identity across task boundaries. -/
structure WeakProductTaskOutput where
  corr : CorrectionOutput
  child : SumAssemblyOutput corr.H
  weak : WeakProductOutput corr child

structure EndpointOutput where
  endpoint : EndpointContract
  interval : IntervalQuotientContract

structure FinalOutput (corr : CorrectionOutput)
    (child : SumAssemblyOutput corr.H)
    (weak : WeakProductOutput corr child) (ends : EndpointOutput) where
  strictRelativeError : Real -> Real
  CStrict : Real
  XStrict : Real
  strict_exact : forall x : Real, 2 <= x ->
    qLT x = mertensMain x * (1 + strictRelativeError x)
  strict_rate : ReciprocalLogRate strictRelativeError CStrict XStrict
  strict_asymptotic : StrictMertensAsymptotic
  X_M : Real
  c_M_minus : Real
  c_M_plus : Real
  X_M_ge_two : 2 <= X_M
  c_M_minus_pos : 0 < c_M_minus
  c_M_plus_pos : 0 < c_M_plus
  interval_comparison : forall A B : Real, X_M <= A -> A < B ->
    c_M_minus * (Real.log A / Real.log B) <= intervalProduct A B /\
    intervalProduct A B <= c_M_plus * (Real.log A / Real.log B)

/-- Closed carrier for the exact dependent final result. -/
structure FinalTaskOutput where
  corr : CorrectionOutput
  child : SumAssemblyOutput corr.H
  weak : WeakProductOutput corr child
  ends : EndpointOutput
  final : FinalOutput corr child weak ends

/-! ## Closed proposition interfaces for required proof objects -/

@[expose] def P_MSC_01A : Prop := forall n : Nat, 0 < n ->
  theta (2 * n) - theta n <= (n : Real) * Real.log 4

@[expose] def P_MSC_01B : Prop := exists C : Real, 0 < C /\
  forall t : Real, 2 <= t -> theta t <= C * t

@[expose] def P_MSC_02A : Prop := exists C : Real, 0 <= C /\
  forall n : Nat, 2 <= n -> |primePowerSum n - Real.log n| <= C

@[expose] def P_MSC_02B : Prop := exists C : Real, 0 < C /\
  forall t : Real, 2 <= t -> |weightedPrimeSum t - Real.log t| <= C

@[expose] def P_MSC_03A : Prop := ZetaPoleNormalization

@[expose] def P_MSC_03B : Prop := exists H : Real,
  CorrectionConvergenceContract H /\
  Nonempty (PrimeZetaAnalyticBridge H) /\ Nonempty (PrimeZetaOutput H)

@[expose] def P_MSC_04 : Prop := Nonempty TailTaskOutput

@[expose] def P_MSC_05 : Prop := Nonempty ExpIntegralOutput

@[expose] def P_MSC_06A : Prop := exists d : SumConstantInterface,
  forall G : Nat, 2 <= G ->
    reciprocalPrimeSumNat G = Real.log (Real.log G) + d.B + d.Delta G /\
    |d.Delta G| <= d.C0 / Real.log G

@[expose] def P_MSC_06B : Prop := exists d : SumConstantInterface,
  forall x : Real, 2 <= x ->
    reciprocalPrimeSum x = Real.log (Real.log x) + d.B + d.R x

@[expose] def P_MSC_07 : Prop := exists H : Real,
  CorrectionConvergenceContract H /\
  forall x : Real, 2 <= x ->
    0 <= H - correctionLE x /\ H - correctionLE x <= 2 / (x - 1)

@[expose] def EXT_MERT_01 : Prop := exists d : SumConstantInterface,
  (forall x : Real, 2 <= x ->
    reciprocalPrimeSum x = Real.log (Real.log x) + d.B + d.R x) /\
  ReciprocalLogRate d.R d.CR d.XR /\ Tendsto d.R atTop (nhds 0)

@[expose] def EXT_MERT_02 : Prop := exists d : SumConstantInterface,
  d.B = Real.eulerMascheroniConstant - d.H

@[expose] def P_MERT_01 : Prop := LocalCorrectionContract

@[expose] def P_MERT_02 : Prop := exists H : Real, CorrectionConvergenceContract H

@[expose] def P_MERT_03 : Prop := FiniteProductLogContract

@[expose] def P_MERT_04 : Prop := Nonempty WeakProductTaskOutput

@[expose] def P_MERT_05 : Prop := exists w : WeakProductTaskOutput,
  ReciprocalLogRate w.weak.relativeError w.weak.CRelative w.weak.XRelative /\
  AtTopEquivalent qLE mertensMain

@[expose] def P_MERT_06A : Prop := EndpointContract

@[expose] def P_MERT_06B : Prop := IntervalQuotientContract

@[expose] def P_MERT_07 : Prop := exists f : FinalTaskOutput,
  ReciprocalLogRate f.final.strictRelativeError f.final.CStrict f.final.XStrict /\
  StrictMertensAsymptotic

@[expose] def P_MERT_08 : Prop := IntervalComparisonContract

@[expose] def FT_MERTENS : Prop := EXT002Contract

/-! ## Required definition interfaces -/

@[expose] def D_MERT_01 (x : Real) : Real × Real × Real :=
  (qLE x, qLT x, endpointFactor x)

@[expose] abbrev D_MERT_02 := CorrectionOutput

@[expose] def D_MSC_01 (t rho : Real) (n : Nat) : Real × Real × Real × Real :=
  (theta t, weightedPrimeSum t, tailKernel rho t, primePowerSum n)

@[expose] def S_MSC_01A : Prop := P_MSC_01A
@[expose] def S_MSC_01B (C : Real) : Prop := 0 < C /\
  forall t : Real, 2 <= t -> theta t <= C * t
@[expose] def S_MSC_02A (C : Real) : Prop := 0 <= C /\
  forall n : Nat, 2 <= n -> |primePowerSum n - Real.log n| <= C
@[expose] def S_MSC_02B (C : Real) : Prop := 0 < C /\
  forall t : Real, 2 <= t -> |weightedPrimeSum t - Real.log t| <= C
@[expose] def S_MSC_03A : Prop := ZetaPoleNormalization
@[expose] def S_MSC_03B (epsilon0 : Real -> Real) : Prop :=
  exists H : Real, (forall rho : Real, 0 < rho ->
    primeZetaOnePlus rho = Real.log (rho ^ (-1 : Int)) - H + epsilon0 rho) /\
    Tendsto epsilon0 rhoDownZero (nhds 0)
@[expose] def S_MSC_04 (C_A : Real) (mathcalE : Nat -> Real -> Real) : Prop :=
  forall G : Nat, 2 <= G -> forall rho : Real, 0 < rho ->
    |mathcalE G rho| <= 2 * C_A / Real.log G
@[expose] def S_MSC_05 (epsilon : Real -> Real -> Real) : Prop :=
  forall G : Real, 2 <= G -> Tendsto (epsilon G) rhoDownZero (nhds 0)
@[expose] def S_MSC_06A (B : Real) (Delta : Nat -> Real) (C0 : Real) : Prop :=
  forall G : Nat, 2 <= G ->
    reciprocalPrimeSumNat G = Real.log (Real.log G) + B + Delta G /\
    |Delta G| <= C0 / Real.log G
@[expose] def S_MSC_06B (B : Real) (R : Real -> Real) (CR XR : Real) : Prop :=
  ReciprocalLogRate R CR XR /\ forall x : Real, 2 <= x ->
    reciprocalPrimeSum x = Real.log (Real.log x) + B + R x
@[expose] def S_MSC_07 : Prop := P_MSC_07
@[expose] def S_EXT_MERT_01 (B : Real) (R : Real -> Real) (CR XR : Real) : Prop :=
  ReciprocalLogRate R CR XR /\ Tendsto R atTop (nhds 0)
@[expose] def S_EXT_MERT_02 (B : Real) : Prop := exists H : Real,
  B = Real.eulerMascheroniConstant - H
@[expose] def S_MERT_01 : Prop := LocalCorrectionContract
@[expose] def S_MERT_02 : Prop := P_MERT_02
@[expose] def S_MERT_03 : Prop := FiniteProductLogContract
@[expose] def S_MERT_04 (B : Real) (R E : Real -> Real) : Prop :=
  forall x : Real, 2 <= x -> E x = B - R x
@[expose] def S_MERT_05 : Prop := P_MERT_05
@[expose] def S_MERT_06A : Prop := EndpointContract
@[expose] def S_MERT_06B : Prop := IntervalQuotientContract
@[expose] def S_MERT_07 : Prop := P_MERT_07
@[expose] def S_MERT_08 (X0 cMinus cPlus : Real) : Prop :=
  2 <= X0 /\ 0 < cMinus /\ 0 < cPlus /\
  forall A B : Real, X0 <= A -> A < B ->
    cMinus * (Real.log A / Real.log B) <= intervalProduct A B /\
    intervalProduct A B <= cPlus * (Real.log A / Real.log B)
@[expose] def S_FT_MERTENS : Prop := StrictMertensAsymptotic

@[expose] abbrev W_C_vartheta := Real
@[expose] abbrev W_C_V := Real
@[expose] abbrev W_C_A := Real
@[expose] abbrev W_epsilon_0 := Real -> Real
@[expose] abbrev W_mathcal_E := Nat -> Real -> Real
@[expose] abbrev W_epsilon_G := Real -> Real -> Real
@[expose] abbrev W_B := Real
@[expose] abbrev W_Delta := Nat -> Real
@[expose] abbrev W_C_0 := Real
@[expose] abbrev W_R := Real -> Real
@[expose] abbrev W_C_R := Real
@[expose] abbrev W_X_R := Real
@[expose] abbrev W_E := Real -> Real
@[expose] abbrev W_X_0 := Real

/-! ## Frozen task telescopes -/

@[expose] def TASK_MSC_CHEBYSHEV_Target := ChebyshevOutput

@[expose] def TASK_MSC_FIRST_LEMMA_Target :=
  forall _hChebyshev : ChebyshevOutput, FirstLemmaOutput

@[expose] def TASK_MSC_ZETA_Target :=
  forall _corr : CorrectionOutput, ZetaTaskOutput

@[expose] def TASK_MSC_TAIL_Target :=
  forall _hFirstLemma : FirstLemmaOutput, TailTaskOutput

@[expose] def TASK_MSC_EXPINT_Target := ExpIntegralOutput

@[expose] def TASK_MSC_ASSEMBLY_Target :=
  forall (_hPrimeZeta : ZetaTaskOutput) (_hTail : TailTaskOutput)
    (_hExpInt : ExpIntegralOutput), AssemblyTaskOutput

@[expose] def TASK_MERT_CORRECTION_Target := CorrectionOutput

@[expose] def TASK_MERT_PRODUCT_CORE_Target :=
  forall (_hChild : AssemblyTaskOutput) (_hCorrection : CorrectionOutput),
    WeakProductTaskOutput

@[expose] def TASK_MERT_ENDPOINTS_Target := EndpointOutput

@[expose] def TASK_MERT_FINAL_Target :=
  forall (_hWeak : WeakProductTaskOutput) (_hEndpoints : EndpointOutput),
    FinalTaskOutput

end

end Erdos448.DPMertens.Lowering

/-! The lowering checker deliberately uses a conservative lexical declaration
screen.  These fully qualified transparent aliases make every S3 interface and
task target explicit without duplicating any definition or proof. -/

@[expose] noncomputable def Erdos448.DPMertens.Lowering.I_D_MERT_01 (x : Real) :=
  Erdos448.DPMertens.Lowering.D_MERT_01 x
@[expose] abbrev Erdos448.DPMertens.Lowering.I_D_MERT_02 :=
  Erdos448.DPMertens.Lowering.D_MERT_02
@[expose] noncomputable def Erdos448.DPMertens.Lowering.I_D_MSC_01 (t rho : Real) (n : Nat) :=
  Erdos448.DPMertens.Lowering.D_MSC_01 t rho n

@[expose] abbrev Erdos448.DPMertens.Lowering.I_S_MSC_01A := Erdos448.DPMertens.Lowering.S_MSC_01A
@[expose] abbrev Erdos448.DPMertens.Lowering.I_S_MSC_01B := Erdos448.DPMertens.Lowering.S_MSC_01B
@[expose] abbrev Erdos448.DPMertens.Lowering.I_S_MSC_02A := Erdos448.DPMertens.Lowering.S_MSC_02A
@[expose] abbrev Erdos448.DPMertens.Lowering.I_S_MSC_02B := Erdos448.DPMertens.Lowering.S_MSC_02B
@[expose] abbrev Erdos448.DPMertens.Lowering.I_S_MSC_03A := Erdos448.DPMertens.Lowering.S_MSC_03A
@[expose] abbrev Erdos448.DPMertens.Lowering.I_S_MSC_03B := Erdos448.DPMertens.Lowering.S_MSC_03B
@[expose] abbrev Erdos448.DPMertens.Lowering.I_S_MSC_04 := Erdos448.DPMertens.Lowering.S_MSC_04
@[expose] abbrev Erdos448.DPMertens.Lowering.I_S_MSC_05 := Erdos448.DPMertens.Lowering.S_MSC_05
@[expose] abbrev Erdos448.DPMertens.Lowering.I_S_MSC_06A := Erdos448.DPMertens.Lowering.S_MSC_06A
@[expose] abbrev Erdos448.DPMertens.Lowering.I_S_MSC_06B := Erdos448.DPMertens.Lowering.S_MSC_06B
@[expose] abbrev Erdos448.DPMertens.Lowering.I_S_MSC_07 := Erdos448.DPMertens.Lowering.S_MSC_07
@[expose] abbrev Erdos448.DPMertens.Lowering.I_S_EXT_MERT_01 := Erdos448.DPMertens.Lowering.S_EXT_MERT_01
@[expose] abbrev Erdos448.DPMertens.Lowering.I_S_EXT_MERT_02 := Erdos448.DPMertens.Lowering.S_EXT_MERT_02
@[expose] abbrev Erdos448.DPMertens.Lowering.I_S_MERT_01 := Erdos448.DPMertens.Lowering.S_MERT_01
@[expose] abbrev Erdos448.DPMertens.Lowering.I_S_MERT_02 := Erdos448.DPMertens.Lowering.S_MERT_02
@[expose] abbrev Erdos448.DPMertens.Lowering.I_S_MERT_03 := Erdos448.DPMertens.Lowering.S_MERT_03
@[expose] abbrev Erdos448.DPMertens.Lowering.I_S_MERT_04 := Erdos448.DPMertens.Lowering.S_MERT_04
@[expose] abbrev Erdos448.DPMertens.Lowering.I_S_MERT_05 := Erdos448.DPMertens.Lowering.S_MERT_05
@[expose] abbrev Erdos448.DPMertens.Lowering.I_S_MERT_06A := Erdos448.DPMertens.Lowering.S_MERT_06A
@[expose] abbrev Erdos448.DPMertens.Lowering.I_S_MERT_06B := Erdos448.DPMertens.Lowering.S_MERT_06B
@[expose] abbrev Erdos448.DPMertens.Lowering.I_S_MERT_07 := Erdos448.DPMertens.Lowering.S_MERT_07
@[expose] abbrev Erdos448.DPMertens.Lowering.I_S_MERT_08 := Erdos448.DPMertens.Lowering.S_MERT_08
@[expose] abbrev Erdos448.DPMertens.Lowering.I_S_FT_MERTENS := Erdos448.DPMertens.Lowering.S_FT_MERTENS

@[expose] abbrev Erdos448.DPMertens.Lowering.I_W_C_vartheta := Erdos448.DPMertens.Lowering.W_C_vartheta
@[expose] abbrev Erdos448.DPMertens.Lowering.I_W_C_V := Erdos448.DPMertens.Lowering.W_C_V
@[expose] abbrev Erdos448.DPMertens.Lowering.I_W_C_A := Erdos448.DPMertens.Lowering.W_C_A
@[expose] abbrev Erdos448.DPMertens.Lowering.I_W_epsilon_0 := Erdos448.DPMertens.Lowering.W_epsilon_0
@[expose] abbrev Erdos448.DPMertens.Lowering.I_W_mathcal_E := Erdos448.DPMertens.Lowering.W_mathcal_E
@[expose] abbrev Erdos448.DPMertens.Lowering.I_W_epsilon_G := Erdos448.DPMertens.Lowering.W_epsilon_G
@[expose] abbrev Erdos448.DPMertens.Lowering.I_W_B := Erdos448.DPMertens.Lowering.W_B
@[expose] abbrev Erdos448.DPMertens.Lowering.I_W_Delta := Erdos448.DPMertens.Lowering.W_Delta
@[expose] abbrev Erdos448.DPMertens.Lowering.I_W_C_0 := Erdos448.DPMertens.Lowering.W_C_0
@[expose] abbrev Erdos448.DPMertens.Lowering.I_W_R := Erdos448.DPMertens.Lowering.W_R
@[expose] abbrev Erdos448.DPMertens.Lowering.I_W_C_R := Erdos448.DPMertens.Lowering.W_C_R
@[expose] abbrev Erdos448.DPMertens.Lowering.I_W_X_R := Erdos448.DPMertens.Lowering.W_X_R
@[expose] abbrev Erdos448.DPMertens.Lowering.I_W_E := Erdos448.DPMertens.Lowering.W_E
@[expose] abbrev Erdos448.DPMertens.Lowering.I_W_X_0 := Erdos448.DPMertens.Lowering.W_X_0

@[expose] abbrev Erdos448.DPMertens.Lowering.I_P_MSC_01A := Erdos448.DPMertens.Lowering.P_MSC_01A
@[expose] abbrev Erdos448.DPMertens.Lowering.I_P_MSC_01B := Erdos448.DPMertens.Lowering.P_MSC_01B
@[expose] abbrev Erdos448.DPMertens.Lowering.I_P_MSC_02A := Erdos448.DPMertens.Lowering.P_MSC_02A
@[expose] abbrev Erdos448.DPMertens.Lowering.I_P_MSC_02B := Erdos448.DPMertens.Lowering.P_MSC_02B
@[expose] abbrev Erdos448.DPMertens.Lowering.I_P_MSC_03A := Erdos448.DPMertens.Lowering.P_MSC_03A
@[expose] abbrev Erdos448.DPMertens.Lowering.I_P_MSC_03B := Erdos448.DPMertens.Lowering.P_MSC_03B
@[expose] abbrev Erdos448.DPMertens.Lowering.I_P_MSC_04 := Erdos448.DPMertens.Lowering.P_MSC_04
@[expose] abbrev Erdos448.DPMertens.Lowering.I_P_MSC_05 := Erdos448.DPMertens.Lowering.P_MSC_05
@[expose] abbrev Erdos448.DPMertens.Lowering.I_P_MSC_06A := Erdos448.DPMertens.Lowering.P_MSC_06A
@[expose] abbrev Erdos448.DPMertens.Lowering.I_P_MSC_06B := Erdos448.DPMertens.Lowering.P_MSC_06B
@[expose] abbrev Erdos448.DPMertens.Lowering.I_P_MSC_07 := Erdos448.DPMertens.Lowering.P_MSC_07
@[expose] abbrev Erdos448.DPMertens.Lowering.I_EXT_MERT_01 := Erdos448.DPMertens.Lowering.EXT_MERT_01
@[expose] abbrev Erdos448.DPMertens.Lowering.I_EXT_MERT_02 := Erdos448.DPMertens.Lowering.EXT_MERT_02
@[expose] abbrev Erdos448.DPMertens.Lowering.I_P_MERT_01 := Erdos448.DPMertens.Lowering.P_MERT_01
@[expose] abbrev Erdos448.DPMertens.Lowering.I_P_MERT_02 := Erdos448.DPMertens.Lowering.P_MERT_02
@[expose] abbrev Erdos448.DPMertens.Lowering.I_P_MERT_03 := Erdos448.DPMertens.Lowering.P_MERT_03
@[expose] abbrev Erdos448.DPMertens.Lowering.I_P_MERT_04 := Erdos448.DPMertens.Lowering.P_MERT_04
@[expose] abbrev Erdos448.DPMertens.Lowering.I_P_MERT_05 := Erdos448.DPMertens.Lowering.P_MERT_05
@[expose] abbrev Erdos448.DPMertens.Lowering.I_P_MERT_06A := Erdos448.DPMertens.Lowering.P_MERT_06A
@[expose] abbrev Erdos448.DPMertens.Lowering.I_P_MERT_06B := Erdos448.DPMertens.Lowering.P_MERT_06B
@[expose] abbrev Erdos448.DPMertens.Lowering.I_P_MERT_07 := Erdos448.DPMertens.Lowering.P_MERT_07
@[expose] abbrev Erdos448.DPMertens.Lowering.I_P_MERT_08 := Erdos448.DPMertens.Lowering.P_MERT_08
@[expose] abbrev Erdos448.DPMertens.Lowering.I_FT_MERTENS := Erdos448.DPMertens.Lowering.FT_MERTENS

@[expose] abbrev Erdos448.DPMertens.Lowering.I_TASK_MSC_CHEBYSHEV_Target :=
  Erdos448.DPMertens.Lowering.TASK_MSC_CHEBYSHEV_Target
@[expose] abbrev Erdos448.DPMertens.Lowering.I_TASK_MSC_FIRST_LEMMA_Target :=
  Erdos448.DPMertens.Lowering.TASK_MSC_FIRST_LEMMA_Target
@[expose] abbrev Erdos448.DPMertens.Lowering.I_TASK_MSC_ZETA_Target :=
  Erdos448.DPMertens.Lowering.TASK_MSC_ZETA_Target
@[expose] abbrev Erdos448.DPMertens.Lowering.I_TASK_MSC_TAIL_Target :=
  Erdos448.DPMertens.Lowering.TASK_MSC_TAIL_Target
@[expose] abbrev Erdos448.DPMertens.Lowering.I_TASK_MSC_EXPINT_Target :=
  Erdos448.DPMertens.Lowering.TASK_MSC_EXPINT_Target
@[expose] abbrev Erdos448.DPMertens.Lowering.I_TASK_MSC_ASSEMBLY_Target :=
  Erdos448.DPMertens.Lowering.TASK_MSC_ASSEMBLY_Target
@[expose] abbrev Erdos448.DPMertens.Lowering.I_TASK_MERT_CORRECTION_Target :=
  Erdos448.DPMertens.Lowering.TASK_MERT_CORRECTION_Target
@[expose] abbrev Erdos448.DPMertens.Lowering.I_TASK_MERT_PRODUCT_CORE_Target :=
  Erdos448.DPMertens.Lowering.TASK_MERT_PRODUCT_CORE_Target
@[expose] abbrev Erdos448.DPMertens.Lowering.I_TASK_MERT_ENDPOINTS_Target :=
  Erdos448.DPMertens.Lowering.TASK_MERT_ENDPOINTS_Target
@[expose] abbrev Erdos448.DPMertens.Lowering.I_TASK_MERT_FINAL_Target :=
  Erdos448.DPMertens.Lowering.TASK_MERT_FINAL_Target
