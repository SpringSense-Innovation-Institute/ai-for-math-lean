module

import all Mathlib.Basic.Real.Basic
public import Erdos448.dependencies.«DP-MERTENS».stage7.tasks.TASK_MSC_CHEBYSHEV.Result
public import Erdos448.dependencies.«DP-MERTENS».stage7.tasks.TASK_MSC_FIRST_LEMMA.Result
public import Erdos448.dependencies.«DP-MERTENS».stage7.tasks.TASK_MSC_ZETA.Result
public import Erdos448.dependencies.«DP-MERTENS».stage7.tasks.TASK_MSC_TAIL.Result
public import Erdos448.dependencies.«DP-MERTENS».stage7.tasks.TASK_MSC_EXPINT.Result
public import Erdos448.dependencies.«DP-MERTENS».stage7.tasks.TASK_MSC_ASSEMBLY.Result
public import Erdos448.dependencies.«DP-MERTENS».stage7.tasks.TASK_MERT_CORRECTION.Result
public import Erdos448.dependencies.«DP-MERTENS».stage7.tasks.TASK_MERT_PRODUCT_CORE.Result
public import Erdos448.dependencies.«DP-MERTENS».stage7.tasks.TASK_MERT_ENDPOINTS.Result
public import Erdos448.dependencies.«DP-MERTENS».stage7.tasks.TASK_MERT_FINAL.Result

public section

set_option backward.isDefEq.respectTransparency false

namespace Erdos448.DPMertens.Stage8

open Erdos448.DPMertens.Lowering

noncomputable section

@[expose] def chebyshev : ChebyshevOutput :=
  Erdos448.DPMertens.Tasks.MSCChebyshev.result

@[expose] def firstLemma : FirstLemmaOutput :=
  Erdos448.DPMertens.Tasks.MSCFirstLemma.result chebyshev

@[expose] def correction : CorrectionOutput :=
  Erdos448.DPMertens.Tasks.MertCorrection.result

@[expose] def primeZeta : ZetaTaskOutput :=
  Erdos448.DPMertens.Tasks.MSCZeta.result correction

@[expose] def primeTail : TailTaskOutput :=
  Erdos448.DPMertens.Tasks.MSCTail.result firstLemma

@[expose] def expIntegral : ExpIntegralOutput :=
  Erdos448.DPMertens.Tasks.MSCExpInt.result

@[expose] def assembly : AssemblyTaskOutput :=
  Erdos448.DPMertens.Tasks.MSCAssembly.result primeZeta primeTail expIntegral

@[expose] def weakProduct : WeakProductTaskOutput :=
  Erdos448.DPMertens.Tasks.MertProductCore.result assembly correction

@[expose] def endpoints : EndpointOutput :=
  Erdos448.DPMertens.Tasks.MertEndpoints.result

@[expose] def finalPackage : FinalTaskOutput :=
  Erdos448.DPMertens.Tasks.MertFinal.result weakProduct endpoints

/-- The direct kernel-closed DP-MERTENS export. -/
theorem target : FT_MERTENS := by
  refine ⟨finalPackage.final.strict_asymptotic, ?_⟩
  exact ⟨finalPackage.final.X_M, finalPackage.final.c_M_minus,
    finalPackage.final.c_M_plus, finalPackage.final.X_M_ge_two,
    finalPackage.final.c_M_minus_pos, finalPackage.final.c_M_plus_pos,
    finalPackage.final.interval_comparison⟩

end

end Erdos448.DPMertens.Stage8
