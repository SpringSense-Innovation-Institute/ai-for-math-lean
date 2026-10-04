module

import all Mathlib.Basic.Real.Basic
public import Erdos448.stage7.tasks.«ROOT-01».Work
public import Erdos448.stage7.tasks.«ROOT-02».Work
public import Erdos448.stage7.tasks.«ROOT-03».Work
public import Erdos448.stage7.tasks.«ROOT-04».Work
public import Erdos448.stage7.tasks.«ROOT-05».Work
public import Erdos448.stage7.foundation.P053.Work
public import Erdos448.stage7.foundation.«P068-P069».Work
public import Erdos448.stage7.tasks.«ROOT-06».Work
public import Erdos448.stage7.tasks.«ROOT-07».Work
public import Erdos448.stage7.tasks.«ROOT-08».Work
public import Erdos448.stage7.tasks.«ROOT-09».Work
public import Erdos448.stage7.tasks.«ROOT-10».Work
public import Erdos448.stage7.tasks.«ROOT-11».Work
public import Erdos448.stage7.tasks.«ROOT-12».Work
public import Erdos448.stage7.tasks.«ROOT-13».Work
public import Erdos448.stage7.providers.«DP-MEAN-EXT001».Work
public import Erdos448.dependencies.«DP-MEAN».stage8.Integration
public import Erdos448.dependencies.«DP-MERTENS».stage8.Integration

public section

set_option backward.isDefEq.respectTransparency false

namespace Erdos448.WrapupFinal

open Erdos448.Stage4 Erdos448.Stage4.Contracts
open Erdos448.Stage6.TaskContracts
open Erdos448.Stage7

/-- The fully linked, premise-free negative answer to Erdős problem 448. -/
theorem negativeAnswer : NegativeAnswer := by
  have e1 : EXT001Statement :=
    DPMeanEXT001Adapter.Work.result Erdos448.DPMean.Stage8.target
  have e2 : EXT002Statement :=
    Erdos448.Stage4.DependencyAdapters.adaptDPMertensEXT002
      Erdos448.DPMertens.Stage8.target
  have r1 := ROOT01.Work.result e1 e2
  have r2 := ROOT02.Work.result e1 r1.p007 r1.p008
  have r3 := ROOT03.Work.result
  have r4 := ROOT04.Work.result
  obtain ⟨r5⟩ := ROOT05.Work.result r1.p001A
  have f53 := FoundationP053.Work.result
  have f6869 := FoundationP068P069.Work.result
  have r6 := ROOT06.Work.result e1 r5.p001C r1.p005 r1.p007 r1.p008
    r5.weightChain r5.commonWeights r5.p051H f53
  have r7 := ROOT07.Work.result r5.p050 r6.p052 r6.p053 r6.p054
    r6.p055 r6.p056 r6.p057 r5.commonWeights r6.p059 f6869.p068 f6869.p069
  have r8 := ROOT08.Work.result r6.p058 r7.p060 r7.p061 r7.p062 r7.p063
    r7.p064 r7.p065 r7.p066 r7.p067 r7.p068 r7.p069 r7.p070
  have r9 := ROOT09.Work.result r1.p005 r1.p007 r1.p008 r5.p050
    r6.p052 r6.p053 r6.p054 r6.p054A r5.weightChain r5.commonWeights
    r5.p051H r6.p057
  have r10 := ROOT10.Work.result r7.p070 r8 r9.p075 r9.p076 r9.p077
    r9.p078 r9.p079 r9.p080 r9.p081 r9.p082 r9.p083 r9.p084
  have r11 := ROOT11.Work.result r4 r6.p054
  have r12 := ROOT12.Work.result r10 r11.p092 r11.p096 r11.p097
    r11.p100 r11.p101
  exact ROOT13.Work.result r2 r3 r12

end Erdos448.WrapupFinal
