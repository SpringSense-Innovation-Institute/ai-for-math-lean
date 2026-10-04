module

import all Mathlib.Basic.Real.Basic
public import Erdos448.dependencies.«DP-MEAN».stage6.tasks.T01.Work
public import Erdos448.dependencies.«DP-MEAN».stage6.tasks.T02.Work
public import Erdos448.dependencies.«DP-MEAN».stage6.tasks.T03.Work
public import Erdos448.dependencies.«DP-MEAN».stage6.tasks.T04.Work
public import Erdos448.dependencies.«DP-MEAN».stage6.tasks.T05.Work
public import Erdos448.dependencies.«DP-MEAN».stage6.tasks.T06.Work
public import Erdos448.dependencies.«DP-MEAN».stage6.tasks.T07.Work
public import Erdos448.dependencies.«DP-MEAN».stage6.tasks.T08.Work
public import Erdos448.dependencies.«DP-MEAN».stage7.T09.Work
public import Erdos448.dependencies.«DP-MEAN».stage7.T10.Work

public section

set_option backward.isDefEq.respectTransparency false

namespace Erdos448.DPMean.Stage8

open Erdos448.DPMean

theorem target : T001Statement := by
  let p001_p003 := Erdos448.DPMean.TaskT01.target
  let p002 := Erdos448.DPMean.TaskT02.publicTarget
  let smoothing_p004_p005 := Erdos448.DPMean.TaskT03.direct
  let p006 := Erdos448.DPMean.TaskT04.publicTarget
  let p007 := Erdos448.DPMean.TaskT05.constructed p001_p003.2
  let p008 := Erdos448.DPMean.TaskT06.publicTarget p002
  let p009_p010 := Erdos448.DPMean.TaskT07.constructed
    p006 p007 p008
    smoothing_p004_p005.1
    smoothing_p004_p005.2.1
    smoothing_p004_p005.2.2
  exact Erdos448.DPMean.TaskT10.publicTarget
    p009_p010
    Erdos448.DPMean.TaskT08.publicTarget
    Erdos448.DPMean.TaskT09.constructed

end Erdos448.DPMean.Stage8
