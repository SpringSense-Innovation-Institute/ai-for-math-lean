module

import all Mathlib.Basic.Real.Basic
public import Erdos448.stage6.TaskContracts
public import Erdos448.stage7.tasks.«ROOT-06».Elementary
public import Erdos448.stage7.tasks.«ROOT-06».GenericMean
public import Erdos448.stage7.tasks.«ROOT-06».Outer

public section

set_option backward.isDefEq.respectTransparency false

namespace Erdos448.Stage7.ROOT06.Work

open Erdos448.Stage4
open Erdos448.Stage4.Contracts
open Erdos448.Stage6.TaskContracts

theorem p054 : P054Statement := Erdos448.Stage7.ROOT06.Elementary.p054

theorem p054A : P054AStatement := Erdos448.Stage7.ROOT06.Elementary.p054A

theorem p057 (W : CommonWeightWitnesses) : P057Statement :=
  Erdos448.Stage7.ROOT06.Elementary.p057 W

theorem result : Erdos448.Stage6.TaskContracts.ROOT06Target := by
  intro hEXT001 hP001C hP005 hP007 hP008 chain W hP051H hP053
  let h054 : P054Statement := Erdos448.Stage7.ROOT06.Elementary.p054
  exact {
    p052 := Erdos448.Stage7.ROOT06.Smoothing.p052 hP001C hP005 hP008 chain W hP051H
    p053 := hP053
    p054 := h054
    p054A := Erdos448.Stage7.ROOT06.Elementary.p054A
    p055 := Erdos448.Stage7.ROOT06.MainNodes.p055 hP005 hP008 chain W hP051H
    p056 := Erdos448.Stage7.ROOT06.MainNodes.p056 hP005 hP008 chain W hP051H
    p057 := Erdos448.Stage7.ROOT06.Elementary.p057 W
    p058 := Erdos448.Stage7.ROOT06.Outer.p058 hP005 hP008 chain W hP051H h054
    p059 := Erdos448.Stage7.ROOT06.GenericMean.p059 hEXT001 hP008 }

end Erdos448.Stage7.ROOT06.Work
