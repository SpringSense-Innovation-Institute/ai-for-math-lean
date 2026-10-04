module

import all Mathlib.Basic.Real.Basic
public import Erdos448.stage7.tasks.«ROOT-07».Family
public import Erdos448.stage7.tasks.«ROOT-07».Partition
public import Erdos448.stage7.tasks.«ROOT-07».Smoothing
public import Erdos448.stage7.tasks.«ROOT-07».WindowTransport

public section

set_option backward.isDefEq.respectTransparency false

namespace Erdos448.Stage7.ROOT07.Work

open Erdos448.Stage4.Contracts
open Erdos448.Stage6.TaskContracts

theorem result : ROOT07Target := by
  intro h050 h052 h053 h054 h055 h056 h057 W h059 h068 h069
  exact {
    p060 := Smoothing.p060 h050 h052
    p061 := Partition.p061
    p062 := Transport.p062 h055
    p063 := WindowTransport.p063 h054 W
    p064 := Transport.p064 h056
    p065 := WindowTransport.p065 h054 W
    p066 := Transport.p066 h057
    p067 := WindowTransport.p067 h053 h054 W
    p068 := h068
    p069 := h069
    p070 := Family.p070 W h059 }

end Erdos448.Stage7.ROOT07.Work
