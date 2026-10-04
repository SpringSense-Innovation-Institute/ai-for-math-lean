module

import all Mathlib.Basic.Real.Basic
public import Erdos448.stage6.TaskContracts
public import Erdos448.stage7.tasks.«ROOT-02».Assembly

public section

set_option backward.isDefEq.respectTransparency false

namespace Erdos448.Stage7.ROOT02.Work

open Erdos448.Stage4.Contracts
open Erdos448.Stage6.TaskContracts

theorem result : Erdos448.Stage6.TaskContracts.ROOT02Target := by
  intro hEXT h007 h008
  exact Erdos448.Stage7.ROOT02.Assembly.p020 hEXT h007 h008

end Erdos448.Stage7.ROOT02.Work
