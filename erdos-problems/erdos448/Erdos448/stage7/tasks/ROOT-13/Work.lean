module

import all Mathlib.Basic.Real.Basic
public import Erdos448.stage7.tasks.«ROOT-13».Recovered

public section

set_option backward.isDefEq.respectTransparency false

/-!
ROOT-13 worker surface (pre-CU ROOT ownership restored).

Every owned node is already recovered as CONDITIONALLY_VERIFIED and imported
above — see `RECOVERY_STATE.md`. The remaining task is assembling
`Erdos448.Stage6.TaskContracts.ROOT13Target` from the recovered nodes as
`Erdos448.Stage7.ROOT13.Work.result`. The S7 premises P-020 (ROOT-02),
P-034 (ROOT-03), P-102 (ROOT-12) stay explicit theorem parameters until S8
linking. Optional cross-check nodes P-118/P-119 are not required.
-/

namespace Erdos448.Stage7.ROOT13.Work

open Erdos448.Stage4
open Erdos448.Stage4.Contracts
open Erdos448.Stage6.TaskContracts
open Erdos448.Stage7.ROOT13.Recovered

theorem result : ROOT13Target := by
  intro h020 h034 h102
  let h112 : P112Statement := p112 h020 h034 h102
  let h117 : P117Statement := p117 h112
  exact final_negative_answer h117

end Erdos448.Stage7.ROOT13.Work
