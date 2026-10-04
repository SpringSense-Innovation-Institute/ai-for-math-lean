module

import all Mathlib.Basic.Real.Basic
public import Erdos448.stage6.TaskContracts

public section

set_option backward.isDefEq.respectTransparency false

namespace Erdos448.Stage7.DPMeanEXT001Adapter.Work

theorem result : Erdos448.Stage6.TaskContracts.DPMeanEXT001AdapterTarget :=
  Erdos448.Stage4.DependencyAdapters.adaptDPMeanT001

end Erdos448.Stage7.DPMeanEXT001Adapter.Work
