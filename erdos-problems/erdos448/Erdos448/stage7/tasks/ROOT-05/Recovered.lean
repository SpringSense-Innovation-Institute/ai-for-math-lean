module

import all Mathlib.Basic.Real.Basic
public import Erdos448.stage7.tasks.«ROOT-05».recovered.P051AE
public import Erdos448.stage7.tasks.«ROOT-05».recovered.P051VF4
public import Erdos448.stage6.TaskContracts

public section

set_option backward.isDefEq.respectTransparency false

/-!
Recovered verified node proofs for ROOT-05.

These theorems are the verbatim verified constructions recovered from the
historical CU run (ledger: `Erdos448/stage7/recovery/PRE_CU_PROOF_RECOVERY.json`).
They are immutable solved prerequisites for the ROOT-05 worker. The concrete
`weightChainWitness` preserves the exact shared witness identity required by
the remaining nodes (P-051G/H) and by the ROOT-05 export assembly.
-/

namespace Erdos448.Stage7.ROOT05.Recovered

open Erdos448.Stage4
open Erdos448.Stage4.Contracts
open Erdos448.Stage6.TaskContracts

theorem p051A : P051AStatement := P051AE.node_p051A
theorem p051B : P051BStatement := P051AE.node_p051B
theorem p051C : P051CStatement := P051AE.node_p051C
theorem p051D : P051DStatement := P051AE.node_p051D
theorem p051E : P051EStatement := P051AE.node_p051E

theorem p051V : P051VStatement := P051VF4.node_p051V
theorem p051F1 : P051F1Statement := P051VF4.node_p051F1
theorem p051F2 : P051F2Statement := P051VF4.node_p051F2
theorem p051F3 : P051F3Statement := P051VF4.node_p051F3
theorem p051F4 : P051F4Statement := P051VF4.node_p051F4

/-- The recovered concrete weight-chain witness. -/
@[expose] noncomputable def weightChain : WeightChainSpec := P051VF4.weightChainWitness

end Erdos448.Stage7.ROOT05.Recovered
