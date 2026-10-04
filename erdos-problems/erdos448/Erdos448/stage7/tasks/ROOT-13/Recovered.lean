module

import all Mathlib.Basic.Real.Basic
public import Erdos448.stage7.tasks.«ROOT-13».recovered.P110112
public import Erdos448.stage7.tasks.«ROOT-13».recovered.P113117
public import Erdos448.stage7.tasks.«ROOT-13».recovered.P120FT
public import Erdos448.stage6.TaskContracts

public section

set_option backward.isDefEq.respectTransparency false

/-!
Recovered verified node proofs for ROOT-13.

These theorems are the verbatim verified constructions recovered from the
historical CU run (ledger: `Erdos448/stage7/recovery/PRE_CU_PROOF_RECOVERY.json`).
All were accepted CONDITIONALLY_VERIFIED: their unresolved S7 logical inputs
(P-020 from ROOT-02, P-034 from ROOT-03, P-102 from ROOT-12) remain explicit
theorem parameters. They are immutable solved prerequisites for the ROOT-13
worker; only S8 linking discharges the premises.
-/

namespace Erdos448.Stage7.ROOT13.Recovered

open Erdos448.Stage4
open Erdos448.Stage4.Contracts
open Erdos448.Stage6.TaskContracts

theorem p110 : P110Statement := P110112.node_p110

theorem p111 (h034 : P034Statement) : P111Statement :=
  P110112.node_p111 h034

theorem p112 (h020 : P020Statement) (h034 : P034Statement)
    (h102 : P102Statement) : P112Statement :=
  P110112.node_p112 h020 h034 h102

theorem p113 : P113Statement := P113117.node_p113

theorem p114 : P114Statement := P113117.node_p114

theorem p115 (h112 : P112Statement) : P115Statement :=
  P113117.node_p115 h112

theorem p116 : P116Statement := P113117.node_p116

theorem p117 (h112 : P112Statement) : P117Statement :=
  P113117.node_p117 h112

theorem p120 (h117 : P117Statement) : P120Statement :=
  P120FT.node_p120 h117

theorem final_negative_answer (h117 : P117Statement) : NegativeAnswer :=
  P120FT.node_final h117

end Erdos448.Stage7.ROOT13.Recovered
