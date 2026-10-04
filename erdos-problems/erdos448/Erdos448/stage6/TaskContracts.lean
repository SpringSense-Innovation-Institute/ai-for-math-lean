module

import all Mathlib.Basic.Real.Basic
public import Erdos448.stage4.contracts.GroupA
public import Erdos448.stage4.contracts.GroupB
public import Erdos448.stage4.contracts.GroupC
public import Erdos448.stage4.contracts.GroupD
public import Erdos448.stage4.DependencyAdapters

public section

set_option backward.isDefEq.respectTransparency false

/-!
Frozen S5 currying surface for the thirteen root S7 tasks.

Every unproved cross-task theorem occurs only as an input to a task target.
This file declares proposition and export structures; it supplies no proof
term, axiom, or theorem implementation.
-/

namespace Erdos448.Stage6.TaskContracts

open Erdos448.Stage4
open Erdos448.Stage4.Contracts

structure Root01Exports : Prop where
  p001 : P001Statement
  p001A : P001AStatement
  /-- Construction-critical local convergence/factorization adapter for P-005. -/
  p005A : P005AStatement
  p005 : P005Statement
  p007 : P007Statement
  p008 : P008Statement.{0}

@[expose] def ROOT01Target : Prop :=
  EXT001Statement → EXT002Statement → Root01Exports

@[expose] def ROOT02Target : Prop :=
  EXT001Statement → P007Statement → P008Statement.{0} → P020Statement

@[expose] def ROOT03Target : Prop := P034Statement

@[expose] def ROOT04Target : Prop := P044Statement

structure Root05Exports where
  p050 : P050Statement
  weightChain : WeightChainSpec
  p001C : P001CStatement
  commonWeights : CommonWeightWitnesses
  p051H : P051HStatement

@[expose] def ROOT05Target : Prop := P001AStatement → Nonempty Root05Exports

@[expose] def FoundationP053Target : Prop := P053Statement

structure FoundationP068P069Exports : Prop where
  p068 : P068Statement
  p069 : P069Statement

@[expose] def FoundationP068P069Target : Prop := FoundationP068P069Exports

structure Root06Exports : Prop where
  p052 : P052Statement
  p053 : P053Statement
  p054 : P054Statement
  p054A : P054AStatement
  p055 : P055Statement
  p056 : P056Statement
  p057 : P057Statement
  p058 : P058Statement
  p059 : P059Statement.{0}

@[expose] def ROOT06Target : Prop :=
  EXT001Statement → P001CStatement → P005Statement →
  P007Statement → P008Statement.{0} →
  WeightChainSpec → CommonWeightWitnesses → P051HStatement →
  P053Statement → Root06Exports

structure Root07Exports : Prop where
  p060 : P060Statement
  p061 : P061Statement
  p062 : P062Statement
  p063 : P063Statement
  p064 : P064Statement
  p065 : P065Statement
  p066 : P066Statement
  p067 : P067Statement
  p068 : P068Statement
  p069 : P069Statement
  p070 : P070Statement

@[expose] def ROOT07Target : Prop :=
  P050Statement → P052Statement → P053Statement → P054Statement →
  P055Statement → P056Statement → P057Statement → CommonWeightWitnesses →
  P059Statement.{0} → P068Statement → P069Statement → Root07Exports

@[expose] def ROOT08Target : Prop :=
  P058Statement → P060Statement → P061Statement → P062Statement →
  P063Statement → P064Statement → P065Statement → P066Statement →
  P067Statement → P068Statement → P069Statement → P070Statement →
  P074Statement

structure Root09Exports : Prop where
  p075 : P075Statement
  p076 : P076Statement
  p077 : P077Statement
  p078 : P078Statement
  p079 : P079Statement
  p080 : P080Statement
  p081 : P081Statement
  p082 : P082Statement
  p083 : P083Statement
  p084 : P084Statement

@[expose] def ROOT09Target : Prop :=
  P005Statement → P007Statement → P008Statement.{0} → P050Statement →
  P052Statement → P053Statement → P054Statement → P054AStatement →
  WeightChainSpec → CommonWeightWitnesses → P051HStatement → P057Statement →
  Root09Exports

@[expose] def ROOT10Target : Prop :=
  P070Statement → P074Statement → P075Statement → P076Statement →
  P077Statement → P078Statement → P079Statement → P080Statement →
  P081Statement → P082Statement → P083Statement → P084Statement →
  P089Statement

structure Root11Exports : Prop where
  p092 : P092Statement
  p096 : P096Statement
  p097 : P097Statement
  p100 : P100Statement
  p101 : P101Statement

@[expose] def ROOT11Target : Prop :=
  P044Statement → P054Statement → Root11Exports

@[expose] def ROOT12Target : Prop :=
  P089Statement → P092Statement → P096Statement → P097Statement →
  P100Statement → P101Statement → P102Statement

@[expose] def ROOT13Target : Prop :=
  P020Statement → P034Statement → P102Statement → NegativeAnswer

@[expose] def DPMeanEXT001AdapterTarget : Prop :=
  Erdos448.DPMean.T001Statement → EXT001Statement
end Erdos448.Stage6.TaskContracts
