module

import all Mathlib.Basic.Real.Basic
public import Erdos448.dependencies.«DP-MEAN».stage4.Design

public section

set_option backward.isDefEq.respectTransparency false

-- MM:BEGIN dpmean-task-interfaces
open Erdos448.DPMean

@[expose] abbrev Erdos448.DPMean.S6.T01Target : Prop :=
  P001Statement ∧ P003Statement

@[expose] abbrev Erdos448.DPMean.S6.T02Target : Prop :=
  P002Statement

@[expose] abbrev Erdos448.DPMean.S6.T03Target : Prop :=
  SmoothingDefinitionStatement ∧ P004Statement ∧ P005Statement

@[expose] abbrev Erdos448.DPMean.S6.T04Target : Prop :=
  P006Statement

@[expose] abbrev Erdos448.DPMean.S6.T05Target : Prop :=
  P003Statement → P007Statement

@[expose] abbrev Erdos448.DPMean.S6.T06Target : Prop :=
  P002Statement → P008Statement

@[expose] abbrev Erdos448.DPMean.S6.T07Target : Prop :=
  P006Statement →
  P007Statement →
  P008Statement →
  SmoothingDefinitionStatement →
  P004Statement →
  P005Statement →
  P009Statement ∧ P010Statement

/- Compatibility-only lowering telescope: the checker consumes each supplier
package once.  The public T07Target above remains unchanged. -/
@[expose] abbrev Erdos448.DPMean.S6.T07PackageTarget : Prop :=
  P006Statement →
  P007Statement →
  P008Statement →
  Erdos448.DPMean.S6.T03Target →
  P009Statement ∧ P010Statement

@[expose] abbrev Erdos448.DPMean.S6.T08Target : Prop :=
  P011Statement

@[expose] abbrev Erdos448.DPMean.S6.T09Target : Prop :=
  P012FullStatement

@[expose] abbrev Erdos448.DPMean.S6.T10Target : Prop :=
  P010Statement → P011Statement → P012FullStatement → T001Statement

/- Compatibility-only lowering telescope: T10 receives T07's closed output
package once and uses its P010 projection.  The public T10Target is unchanged. -/
@[expose] abbrev Erdos448.DPMean.S6.T10PackageTarget : Prop :=
  (P009Statement ∧ P010Statement) →
  P011Statement →
  P012FullStatement →
  T001Statement
-- MM:END dpmean-task-interfaces
