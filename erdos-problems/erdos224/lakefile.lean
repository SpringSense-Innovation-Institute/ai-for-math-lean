import Lake
open Lake DSL

package "lean" {}

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "master"

lean_lib "lean" {}