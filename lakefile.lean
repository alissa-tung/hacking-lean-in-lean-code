import Lake
open Lake DSL

package «hacking-lean-in-lean-src» where

@[default_target]
lean_lib «HackingLeanInLeanSrc» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"
