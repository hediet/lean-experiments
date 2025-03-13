import Lake
open Lake DSL

package «lean-playground» where
  -- add package configuration options here

lean_lib «LeanPlayground» where
  -- add library configuration options here

@[default_target]
lean_exe «hello» where
  root := `Main

require mathlib from git "https://github.com/leanprover-community/mathlib4"
