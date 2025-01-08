import Lake
open Lake DSL

package «dlcf» where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]
  -- add any additional package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.15.0"

require discretion from git
  "https://github.com/imbrem/discretion.git" @ "main"

@[default_target]
lean_lib «DLCF» where
  -- add any library configuration options here
