import Lake
open Lake DSL

package «B» where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    -- ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`pp.proofs.withType, false⟩,
    ⟨`autoImplicit, false⟩
  ]
  -- moreLinkArgs := #[
  --   "-L./.lake/packages/LeanCopilot/.lake/build/lib",
  --   "-lctranslate2"
  -- ]

  -- add any additional package configuration options here
require "leanprover-community" / "mathlib"
require ZFLean from git "https://github.com/VTrelat/ZFLean.git" @ s!"v{Lean.versionString}"

-- require LeanCopilot from git "https://github.com/lean-dojo/LeanCopilot.git" @ "main"

@[default_target]
lean_exe «BEer» where
  root := `Main

lean_lib «B»
lean_lib «SMT»
lean_lib «Extra»
lean_lib «POGReader»
lean_lib «Encoder»
-- lean_lib «ZFC»
lean_lib «CustomPrelude»
