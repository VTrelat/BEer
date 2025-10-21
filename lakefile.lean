import Lake
open Lake DSL

package «B» where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    -- ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`pp.proofs.withType, false⟩,
    ⟨`autoImplicit, false⟩
  ]
  -- add any additional package configuration options here

-- require batteries from git "https://github.com/leanprover-community/batteries" @ s!"v4.20.0"

-- require LeanSearchClient from git "https://github.com/leanprover-community/LeanSearchClient" @ "v4.12.0"
-- require "leanprover-community" / "mathlib" @ git "VT_ZFC_extension_rat"
require "leanprover-community" / "mathlib" @ git s!"v{Lean.versionString}"

@[default_target]
lean_exe «BEer» where
  root := `Main

lean_lib «B»
lean_lib «SMT»
lean_lib «Extra»
lean_lib «POGReader»
lean_lib «Encoder»
lean_lib «ZFC»
lean_lib «CustomPrelude»
