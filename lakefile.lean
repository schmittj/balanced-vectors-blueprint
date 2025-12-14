import Lake
open Lake DSL

package «balanced-vectors» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.14.0"

-- Note: If you need the latest mathlib features, you can use:
-- require mathlib from git
--   "https://github.com/leanprover-community/mathlib4.git" @ "master"
-- and update lean-toolchain to match mathlib's version

@[default_target]
lean_lib «BalancedVectors» where
  -- add library-specific options here
