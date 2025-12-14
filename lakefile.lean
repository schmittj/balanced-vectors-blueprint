import Lake
open Lake DSL

package «balanced-vectors» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩
  ]

-- Using the exact mathlib commit where the code was developed
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "26fffffcccd7299b26cf63fac902165bc553fd56"

@[default_target]
lean_lib «BalancedVectors» where
  -- add library-specific options here
