import Lake
open Lake DSL

package «oriented_percolation» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «OrientedPercolation» where
  globs := #[.submodules `OrientedPercolation]
