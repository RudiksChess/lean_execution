import Lake
open Lake DSL

package thesis where
  -- add package configuration here

require Foundation from git
  "https://github.com/FormalizedFormalLogic/Foundation" @ "c28942b7d9d0df41ee5b736602c3f27b8643532c"
  -- Pinned for thesis reproducibility (Lean v4.29.0). Bump this hash + lean-toolchain together.

@[default_target]
lean_lib Thesis where
  roots := #[
    `Thesis
  ]
