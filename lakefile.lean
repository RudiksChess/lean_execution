import Lake
open Lake DSL

package thesis where
  -- add package configuration here

require Foundation from git
  "https://github.com/FormalizedFormalLogic/Foundation" @ "c28942b7d9d0df41ee5b736602c3f27b8643532c"
  -- Pinned for thesis reproducibility (Lean v4.29.0). Bump this hash + lean-toolchain together.

require subverso from git
  "https://github.com/leanprover/subverso.git" @ "52b9dfbd2658408e37ae6e8b72601ddeaaa25a0c"
  -- Pinned to SubVerso's Lean 4.29.0-compatible release for reproducible explorer exports.

@[default_target]
lean_lib Thesis where
  roots := #[
    `Thesis
  ]

lean_exe proofExplorerExport where
  root := `ProofExplorerExport
  supportInterpreter := true

-- Adaptador separado para Thesis/Teoria: el hash de ProofExplorerExport.lean
-- está fijado en artifacts/explorer/proofs.json y no debe cambiar.
lean_exe proofExplorerTheoryExport where
  root := `ProofExplorerTheoryExport
  supportInterpreter := true
