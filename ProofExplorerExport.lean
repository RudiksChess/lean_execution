import SubVerso.Compat
import SubVerso.Examples.Env
import SubVerso.Highlighting

open Lean Elab Frontend
open Lean.Elab.Command hiding Context
open SubVerso
open SubVerso.Highlighting

namespace ProofExplorerExport

structure Config where
  moduleName : Name
  declaration : String

def Config.fromArgs : List String → IO Config
  | [moduleName, declaration] => pure { moduleName := moduleName.toName, declaration }
  | _ => throw <| IO.userError
      "usage: lake exe proofExplorerExport MODULE DECLARATION"

def positionJson (p : Position) : Json :=
  Json.mkObj [("line", toJson p.line), ("column", toJson (p.column + 1))]

def rangeJson (fm : FileMap) (startPos endPos : SubVerso.Compat.String.Pos) : Json :=
  Json.mkObj [
    ("start", positionJson (fm.toPosition startPos)),
    ("end", positionJson (fm.toPosition endPos)),
    ("startByte", toJson startPos.byteIdx),
    ("endByte", toJson endPos.byteIdx)
  ]

def tokenText (tok : Token) : String :=
  (Highlighted.token tok).toString

def hypothesisJson (h : Highlighted.Hypothesis Highlighted) : Array Json :=
  h.names.map fun name => Json.mkObj [
    ("name", tokenText name),
    ("type", toJson h.typeAndVal.toString)
  ]

def goalJson (g : Highlighted.Goal Highlighted) : Json :=
  let fields : List (String × Json) := [
    ("hypotheses", .arr <| g.hypotheses.flatMap hypothesisJson),
    ("target", toJson g.conclusion.toString)
  ]
  Json.mkObj <| fields ++ match g.name with
    | none => []
    | some name => [("id", toJson name)]

def goalsJson (goals : Array (Highlighted.Goal Highlighted)) : Json :=
  .arr (goals.map goalJson)

def collectTactics (trees : Array InfoTree) : Array (ContextInfo × TacticInfo) :=
  (trees.toList.flatMap fun tree =>
    tree.collectNodesBottomUp fun ci info _ out =>
      if !info.isOriginal then out
      else match info with
        | .ofTacticInfo ti => (ci, ti) :: out
        | _ => out).toArray

def renderedGoals (ci : ContextInfo) (mctx : MetavarContext) (goals : List MVarId)
    (trees : PersistentArray InfoTree) : TermElabM (Array (Highlighted.Goal Highlighted)) :=
  highlightProofState {ci with mctx} goals trees

def tacticJson (fm : FileMap) (contents : String) (trees : PersistentArray InfoTree)
    (ci : ContextInfo) (ti : TacticInfo) : TermElabM (Option Json) := do
  let some ⟨startPos, endPos⟩ := ti.stx.getRange? (canonicalOnly := true)
    | return none
  if startPos.byteIdx = endPos.byteIdx then return none
  let before ← renderedGoals ci ti.mctxBefore ti.goalsBefore trees
  let after ← renderedGoals ci ti.mctxAfter ti.goalsAfter trees
  let sourceText := SubVerso.Compat.String.Pos.extract contents startPos endPos
  return some <| Json.mkObj [
    ("range", rangeJson fm startPos endPos),
    ("sourceText", toJson sourceText),
    ("syntaxKind", toJson (toString ti.stx.getKind)),
    ("before", goalsJson before),
    ("after", goalsJson after)
  ]

def extractCommand (declaration : String) (contents : String) (fm : FileMap)
    (res : SubVerso.Compat.Frontend.FrontendResult) (trees : PersistentArray InfoTree) :
    TermElabM Json := do
  let some item := res.items.find? fun item =>
      match item.commandSyntax.getRange? (canonicalOnly := true) with
      | none => false
      | some ⟨startPos, endPos⟩ =>
        let source := SubVerso.Compat.String.Pos.extract contents startPos endPos
        ["theorem ", "lemma ", "def "].any fun keyword =>
          [" ", "\n", ":"].any fun boundary => source.contains (keyword ++ declaration ++ boundary)
    | throwError "declaration '{declaration}' was not found in elaborated commands"
  let some ⟨declStart, declEnd⟩ := item.commandSyntax.getRange? (canonicalOnly := true)
    | throwError "declaration '{declaration}' has no canonical source range"
  let all := collectTactics item.info.toArray
  let mut steps := #[]
  for (ci, ti) in all do
    if let some json ← tacticJson fm contents trees ci ti then
      steps := steps.push json
  return Json.mkObj [
    ("declaration", toJson declaration),
    ("declarationRange", rangeJson fm declStart declEnd),
    ("code", SubVerso.Compat.String.Pos.extract contents declStart declEnd),
    ("tactics", .arr steps)
  ]

unsafe def extractModule (config : Config) : IO Json := do
  initSearchPath (← findSysroot)
  let srcPath ← SubVerso.Compat.initSrcSearchPath
  let searchPath : SearchPath := (srcPath : List System.FilePath) ++ [("." : System.FilePath)]
  let some fileName ← searchPath.findModuleWithExt "lean" config.moduleName
    | throw <| IO.userError s!"failed to locate module {config.moduleName}"
  let contents ← IO.FS.readFile fileName
  let fm := FileMap.ofString contents
  let inputContext := Parser.mkInputContext contents fileName.toString
  let (headerSyntax, parserState, messages) ← Parser.parseHeader inputContext
  let imports := headerToImports headerSyntax
  enableInitializersExecution
  let env ← SubVerso.Compat.importModules imports {}
  let parserContext : Frontend.Context := {inputCtx := inputContext}
  let commandState : Command.State := {
    env
    maxRecDepth := defaultMaxRecDepth
    messages
  }
  let commandRef ← IO.mkRef {commandState, parserState, cmdPos := parserState.pos}
  let result ← SubVerso.Compat.Frontend.processCommands headerSyntax parserContext commandRef
  let finalState ← commandRef.get
  if finalState.commandState.messages.hasErrors then
    throw <| IO.userError s!"elaboration of {config.moduleName} reported errors"
  let fullName := config.moduleName.getPrefix ++ config.declaration.toName
  if !finalState.commandState.env.contains fullName then
    throw <| IO.userError s!"elaboration did not define expected declaration {fullName}"
  let trees := finalState.commandState.infoState.trees
  let proof ← Frontend.runCommandElabM
    (liftTermElabM <| extractCommand config.declaration contents fm result trees)
    parserContext commandRef
  pure <| Json.mkObj [
    ("module", toJson (toString config.moduleName)),
    ("path", toJson fileName.toString),
    ("proof", proof)
  ]

unsafe def run (args : List String) : IO UInt32 := do
  try
    let config ← Config.fromArgs args
    IO.println (← extractModule config).pretty
    return 0
  catch e =>
    IO.eprintln s!"proof explorer export failed: {e}"
    return 1

end ProofExplorerExport

unsafe def main (args : List String) : IO UInt32 :=
  ProofExplorerExport.run args
