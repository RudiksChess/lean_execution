import SubVerso.Compat
import SubVerso.Examples.Env
import SubVerso.Highlighting

/-!
Adaptador del explorador para los capítulos teóricos (`Thesis/Teoria`).

Es un ejecutable independiente de `ProofExplorerExport.lean`, cuyo hash está
fijado en `artifacts/explorer/proofs.json`; por eso no comparte código con él.
Diferencias:

* recibe un módulo y una lista de nombres completos, y elabora el módulo una
  sola vez;
* localiza cada declaración por los rangos que registra Lean
  (`findDeclarationRanges?`), no por coincidencia de texto, de modo que admite
  espacios de nombres anidados (`Cubo.LambdaOmega.…`, `Cadena.…`);
* si el cuerpo del teorema es un término (no empieza con `by`), exporta además
  el contexto local y el tipo esperado que el elaborador registró para ese
  término (`TermInfo`). No se escribe ningún estado a mano.
-/

open Lean Elab Frontend
open Lean.Elab.Command hiding Context
open SubVerso
open SubVerso.Highlighting

namespace ProofExplorerTheoryExport

structure Config where
  moduleName : Name
  declarations : List Name

def Config.fromArgs : List String → IO Config
  | moduleName :: d :: ds =>
    pure { moduleName := moduleName.toName, declarations := (d :: ds).map String.toName }
  | _ => throw <| IO.userError
      "usage: lake exe proofExplorerTheoryExport MODULE FULL_DECLARATION_NAME..."

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

def collectTerms (trees : Array InfoTree) : Array (ContextInfo × TermInfo) :=
  (trees.toList.flatMap fun tree =>
    tree.collectNodesBottomUp fun ci info _ out =>
      match info with
        | .ofTermInfo ti => (ci, ti) :: out
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

/-- El término que sigue a `:=` en `theorem … := t`, si la declaración tiene esa forma. -/
def bodyTerm? (command : Syntax) : Option Syntax := do
  guard (command.getKind == ``Lean.Parser.Command.declaration)
  let decl := command[1]
  guard (decl.getKind == ``Lean.Parser.Command.theorem)
  let val := decl[3]
  guard (val.getKind == ``Lean.Parser.Command.declValSimple)
  pure val[1]

/-- Estado del cuerpo en modo término: contexto local y tipo esperado que el
elaborador registró en el `TermInfo` de ese término. -/
def termJson (fm : FileMap) (contents : String) (trees : PersistentArray InfoTree)
    (terms : Array (ContextInfo × TermInfo)) (body : Syntax) : TermElabM Json := do
  let some ⟨startPos, endPos⟩ := body.getRange?
    | throwError "term body has no source range"
  let matching := terms.filterMap fun (ci, ti) =>
    match ti.stx.getRange?, ti.expectedType? with
    | some ⟨s, e⟩, some ty =>
      if s.byteIdx = startPos.byteIdx ∧ e.byteIdx = endPos.byteIdx then some (ci, ti, ty) else none
    | _, _ => none
  -- `collectNodesBottomUp` lista primero el nodo más externo de cada árbol.
  let some (ci, ti, ty) := matching[0]?
    | throwError "the elaborator recorded no expected type for the term body"
  let (goal, mctx) ← ci.runMetaM ti.lctx do
    let ty ← instantiateMVars ty
    let goal ← Meta.mkFreshExprSyntheticOpaqueMVar ty
    pure (goal.mvarId!, ← getMCtx)
  let before ← renderedGoals ci mctx [goal] trees
  return Json.mkObj [
    ("range", rangeJson fm startPos endPos),
    ("sourceText", toJson (SubVerso.Compat.String.Pos.extract contents startPos endPos)),
    ("syntaxKind", toJson (toString body.getKind)),
    ("before", goalsJson before)
  ]

def positionLe (a b : Position) : Bool :=
  a.line < b.line || (a.line == b.line && a.column ≤ b.column)

def extractCommand (declaration : Name) (contents : String) (fm : FileMap)
    (res : SubVerso.Compat.Frontend.FrontendResult) (trees : PersistentArray InfoTree) :
    TermElabM Json := do
  let some ranges ← findDeclarationRanges? declaration
    | throwError "declaration '{declaration}' has no recorded source range"
  let namePos := ranges.selectionRange.pos
  let some item := res.items.find? fun item =>
      match item.commandSyntax.getRange? (canonicalOnly := true) with
      | none => false
      | some ⟨startPos, endPos⟩ =>
        positionLe (fm.toPosition startPos) namePos && positionLe namePos (fm.toPosition endPos)
    | throwError "declaration '{declaration}' was not found in elaborated commands"
  let some ⟨declStart, declEnd⟩ := item.commandSyntax.getRange? (canonicalOnly := true)
    | throwError "declaration '{declaration}' has no canonical source range"
  let infoTrees := item.info.toArray
  let mut steps := #[]
  for (ci, ti) in collectTactics infoTrees do
    if let some json ← tacticJson fm contents trees ci ti then
      steps := steps.push json
  let term ← match bodyTerm? item.commandSyntax with
    | none => pure Json.null
    | some body =>
      if body.getKind == ``Lean.Parser.Term.byTactic then pure Json.null
      else termJson fm contents trees (collectTerms infoTrees) body
  return Json.mkObj [
    ("declaration", toJson (toString declaration)),
    ("declarationRange", rangeJson fm declStart declEnd),
    ("code", SubVerso.Compat.String.Pos.extract contents declStart declEnd),
    ("tactics", .arr steps),
    ("term", term)
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
  for declaration in config.declarations do
    if !finalState.commandState.env.contains declaration then
      throw <| IO.userError s!"elaboration did not define expected declaration {declaration}"
  let trees := finalState.commandState.infoState.trees
  let proofs ← Frontend.runCommandElabM
    (liftTermElabM <| config.declarations.toArray.mapM fun declaration =>
      extractCommand declaration contents fm result trees)
    parserContext commandRef
  pure <| Json.mkObj [
    ("module", toJson (toString config.moduleName)),
    ("path", toJson fileName.toString),
    ("proofs", .arr proofs)
  ]

unsafe def run (args : List String) : IO UInt32 := do
  try
    let config ← Config.fromArgs args
    IO.println (← extractModule config).pretty
    return 0
  catch e =>
    IO.eprintln s!"proof explorer theory export failed: {e}"
    return 1

end ProofExplorerTheoryExport

unsafe def main (args : List String) : IO UInt32 :=
  ProofExplorerTheoryExport.run args
