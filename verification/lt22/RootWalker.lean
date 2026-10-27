import Lean
open Lean Elab Command Meta
namespace IndependentRootAudit

def kind (c : ConstantInfo) : String :=
  match c with
  | .axiomInfo _ => "axiom" | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem" | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient" | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor" | .recInfo _ => "recursor"

def structural (c : ConstantInfo) : Array Name := Id.run do
  let mut a := #[]
  match c with
  | .inductInfo v => a := v.all.toArray ++ v.ctors.toArray
  | .ctorInfo v => a := #[v.induct]
  | .recInfo v =>
    a := v.all.toArray
    for rule in v.rules do
      a := a.push rule.ctor ++ rule.rhs.getUsedConstants
  | _ => pure ()
  return a

def namesJson (ns : Array Name) : Json := toJson (ns.map Name.toString)

def walk (root : Name) (outBase : System.FilePath) : CommandElabM Unit := do
  let env := (← getEnv).setExporting false
  let mut queue := #[root]
  let mut seen : NameSet := {}
  let mut rows : Array String := #[]
  let mut localTypes : Array String := #[]
  let mut axioms : Array Name := #[]
  let mut bad : Array Name := #[]
  let mut missing : Array Name := #[]
  let mut i := 0
  while i < queue.size do
    let n := queue[i]!
    i := i+1
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := env.checked.get.find? n | missing := missing.push n; continue
    let types := ci.type.getUsedConstants
    let values := (ci.value? true).map Expr.getUsedConstants |>.getD #[]
    let support := structural ci
    let moduleName := match env.getModuleIdxFor? n with
      | some idx => env.header.moduleNames[idx.toNat]!.toString
      | none => "<current>"
    let row := Json.mkObj [
      ("name",toJson n.toString),("kind",toJson (kind ci)),
      ("module",toJson moduleName),("unsafe",toJson ci.isUnsafe),
      ("partial",toJson ci.isPartial),("has_stored_value",toJson (ci.value? true).isSome),
      ("type_edges",namesJson types),("value_edges",namesJson values),
      ("structural_edges",namesJson support)]
    rows := rows.push row.compress
    if ci.isAxiom then axioms := axioms.push n
    if ci.isUnsafe || ci.isPartial then bad := bad.push n
    if moduleName.startsWith "IsingBulk" || n.toString.startsWith "AuditSentinel" || n==root then
      let pp ← liftTermElabM <| ppExpr ci.type
      localTypes := localTypes.push (Json.mkObj [
        ("name",toJson n.toString),("module",toJson moduleName),
        ("pretty_type",toJson pp.pretty),("elaborated_expr",toJson (repr ci.type).pretty),
        ("level_parameters",toJson (ci.levelParams.map Name.toString))]).compress
    queue := queue ++ types ++ values ++ support
  liftIO <| IO.FS.writeFile (outBase.addExtension "graph.jsonl") (String.intercalate "\n" rows.toList ++ "\n")
  liftIO <| IO.FS.writeFile (outBase.addExtension "types.jsonl") (String.intercalate "\n" localTypes.toList ++ "\n")
  let summary := Json.mkObj [("root",toJson root.toString),("reachable",toJson seen.size),
    ("axioms",namesJson axioms),("unsafe_or_partial",namesJson bad),("missing",namesJson missing),
    ("local_types",toJson localTypes.size)]
  liftIO <| IO.FS.writeFile (outBase.addExtension "summary.json") (summary.pretty ++ "\n")
  logInfo summary.pretty

elab "audit_graph " n:ident " to " path:str : command =>
  walk n.getId path.getString
end IndependentRootAudit
