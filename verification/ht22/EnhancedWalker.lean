import Lean

open Lean Elab Command Meta
namespace CoordinatorC001Graph

/- Deliberately independent of Expr.getUsedConstants and the bundled walker. -/
def expressionNames (expression : Expr) : Array Name := Id.run do
  let mut stack := #[expression]
  let mut visited : Std.HashSet Expr := {}
  let mut names : Std.HashSet Name := {}
  while !stack.isEmpty do
    let current := stack.back!
    stack := stack.pop
    if visited.contains current then continue
    visited := visited.insert current
    match current with
    | .const n _ => names := names.insert n
    | .proj n _ body => names := names.insert n; stack := stack.push body
    | .app f a => stack := (stack.push f).push a
    | .lam _ d b _ | .forallE _ d b _ => stack := (stack.push d).push b
    | .letE _ t v b _ => stack := ((stack.push t).push v).push b
    | .mdata _ body => stack := stack.push body
    | _ => pure ()
  return names.toArray.qsort (fun a b => a.toString < b.toString)

def recursorIndex (environment : Environment) : Std.HashMap Name (Array Name) := Id.run do
  let mut index : Std.HashMap Name (Array Name) := {}
  for (name,information) in environment.constants.toList do
    if let .recInfo v := information then
      for family in v.all do
        index := index.insert family ((index[family]?.getD #[]).push name)
  return index

def support (index : Std.HashMap Name (Array Name)) (information : ConstantInfo) : Array Name := Id.run do
  let mut result : Array Name := #[]
  match information with
  | .inductInfo v =>
    result := v.all.toArray ++ v.ctors.toArray
    for family in v.all do result := result ++ (index[family]?.getD #[])
  | .ctorInfo v => result := #[v.induct]
  | .recInfo v =>
    result := v.all.toArray
    for rule in v.rules do
      result := result.push rule.ctor ++ expressionNames rule.rhs
  | .quotInfo _ => result := #[`Quot, `Quot.mk, `Quot.ind, `Quot.lift]
  | _ => pure ()
  return result

def category : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

def strings (names : Array Name) : Json := toJson (names.map Name.toString)

def nameJson : Name → Json
  | .anonymous => Json.arr #[toJson "anonymous"]
  | .str p s => Json.arr #[toJson "str", nameJson p, toJson s]
  | .num p n => Json.arr #[toJson "num", nameJson p, toJson n]

def levelJson : Level → Json
  | .zero => Json.arr #[toJson "zero"]
  | .succ x => Json.arr #[toJson "succ", levelJson x]
  | .max x y => Json.arr #[toJson "max", levelJson x, levelJson y]
  | .imax x y => Json.arr #[toJson "imax", levelJson x, levelJson y]
  | .param n => Json.arr #[toJson "param", nameJson n]
  | .mvar n => Json.arr #[toJson "mvar", nameJson n.name]

def children : Expr → Array Expr
  | .app f a => #[f,a]
  | .lam _ d b _ | .forallE _ d b _ => #[d,b]
  | .letE _ t v b _ => #[t,v,b]
  | .mdata _ b | .proj _ _ b => #[b]
  | _ => #[]

/- This is a kernel-expression DAG, not an unshared repr tree. Each structurally
   equal node occurs once per expression. Kernel-irrelevant mdata contents are
   explicitly omitted; original .olean bytes are independently hashed. -/
def expressionDag (expression : Expr) : Json := Id.run do
  let mut stack := #[(expression,false)]
  let mut ids : Std.HashMap Expr Nat := {}
  let mut nodes : Array Json := #[]
  while !stack.isEmpty do
    let (current,ready) := stack.back!
    stack := stack.pop
    if ids.contains current then continue
    if !ready then
      stack := stack.push (current,true)
      for child in children current do
        if !ids.contains child then stack := stack.push (child,false)
      continue
    let childIds := (children current).map (fun e => toJson (ids.get! e))
    let node := match current with
      | .bvar n => Json.arr #[toJson "bvar",toJson n]
      | .fvar n => Json.arr #[toJson "fvar",nameJson n.name]
      | .mvar n => Json.arr #[toJson "mvar",nameJson n.name]
      | .sort l => Json.arr #[toJson "sort",levelJson l]
      | .const n ls => Json.arr #[toJson "const",nameJson n,toJson (ls.map levelJson)]
      | .app _ _ => Json.arr (#[toJson "app"]++childIds)
      | .lam n _ _ bi => Json.arr (#[toJson "lam",nameJson n,toJson (repr bi).pretty]++childIds)
      | .forallE n _ _ bi => Json.arr (#[toJson "forall",nameJson n,toJson (repr bi).pretty]++childIds)
      | .letE n _ _ _ nonDep => Json.arr (#[toJson "let",nameJson n,toJson nonDep]++childIds)
      | .lit (.natVal n) => Json.arr #[toJson "nat",toJson n]
      | .lit (.strVal s) => Json.arr #[toJson "string",toJson s]
      | .proj n i _ => Json.arr (#[toJson "proj",nameJson n,toJson i]++childIds)
      | .mdata _ _ => Json.arr (#[toJson "mdata-kernel-irrelevant-payload-erased"]++childIds)
    ids := ids.insert current nodes.size
    nodes := nodes.push node
  return Json.mkObj [("format",toJson "kernel-expr-dag-v1"),
    ("metadata_payload",toJson "erased; original proof objects separately byte-hashed"),
    ("root",toJson (ids.get! expression)),("nodes",Json.arr nodes)]

def graph (root : Name) (base : System.FilePath) : CommandElabM Unit := do
  let environment := (← getEnv).setExporting false
  let recursors := recursorIndex environment
  let edges ← liftIO <| IO.FS.Handle.mk (base.addExtension "graph.jsonl") .write
  let statements ← liftIO <| IO.FS.Handle.mk (base.addExtension "types.jsonl") .write
  let terms ← liftIO <| IO.FS.Handle.mk (base.addExtension "values.jsonl") .write
  let mut queue := #[root]
  let mut visited : Std.HashSet Name := {}
  let mut axioms : Array Name := #[]
  let mut missing : Array Name := #[]
  let mut unsafeOrPartial : Array Name := #[]
  let mut localCount := 0
  let mut index := 0
  while index < queue.size do
    let name := queue[index]!
    index := index+1
    if visited.contains name then continue
    visited := visited.insert name
    let some information := environment.checked.get.find? name
      | missing := missing.push name; continue
    let typeEdges := expressionNames information.type
    let value := information.value? (allowOpaque := true)
    let valueEdges := value.map expressionNames |>.getD #[]
    let structuralEdges := support recursors information
    let owner := match environment.getModuleIdxFor? name with
      | some number => environment.header.moduleNames[number.toNat]!.toString
      | none => "<current>"
    let record := Json.mkObj [
      ("name",toJson name.toString),("kind",toJson (category information)),
      ("module",toJson owner),("unsafe",toJson information.isUnsafe),
      ("partial",toJson information.isPartial),("has_stored_value",toJson value.isSome),
      ("type_edges",strings typeEdges),("value_edges",strings valueEdges),
      ("structural_edges",strings structuralEdges)]
    liftIO <| edges.putStrLn record.compress
    if information.isAxiom then axioms := axioms.push name
    if information.isUnsafe || information.isPartial then unsafeOrPartial := unsafeOrPartial.push name
    if owner.startsWith "IsingBulk" || name==root || name.toString.startsWith "C001Control" then
      localCount := localCount+1
      let printed ← liftTermElabM <| ppExpr information.type
      liftIO <| statements.putStrLn (Json.mkObj [
        ("name",toJson name.toString),("module",toJson owner),
        ("pretty_type",toJson printed.pretty),
        ("elaborated_expr_dag",expressionDag information.type),
        ("level_parameters",toJson (information.levelParams.map Name.toString))]).compress
      let rules : List Json := match information with
        | .recInfo v => v.rules.map (fun (rule : RecursorRule) => Json.mkObj [
            ("constructor",toJson rule.ctor.toString),
            ("rhs_dag",expressionDag rule.rhs)])
        | _ => []
      liftIO <| terms.putStrLn (Json.mkObj [
        ("name",toJson name.toString),("module",toJson owner),
        ("stored_value_dag",toJson (value.map expressionDag)),
        ("recursor_rules",toJson rules)]).compress
    queue := queue ++ typeEdges ++ valueEdges ++ structuralEdges
  liftIO <| edges.flush
  liftIO <| statements.flush
  liftIO <| terms.flush
  let summary := Json.mkObj [
    ("root",toJson root.toString),("reachable",toJson visited.size),
    ("axioms",strings axioms),("unsafe_or_partial",strings unsafeOrPartial),
    ("missing",strings missing),("local_types",toJson localCount),
    ("expression_extractor",toJson "independent explicit AST stack, including projection type names"),
    ("structural_closure",toJson "mutual families, every constructor, reverse family-owned recursors including nested recursors, all rules, quotient primitives"),
    ("stored_values_dumped",toJson true)]
  liftIO <| IO.FS.writeFile (base.addExtension "summary.json") (summary.pretty++"\n")
  logInfo summary.pretty

elab "coordinator_graph " target:ident " to " destination:str : command =>
  graph target.getId destination.getString

end CoordinatorC001Graph
