open Lean Elab Command Meta
elab "publication_fields to " destination:str : command => do
  let env := (← getEnv).setExporting false
  let some info := env.checked.get.find? `IsingBulk.HT22.ht22_full_target | throwError "missing terminal"
  let some stored := info.value? (allowOpaque := true) | throwError "missing stored proof"
  let proof := stored.consumeMData
  unless proof.getAppFn.isConstOf `IsingBulk.HT22.HT22FullTarget.mk do
    throwError "Unexpected stored constructor"
  let fields := getStructureFields env `IsingBulk.HT22.HT22FullTarget
  let arguments := proof.getAppArgs
  unless fields.size == 14 && arguments.size == 14 do throwError "Field count changed"
  let file ← liftIO <| IO.FS.Handle.mk destination.getString .write
  for index in [:14] do
    let value := arguments[index]!
    let type ← liftTermElabM <| inferType value
    let printed ← liftTermElabM <| ppExpr type
    let record := Json.mkObj [
      ("field",toJson fields[index]!.toString),("constructor_index",toJson index),
      ("pretty_type",toJson printed.pretty),
      ("type_dag",CoordinatorC001Graph.expressionDag type),
      ("stored_proof_dag",CoordinatorC001Graph.expressionDag value),
      ("type_edges",CoordinatorC001Graph.strings (CoordinatorC001Graph.expressionNames type)),
      ("value_edges",CoordinatorC001Graph.strings (CoordinatorC001Graph.expressionNames value))]
    liftIO <| file.putStrLn record.compress
  liftIO <| file.flush
  logInfo "Reconstructed all fourteen actual stored constructor proofs and inferred their types"
