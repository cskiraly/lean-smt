import Smt

open Lean Elab Meta

namespace SmtTest.TrustCore

/-- The unsat core in the raw result `smt` with `cfg` sends for the goal `True`. -/
def coreOf (cfg : Smt.Config) (name : Name) : TermElabM (Array cvc5.Term) := do
  let ch ← Smt.initAsyncState name none false true false
  let goal ← mkFreshExprMVar (mkConst ``True)
  discard <| Smt.smt cfg goal.mvarId! #[]
  let mut core := none
  while let some (_, output) ← Std.CloseableChannel.tryRecv ch do
    if let .rawResult (.ok (.unsat _ uc)) := output then
      core := some uc
  Std.CloseableChannel.Sync.close ch
  let some uc := core
    | throwError "{name}: expected an unsat raw result"
  return uc

-- With `trust`, cvc5 is not asked for an unsat core, unless `extraSolverOptions` asks for one.
elab "#test_trust_core" : command => Command.liftTermElabM do
  let core ← coreOf { trust := true } `trust
  unless core.isEmpty do
    throwError "expected no unsat core with trust, got {core}"
  let core ← coreOf { trust := true, extraSolverOptions := [("produce-unsat-cores", "true")] }
    `trustWithCores
  if core.isEmpty then
    throwError "expected the unsat core extraSolverOptions asked for"

end SmtTest.TrustCore

#test_trust_core
