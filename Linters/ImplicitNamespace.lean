import Lean.Elab.Command
open   Lean Elab Command

/-!
# The "implicit namespace" linter

Original code written by Damiano Testa.

The "implicitNamespace" linter emits a warning when a declaration uses the "implicit namespace" feature, see explanation:
https://github.com/leanprover/lean4/issues/6855
-/

namespace Mathlib.Linter

/--
The "implicitNamespace" linter emits a warning when a declaration uses the "implicit namespace" feature.
-/
register_option linter.implicitNamespace : Bool := {
  defValue := true
  descr := "enable the implicitNamespace linter"
}

/-- Add string `a` at the start of the first component of the name `n`. -/
private partial def prepend (n : Name) (a : String := "_") : Name :=
  n.modifyBase fun
    | .anonymous => .str .anonymous a
    | .str .anonymous s => .str .anonymous (a ++ s)
    | .str p s => .str (prepend p a) s
    | .num p n => .num (.str p a) n

private def isMonolithic (n : Name) : Bool :=
  match n with
    | .anonymous => false
    | .str .anonymous _ => true
    | .str _ _ => false
    | .num _ _ => false

namespace ImplicitNamespace

@[inherit_doc Mathlib.Linter.linter.implicitNamespace]
def implicitNamespaceLinter : Linter where run := withSetOptionIn fun stx ↦ do
  unless Linter.getLinterValue linter.implicitNamespace (← getOptions) do
    return
  if (← get).messages.hasErrors then
    return
  -- do not test declarations of inductive types
  if ((stx.getArg 1).getArg 0).getAtomVal == "inductive" then
    return
  let some ID := stx.find? (·.isOfKind ``Parser.Command.declId) | return
  let newID := prepend ID[0].getId
  -- do not test declarations with "atomic" names
  if isMonolithic newID then
    return
  let stx' : Syntax := stx.replaceM (m := Id) fun s =>
    if s.getKind == ``Parser.Command.declId then
      some (s.modifyArg 0 (mkIdentFrom · newID))
    else
      none
  let oldState ← get
  let s ← getScope
  let (errors?, report) := ← do
    elabCommand stx'
    let msgs := (← get).messages
    let allErrors := (← msgs.reported.toArray.mapM (·.toString))
    let unknownId := allErrors.filterMap
      (if let [_, id] := ·.splitOn "unknown identifier" then some id.trim else none)
    return (msgs.hasErrors, unknownId)
  set oldState
  if errors? then
    for r in report do
      Linter.logLint linter.implicitNamespace ID
        m!"'{ID[0]}' exploits an implicit namespace for {r}.\n"
    if report.isEmpty then
      Linter.logLint linter.implicitNamespace ID
        m!"Possible unknown problem in '{ID[0]}'.\n"

initialize addLinter implicitNamespaceLinter

end ImplicitNamespace

end Mathlib.Linter
