import Lean.Elab.Command
open Lean Elab Command

/-!
# The "implicit namespace" linter

Original code written by Damiano Testa.

The "implicitNamespace" linter emits a warning when a declaration uses the "implicit namespace" feature, see explanation:
https://github.com/leanprover/lean4/issues/6855

Note that the linter has some false positives, notably, when `set_option` is called before a declaration containing `.`.
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
  let some ID := stx.find? (·.isOfKind ``Parser.Command.declId) | return
  let stx' : Syntax := stx.replaceM (m := Id) fun s =>
    if s.getKind == ``Parser.Command.declId then
      some (s.modifyArg 0 (fun i => mkIdentFrom i (prepend i.getId)))
    else
      none
  let newID := ((stx'.find? (·.isOfKind ``Parser.Command.declId)).getD default)[0]
  -- do not test declarations with "atomic" names
  if isMonolithic newID.getId then
    return
  -- do not test declarations of inductive types
  if ((stx'.getArg 1).getArg 0).getAtomVal == "inductive" then
    return
  let oldState ← get
  let s ← getScope
  let (errors?, report) ←
    withScope (fun _ =>
      {(default : Scope) with
          header := s.header
          -- Omitting `opts` seems to be fixing some issues.  It may cause other issues, though.
          currNamespace := s.currNamespace
          openDecls := s.openDecls
          levelNames := s.levelNames
          varDecls := s.varDecls
          varUIds := s.varUIds
          includedVars := s.includedVars
          omittedVars := s.omittedVars
          isNoncomputable := s.isNoncomputable
        }) do
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
        m!"'{ID[0]}' uses the implicit namespace '{ID[0].getId.getRoot}' for {r}.\n"
    if report.isEmpty then
      Linter.logLint linter.implicitNamespace ID
        m!"Unknown error in '{ID[0]}', possibly an implicit namespace '{ID[0].getId.getRoot}'.\n"

initialize addLinter implicitNamespaceLinter

end ImplicitNamespace

end Mathlib.Linter
