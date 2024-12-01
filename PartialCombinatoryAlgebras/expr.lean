import Mathlib.Control.Basic
import Qq

/-- An inductive type of expressions with variables ranging over type `V`. -/
inductive Expr where
  /-- Numeric constant -/
| num : Nat → Expr
  /-- Variable -/
| var : String → Expr
  /-- Addition -/
| plus : Expr → Expr → Expr

/-- Evaluate a closed expression and either return
    `inr n` where `n` is its value, or `inl x` is variable
    `x` is encoutnered. -/
def eval_closed : Expr → Sum String Nat
| .num k => return k
| .var x => .inl x
| .plus e₁ e₂ =>
  do
    let n₁ ← eval_closed e₁
    let n₂ ← eval_closed e₂
    return (n₁ + n₂)

#eval eval_closed (.plus (.num 4) (.num 5)) -- .inr 9

#eval eval_closed (.plus (.num 4) (.var "x")) -- .inl "x"

open Qq

elab "⟦" x:term "⟧" : term => do
  let e ← unsafe Lean.Elab.Term.evalTerm Expr q(Expr) x
  match eval_closed e with
  | .inr n => return q($n)
  | .inl x => throwError "{x} occurs"

open Expr
#check ⟦ plus (num 3) (num 5) ⟧ -- this is elaborated to 8
#check_failure ⟦ plus (num 3) (var "x") ⟧ -- this reports an error: "x occurs"

declare_syntax_cat cow
syntax "moo" ident : cow
syntax "[bovine:" cow "]" : term

macro_rules
| `([bovine: moo $x]) => `($x.getId) -- STRUGGLING HERE

#check [bovine: moo x] -- Should produce x as a name or a string
