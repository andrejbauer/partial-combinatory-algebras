import Mathlib.Data.Part
import Mathlib.Data.Finset.Basic

/-!
# Partial combinatory algebras

A partial combinatory algebra is a set equipped with a partial binary operation,
which has the so-called combinators `K` and `S`. We formalize it in two stages.

We first defined the class `PartialApplication` which equips a given set `A` with
a partial binary operation. One might expect such an operation to have type
`A → A → Part A`, but this leads to complications because it is not composable.
So instead we specify that a partial operation is a map of type `Part A → Part A → Part A`
which is strict: if an application is defined then so are its arguments. In other
words, we *always* work with partial elements, and separately state that they are
total as necessary.

We then define the class `PCA` (partial combinatory algebra) to be an extension of
`PartialApplication`. It prescribed combinators `K` and `S` satisfying the usual properties.
Following our strategy, `K` and `S` are again partial elements on the carrier set,
with a separate claim that they are total.

-/

/-- A notation for definedness of a partial element (we find writing `x.Dom` a bit silly). -/
notation:50 u:max " ⇓ " => Part.Dom u

/-- A generic notation for a left-associative binary operation -/
class HasDot (A : Type*) where
  /-- (possibly partial) binary application -/
  dot : A → A → A

@[inherit_doc]
infixl:70 " ⬝ " => HasDot.dot

/-- A partial binary operation on a set. -/
class PartialApplication (A : Type*) where
  /-- Partial application -/
  app : Part A → Part A → Part A
  /-- Partial application is strict in the left argument -/
  strict_left : ∀ {u v : Part A}, (app u v) ⇓ → u ⇓
  /-- Partial application is strict in the right argument -/
  strict_right : ∀ {u v : Part A}, (app u v) ⇓ → v ⇓

instance PartialApplication.hasDot {A : Type*} [PartialApplication A] : HasDot (Part A) where
  dot := app

/-- The partial combinatory structure on a set `A`. -/
class PCA (A : Type*) extends PartialApplication A where
  K : Part A
  S : Part A
  defined_K₀ : K ⇓
  defined_K₁ : ∀ {u : Part A}, u ⇓ → (K ⬝ u) ⇓
  defined_S₀ : S ⇓
  defined_S₁ : ∀ {u : Part A}, u ⇓ → (S ⬝ u) ⇓
  defined_S₂ : ∀ {u v : Part A}, u ⇓ → v ⇓ → (S ⬝ u ⬝ v) ⇓
  eq_K : ∀ (u v : Part A), u ⇓ → v ⇓ → (K ⬝ u ⬝ v) = u
  eq_S : ∀ (u v w : Part A), u ⇓ → v ⇓ → w ⇓ → S ⬝ u ⬝ v ⬝ w = (u ⬝ w) ⬝ (v ⬝ w)

attribute [simp] PCA.defined_K₀
attribute [simp] PCA.defined_K₁
attribute [simp] PCA.eq_K
attribute [simp] PCA.defined_S₀
attribute [simp] PCA.defined_S₁
attribute [simp] PCA.defined_S₂
attribute [simp] PCA.eq_S

/-- Every PCA is inhabited. We pick K as its default element. -/
instance PCA.inhabited {A : Type*} [PCA A] : Inhabited A where
  default := K.get defined_K₀

/-! `Expr Γ A` is the type of expressions built inductively from
    constants `K` and `S`, variables in `Γ` (the variable context),
    the elements of a carrier set `A`, and formal binary application.

    The usual accounts of PCAs typically do not introduce `K` and `S`
    as separate constants, because a PCA `A` already contains such combinators.
    However, as we defined the combinators to be partial elements, it is more
    convenient to have separate primitive constants denoting them.
-/

/-- Expressions with variables from context `Γ` and elements from `A`. -/
inductive Expr (Γ A : Type*) where
  /-- Formal expression denoting the K combinator -/
| K : Expr Γ A
  /-- Formal expression denoting the S combinator -/
| S : Expr Γ A
  /-- An element as a formal expression -/
| elm : A → Expr Γ A
  /-- A variable as a formal expression -/
| var : Γ → Expr Γ A
  /-- Formal expression application -/
| app : Expr Γ A → Expr Γ A → Expr Γ A

instance Expr.hasDot {Γ A : Type*} : HasDot (Expr Γ A) where
  dot := Expr.app

namespace Expr
  universe u v
  variable {Γ : Type u} [DecidableEq Γ]
  variable {A : Type v} [PCA A]

  /-- Does a variable occur in an expression? -/
  @[reducible]
  def occurs (x : Γ) : Expr Γ A → Prop
  | K => False
  | S => False
  | elm _ => False
  | var y => y = x
  | app e₁ e₂ => occurs x e₁ ∨ occurs x e₂

  /-- Occurrence of a variable is decidable -/
  instance decide_occurs {x : Γ} (e : Expr Γ A) : Decidable (occurs x e) :=
    match e with
    | K => .isFalse not_false
    | S => .isFalse not_false
    | elm _ => .isFalse not_false
    | var y => decEq y x
    | app e₁ e₂ =>
      let _ := @decide_occurs x e₁
      let _ := @decide_occurs x e₂
      inferInstance

  /-- A valuation `η : Γ → A` assigning elements to variables,
      with the value of `x` overridden to be `a`. -/
  @[reducible]
  def override (x : Γ) (a : A) (η : Γ → A) (y : Γ) : A :=
    if y = x then a else η y

  /-- Evaluate an expression with respect to a given valuation `η`. -/
  def eval (η : Γ → A): Expr Γ A → Part A
  | .K => PCA.K
  | .S => PCA.S
  | .elm a => .some a
  | .var x => .some (η x)
  | .app e₁ e₂ => (eval η e₁) ⬝ (eval η e₂)

  /-- An expression is said to be defined when it is defined at every valuation. -/
  def defined (e : Expr Γ A) := ∀ (η : Γ → A), (eval η e) ⇓

  /-- The substitution of an element for the extra variable. -/
  def subst (x : Γ) (a : A) : Expr Γ A → Expr Γ A
  | K => K
  | S => S
  | elm b => elm b
  | var y => if y = x then elm a else var y
  | app e₁ e₂ => (subst x a e₁) ⬝ (subst x a e₂)

  /-- `abstr e` is an expression with one fewer variables than
      the expression `e`, which works similarly to function
      abastraction in the λ-calculus. It is at the heart of
      combinatory completeness. -/
  def abstr (x : Γ): Expr Γ A → Expr Γ A
  | K => K ⬝ K
  | S => K ⬝ S
  | elm a => K ⬝ elm a
  | var y => if y = x then S ⬝ K ⬝ K else K ⬝ var y
  | app e₁ e₂ => S ⬝ (abstr x e₁) ⬝ (abstr x e₂)

  /-- An abstraction is defined. -/
  lemma defined_abstr (x : Γ) (e : Expr Γ A) : defined (abstr x e) := by
    intro η
    induction e
    case K => simp [eval]
    case S => simp [eval]
    case elm => simp [eval]
    case var y =>
      cases (decEq y x)
      case isFalse h => simp [abstr, eval, h]
      case isTrue h => simp [abstr, eval, h]
    case app e₁ e₂ ih₁ ih₂ => simp [eval, ih₁, ih₂]

  /-- `abstr e` behaves like abstraction in the extra variable.
      This is known as *combinatory completeness*. -/
  lemma eq_abstr (x : Γ) (e : Expr Γ A) (a : A) (η : Γ → A):
    eval η (abstr x e ⬝ elm a) = eval (override x a η) e := by
    induction e
    case K => simp [eval]
    case S => simp [eval]
    case elm => simp [eval]
    case var y =>
      cases (decEq y x)
      case isFalse h => simp [eval, abstr, override, h]
      case isTrue h => simp [eval, abstr, override, h]
    case app e₁ e₂ ih₁ ih₂ =>
      simp [abstr, eval] at ih₁
      simp [abstr, eval] at ih₂
      simp [abstr, eval, defined_abstr x _ η, ih₁, ih₂]

  lemma eval_abstr_app (η : Γ → A) (x : Γ) (e : Expr Γ A) (u : Part A) (hu : u ⇓) :
    eval η (abstr x e) ⬝ u = eval (override x (u.get hu) η) e := by
    calc
     _ = eval η (abstr x e ⬝ elm (u.get hu)) := by simp [eval]
     _ = eval (override x (u.get hu) η) e := by apply eq_abstr

  /-- Compile an expression to a partial element, substituting
      the default value for any variables occurring in e. -/
  @[simp]
  def compile (e : Expr Γ A) : Part A :=
    eval (fun _ => default) e

end Expr
