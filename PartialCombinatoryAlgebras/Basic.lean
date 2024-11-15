import Mathlib.Data.Part

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

/-- A partial binary operation on a set. -/
class PartialApplication (A : Type*) where
  /-- Partial application -/
  app : Part A → Part A → Part A
  /-- Partial application is strict in the left argument -/
  strict_left : ∀ {u v : Part A}, (app u v) ⇓ → u ⇓
  /-- Partial application is strict in the right argument -/
  strict_right : ∀ {u v : Part A}, (app u v) ⇓ → v ⇓

@[inherit_doc]
infixl:70 (priority := high) " ⬝ " => PartialApplication.app

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
| K : Expr Γ A
| S : Expr Γ A
| elm : A → Expr Γ A
| var : Γ → Expr Γ A
| app : Expr Γ A → Expr Γ A → Expr Γ A

namespace Expr
  /-- A set `Γ` (of variables) extended by one more variable. -/
  inductive Extend (Γ : Type*) where
    /-- The additional variable. -/
  | here : Extend Γ
    /-- The original variable -/
  | there : Γ → Extend Γ

  /-- A valuation `η : Γ → A` assigning elements to variables,
      extended by one more variable and its value. -/
  def extend {Γ A : Type} (η : Γ → A) (a : A) : Extend Γ → A
  | .here => a
  | .there x => η x

  /-- Evaluate an expression with respect to a given valuation `η`. -/
  def eval {Γ A} [PCA A] (η : Γ → A): Expr Γ A → Part A
  | .K => PCA.K
  | .S => PCA.S
  | .elm a => .some a
  | .var x => .some (η x)
  | .app e₁ e₂ => (eval η e₁) ⬝ (eval η e₂)

  /-- An expression is said to be defined when it is defined at every valuation. -/
  def defined {Γ A} [PCA A] (e : Expr Γ A) :=
    ∀ (η : Γ → A), (eval η e) ⇓

  /-- The substitution of an element for the extra variable. -/
  def subst {Γ A} [PCA A] (a : A) : Expr (Extend Γ) A → Expr Γ A
  | .K => .K
  | .S => .S
  | .elm b => .elm b
  | .var .here => .elm a
  | .var (.there x) => .var x
  | .app e₁ e₂ => .app (subst a e₁) (subst a e₂)

  /-- `abstr e` is an expression with one fewer variables than
      the expression `e`, which works similarly to function
      abastraction in the λ-calculus. It is at the heart of
      combinatory completeness. -/
  def abstr {Γ A} [PCA A] : Expr (Extend Γ) A → Expr Γ A
  | .K => .app .K .K
  | .S => .app .K .S
  | .elm a => .app (.K) (.elm a)
  | .var .here => .app (.app .S .K) .K
  | .var (.there x) => .app .K (.var x)
  | .app e₁ e₂ => .app (.app .S (abstr e₁)) (abstr e₂)

  /-- An abstraction is defined. -/
  lemma defined_abstr {Γ A} [PCA A] (e : Expr (Extend Γ) A) : defined (abstr e) := by
    intro η
    induction e
    case K => simp [eval]
    case S => simp [eval]
    case elm => simp [eval]
    case var x => cases x <;> simp [eval]
    case app e₁ e₂ ih₁ ih₂ => simp [eval, ih₁, ih₂]

  /-- Evaluating after substitution is equivalent to evaluating at
      and extended valuation. -/
  lemma eval_subst {Γ A} [PCA A] (e : Expr (Extend Γ) A) :
    ∀ (a : A) (η : Γ → A), eval η (subst a e) = eval (extend η a) e := by
    intro a η
    induction e
    case K => simp [subst, eval]
    case S => simp [subst, eval]
    case elm => simp [subst, eval]
    case var x =>
      cases x <;> simp [subst, eval, extend]
    case app e₁ e₂ ih₁ ih₂ => simp [subst, eval, ih₁, ih₂]

  /-- `abstr e` behaves like abstraction in the extra variable.
      This is known as *combinatory completeness* -/
  lemma eq_abstr {Γ A} [PCA A] (e : Expr (Extend Γ) A) (a : A) (η : Γ → A):
    eval η (.app (abstr e) (.elm a)) = eval (extend η a) e := by
    induction e
    case K => simp [eval]
    case S => simp [eval]
    case elm => simp [eval]
    case var x =>
      cases x <;> simp [eval, extend]
    case app e₁ e₂ ih₁ ih₂ =>
      simp [abstr, eval] at ih₁
      simp [abstr, eval] at ih₂
      simp [abstr, eval, defined_abstr _ η, ih₁, ih₂]
end Expr
