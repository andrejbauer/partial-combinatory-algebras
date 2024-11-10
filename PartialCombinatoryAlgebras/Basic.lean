import Mathlib.Data.Part

/-- A partial binary operation on a set. -/
class PartialApplication (A : Type*) where
  /-- partial application -/
  app : Part A → Part A → Part A

/-- a partial element is defined, with explicit carrier -/
notation:50 u:max " ⇓ " => Part.Dom u

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

namespace PCA

variable {A : Type*} [PCA A]

@[reducible]
def I : Part A := S ⬝ K ⬝ K

lemma defined_I : (I : Part A) ⇓ := by
  apply defined_S₂ <;> apply defined_K₀

lemma eq_I {u : Part A} : u ⇓ → I ⬝ u = u := by
  intro du
  simp [I, eq_S, eq_K, defined_K₀, defined_K₁, du]

end PCA

inductive Expr (Γ A : Type*) where
| K : Expr Γ A
| S : Expr Γ A
| elm : A → Expr Γ A
| var : Γ → Expr Γ A
| app : Expr Γ A → Expr Γ A → Expr Γ A

inductive Extend (Γ : Type*) where
| here : Extend Γ
| there : Γ → Extend Γ

def extend {Γ A : Type} (η : Γ → A) (a : A) : Extend Γ → A
| .here => a
| .there x => η x

namespace Expr

  /-- The evaluation of an expression with respect to a partial application
      and valuation of the variables. -/
  def eval {Γ A} [PCA A]: Expr Γ A → (Γ → A) → Part A
  | .K, _ => PCA.K
  | .S, _ => PCA.S
  | .elm a, _ => .some a
  | .var x, η => .some (η x)
  | .app e₁ e₂, η => (eval e₁ η) ⬝ (eval e₂ η)

  @[inherit_doc]
  notation " ⟦" e "⟧ " η => Expr.eval e η

  def defined {Γ A} [PCA A] (e : Expr Γ A) :=
    ∀ (η : Γ → A), (⟦ e ⟧ η) ⇓

  def abstr {Γ A} [PCA A] : Expr (Extend Γ) A → Expr Γ A
  | .K => .app .K .K
  | .S => .app .K .S
  | .elm a => .app (.K) (.elm a)
  | .var (.here) => .app (.app .S .K) .K
  | .var (.there x) => .app .K (.var x)
  | .app e₁ e₂ => .app (.app .S (abstr e₁)) (abstr e₂)

  lemma defined_abstr {Γ A} [PCA A] (e : Expr (Extend Γ) A) : defined (abstr e) := by
    intro η
    induction e
    case K => simp [eval, PCA.defined_K₁, PCA.defined_K₀]
    case S => simp [eval, PCA.defined_S₁, PCA.defined_K₁, PCA.defined_S₀]
    case elm => simp [eval, PCA.defined_K₁]
    case var x =>
      cases x
      case here => simp [eval, PCA.defined_S₂, PCA.defined_S₁, PCA.defined_K₀]
      case there => simp [eval, PCA.defined_K₁]
    case app e₁ e₂ ih₁ ih₂ => simp [eval, PCA.defined_S₂, ih₁, ih₂]

end Expr
