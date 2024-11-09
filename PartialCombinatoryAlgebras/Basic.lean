import Mathlib.Data.Part

/-- A partial binary operation on a set. -/
class PartialApplication (A : Type*) where
  /-- partial binary application -/
  app : A → A → Part A

@[inherit_doc]
infixr:30 "•" => PartialApplication.app

/-- When a set is equipped with a partial application, we allow implicit
    coercions from the set to its partial elements. -/
instance PartialApplication.hasCoe {A} [PartialApplication A]: Coe A (Part A) where
  coe := Part.some

/-- Monadic application that can be used for expressions with nested applications. -/
@[reducible]
def PartialApplication.mul {A} [PartialApplication A] (a b : Part A) : Part A :=
  Part.bind a (fun u => Part.bind b (fun v => app u v))

instance PartialApplication.hasMul {A} [PartialApplication A]: Mul (Part A) where
  mul := mul

/-- Applicative expressions over a context of variables `Γ` and constants `A`. -/
inductive Expr (Γ : Type*) (A : Type*) where
  /-- An element as an expression -/
| elm : A → Expr Γ A
  /-- A variable as an expression -/
| var : Γ → Expr Γ A
  /-- Formal application of expressions -/
| app : Expr Γ A → Expr Γ A → Expr Γ A

instance Expr.hasMul {Γ A} : Mul (Expr Γ A) where mul := Expr.app

/-- Applicative expressions equipped with the partial application operation `Expr.app`,
    which happens to be total. -/
instance Expr.partialApplication {Γ A : Type*} : PartialApplication (Expr Γ A) where
  app e₁ e₂ := e₁.app e₂

section Expressions

variable {A : Type*} [PartialApplication A]
variable {Γ : Type*}

/-- The evaluation of an expression with respect to a partial application
    and valuation of the variables. -/
def Expr.eval : Expr Γ A → (Γ → A) → Part A
| .elm a, _ => a
| .var x, η => η x
| .app e₁ e₂, η => do
  let v₁ ← eval e₁ η
  let v₂ ← eval e₂ η
  v₁ • v₂

@[inherit_doc]
notation " ⟦" e "⟧ " η => Expr.eval e η

/-- The statement that an expression is defined for the given valuation. -/
def Expr.defined (e : Expr Γ A) (η : Γ → A) := (⟦ e ⟧ η).Dom

@[inherit_doc]
notation:40 e:40 "↓" η:40 => Expr.defined e η

/-- The statement that an expression is undefined for the given valuation. -/
def Expr.undefined (e : Expr Γ A) (η : Γ → A) := ¬ (⟦ e ⟧ η).Dom

@[inherit_doc]
notation e "↑" η:40 => Expr.undefined e η

/-- The left-hand argument of an application is defined if the application is defined. -/
theorem Expr.defined_left {e₁ e₂ : Expr Γ A} {η : Γ → A} : (e₁.app e₂) ↓ η → e₁ ↓ η := by
  rintro ⟨_, _⟩
  assumption

/-- The right-hand argument of an application is defined if the application is defined. -/
theorem Expr.defined_right {e₁ e₂ : Expr Γ A} {η : Γ → A} : (.app e₁ e₂) ↓ η → (e₂ ↓ η) := by
  rintro ⟨_, ⟨_, _⟩⟩
  assumption

end Expressions

/-- The partial combinatory structure on a set `A`. -/
class PCA (A : Type*) extends PartialApplication A where
  K : A
  S : A
  defined_K₁ : ∀ a, (K • a).Dom
  defined_S₁ : ∀ a, (S • a).Dom
  defined_S₂ : ∀ a b, ((S • a).get (defined_S₁ a) • b).Dom
  eq_K : ∀ (a b : A), (K : Part A) * a * b = a
  eq_S : ∀ (a b c : A), (S : Part A) * a * b * c = (a * b) * (a * c)

notation "𝕜" => Part.some PCA.K
notation "𝕤" => Part.some PCA.S

namespace PCA

variable {A : Type*} [PCA A]

lemma definedS (a b : A) : (𝕤 * (a : Part A) * (b : Part A)).Dom := by
  simp [HMul.hMul, Mul.mul, Part.bind_dom]
  use (defined_S₁ a)
  use (defined_S₂ a b)

lemma definedK1 (a : A) : (𝕜 * (a : Part A)).Dom := by
  simp [HMul.hMul, Mul.mul, Part.bind_dom]
  use (defined_K₁ a)

def id : A := (𝕤 * 𝕜 * 𝕜 : Part A).get (definedS _ _)

end PCA
