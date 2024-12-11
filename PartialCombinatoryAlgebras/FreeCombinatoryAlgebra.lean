import PartialCombinatoryAlgebras.Basic
import PartialCombinatoryAlgebras.PartialCombinatoryAlgebra

/-! # Free (total) combinatory algebra -/

namespace FreeCombinatoryAlgebra

/-- The underlying expressions fo the free combinatory algebra -/
inductive Expr where
| K : Expr
| S : Expr
| app : Expr → Expr → Expr

instance Expr.hasDot : HasDot Expr where dot := app

/-- Provable equality on the free combinatory algebra -/
inductive Expr.eq : Expr → Expr → Prop where
| refl : ∀ {a}, eq a a
| sym : ∀ {a b}, eq a b → eq b a
| trans : ∀ {a b c}, eq a b → eq b c → eq a c
| app : ∀ {a b c d}, eq a b → eq c d → eq (a ⬝ c) (b ⬝ d)
| K : ∀ {a b}, eq (app (app K a) b) a
| S : ∀ {a b c}, eq (app (app (app S a) b) c) (app (app a c) (app b c))

infix:40 " ≈ " => Expr.eq

/-- The carrier of the free total combinatory algebra -/
def carrier := Quot Expr.eq

/-- Convert an expression to a (defined) partial element of the carrier. -/
@[reducible]
def mk (e : Expr) : Part carrier := Part.some (Quot.mk Expr.eq e)

@[simp]
theorem df_mk (e : Expr) : (mk e) ⇓ := by trivial

/-- Given a function `f : Expr → α` that preserves provable equality,
    lift it to a function `∀ (u : Part carrier), u ⇓ → α. -/
def lift {α : Sort} (f : Expr → α) (h : ∀ a b, a ≈ b → f a = f b) (u : Part carrier) (hu : u ⇓) : α :=
  Quot.lift f h (u.get hu)

def eq_lift {α : Sort} (f : Expr → α) (h : ∀ a b, a ≈ b → f a = f b) (e : Expr) :
  lift f h (mk e) (df_mk e) = f e := by simp

/-- Given a function `f : Expr → Expr` that preserves provable equality,
    convert it to a function on the partial elements of the carrier. -/
def raise (f : Expr → Expr) (h : ∀ {a b}, a ≈ b → f a ≈ f b) (u : Part carrier) : Part carrier :=
  Part.bind u (Quot.lift (fun (e : Expr) => mk (f e)) (fun a b h' => by simp ; apply Quot.sound ; apply h h'))

theorem eq_raise (f : Expr → Expr) (h : ∀ {a b}, a ≈ b → f a ≈ f b) (e : Expr) :
  raise f h (mk e) = mk (f e) := by simp [raise]

/-- Given a function `f : Expr → Expr → Expr` that preserves provable equality,
    lift it to a function on the partial elements of the carrier. -/
def raise₂ (f : Expr → Expr → Expr) (h : ∀ {a b c d}, a ≈ b → c ≈ d → f a c ≈ f b d) (u v : Part carrier) : Part carrier :=
  Part.bind u (fun a =>
    Part.bind v (fun b =>
      Quot.lift₂
        (fun x y => mk (f x y))
        (fun a b₁ b₂ h' => by simp ; apply Quot.sound; apply h .refl h')
        (fun a₁ a₂ b h' => by simp ; apply Quot.sound; apply h h' .refl)
        a b
    )
  )

theorem eq_raise₂ (f : Expr → Expr → Expr) (h : ∀ {a b c d}, a ≈ b → c ≈ d → f a c ≈ f b d) (a b : Expr) :
  raise₂ f h (mk a) (mk b) = mk (f a b) := by simp [raise₂]

instance CAisApplicativeStructure : PartialApplication carrier where
  app := raise₂ Expr.app Expr.eq.app

@[simp]
theorem df_app (u v : Part carrier) : u ⇓ → v ⇓ → (u ⬝ v) ⇓ := by
  intros hu hv
  sorry

instance CAisPCA : PCA carrier where
  K := mk .K
  S := mk .S

  df_K₀ := by simp
  df_K₁ hu := by simp [hu]
  df_S₀ := by simp
  df_S₁ hu := by simp [hu]
  df_S₂ hu hv := by simp [hu, hv]

  eq_K u v hu hv := by sorry

  eq_S u v w _ _ _ := by sorry

end FreeCombinatoryAlgebra
