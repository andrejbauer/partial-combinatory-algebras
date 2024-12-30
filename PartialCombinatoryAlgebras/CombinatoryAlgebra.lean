import Mathlib.Tactic.NthRewrite
import Mathlib.Data.Part
import PartialCombinatoryAlgebras.Basic
import PartialCombinatoryAlgebras.PartialCombinatoryAlgebra

/-- A (total) combinatory structure on a set `A`. -/
class CA (A : Type*) extends HasDot A where
  K : A
  S : A
  eq_K : ∀ {a b : A}, K ⬝ a ⬝ b = a
  eq_S : ∀ {a b c : A}, S ⬝ a ⬝ b ⬝ c = (a ⬝ c) ⬝ (b ⬝ c)

/-- Missing from `Part` -/
@[simps]
def Part.map₂ {α β γ : Type*} (f : α → β → γ) (u : Part α) (v : Part β) : Part γ :=
  ⟨u.Dom ∧ v.Dom, fun p => f (u.get (And.left p)) (v.get (And.right p))⟩

@[simp]
lemma Part.eq_map₂_some {α β γ : Type*} (f : α → β → γ) (a : α) (b : β) :
  Part.map₂ f (.some a) (.some b) = .some (f a b) := by
  ext c
  simp [map₂]
  constructor <;> apply Eq.symm

namespace CA

  /-- A total application induces a partial application -/
  @[reducible]
  instance partialApp {A : Type} [d : HasDot A] : PartialApplication A where
    app := Part.map₂ d.dot

  lemma eq_app {A : Type} [HasDot A] {u v : Part A} (hu : u ⇓) (hv : v ⇓):
    u ⬝ v = .some (u.get hu ⬝ v.get hv) := by
    nth_rewrite 1 [←Part.some_get hu]
    nth_rewrite 1 [←Part.some_get hv]
    apply Part.eq_map₂_some

  /-- A combinatory algebra is a PCA -/
  instance isPCA {A : Type} [CA A] : PCA A where
    K := .some K
    S := .some S
    df_K₀ := by trivial
    df_K₁ := by intros ; trivial
    eq_K := by intro _ _ hu hv ; simp [CA.eq_app, hu, hv, CA.eq_K]
    df_S₀ := by trivial
    df_S₁ := by intros ; trivial
    df_S₂ := by intros ; trivial
    eq_S := by intro _ _ _ hu hv hw ; simp [CA.eq_app, hu, hv, hw, CA.eq_S]

  end CA
