import PartialCombinatoryAlgebras.Basic
import PartialCombinatoryAlgebras.CombinatoryAlgebra

/-! We show that a pairing function `A × A → A` on a set `A` induces
    a combinatory algebra structure on the power set of `A`.
-/

class Pairing (α : Type) where
  /-- Concatenation of an element and a list -/
  pair : α → α → α
  /-- The head of a list -/
  fst : α → α
  /-- The tail of a list -/
  snd : α → α

  eq_fst : ∀ x y, fst (pair x y) = x
  eq_snd : ∀ x y, snd (pair x y) = y

inductive Pairing.toSet {A : Type} [Pairing A] : A → Set A where
  | elem_fst: ∀ x y, toSet (pair x y) x
  | elem_snd: ∀ x x' y, toSet y x → toSet (pair x' y) x

instance Pairing.membership {α : Type} [Pairing α] : Membership α α where
  mem x y := toSet y x

section GraphModel

  variable {α : Type}
  variable [Pairing α]
  open Pairing

  def isContinuous (f : Set α → Set α) :=
    ∀ (S : Set α) (x : α), x ∈ f S ↔ ∃ y : α, toSet y ⊆ S ∧ (x ∈ f (toSet y))

  /-- The graph of a function -/
  @[reducible]
  def Γ (f : Set α → Set α) : Set α :=
    fun a => fst a ∈ f (toSet (snd a))

  @[reducible]
  def apply (S : Set α) : Set α → Set α :=
    fun T x => ∃ y, toSet y ⊆ T ∧ pair x y ∈ S

  theorem eq_applyΓ (f : Set α → Set α) : isContinuous f → apply (Γ f) = f := by
    intro Cf
    ext S x
    constructor
    case mp =>
      simp only [apply, Γ, Membership.mem, Set.Mem]
      rintro ⟨y, yS, H⟩
      rw [eq_fst, eq_snd] at H
      apply (Cf S x).mpr
      use y
      trivial
    case mpr =>
      intro xfS
      obtain ⟨y, ys, H⟩ := (Cf S x).mp xfS
      use y
      constructor
      · assumption
      · simp only [apply, Γ, Membership.mem, Set.Mem]
        rw [eq_fst, eq_snd]
        assumption

  def Pair (S : Set α) (T : Set α) : Set α := { pair (x : α) y | (x : S) (y : T)}

  instance Pairing.hasDot: HasDot (Set α) where
    dot := apply

  def k : Set α → Set α


end GraphModel
