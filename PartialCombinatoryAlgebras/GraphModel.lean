import Mathlib.Data.SetLike.Basic

import PartialCombinatoryAlgebras.Basic
import PartialCombinatoryAlgebras.CombinatoryAlgebra

/-! We show that a pairing function `A × A → A` on a set `A` induces
    a combinatory algebra structure on the power set of `A`.
-/

class Listing (α : Type) where
  fromList : List α → α
  toList : α → List α
  eq_list : ∀ xs, toList (fromList xs) = xs

instance Listing.membership {α : Type} [Listing α] : Membership α α where
  mem x y := x ∈ toList y

instance Listing.inhabited {α : Type} [Listing α] : Inhabited α where
  default := fromList []

/-- [x] qua finite set when decoded to a list -/
def toSet {α : Type} [Listing α] (x : α) : Set α := (Listing.toList x).Mem

@[simp]
theorem eq_toSet_fromList {α : Type} [Listing α] {ys : List α} :
  toSet (Listing.fromList ys) = ys.Mem := by
  ext ; unfold toSet ; rw [Listing.eq_list]

def Listing.pair {α : Type} [Listing α] (x y : α) : α := fromList [x, y]

def Listing.fst {α : Type} [Listing α] (x : α) : α := (toList x).head!

def Listing.snd {α : Type} [Listing α] (x : α) : α := (toList x).get! 1

theorem Listing.eq_fst_pair {α : Type} [Listing α] (x y : α) : fst (pair x y) = x
  := by simp [fst, snd, pair, eq_list]

theorem Listing.eq_snd_pair {α : Type} [Listing α] (x y : α) : snd (pair x y) = y
  := by simp [fst, snd, pair, eq_list]

section GraphModel

  variable {α : Type} [Listing α]
  open Listing

  def isContinuous (f : Set α → Set α) :=
    ∀ (S : Set α) (x : α), x ∈ f S ↔ ∃ y : α, toSet y ⊆ S ∧ (x ∈ f (toSet y))

  def id_isContinuous : isContinuous (@id (Set α)) := by
    intros S x
    simp
    constructor
    case mp =>
      intro xS
      use (fromList [x])
      constructor
      · intro y
        rw [eq_toSet_fromList]
        simp [Membership.mem, Set.Mem]
        rintro (H | ⟨A, ⟨⟩⟩) ; assumption
      · rw [eq_toSet_fromList]
        constructor
    case mpr =>
      rintro ⟨y, yS, xy⟩
      exact yS xy

  def const_isContinuous (T : Set α) : isContinuous (fun (_ : Set α) => T) := by
    intro S x
    simp
    intro xT
    use (fromList [])
    rw [eq_toSet_fromList]
    rintro x ⟨⟩

  /-- The graph of a function -/
  def graph (f : Set α → Set α) : Set α :=
    fun a => fst a ∈ f (toSet (snd a))

  def apply (S : Set α) : Set α → Set α :=
    fun T x => ∃ y, toSet y ⊆ T ∧ pair x y ∈ S

  instance : HasDot (Set α) where dot := apply

  def apply_monotone₁ {S T U : Set α} : S ⊆ T → apply S U ⊆ apply T U := by
    rintro ST U ⟨y, yU, xyS⟩
    use y
    constructor
    · assumption
    · exact ST xyS

  def apply_monotone₂ {S T U : Set α} : S ⊆ T → apply U S ⊆ apply U T := by
    rintro ST x ⟨y, yS, xyU⟩
    use y
    constructor
    · intro z ; exact fun a ↦ ST (yS a)
    · assumption

  def apply_monotone {S T U V : Set α} : S ⊆ T → U ⊆ V → apply S U ⊆ apply T V := by
    intro ST UV x xSU
    apply apply_monotone₁ ST
    apply apply_monotone₂ UV xSU

  def apply_isContinuous (T : Set α) : isContinuous (apply T) := by
    intros S x
    constructor
    · rintro ⟨y, yS, xyT⟩
      use y
      constructor
      · assumption
      · use y
    · rintro ⟨y, yS, xTy⟩
      apply apply_monotone₂ yS xTy

  theorem eq_apply_graph (f : Set α → Set α) : isContinuous f → apply (graph f) = f := by
    intro Cf
    ext S x
    constructor
    case mp =>
      simp only [apply, graph, Membership.mem, Set.Mem]
      rintro ⟨y, yS, H⟩
      rw [eq_fst_pair, eq_snd_pair] at H
      apply (Cf S x).mpr
      use y
      trivial
    case mpr =>
      intro xfS
      obtain ⟨y, ys, H⟩ := (Cf S x).mp xfS
      use y
      constructor
      · assumption
      · simp only [apply, graph, Membership.mem, Set.Mem]
        rw [eq_fst_pair, eq_snd_pair]
        assumption

  def K : Set α := graph (fun A => graph (fun _ => A))

  theorem eq_K {A B : Set α} : K ⬝ A ⬝ B = A := by
    unfold K graph
    ext x
    simp [Membership.mem, Set.Mem, HasDot.dot]
    constructor
    · rintro ⟨y, yB, ⟨z, zA, xyzK⟩⟩
      simp [Membership.mem, Set.Mem, eq_fst_pair, eq_snd_pair] at xyzK
      exact (zA xyzK)
    · intro xA
      use (fromList [])
      constructor
      · intro x
        rw [eq_toSet_fromList]
        rintro ⟨⟩
      · use (fromList [x])
        constructor
        · rw [eq_toSet_fromList]
          intro y H
          cases H
          case head => assumption
          case tail H => cases H
        · simp [Membership.mem, Set.Mem, eq_fst_pair, eq_snd_pair]
          constructor

  def S : Set α := graph (fun A => graph (fun B => graph (fun C => (A ⬝ C) ⬝ (B ⬝ C))))

  theorem eq_S {A B C : Set α} : S ⬝ A ⬝ B ⬝ C = (A ⬝ C) ⬝ (B ⬝ C) := by
    unfold S graph
    ext x
    simp [Membership.mem, Set.Mem, HasDot.dot]
    constructor
    · rintro ⟨y, yC, ⟨z, zB, ⟨w, wA, H⟩⟩⟩
      simp [Membership.mem, Set.Mem, eq_fst_pair, eq_snd_pair] at H
      have wyAC : apply (toSet w) (toSet y) ⊆ apply A C := apply_monotone wA yC
      have zyBC : apply (toSet z) (toSet y) ⊆ apply B C := apply_monotone zB yC
      apply apply_monotone wyAC zyBC H
    · rintro ⟨y, yBC, ⟨z, zC, H⟩⟩
      sorry

  /-- The graph model -/
  instance isCA : CA (Set α) where
    K := K
    S := S
    eq_K := eq_K
    eq_S := eq_S

end GraphModel
