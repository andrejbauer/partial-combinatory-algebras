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

  def isContinuous_monotone {f : Set α → Set α} :
    isContinuous f → ∀ (S T), S ⊆ T → f S ⊆ f T := by
    intro Cf S T ST x xfS
    obtain ⟨y, yS, xfy⟩ := (Cf S x).mp xfS
    apply (Cf T x).mpr
    use y
    constructor
    · intro z zy ; exact ST (yS zy)
    · assumption

  def isContinuous.id : isContinuous (@id (Set α)) := by
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

  def isContinuous.const (T : Set α) : isContinuous (fun (_ : Set α) => T) := by
    intro S x
    simp
    intro xT
    use (fromList [])
    rw [eq_toSet_fromList]
    rintro x ⟨⟩

  lemma isContinuous_finite {f : Set α → Set α} (ys : List α) (S : Set α) :
    isContinuous f → (∀ y, y ∈ ys → y ∈ f S) → ∃ z, toSet z ⊆ S ∧ ∀ y, y ∈ ys → y ∈ f (toSet z) := by
    intro Cf ysfS
    induction ys
    case nil =>
      use (fromList [])
      constructor
      · rw [eq_toSet_fromList] ; rintro _ ⟨⟩
      · rintro _ ⟨⟩
    case cons y ys ih =>
      have H : ∀ z ∈ ys, z ∈ f S := by
        intro z zys
        apply ysfS
        exact List.mem_cons_of_mem _ zys
      obtain ⟨zs, zsS, ysfzs⟩ := ih H
      obtain ⟨z, zS, yfz⟩ := (Cf S y).mp (ysfS y (List.mem_cons_self _ _))
      use (fromList (toList z ++ toList zs))
      rw [eq_toSet_fromList]
      constructor
      · intro w
        simp [Membership.mem, Set.Mem]
        intro wzws
        cases List.mem_append.mp wzws
        case inl => apply zS ; assumption
        case inr H => apply zsS ; assumption
      · intro w wyys
        cases wyys
        case head =>
          apply isContinuous_monotone Cf (toSet z)
          · intro w wz
            apply List.mem_append.mpr ; left ; exact wz
          · assumption
        case tail =>
          apply isContinuous_monotone Cf (toSet zs)
          · intro w wzs
            apply List.mem_append.mpr ; right ; exact wzs
          · apply ysfzs ; assumption

  def isContinuous.comp (f g : Set α → Set α) :
    isContinuous f → isContinuous g → isContinuous (f ∘ g) := by
    intro Cf Cg S x
    constructor
    · intro xfgS
      obtain ⟨y, ygS, xfy⟩ := (Cf (g S) x).mp xfgS
      unfold toSet at ygS
      obtain ⟨z, zS, ygz⟩ := isContinuous_finite (toList y) S Cg ygS
      use z
      constructor
      · assumption
      · apply isContinuous_monotone Cf (toSet y) (g (toSet z))
        · intro z zy
          apply ygz
          apply zy
        · assumption
    · rintro ⟨y, yS, xfgy⟩
      apply isContinuous_monotone Cf (g (toSet y)) (g S)
      · exact isContinuous_monotone Cg _ _ yS
      · assumption

  /-- The graph of a function -/
  def graph (f : Set α → Set α) : Set α :=
    fun x => fst x ∈ f (toSet (snd x))

  def isContinuous.binary (f : Set α → Set α → Set α) :
    (∀ S, isContinuous (f S)) →
    (∀ T, isContinuous (fun S => f S T)) →
    isContinuous (fun S => graph (f S)) := by
    intro fC₁ fC₂ S x
    constructor
    · exact (fC₂ (toSet (snd x)) S (fst x)).mp
    · intro ⟨y, yS, H⟩
      apply (fC₁ S (toSet (snd x)) (fst x)).mpr
      use (snd x)
      constructor
      · trivial
      · exact isContinuous_monotone (fC₂ (toSet (snd x))) _ _ yS H

  def apply (S : Set α) : Set α → Set α :=
    fun T x => ∃ y, toSet y ⊆ T ∧ pair x y ∈ S

  @[reducible]
  instance Listing.hasDot : HasDot (Set α) where dot := apply

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

  def isContinuous.apply (T : Set α) : isContinuous (apply T) := by
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
    simp [K, Listing.hasDot]
    rw [eq_apply_graph, eq_apply_graph]
    · apply isContinuous.const
    · apply isContinuous.binary
      · exact isContinuous.const
      · intro
        exact isContinuous.id

  def S : Set α := graph (fun A => graph (fun B => graph (fun C => (A ⬝ C) ⬝ (B ⬝ C))))

  theorem eq_S {A B C : Set α} : S ⬝ A ⬝ B ⬝ C = (A ⬝ C) ⬝ (B ⬝ C) := by
    simp [S, Listing.hasDot]
    rw [eq_apply_graph, eq_apply_graph, eq_apply_graph]
    · sorry
    · sorry
    · sorry

  /-- The graph model -/
  instance isCA : CA (Set α) where
    K := K
    S := S
    eq_K := eq_K
    eq_S := eq_S

end GraphModel
