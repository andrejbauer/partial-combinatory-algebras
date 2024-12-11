import Mathlib.Data.Part

/-- A notation for totality of a partial element (we find writing `x.Dom` a bit silly). -/
notation:50 u:max " ⇓ " => Part.Dom u

/-- A generic notation for a left-associative binary operation. -/
class HasDot (A : Type*) where
  /-- (possibly partial) binary application -/
  dot : A → A → A

@[inherit_doc]
infixl:70 " ⬝ " => HasDot.dot

/-- A partial binary operation on a set. -/
class PartialApplication (A : Type*) where
  /-- Partial application -/
  app : Part A → Part A → Part A

instance PartialApplication.hasDot {A : Type*} [PartialApplication A] : HasDot (Part A) where
  dot := app
