import Mathlib.Logic.Denumerable
import Mathlib.Computability.Partrec
import Mathlib.Computability.PartrecCode
import PartialCombinatoryAlgebras.PartialCombinatoryAlgebra

/-! The Mathlib computability library has theorems stating that Gödel codes
     of partial computable maps *exist*, but has no way of actually constructing
     them, because `Nat.Partrec` maps into `Prop`, evan though the proofs all
     seem to be explicit enough that the codes could be extracted.

     Consequently and unfortunately, we construct the first Kleene algebra in
     a non-computable manner.
-/

namespace FirstKleeneAlgebra

open Nat.Partrec

@[reducible]
def kleeneApp : ℕ → ℕ →. ℕ := fun m n => Code.eval (Denumerable.ofNat Code m) n

theorem kleeneApp_partrec₂ : Partrec₂ kleeneApp := by
  apply Partrec₂.comp₂ (f := Code.eval)
  · exact Code.eval_part
  · apply Computable.comp (f := Denumerable.ofNat Code) (g := Prod.fst)
    · apply Computable.ofNat
    · exact Computable.fst
  · apply Computable.to₂
    apply Computable.snd

instance hasDot: HasDot (Part ℕ) where
  dot u v := u.bind (fun m => v.bind (fun n => kleeneApp m n))

@[reducible]
def K : ℕ → ℕ →. ℕ := Code.eval ∘ Code.const

theorem K_part : Partrec₂ K := by
  apply Partrec₂.comp₂ (f := Code.eval)
  · exact Code.eval_part
  · apply Computable.comp (f := Code.const) (g := Prod.fst)
    · exact Code.const_prim.to_comp
    · apply Computable.fst
  · apply Computable.snd

lemma eq_decode_encode (c : Code) : Denumerable.ofNat Code c.encodeCode = c := by
  rw [Code.ofNatCode_eq]
  induction c <;> simp [Code.encodeCode, Code.ofNatCode, Nat.div2_val, *]

theorem K_code_exists : ∃ k : ℕ, ∀ (a b : ℕ), (Part.some k) ⬝ a ⬝ b = .some a := by
  obtain ⟨c, H⟩ := Code.exists_code.mp K_part
  rw [K] at H ; simp at H
  use c.encodeCode
  intros a b
  simp [hasDot, eq_decode_encode, kleeneApp]
  rw [H]
  simp


end FirstKleeneAlgebra
