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
def app : ℕ → ℕ →. ℕ := Code.eval ∘ Denumerable.ofNat Code

theorem app_partrec₂ : Partrec₂ app := by
  apply Partrec₂.comp₂ (f := Code.eval)
  · exact Code.eval_part
  · apply Computable.comp (f := Denumerable.ofNat Code) (g := Prod.fst)
    · apply Computable.ofNat
    · exact Computable.fst
  · apply Computable.to₂
    apply Computable.snd

instance partialApplication: PartialApplication ℕ where
  app u v := u.bind (fun m => v.bind (fun n => app m n))

theorem K_part : Partrec (Part.some ∘ Code.encodeCode ∘ Code.const) := by
  apply Computable.comp
  · apply Computable.comp (f := Code.encodeCode)
    · apply Computable.encode
    · exact Code.const_prim.to_comp
  · exact Computable.id

lemma eq_ofNat_encodeCode (c : Code) : Denumerable.ofNat Code c.encodeCode = c := by
  rw [Code.ofNatCode_eq]
  induction c <;> simp [Code.encodeCode, Code.ofNatCode, Nat.div2_val, *]

theorem K_exists : ∃ k : ℕ, ∀ (u v : Part ℕ), u ⇓ → v ⇓ → .some k ⬝ u ⬝ v = u := by
  obtain ⟨c, evalc⟩ := Code.exists_code.mp K_part
  use c.encodeCode
  rintro u v hu hv
  simp [HasDot.dot, PartialApplication.app, app, eq_ofNat_encodeCode, evalc]
  rw [← Part.some_get hu]
  simp only [Part.bind_some]
  rw [← Part.some_get hv]
  simp only [Part.bind_some, eq_ofNat_encodeCode]
  simp

theorem S_exists : ∃ s : ℕ, ∀ (u v w : Part ℕ), u ⇓ → v ⇓ → w ⇓ → .some s ⬝ u ⬝ v ⬝ w = (u ⬝ w) ⬝ (v ⬝ w) := by
  sorry

noncomputable instance isPCA : PCA ℕ where
  K := .some K_exists.choose
  S := .some S_exists.choose

  df_K₀ := trivial
  df_K₁ := sorry

  df_S₀ := trivial
  df_S₁ := sorry
  df_S₂ := sorry

  eq_K := K_exists.choose_spec
  eq_S := S_exists.choose_spec


end FirstKleeneAlgebra
