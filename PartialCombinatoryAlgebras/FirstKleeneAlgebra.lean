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

lemma eq_ofNat_encodeCode (c : Code) : Denumerable.ofNat Code c.encodeCode = c := by
  rw [Code.ofNatCode_eq]
  induction c <;> simp [Code.encodeCode, Code.ofNatCode, Nat.div2_val, *]

@[reducible]
def K_map : ℕ → ℕ := Code.encodeCode ∘ Code.const

theorem K_part : Computable K_map := by
  apply Computable.comp (f := Code.encodeCode)
  · apply Computable.encode
  · exact Code.const_prim.to_comp

noncomputable def K := (Code.exists_code.mp K_part).choose

theorem K_spec : K.eval = fun n => .some (Code.encodeCode (Code.const n)) := by
  rw [K, (Code.exists_code.mp K_part).choose_spec]
  funext n
  simp

/-- Partially recursive partial functions `α → β → σ` between `Primcodable` types -/
def Partrec₃ {α β γ σ : Type} [Primcodable α] [Primcodable β] [Primcodable γ] [Primcodable σ] (f : α → β → γ →. σ) :=
  Partrec fun p : α × β × γ => f p.1 p.2.1 p.2.2

theorem Computable₂.Computable {α β σ : Type} [Primcodable α] [Primcodable β] [Primcodable σ] {f : α → β → σ} :
  Computable₂ f → ∀ {a : α}, Computable (f a) :=
  fun fc a => Computable₂.comp fc (Computable.const a) (Computable.id)

theorem S_exists : ∃ s : ℕ, ∀ (u v w : Part ℕ), u ⇓ → v ⇓ → w ⇓ → .some s ⬝ u ⬝ v ⬝ w = (u ⬝ w) ⬝ (v ⬝ w) := by
  let S : ℕ × ℕ × ℕ →. ℕ := fun (x, y, z) => (x ⬝ z) ⬝ (y ⬝ z)
  have S_part : Partrec S := by
    open Computable in
    simp [S, HasDot.dot, PartialApplication.app]
    apply Partrec.bind
    · exact Partrec₂.comp Code.eval_part (Computable.comp (Computable.ofNat Code) fst) (Computable.comp snd snd)
    · apply Partrec.bind
      · apply Partrec₂.comp
        · exact Code.eval_part
        · apply Computable.comp (Computable.ofNat Code)
          · exact Computable.comp fst (Computable.comp snd fst)
        · apply comp snd (comp snd fst)
      · apply Partrec₂.comp Code.eval_part
        · apply comp (Computable.ofNat Code) (comp snd fst)
        · exact snd
  obtain ⟨c, evalc⟩ := Code.exists_code.mp S_part
  have d := Code.curry_prim (Code.curry c)
  use c.encodeCode
  intros u v w hu hv hw
  simp [S, HasDot.dot, PartialApplication.app, app, eq_ofNat_encodeCode, evalc]
  rw [← Part.some_get hu]
  simp only [Part.bind_some]
  rw [← Part.some_get hv]
  simp only [Part.bind_some]
  rw [← Part.some_get hw]
  simp only [Part.bind_some]
  sorry

noncomputable instance isPCA : PCA ℕ where
  K := .some K.encodeCode
  S := .some S_exists.choose

  df_K₀ := by trivial

  df_K₁ := by
    intro u hu
    simp [HasDot.dot, PartialApplication.app, hu, eq_ofNat_encodeCode, K_spec]

  df_S₀ := trivial

  df_S₁ := sorry

  df_S₂ := sorry

  eq_K := by
    intro u v hu hv
    simp [HasDot.dot, PartialApplication.app, app, eq_ofNat_encodeCode, K_spec]
    rw [← Part.some_get hu]
    simp only [Part.bind_some]
    rw [← Part.some_get hv]
    simp only [Part.bind_some, eq_ofNat_encodeCode]
    simp


  eq_S := S_exists.choose_spec


end FirstKleeneAlgebra
