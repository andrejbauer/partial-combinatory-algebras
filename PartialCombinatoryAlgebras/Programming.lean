import PartialCombinatoryAlgebras.Basic

namespace PCA

  open Expr

  universe u
  variable {A : Type u} [PCA A]

  def I : Part A := [pca: Expr.S ⬝ Expr.K ⬝ Expr.K]

  @[simp]
  theorem eq_I {u : Part A} : u ⇓ → I ⬝ u = u := by
    intro hu ; simp [I, hu, eval]

  @[simp]
  theorem df_I (u : Part A) : u ⇓ → (I ⬝ u) ⇓ := by
    intro hu
    rw [eq_I] <;> assumption

  def pair : Part A := [pca: ≪`x≫ ≪`y≫ ≪`z≫ var `z ⬝ var `x ⬝ var `y]

  @[simp]
  theorem df_pair (u v : Part A):
    u ⇓ → v ⇓ → (pair ⬝ u ⬝ v) ⇓ := by
      intro hu hv
      simp [pair]
      rw [eval_abstr_app, eval_abstr_app] <;> try assumption
      apply df_abstr

  @[simp]
  theorem eq_pair (u v w : Part A) :
    u ⇓ → v ⇓ → w ⇓ → pair ⬝ u ⬝ v ⬝ w = w ⬝ u ⬝ v := by
    intros hu hv hw
    simp [pair]
    rw [eval_abstr_app, eval_abstr_app, eval_abstr_app]
    simp [override, eval]
    rw [Part.some_get, Part.some_get, Part.some_get] <;> assumption

  def fst : Part A := [pca: ≪ `x ≫ var `x ⬝ Expr.K]

  theorem eq_fst (u : Part A):
    u ⇓ → fst ⬝ u = u ⬝ PCA.K := by
    intro hu
    simp [fst]
    rw [eval_abstr_app]
    simp [override, eval]
    rw [Part.some_get]
    assumption

  def snd : Part A := [pca: ≪ `x ≫ var `x ⬝ (Expr.K ⬝ (Expr.S ⬝ Expr.K ⬝ Expr.K)) ]

  theorem eq_snd (u : Part A):
    u ⇓ → snd ⬝ u = u ⬝ (K ⬝ (S ⬝ K ⬝ K)) := by
    intro hu
    simp [snd]
    rw [eval_abstr_app]
    simp [override, eval]
    rw [Part.some_get]
    assumption

  @[simp]
  def eq_fst_pair (u v : Part A) : u ⇓ → v ⇓ → fst ⬝ (pair ⬝ u ⬝ v) = u := by
    intro hu hv
    calc
    _ = pair ⬝ u ⬝ v ⬝ K  := by apply eq_fst ; apply df_pair <;> assumption
    _ = K ⬝ u ⬝ v        := by apply eq_pair <;> simp [hu, hv]
    _ = u               := by apply eq_K <;> assumption

  @[simp]
  def eq_snd_pair (u v : Part A) : u ⇓ → v ⇓ → snd ⬝ (pair ⬝ u ⬝ v) = v := by
    intro hu hv
    calc
    _ = pair ⬝ u ⬝ v ⬝ (K ⬝ (S ⬝ K ⬝ K)) := by apply eq_snd ; apply df_pair <;> assumption
    _ = (K ⬝ (S ⬝ K ⬝ K)) ⬝ u ⬝ v := by apply eq_pair <;> simp [hu, hv]
    _ = v := by rw [eq_K, eq_S, eq_K] <;> simp [hu, hv]

  def ite : Part A := sorry
  def fal : Part A := sorry
  def tru : Part A := sorry

  theorem eq_ite_fal (u v : Part A) : u ⇓ → v ⇓ → ite ⬝ fal ⬝ u ⬝ v = v := by
    sorry

  theorem eq_ite_tru (u v : Part A) : u ⇓ → v ⇓ → ite ⬝ tru ⬝ u ⬝ v = u := by
    sorry

  def numeral (n : ℕ) : Part  A := sorry
  def succ : Part A := sorry
  def primrec : Part A := sorry

  theorem eq_primrec_zero (n : ℕ) (u f : Part A) : u ⇓ → f ⇓ → primrec ⬝ u ⬝ f ⬝ numeral 0 = u := by
    sorry

  theorem eq_primrec_succ (n : ℕ) (u f : Part A) : u ⇓ → f ⇓ →
    primrec ⬝ u ⬝ f ⬝ numeral n.succ = f ⬝ numeral n ⬝ (primrec ⬝ u ⬝ f ⬝ numeral n)
    := by
    sorry

end PCA
