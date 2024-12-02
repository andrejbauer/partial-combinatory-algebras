import PartialCombinatoryAlgebras.Basic

namespace PCA

  open Expr

  universe u
  variable {A : Type u} [PCA A]

  def I : Part A := [pca: Expr.S ⬝ Expr.K ⬝ Expr.K]

  def I.elm {Γ} : Expr Γ A := .elm (I.get (PCA.df_S₂ PCA.df_K₀ PCA.df_K₀))

  @[simp]
  theorem df_I : (I : Part A) ⇓ := by
    simp [I, eval]

  @[simp]
  theorem eq_I {u : Part A} : u ⇓ → I ⬝ u = u := by
    intro hu ; simp [I, hu, eval]

  def K' : Part A := K ⬝ (S ⬝ K ⬝ K)

  @[simp]
  theorem df_K' : (K' : Part A) ⇓ := by simp [K', eval]

  @[simp]
  theorem eq_K' (u v : Part A) :
    u ⇓ → v ⇓ → K' ⬝ u ⬝ v = v := by
    intros hu hv
    simp [K', eval, hu, hv]

  /-! ### Pairing -/

  def pair : Part A := [pca: ≪`x≫ ≪`y≫ ≪`z≫ var `z ⬝ var `x ⬝ var `y]

  @[simp]
  theorem df_pair : (pair : Part A) ⇓ := by
    apply df_abstr

  @[simp]
  theorem df_pair_app (u : Part A):
    u ⇓ → (pair ⬝ u) ⇓ := by
      intro hu
      simp [pair]
      rw [eval_abstr_app] <;> try assumption
      apply df_abstr

  @[simp]
  theorem df_pair_app_app (u v : Part A):
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

  def fst.elm {Γ}: Expr Γ A := .elm (fst.get (df_abstr _ _ _))

  @[simp]
  theorem eq_fst (u : Part A):
    u ⇓ → fst ⬝ u = u ⬝ PCA.K := by
    intro hu
    simp [fst]
    rw [eval_abstr_app]
    simp [override, eval]
    rw [Part.some_get]
    assumption

  def snd : Part A := [pca: ≪ `x ≫ var `x ⬝ (Expr.K ⬝ (Expr.S ⬝ Expr.K ⬝ Expr.K))]

  def snd.elm {Γ} : Expr Γ A := .elm (snd.get (df_abstr _ _ _))

  @[simp]
  theorem eq_snd (u : Part A):
    u ⇓ → snd ⬝ u = u ⬝ K' := by
    intro hu
    simp [snd]
    rw [eval_abstr_app]
    simp [override, eval]
    rw [Part.some_get] <;> simp [hu, K']

  @[simp]
  def eq_fst_pair (u v : Part A) : u ⇓ → v ⇓ → fst ⬝ (pair ⬝ u ⬝ v) = u := by
    intro hu hv
    calc
    _ = pair ⬝ u ⬝ v ⬝ K  := by apply eq_fst ; apply df_pair_app_app <;> assumption
    _ = K ⬝ u ⬝ v        := by apply eq_pair <;> simp [hu, hv]
    _ = u               := by apply eq_K <;> assumption

  @[simp]
  def eq_snd_pair (u v : Part A) : u ⇓ → v ⇓ → snd ⬝ (pair ⬝ u ⬝ v) = v := by
    intro hu hv
    calc
    _ = pair ⬝ u ⬝ v ⬝ K' := by apply eq_snd ; apply df_pair_app_app <;> assumption
    _ = K' ⬝ u ⬝ v := by apply eq_pair <;> simp [hu, hv]
    _ = v := by rw [eq_K'] <;> assumption

  /-- Conditional statements -/
  def ite : Part A := I

  /-- The bollean false -/
  def fal : Part A := K'

  @[simp] theorem df_fal : (fal : Part A) ⇓ := by simp [fal]

  /-- The boolean true -/
  def tru : Part A := K

  @[simp] theorem df_tru : (tru : Part A) ⇓ := by simp [tru]

  @[simp]
  theorem eq_ite_fal (u v : Part A) : u ⇓ → v ⇓ → ite ⬝ fal ⬝ u ⬝ v = v := by
    intros hu hv
    simp [hu, hv, ite, fal]

  @[simp]
  theorem eq_ite_tru (u v : Part A) : u ⇓ → v ⇓ → ite ⬝ tru ⬝ u ⬝ v = u := by
    intros hu hv
    simp [hu, hv, ite, tru]

  /-! ### The fixed point combinator -/

  def X : Part A := [pca: ≪`x≫ ≪`y≫ ≪`z≫ var `y ⬝ (var `x ⬝ var `x ⬝ var `y) ⬝ var `z]

  @[simp]
  theorem df_X : (X : Part A) ⇓ := by
    simp [X]
    apply df_abstr

  @[simp]
  theorem df_X_app (u : Part A) : u ⇓ → (X ⬝ u) ⇓ := by
    intro hu
    simp [X]
    rw [eval_abstr_app]
    apply df_abstr
    assumption

  @[simp]
  theorem df_X_app_app (u v : Part A) : u ⇓ → v ⇓ → (X ⬝ u ⬝ v) ⇓ := by
    intro hu hv
    simp [X]
    rw [eval_abstr_app, eval_abstr_app] <;> try assumption
    apply df_abstr

  theorem eq_X (u v w : Part A) : u ⇓ → v ⇓ → w ⇓ → X ⬝ u ⬝ v ⬝ w = v ⬝ (u ⬝ u ⬝ v) ⬝ w := by
    intros hu hv hw
    simp [X]
    rw [eval_abstr_app, eval_abstr_app, eval_abstr_app] <;> try assumption
    simp [eval, override]

  def Z : Part A := X ⬝ X

  theorem df_Z : (Z : Part A) ⇓ := by simp [Z]

  @[simp]
  theorem df_Z_app (u : Part A) : u ⇓ → (Z ⬝ u) ⇓ := by
    intros hu
    simp [Z, hu]

  theorem eq_Z (u v : Part A) : u ⇓ → v ⇓ → Z ⬝ u ⬝ v = u ⬝ (Z ⬝ u) ⬝ v := by
    intro hu hv
    simp [Z, hu, hv]
    rw [eq_X] <;> simp [hu, hv]

  def W : Part A := [pca: ≪`x≫ ≪`y≫ var `y ⬝ (var `x ⬝ var `x ⬝ var `y)]

  @[simp]
  def df_W : (W : Part A) ⇓ := by simp [W] ; apply df_abstr

  @[simp]
  def df_W_app (u : Part A) : u ⇓ → (W ⬝ u) ⇓ := by
    intro hu
    simp [W]
    rw [eval_abstr_app] <;> try assumption
    apply df_abstr

  def eq_W (u v : Part A) : u ⇓ → v ⇓ → W ⬝ u ⬝ v = v ⬝ (u ⬝ u ⬝ v) := by
    intro hu hv
    simp [W]
    rw [eval_abstr_app, eval_abstr_app] <;> try assumption
    simp [eval, override]

  def Y : Part A := W ⬝ W

  @[simp]
  theorem df_Y : (Y : Part A) ⇓ := by simp [Y]

  theorem eq_Y (u : Part A) : u ⇓ → Y ⬝ u = u ⬝ (Y ⬝ u) := by
    intro hu
    simp [Y, hu]
    nth_rewrite 1 [eq_W] <;> simp [hu]


  /-! ### Curry numerals -/

  /-- Curry numeral -/
  def numeral : Nat → Part A
  | 0 => I
  | .succ n => pair ⬝ fal ⬝ (numeral n)

  @[simp]
  theorem df_numeral (n : Nat) : (numeral n : Part A) ⇓ := by
    induction n
    case zero => simp [numeral]
    case succ n ih => simp [numeral, ih]

  /-- The successor of a Curry numeral -/
  def succ : Part A := pair ⬝ fal

  @[simp]
  def df_succ : (succ : Part A) ⇓ := by simp [succ]

  @[simp]
  def df_succ_app (u : Part A) : u ⇓ → (succ ⬝ u) ⇓ := by
    intro hu
    simp [succ, df_pair_app_app, hu]

  /-- Is a numeral equal to zero? -/
  def iszero : Part A := fst

  @[simp]
  theorem eq_iszero_0 : iszero ⬝ (numeral 0) = (tru : Part A) := by
    simp [iszero, numeral, tru]

  @[simp]
  theorem eq_iszero_succ (n : Nat): iszero ⬝ (numeral n.succ) = (fal : Part A) := by
    simp [iszero, numeral]

  /-- Predecessor of a Curry numeral -/
  def pred : Part A := [pca: ≪`x≫ (fst.elm ⬝ var `x) ⬝ I.elm ⬝ (snd.elm ⬝ var `x)]

  @[simp]
  theorem eq_pred (u : Part A) : u ⇓ → pred ⬝ u = (fst ⬝ u) ⬝ I ⬝ (snd ⬝ u) := by
    intro hu
    simp [pred]
    rw [eval_abstr_app] <;> try assumption
    simp [eval, override]

  @[simp]
  theorem eq_pred_succ (n : Nat) : pred ⬝ (succ ⬝ numeral n) = (numeral n : Part A) := sorry

  /-- Primitive recursion -/
  def primrec : Part A := sorry

  theorem eq_primrec_zero (n : ℕ) (u f : Part A) : u ⇓ → f ⇓ → primrec ⬝ u ⬝ f ⬝ numeral 0 = u := by
    sorry

  theorem eq_primrec_succ (n : ℕ) (u f : Part A) : u ⇓ → f ⇓ →
    primrec ⬝ u ⬝ f ⬝ numeral n.succ = f ⬝ numeral n ⬝ (primrec ⬝ u ⬝ f ⬝ numeral n)
    := by
    sorry

end PCA
