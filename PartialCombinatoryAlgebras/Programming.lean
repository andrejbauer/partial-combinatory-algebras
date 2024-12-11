import PartialCombinatoryAlgebras.Basic
import PartialCombinatoryAlgebras.PartialCombinatoryAlgebra

/-! ## Programming with PCAs

  A (non-trivial) PCA is Turing-complete in the sense that it implements
  every partial computable function. We develop here basic programming
  constructs that witness this fact:

  * the identity combinatory `I`
  * ordered pairs `pair` with projections `fst` and `snd`
  * booleans `true`, `false` and the conditional statement `ite`
  * fixed-point combinators `Z` and `Y`
  * Curry numerals `numeral n` with `zero`, successor `succ`, predecessor `pred` and primitive recursion `primrec`
  * TODO: general recursion (but it should be easy given what we have)

  For any of the combinators so defined, say `C`, we also prove two lemmas: `df_C` characterizes totality of
  expressions involving `C`, and `eq_C` gives the characteristic equation for `C`. These lemmas are automatically
  used by `simp`.
-/

namespace PCA

  universe u
  variable {A : Type u} [PCA A]

  /-- The identity combinator -/
  def I : Part A := S ⬝ K ⬝ K

  /-- The expression denoting the identity combinator -/
  def Expr.I {Γ} : Expr Γ A := .S ⬝ .K ⬝ .K

  @[simp]
  theorem df_I : (I : Part A) ⇓ := by
    simp [I, eval]

  @[simp]
  theorem eq_I {u : Part A} : u ⇓ → I ⬝ u = u := by
    intro hu ; simp [eq_S, eq_K, I, hu, eval]

  def K' : Part A := K ⬝ I

  def Expr.K' {Γ} : Expr Γ A := .K ⬝ .I

  @[simp]
  theorem df_K' : (K' : Part A) ⇓ := by simp [K', eval]

  @[simp]
  theorem eq_K' (u v : Part A) :
    u ⇓ → v ⇓ → K' ⬝ u ⬝ v = v := by
    intros hu hv
    simp [K', eq_S, eq_K, eval, hu, hv]

  /-! ### Pairing -/

  def pair : Part A := [pca: ≪`x≫ ≪`y≫ ≪`z≫ .var `z ⬝ .var `x ⬝ .var `y]

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
    rw [eval_abstr_app, eval_abstr_app, eval_abstr_app, eval_override, eval_override, eval_override]
    simp [eval]
    rw [Part.some_get, Part.some_get, Part.some_get] <;> assumption

  def fst : Part A := [pca: ≪ `x ≫ .var `x ⬝ .K]

  def fst.elm {Γ}: Expr Γ A := .elm (fst.get (df_abstr _ _ _))

  @[simp]
  theorem eq_fst (u : Part A):
    u ⇓ → fst ⬝ u = u ⬝ PCA.K := by
    intro hu
    simp [fst]
    rw [eval_abstr_app, eval_override]
    simp [eval]
    rw [Part.some_get]
    assumption

  def snd : Part A := [pca: ≪ `x ≫ .var `x ⬝ .K']

  def snd.elm {Γ} : Expr Γ A := .elm (snd.get (df_abstr _ _ _))

  @[simp]
  theorem eq_snd (u : Part A):
    u ⇓ → snd ⬝ u = u ⬝ K' := by
    intro hu
    simp [snd]
    rw [eval_abstr_app, eval_override]
    simp [eval]
    rw [Part.some_get]
    rfl
    assumption

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

  @[simp] theorem eq_fal (u v : Part A) : u ⇓ → v ⇓ → fal ⬝ u ⬝ v = v := eq_K' _ _

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
    simp [eq_K, hu, hv, ite, tru]

  /-! ### The fixed point combinator -/

  def X : Part A := [pca: ≪`x≫ ≪`y≫ ≪`z≫ .var `y ⬝ (.var `x ⬝ .var `x ⬝ .var `y) ⬝ .var `z]

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
    rw [eval_abstr_app, eval_abstr_app, eval_abstr_app, eval_override, eval_override, eval_override] <;> try assumption
    simp [eval]

  def Z : Part A := X ⬝ X

  @[simp]
  theorem df_Z : (Z : Part A) ⇓ := by simp [Z]

  @[reducible]
  def Z.elm {Γ} : Expr Γ A := .elm (Z.get df_Z)

  @[simp]
  theorem df_Z_app (u : Part A) : u ⇓ → (Z ⬝ u) ⇓ := by
    intros hu
    simp [Z, hu]

  theorem eq_Z (u v : Part A) : u ⇓ → v ⇓ → Z ⬝ u ⬝ v = u ⬝ (Z ⬝ u) ⬝ v := by
    intro hu hv
    simp [Z, hu, hv]
    rw [eq_X] <;> simp [hu, hv]

  def W : Part A := [pca: ≪`x≫ ≪`y≫ .var `y ⬝ (.var `x ⬝ .var `x ⬝ .var `y)]

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
    rw [eval_abstr_app, eval_abstr_app, eval_override, eval_override] <;> try assumption
    simp [eval]

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
    simp [iszero, numeral, eq_K]

  /-- Predecessor of a Curry numeral -/
  def pred : Part A := [pca: ≪`x≫ (fst.elm ⬝ .var `x) ⬝ .I ⬝ (snd.elm ⬝ .var `x)]

  @[simp]
  def df_pred : (pred : Part A) ⇓ := by simp [pred] ; apply df_abstr

  @[reducible]
  def pred.elm {Γ} : Expr Γ A := .elm (pred.get df_pred)

  @[simp]
  theorem eq_pred (u : Part A) : u ⇓ → pred ⬝ u = (fst ⬝ u) ⬝ I ⬝ (snd ⬝ u) := by
    intro hu
    simp [pred]
    rw [eval_abstr_app, eval_override] <;> try assumption
    simp [eval] ; rfl

  @[simp]
  theorem eq_pred_succ (u : Part A) : u ⇓ → pred ⬝ (succ ⬝ u) = u := by
    intro hu
    simp [pred]
    rw [eval_abstr_app, eval_override] <;> simp [eq_K, eq_K', eval, succ, fal, hu]

  def primrec.R : Part A := [pca:
    ≪`r≫ ≪`x≫ ≪`f≫ ≪`m≫
      (fst.elm ⬝ .var `m) ⬝ (.K ⬝ .var `x) ⬝
      (≪ `y ≫ .var `f ⬝ (pred.elm ⬝ .var `m) ⬝ (.var `r ⬝ .var `x ⬝ .var `f ⬝ (pred.elm ⬝ .var `m) ⬝ .I))
  ]

  def primrec.eq_R (r u f m : Part A) (hr : r ⇓) (hu : u ⇓) (hf : f ⇓) (hm : m ⇓) :
      primrec.R ⬝ r ⬝ u ⬝ f ⬝ m =
      (fst ⬝ m) ⬝ (K ⬝ u) ⬝ [pca: ≪`y≫ .elm (f.get hf) ⬝
      (pred.elm ⬝ .elm (m.get hm)) ⬝ (.elm (r.get hr) ⬝ .elm (u.get hu) ⬝ .elm (f.get hf) ⬝ (pred.elm ⬝ .elm (m.get hm)) ⬝ (Expr.S ⬝ Expr.K ⬝ Expr.K))]
    := by
    simp [R]
    rw [eval_abstr_app, eval_abstr_app, eval_abstr_app, eval_abstr_app, eval_override, eval_override, eval_override, eval_override] <;> try assumption
    simp [eval]

  @[simp]
  def primrec.df_R : (R : Part A) ⇓ := by simp [R] ; apply df_abstr

  def primrec.R.elm {Γ} : Expr Γ A := .elm (R.get df_R)

  /-- Primitive recursion -/
  def primrec : Part A := [pca: ≪`x≫ ≪`f≫ ≪`m≫ (Z.elm ⬝ primrec.R.elm) ⬝ .var `x ⬝ .var `f ⬝ .var `m ⬝ .I]

  @[simp]
  theorem eq_primrec (u f m : Part A) :
    u ⇓ → f ⇓ → m ⇓ → primrec ⬝ u ⬝ f ⬝ m = (Z ⬝ primrec.R) ⬝ u ⬝ f ⬝ m ⬝ I := by
      intros hu hf hm
      simp [primrec]
      rw [eval_abstr_app, eval_abstr_app, eval_abstr_app, eval_override, eval_override, eval_override] <;> try assumption
      simp [eval] ; rfl

  theorem eq_primrec_zero (u f : Part A) : u ⇓ → f ⇓ → primrec ⬝ u ⬝ f ⬝ numeral 0 = u := by
    intro hu hf
    rw [numeral, eq_primrec, eq_Z, primrec.eq_R] <;> simp [hu, hf]
    rw [eq_K, eq_K]
    · assumption
    · simp
    · apply df_K₁ ; assumption
    · apply df_abstr

  theorem eq_primrec_succ (u f n : Part A) : u ⇓ → f ⇓ → n ⇓ →
    primrec ⬝ u ⬝ f ⬝ (succ ⬝ n) = f ⬝ n ⬝ (primrec ⬝ u ⬝ f ⬝ n) := by
    intros hu hf hn
    rw [eq_primrec] <;> simp [hu, hf, hn]
    rw [eq_Z, primrec.eq_R, eq_fst] <;> simp [hu, hf, hn]
    unfold succ
    rw [eq_pair, eq_K, eq_fal] <;> try simp [hu, hf, hn]
    · rw [eval_abstr_app, eval_override] <;> try apply df_I
      simp [eval]
      rw [eq_pred, eq_fst, eq_pair, eq_K, eq_fal, eq_snd_pair] <;> try simp [*]
      nth_rewrite 1 [eq_Z] <;> try simp [*]
      rfl
    · apply df_abstr

end PCA
