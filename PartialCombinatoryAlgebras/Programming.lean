import PartialCombinatoryAlgebras.Basic

namespace PCA
  open Expr

  universe u
  variable {A : Type u} [PCA A]

  def I : Part A := S ⬝ K ⬝ K

  @[simp]
  theorem equal_I {u : Part A} : u ⇓ → I ⬝ u = u := by
    intro hu ; simp [I, hu]

  @[simp]
  theorem defined_I (u : Part A) : u ⇓ → (I ⬝ u) ⇓ := by
    intro hu
    rw [equal_I] <;> assumption

  def pair : Part A :=
    compile (abstr "x" (abstr "y" (abstr "z" (var "z" ⬝ var "x" ⬝ var "y"))))

  @[simp]
  theorem defined_pair (u v : Part A):
    u ⇓ → v ⇓ → (pair ⬝ u ⬝ v) ⇓ := by
      intro hu hv
      simp [pair]
      rw [eval_abstr_app, eval_abstr_app] <;> try assumption
      apply defined_abstr

  theorem equal_pair (u v w : Part A) :
    u ⇓ → v ⇓ → w ⇓ → pair ⬝ u ⬝ v ⬝ w = w ⬝ u ⬝ v := by
    intros hu hv hw
    simp [pair]
    rw [eval_abstr_app, eval_abstr_app, eval_abstr_app]
    simp [override, eval]
    rw [Part.some_get, Part.some_get, Part.some_get] <;> assumption

  def fst : Part A :=
    compile (abstr "x" (var "x" ⬝ .K))

  theorem equal_fst (u : Part A):
    u ⇓ → fst ⬝ u = u ⬝ K := by
    intro hu
    simp [fst]
    rw [eval_abstr_app]
    simp [override, eval]
    rw [Part.some_get]
    assumption

  def snd : Part A :=
    compile ((abstr "x" (var "x" ⬝ (.K ⬝ (.S ⬝ .K ⬝ .K)))))

  theorem equal_snd (u : Part A):
    u ⇓ → snd ⬝ u = u ⬝ (K ⬝ (S ⬝ K ⬝ K)) := by
    intro hu
    simp [snd]
    rw [eval_abstr_app]
    simp [override, eval]
    rw [Part.some_get]
    assumption

  @[simp]
  def equal_fst_pair (u v : Part A) : u ⇓ → v ⇓ → fst ⬝ (pair ⬝ u ⬝ v) = u := by
    intro hu hv
    calc
    _ = pair ⬝ u ⬝ v ⬝ K  := by apply equal_fst ; apply defined_pair <;> assumption
    _ = K ⬝ u ⬝ v        := by apply equal_pair <;> simp [hu, hv]
    _ = u               := by apply eq_K <;> assumption

  @[simp]
  def equal_snd_pair (u v : Part A) : u ⇓ → v ⇓ → snd ⬝ (pair ⬝ u ⬝ v) = v := by
    intro hu hv
    calc
    _ = pair ⬝ u ⬝ v ⬝ (K ⬝ (S ⬝ K ⬝ K)) := by apply equal_snd ; apply defined_pair <;> assumption
    _ = (K ⬝ (S ⬝ K ⬝ K)) ⬝ u ⬝ v := by apply equal_pair <;> simp [hu, hv]
    _ = v := by rw [eq_K, eq_S, eq_K] <;> simp [hu, hv]

  def ite : Part A := sorry
  def fal : Part A := sorry
  def tru : Part A := sorry

  theorem equal_ite_fal (u v : Part A) : u ⇓ → v ⇓ → ite ⬝ fal ⬝ u ⬝ v = v := by
    sorry

  theorem equal_ite_tru (u v : Part A) : u ⇓ → v ⇓ → ite ⬝ tru ⬝ u ⬝ v = u := by
    sorry

  def numeral (n : ℕ) : Part  A := sorry
  def succ : Part A := sorry
  def primrec : Part A := sorry

  theorem equal_primrec_zero (n : ℕ) (u f : Part A) : u ⇓ → f ⇓ → primrec ⬝ u ⬝ f ⬝ numeral 0 = u := by
    sorry

  theorem equal_primrec_succ (n : ℕ) (u f : Part A) : u ⇓ → f ⇓ →
    primrec ⬝ u ⬝ f ⬝ numeral n.succ = f ⬝ numeral n ⬝ (primrec ⬝ u ⬝ f ⬝ numeral n)
    := by
    sorry


end PCA
