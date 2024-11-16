import PartialCombinatoryAlgebras.Basic

namespace PCA

  variable {A : Type*} [PCA A]

  def I : Part A := S ⬝ K ⬝ K

  @[simp]
  theorem equal_I {u : Part A} : u ⇓ → I ⬝ u = u := by
    intro hu ; simp [I, hu]

  @[simp]
  theorem defined_I (u : Part A) : u ⇓ → (I ⬝ u) ⇓ := by
    intro hu
    rw [equal_I] <;> assumption

  def emptyEnv {A} := @Empty.elim A

  #print emptyEnv

  def pair (u v : Part A) : Part A := Expr.eval emptyEnv (Expr.abstr (.var .here))

  def fst : Part A := sorry

  def snd : Part A := sorry

  def equal_pair : Part A := sorry


  end PCA
