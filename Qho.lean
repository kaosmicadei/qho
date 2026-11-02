import Mathlib

/- Using namespace to keep the definitions organized and avoid name clashes -/
namespace Quantum

/-
Before we start proving the properties of the quantum harmonic oscillator, we
need to establish the basic properties of commutators.
-/
section Commutator

/-
To define a commutator we need a ring, a type equipped with addition, multiplication,
and additive inverses.
-/
variable {A : Type*} [Ring A]

def comm (x y : A) : A := x * y - y * x

/-
Be able to define new notations is one of the coolest things in Lean.
-/
notation "⟦" x ", " y "⟧" => comm x y

/- --- Useful lemmas about commutators --- -/
theorem comm_self (x : A) : ⟦x, x⟧ = 0 := by simp [comm]

theorem comm_skew (x y : A) : ⟦x, y⟧ = - ⟦y, x⟧ := by simp [comm]

theorem comm_add_left (x y z : A) : ⟦x + y, z⟧ = ⟦x, z⟧ + ⟦y, z⟧ := by
  unfold comm
  rw [add_mul, mul_add]
  abel

theorem comm_add_right (x y z : A) : ⟦x, y + z⟧ = ⟦x, y⟧ + ⟦x, z⟧ := by
  unfold comm
  rw [add_mul, mul_add]
  abel

theorem comm_mul_left (x y z : A) : ⟦x * y, z⟧ = x * ⟦y, z⟧ + ⟦x, z⟧ * y := by
  unfold comm
  noncomm_ring

theorem comm_mul_right (x y z : A) : ⟦x, y * z⟧ = ⟦x, y⟧ * z + y * ⟦x, z⟧ := by
  unfold comm
  noncomm_ring

end Commutator

section NumberOperator

variable {A : Type*} [Ring A]
variable (a ad : A)

def numberOp (a ad : A) : A := ad * a

theorem numberOp_annihilation (h : ⟦a, ad⟧ = 1) : ⟦numberOp a ad, a⟧ = -a := by
  unfold numberOp
  rw [comm_mul_left, comm_skew ad a, comm_self, h, mul_zero, zero_add, neg_one_mul]

theorem numberOp_creation (h : ⟦a, ad⟧ = 1) : ⟦numberOp a ad, ad⟧ = ad := by
  unfold numberOp
  rw [comm_mul_left, comm_self, h, mul_one, zero_mul, add_zero]

end NumberOperator

end Quantum
