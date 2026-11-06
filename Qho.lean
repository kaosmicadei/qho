import Mathlib

/-!
# Quantum Harmonic Oscillator
The goal of this file is to show that the quantum harmonic oscillator has a
discrete spectrum and that its eigenvalues are non-negative.

We use ladder operators a and a†, the number operator N = a†·a together with
their commutation relations as starting point. Using the number operations, the
Hamiltonian of a 1D harmonic oscillator can be written as H = ℏω(N + 1/2).
-/
namespace QuantumHarmonicOscillator

/-!
## Commutator
Before we start proving the properties of the quantum harmonic oscillator, we
need to establish the basic properties of commutators.

Mathlib already provides a definition of the commutator as `Ring.lie`. However,
I wanted to try to implement it myself to learn more about definitions and custom
notations.
-/
section Commutator

/- We define the commutator over a ring. A ring is a type equipped with addition,
multiplication, and additive inverses. -/
variable {A : Type*} [Ring A]

/-- Commutation relation. -/
def comm (x y : A) : A := x * y - y * x

/- To make the expressions easier to read, we introduce the notation ⟦x, y⟧ for the
commutator of x and y. -/
notation "⟦" x ", " y "⟧" => comm x y

/-
### Basic properties
In this file we present some basic properties of the commutator. However, not
all of them will be used in the proofs shown here.
-/
section BasicProperties

theorem comm_self (x : A) : ⟦x, x⟧ = 0 := by simp [comm]

theorem comm_skew (x y : A) : ⟦x, y⟧ = - ⟦y, x⟧ := by simp [comm]

theorem comm_add_left (x y z : A) : ⟦x + y, z⟧ = ⟦x, z⟧ + ⟦y, z⟧ := by
  unfold comm
  rw [mul_add, add_mul]
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

end BasicProperties

theorem lie_mul_left (x y z : A) : ⁅x * y, z⁆ = x * ⁅y, z⁆ + ⁅x, z⁆ * y := by
  simp only [Ring.lie_def]
  noncomm_ring

end Commutator

/-!
## Canonical commutation relation
The ladder operators satisfy the canonical commutation relation ⟦a, a†⟧ = 1.

Being the number operator defined as N = a†·a, it satisfies the commutation
relations:
* ⟦N, a⟧ = -a,
* ⟦N, a†⟧ = a†.
-/
section CCR

variable {A : Type*} [Ring A]
/- We use the ladder operators a and a† as opaque variables. -/
variable (a ad : A)

/-- Number operator defined as N = a†·a. -/
def numberOp : A := ad * a

/-- The commutation between the ladder operators is passed as a hypothesis because
they are treated as opaque variables. -/
theorem number_annihilation_comm (h : ⟦a, ad⟧ = 1) : ⟦numberOp a ad, a⟧ = -a := by
  unfold numberOp
  rw [comm_mul_left, comm_skew ad a, comm_self, h, mul_zero, zero_add, neg_one_mul]

/-- The commutation between the ladder operators is passed as a hypothesis because
they are treated as opaque variables. -/
theorem number_creation_comm (h : ⟦a, ad⟧ = 1) : ⟦numberOp a ad, ad⟧ = ad := by
  unfold numberOp
  rw [comm_mul_left, comm_self, h, mul_one, zero_mul, add_zero]

end CCR

/- A Hilbert space is normed vector space with norm induced by the inner product.
In the case of quantum mechanics, the Hilbert space is defined over the complex
numbers. -/
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
/- Ladder operators as ℂ-linear map on the Hilbert space H. -/
variable (a ad : H →ₗ[ℂ] H)
/- General hypothesis: there is x ∈ H such that N x = c • x. -/
variable {x : H} {c : ℂ}

/-
NOTE: `H →ₗ[ℂ] H` could be replaced with `Module.End ℂ H`. `Module` is the
generalisation of vector spaces and `End` refers to endomorphisms
-/

/-!
## Eigenstates of the number operator
Assume x is an eigenstate of the number operator with eigenvalue c, i.e.,
N x = c • x. We use the commutation relations of the ladder operators to derive
the properties of the action of the ladder operators on these eigenstates.
-/
section Eigenstate

/-- N(a x) = a(N x) - a x. -/
theorem number_annihilation_apply (h : ⟦a, ad⟧ = 1) :
    (numberOp a ad) (a x) = a ((numberOp a ad) x) - a x := by
  have : ⟦numberOp a ad, a⟧ x = (-a) x := LinearMap.congr_fun (number_annihilation_comm a ad h) x
  simp? [numberOp, comm, sub_eq_iff_eq_add] at this
  rw [numberOp, Module.End.mul_apply, this]
  abel

/-- Applying the annihilation operator to an eigenstate of the number operator
lowers its eigenvalue by 1. -/
theorem number_lower_one (h : ⟦a, ad⟧ = 1) (hx : (numberOp a ad) x = c • x) :
    (numberOp a ad) (a x) = (c - 1) • (a x) := by
  rw [number_annihilation_apply a ad h, hx, map_smul, sub_smul, one_smul]

/-- Applying the annihilation operator k times to an eigenstate of the number
operator lowers its eigenvalue by k with k ∈ ℕ. -/
theorem number_lower_k (h : ⟦a, ad⟧ = 1) (hx : (numberOp a ad) x = c • x) (k : ℕ) :
    (numberOp a ad) ((a^k) x) = (c - k) • ((a^k) x) := by
  induction k with
  | zero => simp [hx]
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, number_lower_one a ad h ih, sub_sub]
    norm_cast

/-- N(a† x) = a†(N x) + a† x. -/
theorem number_creation_apply (h : ⟦a, ad⟧ = 1) :
    (numberOp a ad) (ad x) = ad ((numberOp a ad) x) + ad x := by
  have : ⟦numberOp a ad, ad⟧ x = ad x := LinearMap.congr_fun (number_creation_comm a ad h) x
  simp? [numberOp, comm, sub_eq_iff_eq_add] at this
  rw [numberOp, Module.End.mul_apply, this]
  abel

/-- Applying the creation operator to an eigenstate of the number operator
raises its eigenvalue by 1. -/
theorem number_raise_one (h : ⟦a, ad⟧ = 1) (hx : (numberOp a ad) x = c • x) :
    (numberOp a ad) (ad x) = (c + 1) • (ad x) := by
  rw [number_creation_apply a ad h, hx, map_smul, add_smul, one_smul]

/-- Applying the creation operator k times to an eigenstate of the number
operator raises its eigenvalue by k with k ∈ ℕ. -/
theorem number_raise_k (h : ⟦a, ad⟧ = 1) (hx : (numberOp a ad) x = c • x) (k : ℕ) :
    (numberOp a ad) ((ad^k) x) = (c + k) • ((ad^k) x) := by
  induction k with
  | zero => simp [hx]
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, number_raise_one a ad h ih, add_assoc]
    norm_cast

end Eigenstate

/-!
## Properties involving norm
-/
section Norm

/- Notation for the inner product in a complex Hilbert space. -/
open scoped ComplexInnerProductSpace

def IsAdjoint (a ad : H →ₗ[ℂ] H) : Prop := ∀ x y : H, ⟪a x, y⟫ = ⟪x, ad y⟫

/-- From the definition of the number operator, ⟪x, N x⟫ = ‖a x‖^2. -/
theorem number_inner_eq_norm_annihilation (hadj : IsAdjoint a ad) :
    ⟪x, (numberOp a ad) x⟫ = ‖a x‖^2 := by
  simp? [numberOp]
  rw [← hadj, inner_self_eq_norm_sq_to_K]
  norm_cast

/-- ⟪x, N x⟫ = c * ‖x‖^2 -/
theorem number_inner_eq_norm (hx : (numberOp a ad) x = c • x) :
    ⟪x, (numberOp a ad) x⟫ = c * ‖x‖^2 := by
  rw [hx]
  simp

theorem eigenvalue_norm_sq_eq_norm_sq (hadj : IsAdjoint a ad) (hx : (numberOp a ad) x = c • x) :
    c * ‖x‖^2 = ‖a x‖^2 := calc
  c * ‖x‖^2 = ⟪x, (numberOp a ad) x⟫ := by rw [number_inner_eq_norm a ad hx]
  _ = ‖a x‖^2 := by rw [number_inner_eq_norm_annihilation a ad hadj]

end Norm

/-!
## Prove number operator eigenvalue are real and non-negative
From `number_inner_eq_norm` and `number_inner_eq_norm_annihilation` we can conclude
that the eigenvalue of the number operator is real and non-negative.
-/
section EigenvalueRealNonNeg

/-- Number operator eigenvalue real part is non-negative. -/
theorem eigenvalue_re_nonneg
    (hadj : IsAdjoint a ad) (hx : (numberOp a ad) x = c • x) (h0x : x ≠ 0) :
    0 ≤ c.re := by
  have hre :c.re * ‖x‖ ^ 2 = ‖a x‖ ^ 2 := by
    have := congrArg Complex.re (eigenvalue_norm_sq_eq_norm_sq a ad hadj hx)
    simp? [← Complex.ofReal_pow] at this
    exact this
  have hpos : 0 < ‖x‖^2 := pow_pos (norm_pos_iff.mpr h0x) 2
  nlinarith [hre, hpos]

/-- Number operator eigenvalue has no imaginary part. -/
theorem eigenvalue_im_zero
    (hadj : IsAdjoint a ad) (hx : (numberOp a ad) x = c • x) (h0x : x ≠ 0) :
    c.im = 0 := by
  have him : c.im * ‖x‖^2 = 0 := by
    have := congrArg Complex.im (eigenvalue_norm_sq_eq_norm_sq a ad hadj hx)
    simp? [← Complex.ofReal_pow] at this
    cases this with
    | inl h => rw [h]; simp
    | inr h => exact absurd h h0x
  have hpos : 0 < ‖x‖^2 := pow_pos (norm_pos_iff.mpr h0x) 2
  nlinarith [him, hpos]

end EigenvalueRealNonNeg

/-!
## Existence of a ground state
We can use `number_lower_k` to show that there exists a ground state, i.e., a
eigenstate x₀ such that a x₀ = 0.

The reasoning is simple. Since there is not limit of how many times we can apply
the annihilation operator, if all the eigenvalues of N are non-negative and
N (a^k x) = (c - k) • (a^k x), then c - k ≥ 0 or (a^k x) = 0. Therefore, must
exists k : ℕ, k > c.re such that (a^k x) = 0, i.e., the state is annihilated.
-/
section GroundState

theorem exists_ground_state
    (h : ⟦a, ad⟧ = 1) (hadj : IsAdjoint a ad)
    (hx : (numberOp a ad) x = c • x) :
    ∃ k : ℕ, (a ^ k) x = 0 := by
  -- Let's assume there is no such k.
  by_contra hcon
  push Not at hcon
  -- If there is no k such that (a^k) x = 0, then for all k, 0 ≤ c - k.
  have hbound : ∀ k : ℕ, (k : ℝ) ≤ c.re := by
    intro k
    have hpow := number_lower_k a ad h hx k
    have hnonneg := eigenvalue_re_nonneg a ad hadj hpow (hcon k)
    rw [Complex.sub_re, Complex.natCast_re, sub_nonneg] at hnonneg
    exact hnonneg
  -- But there is always a natural number greater than a real number.
  obtain ⟨k, hk⟩ := exists_nat_gt c.re
  -- Contradiction!
  exact absurd (hbound k) (not_le.mpr hk)

end GroundState

/-!
## Number operator eigenvalues are discrete
From the theorems `number_lower_k` and `number_raise_k`, we know that the
eigenvalues of the number operator are move up and down by a whole unit, which,
by definition, implies the eigenvalues are discrete.

From the theorems `eigenvalue_re_nonnneg` and `eigenvalue_im_zero`, we know that
the eigenvalues of the number operator are non-negative real numbers.

Now, let's prove that the eigenvalues of the number operator are natural numbers
and that the ground state has eigenvalue zero.

Finally, we can prove that every non-negative integer can be realized as an
eigenvalue of the number operator by successively applying the creation operator
to the ground state.
-/
section EigenvalueDiscrete

/-- If x is an eigenstate of the number operator, N x = c • x, then c ∈ ℕ. -/
theorem eigenvalue_mem_nat
    (h : ⟦a, ad⟧ = 1) (hadj : IsAdjoint a ad)
    (h0x : x ≠ 0) (hx : (numberOp a ad) x = c • x) :
    ∃ n : ℕ, c = n := by
  -- To be able to use decidable instances for natural numbers we need to use
  -- classical logic
  classical
  -- Existence of a ground state such that gets annihilated by a, i.e., a|0⟩ = 0.
  have hvanish : ∃ k, (a ^ k) x = 0 := exists_ground_state a ad h hadj hx
  -- k is a non-zero natural number
  have hk : Nat.find hvanish ≠ 0 := by
    intro hz
    have := Nat.find_spec hvanish
    rw [hz] at this
    simp [h0x] at this
  -- There is a p = k-1 such that a^p |x⟩ = |0⟩
  obtain ⟨p, hp⟩ := Nat.exists_eq_succ_of_ne_zero hk
  have hground : (a ^ p) x ≠ 0 := Nat.find_min hvanish (by rw [hp]; simp)
  -- Applying the annihilation operator to the ground state yields zero.
  have haground: a ((a ^ p) x) = 0 := by
    rw [← Module.End.mul_apply, ← pow_succ', Nat.add_one, ← hp]
    exact Nat.find_spec hvanish
  -- N|0⟩ = 0 therefore, N(a^p|x⟩) = 0
  have h0n : (numberOp a ad) ((a ^ p) x) = 0 := by simp [numberOp, haground]
  have hcp : (c - p) • ((a ^ p) x) = 0 := by
    have := number_lower_k a ad h hx p
    rw [h0n] at this
    exact this.symm
  have h1 : c - p = 0 ∨ (a ^ p) x = 0 := smul_eq_zero.mp hcp
  cases h1 with
  | inl hl => rw [sub_eq_zero] at hl; exists p
  | inr hr => exact absurd hr hground

/-- The eigenvalue of a ground state is zero. -/
theorem eigenvalue_ground_state_eq_zero (hax₀ : a x₀ = 0) : (numberOp a ad) x₀ = 0 := by
  simp [numberOp, hax₀]

/-- Every n ∈ ℕ can be realized as an eigenvalue of the number operator by
applying (ad ^ n) to the ground state. -/
theorem eigenvalue_nat_realized (h : ⟦a, ad⟧ = 1) (hax₀ : a x₀ = 0) (n : ℕ) :
    (numberOp a ad) ((ad ^ n) x₀) = n • ((ad ^ n) x₀) := by
  have h1 := eigenvalue_ground_state_eq_zero a ad hax₀
  rw [← zero_smul ℂ x₀] at h1
  have h2 := number_raise_k a ad h h1 n
  simp? [Nat.cast_smul_eq_nsmul] at h2
  exact h2

end EigenvalueDiscrete

end QuantumHarmonicOscillator
