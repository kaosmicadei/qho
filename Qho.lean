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

/-! ## Prologue -/

/- A pre-Hilbert space is normed vector space with norm induced by the inner
product. In the case of quantum mechanics, the pre-Hilbert space is defined over
the complex numbers. -/
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/- Generic eigenstate and eigenvalue of the number operator. -/
variable {x : H} {c : ℂ}

/- For simplicity we use the ladder operators as opaque variable. Ladder
operators are ℂ-linear maps on the Hilbert space H. `H →ₗ[ℂ] H`. On Mathlib,
`Module.End ℂ H` is an abbreviation for `H →ₗ[ℂ] H`. `Module` here stands for the
generalisation of the vector space defined over a ring, and `End` stands for
endomorphism. -/
variable (a ad : Module.End ℂ H)

/- Open the notation for the inner product -/
open scoped ComplexInnerProductSpace

/- The ladder operators a and a† are adjoint to each other. -/
def IsAdjoint (a ad : Module.End ℂ H) : Prop := ∀ x y : H, ⟪a x, y⟫ = ⟪x, ad y⟫

/-- Adjoint of ladder operators is symmetric. -/
theorem IsAdjoint.symm (h : IsAdjoint a ad) : IsAdjoint ad a := by
  intro x y
  -- Conjugate symmetry of the inner product: ⟪x, y⟫* = ⟪y, x⟫
  have conjugate := congrArg (starRingEnd ℂ) (h y x)
  rw [inner_conj_symm, inner_conj_symm] at conjugate
  exact conjugate.symm

/-!
## Canonical commutation relation
The ladder operators satisfy the canonical commutation relation ⟦a, a†⟧ = 1.

Being the number operator defined as N = a†·a, it satisfies the commutation
relations:
* [N, a] = -a,
* [N, a†] = a†.
-/
section CCR

/-- Number operator defined as N = a†·a. -/
def numberOp : Module.End ℂ H := ad * a

/-- The commutation between the ladder operators is passed as a hypothesis since
they are treated as opaque variables. -/
theorem comm_number_lower (h : ⁅a, ad⁆ = 1) : ⁅numberOp a ad, a⁆ = -a := by
  have h' : a * ad - ad * a = 1 := by rw [← Ring.lie_def, h]
  unfold numberOp
  rw [Ring.lie_def]
  have : ad * a * a - a * (ad * a) = -(a * ad - ad * a) * a := by noncomm_ring
  rw [this, h', neg_one_mul]

/-- The commutation between the ladder operators is passed as a hypothesis because
they are treated as opaque variables. -/
theorem comm_number_raise (h : ⁅a, ad⁆ = 1) : ⁅numberOp a ad, ad⁆ = ad := by
  have h' : a * ad - ad * a = 1 := by rw [← Ring.lie_def, h]
  unfold numberOp
  rw [Ring.lie_def]
  have : ad * a * ad - ad * (ad * a) = ad * (a * ad - ad * a):= by noncomm_ring
  rw [this, h', mul_one]

end CCR

/-!
## Ladder operators application
Assume x is an eigenstate of the number operator with eigenvalue c, i.e.,
N x = c • x. We use the commutation relations of the ladder operators to derive
the properties of the action of the ladder operators on these eigenstates.
-/
section LadderOperatorsApplication

/-- N (a x) = a (N x) - a x. -/
theorem number_lower_apply (h : ⁅a, ad⁆ = 1) :
    (numberOp a ad) (a x) = a ((numberOp a ad) x) - a x := by
  have := LinearMap.congr_fun (comm_number_lower a ad h) x
  simp? [Ring.lie_def, numberOp, sub_eq_iff_eq_add] at this
  simp [numberOp, Module.End.mul_apply, this]
  abel

/-- Applying the annihilation operator to an eigenstate of the number operator
lowers its eigenvalue by 1. -/
theorem number_lower_eq_lower_one (h : ⁅a, ad⁆ = 1) (hx : (numberOp a ad) x = c • x) :
    numberOp a ad (a x) = (c - 1) • (a x) := by
  rw [number_lower_apply a ad h, hx, map_smul, sub_smul, one_smul]

/-- Applying the annihilation operator k times to an eigenstate of the number
operator lowers its eigenvalue by k with k ∈ ℕ. -/
theorem number_lower_eq_lower_k (h : ⁅a, ad⁆ = 1) (hx : (numberOp a ad) x = c • x) (k : ℕ) :
    numberOp a ad ((a ^ k) x) = (c - k) • ((a ^ k) x) := by
  induction k with
  | zero => simp [hx]
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, number_lower_eq_lower_one a ad h ih, sub_sub]
    norm_cast

/-- N (ad x) = ad (N x) + ad x. -/
theorem number_raise_apply (h : ⁅a, ad⁆ = 1) :
    (numberOp a ad) (ad x) = ad ((numberOp a ad) x) + ad x := by
  have := LinearMap.congr_fun (comm_number_raise a ad h) x
  simp? [Ring.lie_def, numberOp, sub_eq_iff_eq_add] at this
  simp [numberOp, Module.End.mul_apply, this]
  abel

/-- Applying the creation operator to an eigenstate of the number operator
raises its eigenvalue by 1. -/
theorem number_raise_eq_raise_one (h : ⁅a, ad⁆ = 1) (hx : (numberOp a ad) x = c • x) :
    (numberOp a ad) (ad x) = (c + 1) • (ad x) := by
  rw [number_raise_apply a ad h, hx, map_smul, add_smul, one_smul]

/-- Applying the creation operator k times to an eigenstate of the number
operator raises its eigenvalue by k with k ∈ ℕ. -/
theorem number_raise_eq_raise_k (h : ⁅a, ad⁆ = 1) (hx : (numberOp a ad) x = c • x) (k : ℕ) :
    numberOp a ad ((ad ^ k) x) = (c + k) • ((ad ^ k) x) := by
  induction k with
  | zero => simp [hx]
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, number_raise_eq_raise_one a ad h ih, add_assoc]
    norm_cast

end LadderOperatorsApplication

/-!
## Number operators eigenvalues are real and non-negative.
-/
section EigenvaluesRealNonNegative

/-- ⟪x, N x⟫ = c * ‖x‖^2 -/
theorem inner_number_eq_mul_norm (hx : (numberOp a ad) x = c • x) :
    ⟪x, (numberOp a ad) x⟫ = c * ‖x‖^2 := by
  simp [hx]

/-- From the definition of the number operator, ⟪x, N x⟫ = ‖a x‖^2. -/
theorem inner_number_eq_norm_lower (hadj : IsAdjoint a ad) :
    ⟪x, (numberOp a ad) x⟫ = ‖a x‖^2 := by
  simp only [numberOp, Module.End.mul_apply]
  rw [← hadj, inner_self_eq_norm_sq_to_K]
  norm_cast

theorem norm_lower_eq_mul_norm
    (hadj : IsAdjoint a ad) (hx : (numberOp a ad) x = c • x) :
    ‖a x‖^2 = c * ‖x‖^2 := calc
      ‖a x‖^2 = ⟪x, (numberOp a ad) x⟫ := (inner_number_eq_norm_lower a ad hadj).symm
      _ = c * ‖x‖^2 := inner_number_eq_mul_norm a ad hx

/-- Since c * ‖x‖^2 = ‖a x‖^2, and ‖x‖^2 and ‖a x‖^2 are real numbers, then c must be
a real number. -/
theorem eigenvalue_im_zero
    (hadj : IsAdjoint a ad) (hx : (numberOp a ad) x = c • x) (h0x : x ≠ 0) :
    c.im = 0 := by
  have him : c.im * ‖x‖^2 = 0 := by
    have := congrArg Complex.im (norm_lower_eq_mul_norm a ad hadj hx)
    simp? [← Complex.ofReal_pow] at this
    cases this with
    | inl hl => simp [hl]
    | inr hr => exact absurd hr h0x
  have hpos : 0 < ‖x‖^2 := pow_pos (norm_pos_iff.mpr h0x) 2
  nlinarith

/-- For x ≠ 0, c = ‖a x‖^2 / ‖x‖^2 implies that c must be non-negative. -/
theorem eigenvalue_nonneg
    (hadj : IsAdjoint a ad) (hx : (numberOp a ad) x = c • x) (h0x : x ≠ 0) :
    0 ≤ c.re := by
  have hr : ‖a x‖^2 = c.re * ‖x‖^2 := by
    have := congrArg Complex.re (norm_lower_eq_mul_norm a ad hadj hx)
    simp? [← Complex.ofReal_pow] at this
    exact this
  have hpos : 0 < ‖x‖^2 := pow_pos (norm_pos_iff.mpr h0x) 2
  nlinarith [hr, hpos]

end EigenvaluesRealNonNegative

/-!
## Existence of a ground state
We can use `number_lower_eq_lower_k` to show that there exists a ground state,
i.e., a eigenstate x₀ such that a x₀ = 0.

The reasoning is simple. Since there is not limit of how many times we can apply
the annihilation operator, if all the eigenvalues of N are non-negative and
N (a^k x) = (c - k) • (a^k x) for any x ≠ 0, then either for all k:ℕ, c - k ≥ 0
or exists k:ℕ such that (a^k x) = 0.
-/
section GroundState

/-- There is an enough number of applications of the lower operator that vanishes
any eigenstate. -/
theorem lower_terminates
    (h : ⁅a, ad⁆ = 1) (hadj : IsAdjoint a ad)
    (hx : (numberOp a ad) x = c • x) :
    ∃ k : ℕ, (a ^ k) x = 0 := by
  -- Let's assume there is no such k.
  by_contra hcon
  push Not at hcon
  -- If there is no k such that (a^k) x = 0, then for all k, 0 ≤ c - k.
  have hle : ∀ k : ℕ, k ≤ c.re := by
    intro k
    have hpow := number_lower_eq_lower_k a ad h hx k
    have hnonneg := eigenvalue_nonneg a ad hadj hpow (hcon k)
    simp? at hnonneg
    exact hnonneg
  -- But there is always a natural number greater than a real number.
  obtain ⟨k, hk⟩ := exists_nat_gt c.re
  -- Contradiction!
  exact absurd (hle k) (not_le.mpr hk)

theorem exists_ground_state
    (h : ⁅a, ad⁆ = 1) (hadj : IsAdjoint a ad)
    (hx : (numberOp a ad) x = c • x) (h0x : x ≠ 0) :
    ∃ k : ℕ, (a ^ k) x ≠ 0 ∧ a ((a ^ k) x) = 0 := by
  classical
  have terminates : ∃ k : ℕ, (a ^ k) x = 0 := lower_terminates a ad h hadj hx
  -- k is a non-zero natural number
  have hk : Nat.find terminates ≠ 0 := by
    intro hcontra
    have := Nat.find_spec terminates
    rw [hcontra] at this
    simp? at this
    exact h0x this
  -- There is a p = k-1 such that x₀ = (a^p) x ≠ 0.
  obtain ⟨p, hp⟩ := Nat.exists_eq_succ_of_ne_zero hk
  have ground : (a^p) x ≠ 0 := Nat.find_min terminates (by simp [hp])
  -- Applying the annihilation operator to the ground state yields zero.
  have vanish : a ((a^p) x) = 0 := by
    rw [← Module.End.mul_apply, ← pow_succ', Nat.add_one, ← hp]
    exact Nat.find_spec terminates
  exact ⟨p, ground, vanish⟩

end GroundState

/-!
## Creation operator never vanishes
Applying the creation operator any number of times to a non-zero state never
results in zero.
-/
section CreationOperatorNeverVanish

theorem inner_lower_raise_eq_norm_raise (hadj : IsAdjoint a ad) (x : H) :
    ⟪x, (a * ad) x⟫ = ‖ad x‖^2 := by
    rw [Module.End.mul_apply, ← hadj.symm, inner_self_eq_norm_sq_to_K]
    norm_cast

theorem inner_lower_raise_eq_norm_add
    (h : ⁅a, ad⁆ = 1) (hadj : IsAdjoint a ad) (x : H) :
    ⟪x, (a * ad) x⟫ = ‖x‖^2 + ‖a x‖^2 := by
    have h' : a * ad = 1 + ad * a := by
      rw [Ring.lie_def, sub_eq_iff_eq_add] at h
      exact h
    simp? [h']
    rw [← hadj, inner_self_eq_norm_sq_to_K]
    norm_cast

theorem norm_raise_eq_norm_add_norm
    (h : ⁅a, ad⁆ = 1) (hadj : IsAdjoint a ad) (x : H) :
    ‖ad x‖^2 = ‖x‖^2 + ‖a x‖^2 := by
  have := inner_lower_raise_eq_norm_add a ad h hadj x
  rw [inner_lower_raise_eq_norm_raise a ad hadj x] at this
  exact_mod_cast this

/-- Apply the creation operator to a non-zero state yields a non-zero state. -/
theorem raise_apply_not_zero
    (h : ⁅a, ad⁆ = 1) (hadj : IsAdjoint a ad) (h0x : x ≠ 0) :
    ad x ≠ 0 := by
  intro hcontra
  have hnorm := norm_raise_eq_norm_add_norm a ad h hadj x
  have hpos : 0 < ‖x‖^2 := pow_pos (norm_pos_iff.mpr h0x) 2
  have hpos' : 0 < ‖ad x‖^2 := by rw [hnorm]; nlinarith [hpos]
  simp [hcontra] at hpos'

/-- Successive application of the raising operator on a non-zero state never
vanishes. -/
theorem raise_apply_k_not_zero
    (h : ⁅a, ad⁆ = 1) (hadj : IsAdjoint a ad) (h0x : x ≠ 0) :
    ∀ k : ℕ, (ad ^ k) x ≠ 0 := by
    intro k
    induction k with
    | zero => simp [h0x]
    | succ k ih =>
      rw [pow_succ', Module.End.mul_apply]
      exact raise_apply_not_zero a ad h hadj ih

end CreationOperatorNeverVanish

/-!
## Number operator eigenvalues are discrete
From the theorems `number_lower_eq_lower_k` and `number_raise_eq_raise_k`, we
know that the eigenvalues of the number operator are move up and down by a whole
unit, which, by definition, implies the eigenvalues are discrete.

From the theorems `eigenvalue_nonnneg` and `eigenvalue_im_zero`, we know that
the eigenvalues of the number operator are non-negative real numbers.

Now, let's prove that the eigenvalues of the number operator are natural numbers
and that the ground state has eigenvalue zero.

Finally, we can prove that every non-negative integer can be realized as an
eigenvalue of the number operator by successively applying the creation operator
to the ground state.
-/
section EigenvaluesAreDiscrete

/-- If x is an eigenstate of the number operator, N x = c • x, then c ∈ ℕ. -/
theorem eigenvalue_mem_nat
    (h : ⁅a, ad⁆ = 1) (hadj : IsAdjoint a ad)
    (h0x : x ≠ 0) (hx : (numberOp a ad) x = c • x) :
    ∃ n : ℕ, c = n := by
  -- To be able to use decidable instances for natural numbers we need to use
  -- classical logic
  obtain ⟨p, ground, aground⟩ := exists_ground_state a ad h hadj hx h0x
  have nground : (numberOp a ad) ((a^p) x) = 0 := by simp [numberOp, aground]
  have heq_zero : (c - p) • ((a^p) x) = 0 := by
    have := number_lower_eq_lower_k a ad h hx p
    rw [nground] at this
    exact this.symm
  cases smul_eq_zero.mp heq_zero with
  | inl hl => rw [sub_eq_zero] at hl; exists p
  | inr hr => exact absurd hr ground

/-- The eigenvalue of a ground state is zero. -/
theorem number_eq_zero_of_lower (hax₀ : a x₀ = 0) :
    (numberOp a ad) x₀ = 0 := by
  simp only [numberOp, Module.End.mul_apply, hax₀, map_zero]

/-- Every n:ℕ can be realized as an eigenvalue of the number operator by
applying (ad ^ n) to the ground state. -/
theorem eigenvalue_nat_realized (h : ⁅a, ad⁆ = 1) (hax₀ : a x₀ = 0) (n : ℕ) :
    (numberOp a ad) ((ad ^ n) x₀) = n • ((ad ^ n) x₀) := by
  have h0 := number_eq_zero_of_lower a ad hax₀
  rw [← zero_smul ℂ x₀] at h0
  have hn := number_raise_eq_raise_k a ad h h0 n
  simp only [zero_add, Nat.cast_smul_eq_nsmul] at hn
  exact hn

/-- Given any eigenstate x≠0, every n:ℕ can be realized as an eigenvalue of the
number operator. -/
theorem number_eq_nat_realized (h : ⁅a, ad⁆ = 1) (hadj : IsAdjoint a ad)
    (hx : (numberOp a ad) x = c • x) (h0x : x ≠ 0) (n : ℕ) :
    ∃ y : H, y ≠ 0 ∧ (numberOp a ad) y = n • y := by
  obtain ⟨p, ground, vanish⟩ := exists_ground_state a ad h hadj hx h0x
  have eigenvalue := eigenvalue_nat_realized a ad h vanish n
  have raise := raise_apply_k_not_zero a ad h hadj ground n
  exists ((ad ^ n) ((a ^ p) x))

end EigenvaluesAreDiscrete

end QuantumHarmonicOscillator
