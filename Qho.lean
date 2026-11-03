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

theorem comm_numberOp_annihilation (h : ⟦a, ad⟧ = 1) : ⟦numberOp a ad, a⟧ = -a := by
  unfold numberOp
  rw [comm_mul_left, comm_skew ad a, comm_self, h, mul_zero, zero_add, neg_one_mul]

theorem comm_numberOp_creation (h : ⟦a, ad⟧ = 1) : ⟦numberOp a ad, ad⟧ = ad := by
  unfold numberOp
  rw [comm_mul_left, comm_self, h, mul_one, zero_mul, add_zero]

end NumberOperator

section InnerProduct

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable (a ad : Module.End ℂ H)

open scoped InnerProductSpace

def IsAdjoint (a ad : Module.End ℂ H) : Prop := ∀ x y : H, ⟪a x, y⟫_ℂ = ⟪x, ad y⟫_ℂ

theorem numberOp_eq_ladder (h : IsAdjoint a ad) (x : H) :
    ⟪x, numberOp a ad x⟫_ℂ = ⟪a x, a x⟫_ℂ := by
  unfold numberOp
  rw [h, Module.End.mul_apply]

end InnerProduct

section HarmonicOscillator

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable (a ad : Module.End ℂ H)

open scoped InnerProductSpace

/-- N(a|x⟩) = a(N|x⟩) - a|x⟩ -/
theorem numberOp_annihilation_apply (h : ⟦a, ad⟧ = 1) (x : H) :
    (numberOp a ad) (a x) = a ((numberOp a ad) x) - a x := by
  unfold numberOp
  have h1 := LinearMap.congr_fun (comm_numberOp_annihilation a ad h) x
  simp? [comm, numberOp] at h1
  rw [sub_eq_iff_eq_add] at h1
  simp [h1]
  abel

/-- N(a|x⟩) = (c-1)•(a|x⟩) -/
theorem numberOp_lower
    (h : ⟦a, ad⟧ = 1) {x : H} {c : ℂ}
    (hx : (numberOp a ad) x = c • x) :
    (numberOp a ad) (a x) = (c - 1) • (a x) := by
  rw [numberOp_annihilation_apply a ad h, hx, map_smul, sub_smul, one_smul]

/- Useful lemma: N(a^k |x⟩) = (c - k) • (a^k |x⟩) -/
theorem numberOp_annihilation_pow
    (h : ⟦a, ad⟧ = 1) {x : H} {c : ℂ}
    (hx : (numberOp a ad) x = c • x) (k : ℕ) :
    (numberOp a ad) ((a ^ k) x) = (c - k) • ((a ^ k) x) := by
  induction k with
  | zero => simp [hx]
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, numberOp_lower a ad h ih, sub_sub]
    push_cast
    rfl

/-- ⟪x,Nx⟫ = c•⟪x,x⟫ = ⟪a x,a x⟫ = ‖a x‖² ≥ 0 → c ∈ ℝ+ -/
theorem numberOp_eigenvalue_re_nonneg
    (hadj : IsAdjoint a ad) {x : H} {c : ℂ}
    (hx : (numberOp a ad) x = c • x) (h0x : x ≠ 0) :
    0 ≤ c.re := by
  have hid : c * ⟪x, x⟫_ℂ = ⟪a x, a x⟫_ℂ :=
    calc
      c * ⟪x, x⟫_ℂ = ⟪x, (numberOp a ad) x⟫_ℂ := by rw [hx]; simp
      _ = ⟪a x, a x⟫_ℂ := by rw [numberOp_eq_ladder a ad hadj x]
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at hid
  have hnorm : c.re * ‖x‖^2 = ‖a x‖^2 := by
    have := congrArg Complex.re hid
    simp? [← Complex.ofReal_pow] at this
    exact this
  have hpos : 0 < ‖x‖^2 := pow_pos (norm_pos_iff.mpr h0x) 2
  nlinarith [hnorm, hpos]

theorem numberOp_eigenvalue_nat
    (h : comm a ad = 1) (hadj : IsAdjoint a ad)
    {x : H} {c : ℂ} (h0x : x ≠ 0) (hx : (numberOp a ad) x = c • x) :
    ∃ n : ℕ, c = n := by
  classical
  have ha0x : (a ^ 0) x ≠ 0 := by simp [h0x]
  -- existence of a ground state, |0⟩
  have hground : ∃ k : ℕ, (a ^ k) x = 0 := by
    by_contra hcon
    push Not at hcon
    have hupper : ∀ k : ℕ, (k : ℝ) ≤ c.re := by
      intro k
      have hpow := numberOp_annihilation_pow a ad h hx k
      have hnonneg := numberOp_eigenvalue_re_nonneg a ad hadj hpow (hcon k)
      rw [Complex.sub_re, Complex.natCast_re, sub_nonneg] at hnonneg
      exact hnonneg
    obtain ⟨k, hk⟩ := exists_nat_gt c.re
    exact absurd (hupper k) (not_le.mpr hk)
  -- find a ground state
  have hzero : Nat.find hground ≠ 0 := by
    intro hz
    have := Nat.find_spec hground
    rw [hz] at this
    exact ha0x this
  -- the last non-zero state is the one above the ground state, |1⟩
  obtain ⟨p, hp⟩ := Nat.exists_eq_succ_of_ne_zero hzero
  have hone : (a ^ p) x ≠ 0 := Nat.find_min hground (by rw [hp]; simp)
  have haone : a ((a ^ p) x) = 0 := by
    rw [← Module.End.mul_apply, ← pow_succ', Nat.add_one, ← hp]
    exact Nat.find_spec hground
  have h0n : (numberOp a ad) ((a ^ p) x) = 0 := by
    simp [numberOp, haone]
  have h1 := numberOp_annihilation_pow a ad h hx p
  rw [h0n] at h1
  have h2 := smul_eq_zero.mp h1.symm
  rw [sub_eq_zero] at h2
  exists p
  cases h2 with
  | inl h => exact h
  | inr h => exact absurd h hone

end HarmonicOscillator

end Quantum
