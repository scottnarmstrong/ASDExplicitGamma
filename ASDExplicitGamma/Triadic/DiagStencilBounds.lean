module

public import ASDExplicitGamma.Triadic.DiagStencilCertificates

/-! Sharp quadratic-form contraction of the actual nodal lattice multipliers. -/

@[expose] public section

namespace ASDExplicitGamma.Triadic

open scoped BigOperators

noncomputable section

theorem diagStencilQuadratic_nat_mul {G : Type*} [AddCommGroup G] [Fintype G]
    (φ : (ℤ × ℤ) →+ G) (n : ℕ) (p : DiagStencil) (f : G → ℝ) :
    diagStencilQuadratic φ ((n : DiagStencil) * p) f =
      (n : ℝ) * diagStencilQuadratic φ p f := by
  rw [← nsmul_eq_mul, ← Nat.cast_smul_eq_nsmul ℚ, diagStencilQuadratic_smul]
  simp only [Rat.cast_natCast]

theorem diagStencilQuadratic_four_mul {G : Type*} [AddCommGroup G] [Fintype G]
    (φ : (ℤ × ℤ) →+ G) (p : DiagStencil) (f : G → ℝ) :
    diagStencilQuadratic φ (4 * p) f = 4 * diagStencilQuadratic φ p f := by
  simpa only [Nat.cast_ofNat] using diagStencilQuadratic_nat_mul φ 4 p f

/-- The half-gain residual inequality on any finite periodic lattice. -/
theorem diagStencil_residual_contracts {G : Type*} [AddCommGroup G] [Fintype G]
    (φ : (ℤ × ℤ) →+ G) (g h : ℤ × ℤ) (f : G → ℝ) :
    diagStencilQuadratic φ (diagStencilL (diagStencilU g) (diagStencilU h)) f +
      (1/10:ℝ) * diagStencilQuadratic φ (diagStencilH (diagStencilU g) (diagStencilU h)) f ≤
        diagStencilQuadratic φ (2 - diagStencilU g - diagStencilU h) f := by
  have hid := congrArg (fun p => diagStencilQuadratic φ p f) (diagStencil_residual_squares g h)
  have hs (p : DiagStencil) : 0 ≤ diagStencilQuadratic φ (diagStencilSquare p) f :=
    diagStencilQuadratic_square_nonneg φ p f
  have h0 := hs (diagStencilDifference g ^ 2 * diagStencilDifference h ^ 2)
  have h1 := hs (diagStencilDifference g ^ 2 * diagStencilAverage h * diagStencilDifference h)
  have h2 := hs (diagStencilAverage g * diagStencilDifference g * diagStencilDifference h ^ 2)
  have h3 := hs (diagStencilAverage g * diagStencilDifference g * diagStencilAverage h * diagStencilDifference h)
  have h4 := hs (diagStencilAverage g * diagStencilDifference g * diagStencilAverage h ^ 2)
  have h5 := hs (diagStencilAverage g ^ 2 * diagStencilAverage h * diagStencilDifference h)
  simp only [diagStencilQuadratic_add, diagStencilQuadratic_sub,
    diagStencilQuadratic_smul] at hid ⊢
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hid
  linarith only [hid, h0, h1, h2, h3, h4, h5]

/-- Positive-gradient contraction, with the constant-one source row multiplier. -/
theorem diagStencil_gradient_contracts {G : Type*} [AddCommGroup G] [Fintype G]
    (φ : (ℤ × ℤ) →+ G) (g h : ℤ × ℤ) (f : G → ℝ) :
    diagStencilQuadratic φ (diagStencilGradient (diagStencilU g) (diagStencilU h)) f ≤
      diagStencilQuadratic φ (4 * (1-diagStencilU g)) f := by
  have hid := congrArg (fun p => diagStencilQuadratic φ p f) (diagStencil_gradient_squares g h)
  have hs (p : DiagStencil) : 0 ≤ diagStencilQuadratic φ (diagStencilSquare p) f :=
    diagStencilQuadratic_square_nonneg φ p f
  have h0 := hs (diagStencilDifference g ^ 2)
  have h1 := hs (diagStencilDifference g * diagStencilAverage g * diagStencilDifference h)
  have h2 := hs (diagStencilDifference g * diagStencilAverage g * diagStencilDifference h * diagStencilAverage h)
  simp only [diagStencilQuadratic_add, diagStencilQuadratic_sub,
    diagStencilQuadratic_smul, diagStencilQuadratic_four_mul] at hid ⊢
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat] at hid
  linarith only [hid, h0, h1, h2]

/-- The discrete source-row square is exactly the complement of U. -/
theorem diagStencil_row_square {G : Type*} [AddCommGroup G] [Fintype G]
    (φ : (ℤ × ℤ) →+ G) (g : ℤ × ℤ) (f : G → ℝ) :
    diagStencilQuadratic φ (4 * (1-diagStencilU g)) f =
      ∑ x, (f x - f (x + φ g)) ^ 2 := by
  rw [diagStencilQuadratic_four_mul, diagStencil_complement, diagStencilQuadratic_square]
  have heval (x : G) : diagStencilAction φ (diagStencilDifference g) f x =
      (1/2:ℝ) * (f x - f (x + φ g)) := by
    simp [diagStencilDifference, Rat.smul_def]
  simp_rw [heval]
  norm_num only [Nat.cast_ofNat]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

end

end ASDExplicitGamma.Triadic
