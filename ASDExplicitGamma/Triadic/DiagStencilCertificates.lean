module

public import ASDExplicitGamma.Triadic.DiagStencilPairing

/-! Exact Laurent-square certificates for the sharp nodal multipliers.
These identities are Parseval certificates without a choice of Fourier normalization. -/

@[expose] public section

namespace ASDExplicitGamma.Triadic

noncomputable section

/-- A nonnegative Laurent square. -/
def diagStencilSquare (p : DiagStencil) : DiagStencil := diagStencilAdjoint p * p

theorem diagStencilSquare_mul (p q : DiagStencil) :
    diagStencilSquare (p * q) = diagStencilSquare p * diagStencilSquare q := by
  simp only [diagStencilSquare, map_mul]
  ring

theorem diagStencilSquare_pow (p : DiagStencil) (n : ℕ) :
    diagStencilSquare (p ^ n) = diagStencilSquare p ^ n := by
  simp only [diagStencilSquare, map_pow, mul_pow]

@[simp] theorem diagStencilSquare_average (g : ℤ × ℤ) :
    diagStencilSquare (diagStencilAverage g) = diagStencilU g := rfl

@[simp] theorem diagStencilSquare_difference (g : ℤ × ℤ) :
    diagStencilSquare (diagStencilDifference g) = 1 - diagStencilU g :=
  (diagStencil_complement g).symm

/-- Integrated squared one-dimensional nodal multiplier, M(U)=U(1+2U)/3. -/
def diagStencilM (u : DiagStencil) : DiagStencil := (1/3:ℚ) • u + (2/3:ℚ) • u^2

/-- Cell-integrated residual square. -/
def diagStencilL (u v : DiagStencil) : DiagStencil := 1 - 2*u*v + diagStencilM u*diagStencilM v

/-- The cell-side-scaled squared gradient of the interpolant. -/
def diagStencilH (u v : DiagStencil) : DiagStencil :=
  4*(u*(1-u)*diagStencilM v + v*(1-v)*diagStencilM u)

/-- Algebraic form of the degree-(2,2) Bernstein matrix. -/
theorem diagStencil_bernstein_polynomial (u v : DiagStencil) :
    2 - u - v - diagStencilL u v - (1/10:ℚ) • diagStencilH u v =
      (1-u)^2*(1-v)^2+(1-u)^2*v*(1-v)+u*(1-u)*(1-v)^2+
        (73/45:ℚ) • (u*(1-u)*v*(1-v))+(4/15:ℚ) • (u*(1-u)*v^2)+
        (4/15:ℚ) • (u^2*v*(1-v)) := by
  unfold diagStencilL diagStencilH diagStencilM
  simp only [pow_two, two_mul, add_mul, mul_add, sub_mul, mul_sub,
    one_mul, mul_one, smul_add, smul_sub, smul_mul_assoc, mul_smul_comm, smul_smul]
  ring_nf
  simp only [show (4 : DiagStencil) = 1 + 1 + 1 + 1 by ring, mul_add, mul_one,
    mul_two, smul_add]
  module

/-- The Bernstein polynomial is a sum of actual squared lattice filters. -/
theorem diagStencil_residual_squares (g h : ℤ × ℤ) :
    2 - diagStencilU g - diagStencilU h - diagStencilL (diagStencilU g) (diagStencilU h) -
        (1/10:ℚ) • diagStencilH (diagStencilU g) (diagStencilU h) =
      diagStencilSquare (diagStencilDifference g ^ 2 * diagStencilDifference h ^ 2) +
      diagStencilSquare (diagStencilDifference g ^ 2 * diagStencilAverage h * diagStencilDifference h) +
      diagStencilSquare (diagStencilAverage g * diagStencilDifference g * diagStencilDifference h ^ 2) +
      (73/45:ℚ) • diagStencilSquare
        (diagStencilAverage g * diagStencilDifference g * diagStencilAverage h * diagStencilDifference h) +
      (4/15:ℚ) • diagStencilSquare
        (diagStencilAverage g * diagStencilDifference g * diagStencilAverage h ^ 2) +
      (4/15:ℚ) • diagStencilSquare
        (diagStencilAverage g ^ 2 * diagStencilAverage h * diagStencilDifference h) := by
  rw [diagStencil_bernstein_polynomial]
  simp only [diagStencilSquare_mul, diagStencilSquare_pow,
    diagStencilSquare_average, diagStencilSquare_difference]

/-- Positive-norm gradient multiplier at the exact rational enclosure c₁²≤1/10. -/
def diagStencilGradient (u v : DiagStencil) : DiagStencil :=
  4 * u * (1-u) * (diagStencilM v + (2/5:ℚ) • (v*(1-v)))

/-- The gradient contraction deficit is another sum of Laurent squares. -/
theorem diagStencil_gradient_squares (g h : ℤ × ℤ) :
    4 * (1-diagStencilU g) - diagStencilGradient (diagStencilU g) (diagStencilU h) =
      4 * diagStencilSquare (diagStencilDifference g ^ 2) +
      4 * diagStencilSquare (diagStencilDifference g * diagStencilAverage g * diagStencilDifference h) +
      (16/15:ℚ) • diagStencilSquare
        (diagStencilDifference g * diagStencilAverage g * diagStencilDifference h * diagStencilAverage h) := by
  simp only [diagStencilSquare_mul, diagStencilSquare_pow,
    diagStencilSquare_average, diagStencilSquare_difference]
  unfold diagStencilGradient diagStencilM
  simp only [pow_two, mul_add, sub_mul, mul_sub,
    one_mul, mul_one, smul_sub, mul_smul_comm]
  ring_nf
  simp only [show (4 : DiagStencil) = 1 + 1 + 1 + 1 by ring, mul_add, mul_one,
    smul_add]
  module

end

end ASDExplicitGamma.Triadic
