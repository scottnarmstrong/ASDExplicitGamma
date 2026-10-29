module

public import ASDExplicitGamma.Triadic.DiagStencilBounds
public import ASDExplicitGamma.Triadic.DiagStencilMoments

/-! Cell-centered coefficients and sharp nodal interpolation energy bounds. -/

@[expose] public section

namespace ASDExplicitGamma.Triadic

open scoped BigOperators

noncomputable section

/-- The four centered bilinear coefficients of the nodal-average interpolant. -/
def diagNodalCoefficients {G : Type*} [AddCommGroup G]
    (φ : (ℤ × ℤ) →+ G) (g h : ℤ × ℤ) (f : G → ℝ) (a : Fin 4) : G → ℝ :=
  ![diagStencilAction φ (diagStencilU g * diagStencilU h) f,
    diagStencilAction φ (diagStencilV g * diagStencilU h) f,
    diagStencilAction φ (diagStencilU g * diagStencilV h) f,
    diagStencilAction φ (diagStencilV g * diagStencilV h) f] a

/-- Exact residual L² moment plus the rational positive-gradient enclosure. -/
def diagNodalResidualBudget {G : Type*} [AddCommGroup G]
    (φ : (ℤ × ℤ) →+ G) (g h : ℤ × ℤ) (f : G → ℝ) (x : G) : ℝ :=
  let c := diagNodalCoefficients φ g h f
  (c 0 x-f x)^2 + (c 1 x)^2/12 + (c 2 x)^2/12 + (c 3 x)^2/144 +
    ((c 1 x)^2+(c 2 x)^2+(c 3 x)^2/6)/10

/-- Exact positive-gradient budget for the first coordinate. -/
def diagNodalGradientBudget {G : Type*} [AddCommGroup G]
    (φ : (ℤ × ℤ) →+ G) (g h : ℤ × ℤ) (f : G → ℝ) (x : G) : ℝ :=
  let c := diagNodalCoefficients φ g h f
  (c 1 x)^2 + (11/60:ℝ)*(c 3 x)^2

theorem diagNodalResidualBudget_sum {G : Type*} [AddCommGroup G] [Fintype G]
    (φ : (ℤ × ℤ) →+ G) (g h : ℤ × ℤ) (f : G → ℝ) :
    (∑ x, diagNodalResidualBudget φ g h f x) =
      diagStencilQuadratic φ (diagStencilL (diagStencilU g) (diagStencilU h)) f +
      (1/10:ℝ)*diagStencilQuadratic φ (diagStencilH (diagStencilU g) (diagStencilU h)) f := by
  rw [← diagStencilL_moments, ← diagStencilH_moments]
  simp only [diagStencilQuadratic_add, diagStencilQuadratic_smul, diagStencilSquare,
    diagStencilQuadratic_square]
  norm_num only [Rat.cast_div, Rat.cast_ofNat]
  have hsub (x : G) : diagStencilAction φ (diagStencilU g * diagStencilU h - 1) f x =
      diagNodalCoefficients φ g h f 0 x - f x := by
    simp [diagNodalCoefficients]
  simp_rw [hsub]
  dsimp only [diagNodalResidualBudget, diagNodalCoefficients]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem diagNodalGradientBudget_sum {G : Type*} [AddCommGroup G] [Fintype G]
    (φ : (ℤ × ℤ) →+ G) (g h : ℤ × ℤ) (f : G → ℝ) :
    (∑ x, diagNodalGradientBudget φ g h f x) =
      diagStencilQuadratic φ (diagStencilGradient (diagStencilU g) (diagStencilU h)) f := by
  rw [← diagStencilGradient_moments]
  simp only [diagStencilQuadratic_add, diagStencilQuadratic_smul, diagStencilSquare,
    diagStencilQuadratic_square]
  norm_num only [Rat.cast_div, Rat.cast_ofNat]
  simp [diagNodalGradientBudget, diagNodalCoefficients, Finset.sum_add_distrib, Finset.mul_sum]

/-- Sharp half-gain for the residual, expressed in actual cell coefficients. -/
theorem diagNodalResidualBudget_contracts {G : Type*} [AddCommGroup G] [Fintype G]
    (φ : (ℤ × ℤ) →+ G) (g h : ℤ × ℤ) (f : G → ℝ) :
    (∑ x, diagNodalResidualBudget φ g h f x) ≤
      (1/4:ℝ)*∑ x, ((f x-f (x+φ g))^2+(f x-f (x+φ h))^2) := by
  rw [diagNodalResidualBudget_sum]
  apply (diagStencil_residual_contracts φ g h f).trans_eq
  have hid : 2 - diagStencilU g - diagStencilU h =
      (1/4:ℚ) • (4*(1-diagStencilU g)) + (1/4:ℚ) • (4*(1-diagStencilU h)) := by
    simp only [show (4:DiagStencil)=1+1+1+1 by ring, show (2:DiagStencil)=1+1 by ring,
      add_mul, one_mul, smul_add]
    module
  rw [hid, diagStencilQuadratic_add, diagStencilQuadratic_smul, diagStencilQuadratic_smul,
    diagStencil_row_square, diagStencil_row_square]
  norm_num only [Rat.cast_div, Rat.cast_ofNat]
  rw [Finset.sum_add_distrib]
  ring

/-- Constant-one gradient contraction, expressed in actual cell coefficients. -/
theorem diagNodalGradientBudget_contracts {G : Type*} [AddCommGroup G] [Fintype G]
    (φ : (ℤ × ℤ) →+ G) (g h : ℤ × ℤ) (f : G → ℝ) :
    (∑ x, diagNodalGradientBudget φ g h f x) ≤ ∑ x, (f x-f (x+φ g))^2 := by
  rw [diagNodalGradientBudget_sum, ← diagStencil_row_square]
  exact diagStencil_gradient_contracts φ g h f

end

end ASDExplicitGamma.Triadic
