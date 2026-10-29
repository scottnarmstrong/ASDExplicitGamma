module

public import ASDExplicitGamma.Triadic.DiagStencilCertificates

/-! Centered cell moments of the nodal stencil. -/

@[expose] public section

namespace ASDExplicitGamma.Triadic

noncomputable section

theorem diagStencilAdjoint_involutive (p : DiagStencil) :
    diagStencilAdjoint (diagStencilAdjoint p) = p := by
  induction p using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | single g c => simp [diagStencilAdjoint]

theorem diagStencilSquare_adjoint (p : DiagStencil) :
    diagStencilSquare (diagStencilAdjoint p) = diagStencilSquare p := by
  rw [diagStencilSquare, diagStencilAdjoint_involutive]
  exact mul_comm _ _

theorem diagStencilSquare_smul (c : ℚ) (p : DiagStencil) :
    diagStencilSquare (c • p) = (c*c) • diagStencilSquare p := by
  simp only [diagStencilSquare, map_smul, smul_mul_assoc, mul_smul_comm, smul_smul]

/-- Centered variation of the nodal multiplier across a source cell. -/
def diagStencilV (g : ℤ × ℤ) : DiagStencil :=
  (-2:ℚ) • (diagStencilAdjoint (diagStencilAverage g) * diagStencilDifference g)

theorem diagStencilV_atoms (g : ℤ × ℤ) :
    diagStencilV g = (1/2:ℚ) • (diagStencilAtom g - diagStencilAtom (-g)) := by
  unfold diagStencilV diagStencilAverage diagStencilDifference
  simp only [map_smul, map_add, map_one, diagStencilAdjoint_atom,
    smul_mul_assoc, mul_smul_comm, smul_smul, mul_sub, add_mul, one_mul,
    mul_one, diagStencilAtom_inverse, smul_sub, smul_add]
  module

theorem diagStencilSquare_V (g : ℤ × ℤ) :
    diagStencilSquare (diagStencilV g) = (4:ℚ) • (diagStencilU g * (1-diagStencilU g)) := by
  unfold diagStencilV
  rw [diagStencilSquare_smul, diagStencilSquare_mul, diagStencilSquare_adjoint,
    diagStencilSquare_average, diagStencilSquare_difference]
  norm_num

theorem diagStencilAdjoint_U (g : ℤ × ℤ) :
    diagStencilAdjoint (diagStencilU g) = diagStencilU g := by
  unfold diagStencilU
  rw [map_mul, diagStencilAdjoint_involutive, mul_comm]

theorem diagStencilSquare_U (g : ℤ × ℤ) :
    diagStencilSquare (diagStencilU g) = diagStencilU g ^ 2 := by
  rw [diagStencilSquare, diagStencilAdjoint_U, pow_two]

/-- The four centered coefficients give exactly the integrated residual square. -/
theorem diagStencilL_moments (g h : ℤ × ℤ) :
    diagStencilSquare (diagStencilU g * diagStencilU h - 1) +
      (1/12:ℚ) • diagStencilSquare (diagStencilV g * diagStencilU h) +
      (1/12:ℚ) • diagStencilSquare (diagStencilU g * diagStencilV h) +
      (1/144:ℚ) • diagStencilSquare (diagStencilV g * diagStencilV h) =
        diagStencilL (diagStencilU g) (diagStencilU h) := by
  have hc : diagStencilSquare (diagStencilU g * diagStencilU h - 1) =
      (diagStencilU g * diagStencilU h - 1)^2 := by
    simp only [diagStencilSquare, map_sub, map_mul, map_one, diagStencilAdjoint_U, pow_two]
  rw [hc]
  simp only [diagStencilSquare_mul, diagStencilSquare_U, diagStencilSquare_V]
  unfold diagStencilL diagStencilM
  simp only [pow_two, two_mul, add_mul, mul_add, sub_mul, mul_sub, one_mul,
    mul_one, smul_add, smul_sub, smul_mul_assoc, mul_smul_comm, smul_smul]
  ring_nf
  simp only [mul_two]
  module

/-- Integrated gradient square from the three nonconstant centered coefficients. -/
theorem diagStencilH_moments (g h : ℤ × ℤ) :
    diagStencilSquare (diagStencilV g * diagStencilU h) +
      diagStencilSquare (diagStencilU g * diagStencilV h) +
      (1/6:ℚ) • diagStencilSquare (diagStencilV g * diagStencilV h) =
        diagStencilH (diagStencilU g) (diagStencilU h) := by
  simp only [diagStencilSquare_mul, diagStencilSquare_U, diagStencilSquare_V]
  unfold diagStencilH diagStencilM
  simp only [pow_two, mul_add, sub_mul, mul_sub,
    mul_one, smul_sub, smul_mul_assoc, mul_smul_comm, smul_smul]
  ring_nf
  simp only [show (4 : DiagStencil) = 1 + 1 + 1 + 1 by ring, mul_add, mul_one,
    mul_two, smul_add]
  module

/-- The local positive norm of a gradient component uses the exact 1/12
centered variance and the enclosed positive-gradient constant 1/10. -/
theorem diagStencilGradient_moments (g h : ℤ × ℤ) :
    diagStencilSquare (diagStencilV g * diagStencilU h) +
      (11/60:ℚ) • diagStencilSquare (diagStencilV g * diagStencilV h) =
        diagStencilGradient (diagStencilU g) (diagStencilU h) := by
  simp only [diagStencilSquare_mul, diagStencilSquare_U, diagStencilSquare_V]
  unfold diagStencilGradient diagStencilM
  simp only [pow_two, mul_add, sub_mul, mul_sub,
    mul_one, smul_sub, smul_mul_assoc, mul_smul_comm, smul_smul]
  ring_nf
  simp only [show (4 : DiagStencil) = 1 + 1 + 1 + 1 by ring, mul_add, mul_one,
    smul_add]
  module

end

end ASDExplicitGamma.Triadic
