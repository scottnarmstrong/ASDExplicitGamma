module

public import ASDExplicitGamma.Native.ParentRowPhysicalScales
public import ASDExplicitGamma.Native.ParentRowBoundary
public import ASDExplicitGamma.Native.BoundaryChargeFlatConstants

/-! Exact shell weights for the two centered parent boundary charges. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization Gaussian Main Triadic Scalar Algsuperdiff.Section3
noncomputable section

/-- The shell's rational parent Dirichlet ratio. -/
def parentRowBoundaryRho (k : ℕ) : ℚ := (26/15)*(1/9)^(k+1)

/-- The rational fine-cell covariance coefficient. -/
def parentRowBoundaryGradient (k : ℕ) : ℚ := (38/125)^2*(156/5)*(1/9)^(k+6)

/-- The two exact source boundary weights, before multiplying shell variance. -/
def parentRowBoundaryWeight (k : ℕ) (plus : Bool) : ℝ :=
  let rho : ℝ := (parentRowBoundaryRho k:ℝ)
  let f := if plus then Real.sqrt 2+2 else Real.sqrt (rho/2)+1
  Real.sqrt (rho-rho^2/2+(parentRowBoundaryGradient k:ℝ)*f^2)

/-- Every shell ratio remains in the physical small-ratio range. -/
theorem parent_row_boundary_rho_range (k : ℕ) :
    0≤(parentRowBoundaryRho k:ℝ) ∧ (parentRowBoundaryRho k:ℝ)≤26/135 := by
  simp only [parentRowBoundaryRho,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat,Rat.cast_pow,Rat.cast_one]
  refine ⟨by positivity,?_⟩
  have hp := pow_le_pow_of_le_one (by norm_num : (0:ℝ)≤1/9) (by norm_num : (1/9:ℝ)≤1)
    (show 1≤k+1 by omega)
  exact (mul_le_mul_of_nonneg_left hp (by norm_num : (0:ℝ)≤26/15)).trans_eq (by norm_num)

/-- Both actual centered covariance clocks fit their distinct stored weights. -/
theorem parent_row_boundary_clock_weight (n : ℤ) (k : ℕ) (plus : Bool) :
    Real.sqrt (parentBoundaryCovarianceClock (cubeScaleFactor (originCube 2 n)) 5
      (q3ModelLength (n+((k+1:ℕ):ℤ))).val)≤parentRowBoundaryWeight k plus := by
  let rho : ℝ := (parentRowBoundaryRho k:ℝ)
  have hrho : 0≤rho ∧ rho≤26/135 := parent_row_boundary_rho_range k
  have hfac : 1+Real.sqrt (rho/2)≤
      (if plus then Real.sqrt 2+2 else Real.sqrt (rho/2)+1) := by
    cases plus
    · simp only [Bool.false_eq_true,ite_false]
      exact le_of_eq (add_comm _ _)
    · simp only [ite_true]
      have hs : Real.sqrt (rho/2)≤1 := Real.sqrt_le_one.mpr (by linarith only [hrho.2])
      linarith only [hs,Real.sqrt_nonneg (2:ℝ)]
  have hc : planarC1^2≤(38/125:ℝ)^2 :=
    pow_le_pow_left₀ (Real.sqrt_nonneg _) (native_boundary_planarC1_le.trans_eq (by norm_num)) 2
  have hf := pow_le_pow_left₀ (add_nonneg (by norm_num : (0:ℝ)≤1) (Real.sqrt_nonneg _)) hfac 2
  have hp := mul_le_mul hc hf (sq_nonneg _) (sq_nonneg _)
  have hscaled := mul_le_mul_of_nonneg_left hp
    (show 0≤(156/5:ℝ)*(1/9:ℝ)^(k+6) by positivity)
  have hratio : (cubeScaleFactor (originCube 2 n)/(q3ModelLength (n+((k+1:ℕ):ℤ))).val)^2=
      (1/9:ℝ)^(k+1) := by
    rw [parent_boundary_model_length_ratio,←pow_mul,Nat.mul_comm,pow_mul]
    norm_num
  have hmesh : (cubeScaleFactor (originCube 2 n)/(3^5*(q3ModelLength (n+((k+1:ℕ):ℤ))).val))^2=
      (1/9:ℝ)^(k+6) := by
    rw [show cubeScaleFactor (originCube 2 n)/(3^5*(q3ModelLength (n+((k+1:ℕ):ℤ))).val)=
      (cubeScaleFactor (originCube 2 n)/3^5)/(q3ModelLength (n+((k+1:ℕ):ℤ))).val by ring,
      parent_row_mesh_length_ratio,←pow_mul,Nat.mul_comm,pow_mul]
    norm_num
  apply Real.sqrt_le_sqrt
  unfold parentBoundaryCovarianceClock
  rw [hratio,hmesh]
  simp only [parentRowBoundaryRho,parentRowBoundaryGradient,Rat.cast_mul,Rat.cast_div,
    Rat.cast_pow,Rat.cast_ofNat,Rat.cast_one] at *
  apply add_le_add le_rfl
  convert hscaled using 1 <;> dsimp only [rho] <;>
    simp only [parentRowBoundaryRho,Rat.cast_mul,Rat.cast_div,Rat.cast_pow,Rat.cast_ofNat,Rat.cast_one] <;> ring

/-- Actual centered beta retains the physical shell variance and its exact
sign-specific source weight. -/
theorem parent_row_shell_beta_weight (n : ℤ) (k : ℕ) (b : ℝ) (plus : Bool) :
    parentRowBeta n 5 b (q3ModelLength (n+((k+1:ℕ):ℤ))) plus≤
      b^2*parentRowBoundaryWeight k plus :=
  (parent_boundary_model_beta_clock n (k+1) 5 (by omega) b plus).trans
    (mul_le_mul_of_nonneg_left (parent_row_boundary_clock_weight n k plus) (sq_nonneg b))

end
end ASDExplicitGamma.Native
