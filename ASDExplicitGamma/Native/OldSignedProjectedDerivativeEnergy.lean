module

public import ASDExplicitGamma.Native.OldSignedPhysicalDerivativeTrace

/-! Exact derivative covariance energies on the actual q3 spectral and
white realizations, before spatial scale factors are applied. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Complex ASDExplicitGamma.Model ASDExplicitGamma.Gaussian ASDExplicitGamma.Scalar
noncomputable section

/-- The trace derivative has the actual scalar first-derivative covariance
energy, including the shell-length factor canceled by dimensionless coordinates. -/
theorem old_signed_white_trace_derivative_energy (b : ℝ) (L : {l : ℝ // 0 < l}) (x : Vec 2) (k : Fin 2) :
    ‖oldSignedProjectedDerivativeWhiteKernel b L x 0 0 k+
      oldSignedProjectedDerivativeWhiteKernel b L x 1 1 k‖^2=b^2*(78/5:ℝ) := by
  rw [old_signed_white_trace_derivative,norm_smul,mul_pow,Real.norm_eq_abs,sq_abs,gaussQ3Section_norm_sq]
  fin_cases k
  all_goals norm_num [lambda8Q3FirstIndex,h3Next,h3Zero,H3Index,q3DerivativeMoment]
  all_goals field_simp [L.2.ne']

end
end ASDExplicitGamma.Native
