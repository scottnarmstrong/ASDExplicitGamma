module

public import ASDExplicitGamma.Gaussian.SupMeanJetObservation

/-! Exact identification of the stored derivative covariance with the physical q3 jet matrix. -/
@[expose] public section
namespace ASDExplicitGamma.Gaussian
open Homogenization ASDExplicitGamma.Model Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3 MeasureTheory
noncomputable section

/-- All mixed value, gradient and Hessian covariances of the actual shell agree
with the literal differentiated product covariance at the physical shell scale. -/
theorem supMean_shell_coordinate_covariance (M : ABKModel 2) (h : ℝ)
    (hM : PlanarQ3Gaussian M h) (k : ℤ) (o p : Q3SpatialJet) (x y : Vec 2) :
    (∫ j, shellDerivativeEval (supMeanJetObservation o x) j *
      shellDerivativeEval (supMeanJetObservation p y) j
        ∂(ShellField.shellMarginalLaw M.P k).toMeasure) =
      q3ScaledJetCovariance (h^2*(3:ℝ)^(2*M.gamma*(k:ℝ))) ((3:ℝ)^k) o p x y := by
  rw [q3Shell_stored_derivative_covariance M h hM]
  let A := h^2*(3:ℝ)^(2*M.gamma*(k:ℝ))
  let c := ((3:ℝ)^k)⁻¹
  have hk (z w : Vec 2) : q3ShellCovariance M h k z w = A*supMeanProductJet 0 0 c z w := by
    simp only [q3ShellCovariance, supMeanProductJet, iteratedDeriv_zero, Pi.sub_apply, A, c]
    ring
  unfold q3ShellDerivativeCovariance
  simp only [hk, supMean_jet_observation_const_mul, supMean_jet_observation_right,
    supMean_jet_observation_left]
  unfold q3ScaledJetCovariance
  rw [q3CovariancePartial_eq]
  have hneg : (-c)^p.order = (-1:ℝ)^p.order*c^p.order := by
    rw [← mul_pow]
    congr 1
    ring
  rw [hneg]
  simp only [supMeanProductJet, A, c, inv_pow, div_eq_mul_inv, pow_add]
  ring_nf

end
end ASDExplicitGamma.Gaussian
