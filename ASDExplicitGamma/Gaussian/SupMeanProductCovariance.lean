module

public import ASDExplicitGamma.Gaussian.SupMeanJetObservation

/-! Ordinary coordinate derivatives of the scaled product covariance equal its explicit jet formula. -/
@[expose] public section
namespace ASDExplicitGamma.Gaussian
open Homogenization ASDExplicitGamma.Model
noncomputable section

/-- The explicit product jet is the actual nested coordinate derivative of the
covariance, including mixed value and Hessian observations and stationary signs. -/
theorem supMean_product_covariance_observations (v L : ℝ) (o p : Q3SpatialJet) (x y : Vec 2) :
    shellObservationApply (supMeanJetObservation o x) (fun z =>
      shellObservationApply (supMeanJetObservation p y) (fun w =>
        v*q3Cov ((z 0-w 0)/L)*q3Cov ((z 1-w 1)/L))) =
      q3ScaledJetCovariance v L o p x y := by
  let c := L⁻¹
  have hk (z w : Vec 2) : v*q3Cov ((z 0-w 0)/L)*q3Cov ((z 1-w 1)/L) =
      v*supMeanProductJet 0 0 c z w := by
    simp only [supMeanProductJet, iteratedDeriv_zero, c, div_eq_mul_inv]
    ring_nf
  simp only [hk, supMean_jet_observation_const_mul, supMean_jet_observation_right,
    supMean_jet_observation_left]
  unfold q3ScaledJetCovariance
  rw [q3CovariancePartial_eq]
  have hneg : (-c)^p.order = (-1:ℝ)^p.order*c^p.order := by
    rw [← mul_pow]
    congr 1
    ring
  rw [hneg]
  simp only [supMeanProductJet, c, inv_pow, div_eq_mul_inv, pow_add]
  ring_nf

end
end ASDExplicitGamma.Gaussian
