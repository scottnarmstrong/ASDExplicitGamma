module

public import ASDExplicitGamma.Gaussian.SupMeanKernelJet
public import ASDExplicitGamma.Gaussian.SupMeanProductCovariance
public import ASDExplicitGamma.Gaussian.Q3KernelCovariance

/-! The genuine white-noise kernel jets have the exact differentiated product covariance. -/
@[expose] public section
namespace ASDExplicitGamma.Gaussian
open Homogenization ASDExplicitGamma.Model
open scoped RealInnerProductSpace
noncomputable section

/-- The complete gradient/Hessian Gram matrix of the actual Hilbert convolution
factor, at arbitrary points and with every cross-jet row retained. -/
theorem supMean_kernel_jet_covariance (β : ℝ) (L : {l : ℝ // 0 < l})
    (o p : Q3SpatialJet) (x y : Vec 2) :
    ⟪q3Section β L (supMeanKernelJetIndex o) x,
      q3Section β L (supMeanKernelJetIndex p) y⟫ =
        q3ScaledJetCovariance (β^2) L.val o p x y := by
  have hp (z : Vec 2) : shellObservationApply (supMeanJetObservation p y)
      (fun w => β^2*q3Cov ((z 0-w 0)/L.val)*q3Cov ((z 1-w 1)/L.val)) =
        ⟪q3Section β L (supMeanKernelJetIndex p) y, q3Section β L h3Zero z⟫ := by
    have hf : (fun w => β^2*q3Cov ((z 0-w 0)/L.val)*q3Cov ((z 1-w 1)/L.val)) =
        q3Convolution β L h3Zero (q3Section β L h3Zero z) := by
      funext w
      exact (q3Section_covariance β L z w).symm
    rw [hf, supMean_kernel_jet_observation]
    exact real_inner_comm _ _
  rw [← supMean_product_covariance_observations (β^2) L.val o p x y]
  simp only [hp]
  change _ = shellObservationApply (supMeanJetObservation o x)
    (q3Convolution β L h3Zero (q3Section β L (supMeanKernelJetIndex p) y))
  rw [supMean_kernel_jet_observation]
  exact real_inner_comm _ _

end
end ASDExplicitGamma.Gaussian
