module

public import ASDExplicitGamma.Native.ParentBoundaryGradientClock
public import ASDExplicitGamma.Native.ParentBoundaryInverseBulk

/-! Derivative-only own-native clock for the actual complete flat energy. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Scalar ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Triadic ASDExplicitGamma.Main
noncomputable section

/-- Each actual parent projected mode obeys the derivative-only clock.
The Laplacian is identified with the physical q3 derivative internally. -/
theorem parent_boundary_dirichlet_mode_clock (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0<l}) (n : whiteBasisIndex) :
    oldSignedFlatDirichletModeEnergy Q b L n ≤
      cubeScaleFactor Q^2/(2*Real.pi^2)*∑ i : Fin 2,
        energy Q (lambda8Q3GaussianModeDerivative b L (basisVec i) n) := by
  rw [old_signed_q3_parent_two_load_energy,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hc := parent_boundary_gradient_laplacian_clock Q
    (lambda8Q3GaussianModeParentPotential Q b L (basisVec i) n)
    (lambda8Q3GaussianModeParentHessian Q b L (basisVec i) n)
  apply hc.trans_eq
  apply congrArg (fun z : ℝ => cubeScaleFactor Q^2/(2*Real.pi^2)*z)
  rw [energy_eq_integral_sq,energy_eq_integral_sq]
  apply integral_congr_ae
  filter_upwards [(lambda8Q3GaussianModeParentPotential_spec Q b L (basisVec i) n).2] with x hx
  rw [hx]

/-- The complete two-load physical divergence trace is precisely sigma². -/
theorem parent_boundary_derivative_trace (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0<l}) :
    HasSum (fun n : whiteBasisIndex => ∑ i : Fin 2,
      energy Q (lambda8Q3GaussianModeDerivative b L (basisVec i) n)) (mainFlatSigmaSq b L) := by
  have hs := hasSum_sum (s := Finset.univ) (fun i _ =>
    (lambda8Q3GaussianModeDerivative_energy_tsum Q b L (basisVec i)).1.hasSum)
  simp_rw [(fun i => (lambda8Q3GaussianModeDerivative_energy_tsum Q b L (basisVec i)).2)] at hs
  have he : (∑ i : Fin 2,b^2/L.1^2*(78/5:ℝ)*((basisVec i) 0^2+(basisVec i) 1^2)) =
      mainFlatSigmaSq b L := by
    norm_num [Fin.sum_univ_two,basisVec,Pi.single_apply,mainFlatSigmaSq]
    ring
  rwa [he] at hs

/-- The actual COMPLETE own-native Dirichlet energy has the summable
source clock Y ≤ R² sigma²/(2 pi²), with no projection estimate premise. -/
theorem parent_boundary_dirichlet_energy_clock (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0<l}) :
    parentBoundaryDirichletEnergy Q b L ≤ cubeScaleFactor Q^2/(2*Real.pi^2)*mainFlatSigmaSq b L := by
  have hs := (parent_boundary_derivative_trace Q b L).mul_left (cubeScaleFactor Q^2/(2*Real.pi^2))
  exact ((old_signed_flat_minus_complete_energy Q b L).1.tsum_le_tsum
    (parent_boundary_dirichlet_mode_clock Q b L) hs.summable).trans_eq hs.tsum_eq

/-- Safe rational own-native clock from pi² ≥ 9. The full physical point
variance remains b²; only the parent Dirichlet energy receives this clock. -/
theorem parent_boundary_dirichlet_energy_rational_clock (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0<l}) :
    parentBoundaryDirichletEnergy Q b L ≤
      (26/15:ℝ)*(cubeScaleFactor Q/L.1)^2*b^2 := by
  have hpi : (9:ℝ)≤Real.pi^2 := by nlinarith only [Real.pi_gt_three]
  have hcoeff : (78:ℝ)/(5*Real.pi^2)≤26/15 := by
    apply (div_le_iff₀ (by positivity : (0:ℝ)<5*Real.pi^2)).2
    nlinarith only [hpi]
  apply (parent_boundary_dirichlet_energy_clock Q b L).trans
  calc
    cubeScaleFactor Q^2/(2*Real.pi^2)*mainFlatSigmaSq b L =
        (78/(5*Real.pi^2))*(cubeScaleFactor Q^2*b^2/L.1^2) := by
      unfold mainFlatSigmaSq
      ring
    _ ≤ (26/15:ℝ)*(cubeScaleFactor Q^2*b^2/L.1^2) :=
      mul_le_mul_of_nonneg_right hcoeff (by positivity)
    _ = _ := by rw [div_pow]; ring

end
end ASDExplicitGamma.Native
