module

public import ASDExplicitGamma.Native.ParentBoundaryValueVariance
public import ASDExplicitGamma.Native.ParentBoundaryCovarianceGradient
public import ASDExplicitGamma.Triadic.DiagEnergyCongr

/-! Honest H1 representatives of the actual centered covariance fields.
The parent mean is constant and removes no derivative contribution. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Scalar ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Triadic ASDExplicitGamma.Main ASDExplicitGamma.Response
noncomputable section

local instance parentBoundaryCenteredFiniteMeasure (Q : TriadicCube 2) :
    IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
  (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume

/-- The complete full-minus covariance minus its ACTUAL parent mean. -/
def parentBoundaryCenteredMinusH1 (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0<l}) (i k : Fin 2) : H1Function (openCubeSet Q) :=
  parentBoundaryMinusFullCovarianceH1 Q b L i k-
    H1Function.const (parentBoundaryFlatMean Q b L false i k)

/-- The representative agrees with AN's actual centered covariance. -/
theorem parent_boundary_centered_h1_ae (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0<l}) (i k : Fin 2) :
    (parentBoundaryCenteredMinusH1 Q b L i k).toFun =ᵐ[normalizedCubeMeasure Q]
      fun x => parentBoundaryCenteredCovariance Q b L false i x k := by
  have hh := (parent_boundary_centered_eq_full Q b L i k).symm
  simpa only [parentBoundaryCenteredMinusH1,H1Function.sub_toFun,H1Function.const,
    parent_boundary_full_covariance_h1_toFun,Pi.sub_apply] using hh

/-- Centering does not change the actual covariance gradient. -/
theorem parent_boundary_centered_h1_grad (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0<l}) (i k : Fin 2) :
    (parentBoundaryCenteredMinusH1 Q b L i k).grad =
      (parentBoundaryMinusFullCovarianceH1 Q b L i k).grad := by
  simp [parentBoundaryCenteredMinusH1,H1Function.sub_grad,H1Function.const]

/-- The output quarter turn preserves the complete derivative energy,
with both spatial and load coordinates retained exactly. -/
theorem parent_boundary_centered_gradient_rotation (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0<l}) :
    (∑ i : Fin 2,∑ k : Fin 2,∑ j : Fin 2,energy Q
      (fun x => (parentBoundaryCenteredMinusH1 Q b L i k).grad x j)) =
    ∑ a : Fin 2 × Fin 2,∑ j : Fin 2,energy Q
      (fun x => (parentBoundaryMinusCovarianceH1 Q b L a).grad x j) := by
  simp_rw [parent_boundary_centered_h1_grad]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  have h0 : (parentBoundaryMinusFullCovarianceH1 Q b L i 0).grad=
      -(parentBoundaryMinusCovarianceH1 Q b L (i,1)).grad := by
    funext x j
    simp [parentBoundaryMinusFullCovarianceH1,Fin.sum_univ_two,responsePlanarJ]
  have h1 : (parentBoundaryMinusFullCovarianceH1 Q b L i 1).grad=
      (parentBoundaryMinusCovarianceH1 Q b L (i,0)).grad := by
    funext x j
    simp [parentBoundaryMinusFullCovarianceH1,Fin.sum_univ_two,responsePlanarJ]
  simp only [Fin.sum_univ_two,h0,h1,Pi.neg_apply,energy_neg]
  ring

/-- Sharp complete derivative bound for those actual centered H1 fields. -/
theorem parent_boundary_centered_gradient_bound (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0<l}) :
    (∑ i : Fin 2,∑ k : Fin 2,∑ j : Fin 2,energy Q
      (fun x => (parentBoundaryCenteredMinusH1 Q b L i k).grad x j)) ≤
      (Real.sqrt (b^2*mainFlatSigmaSq b L)+
        Real.sqrt ((mainFlatSigmaSq b L/2)*parentBoundaryDirichletEnergy Q b L))^2 := by
  rw [parent_boundary_centered_gradient_rotation]
  have hh := parent_boundary_minus_covariance_gradient Q b L
  have hs := pow_le_pow_left₀ (Real.sqrt_nonneg _) hh 2
  rwa [Real.sq_sqrt (Finset.sum_nonneg (fun a _ =>
    Finset.sum_nonneg (fun j _ => energy_nonneg Q _)))] at hs

end
end ASDExplicitGamma.Native
