module

public import ASDExplicitGamma.Native.ParentBoundaryCommonGeneratorFinite
public import ASDExplicitGamma.Native.ParentBoundaryCommonResponseDirections
public import ASDExplicitGamma.Inverse.PureFluxGeneratorTraceLimit

/-! Complete actual common-center affine-load covariance generators. -/

@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Gaussian Main Model Response Triadic Variational Scalar Inverse
noncomputable section

local instance parentCommonAffineGeneratorMeasure (Q : TriadicCube 2) :
    IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
  (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume

/-- The complete physical affine-load generator, with actual common-center
convolution directions and no covariance-representation or minimizer premise. -/
theorem parent_boundary_common_affine_generator
    (P0 Q : TriadicCube 2) (hQP : cubeSet Q ⊆ cubeSet P0)
    (ν σ b : ℝ) (hν : 0 < ν) (hσ : 0 < σ) (L : {l : ℝ // 0 < l}) (m : ℕ)
    (P : BlockVec 2) (k : ResponseCoefficient (openCubeSet Q))
    (B : ℝ) (hB : 0 ≤ B)
    (hhist : ∀ U ∈ descendantsAtDepth Q m,lemmaVInverseHistory U
      (responseFramePlanarCoefficientField ν σ k) ((3:ℝ)^(1/4:ℝ)) ≤ B) :
    (1/2:ℝ)*modelCovarianceTrace
      (responseFrameEnergyObservable (measurableSet_openCubeSet Q)
        (square_volume_pos Q) ν σ hν hσ P)
      (parentBoundaryCommonResponseDirections P0 Q b L) k ≤
    |σ⁻¹|^2*pureFluxCovarianceMu (parentBoundaryCommonRowCoefficient P0 Q b L m)
      (parentBoundaryCommonFeedbackCoefficient P0 Q b L m)*B^2*
      responseFrameEnergyObservable (measurableSet_openCubeSet Q)
        (square_volume_pos Q) ν σ hν hσ P k := by
  let hv := square_volume_pos Q
  let E := responseFrameEnergyObservable (measurableSet_openCubeSet Q) hv ν σ hν hσ P
  let K := parentBoundaryCommonResponseDirections P0 Q b L
  let enc := @Encodable.encode whiteBasisIndex (Encodable.ofCountable whiteBasisIndex)
  let H := fun l : whiteBasisIndex => K (enc l)
  let g := fun l => pureFluxResponseHessianDiagonal (measurableSet_openCubeSet Q) hv ν σ hν hσ P k (H l)
  let C := |σ⁻¹|^2*pureFluxCovarianceMu (parentBoundaryCommonRowCoefficient P0 Q b L m)
    (parentBoundaryCommonFeedbackCoefficient P0 Q b L m)*B^2*E k
  have hfinite (s : Finset whiteBasisIndex) : (1/2:ℝ)*(∑ l ∈ s,g l) ≤ C :=
    parent_boundary_common_finite_affine_generator P0 Q hQP ν σ b hν hσ L m P k H
      (fun l => parent_boundary_common_response_direction_frame P0 Q b σ L l) B hB hhist s
  have hEd : ContDiff ℝ 2 E := responseFrameEnergyObservable_contDiff _ _ ν σ hν hσ P
  have hdirs := parent_boundary_common_response_directions_summable P0 Q b L
  have hsecond (j : ℕ) : secondDirectionalDerivative E k (K j) =
      pureFluxResponseHessianDiagonal (measurableSet_openCubeSet Q) hv ν σ hν hσ P k (K j) := by
    unfold secondDirectionalDerivative pureFluxResponseHessianDiagonal
    exact responseFrameEnergyObservable_hessian _ _ ν σ hν hσ P k _ _
  have hs0 := pureFlux_secondDirectionalDerivative_summable E hEd K hdirs k
  have hs1 : Summable (fun j => pureFluxResponseHessianDiagonal (measurableSet_openCubeSet Q)
      hv ν σ hν hσ P k (K j)) := by
    simpa only [hsecond] using hs0
  have hgs : Summable g := hs1.comp_injective
    (@Encodable.encode_injective whiteBasisIndex (Encodable.ofCountable whiteBasisIndex))
  have ht := pureFlux_tsum_half_le_of_finite_bounds g hgs C hfinite
  have hz : pureFluxResponseHessianDiagonal (measurableSet_openCubeSet Q) hv ν σ hν hσ P k 0=0 := by
    have h0 : secondDirectionalDerivative E k 0 =
        pureFluxResponseHessianDiagonal (measurableSet_openCubeSet Q) hv ν σ hν hσ P k 0 := by
      unfold secondDirectionalDerivative pureFluxResponseHessianDiagonal
      exact responseFrameEnergyObservable_hessian _ _ ν σ hν hσ P k 0 0
    rw [← h0]
    simp [secondDirectionalDerivative]
  have heq : modelCovarianceTrace E K k=∑' l,g l := by
    rw [responseFrameEnergyObservable_covarianceTrace_eq_hessianDiagonal_sum]
    exact parent_boundary_common_response_directions_tsum P0 Q b L
      (pureFluxResponseHessianDiagonal (measurableSet_openCubeSet Q) hv ν σ hν hσ P k) hz
  rw [← heq] at ht
  exact ht

end
end ASDExplicitGamma.Native
