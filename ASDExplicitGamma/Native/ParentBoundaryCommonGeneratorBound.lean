module

public import ASDExplicitGamma.Native.ParentBoundaryCommonGeneratorTiled
public import ASDExplicitGamma.Native.ParentBoundaryCommonCenterHilbertBound
public import ASDExplicitGamma.Triadic.PlanarDirectionScalar

/-! Complete common-center covariance energy of the actual projected sources. -/

@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Gaussian Main Model Response Triadic Variational Scalar Inverse
open scoped ENNReal BigOperators
noncomputable section

local instance parentBoundaryCommonGeneratorBoundFiniteMeasure (Q : TriadicCube 2) :
    IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
  (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume

/-- The actual generator-source covariance energy is paid by the complete
common-center Hilbert--Schmidt row trace. All histories belong to the actual
coefficient. Its affine minimizer and physical coefficient links are exact
characterizations, not source-energy or generator estimates. -/
theorem parent_boundary_common_generatorY_trace_bound
    (P0 Q : TriadicCube 2) (hQP : cubeSet Q ⊆ cubeSet P0)
    (ν σ b : ℝ) (hν : 0 < ν) (hσ : 0 < σ) (L : {l : ℝ // 0 < l}) (m : ℕ)
    (P : BlockVec 2) (k : ResponseCoefficient (openCubeSet Q))
    (H : whiteBasisIndex → ResponseCoefficient (openCubeSet Q))
    (r : H10Function (openCubeSet Q))
    (hlink : ∀ l,(parentBoundaryCommonBasisMultiplier P0 Q b σ L l).toFun =ᵐ[
      volume.restrict (openCubeSet Q)] fun x => responseCoefficientExtension (H l) x / σ)
    (hfirst : (fun x => (hilbertBlockL2ToBlockL2
      ((responseFrameMuOperatorSystemData (measurableSet_openCubeSet Q)
        (by rw [volume_openCubeSet_toReal]; exact cubeVolume_pos Q) ν σ hν hσ k).toMuHilbertRealization.minimizerMap P) x).1) =ᵐ[
      volumeMeasureOn (openCubeSet Q)]
        (lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) P.1 r).grad)
    (B : ℝ) (hB : 0 ≤ B)
    (hhist : ∀ U ∈ descendantsAtDepth Q m,lemmaVInverseHistory U
      (responseFramePlanarCoefficientField ν σ k) ((3:ℝ)^(1/4:ℝ)) ≤ B) :
    let v := lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) P.1 r
    let Y := fun l => ‖pureFluxResponseGeneratorY (measurableSet_openCubeSet Q)
      (by rw [volume_openCubeSet_toReal]; exact cubeVolume_pos Q) ν σ hν hσ P k (H l)‖^2
    Summable Y ∧ (∑' l,Y l) ≤ B*(|σ⁻¹| * parentBoundaryCommonRowCoefficient P0 Q b L m)^2*
      lemmaVTiledWeakEnergy Q m v.grad := by
  intro v Y
  let R := parentBoundaryCommonRowEnergy P0 Q b σ L m P.1 r
  let C := |σ⁻¹| * parentBoundaryCommonRowCoefficient P0 Q b L m
  have hrow := parent_boundary_common_row_trace_bound P0 Q hQP b σ L m P.1 r
  have hRn (l : whiteBasisIndex) : 0 ≤ R l := by
    unfold R parentBoundaryCommonRowEnergy descendantsAverage
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun U _ => vectorPositiveHaarEnergy_nonneg U _)
  have hRtotal : (∑' l,R l) ≤ C^2*lemmaVTiledWeakEnergy Q m v.grad := by
    have hh := pow_le_pow_left₀ (Real.sqrt_nonneg _) hrow.2 2
    rw [Real.sq_sqrt (tsum_nonneg hRn),mul_pow,
      Real.sq_sqrt (lemmaVTiledWeakEnergy_nonneg Q m v.grad)] at hh
    exact hh
  have hYR (l : whiteBasisIndex) : Y l ≤ B*R l := by
    let F : Vec 2 → Vec 2 := fun x => -(lemmaVPlanarRowField (diagInterpolant Q m)
      (parentBoundaryCommonBasisMultiplier P0 Q b σ L l) v x)
    obtain ⟨hF,hgen,z,hz,he,hfeedback⟩ := parent_boundary_common_generator_tiled_source
      P0 Q hQP ν σ b hν hσ L m P k l (H l) r (hlink l) hfirst B hB hhist
    have hnorm : Y l = (scalarFrameRealization Q ν σ hν hσ k).energyBilin
        (scalarProjectionResidual Q ν σ hν hσ k (projectedSourceLoad Q hF))
        (scalarProjectionResidual Q ν σ hν hσ k (projectedSourceLoad Q hF)) := by
      dsimp only [Y]
      rw [hgen,energyCarrier_norm_sq]
      simp [responseEnergyUp_down,responseFrameEnergyData,
        scalarFrameRealization,scalarFrameEnergyData,responseEnergyHilbertData]
    rw [hnorm]
    apply he.trans_eq
    congr 1
    dsimp only [lemmaVTiledPositiveEnergy,R,parentBoundaryCommonRowEnergy,descendantsAverage]
    congr 1
    apply Finset.sum_congr rfl
    intro U hU
    unfold vectorPositiveHaarEnergy
    apply Finset.sum_congr rfl
    intro i hi
    dsimp only [F]
    exact primalEnergy_neg U (Real.sqrt 3) _
  have hYn (l : whiteBasisIndex) : 0 ≤ Y l := sq_nonneg _
  have hYsum : Summable Y := Summable.of_nonneg_of_le hYn hYR (hrow.1.mul_left B)
  refine ⟨hYsum,?_⟩
  calc
    _ ≤ ∑' l,B*R l := hYsum.tsum_le_tsum hYR (hrow.1.mul_left B)
    _ = B*∑' l,R l := tsum_mul_left
    _ ≤ B*(C^2*lemmaVTiledWeakEnergy Q m v.grad) := mul_le_mul_of_nonneg_left hRtotal hB
    _ = _ := by ring

end
end ASDExplicitGamma.Native
