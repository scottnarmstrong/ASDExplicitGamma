module

public import ASDExplicitGamma.Native.ParentBoundaryCommonGeneratorRow
public import ASDExplicitGamma.Native.ParentBoundaryCommonCenterHilbertSeries
public import ASDExplicitGamma.Triadic.PlanarDirectionScalar

/-! Actual projected-source energies and first potentials on a common-center tiling. -/

@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Gaussian Main Model Response Triadic Variational Scalar Inverse
open scoped ENNReal BigOperators
noncomputable section

local instance parentBoundaryCommonGeneratorTiledFiniteMeasure (Q : TriadicCube 2) :
    IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
  (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume

/-- The actual common-center source has a genuine tiled positive energy,
and its actual first potential obeys the OLD 1.26 forced feedback bound. -/
theorem parent_boundary_common_generator_tiled_source
    (P0 Q : TriadicCube 2) (hQP : cubeSet Q ⊆ cubeSet P0)
    (ν σ b : ℝ) (hν : 0 < ν) (hσ : 0 < σ) (L : {l : ℝ // 0 < l}) (m : ℕ)
    (P : BlockVec 2) (k : ResponseCoefficient (openCubeSet Q))
    (l : whiteBasisIndex) (H : ResponseCoefficient (openCubeSet Q))
    (r : H10Function (openCubeSet Q))
    (hlink : (parentBoundaryCommonBasisMultiplier P0 Q b σ L l).toFun =ᵐ[
      volume.restrict (openCubeSet Q)] fun x => responseCoefficientExtension H x / σ)
    (hfirst : (fun x => (hilbertBlockL2ToBlockL2
      ((responseFrameMuOperatorSystemData (measurableSet_openCubeSet Q)
        (by rw [volume_openCubeSet_toReal]; exact cubeVolume_pos Q) ν σ hν hσ k).toMuHilbertRealization.minimizerMap P) x).1) =ᵐ[
      volumeMeasureOn (openCubeSet Q)]
        (lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) P.1 r).grad)
    (B : ℝ) (hB : 0 ≤ B)
    (hhist : ∀ U ∈ descendantsAtDepth Q m,lemmaVInverseHistory U
      (responseFramePlanarCoefficientField ν σ k) ((3:ℝ)^(1/4:ℝ)) ≤ B) :
    let v := lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) P.1 r
    let η := parentBoundaryCommonBasisMultiplier P0 Q b σ L l
    let F := fun x => -(lemmaVPlanarRowField (diagInterpolant Q m) η v x)
    ∃ hF : MemLp F 2 (normalizedCubeMeasure Q),
      pureFluxResponseGeneratorY (measurableSet_openCubeSet Q)
        (by rw [volume_openCubeSet_toReal]; exact cubeVolume_pos Q) ν σ hν hσ P k H =
        responseEnergyUp (responseFrameEnergyData (measurableSet_openCubeSet Q)
          (by rw [volume_openCubeSet_toReal]; exact cubeVolume_pos Q) ν σ hν hσ k)
          (scalarProjectionResidual Q ν σ hν hσ k (projectedSourceLoad Q hF)) ∧
      ∃ z : H10Function (openCubeSet Q),
        (fun x => (projectedSourceField Q ν σ hν hσ k hF x).1) =ᵐ[
          volumeMeasureOn (openCubeSet Q)] z.toH1Function.grad ∧
        (scalarFrameRealization Q ν σ hν hσ k).energyBilin
          (scalarProjectionResidual Q ν σ hν hσ k (projectedSourceLoad Q hF))
          (scalarProjectionResidual Q ν σ hν hσ k (projectedSourceLoad Q hF)) ≤
          B*lemmaVTiledPositiveEnergy Q m F ∧
        Real.sqrt (lemmaVTiledWeakEnergy Q m z.toH1Function.grad) ≤
          (126/100:ℝ)*B*Real.sqrt (lemmaVTiledPositiveEnergy Q m F) := by
  intro v ηbasis F
  let η := (parentBoundaryCommonQ3Direction P0 Q b L (whiteBasis l)).smul σ⁻¹
  let I := diagInterpolant Q m
  have hη : η.value = (σ⁻¹:ℝ) • parentBoundaryCommonBasisMultiplier P0 Q b 1 L l := by
    simp [η,PlanarW2Infinity.smul,parentBoundaryCommonBasisMultiplier]
  obtain ⟨hF,hgen⟩ := parent_boundary_common_generator_row_identity Q ν σ hν hσ P k H η r hlink hfirst m
  have hpos : ∀ U ∈ descendantsAtDepth Q m,∀ i : Fin 2,Summable (fun j : ℕ =>
      (Real.sqrt 3)^(j+1)*energy U (cubeIncrement U (j+1) (fun x => F x i))) := by
    intro U hU i
    have hs := parent_boundary_common_row_positive_series_unit P0 Q hQP b L m P.1 r U hU l i
    have he : (fun x => F x i) = fun x => (-σ⁻¹) *
        lemmaVPlanarRowField I (parentBoundaryCommonBasisMultiplier P0 Q b 1 L l) v x i := by
      funext x
      change -(lemmaVPlanarRowField I η.value v x i) = _
      rw [hη,pureFluxPlanarRowField_smul]
      simp only [Pi.smul_apply,smul_eq_mul,neg_mul]
    rw [he]
    exact pureFlux_positive_series_smul U _ (-σ⁻¹) hs
  obtain ⟨z,hz⟩ := projectedSource_firstPotential_exists Q ν σ hν hσ k hF
  have ht := pureFlux_projectedSource_tiled_bound Q m ν σ hν hσ k hF hpos z hz B hB hhist
  refine ⟨hF,hgen,z,hz,ht.1,?_⟩
  have hcap : (1/2:ℝ)+(3:ℝ)^(-(1/4:ℝ)) ≤ 126/100 := by
    have hh := pureFlux_half_gain_cap
    norm_num at hh ⊢
    exact hh.le
  exact ht.2.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hcap hB) (Real.sqrt_nonneg _))

end
end ASDExplicitGamma.Native
