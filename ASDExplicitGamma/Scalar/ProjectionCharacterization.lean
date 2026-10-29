module

public import ASDExplicitGamma.Scalar.ProjectionRealization

/-! Exact source characterization of the complementary weighted projection. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization Response MeasureTheory
open scoped RealInnerProductSpace

/-- The realized correction space is exactly the canonical Sobolev correction space. -/
theorem scalar_frame_correction_space (Q : TriadicCube 2) (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet Q)) :
    (scalarFrameRealization Q ν σ hν hσ k).correctionSpace=
      (PotentialSolenoidalL2Data.ofSubmoduleClosures (openCubeSet Q)).toMuCorrectionSpaceData := rfl

/-- Every actual zero-trace source variation belongs to the realized weighted correction space. -/
theorem scalar_variation_mem_frame_correction (Q : TriadicCube 2) (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet Q)) {F : Vec 2 → BlockVec 2}
    (hF : ScalarVariation (openCubeSet Q) F) :
    toHilbertBlockL2OfBlockField hF.1 ∈ (scalarFrameRealization Q ν σ hν hσ k).correctionSpace.correctionSpace := by
  rw [scalar_frame_correction_space]
  have h := (PotentialSolenoidalL2Data.ofSubmoduleClosures (openCubeSet Q)).toMuCorrectionSpaceData.mem_correctionSpace
    (memVectorL2_fst_of_memBlockL2 hF.1) (memVectorL2_snd_of_memBlockL2 hF.1) hF.2.1 hF.2.2
  exact h

/-- The removed component is a genuine member of the canonical correction space. -/
theorem scalar_projection_removed_mem (Q : TriadicCube 2) (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet Q)) (F : HilbertBlockL2 (openCubeSet Q)) :
    F-scalarProjectionResidual Q ν σ hν hσ k F ∈
      (scalarFrameRealization Q ν σ hν hσ k).correctionSpace.correctionSpace := by
  let D := scalarFrameEnergyData Q ν σ hν hσ k
  let K := scalarFrameVariationSpace Q ν σ hν hσ k
  have h := K.toSubmodule.starProjection_apply_mem (responseEnergyUp D F)
  change (K.toSubmodule.starProjection (responseEnergyUp D F)).down ∈
    (scalarFrameRealization Q ν σ hν hσ k).correctionSpace.correctionSpace at h
  have he : F-scalarProjectionResidual Q ν σ hν hσ k F=
      (K.toSubmodule.starProjection (responseEnergyUp D F)).down := by
    change F-(F-(K.toSubmodule.starProjection (responseEnergyUp D F)).down)=_
    abel
  rwa [he]

/-- The retained component is energy orthogonal to the actual full correction space. -/
theorem scalar_projection_residual_orthogonal (Q : TriadicCube 2) (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet Q)) (F Y : HilbertBlockL2 (openCubeSet Q))
    (hY : Y ∈ (scalarFrameRealization Q ν σ hν hσ k).correctionSpace.correctionSpace) :
    (scalarFrameRealization Q ν σ hν hσ k).energyBilin
      (scalarProjectionResidual Q ν σ hν hσ k F) Y=0 := by
  let D := scalarFrameEnergyData Q ν σ hν hσ k
  let K := scalarFrameVariationSpace Q ν σ hν hσ k
  have ho := K.toSubmodule.sub_starProjection_mem_orthogonal (responseEnergyUp D F)
  have hy : responseEnergyUp D Y ∈ K.toSubmodule := hY
  have hp := (Submodule.mem_orthogonal _ _).mp ho _ hy
  change (scalarFrameRealization Q ν σ hν hσ k).energyBilin Y
    (scalarProjectionResidual Q ν σ hν hσ k F)=0 at hp
  rwa [(scalarFrameRealization Q ν σ hν hσ k).energySymm] at hp

/-- The retained source energy equals its exact pairing with the input source. -/
theorem scalar_projection_residual_energy_pairing (Q : TriadicCube 2) (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet Q)) (F : HilbertBlockL2 (openCubeSet Q)) :
    (scalarFrameRealization Q ν σ hν hσ k).energyBilin
      (scalarProjectionResidual Q ν σ hν hσ k F) F=
    (scalarFrameRealization Q ν σ hν hσ k).energyBilin
      (scalarProjectionResidual Q ν σ hν hσ k F) (scalarProjectionResidual Q ν σ hν hσ k F) := by
  have h := scalar_projection_residual_orthogonal Q ν σ hν hσ k F _
    (scalar_projection_removed_mem Q ν σ hν hσ k F)
  rw [map_sub] at h
  exact sub_eq_zero.mp h

end ASDExplicitGamma.Scalar
