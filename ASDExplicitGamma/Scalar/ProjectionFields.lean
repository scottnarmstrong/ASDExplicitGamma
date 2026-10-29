module

public import ASDExplicitGamma.Scalar.ProjectionCharacterization

/-! Pointwise L2 representatives and genuine field orthogonality of the weighted residual. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization Response MeasureTheory

/-- Rebuilding a Hilbert field from its actual plain L2 representative gives the original class. -/
theorem hilbert_field_rebuild {U : Set (Vec 2)} (F : HilbertBlockL2 U) :
    toHilbertBlockL2OfBlockField (Lp.memLp (hilbertBlockL2ToBlockL2 F))=F := by
  rw [← blockL2ToHilbertBlockL2_toBlockL2]
  unfold toBlockL2
  rw [Lp.toLp_coeFn]
  exact blockL2ToHilbertBlockL2_hilbertBlockL2ToBlockL2 F

/-- The source realization's bilinear form is the literal averaged doubled coefficient pairing. -/
theorem scalar_frame_bilinear_field (Q : TriadicCube 2) (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet Q)) {F G : Vec 2 → BlockVec 2}
    (hF : MemBlockL2 (openCubeSet Q) F) (hG : MemBlockL2 (openCubeSet Q) G) :
    (scalarFrameRealization Q ν σ hν hσ k).energyBilin
      (toHilbertBlockL2OfBlockField hF) (toHilbertBlockL2OfBlockField hG)=
    volumeAverage (openCubeSet Q) (fun x => blockVecDot (G x)
      (blockMatVecMul (blockCoeffField (responseFramePlanarCoefficientField ν σ k) x) (F x))) := by
  let finiteScalarBilinearVolume : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume
  exact (responseFrameMuOperatorSystemData (measurableSet_openCubeSet Q)
    (show 0 < (volume (openCubeSet Q)).toReal by rw [volume_openCubeSet_toReal];exact cubeVolume_pos Q)
    ν σ hν hσ k).toMuOperatorRealization.energyBilin_eq_volumeAverage_swap_of_memBlockL2 hG hF

/-- The actual pointwise L2 representative of the complementary weighted projection. -/
noncomputable def scalarResidualField (Q : TriadicCube 2) (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet Q)) (F : HilbertBlockL2 (openCubeSet Q)) :
    BlockL2 (openCubeSet Q) :=
  hilbertBlockL2ToBlockL2 (scalarProjectionResidual Q ν σ hν hσ k F)

/-- The true residual is orthogonal to every genuine source variation, in the literal field pairing. -/
theorem scalar_residual_field_orthogonal (Q : TriadicCube 2) (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet Q)) (F : HilbertBlockL2 (openCubeSet Q))
    (Y : Vec 2 → BlockVec 2) (hY : ScalarVariation (openCubeSet Q) Y) :
    volumeAverage (openCubeSet Q) (fun x => blockVecDot (Y x)
      (blockMatVecMul (blockCoeffField (responseFramePlanarCoefficientField ν σ k) x)
        (scalarResidualField Q ν σ hν hσ k F x)))=0 := by
  have h := scalar_projection_residual_orthogonal Q ν σ hν hσ k F _
    (scalar_variation_mem_frame_correction Q ν σ hν hσ k hY)
  have hb := scalar_frame_bilinear_field Q ν σ hν hσ k
    (Lp.memLp (scalarResidualField Q ν σ hν hσ k F)) hY.1
  have he : toHilbertBlockL2OfBlockField (Lp.memLp (scalarResidualField Q ν σ hν hσ k F))=
      scalarProjectionResidual Q ν σ hν hσ k F := hilbert_field_rebuild _
  rw [he] at hb
  exact hb.symm.trans h

end ASDExplicitGamma.Scalar
