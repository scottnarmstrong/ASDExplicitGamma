module

public import ASDExplicitGamma.Native.ParentBoundaryCompatibleWeak
public import ASDExplicitGamma.Native.OldSignedEnergyFieldTransport
public import ASDExplicitGamma.Main.InverseLowerVariation

/-! Sharp inverse-history weak coercivity for the genuine correction
variations of the response Hilbert space. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Gaussian Main Triadic Variational Inverse
noncomputable section

/-- Every actual response variation has a genuine first potential whose
fine-cell weak energy is paid by the complete bank history, rather than
the molecular ellipticity ratio. -/
theorem parent_boundary_variation_first_potential_weak
    (n : ℤ) (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet (originCube 2 n)))
    (Y : (responseFrameEnergyVariationSpace (measurableSet_openCubeSet (originCube 2 n))
      (volume_openCubeSet_originCube_toReal_pos (d := 2) n) nu sigma hnu hsigma k).toSubmodule) :
    ∃ z : H10Function (openCubeSet (originCube 2 n)),
      (fun x => (hilbertBlockL2ToBlockL2 (Y : EnergyCarrier
        (responseFrameEnergyData (measurableSet_openCubeSet (originCube 2 n))
          (volume_openCubeSet_originCube_toReal_pos (d := 2) n) nu sigma hnu hsigma k)).down x).1) =ᵐ[
          volumeMeasureOn (openCubeSet (originCube 2 n))] z.toH1Function.grad ∧
      ∀ (depth : ℕ) (B : ℝ),
        (∀ U∈descendantsAtDepth (originCube 2 n) depth,
          lemmaVInverseHistory U (responseFramePlanarCoefficientField nu sigma k)
            ((3:ℝ)^(1/4:ℝ))≤B) →
        lemmaVTiledWeakEnergy (originCube 2 n) depth z.toH1Function.grad≤
          B*‖(Y : EnergyCarrier (responseFrameEnergyData
            (measurableSet_openCubeSet (originCube 2 n))
            (volume_openCubeSet_originCube_toReal_pos (d := 2) n) nu sigma hnu hsigma k))‖^2 := by
  let Q := originCube 2 n
  let D := responseFrameEnergyData (measurableSet_openCubeSet Q)
    (volume_openCubeSet_originCube_toReal_pos (d := 2) n) nu sigma hnu hsigma k
  let X := (Y : EnergyCarrier D).down
  let F := hilbertBlockL2ToBlockL2 X
  have hmem : X∈(scalarFrameRealization Q nu sigma hnu hsigma k).correctionSpace.correctionSpace :=
    Y.property
  have hvar := old_signed_hilbert_correction_variation Q nu sigma hnu hsigma k X hmem
  have hcomp := scalar_variation_compatible hvar
  obtain ⟨z,hz⟩ := main_response_variation_first_potential n nu sigma hnu hsigma k Y
  refine ⟨z,hz,?_⟩
  intro depth B hhist
  have hb := parent_boundary_compatible_tiled_weak Q depth nu sigma hnu hsigma k B hcomp hhist
  have hrebuild := old_signed_hilbert_field_of_representative Q hvar.1 X (Filter.EventuallyEq.rfl)
  have he := scalar_frame_bilinear_field Q nu sigma hnu hsigma k hvar.1 hvar.1
  rw [hrebuild] at he
  change (scalarFrameRealization Q nu sigma hnu hsigma k).energyBilin X X=
    oldSignedEnergyPairing Q nu sigma k F F at he
  have henergy : oldSignedEnergyPairing Q nu sigma k F F=‖(Y : EnergyCarrier D)‖^2 := by
    rw [←he]
    exact (energyCarrier_norm_sq D (Y : EnergyCarrier D)).symm
  rw [henergy] at hb
  apply le_trans _ hb
  apply le_of_eq
  unfold lemmaVTiledWeakEnergy descendantsAverage
  apply congrArg (fun r : ℝ => ((descendantsAtDepth Q depth).card:ℝ)⁻¹*r)
  apply Finset.sum_congr rfl
  intro U hU
  unfold vectorWeakHaarEnergy
  apply Finset.sum_congr rfl
  intro i _
  have hq : 1<Real.sqrt 3 := by
    nlinarith [Real.sq_sqrt (show (0:ℝ)≤3 by norm_num),Real.sqrt_nonneg (3:ℝ)]
  apply lemmaV_dualEnergy_congr_ae U hq
    (memLp_on_descendant_of_memLp hU (z.toH1Function.grad_memL2_normalizedCubeMeasure i))
    (memLp_on_descendant_of_memLp hU (memLp_normalized_of_memL2On
      (memScalarL2_coord_of_memVectorL2 (memVectorL2_fst_of_memBlockL2 hvar.1) i)))
  rw [volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]
  exact (ae_restrict_of_ae_restrict_of_subset
    (openCubeSet_subset_of_mem_descendantsAtDepth hU) hz.symm).mono
      (fun x hx => congrFun hx i)


/-- The same sharp budget holds for any genuine first-potential representative
of the actual variation, so consumers may retain their existing selections. -/
theorem parent_boundary_variation_tiled_weak
    (n : ℤ) (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet (originCube 2 n)))
    (Y : (responseFrameEnergyVariationSpace (measurableSet_openCubeSet (originCube 2 n))
      (volume_openCubeSet_originCube_toReal_pos (d := 2) n) nu sigma hnu hsigma k).toSubmodule)
    (z : H10Function (openCubeSet (originCube 2 n)))
    (hz : (fun x => (hilbertBlockL2ToBlockL2 (Y : EnergyCarrier
        (responseFrameEnergyData (measurableSet_openCubeSet (originCube 2 n))
          (volume_openCubeSet_originCube_toReal_pos (d := 2) n) nu sigma hnu hsigma k)).down x).1) =ᵐ[
          volumeMeasureOn (openCubeSet (originCube 2 n))] z.toH1Function.grad)
    (depth : ℕ) (B : ℝ)
    (hhist : ∀ U∈descendantsAtDepth (originCube 2 n) depth,
      lemmaVInverseHistory U (responseFramePlanarCoefficientField nu sigma k)
        ((3:ℝ)^(1/4:ℝ))≤B) :
    lemmaVTiledWeakEnergy (originCube 2 n) depth z.toH1Function.grad≤
      B*‖(Y : EnergyCarrier (responseFrameEnergyData
        (measurableSet_openCubeSet (originCube 2 n))
        (volume_openCubeSet_originCube_toReal_pos (d := 2) n) nu sigma hnu hsigma k))‖^2 := by
  obtain ⟨v,hv,hbound⟩ := parent_boundary_variation_first_potential_weak n nu sigma hnu hsigma k Y
  rw [pureFlux_tiledWeakEnergy_h1_congr (originCube 2 n) depth z.toH1Function v.toH1Function
    (hz.symm.trans hv)]
  exact hbound depth B hhist

end
end ASDExplicitGamma.Native
