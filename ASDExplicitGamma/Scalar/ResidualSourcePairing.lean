module

public import ASDExplicitGamma.Scalar.ResidualWeakHistory

/-! The weighted projection residual energy is its exact pairing with the original load. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
noncomputable section
open Homogenization Response Variational MeasureTheory Triadic

/-- The first-component source as an actual doubled L2 field. -/
theorem scalar_source_block_memL2 (Q : TriadicCube 2) {f : Vec 2 → Vec 2}
    (hf : MemLp f 2 (normalizedCubeMeasure Q)) :
    MemBlockL2 (openCubeSet Q) (fun x => (f x,0)) := by
  have hv : MemVectorL2 (openCubeSet Q) f :=
    memVectorL2_openCubeSet_of_memLp_normalizedCubeMeasure Q hf
  exact (ContinuousLinearMap.inl ℝ (Vec 2) (Vec 2)).comp_memLp' hv

/-- A physical normalized average is the true volume average on the open square. -/
theorem cube_average_eq_volume_average_open (Q : TriadicCube 2) (g : Vec 2 → ℝ) :
    cubeAverage Q g=volumeAverage (openCubeSet Q) g := by
  rw [cubeAverage_eq_integralAverage_openCubeSet]
  rfl

/-- The residual energy agrees exactly with its source pairing for every L2 load. -/
theorem scalar_residual_energy_eq_source_pairing (Q : TriadicCube 2) (ν σ : ℝ)
    (hν : 0 < ν) (hσ : 0 < σ) (k : ResponseCoefficient (openCubeSet Q))
    {f : Vec 2 → Vec 2} (hf : MemLp f 2 (normalizedCubeMeasure Q)) :
    cubeAverage Q (fun x => blockVecDot
      (scalarResidualField Q ν σ hν hσ k
        (toHilbertBlockL2OfBlockField (scalar_source_block_memL2 Q hf)) x)
      (scalarCoefficientFlux (responseFramePlanarCoefficientField ν σ k)
        (scalarResidualField Q ν σ hν hσ k
          (toHilbertBlockL2OfBlockField (scalar_source_block_memL2 Q hf))) x)) =
    ∑ i,pairing Q (fun x =>
      (scalarCoefficientFlux (responseFramePlanarCoefficientField ν σ k)
        (scalarResidualField Q ν σ hν hσ k
          (toHilbertBlockL2OfBlockField (scalar_source_block_memL2 Q hf))) x).1 i)
      (fun x => f x i) := by
  let a := responseFramePlanarCoefficientField ν σ k
  let L : Vec 2 → BlockVec 2 := fun x => (f x,0)
  let hL : MemBlockL2 (openCubeSet Q) L := scalar_source_block_memL2 Q hf
  let H : HilbertBlockL2 (openCubeSet Q) := toHilbertBlockL2OfBlockField hL
  let Z : Vec 2 → BlockVec 2 := scalarResidualField Q ν σ hν hσ k H
  let hZ : MemBlockL2 (openCubeSet Q) Z := (scalarResidualField Q ν σ hν hσ k H).property
  let r : Vec 2 → Vec 2 := fun x => (scalarCoefficientFlux a Z x).1
  have hEll := responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet Q) ν σ hν hσ k
  have hbilL := scalar_frame_bilinear_field Q ν σ hν hσ k hZ hL
  have hbilZ := scalar_frame_bilinear_field Q ν σ hν hσ k hZ hZ
  have hrebuilt : toHilbertBlockL2OfBlockField hZ=scalarProjectionResidual Q ν σ hν hσ k H := by
    change toHilbertBlockL2OfBlockField
      (Lp.memLp (hilbertBlockL2ToBlockL2 (scalarProjectionResidual Q ν σ hν hσ k H)))=_
    exact hilbert_field_rebuild _
  rw [hrebuilt] at hbilL hbilZ
  have horth := scalar_projection_residual_energy_pairing Q ν σ hν hσ k H
  rw [horth,hbilZ] at hbilL
  have havg : volumeAverage (openCubeSet Q) (fun x => blockVecDot (L x)
      (blockMatVecMul (blockCoeffField a x) (Z x)))=
      volumeAverage (openCubeSet Q) (fun x => blockVecDot (Z x)
      (blockMatVecMul (blockCoeffField a x) (Z x))) := by
    simpa only [a] using hbilL.symm
  have hv : MemVectorL2 (openCubeSet Q) f :=
    memVectorL2_openCubeSet_of_memLp_normalizedCubeMeasure Q hf
  have hflux := scalar_coefficient_flux_memL2 Q a hEll hZ
  have hrLocal (i : Fin 2) : MemScalarL2 (openCubeSet Q) (fun x => r x i) :=
    Homogenization.memScalarL2_coord_of_memVectorL2 (memVectorL2_fst_of_memBlockL2 hflux) i
  have hfLocal (i : Fin 2) : MemScalarL2 (openCubeSet Q) (fun x => f x i) :=
    Homogenization.memScalarL2_coord_of_memVectorL2 hv i
  have hrf (i : Fin 2) : MemLp (fun x => r x i) 2 (normalizedCubeMeasure Q) :=
    memLp_normalized_of_memL2On (hrLocal i)
  have hfi (i : Fin 2) : MemLp (fun x => f x i) 2 (normalizedCubeMeasure Q) :=
    memLp_normalized_of_memL2On (hfLocal i)
  have hsumInt : ∀ i, IntegrableOn (fun x => r x i * f x i) (openCubeSet Q) := by
    intro i
    exact (hrLocal i).integrable_mul (hfLocal i)
  have hsum : volumeAverage (openCubeSet Q) (fun x => vecDot (r x) (f x))=
      ∑ i,pairing Q (fun x => r x i) (fun x => f x i) := by
    change volumeAverage (openCubeSet Q) (fun x => ∑ i,r x i*f x i)=_
    rw [volumeAverage_sum Finset.univ (fun i x => r x i*f x i) (fun i _ => hsumInt i)]
    apply Finset.sum_congr rfl
    intro i hi
    rw [pairing]
    exact (cube_average_eq_volume_average_open Q (fun x => r x i*f x i)).symm
  change cubeAverage Q (fun x => blockVecDot (Z x) (scalarCoefficientFlux a Z x))=_
  calc
    cubeAverage Q (fun x => blockVecDot (Z x)
        (scalarCoefficientFlux a Z x)) =
      volumeAverage (openCubeSet Q) (fun x => blockVecDot (Z x)
        (blockMatVecMul (blockCoeffField a x) (Z x))) := by
          exact cube_average_eq_volume_average_open Q _
    _ = volumeAverage (openCubeSet Q) (fun x => vecDot (f x) (r x)) := by
      rw [← havg]
      congr 1
      funext x
      simp [L,blockVecDot,vecDot,scalarCoefficientFlux,r]
    _ = volumeAverage (openCubeSet Q) (fun x => vecDot (r x) (f x)) := by
      congr 1
      funext x
      exact vecDot_comm _ _
    _ = _ := hsum

end

end ASDExplicitGamma.Scalar
