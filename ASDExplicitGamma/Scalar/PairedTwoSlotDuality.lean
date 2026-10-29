module

public import ASDExplicitGamma.Scalar.PairedTwoSlotCell
public import ASDExplicitGamma.Scalar.PairedTwoSlotAggregate
public import ASDExplicitGamma.Inverse.PureFluxGeneratorTiledFeedback

/-! Cell duality and the decomposition of parent integrals over a tiling. -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Triadic
  ASDExplicitGamma.Variational ASDExplicitGamma.Inverse

noncomputable section

/-- A parent integral is the volume times the average of the cell averages. -/
theorem integral_eq_vol_mul_avg (Q : TriadicCube 2) (n : ℕ) {f : Vec 2 → ℝ}
    (hf : IntegrableOn f (openCubeSet Q)) :
    ∫ z in openCubeSet Q, f z ∂volume =
      (volume (openCubeSet Q)).toReal *
        descendantsAverage Q n (fun U => volumeAverage (openCubeSet U) f) := by
  have hfc : IntegrableOn f (cubeSet Q) := integrableOn_cubeSet_iff_integrableOn_openCubeSet.mpr hf
  have h := cubeAverage_eq_descendantsAverage_cubeAverage_of_integrableOn Q n f hfc
  have hcell : (fun U => volumeAverage (openCubeSet U) f) = fun U => cubeAverage U f := by
    funext U
    rw [cubeAverage_eq_integralAverage_openCubeSet U]
    rfl
  rw [hcell, ← h, cubeAverage_eq_integralAverage_openCubeSet Q]
  have hvol : 0 < (volume (openCubeSet Q)).toReal := by
    rw [volume_openCubeSet_toReal]; exact cubeVolume_pos Q
  change _ = _ * ((volume (openCubeSet Q)).toReal⁻¹ * _)
  field_simp

/-- Cellwise duality between a source and a gradient field, in volume averages. -/
theorem cell_duality (U : TriadicCube 2) {F V : Vec 2 → Vec 2}
    (hF : MemLp F 2 (normalizedCubeMeasure U))
    (hFpos : ∀ i : Fin 2, Summable (fun j : ℕ => (Real.sqrt 3) ^ (j + 1) *
      energy U (cubeIncrement U (j + 1) (fun x => F x i))))
    (hV : MemVectorL2 (openCubeSet U) V) :
    |volumeAverage (openCubeSet U) (fun z => vecDot (F z) (V z))| ≤
      Real.sqrt (vectorPositiveHaarEnergy U F) * Real.sqrt (vectorWeakHaarEnergy U V) := by
  have hFvec := memVectorL2_openCubeSet_of_memLp_normalizedCubeMeasure U hF
  have hFc (i : Fin 2) : MemLp (fun x => F x i) 2 (normalizedCubeMeasure U) :=
    memLp_normalized_of_memL2On (memScalarL2_coord_of_memVectorL2 hFvec i)
  have hVc (i : Fin 2) : MemLp (fun x => V x i) 2 (normalizedCubeMeasure U) :=
    memLp_normalized_of_memL2On (memScalarL2_coord_of_memVectorL2 hV i)
  have hav : volumeAverage (openCubeSet U) (fun z => vecDot (F z) (V z)) =
      vectorPairing U F V := by
    rw [← lemmaV_cubeAverage_vecDot_eq_vectorPairing U hFc hVc,
      cubeAverage_eq_integralAverage_openCubeSet U]
    rfl
  rw [hav]
  exact abs_vectorPairing_le_vectorPositiveHaarNorm_mul_vectorWeakHaarNorm U hFc hVc hFpos

end

end ASDExplicitGamma.Scalar
