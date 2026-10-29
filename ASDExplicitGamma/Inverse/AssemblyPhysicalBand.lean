module

public import ASDExplicitGamma.Inverse.LaterBandW2
public import ASDExplicitGamma.Inverse.PhysicalGaussianShear

/-! Identification of the variational later band with the actual Gaussian
physical band and its mean on the same translated triadic square. -/

@[expose] public section
namespace ASDExplicitGamma.Inverse

open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian
noncomputable section

/-- Both physical-band realizations enumerate the same actual shells. -/
theorem assembly_physical_band_apply {a b c d : ℝ}
    (j N : ℤ) (weights : ℤ → ℝ) (ω : Cutoff.CutoffSample 2)
    (x : closedRectangle a b c d) :
    wholeRootModelBand j N weights ω x = laterScalarBand j N weights ω x := by
  simp only [wholeRootModelBand,modelWeightedBand,ContinuousMap.sum_apply,
    ContinuousMap.smul_apply,smul_eq_mul,wholeRootWeights,
    shellFieldScalarRestriction,planarShellScalarStream,ContinuousMap.restrict_apply,
    ContinuousMap.comp_apply]
  exact wholeRootShellLabel_sum_Ioc j N
    (fun k => weights k*shellScalarValue (ω.val k) x)

/-- The closed observation rectangle is the actual triadic square up to
its null boundary, including negative translated coordinates. -/
theorem assembly_cube_ae_eq_rectangle (Q : TriadicCube 2) :
    cubeSet Q =ᵐ[volume] closedRectangle
      (((Q.index 0:ℝ)-1/2)*(3:ℝ)^Q.scale)
      ((((Q.index 0:ℝ)-1/2)*(3:ℝ)^Q.scale)+(3:ℝ)^Q.scale)
      (((Q.index 1:ℝ)-1/2)*(3:ℝ)^Q.scale)
      ((((Q.index 1:ℝ)-1/2)*(3:ℝ)^Q.scale)+(3:ℝ)^Q.scale) := by
  have hu (i : Fin 2) : (((Q.index i:ℝ)-1/2)*(3:ℝ)^Q.scale)+(3:ℝ)^Q.scale =
      ((Q.index i:ℝ)+1/2)*(3:ℝ)^Q.scale := by ring
  rw [hu 0,hu 1,cubeSet_eq_pi_Ico]
  have he : closedRectangle
      (((Q.index 0:ℝ)-1/2)*(3:ℝ)^Q.scale) (((Q.index 0:ℝ)+1/2)*(3:ℝ)^Q.scale)
      (((Q.index 1:ℝ)-1/2)*(3:ℝ)^Q.scale) (((Q.index 1:ℝ)+1/2)*(3:ℝ)^Q.scale) =
      Set.pi Set.univ (fun i : Fin 2 => Set.Icc
        (((Q.index i:ℝ)-1/2)*(3:ℝ)^Q.scale)
        (((Q.index i:ℝ)+1/2)*(3:ℝ)^Q.scale)) := by
    ext x
    simp only [closedRectangle,Set.mem_ofPred_eq,Set.mem_pi,Set.mem_univ,
      forall_const,Fin.forall_fin_two]
  rw [he]
  simpa only [Set.pi_univ_Icc, cubeScaleFactor, MeasureTheory.volume_pi] using (Measure.univ_pi_Ico_ae_eq_Icc
    (μ := fun _ : Fin 2 => (volume : Measure ℝ))
    (f := fun i : Fin 2 => ((Q.index i:ℝ)-1/2)*cubeScaleFactor Q)
    (g := fun i : Fin 2 => ((Q.index i:ℝ)+1/2)*cubeScaleFactor Q))

/-- The physical Gaussian shear uses exactly the scalar cube mean in the
variational sensitivity construction. -/
theorem assembly_physical_average_eq_cubeAverage (M : ABKModel 2)
    (Q : TriadicCube 2) (j N : ℤ) (weights : ℤ → ℝ)
    (ω : Cutoff.CutoffSample 2) :
    physicalMissingWaveAverage M j Q.scale N
      (((Q.index 0:ℝ)-1/2)*(3:ℝ)^Q.scale)
      (((Q.index 1:ℝ)-1/2)*(3:ℝ)^Q.scale) weights ω =
        cubeAverage Q (laterBandW2 Q j N weights ω).value.toFun := by
  let a := ((Q.index 0:ℝ)-1/2)*(3:ℝ)^Q.scale
  let c := ((Q.index 1:ℝ)-1/2)*(3:ℝ)^Q.scale
  let K := closedRectangle a (a+(3:ℝ)^Q.scale) c (c+(3:ℝ)^Q.scale)
  have hK : MeasurableSet K := (closedRectangle_isCompact _ _ _ _).measurableSet
  have hae : cubeSet Q =ᵐ[volume] K := assembly_cube_ae_eq_rectangle Q
  have hvol : (spatialVolume K).real Set.univ = cubeVolume Q := by
    rw [Measure.real,spatialVolume_univ,← measure_congr hae,volume_cubeSet_toReal]
  have hint : (∫ x : K, wholeRootModelBand j N weights ω x ∂spatialVolume K) =
      ∫ x in cubeSet Q, laterScalarBand j N weights ω x := by
    calc
      _ = ∫ x : K, laterScalarBand j N weights ω x ∂spatialVolume K := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x =>
          assembly_physical_band_apply j N weights ω x
      _ = ∫ x in K, laterScalarBand j N weights ω x :=
        integral_subtype_comap hK _
      _ = _ := by rw [Measure.restrict_congr_set hae]
  change q3SpatialAverageCLM _ (wholeRootModelBand j N weights ω) = _
  rw [q3SpatialAverageCLM_apply,hvol,hint,later_band_w2_value]
  rfl

end
end ASDExplicitGamma.Inverse
