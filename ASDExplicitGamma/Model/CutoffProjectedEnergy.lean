module

public import ASDExplicitGamma.Model.CutoffForcingIdentification
public import ASDExplicitGamma.Model.StationaryPhysicalProjection

@[expose] public section

open MeasureTheory Homogenization
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Provider.Corrector

namespace ASDExplicitGamma.Model

/-- The physical realization of the positive stationary cutoff projection. -/
noncomputable def cutoffProjectedField (M : ABKModel 2) (e : Vec 2) (m : ℤ)
    (ω : Cutoff.CutoffSample 2) (x : Vec 2) : HilbertVec 2 :=
  realize (stationaryProjectionRepr (memLp_cutoffOriginForcing M e m)) ω x

/-- Actual physical energy on an open observation cube. -/
noncomputable def cutoffProjectedEnergy (M : ABKModel 2) (e : Vec 2) (m n : ℤ)
    (ω : Cutoff.CutoffSample 2) : ℝ :=
  volumeAverage (openCubeSet (originCube 2 n)) (fun x => ‖cutoffProjectedField M e m ω x‖ ^ 2)

theorem cutoffProjectedEnergy_nonneg (M : ABKModel 2) (e : Vec 2) (m n : ℤ)
    (ω : Cutoff.CutoffSample 2) : 0 ≤ cutoffProjectedEnergy M e m n ω :=
  mul_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg) (integral_nonneg fun _ => sq_nonneg _)

/-- The cutoff projection is locally L² and its residual is physically
solenoidal, on the actual cutoff-sample law. -/
theorem cutoffProjectedField_residual (M : ABKModel 2) (e : Vec 2) (m n : ℤ) :
    ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      MemVectorL2 (openCubeSet (originCube 2 n))
        (fun x => (cutoffProjectedField M e m ω x).toVec) ∧
      IsSolenoidalOn (openCubeSet (originCube 2 n)) (fun x =>
        matVecMul (Cutoff.cutoffValue m ω x) e - (cutoffProjectedField M e m ω x).toVec) := by
  let F := cutoffOriginForcing e m
  have hF := memLp_cutoffOriginForcing M e m
  have hHm := stronglyMeasurable_stationaryProjectionRepr hF
  have hH := memLp_stationaryProjectionRepr hF
  have hfin := (volume_openCubeSet_lt_top (originCube 2 n)).ne
  filter_upwards [ae_memLp_two_realize (μ := (Cutoff.cutoffSampleLaw M).toMeasure) hfin hHm hH,
    stationaryProjectionRepr_physical_residual (isOpen_openCubeSet (originCube 2 n)) hfin
      (stronglyMeasurable_cutoffOriginForcing e m) hF] with ω hh hr
  refine ⟨(HilbertVec.continuousLinearEquivVec 2).toContinuousLinearMap.comp_memLp' hh, ?_⟩
  convert hr.2 using 1
  funext x i
  rw [realize_cutoffOriginForcing]
  rfl

/-- Spatial energy is integrable in the sample. -/
theorem integrable_cutoffProjectedEnergy (M : ABKModel 2) (e : Vec 2) (m n : ℤ) :
    Integrable (cutoffProjectedEnergy M e m n) (Cutoff.cutoffSampleLaw M).toMeasure :=
  (integrable_setIntegral_normSq_realize (volume_openCubeSet_lt_top (originCube 2 n)).ne
    (stronglyMeasurable_stationaryProjectionRepr (memLp_cutoffOriginForcing M e m))
    (memLp_stationaryProjectionRepr (memLp_cutoffOriginForcing M e m))).const_mul _

/-- The physical projected energy has exactly the completed J4 energy in
expectation, at every observation scale. -/
theorem integral_cutoffProjectedEnergy (M : ABKModel 2) (h : ℝ)
    (hM : ASDExplicitGamma.PlanarQ3Gaussian M h) {e : Vec 2}
    (he : Book.Ch02.vecNorm e = 1) (m n : ℤ) :
    (∫ ω, cutoffProjectedEnergy M e m n ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) =
      shellVarianceSum h M.gamma m / 2 := by
  let hF := memLp_cutoffOriginForcing M e m
  change (∫ ω, (volume (openCubeSet (originCube 2 n))).toReal⁻¹ *
    (∫ x in openCubeSet (originCube 2 n),
      ‖realize (stationaryProjectionRepr hF) ω x‖ ^ 2) ∂(Cutoff.cutoffSampleLaw M).toMeasure) = _
  rw [integral_const_mul, integral_setIntegral_normSq_realize
    (volume_openCubeSet_lt_top (originCube 2 n)).ne
    (stronglyMeasurable_stationaryProjectionRepr hF) (memLp_stationaryProjectionRepr hF),
    integral_normSq_eq_norm_sq_toLp (memLp_stationaryProjectionRepr hF),
    toLp_stationaryProjectionRepr, toLp_cutoffOriginForcing,
    q3_cutoffForcing_projection_energy M h hM he m]
  have hv := Internal.Ch02.BookCh02.domain_volume_pos (Book.Ch02.cubeDomain (originCube 2 n))
  change 0 < (volume (openCubeSet (originCube 2 n))).toReal at hv
  rw [← mul_assoc, inv_mul_cancel₀ hv.ne', one_mul]

end ASDExplicitGamma.Model
