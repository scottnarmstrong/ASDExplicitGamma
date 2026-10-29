module

public import ASDExplicitGamma.Cold.NativeCanonicalOptimizer

/-! # Measurable actual canonical gradient and flux cell averages -/

@[expose] public section
noncomputable section
open MeasureTheory Homogenization Homogenization.Book
namespace ASDExplicitGamma.Cold

/-- Any genuine measurable elliptic field family has the public restriction-law carrier. -/
theorem cold_coefficient_map_carrier {Ω : Type*} [MeasurableSpace Ω] (μprob : Measure Ω) [IsProbabilityMeasure μprob]
    (a : Ω → RegCoeffField 2) (hm : Measurable a) (ha : ∀ ω, Ch04.AELocallyUniformlyEllipticField (a ω)) :
    Ch04.RestrictionLawCarrier (Measure.map a μprob) := by
  apply Ch04.lawCarrier_of_aeLocallyUniformlyElliptic
  rw [Ch04.AELocallyUniformlyEllipticLaw,ae_map_iff hm.aemeasurable cold_measurableSet_locallyElliptic]
  exact Filter.Eventually.of_forall ha

/-- The actual canonical gradient averages are measurable on every real descendant cell. -/
theorem cold_canonical_gradient_average_measurable {Ω : Type*} [MeasurableSpace Ω] (μprob : Measure Ω) [IsProbabilityMeasure μprob]
    (a : Ω → RegCoeffField 2) (hm : Measurable a) (ha : ∀ ω, Ch04.AELocallyUniformlyEllipticField (a ω))
    (Q R : TriadicCube 2) {r : ℕ} (hR : R ∈ descendantsAtDepth Q r) (p q : Vec 2) :
    AEMeasurable (fun ω => cubeAverageVec R (coldCanonicalOptimizer (a ω) (ha ω) Q p q).toH1.grad) μprob := by
  have hc := cold_coefficient_map_carrier μprob a hm ha
  have hf := hc.aemeasurable_canonicalScalarResponseGradientAverage_cubeSet Q R p q
  have hh := hf.comp_aemeasurable hm.aemeasurable
  have he : (fun ω => Ch04.canonicalScalarResponseGradientAverageCubeSet Q R p q (a ω).toFun) =
      (fun ω => cubeAverageVec R (coldCanonicalOptimizer (a ω) (ha ω) Q p q).toH1.grad) := by
    funext ω
    exact Ch04.canonicalScalarResponseGradientAverageCubeSet_eq_cubeAverageVec_canonicalMaximizer (a ω) (ha ω) hR p q
  rw [← he]
  exact hh

/-- The actual canonical flux averages are measurable on every real descendant cell. -/
theorem cold_canonical_flux_average_measurable {Ω : Type*} [MeasurableSpace Ω] (μprob : Measure Ω) [IsProbabilityMeasure μprob]
    (a : Ω → RegCoeffField 2) (hm : Measurable a) (ha : ∀ ω, Ch04.AELocallyUniformlyEllipticField (a ω))
    (Q R : TriadicCube 2) {r : ℕ} (hR : R ∈ descendantsAtDepth Q r) (p q : Vec 2) :
    AEMeasurable (fun ω => cubeAverageVec R (fun x => matVecMul ((a ω).toFun x)
      ((coldCanonicalOptimizer (a ω) (ha ω) Q p q).toH1.grad x))) μprob := by
  have hc := cold_coefficient_map_carrier μprob a hm ha
  have hf := hc.aemeasurable_canonicalScalarResponseFluxAverage_cubeSet Q R p q
  have hh := hf.comp_aemeasurable hm.aemeasurable
  have he : (fun ω => Ch04.canonicalScalarResponseFluxAverageCubeSet Q R p q (a ω).toFun) =
      (fun ω => cubeAverageVec R (fun x => matVecMul ((a ω).toFun x) ((coldCanonicalOptimizer (a ω) (ha ω) Q p q).toH1.grad x))) := by
    funext ω
    exact Ch04.canonicalScalarResponseFluxAverageCubeSet_eq_cubeAverageVec_canonicalMaximizerFlux (a ω) (ha ω) hR p q
  rw [← he]
  exact hh

end ASDExplicitGamma.Cold
