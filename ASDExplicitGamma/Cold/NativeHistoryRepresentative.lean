module

public import ASDExplicitGamma.Cold.NativeHistoryDepth

/-! # A measurable genuine-history representative for the ordinary plateau expectations -/

@[expose] public section
noncomputable section
open MeasureTheory Homogenization Algsuperdiff.Section3
namespace ASDExplicitGamma.Cold
open ASDExplicitGamma.Numerics.Cold

/-- The actual complete history is nonnegative at every sample, including any divergent sample
where the ordinary real tsum convention returns zero. -/
theorem coldNativeHistory_nonneg (M : ABKModel 2) (m : ℤ) (j : ℕ) (ω : Cutoff.CutoffSample 2) :
    0 ≤ coldNativeHistory M m j ω := by
  unfold coldNativeHistory coldWeightedHistory
  apply mul_nonneg (sub_nonneg.mpr coldHistoryAlpha_le_one)
  exact tsum_nonneg (fun r => mul_nonneg (pow_nonneg coldHistoryAlpha_pos.le r)
    (coldNativeHistory_maximum_nonneg M m j r ω))

/-- The genuine native history has a measurable a.e.-equal representative with precisely the
moment and depth bounds consumed by the actual P1--P6 expectation theorem. -/
theorem cold_native_history_representative (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (m : ℤ)
    {θ : ℝ} (hθ : 0 ≤ θ) (hroot : root20 M m ≤ ENNReal.ofReal (θ*(coldR20:ℝ)))
    (hstrong : strong20 M m ≤ ENNReal.ofReal (θ*(coldS20:ℝ))) {j : ℕ} (hj : j ∈ coldUpdatedLags)
    (hmean : ∀ k < j, coldNativeMean M m k ≤ θ*(coldMeanAt k:ℝ)) :
    let F := coldNativePlateauFamily M m (originCube 2 (m+(j:ℤ)))
    ∃ D : Cutoff.CutoffSample 2 → ℝ, Measurable D ∧
      D =ᵐ[(Cutoff.cutoffSampleLaw M).toMeasure] coldNativeHistory M m j ∧
      (∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure, 0 ≤ D ω) ∧
      Integrable (fun ω => D ω^20) (Cutoff.cutoffSampleLaw M).toMeasure ∧
      (∫ ω, D ω^20 ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤ (θ*(coldHistoryAt j:ℝ))^20 ∧
      (∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure, (F.atDepth 0).parentTrace ω ≤ D ω) ∧
      (∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure, ∀ r, ∀ C : SquareCells (originCube 2 (m+(j:ℤ))) r,
        (F.atDepth r).cellTrace C ω ≤ (3:ℝ)^((r:ℝ)/4)*D ω) := by
  dsimp only
  have hc := cold_native_history_table M h hM m hθ hroot hstrong hj hmean
  let D := hc.1.aestronglyMeasurable.mk (coldNativeHistory M m j)
  have he : coldNativeHistory M m j =ᵐ[(Cutoff.cutoffSampleLaw M).toMeasure] D := hc.1.aestronglyMeasurable.ae_eq_mk
  have hm : Measurable D := hc.1.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hD : MemLp D 20 (Cutoff.cutoffSampleLaw M).toMeasure := by
    change eLpNorm D 20 _ < ⊤
    rw [eLpNorm_congr_ae he.symm]
    exact hc.1
  have hnorm : lpNorm D 20 (Cutoff.cutoffSampleLaw M).toMeasure ≤ θ*(coldHistoryAt j:ℝ) := by
    have hh := congrArg ENNReal.toReal (eLpNorm_congr_ae he.symm (p := 20))
    exact hh.trans_le hc.2
  have hInt : Integrable (fun ω => D ω^20) (Cutoff.cutoffSampleLaw M).toMeasure := by
    have hh := hD.integrable_norm_pow (p := 20) (by norm_num)
    simpa only [Real.norm_eq_abs,show (20:ℕ)=2*10 by norm_num,pow_mul,sq_abs] using hh
  have hdepth := cold_native_history_depth_bounds hroot
    (show 0 ≤ θ*(coldS20:ℝ) by exact mul_nonneg hθ (by norm_num [coldS20])) hstrong j
  refine ⟨D,hm,he.symm,?_,hInt,cold_integral_twentieth_le hD hnorm,?_,?_⟩
  · filter_upwards [he] with ω hω
    rw [← hω]
    exact coldNativeHistory_nonneg M m j ω
  · filter_upwards [he,hdepth.1] with ω hω hrootω
    rwa [← hω]
  · filter_upwards [he,hdepth.2] with ω hω hmaxω r C
    rw [← hω]
    exact hmaxω r C

end ASDExplicitGamma.Cold
