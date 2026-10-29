module

public import ASDExplicitGamma.Model.CutoffForcingIdentification
public import Algsuperdiff.Section3.Provider.Corrector.FreshShellCorrectorEnergy

@[expose] public section

open MeasureTheory Homogenization
open Algsuperdiff.Section3
open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3.Provider.Corrector
open Algsuperdiff.Probability.Stationary

namespace ASDExplicitGamma.Model

/-- Distinct layer forcings are orthogonal on the common sequence carrier. -/
theorem inner_layerForcingL2_eq_zero {d : ℕ} (M : ABKModel d) (e : Vec d)
    {k l : ℤ} (hkl : l ≠ k) :
    inner ℝ (layerForcingL2 M e k) (layerForcingL2 M e l) = 0 := by
  have hi := inner_flipKoopman M k (layerForcingL2 M e k) (layerForcingL2 M e l)
  rw [flipKoopman_layerForcingL2 M e k k, ite_eq_left rfl,
    flipKoopman_layerForcingL2 M e k l, ite_eq_right hkl, inner_neg_left] at hi
  linarith only [hi]

/-- The total vector forcing mass of the planar zero shell is h². -/
theorem q3OriginForcingL2_norm_sq (M : ABKModel 2) (h : ℝ)
    (hM : ASDExplicitGamma.PlanarQ3Gaussian M h) : ‖q3OriginForcingL2 M‖ ^ 2 = h ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, q3VectorL2_inner_eq_sum_coord,
    Fin.sum_univ_two, q3OriginForcingL2_coord0_eq_zero, inner_zero_left, zero_add]
  change inner ℝ (q3StreamOriginL2 M) (q3StreamOriginL2 M) = h ^ 2
  rw [real_inner_self_eq_norm_sq, q3StreamOriginL2_norm_sq M h hM]

private theorem norm_layerForcingL2_zero (M : ABKModel 2) :
    ‖layerForcingL2 M planarBasis0 0‖ = ‖q3OriginForcingL2 M‖ := by
  have h₀ := norm_carrierTransport (measurePreserving_seqPathCoord_zero M)
    (valuePathForcingL2 M planarBasis0_unit)
  rw [carrierTransport_valuePathForcingL2 M planarBasis0_unit] at h₀
  have hmem := ShellField.memLp_originForcing_of_j2_tail M.P M.J2.gaussian_tail
    planarBasis0 planarBasis0_unit
  have h₁ := norm_carrierTransport (measurePreserving_regOfPath M)
    (ShellField.zeroShellForcingL2 M.P planarBasis0 hmem)
  rw [carrierTransport_zeroShellForcingL2 M planarBasis0_unit hmem] at h₁
  exact h₀.trans h₁

/-- The squared forcing mass at each shell is its exact scalar variance. -/
theorem q3_layerForcingL2_norm_sq (M : ABKModel 2) (h : ℝ)
    (hM : ASDExplicitGamma.PlanarQ3Gaussian M h) (k : ℤ) :
    ‖layerForcingL2 M planarBasis0 k‖ ^ 2 = h ^ 2 * (3 : ℝ) ^ (2 * M.gamma * (k : ℝ)) := by
  have hbase : ‖shellSumForcingL2 M planarBasis0 (0 - 1) 0‖ ^ 2 = h ^ 2 := by
    have h₀ := norm_layerForcingL2_scale M planarBasis0 0
    norm_num at h₀
    rw [← h₀, norm_layerForcingL2_zero, q3OriginForcingL2_norm_sq M h hM]
  have hpow : ((3 : ℝ) ^ (M.gamma * (k : ℝ))) ^ (2 : ℕ) =
      (3 : ℝ) ^ (2 * M.gamma * (k : ℝ)) := by
    rw [← Real.rpow_natCast ((3 : ℝ) ^ (M.gamma * (k : ℝ))) 2,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    congr 1
    push_cast
    ring
  rw [norm_layerForcingL2_scale, mul_pow, hbase, hpow, mul_comm]

/-- The completed forcing has the accumulated point variance B_m. -/
theorem q3_completedLayerForcing_norm_sq (M : ABKModel 2) (h : ℝ)
    (hM : ASDExplicitGamma.PlanarQ3Gaussian M h) (m : ℤ) :
    ‖completedLayerForcingL2 M planarBasis0 m‖ ^ 2 = shellVarianceSum h M.gamma m := by
  change ‖∑' n : ℕ, layerForcingL2 M planarBasis0 (m - (n : ℤ))‖ ^ 2 = _
  rw [norm_sq_tsum_of_pairwise_inner_eq_zero (summable_completedLayerForcing M planarBasis0 m)]
  · simp_rw [q3_layerForcingL2_norm_sq M h hM]
    convert shellVarianceSeries_eq_shellVarianceSum h M.gamma m M.shellPrefix.gamma_pos using 1
    apply tsum_congr
    intro n
    simp only [shellVarianceSeries, Int.cast_sub, Int.cast_natCast]
  · intro i j hij
    apply inner_layerForcingL2_eq_zero
    omega

/-- Exact point variance of the actual accumulated scalar stream, at every
physical point, on the frozen cutoff-sample law. -/
theorem q3_cutoff_stream_second_moment (M : ABKModel 2) (h : ℝ)
    (hM : ASDExplicitGamma.PlanarQ3Gaussian M h) (m : ℤ) (x : Vec 2) :
    (∫ ω, (Cutoff.cutoffValue m ω x 1 0) ^ 2 ∂(Cutoff.cutoffSampleLaw M).toMeasure) =
      shellVarianceSum h M.gamma m := by
  have hnorm : ‖cutoffForcingL2 M planarBasis0 m‖ ^ 2 = shellVarianceSum h M.gamma m := by
    rw [cutoffForcingL2, norm_carrierTransport, q3_completedLayerForcing_norm_sq M h hM]
  have hraw : (∫ ω, ‖cutoffOriginForcing planarBasis0 m ω‖ ^ 2
      ∂(Cutoff.cutoffSampleLaw M).toMeasure) = shellVarianceSum h M.gamma m := by
    rw [integral_normSq_eq_norm_sq_toLp (memLp_cutoffOriginForcing M planarBasis0 m),
      toLp_cutoffOriginForcing]
    exact hnorm
  have htrans := integral_comp_const_vadd
    (μ := (Cutoff.cutoffSampleLaw M).toMeasure)
    (fun ω => ‖cutoffOriginForcing planarBasis0 m ω‖ ^ 2) x
  have hpoint (ω : Cutoff.CutoffSample 2) :
      ‖cutoffOriginForcing planarBasis0 m (x +ᵥ ω)‖ ^ 2 =
        (Cutoff.cutoffValue m ω x 1 0) ^ 2 := by
    have hreal := realize_cutoffOriginForcing planarBasis0 m ω x
    change ‖realize (cutoffOriginForcing planarBasis0 m) ω x‖ ^ 2 = _
    rw [hreal, HilbertVec.norm_sq_eq_sum_sq, Fin.sum_univ_two]
    have hskew := congrArg (fun A : Mat 2 => A 0 0) (Cutoff.cutoff_skew m ω x)
    change Cutoff.cutoffValue m ω x 0 0 = -Cutoff.cutoffValue m ω x 0 0 at hskew
    have hz : Cutoff.cutoffValue m ω x 0 0 = 0 := by linarith only [hskew]
    simp [planarBasis0, matVecMul, Pi.single_apply, hz]
  simpa only [hpoint] using htrans.trans hraw

/-- The literal cutoff stream is in the stationary mean-zero gauge. -/
theorem cutoff_stream_mean_zero (M : ABKModel 2) (m : ℤ) (x : Vec 2) :
    (∫ ω, Cutoff.cutoffValue m ω x 1 0 ∂(Cutoff.cutoffSampleLaw M).toMeasure) = 0 := by
  have hm : Measurable (fun ω : Cutoff.CutoffSample 2 => Cutoff.cutoffValue m ω x 1 0) :=
    Cutoff.measurable_cutoff_apply_entry m x 1 0
  have hi := integral_map Cutoff.measurable_negateCutoffSample.aemeasurable
    (f := fun ω : Cutoff.CutoffSample 2 => (Cutoff.cutoff m ω).toFun x 1 0)
    (μ := (Cutoff.cutoffSampleLaw M).toMeasure)
    (by rw [Cutoff.map_negateCutoffSample_cutoffSampleLaw M]; exact hm.aestronglyMeasurable)
  rw [Cutoff.map_negateCutoffSample_cutoffSampleLaw M] at hi
  change (∫ ω, Cutoff.cutoffValue m ω x 1 0 ∂(Cutoff.cutoffSampleLaw M).toMeasure) =
    ∫ ω, Cutoff.cutoffValue m (Cutoff.negateCutoffSample ω) x 1 0
      ∂(Cutoff.cutoffSampleLaw M).toMeasure at hi
  have hneg (ω : Cutoff.CutoffSample 2) :
      Cutoff.cutoffValue m (Cutoff.negateCutoffSample ω) x 1 0 = -Cutoff.cutoffValue m ω x 1 0 := by
    have hneg := congrArg (fun a : RegCoeffField 2 => a x 1 0) (Cutoff.cutoff_negateCutoffSample m ω)
    simp only [Algsuperdiff.Probability.negReg_apply, Matrix.neg_apply] at hneg
    exact hneg
  simp_rw [hneg] at hi
  rw [integral_neg] at hi
  linarith only [hi]

/-- The actual accumulated point variance equals the frozen B_m. -/
theorem q3_cutoff_stream_variance (M : ABKModel 2) (h : ℝ)
    (hM : ASDExplicitGamma.PlanarQ3Gaussian M h) (m : ℤ) (x : Vec 2) :
    ProbabilityTheory.variance (fun ω => Cutoff.cutoffValue m ω x 1 0)
      (Cutoff.cutoffSampleLaw M).toMeasure = shellVarianceSum h M.gamma m := by
  change ProbabilityTheory.variance (fun ω : Cutoff.CutoffSample 2 => (Cutoff.cutoff m ω).toFun x 1 0)
    (Cutoff.cutoffSampleLaw M).toMeasure = _
  have hz := cutoff_stream_mean_zero M m x
  change (∫ ω, (Cutoff.cutoff m ω).toFun x 1 0 ∂(Cutoff.cutoffSampleLaw M).toMeasure) = 0 at hz
  rw [ProbabilityTheory.variance_eq_integral
    (Cutoff.measurable_cutoff_apply_entry m x 1 0).aemeasurable, hz]
  simp only [sub_zero]
  change (∫ ω, (Cutoff.cutoffValue m ω x 1 0) ^ 2 ∂(Cutoff.cutoffSampleLaw M).toMeasure) = _
  exact q3_cutoff_stream_second_moment M h hM m x

end ASDExplicitGamma.Model
