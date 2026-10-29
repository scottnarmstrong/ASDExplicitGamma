module

public import ASDExplicitGamma.Gaussian.CovarianceTrace

/-! # The auxiliary-field formula for every bounded bilinear covariance trace -/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology

namespace ASDExplicitGamma.Gaussian

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The quadratic test associated with any bounded bilinear form has the required C² bounds. -/
theorem bilinear_diagonal_polynomial (B : E →L[ℝ] E →L[ℝ] ℝ) :
    HasPolynomiallyBoundedC2Derivatives (fun x => B x x) := by
  have hd (x : E) : HasFDerivAt (fun y => B y y) (B x + B.flip x) x := by
    convert B.hasFDerivAt_of_bilinear (hasFDerivAt_id x) (hasFDerivAt_id x) using 1 <;> ext u <;> rfl
  have heq : fderiv ℝ (fun y => B y y) = fun x => B x + B.flip x := funext fun x => (hd x).fderiv
  have hsecond (x u w : E) : fderiv ℝ (fun z => fderiv ℝ (fun y => B y y) z w) x u =
      B u w + B w u := by
    simp only [heq, add_apply, ContinuousLinearMap.flip_apply]
    change fderiv ℝ (fun z => B.flip w z + B w z) x u = _
    exact congrArg (fun f : E →L[ℝ] ℝ => f u)
      (((B.flip w).hasFDerivAt (x := x)).add (B w).hasFDerivAt).fderiv
  refine ⟨B.isBoundedBilinearMap.contDiff.comp (contDiff_id.prodMk contDiff_id),
    2 * ‖B‖, by positivity, 2, ?_, ?_, ?_⟩
  · intro x
    exact (B.le_opNorm₂ x x).trans (by nlinarith [norm_nonneg B, norm_nonneg x])
  · intro x
    rw [heq]
    calc
      ‖B x + B.flip x‖ ≤ ‖B x‖ + ‖B.flip x‖ := norm_add_le _ _
      _ ≤ ‖B‖ * ‖x‖ + ‖B‖ * ‖x‖ := by
        exact add_le_add (B.le_opNorm x) (by simpa only [ContinuousLinearMap.opNorm_flip] using B.flip.le_opNorm x)
      _ ≤ 2 * ‖B‖ * (1 + ‖x‖) ^ 2 := by
        have hh : ‖x‖ ≤ (1 + ‖x‖) ^ 2 := by nlinarith [norm_nonneg x]
        nlinarith [mul_le_mul_of_nonneg_left hh (norm_nonneg B)]
  · intro x u w
    rw [hsecond]
    calc
      |B u w + B w u| ≤ |B u w| + |B w u| := abs_add_le _ _
      _ ≤ ‖B‖ * ‖u‖ * ‖w‖ + ‖B‖ * ‖w‖ * ‖u‖ := add_le_add (B.le_opNorm₂ u w) (B.le_opNorm₂ w u)
      _ ≤ 2 * ‖B‖ * (1 + ‖x‖) ^ 2 * ‖u‖ * ‖w‖ := by
        have h : 2 * ‖B‖ ≤ 2 * ‖B‖ * (1 + ‖x‖) ^ 2 := by
          apply le_mul_of_one_le_right (by positivity)
          nlinarith [norm_nonneg x]
        nlinarith [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h (norm_nonneg u)) (norm_nonneg w)]

end

/-- GA-COVARIANCE-TRACE: the absolutely convergent trace is the expected bilinear
evaluation of the auxiliary field. This holds for nonsymmetric bilinear forms as well. -/
theorem integral_bilinear_diagonal {V E : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    {v : ℕ → V} (hA : Summable (fun j => ‖v j‖ ^ 2)) (T : V →L[ℝ] E)
    (B : E →L[ℝ] E →L[ℝ] ℝ) :
    ∫ ω, B (gaussianSeriesLimitE hA T ω) (gaussianSeriesLimitE hA T ω)
      ∂standardGaussianInfinitePi = ∑' j, B (T (v j)) (T (v j)) := by
  let Q : E → ℝ := fun x => B x x
  let a : ℝ := ∫ ω, Q (gaussianSeriesLimitE hA T ω) ∂standardGaussianInfinitePi
  have hQ := bilinear_diagonal_polynomial B
  have heq : EqOn (gaussianSeriesHeatAverage hA T Q 0) (fun t => t * a) (Ici 0) := by
    intro t ht
    unfold gaussianSeriesHeatAverage gaussianSeriesHeatArgument
    simp only [zero_add]
    have hp (z : E) : Q (Real.sqrt t • z) = t * Q z := by
      dsimp only [Q]
      simp only [map_smul, smul_apply, smul_eq_mul]
      rw [← mul_assoc, ← pow_two, Real.sq_sqrt ht]
    simp only [hp, integral_const_mul, a]
  have hd := (hasDerivWithinAt_gaussianSeriesHeatAverage_zero hA T Q hQ 0).congr_of_mem
    (fun t ht => (heq ht).symm) (show (0 : ℝ) ∈ Ici 0 from le_refl _)
  have ha : HasDerivWithinAt (fun t : ℝ => t * a) a (Ici 0) 0 := by
    simpa only [one_mul, id_eq] using ((hasDerivAt_id (0 : ℝ)).mul_const a).hasDerivWithinAt
  have htrace : gaussianSeriesHeatTraceAverage hA T Q 0 0 =
      2 * ∑' j, B (T (v j)) (T (v j)) := by
    have hf (x : E) : fderiv ℝ Q x = B x + B.flip x := by
      convert (B.hasFDerivAt_of_bilinear (hasFDerivAt_id x) (hasFDerivAt_id x)).fderiv using 1 <;> ext u <;> rfl
    have hs (x u : E) : secondDirectionalDerivative Q x u = 2 * B u u := by
      unfold secondDirectionalDerivative
      simp only [hf, add_apply, ContinuousLinearMap.flip_apply]
      change fderiv ℝ (fun y => B.flip u y + B u y) x u = _
      have hh := congrArg (fun f : E →L[ℝ] ℝ => f u)
        (((B.flip u).hasFDerivAt (x := x)).add (B u).hasFDerivAt).fderiv
      convert hh using 1
      simp only [add_apply, ContinuousLinearMap.flip_apply]
      ring
    simp [gaussianSeriesHeatTraceAverage, gaussianSeriesHeatTrace, hs, tsum_mul_left]
  have hu := (hd.derivWithin (uniqueDiffWithinAt_Ici (0 : ℝ))).symm.trans
    (ha.derivWithin (uniqueDiffWithinAt_Ici (0 : ℝ)))
  rw [htrace] at hu
  change a = _
  linarith only [hu]

/-- In particular the bilinear trace depends only on the Gaussian law, including for
singular covariance factors and bounded observations of a joint finite band. -/
theorem bilinearTrace_eq_of_law {V W E : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
    [SecondCountableTopology W] [MeasurableSpace W] [BorelSpace W]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    {v : ℕ → V} (hA : Summable (fun j => ‖v j‖ ^ 2)) (T : V →L[ℝ] E)
    {w : ℕ → W} (hB : Summable (fun j => ‖w j‖ ^ 2)) (S : W →L[ℝ] E)
    (hlaw : standardGaussianInfinitePi.map (gaussianSeriesLimitE hA T) =
      standardGaussianInfinitePi.map (gaussianSeriesLimitE hB S))
    (B : E →L[ℝ] E →L[ℝ] ℝ) :
    (∑' j, B (T (v j)) (T (v j))) = ∑' j, B (S (w j)) (S (w j)) := by
  rw [← integral_bilinear_diagonal hA T B, ← integral_bilinear_diagonal hB S B]
  have hc : Continuous (fun x => B x x) := B.continuous.clm_apply continuous_id
  rw [← integral_map (stronglyMeasurable_gaussianSeriesLimitE hA T).measurable.aemeasurable
      hc.aestronglyMeasurable,
    ← integral_map (stronglyMeasurable_gaussianSeriesLimitE hB S).measurable.aemeasurable
      hc.aestronglyMeasurable, hlaw]

end ASDExplicitGamma.Gaussian
