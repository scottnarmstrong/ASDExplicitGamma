module

public import ASDExplicitGamma.Gaussian.TimeAverage

/-! # Endpoint continuity in the time-dependent heat identity -/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology

namespace ASDExplicitGamma.Gaussian

section
variable {V E : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  {v : ℕ → V} (hA : Summable (fun j => ‖v j‖ ^ 2)) (T : V →L[ℝ] E)
  (ν : Measure E) [IsFiniteMeasure ν]

/-- Joint continuity and the polynomial Hessian bound give continuity of both expected terms,
including both endpoints. Absolute covariance summability is used before taking expectations. -/
theorem continuousOn_timeHeatAverage_and_derivative
    (hν : ∀ d : ℕ, Integrable (fun x : E => (1 + ‖x‖) ^ d) ν)
    {G D : ℝ → E → ℝ} (hG : TimeRegularity G D) :
    ContinuousOn (timeHeatAverage hA T ν G) (Icc 0 1) ∧
    ContinuousOn (timeHeatDerivative hA T ν G D) (Icc 0 1) := by
  obtain ⟨C, hC, d, hb⟩ := hG.polynomial_bound
  let μ := ν.prod standardGaussianInfinitePi
  let Z := gaussianSeriesLimitE hA T
  let M : E × (ℕ → ℝ) → ℝ := fun p => 1 + ‖p.1‖ + ‖Z p.2‖
  let S : ℝ := ∑' j, ‖T (v j)‖ ^ 2
  let F : ℝ → E × (ℕ → ℝ) → ℝ := fun t p => G t (p.1 + Real.sqrt t • Z p.2)
  let A : ℝ → E × (ℕ → ℝ) → ℝ := fun t p => D t (p.1 + Real.sqrt t • Z p.2)
  let B : ℝ → E × (ℕ → ℝ) → ℝ := fun t p =>
    ∑' j, fderiv ℝ (fderiv ℝ (G t)) (p.1 + Real.sqrt t • Z p.2) (T (v j)) (T (v j))
  have hS : 0 ≤ S := tsum_nonneg fun j => sq_nonneg _
  have hdir := summable_sq_norm_gaussianDirections hA T
  have hm : Integrable (fun p => C * M p ^ d) μ :=
    (integrable_product_envelope hA T ν hν d).const_mul C
  have hpath (p : E × (ℕ → ℝ)) : Continuous (fun t : ℝ => (t, p.1 + Real.sqrt t • Z p.2)) :=
    continuous_id.prodMk (continuous_const.add (Real.continuous_sqrt.smul continuous_const))
  have hmem (p : E × (ℕ → ℝ)) : MapsTo (fun t : ℝ => (t, p.1 + Real.sqrt t • Z p.2))
      (Icc 0 1) (Icc (0 : ℝ) 1 ×ˢ (univ : Set E)) := fun t ht => ⟨ht, mem_univ _⟩
  have harg (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (p : E × (ℕ → ℝ)) :
      1 + ‖p.1 + Real.sqrt t • Z p.2‖ ≤ M p := by
    have htri := norm_add_le p.1 (Real.sqrt t • Z p.2)
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg t)] at htri
    have hsqrt : Real.sqrt t ≤ 1 := by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt ht.2
    have hz := mul_le_mul_of_nonneg_right hsqrt (norm_nonneg (Z p.2))
    dsimp [M]
    linarith
  have hbounds (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (p : E × (ℕ → ℝ)) :
      |F t p| ≤ C * M p ^ d ∧ |A t p| ≤ C * M p ^ d ∧
      ‖fderiv ℝ (fderiv ℝ (G t)) (p.1 + Real.sqrt t • Z p.2)‖ ≤ C * M p ^ d := by
    have h := hb t ht (p.1 + Real.sqrt t • Z p.2)
    have hp := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (harg t ht p) d) hC
    dsimp [F, A]
    constructor
    · linarith [abs_nonneg (D t (p.1 + Real.sqrt t • Z p.2)),
        norm_nonneg (fderiv ℝ (G t) (p.1 + Real.sqrt t • Z p.2)),
        norm_nonneg (fderiv ℝ (fderiv ℝ (G t)) (p.1 + Real.sqrt t • Z p.2))]
    constructor
    · linarith [abs_nonneg (G t (p.1 + Real.sqrt t • Z p.2)),
        norm_nonneg (fderiv ℝ (G t) (p.1 + Real.sqrt t • Z p.2)),
        norm_nonneg (fderiv ℝ (fderiv ℝ (G t)) (p.1 + Real.sqrt t • Z p.2))]
    · linarith [abs_nonneg (G t (p.1 + Real.sqrt t • Z p.2)),
        abs_nonneg (D t (p.1 + Real.sqrt t • Z p.2)),
        norm_nonneg (fderiv ℝ (G t) (p.1 + Real.sqrt t • Z p.2))]
  have hterm (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (p : E × (ℕ → ℝ)) (j : ℕ) :
      ‖fderiv ℝ (fderiv ℝ (G t)) (p.1 + Real.sqrt t • Z p.2) (T (v j)) (T (v j))‖ ≤
        C * M p ^ d * ‖T (v j)‖ ^ 2 := by
    have h := (fderiv ℝ (fderiv ℝ (G t)) (p.1 + Real.sqrt t • Z p.2)).le_opNorm₂ (T (v j)) (T (v j))
    exact h.trans (by simpa only [pow_two, mul_assoc] using
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hbounds t ht p).2.2 (norm_nonneg _)) (norm_nonneg _))
  have hBbound (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (p : E × (ℕ → ℝ)) :
      ‖B t p‖ ≤ C * M p ^ d * S := by
    have hsum := (hdir.mul_left (C * M p ^ d)).of_norm_bounded (hterm t ht p)
    have hle := (norm_tsum_le_tsum_norm hsum.norm).trans
      (hsum.norm.tsum_le_tsum (hterm t ht p) (hdir.mul_left (C * M p ^ d)))
    simpa only [B, tsum_mul_left, S] using hle
  have hFcont (p : E × (ℕ → ℝ)) : ContinuousOn (fun t => F t p) (Icc 0 1) :=
    hG.continuous_value.comp (hpath p).continuousOn (hmem p)
  have hAcont (p : E × (ℕ → ℝ)) : ContinuousOn (fun t => A t p) (Icc 0 1) :=
    hG.continuous_time.comp (hpath p).continuousOn (hmem p)
  have hBcont (p : E × (ℕ → ℝ)) : ContinuousOn (fun t => B t p) (Icc 0 1) := by
    apply continuousOn_tsum (u := fun j => C * M p ^ d * ‖T (v j)‖ ^ 2)
      ?_ (hdir.mul_left _) (fun j t ht => hterm t ht p j)
    intro j
    exact ((hG.continuous_field_hessian.comp (hpath p).continuousOn (hmem p)).clm_apply
      continuousOn_const).clm_apply continuousOn_const
  have hpathMeas (t : ℝ) : Measurable (fun p : E × (ℕ → ℝ) => p.1 + Real.sqrt t • Z p.2) :=
    measurable_fst.add (((stronglyMeasurable_gaussianSeriesLimitE hA T).measurable.comp measurable_snd).const_smul _)
  have hFmeas (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : AEStronglyMeasurable (F t) μ :=
    ((hG.field_c2 t ht).continuous.measurable.comp (hpathMeas t)).aestronglyMeasurable
  have hAmeas (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : AEStronglyMeasurable (A t) μ := by
    have hc : Continuous (D t) := hG.continuous_time.comp_continuous
      (continuous_const.prodMk continuous_id) (fun x => ⟨ht, mem_univ x⟩)
    exact (hc.measurable.comp (hpathMeas t)).aestronglyMeasurable
  have hBeq (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : B t = fun p =>
      modelCovarianceTrace (G t) (fun j => T (v j)) (p.1 + Real.sqrt t • Z p.2) := by
    funext p
    apply tsum_congr
    intro j
    exact (second_fderiv_eq (hG.field_c2 t ht) _ _ _).symm
  have hBmeas (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : AEStronglyMeasurable (B t) μ := by
    rw [hBeq t ht]
    exact ((measurable_modelCovarianceTrace (G t) (hG.field_c2 t ht) _).comp
      (hpathMeas t)).aestronglyMeasurable
  have hFc : ContinuousOn (fun t => ∫ p, F t p ∂μ) (Icc 0 1) :=
    continuousOn_of_dominated hFmeas
      (fun t ht => Eventually.of_forall fun p => (hbounds t ht p).1) hm
      (Eventually.of_forall hFcont)
  have hAc : ContinuousOn (fun t => ∫ p, A t p ∂μ) (Icc 0 1) :=
    continuousOn_of_dominated hAmeas
      (fun t ht => Eventually.of_forall fun p => (hbounds t ht p).2.1) hm
      (Eventually.of_forall hAcont)
  have hBc : ContinuousOn (fun t => ∫ p, B t p ∂μ) (Icc 0 1) :=
    continuousOn_of_dominated hBmeas
      (fun t ht => Eventually.of_forall fun p => hBbound t ht p) (hm.mul_const S)
      (Eventually.of_forall hBcont)
  refine ⟨hFc, ?_⟩
  apply (hAc.add (continuousOn_const.mul hBc)).congr
  intro t ht
  dsimp only [timeHeatDerivative]
  congr 1
  congr 1
  symm
  change integral μ (B t) = _
  rw [hBeq t ht]
  exact integral_prod _ (integrable_randomBaseHeatIntegrand hA T ν hν
    (modelCovarianceTrace (G t) (fun j => T (v j)))
    (measurable_modelCovarianceTrace (G t) (hG.field_c2 t ht) _)
    (polynomial_modelCovarianceTrace _ hdir (G t) (hG.field_growth ht)) t)

end
end ASDExplicitGamma.Gaussian
