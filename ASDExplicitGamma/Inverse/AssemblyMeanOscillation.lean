module

public import ASDExplicitGamma.Inverse.AssemblyLipschitz
public import ASDExplicitGamma.Inverse.AssemblyActiveTriangleTrace

/-! Parent derivative control pays every contained-cube wave mean. -/

@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory ASDExplicitGamma.Triadic
open scoped ENNReal
noncomputable section

/-- Two probability averages of the same integrable function differ by at
most a common almost-everywhere oscillation bound. -/
theorem assembly_average_difference_le {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : Ω → ℝ) (hfμ : Integrable f μ) (hfν : Integrable f ν) (C : ℝ)
    (hC : ∀ᵐ x ∂μ, ∀ᵐ y ∂ν, ‖f x-f y‖ ≤ C) :
    |(∫ x, f x ∂μ)-(∫ y, f y ∂ν)| ≤ C := by
  have hx : ∀ᵐ x ∂μ, ‖f x-(∫ y, f y ∂ν)‖ ≤ C := by
    filter_upwards [hC] with x hx
    have hh := norm_integral_le_of_norm_le_const hx
    rw [integral_sub (integrable_const (f x)) hfν,integral_const,probReal_univ,
      smul_eq_mul,one_mul,mul_one] at hh
    exact hh
  have hh := norm_integral_le_of_norm_le_const hx
  rw [integral_sub hfμ (integrable_const _),integral_const,probReal_univ,
    smul_eq_mul,one_mul,mul_one,Real.norm_eq_abs] at hh
  exact hh

/-- Any two points of one physical square are at distance at most its side. -/
theorem assembly_cube_dist_le (Q : TriadicCube 2) {x y : Vec 2}
    (hx : x ∈ cubeSet Q) (hy : y ∈ cubeSet Q) : dist x y ≤ cubeScaleFactor Q := by
  have hx' := Metric.mem_closedBall.mp (cubeSet_subset_closedBall Q hx)
  have hy' := Metric.mem_closedBall.mp (cubeSet_subset_closedBall Q hy)
  calc
    dist x y ≤ dist x (cubeCenter Q)+dist (cubeCenter Q) y := dist_triangle _ _ _
    _ ≤ cubeRadius Q+cubeRadius Q := add_le_add hx' (by rwa [dist_comm])
    _ = cubeScaleFactor Q := by rw [cubeScaleFactor_eq_two_mul_cubeRadius]; ring

/-- A parent W^{2,∞} direction controls the difference between its own average and
every descendant average by twice the actual parent Dsharp. -/
theorem assembly_descendant_mean_difference (Q : TriadicCube 2)
    (h : PlanarW2Infinity Q) {R : TriadicCube 2} {j : ℕ}
    (hR : R ∈ descendantsAtDepth Q j) :
    |cubeAverage R (h.restrict hR).value.toFun-cubeAverage Q h.value.toFun| ≤
      2*sensitivityDsharp Q h := by
  let meanProbabilityQ : IsProbabilityMeasure (normalizedCubeMeasure Q) :=
    ⟨normalizedCubeMeasure_apply_univ Q⟩
  let meanProbabilityR : IsProbabilityMeasure (normalizedCubeMeasure R) :=
    ⟨normalizedCubeMeasure_apply_univ R⟩
  obtain ⟨r,hr,hAE⟩ := assembly_W2_lipschitz_representative h
  let K := planarGradientLInf h
  have hK : 0 ≤ K := ENNReal.toReal_nonneg
  have hAEQ : h.value.toFun =ᵐ[normalizedCubeMeasure Q] r := by
    unfold normalizedCubeMeasure cubeMeasure
    apply Measure.ae_smul_measure
    exact (ae_restrict_cubeSet_iff).mpr hAE
  have hAER : (h.restrict hR).value.toFun =ᵐ[normalizedCubeMeasure R] r := by
    unfold normalizedCubeMeasure cubeMeasure
    apply Measure.ae_smul_measure
    exact ae_eq_cubeSet_of_mem_descendantsAtDepth_of_ae_eq_openCubeSet hR hAE
  have hQmem : ∀ᵐ x ∂normalizedCubeMeasure Q, x ∈ cubeSet Q := by
    unfold normalizedCubeMeasure cubeMeasure
    apply Measure.ae_smul_measure
    exact ae_restrict_mem (measurableSet_cubeSet Q)
  have hRmem : ∀ᵐ x ∂normalizedCubeMeasure R, x ∈ cubeSet Q := by
    unfold normalizedCubeMeasure cubeMeasure
    apply Measure.ae_smul_measure
    filter_upwards [ae_restrict_mem (measurableSet_cubeSet R)] with x hx
    exact cubeSet_subset_of_mem_descendantsAtDepth hR hx
  have hosc : ∀ᵐ x ∂normalizedCubeMeasure R, ∀ᵐ y ∂normalizedCubeMeasure Q,
      ‖(h.restrict hR).value.toFun x-h.value.toFun y‖ ≤ 2*K*cubeScaleFactor Q := by
    filter_upwards [hAER,hRmem] with x hxr hx
    filter_upwards [hAEQ,hQmem] with y hyr hy
    rw [hxr,hyr,← dist_eq_norm]
    have hh := hr.dist_le_mul x y
    rw [Real.coe_toNNReal (2*planarGradientLInf h)
      (mul_nonneg (by norm_num) hK)] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left (assembly_cube_dist_le Q hx hy)
      (mul_nonneg (by norm_num) hK))
  have hsame : (h.restrict hR).value.toFun=h.value.toFun := rfl
  have hdiff := assembly_average_difference_le (normalizedCubeMeasure R) (normalizedCubeMeasure Q)
    h.value.toFun
    (by rw [← hsame]; exact (h.restrict hR).value.memL2_normalizedCubeMeasure.integrable (by norm_num))
    (h.value.memL2_normalizedCubeMeasure.integrable (by norm_num))
    (2*K*cubeScaleFactor Q) (by simpa only [hsame] using hosc)
  rw [← cubeAverage_eq_integral_normalizedCubeMeasure,← cubeAverage_eq_integral_normalizedCubeMeasure] at hdiff
  rw [hsame]
  apply hdiff.trans
  have hroot : 1 ≤ Real.sqrt 2 := by norm_num
  have hLK : 0 ≤ cubeScaleFactor Q*K := mul_nonneg (Homogenization.cubeScaleFactor_pos' Q).le hK
  have hfirst : cubeScaleFactor Q*K ≤ sensitivityD1 Q h := by
    unfold sensitivityD1
    have hh := mul_le_mul_of_nonneg_left hroot hLK
    dsimp only [K] at hh
    convert hh using 1 <;> ring
  have hsecond : 0 ≤ sensitivityKappaH*sensitivityD2 Q h := by
    unfold sensitivityKappaH sensitivityD2 planarHessianFrobeniusLInf
      planarW1DerivativeFrobeniusLInf planarC0 planarC1
    positivity
  unfold sensitivityDsharp
  linarith only [hfirst,hsecond]

/-- The same derivative bound controls the parent-centered direction at
almost every physical point, as needed for weighted active-cell integration. -/
theorem assembly_parent_mean_oscillation (Q : TriadicCube 2) (h : PlanarW2Infinity Q) :
    ∀ᵐ x ∂normalizedCubeMeasure Q,
      |h.value.toFun x-cubeAverage Q h.value.toFun| ≤ 2*sensitivityDsharp Q h := by
  let oscillationProbability : IsProbabilityMeasure (normalizedCubeMeasure Q) :=
    ⟨normalizedCubeMeasure_apply_univ Q⟩
  obtain ⟨r,hr,hAE⟩ := assembly_W2_lipschitz_representative h
  let K := planarGradientLInf h
  have hK : 0 ≤ K := ENNReal.toReal_nonneg
  have hAEQ : h.value.toFun =ᵐ[normalizedCubeMeasure Q] r := by
    unfold normalizedCubeMeasure cubeMeasure
    apply Measure.ae_smul_measure
    exact ae_restrict_cubeSet_iff.mpr hAE
  have hQmem : ∀ᵐ x ∂normalizedCubeMeasure Q, x ∈ cubeSet Q := by
    unfold normalizedCubeMeasure cubeMeasure
    apply Measure.ae_smul_measure
    exact ae_restrict_mem (measurableSet_cubeSet Q)
  have hrint : Integrable r (normalizedCubeMeasure Q) :=
    (h.value.memL2_normalizedCubeMeasure.integrable (by norm_num)).congr hAEQ
  have hmean : (∫ y, r y ∂normalizedCubeMeasure Q)=cubeAverage Q h.value.toFun := by
    rw [cubeAverage_eq_integral_normalizedCubeMeasure]
    exact integral_congr_ae hAEQ.symm
  have hscale : 2*K*cubeScaleFactor Q ≤ 2*sensitivityDsharp Q h := by
    have hroot : 1 ≤ Real.sqrt 2 := by norm_num
    have hLK : 0 ≤ cubeScaleFactor Q*K := mul_nonneg (Homogenization.cubeScaleFactor_pos' Q).le hK
    have hfirst : cubeScaleFactor Q*K ≤ sensitivityD1 Q h := by
      unfold sensitivityD1
      have hh := mul_le_mul_of_nonneg_left hroot hLK
      dsimp only [K] at hh
      convert hh using 1 <;> ring
    have hsecond : 0 ≤ sensitivityKappaH*sensitivityD2 Q h := by
      unfold sensitivityKappaH sensitivityD2 planarHessianFrobeniusLInf
        planarW1DerivativeFrobeniusLInf planarC0 planarC1
      positivity
    unfold sensitivityDsharp
    linarith only [hfirst,hsecond]
  filter_upwards [hAEQ,hQmem] with x hxr hx
  have hbound : ∀ᵐ y ∂normalizedCubeMeasure Q, ‖r x-r y‖ ≤ 2*K*cubeScaleFactor Q := by
    filter_upwards [hQmem] with y hy
    rw [← dist_eq_norm]
    have hh := hr.dist_le_mul x y
    rw [Real.coe_toNNReal (2*planarGradientLInf h) (mul_nonneg (by norm_num) hK)] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left (assembly_cube_dist_le Q hx hy)
      (mul_nonneg (by norm_num) hK))
  have hh := norm_integral_le_of_norm_le_const hbound
  rw [integral_sub (integrable_const (r x)) hrint,integral_const,probReal_univ,
    smul_eq_mul,one_mul,mul_one,hmean,Real.norm_eq_abs] at hh
  rw [hxr]
  exact hh.trans hscale

end
end ASDExplicitGamma.Inverse
