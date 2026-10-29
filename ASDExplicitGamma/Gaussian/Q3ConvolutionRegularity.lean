module

public import ASDExplicitGamma.Gaussian.Q3SectionBounds
public import ASDExplicitGamma.Gaussian.Q3SectionDerivative
public import ASDExplicitGamma.Gaussian.LocalizedKernelDerivative

/-! # Continuous spatial derivatives of convolution against every white-noise L² input -/

@[expose] public section

open MeasureTheory Homogenization Set Filter
open scoped Topology RealInnerProductSpace

namespace ASDExplicitGamma.Gaussian

/-- The actual convolution coordinate, evaluated using its Hilbert-space kernel section. -/
noncomputable def q3Convolution (b : ℝ) (L : {l : ℝ // 0 < l}) (a : H3Index)
    (u : WhiteNoise) (x : Vec 2) : ℝ := ⟪u, q3Section b L a x⟫

theorem q3Convolution_continuous (b : ℝ) (L : {l : ℝ // 0 < l}) (a : H3Index)
    (u : WhiteNoise) : Continuous (q3Convolution b L a u) :=
  continuous_const.inner (q3Section_continuous b L a)

theorem q3Convolution_eq_integral (b : ℝ) (L : {l : ℝ // 0 < l}) (a : H3Index)
    (u : WhiteNoise) (x : Vec 2) :
    q3Convolution b L a u x = ∫ y, q3SectionFunction b L a x y * u y := by
  rw [q3Convolution, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(q3SectionFunction_memLp b L a x).coeFn_toLp] with y hy
  change q3Section b L a x y = q3SectionFunction b L a x y at hy
  simp only [RCLike.inner_apply, starRingEnd_apply, star_trivial, hy]

theorem q3SectionFunction_measurable (b : ℝ) (L : {l : ℝ // 0 < l}) (a : H3Index)
    (x : Vec 2) : Measurable (q3SectionFunction b L a x) := by
  unfold q3SectionFunction
  exact measurable_const.mul
    (((q3Derivative_measurable a.1.1).comp (by fun_prop)).mul
      ((q3Derivative_measurable a.1.2).comp (by fun_prop)))

/-- The derivative of convolution is the convolution with the successor derivative kernels. -/
theorem q3Convolution_hasFDerivAt (b : ℝ) (L : {l : ℝ // 0 < l}) (a : H3Index)
    (ha : a.1.1.val + a.1.2.val ≤ 2) (u : WhiteNoise) (x : Vec 2) :
    HasFDerivAt (q3Convolution b L a u)
      (q3Convolution b L (h3Next a 0 ha) u x • (ContinuousLinearMap.proj 0 : Vec 2 →L[ℝ] ℝ) +
        q3Convolution b L (h3Next a 1 ha) u x • (ContinuousLinearMap.proj 1 : Vec 2 →L[ℝ] ℝ)) x := by
  obtain ⟨C, hC⟩ := q3SectionFunction_lipschitz b L a ha
  have hm : AEStronglyMeasurable (q3SectionDerivative b L a ha x) := by
    exact (((q3SectionFunction_measurable b L (h3Next a 0 ha) x).aestronglyMeasurable.smul_const
      (ContinuousLinearMap.proj 0 : Vec 2 →L[ℝ] ℝ)).add
      ((q3SectionFunction_measurable b L (h3Next a 1 ha) x).aestronglyMeasurable.smul_const
        (ContinuousLinearMap.proj 1 : Vec 2 →L[ℝ] ℝ)))
  obtain ⟨hi, hd⟩ := hasFDerivAt_localized_kernel_integral (q3SectionFunction b L a)
    (q3SectionDerivative b L a ha x) x u (Metric.closedBall x (1 + L.1))
    (isCompact_closedBall _ _) (Metric.ball x 1) (Metric.ball_mem_nhds x (by norm_num)) C
    (q3SectionFunction_measurable b L a) (q3SectionFunction_memLp b L a x) hm hC
    (fun z hz y hy => q3SectionFunction_local_support b L a x hz hy)
    (q3SectionFunction_hasFDerivAt_ae b L a ha x)
  have he : (∫ y, u y • q3SectionDerivative b L a ha x y) =
      q3Convolution b L (h3Next a 0 ha) u x • (ContinuousLinearMap.proj 0 : Vec 2 →L[ℝ] ℝ) +
        q3Convolution b L (h3Next a 1 ha) u x • (ContinuousLinearMap.proj 1 : Vec 2 →L[ℝ] ℝ) := by
    ext h
    rw [ContinuousLinearMap.integral_apply hi]
    have h₀ := (q3SectionFunction_memLp b L (h3Next a 0 ha) x).integrable_mul (Lp.memLp u)
    have h₁ := (q3SectionFunction_memLp b L (h3Next a 1 ha) x).integrable_mul (Lp.memLp u)
    change Integrable (fun y => q3SectionFunction b L (h3Next a 0 ha) x y * u y) at h₀
    change Integrable (fun y => q3SectionFunction b L (h3Next a 1 ha) x y * u y) at h₁
    simp only [q3SectionDerivative, smul_apply,
      add_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
    simp_rw [mul_add, ← mul_assoc, mul_comm (u _)]
    rw [integral_add (h₀.mul_const (h 0)) (h₁.mul_const (h 1)), integral_mul_const, integral_mul_const,
      ← q3Convolution_eq_integral, ← q3Convolution_eq_integral]
  rw [he] at hd
  simpa only [← q3Convolution_eq_integral] using hd

/-- Continuity of all successor kernels upgrades the convolution derivatives to C¹. -/
theorem q3Convolution_contDiff_one (b : ℝ) (L : {l : ℝ // 0 < l}) (a : H3Index)
    (ha : a.1.1.val + a.1.2.val ≤ 2) (u : WhiteNoise) :
    ContDiff ℝ 1 (q3Convolution b L a u) := by
  apply contDiff_one_iff_fderiv.mpr
  refine ⟨fun x => (q3Convolution_hasFDerivAt b L a ha u x).differentiableAt, ?_⟩
  have he : fderiv ℝ (q3Convolution b L a u) = fun x =>
      q3Convolution b L (h3Next a 0 ha) u x • (ContinuousLinearMap.proj 0 : Vec 2 →L[ℝ] ℝ) +
        q3Convolution b L (h3Next a 1 ha) u x • (ContinuousLinearMap.proj 1 : Vec 2 →L[ℝ] ℝ) :=
    funext fun x => (q3Convolution_hasFDerivAt b L a ha u x).fderiv
  rw [he]
  exact ((q3Convolution_continuous b L (h3Next a 0 ha) u).smul continuous_const).add
    ((q3Convolution_continuous b L (h3Next a 1 ha) u).smul continuous_const)

end ASDExplicitGamma.Gaussian
