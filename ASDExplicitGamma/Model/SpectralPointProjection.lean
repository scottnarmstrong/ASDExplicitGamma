module

public import ASDExplicitGamma.Model.SpectralMeasure
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic

@[expose] public section

open Complex
open scoped RealInnerProductSpace

namespace ASDExplicitGamma.Model

abbrev Q3ComplexPlane := WithLp 2 (ℂ × ℂ)

/-- A real frequency viewed as a complex vector. -/
def q3ComplexFrequency (ξ : Q3FrequencyPlane) : Q3ComplexPlane :=
  WithLp.toLp 2 ((ξ.fst : ℂ), (ξ.snd : ℂ))

/-- Pointwise orthogonal projection onto the line parallel to the frequency. -/
noncomputable def q3PointHelmholtz (ξ : Q3FrequencyPlane) :
    Q3ComplexPlane →L[ℂ] Q3ComplexPlane :=
  (Submodule.span ℂ {q3ComplexFrequency ξ}).starProjection

/-- The pointwise rank-one formula; its value at zero frequency is zero. -/
theorem q3PointHelmholtz_apply (ξ : Q3FrequencyPlane) (X : Q3ComplexPlane) :
    q3PointHelmholtz ξ X =
      (((ξ.fst : ℂ) * X.fst + (ξ.snd : ℂ) * X.snd) /
        ((ξ.fst ^ 2 + ξ.snd ^ 2 : ℝ) : ℂ)) • q3ComplexFrequency ξ := by
  rw [q3PointHelmholtz, Submodule.starProjection_singleton]
  have hn : ‖q3ComplexFrequency ξ‖ ^ 2 = ξ.fst ^ 2 + ξ.snd ^ 2 := by
    simp only [q3ComplexFrequency, WithLp.prod_norm_sq_eq_of_L2,
      WithLp.toLp_fst, WithLp.toLp_snd, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hi : inner ℂ (q3ComplexFrequency ξ) X =
      (ξ.fst : ℂ) * X.fst + (ξ.snd : ℂ) * X.snd := by
    simp only [WithLp.prod_inner_apply, WithLp.ofLp_fst, WithLp.ofLp_snd,
      q3ComplexFrequency, RCLike.inner_apply,
      Complex.conj_ofReal]
    ring
  rw [hn, hi]
  simp only [RCLike.ofReal_eq_complex_ofReal]

theorem q3PointHelmholtz_norm_le (ξ : Q3FrequencyPlane) (X : Q3ComplexPlane) :
    ‖q3PointHelmholtz ξ X‖ ≤ ‖X‖ :=
  Submodule.norm_starProjection_apply_le _ _

private theorem complex_plane_norm_le (a b : ℂ) :
    ‖WithLp.toLp 2 (a, b)‖ ≤ ‖a‖ + ‖b‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  rw [WithLp.prod_norm_sq_eq_of_L2]
  simp only [WithLp.toLp_fst, WithLp.toLp_snd]
  nlinarith only [mul_nonneg (norm_nonneg a) (norm_nonneg b)]

theorem q3PointHelmholtz_fst_bound (ξ : Q3FrequencyPlane) (a b : ℂ) :
    ‖(q3PointHelmholtz ξ (WithLp.toLp 2 (a, b))).fst‖ ≤ ‖a‖ + ‖b‖ :=
  (WithLp.norm_fst_le ℂ _).trans ((q3PointHelmholtz_norm_le _ _).trans (complex_plane_norm_le _ _))

theorem q3PointHelmholtz_snd_bound (ξ : Q3FrequencyPlane) (a b : ℂ) :
    ‖(q3PointHelmholtz ξ (WithLp.toLp 2 (a, b))).snd‖ ≤ ‖a‖ + ‖b‖ :=
  (WithLp.norm_snd_le ℂ _).trans ((q3PointHelmholtz_norm_le _ _).trans (complex_plane_norm_le _ _))

/-- The residual is perpendicular to its frequency at every point. -/
theorem q3PointHelmholtz_residual_perp (ξ : Q3FrequencyPlane) (X : Q3ComplexPlane) :
    (ξ.fst : ℂ) * (X.fst - (q3PointHelmholtz ξ X).fst) +
      (ξ.snd : ℂ) * (X.snd - (q3PointHelmholtz ξ X).snd) = 0 := by
  have hp := (Submodule.span ℂ {q3ComplexFrequency ξ}).sub_starProjection_mem_orthogonal X
  have hzero := hp (q3ComplexFrequency ξ) (Submodule.mem_span_singleton_self _)
  simp only [WithLp.prod_inner_apply, WithLp.ofLp_fst, WithLp.ofLp_snd,
    q3ComplexFrequency, RCLike.inner_apply,
    Complex.conj_ofReal, WithLp.sub_fst, WithLp.sub_snd] at hzero
  unfold q3PointHelmholtz q3ComplexFrequency
  convert hzero using 1
  ring

/-- The projected vector is orthogonal to every frequency-perpendicular vector. -/
theorem q3PointHelmholtz_inner_perp (ξ : Q3FrequencyPlane) (X G : Q3ComplexPlane)
    (hG : (ξ.fst : ℂ) * G.fst + (ξ.snd : ℂ) * G.snd = 0) :
    inner ℂ (q3PointHelmholtz ξ X) G = 0 := by
  have hg : G ∈ (Submodule.span ℂ {q3ComplexFrequency ξ})ᗮ := by
    rw [Submodule.mem_orthogonal_singleton_iff_inner_left]
    have hc := congrArg (starRingEnd ℂ) hG
    simpa only [map_add, map_mul, map_zero, Complex.conj_ofReal, WithLp.prod_inner_apply, WithLp.ofLp_fst, WithLp.ofLp_snd,
      q3ComplexFrequency, RCLike.inner_apply,
      Complex.conj_ofReal, mul_comm] using hc
  exact hg _ ((Submodule.span ℂ {q3ComplexFrequency ξ}).starProjection_apply_mem X)

end ASDExplicitGamma.Model
