module

public import ASDExplicitGamma.Model.SpectralHelmholtzProjection
public import ASDExplicitGamma.Model.SpectralMassSymmetry
public import ASDExplicitGamma.Model.SpectralIsometry

@[expose] public section

open MeasureTheory Complex

namespace ASDExplicitGamma.Model

/-- The spectral image of the J4 forcing in direction `(1,0)`. -/
noncomputable def q3SpectralSecondForcing (h : ℝ) : Q3SpectralVector h :=
  WithLp.toLp 2 (0, q3SpectralCharacter h 0)

theorem q3SpectralSecondForcing_value (h : ℝ) :
    (fun ξ => q3SpectralVectorValue (q3SpectralSecondForcing h) ξ) =ᵐ[q3SpectralMeasure h]
      fun _ => WithLp.toLp 2 ((0 : ℂ), (1 : ℂ)) := by
  filter_upwards [Lp.coeFn_zero ℂ 2 (q3SpectralMeasure h),
    q3SpectralCharacter_coeFn h 0] with ξ h0 h1
  simp only [WithLp.zero_fst, WithLp.zero_snd, mul_zero, add_zero, ofReal_zero,
    zero_mul, exp_zero] at h1
  apply WithLp.ofLp_injective 2
  exact Prod.ext h0 h1

private theorem point_projection_second_pairing (ξ : Q3FrequencyPlane) :
    inner ℂ (WithLp.toLp 2 ((0 : ℂ), (1 : ℂ)))
      (q3PointHelmholtz ξ (WithLp.toLp 2 ((0 : ℂ), (1 : ℂ)))) =
      ((ξ.snd ^ 2 / (ξ.fst ^ 2 + ξ.snd ^ 2) : ℝ) : ℂ) := by
  rw [q3PointHelmholtz_apply]
  simp only [WithLp.prod_inner_apply, WithLp.ofLp_fst, WithLp.ofLp_snd,
    WithLp.smul_fst, WithLp.smul_snd, WithLp.toLp_fst, WithLp.toLp_snd,
    q3ComplexFrequency, RCLike.inner_apply, map_zero, map_one, mul_zero, mul_one,
    zero_add, smul_eq_mul]
  push_cast
  ring

/-- The literal planar spectral projection energy is one half of `h²`. -/
theorem q3SpectralSecondForcing_projection_energy (h : ℝ) :
    ‖(q3SpectralPotentialSubspace h).starProjection (q3SpectralSecondForcing h)‖ ^ 2 = h ^ 2 / 2 := by
  let K := q3SpectralPotentialSubspace h
  let X := q3SpectralSecondForcing h
  let P := K.starProjection X
  have hinner : inner ℂ X P = inner ℂ P P := by
    have hz := K.starProjection_inner_eq_zero X P (K.starProjection_apply_mem X)
    rw [inner_sub_left] at hz
    exact sub_eq_zero.mp hz
  have hnorm : ‖P‖ ^ 2 = (inner ℂ X P).re := by
    rw [hinner]
    simpa only [RCLike.re_eq_complex_re] using norm_sq_eq_re_inner (𝕜 := ℂ) P
  have hi : inner ℂ X P = ∫ ξ : Q3FrequencyPlane,
      ((ξ.snd ^ 2 / (ξ.fst ^ 2 + ξ.snd ^ 2) : ℝ) : ℂ) ∂q3SpectralMeasure h := by
    change inner ℂ (q3SpectralSecondForcing h)
      ((q3SpectralPotentialSubspace h).starProjection (q3SpectralSecondForcing h)) = _
    rw [q3HelmholtzMultiplier, q3SpectralVector_inner]
    apply integral_congr_ae
    filter_upwards [q3SpectralSecondForcing_value h,
      q3HelmholtzProjection_value h (q3SpectralSecondForcing h)] with ξ hX hP
    rw [hP, hX]
    exact point_projection_second_pairing ξ
  change ‖P‖ ^ 2 = _
  rw [hnorm, hi, integral_complex_ofReal, Complex.ofReal_re,
    q3SpectralMeasure_diagonal_energy]

end ASDExplicitGamma.Model
