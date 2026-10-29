module

public import ASDExplicitGamma.Model.SpectralCovariance
public import ASDExplicitGamma.Model.SpectralModel
public import ASDExplicitGamma.Model.SpectralStreamLaw
public import ASDExplicitGamma.Model.SpectralGraphNorm
public import Mathlib.Analysis.Normed.Operator.Extend

@[expose] public section

open MeasureTheory FourierTransform Complex
open scoped RealInnerProductSpace

namespace ASDExplicitGamma.Model

/-- The character corresponding to a stream observation at `x`. -/
noncomputable def q3SpectralCharacter (h : ℝ) (x : Q3FrequencyPlane) :
    Lp ℂ 2 (q3SpectralMeasure h) :=
  BoundedContinuousFunction.toLp 2 (q3SpectralMeasure h) ℂ
    (BoundedContinuousFunction.innerProbChar ((2 * Real.pi) • x))

theorem q3SpectralCharacter_coeFn (h : ℝ) (x : Q3FrequencyPlane) :
    (q3SpectralCharacter h x : Q3FrequencyPlane → ℂ) =ᵐ[q3SpectralMeasure h]
      fun ξ => exp (((2 * Real.pi * (ξ.fst * x.fst + ξ.snd * x.snd) : ℝ) : ℂ) * I) := by
  unfold q3SpectralCharacter
  have hc := BoundedContinuousFunction.coeFn_toLp 2 (q3SpectralMeasure h) ℂ
    (BoundedContinuousFunction.innerProbChar ((2 * Real.pi) • x))
  filter_upwards [hc] with ξ hξ
  rw [hξ, BoundedContinuousFunction.innerProbChar_apply, inner_smul_right,
    WithLp.prod_inner_apply]
  simp only [RCLike.inner_apply, conj_trivial, WithLp.ofLp_fst, WithLp.ofLp_snd]
  congr 1
  push_cast
  ring

/-- The spectral characters have precisely the q3 covariance kernel. -/
theorem q3SpectralCharacter_inner (h : ℝ) (x y : Q3FrequencyPlane) :
    inner ℂ (q3SpectralCharacter h x) (q3SpectralCharacter h y) =
      (h ^ 2 * q3Cov (y.fst - x.fst) * q3Cov (y.snd - x.snd) : ℝ) := by
  rw [L2.inner_def]
  calc
    (∫ ξ, inner ℂ (q3SpectralCharacter h x ξ) (q3SpectralCharacter h y ξ)
        ∂q3SpectralMeasure h) =
        ∫ ξ : Q3FrequencyPlane,
          exp (((2 * Real.pi * (ξ.fst * (y.fst - x.fst) +
            ξ.snd * (y.snd - x.snd)) : ℝ) : ℂ) * I) ∂q3SpectralMeasure h := by
      apply integral_congr_ae
      filter_upwards [q3SpectralCharacter_coeFn h x, q3SpectralCharacter_coeFn h y]
        with ξ hx hy
      rw [RCLike.inner_apply, hx, hy, ← Complex.exp_conj, ← Complex.exp_add]
      congr 1
      simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
      push_cast
      ring
    _ = _ := q3SpectralMeasure_exponential_integral h _ _

/-- The spectral characters span the entire complex spectral `L²` space. -/
theorem q3SpectralCharacter_span_dense (h : ℝ) :
    (Submodule.span ℂ (Set.range (q3SpectralCharacter h))).topologicalClosure = ⊤ :=
  exponential_span_dense_rescale (q3SpectralMeasure h) (2 * Real.pi)
    (mul_ne_zero (by norm_num) Real.pi_ne_zero)

theorem q3SpectralCharacter_norm_sq (h : ℝ) (x : Q3FrequencyPlane) :
    ‖q3SpectralCharacter h x‖ ^ 2 = h ^ 2 := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), q3SpectralCharacter_inner]
  simp only [sub_self, q3Cov_zero_eq_one, mul_one, RCLike.re_eq_complex_re, Complex.ofReal_re]

/-- The elementary two-point covariance quadratic form is nonnegative. -/
theorem q3Cov_two_point_nonneg (h : ℝ) (x y : Q3FrequencyPlane) :
    0 ≤ h ^ 2 * (2 + 2 * q3Cov (y.fst - x.fst) * q3Cov (y.snd - x.snd)) := by
  have hn := sq_nonneg ‖q3SpectralCharacter h x + q3SpectralCharacter h y‖
  rw [norm_add_sq (𝕜 := ℂ), q3SpectralCharacter_norm_sq, q3SpectralCharacter_norm_sq,
    q3SpectralCharacter_inner, RCLike.re_eq_complex_re, Complex.ofReal_re] at hn
  nlinarith only [hn]

/-- The frequency-plane point associated with a source spatial vector. -/
def q3SpectralPoint (x : Homogenization.Vec 2) : Q3FrequencyPlane :=
  WithLp.toLp 2 (x 0, x 1)

private theorem q3Cov_sub_symm (x y : ℝ) : q3Cov (y - x) = q3Cov (x - y) := by
  rw [show y - x = -(x - y) by ring, q3Cov_even]

/-- The frozen Gaussian law has exactly the same real covariance kernel as the
spectral characters. -/
theorem q3StreamKoopman_inner
    (M : Algsuperdiff.Section3.ABKModel 2) (h : ℝ)
    (hM : ASDExplicitGamma.PlanarQ3Gaussian M h) (x y : Homogenization.Vec 2) :
    inner ℝ (q3StreamKoopman M x (q3StreamOriginL2 M))
      (q3StreamKoopman M y (q3StreamOriginL2 M)) =
      h ^ 2 * q3Cov ((x - y) 0) * q3Cov ((x - y) 1) := by
  let A := q3StreamKoopman M x (q3StreamOriginL2 M)
  let B := q3StreamKoopman M y (q3StreamOriginL2 M)
  have hA : ‖A‖ ^ 2 = h ^ 2 := by
    rw [(q3StreamKoopman M x).norm_map]
    exact q3StreamOriginL2_norm_sq M h hM
  have hB : ‖B‖ ^ 2 = h ^ 2 := by
    rw [(q3StreamKoopman M y).norm_map]
    exact q3StreamOriginL2_norm_sq M h hM
  have hs : ‖A + B‖ ^ 2 = max (q3CovarianceQuadratic h ![x, y] (fun _ => 1)) 0 := by
    simpa [A, B, Fin.sum_univ_two] using
      q3StreamSum_norm_sq_max M h hM ![x, y] (fun _ => 1)
  have hq : q3CovarianceQuadratic h ![x, y] (fun _ => 1) =
      h ^ 2 * (2 + 2 * q3Cov (x 0 - y 0) * q3Cov (x 1 - y 1)) := by
    simp only [q3CovarianceQuadratic, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, one_mul, Pi.sub_apply, sub_self, q3Cov_zero_eq_one,
      mul_one]
    rw [q3Cov_sub_symm (x 0) (y 0), q3Cov_sub_symm (x 1) (y 1)]
    ring
  have hp := q3Cov_two_point_nonneg h (q3SpectralPoint y) (q3SpectralPoint x)
  simp only [q3SpectralPoint, WithLp.toLp_fst, WithLp.toLp_snd] at hp
  rw [hq, max_eq_left hp] at hs
  have hn := norm_add_sq_real A B
  change inner ℝ A B = _
  simp only [Pi.sub_apply]
  nlinarith only [hs, hn, hA, hB]

end ASDExplicitGamma.Model
