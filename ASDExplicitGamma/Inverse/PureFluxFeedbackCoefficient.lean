module

public import ASDExplicitGamma.Numerics.Inverse.RealBounds

/-! Exact all-load covariance/feedback coefficient for the positive per-shell generator. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
noncomputable section

/-- The source coefficient mu_i, with the literal half-gain cap D_f=63/50.
Its arguments are the covariance rows A_i,B_i, not the inverse history. -/
def pureFluxCovarianceMu (A B : ℝ) : ℝ :=
  (A^2+Real.sqrt (A^4+4*(63/50:ℝ)^2*A^2*B^2))/2

/-- The literal half-gain constant used by the source per-shell coefficient. -/
theorem pureFlux_half_gain_cap : (1/2:ℝ)+(3:ℝ)^(-(1/4:ℝ)) < 63/50 := by
  have hh := Numerics.Inverse.inv_alpha_real.2
  have hn : (Numerics.Inverse.invAlphaUpper:ℝ) < 19/25 := by
    norm_num [Numerics.Inverse.invAlphaUpper]
  rw [Real.rpow_neg_eq_inv_rpow]
  norm_num only [one_div] at hh
  linarith only [hh,hn]

/-- The selected branch is nonnegative and dominates its diagonal entry. -/
theorem pureFlux_covariance_mu_lower (A B : ℝ) :
    0 ≤ pureFluxCovarianceMu A B ∧ A^2 ≤ pureFluxCovarianceMu A B := by
  have hs : A^2 ≤ Real.sqrt (A^4+4*(63/50:ℝ)^2*A^2*B^2) := by
    apply (Real.le_sqrt (sq_nonneg A) (by positivity)).mpr
    nlinarith only [sq_nonneg B,sq_nonneg (A*B)]
  unfold pureFluxCovarianceMu
  constructor <;> nlinarith only [hs,sq_nonneg A]

/-- Exact quadratic equation for the positive feedback branch. -/
theorem pureFlux_covariance_mu_equation (A B : ℝ) :
    pureFluxCovarianceMu A B*(pureFluxCovarianceMu A B-A^2) = ((63/50:ℝ)*A*B)^2 := by
  have h0 : 0 ≤ A^4+4*(63/50:ℝ)^2*A^2*B^2 := by positivity
  have hs := Real.sq_sqrt h0
  unfold pureFluxCovarianceMu
  nlinarith only [hs]

/-- The covariance/feedback quadratic form is bounded on every pair of
channels. This algebraic bound does not restrict the affine load. -/
theorem pureFlux_covariance_quadratic_bound (A B x y : ℝ) :
    A^2*x^2+2*(63/50:ℝ)*A*B*x*y ≤ pureFluxCovarianceMu A B*(x^2+y^2) := by
  let μ := pureFluxCovarianceMu A B
  have hlo : 0 ≤ μ ∧ A^2 ≤ μ := pureFlux_covariance_mu_lower A B
  have he : μ*(μ-A^2) = ((63/50:ℝ)*A*B)^2 := pureFlux_covariance_mu_equation A B
  by_cases hμ : μ=0
  · have hA : A=0 := by rw [hμ] at hlo; nlinarith only [hlo.2,sq_nonneg A]
    change A^2*x^2+2*(63/50:ℝ)*A*B*x*y ≤ μ*(x^2+y^2)
    rw [hA,hμ]
    norm_num
  · have hpos : 0 < μ := lt_of_le_of_ne hlo.1 (Ne.symm hμ)
    have hs := sq_nonneg (μ*y-(63/50:ℝ)*A*B*x)
    have hex : μ*(μ*(x^2+y^2)-(A^2*x^2+2*(63/50:ℝ)*A*B*x*y)) =
        (μ*y-(63/50:ℝ)*A*B*x)^2 := by
      have hmul := congrArg (fun t : ℝ => t*x^2) he
      nlinarith only [hmul]
    have hh : 0 ≤ μ*(μ*(x^2+y^2)-(A^2*x^2+2*(63/50:ℝ)*A*B*x*y)) := hex.symm ▸ hs
    have hfin := (mul_nonneg_iff_of_pos_left hpos).mp hh
    exact sub_nonneg.mp hfin

/-- Monotonicity in the nonnegative covariance rows. -/
theorem pureFlux_covariance_mu_mono (A B A' B' : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hAA : A ≤ A') (hBB : B ≤ B') : pureFluxCovarianceMu A B ≤ pureFluxCovarianceMu A' B' := by
  have hA2 := pow_le_pow_left₀ hA hAA 2
  have hA4 := pow_le_pow_left₀ hA hAA 4
  have hB2 := pow_le_pow_left₀ hB hBB 2
  have hprod := mul_le_mul hA2 hB2 (sq_nonneg B) (sq_nonneg A')
  have hdisc : A^4+4*(63/50:ℝ)^2*A^2*B^2 ≤ A'^4+4*(63/50:ℝ)^2*A'^2*B'^2 := by
    nlinarith only [hA4,hprod]
  have hs := Real.sqrt_le_sqrt hdisc
  unfold pureFluxCovarianceMu
  nlinarith only [hA2,hs]

/-- A non-strict square-root certificate also allows a zero covariance row. -/
theorem pureFlux_covariance_mu_le_of_certificate (A B C : ℝ)
    (hC : 0 ≤ 2*C-A^2)
    (hroot : A^4+4*(63/50:ℝ)^2*A^2*B^2 ≤ (2*C-A^2)^2) :
    pureFluxCovarianceMu A B ≤ C := by
  have hs : Real.sqrt (A^4+4*(63/50:ℝ)^2*A^2*B^2) ≤ 2*C-A^2 :=
    Real.sqrt_le_iff.mpr ⟨hC,hroot⟩
  unfold pureFluxCovarianceMu
  linarith only [hs]

/-- Source tail coefficient 233/100, valid for every nonnegative row B<=A. -/
theorem pureFlux_covariance_mu_tail_bound (A B : ℝ) (hB : 0 ≤ B) (hBA : B ≤ A) :
    pureFluxCovarianceMu A B ≤ (233/100:ℝ)*A^2 := by
  apply pureFlux_covariance_mu_le_of_certificate
  · nlinarith only [sq_nonneg A]
  · have hh := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hB hBA 2) (sq_nonneg A)
    nlinarith only [hh,sq_nonneg (A^2)]

end
end ASDExplicitGamma.Inverse
