module

public import ASDExplicitGamma.Inverse.PureFluxFeedbackCoefficient
public import ASDExplicitGamma.Numerics.Inverse.Covariance0

/-! Literal source covariance rows and genuine real soundness of their upward coefficients. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
noncomputable section

/-- Source rho at shell i+1, shifted by q protected generations. -/
def pureFluxCovarianceRho (q i : ℕ) : ℝ := (1/3:ℝ)^(q+i+1)

def pureFluxCovarianceDelta (q i : ℕ) : ℝ := min (1/243:ℝ) (pureFluxCovarianceRho q i)

def pureFluxCovarianceAr : ℝ := Real.sqrt ((78/5:ℝ)/2)
def pureFluxCovarianceBA : ℝ := (36/25:ℝ)*Real.sqrt (2*(78/5:ℝ))
def pureFluxCovarianceBB : ℝ := (36/25:ℝ)*Real.sqrt (78/5:ℝ)
def pureFluxCovarianceCA : ℝ := (57/200:ℝ)*Real.sqrt (2*((3432/5:ℝ)+(78/5:ℝ)^2))
def pureFluxCovarianceCB : ℝ := (57/200:ℝ)*Real.sqrt ((3432/5:ℝ)+(78/5:ℝ)^2)

/-- Source first covariance row, using the coded C1=1.440 and C2=.285. -/
def pureFluxCovarianceA (q i : ℕ) : ℝ :=
  pureFluxCovarianceAr*pureFluxCovarianceRho q i+
    pureFluxCovarianceBA*pureFluxCovarianceDelta q i+
    pureFluxCovarianceCA*(pureFluxCovarianceDelta q i)^2

/-- Source reciprocal covariance row, with the smaller covariance traces. -/
def pureFluxCovarianceB (q i : ℕ) : ℝ :=
  pureFluxCovarianceAr*pureFluxCovarianceRho q i+
    pureFluxCovarianceBB*pureFluxCovarianceDelta q i+
    pureFluxCovarianceCB*(pureFluxCovarianceDelta q i)^2

theorem pureFlux_covariance_rho_pos (q i : ℕ) : 0 < pureFluxCovarianceRho q i := by
  unfold pureFluxCovarianceRho
  positivity

theorem pureFlux_covariance_delta_bounds (q i : ℕ) :
    0 ≤ pureFluxCovarianceDelta q i ∧ pureFluxCovarianceDelta q i ≤ pureFluxCovarianceRho q i := by
  exact ⟨le_min (by norm_num) (pureFlux_covariance_rho_pos q i).le,min_le_right _ _⟩

/-- The reciprocal row is nonnegative and no larger than the first row. -/
theorem pureFlux_covariance_rows_order (q i : ℕ) :
    0 ≤ pureFluxCovarianceB q i ∧ pureFluxCovarianceB q i ≤ pureFluxCovarianceA q i := by
  have hρ := (pureFlux_covariance_rho_pos q i).le
  have hδ := (pureFlux_covariance_delta_bounds q i).1
  have hb : pureFluxCovarianceBB ≤ pureFluxCovarianceBA :=
    mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by norm_num : (78/5:ℝ) ≤ 2*(78/5:ℝ))) (by norm_num)
  have hc : pureFluxCovarianceCB ≤ pureFluxCovarianceCA :=
    mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by norm_num : (3432/5:ℝ)+(78/5:ℝ)^2 ≤
      2*((3432/5:ℝ)+(78/5:ℝ)^2))) (by norm_num)
  constructor
  · unfold pureFluxCovarianceB pureFluxCovarianceAr pureFluxCovarianceBB pureFluxCovarianceCB
    positivity
  · unfold pureFluxCovarianceB pureFluxCovarianceA
    exact add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_right hb hδ))
      (mul_le_mul_of_nonneg_right hc (sq_nonneg _))

/-- The exact source coefficient obeys the analytic all-shell tail cap. -/
theorem pureFlux_covariance_rows_mu_tail (q i : ℕ) :
    pureFluxCovarianceMu (pureFluxCovarianceA q i) (pureFluxCovarianceB q i) ≤
      (233/100:ℝ)*(pureFluxCovarianceA q i)^2 :=
  pureFlux_covariance_mu_tail_bound _ _ (pureFlux_covariance_rows_order q i).1 (pureFlux_covariance_rows_order q i).2

/-- Rational scaled-square certificate soundness for an actual covariance radical. -/
theorem pureFlux_scaled_sqrt_cap (c x u : ℚ) (hc : 0 ≤ c) (hu : 0 ≤ u) (hs : c^2*x < u^2) :
    (c:ℝ)*Real.sqrt (x:ℝ) ≤ (u:ℝ) := by
  have hh := Numerics.Inverse.inv_sqrt_upper hu hs
  have hcR : (0:ℝ) ≤ c := by exact_mod_cast hc
  have he : Real.sqrt ((c^2*x:ℚ):ℝ) = (c:ℝ)*Real.sqrt (x:ℝ) := by
    push_cast
    rw [Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq_eq_abs,abs_of_nonneg hcR]
  rw [he] at hh
  exact hh

/-- Every upward q3 coefficient in the numeric row bounds its actual
real radical. The two source row families use the same coefficient constants. -/
theorem pureFlux_covariance_coefficient_caps :
    pureFluxCovarianceAr ≤ (Numerics.Inverse.invCov0Ar:ℝ) ∧
    pureFluxCovarianceBA ≤ (Numerics.Inverse.invCov0BA:ℝ) ∧
    pureFluxCovarianceBB ≤ (Numerics.Inverse.invCov0BB:ℝ) ∧
    pureFluxCovarianceCA ≤ (Numerics.Inverse.invCov0CA:ℝ) ∧
    pureFluxCovarianceCB ≤ (Numerics.Inverse.invCov0CB:ℝ) := by
  rcases Numerics.Inverse.invCov0_coefficient_roots with ⟨har,harsq,hba,hbasq,hbb,hbbsq,hca,hcasq,hcb,hcbsq⟩
  rw [show (1.440:ℚ)=36/25 by norm_num] at hbasq hbbsq
  rw [show (0.285:ℚ)=57/200 by norm_num] at hcasq hcbsq
  rw [show (2*78/5:ℚ)=2*(78/5) by norm_num] at hbasq
  refine ⟨?_,?_,?_,?_,?_⟩
  · simpa only [pureFluxCovarianceAr,Rat.cast_div,Rat.cast_ofNat] using!
      Numerics.Inverse.inv_sqrt_upper har.le harsq
  · simpa only [pureFluxCovarianceBA,Rat.cast_div,Rat.cast_mul,Rat.cast_ofNat] using!
      pureFlux_scaled_sqrt_cap (36/25) (2*(78/5)) Numerics.Inverse.invCov0BA (by norm_num) hba.le hbasq
  · simpa only [pureFluxCovarianceBB,Rat.cast_div,Rat.cast_ofNat] using!
      pureFlux_scaled_sqrt_cap (36/25) (78/5) Numerics.Inverse.invCov0BB (by norm_num) hbb.le hbbsq
  · simpa only [pureFluxCovarianceCA,Rat.cast_div,Rat.cast_mul,Rat.cast_add,Rat.cast_pow,Rat.cast_ofNat] using!
      pureFlux_scaled_sqrt_cap (57/200) (2*((3432/5)+(78/5)^2)) Numerics.Inverse.invCov0CA (by norm_num) hca.le hcasq
  · simpa only [pureFluxCovarianceCB,Rat.cast_div,Rat.cast_add,Rat.cast_pow,Rat.cast_ofNat] using!
      pureFlux_scaled_sqrt_cap (57/200) ((3432/5)+(78/5)^2) Numerics.Inverse.invCov0CB (by norm_num) hcb.le hcbsq

end
end ASDExplicitGamma.Inverse
