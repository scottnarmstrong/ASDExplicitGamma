module

public import ASDExplicitGamma.Gaussian.IntegralSmooth

/-! # Preservation of the C² response class under auxiliary Gaussian averaging -/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology

namespace ASDExplicitGamma.Gaussian

/-- The directional bounds in the response interface control the full bounded Hessian. -/
theorem polynomial_c2_jet_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} (hf : HasPolynomiallyBoundedC2Derivatives f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ d : ℕ, ∀ x,
      |f x| + ‖fderiv ℝ f x‖ + ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ C * (1 + ‖x‖) ^ d := by
  obtain ⟨hf2, C, hC, d, hv, hd, hh⟩ := hf
  have hB (x : E) : ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ C * (1 + ‖x‖) ^ d := by
    refine (fderiv ℝ (fderiv ℝ f) x).opNorm_le_bound (by positivity) ?_
    intro u
    refine ((fderiv ℝ (fderiv ℝ f) x) u).opNorm_le_bound (by positivity) ?_
    intro w
    rw [Real.norm_eq_abs, ← second_fderiv_eq hf2]
    exact hh x u w
  refine ⟨3 * C, by positivity, d, fun x => ?_⟩
  have h := hv x
  have h' := hd x
  have h'' := hB x
  nlinarith

/-- Independently averaging a translated response preserves C² regularity. The two derivative
formulas are proved by differentiation under the integral, not assumed. -/
theorem c2_integral_translate {E Ω : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace Ω] (μ : Measure Ω) (Z : Ω → E) (hZ : StronglyMeasurable Z)
    (hMom : ∀ d : ℕ, Integrable (fun ω => (1 + ‖Z ω‖) ^ d) μ)
    {f : E → ℝ} (hf : HasPolynomiallyBoundedC2Derivatives f) :
    ContDiff ℝ 2 (fun x => ∫ ω, f (x + Z ω) ∂μ) ∧
    (∀ x, fderiv ℝ (fun y => ∫ ω, f (y + Z ω) ∂μ) x =
      ∫ ω, fderiv ℝ f (x + Z ω) ∂μ) ∧
    (∀ x, fderiv ℝ (fderiv ℝ (fun y => ∫ ω, f (y + Z ω) ∂μ)) x =
      ∫ ω, fderiv ℝ (fderiv ℝ f) (x + Z ω) ∂μ) := by
  obtain ⟨C, hC, d, hb⟩ := polynomial_c2_jet_bound hf
  have hsum (x : E) : ‖f x‖ + ‖fderiv ℝ f x‖ ≤ C * (1 + ‖x‖) ^ d := by
    have h := hb x
    rw [Real.norm_eq_abs]
    linarith [norm_nonneg (fderiv ℝ (fderiv ℝ f) x)]
  have hdfsum (x : E) : ‖fderiv ℝ f x‖ + ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ C * (1 + ‖x‖) ^ d := by
    have h := hb x
    linarith [abs_nonneg (f x)]
  have hdf := hf.1.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)
  have hD (x : E) := hasFDerivAt_integral_translate μ Z hZ hMom
    (hf.1.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)) ⟨C, hC, d, hsum⟩ x
  have hDD (x : E) := hasFDerivAt_integral_translate μ Z hZ hMom hdf ⟨C, hC, d, hdfsum⟩ x
  have hDDeq : fderiv ℝ (fun x => ∫ ω, fderiv ℝ f (x + Z ω) ∂μ) =
      fun x => ∫ ω, fderiv ℝ (fderiv ℝ f) (x + Z ω) ∂μ := funext fun x => (hDD x).fderiv
  have hDDcont : Continuous (fun x => ∫ ω, fderiv ℝ (fderiv ℝ f) (x + Z ω) ∂μ) := by
    apply continuous_integral_translate μ Z hZ hMom (hdf.continuous_fderiv (by norm_num))
    refine ⟨C, hC, d, fun x => ?_⟩
    have h := hb x
    linarith [abs_nonneg (f x), norm_nonneg (fderiv ℝ f x)]
  have hdfC1 : ContDiff ℝ 1 (fun x => ∫ ω, fderiv ℝ f (x + Z ω) ∂μ) := by
    apply contDiff_one_iff_fderiv.mpr
    refine ⟨fun x => (hDD x).differentiableAt, ?_⟩
    rw [hDDeq]
    exact hDDcont
  have hDeq : fderiv ℝ (fun x => ∫ ω, f (x + Z ω) ∂μ) =
      fun x => ∫ ω, fderiv ℝ f (x + Z ω) ∂μ := funext fun x => (hD x).fderiv
  refine ⟨?_, fun x => (hD x).fderiv, ?_⟩
  · have hn : (2 : WithTop ℕ∞) = 1 + 1 := by norm_num
    rw [hn, contDiff_succ_iff_fderiv]
    refine ⟨fun x => (hD x).differentiableAt, by simp, ?_⟩
    rw [hDeq]
    exact hdfC1
  · intro x
    rw [hDeq]
    exact (hDD x).fderiv

end ASDExplicitGamma.Gaussian
