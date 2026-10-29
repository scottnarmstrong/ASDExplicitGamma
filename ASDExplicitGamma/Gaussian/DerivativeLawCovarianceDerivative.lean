module

public import ASDExplicitGamma.Gaussian.DerivativeLawCovarianceLimit
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Order.Filter.AtTopBot.CountablyGenerated

/-! Differentiation of actual Gaussian covariances, from pathwise derivatives. -/

@[expose] public section
namespace ASDExplicitGamma.Gaussian
open MeasureTheory ProbabilityTheory Filter
open scoped Topology BigOperators
noncomputable section

/-- Pathwise differentiation of a jointly Gaussian family differentiates its covariance.
No covariance differentiability or interchange-of-integral premise is assumed. -/
theorem hasDerivAt_integral_product_of_gaussian {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : ℝ → Ω → ℝ) (Y D : Ω → ℝ) (x : ℝ)
    (hg : IsCenteredGaussianFamily μ (Sum.elim (fun _ : Unit => Y) X))
    (hD : AEMeasurable D μ)
    (hpath : ∀ᵐ ω ∂μ, HasDerivAt (fun t => X t ω) (D ω) x) :
    HasDerivAt (fun t => ∫ ω, X t ω*Y ω ∂μ) (∫ ω, D ω*Y ω ∂μ) x := by
  classical
  apply hasDerivAt_iff_tendsto_slope_zero.2
  apply Filter.tendsto_iff_seq_tendsto.2
  intro ε hε
  let Xn : ℕ → Fin 2 → Ω → ℝ := fun n i ω => if i=0 then
    (ε n)⁻¹*(X (x+ε n) ω-X x ω) else Y ω
  let Z : Fin 2 → Ω → ℝ := fun i => if i=0 then D else Y
  let point : ℕ → Fin 2 → Fin 2 → Sum Unit ℝ := fun n i a => if i=0 then
    .inr (if a=0 then x else x+ε n) else .inl ()
  let coeff : ℕ → Fin 2 → Fin 2 → ℝ := fun n i a => if i=0 then
    (if a=0 then -(ε n)⁻¹ else (ε n)⁻¹) else if a=0 then 1 else 0
  have hXn (n : ℕ) : IsCenteredGaussianFamily μ (Xn n) := by
    have h := hg.finite_linear_image (point n) (coeff n)
    have heq : (fun i ω => ∑ a : Fin 2, coeff n i a*(Sum.elim (fun _ : Unit => Y) X (point n i a)) ω) = Xn n := by
      funext i ω
      fin_cases i
      all_goals simp [Xn, point, coeff, Fin.sum_univ_two] <;> ring
    rw [← heq]
    exact h
  have hZ (i : Fin 2) : AEMeasurable (Z i) μ := by
    fin_cases i
    · exact hD
    · exact hg.1 (.inl ())
  have hlim (i : Fin 2) : ∀ᵐ ω ∂μ, Tendsto (fun n => Xn n i ω) atTop (𝓝 (Z i ω)) := by
    fin_cases i
    · filter_upwards [hpath] with ω hω
      change Tendsto (fun n => (ε n)⁻¹*(X (x+ε n) ω-X x ω)) atTop (𝓝 (D ω))
      simpa only [Function.comp_def, smul_eq_mul] using hω.tendsto_slope_zero.comp hε
    · exact Filter.Eventually.of_forall fun _ => tendsto_const_nhds
  have hcov := tendsto_integral_product_gaussian_of_ae_limit μ Xn Z hXn hZ hlim 0 1
  have hL2 (t : ℝ) : MemLp (X t) 2 μ := hg.memLp (.inr t) 2 (by simp)
  have hYL2 : MemLp Y 2 μ := hg.memLp (.inl ()) 2 (by simp)
  have heq (h : ℝ) : (∫ ω, h⁻¹*(X (x+h) ω-X x ω)*Y ω ∂μ) =
      h⁻¹*((∫ ω, X (x+h) ω*Y ω ∂μ)-(∫ ω, X x ω*Y ω ∂μ)) := by
    have hp : (fun ω => h⁻¹*(X (x+h) ω-X x ω)*Y ω) = fun ω => h⁻¹*(X (x+h) ω*Y ω-X x ω*Y ω) := by funext ω; ring
    rw [hp, integral_const_mul, integral_sub (f := fun ω => X (x+h) ω*Y ω) (g := fun ω => X x ω*Y ω) ((hL2 (x+h)).integrable_mul hYL2) ((hL2 x).integrable_mul hYL2)]
  simpa only [Function.comp_def, Xn, Z, ite_true, show (1:Fin 2)≠0 by decide, ite_false,
    smul_eq_mul, heq] using hcov

end
end ASDExplicitGamma.Gaussian
