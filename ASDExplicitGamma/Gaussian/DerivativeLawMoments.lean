module

public import ASDExplicitGamma.Gaussian.DerivativeLawClosure

/-! Actual moments and covariance convergence for centered Gaussian limits. -/

@[expose] public section
namespace ASDExplicitGamma.Gaussian
open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal
noncomputable section

 theorem memLp_of_map_gaussianReal {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : Ω → ℝ} (hX : AEMeasurable X μ) {m : ℝ} {v : NNReal} (hlaw : μ.map X=gaussianReal m v)
    (p : ℝ≥0∞) (hp : p ≠ ⊤) : MemLp X p μ := by
  have h : MemLp id p (μ.map X) := by rw [hlaw]; exact memLp_id_gaussianReal' p hp
  simpa only [Function.comp_def, id_eq] using h.comp_of_map hX

 theorem integral_of_map_gaussianReal {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : Ω → ℝ} (hX : AEMeasurable X μ) {m : ℝ} {v : NNReal} (hlaw : μ.map X=gaussianReal m v) :
    (∫ ω, X ω ∂μ)=m := by
  have h := integral_id_gaussianReal (μ := m) (v := v)
  rw [← hlaw, integral_map hX (by fun_prop)] at h
  exact h

 theorem integral_sq_of_map_gaussianReal_zero {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : Ω → ℝ} (hX : AEMeasurable X μ) {v : NNReal} (hlaw : μ.map X=gaussianReal 0 v) :
    (∫ ω, (X ω)^2 ∂μ)=(v:ℝ) := by
  have hm := integral_of_map_gaussianReal hX hlaw
  have h := variance_id_gaussianReal (μ := 0) (v := v)
  rw [← hlaw, variance_id_map hX, variance_eq_integral hX, hm] at h
  simpa only [sub_zero] using h

/-- Along an almost-sure centered Gaussian limit, actual second moments converge. -/
theorem tendsto_integral_sq_gaussian_of_ae_limit {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ) (Z : Ω → ℝ) (v : ℕ → NNReal)
    (hX : ∀ n, AEMeasurable (X n) μ) (hZ : AEMeasurable Z μ)
    (hlaw : ∀ n, μ.map (X n)=gaussianReal 0 (v n))
    (hlim : ∀ᵐ ω ∂μ, Tendsto (fun n => X n ω) atTop (𝓝 (Z ω))) :
    Tendsto (fun n => ∫ ω, (X n ω)^2 ∂μ) atTop (𝓝 (∫ ω, (Z ω)^2 ∂μ)) := by
  obtain ⟨V,hV,hZlaw,hv⟩ := exists_gaussianReal_map_of_ae_limit μ X Z v hX hZ hlaw hlim
  have hmom := integral_sq_of_map_gaussianReal_zero hZ hZlaw
  rw [Real.coe_toNNReal V hV] at hmom
  simpa only [integral_sq_of_map_gaussianReal_zero (hX _) (hlaw _), hmom] using hv

/-- Polarization of actual integrals, requiring only true L2 membership. -/
theorem integral_product_eq_polarization {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {X Y : Ω → ℝ} (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    (∫ ω, X ω*Y ω ∂μ) = ((∫ ω, (X ω+Y ω)^2 ∂μ)-(∫ ω, (X ω)^2 ∂μ)-(∫ ω, (Y ω)^2 ∂μ))/2 := by
  have hiX : Integrable (fun ω => (X ω)^2) μ := by simpa only [Real.norm_eq_abs, sq_abs] using hX.integrable_norm_pow (by norm_num : 2 ≠ 0)
  have hiY : Integrable (fun ω => (Y ω)^2) μ := by simpa only [Real.norm_eq_abs, sq_abs] using hY.integrable_norm_pow (by norm_num : 2 ≠ 0)
  have hiXY : Integrable (fun ω => X ω*Y ω) μ := hX.integrable_mul hY
  have heq : (∫ ω, (X ω+Y ω)^2 ∂μ) = (∫ ω, (X ω)^2 ∂μ)+2*(∫ ω, X ω*Y ω ∂μ)+(∫ ω, (Y ω)^2 ∂μ) := by
    have hp : (fun ω => (X ω+Y ω)^2) = fun ω => (X ω)^2+2*(X ω*Y ω)+(Y ω)^2 := by funext ω; ring
    rw [hp, integral_add (f := fun ω => (X ω)^2+2*(X ω*Y ω)) (g := fun ω => (Y ω)^2) (hiX.add (hiXY.const_mul 2)) hiY,
      integral_add (f := fun ω => (X ω)^2) (g := fun ω => 2*(X ω*Y ω)) hiX (hiXY.const_mul 2), integral_const_mul]
  linarith only [heq]

end
end ASDExplicitGamma.Gaussian
