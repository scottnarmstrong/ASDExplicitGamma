module

public import ASDExplicitGamma.Model.SpectralTranslation
public import ASDExplicitGamma.Model.SpectralDerivative

@[expose] public section

open MeasureTheory Homogenization Complex

namespace ASDExplicitGamma.Model

private theorem hasDerivAt_isometry_iff
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (U : E →ₗᵢ[ℝ] F) (f : ℝ → E) (g : E) :
    HasDerivAt (fun t => U (f t)) (U g) 0 ↔ HasDerivAt f g 0 := by
  have heq (t : ℝ) : ‖slope (fun t => U (f t)) 0 t - U g‖ =
      ‖slope f 0 t - g‖ := by
    simp only [slope_def_module, sub_zero]
    rw [← U.map_sub, ← U.map_smul, ← U.map_sub, U.norm_map]
  constructor
  · intro hd
    apply hasDerivAt_iff_tendsto_slope.mpr
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    have hn := tendsto_iff_norm_sub_tendsto_zero.mp hd.tendsto_slope
    simpa only [heq] using hn
  · intro hd
    apply hasDerivAt_iff_tendsto_slope.mpr
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    have hn := tendsto_iff_norm_sub_tendsto_zero.mp hd.tendsto_slope
    simpa only [heq] using hn

private theorem q3SpectralPhase_basis (i : Fin 2) (t : ℝ) (ξ : Q3FrequencyPlane) :
    q3SpectralPhase (t • (Pi.single i 1 : Vec 2)) ξ =
      exp (((t * (2 * Real.pi * q3FrequencyCoordinate i ξ) : ℝ) : ℂ) * I) := by
  fin_cases i
  all_goals
    simp only [q3SpectralPhase, q3FrequencyCoordinate, Pi.smul_apply, smul_eq_mul,
      Pi.single_apply]
    norm_num
    congr 1
    ring

/-- On the complexified first chaos, Superdiffusion's strong coordinate
horizontal derivative is exactly multiplication by `2π i ξ_j`. The definition
uses the derivative at zero of `t ↦ τ_(t e_j) φ`, exactly as in
`Algsuperdiff.Probability.Stationary.HasHorizontalGradient`. -/
theorem q3SpectralInverse_horizontal_derivative_iff
    (M : Algsuperdiff.Section3.ABKModel 2) (h : ℝ)
    (hM : ASDExplicitGamma.PlanarQ3Gaussian M h) (i : Fin 2)
    (f g : Lp ℂ 2 (q3SpectralMeasure h)) :
    HasDerivAt
      (fun t : ℝ => q3ComplexKoopman M (t • (Pi.single i 1 : Vec 2))
        (q3SpectralInverse M h hM f))
      (q3SpectralInverse M h hM g) 0 ↔
      (g : Q3FrequencyPlane → ℂ) =ᵐ[q3SpectralMeasure h]
        fun ξ => (((2 * Real.pi * q3FrequencyCoordinate i ξ : ℝ) : ℂ) * I) * f ξ := by
  have hfun :
      (fun t : ℝ => q3ComplexKoopman M (t • (Pi.single i 1 : Vec 2))
        (q3SpectralInverse M h hM f)) =
      (fun t : ℝ => q3SpectralInverse M h hM
        (q3SpectralTranslation h (t • (Pi.single i 1 : Vec 2)) f)) := by
    funext t
    exact q3SpectralInverse_intertwine M h hM _ f
  rw [hfun]
  let U : Lp ℂ 2 (q3SpectralMeasure h) →ₗᵢ[ℝ] Lp ℂ 2 (planarRegLaw M) :=
    { toLinearMap := (q3SpectralInverse M h hM).toLinearMap.restrictScalars ℝ
      norm_map' := (q3SpectralInverse M h hM).norm_map }
  change HasDerivAt (fun t : ℝ => U
    (q3SpectralTranslation h (t • (Pi.single i 1 : Vec 2)) f)) (U g) 0 ↔ _
  rw [hasDerivAt_isometry_iff U]
  apply hasDerivAt_spectral_iff
  · exact (q3FrequencyCoordinate_continuous i).measurable.const_mul _
  · intro t
    have hc := q3SpectralTranslation_coeFn h (t • (Pi.single i 1 : Vec 2)) f
    simpa only [q3SpectralPhase_basis] using hc

theorem q3ComplexKoopman_firstChaos_stable
    (M : Algsuperdiff.Section3.ABKModel 2) (h : ℝ)
    (hM : ASDExplicitGamma.PlanarQ3Gaussian M h) (z : Vec 2)
    (φ : Lp ℂ 2 (planarRegLaw M)) (hφ : φ ∈ q3ComplexFirstChaos M) :
    q3ComplexKoopman M z φ ∈ q3ComplexFirstChaos M := by
  rw [← q3SpectralInverse_range M h hM] at hφ ⊢
  obtain ⟨f, rfl⟩ := hφ
  exact ⟨q3SpectralTranslation h z f, (q3SpectralInverse_intertwine M h hM z f).symm⟩

/-- A strong derivative of a first-chaos orbit remains in the first chaos. -/
theorem q3ComplexHorizontalDerivative_mem
    (M : Algsuperdiff.Section3.ABKModel 2) (h : ℝ)
    (hM : ASDExplicitGamma.PlanarQ3Gaussian M h) (i : Fin 2)
    (φ G : Lp ℂ 2 (planarRegLaw M)) (hφ : φ ∈ q3ComplexFirstChaos M)
    (hd : HasDerivAt
      (fun t : ℝ => q3ComplexKoopman M (t • (Pi.single i 1 : Vec 2)) φ) G 0) :
    G ∈ q3ComplexFirstChaos M := by
  have hclosed : IsClosed (q3ComplexFirstChaos M : Set (Lp ℂ 2 (planarRegLaw M))) :=
    Submodule.isClosed_topologicalClosure _
  apply hclosed.mem_of_tendsto hd.tendsto_slope
  apply Filter.Eventually.of_forall
  intro t
  rw [slope_def_module]
  apply (q3ComplexFirstChaos M).smul_mem
  exact (q3ComplexFirstChaos M).sub_mem
    (q3ComplexKoopman_firstChaos_stable M h hM _ φ hφ)
    (q3ComplexKoopman_firstChaos_stable M h hM _ φ hφ)

end ASDExplicitGamma.Model
