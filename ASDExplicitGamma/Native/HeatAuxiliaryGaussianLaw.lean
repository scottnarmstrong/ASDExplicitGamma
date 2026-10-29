module

public import ASDExplicitGamma.Native.HeatRemainderControlGaussianMoments

/-! Scalar marginals of the correlated auxiliary vector, with finiteness retained. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Nat
noncomputable section

/-- An actual Gaussian marginal has the source raw norm bound, INCLUDING
finite ENNReal norm; no infinity is lost through toReal. The other auxiliary
coordinates may be correlated arbitrarily with this coordinate. -/
theorem heat_auxiliary_gaussian_raw_norm
    {Ξ : Type*} [MeasurableSpace Ξ] (η : Measure Ξ)
    (G : Ξ → ℝ) (hG : Measurable G) (v : ℝ≥0)
    (hlaw : η.map G = gaussianReal 0 v) :
    eLpNorm G 256 η < ⊤ ∧
      eLpNorm G 256 η ≤ ENNReal.ofReal (Real.sqrt (255*(v:ℝ))) := by
  have hnorm : eLpNorm G 256 η = eLpNorm (id : ℝ → ℝ) 256 (gaussianReal 0 v) := by
    rw [←hlaw]
    symm
    simpa only [Function.id_comp] using eLpNorm_map_measure
      (by fun_prop : AEStronglyMeasurable (id : ℝ → ℝ) (η.map G)) hG.aemeasurable
  have hfinite : eLpNorm G 256 η < ⊤ := by
    rw [hnorm]
    exact memLp_id_gaussianReal' (μ := 0) (v := v) 256 (by norm_num)
  refine ⟨hfinite,?_⟩
  apply (ENNReal.toReal_le_toReal hfinite.ne ENNReal.ofReal_ne_top).mp
  rw [ENNReal.toReal_ofReal (Real.sqrt_nonneg _),hnorm]
  exact Real.le_sqrt_of_sq_le (nativeHeat_gaussian_raw_norm256_sq_le v)

/-- The exact even marginal factor gives every individual auxiliary clock.
The statement controls the ENNReal norm, with finiteness proved first. -/
theorem heat_auxiliary_gaussian_even_norm
    {Ξ : Type*} [MeasurableSpace Ξ] (η : Measure Ξ)
    (G : Ξ → ℝ) (hG : Measurable G) (v : ℝ≥0)
    (hlaw : η.map G = gaussianReal 0 v) (k : ℕ) (hk : 1 ≤ k) :
    eLpNorm G (ENNReal.ofReal (2*(k:ℝ))) η < ⊤ ∧
      eLpNorm G (ENNReal.ofReal (2*(k:ℝ))) η ≤
        ENNReal.ofReal (Real.sqrt ((v:ℝ)*Real.rpow ((2*k-1)‼:ℝ) ((k:ℝ)⁻¹))) := by
  have hnorm : eLpNorm G (ENNReal.ofReal (2*(k:ℝ))) η =
      eLpNorm (id : ℝ → ℝ) (ENNReal.ofReal (2*(k:ℝ))) (gaussianReal 0 v) := by
    rw [←hlaw]
    symm
    simpa only [Function.id_comp] using eLpNorm_map_measure
      (by fun_prop : AEStronglyMeasurable (id : ℝ → ℝ) (η.map G)) hG.aemeasurable
  have hfinite : eLpNorm G (ENNReal.ofReal (2*(k:ℝ))) η < ⊤ := by
    rw [hnorm]
    exact memLp_id_gaussianReal' (μ := 0) (v := v) _ ENNReal.ofReal_ne_top
  refine ⟨hfinite,?_⟩
  apply (ENNReal.toReal_le_toReal hfinite.ne ENNReal.ofReal_ne_top).mp
  rw [ENNReal.toReal_ofReal (Real.sqrt_nonneg _),hnorm]
  exact Real.le_sqrt_of_sq_le (nativeHeat_gaussian_even_norm_sq v k hk).le

end
end ASDExplicitGamma.Native
