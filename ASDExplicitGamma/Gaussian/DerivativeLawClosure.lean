module

public import ASDExplicitGamma.Gaussian.DerivativeLawLimits
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion

/-! Closedness of centered Gaussian laws, with derived variance convergence. -/

@[expose] public section
namespace ASDExplicitGamma.Gaussian
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
noncomputable section

/-- Almost-sure limits of centered Gaussian variables are centered Gaussian.
Variance convergence is derived from characteristic functions, rather than assumed. -/
theorem exists_gaussianReal_map_of_ae_limit {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ) (Z : Ω → ℝ) (v : ℕ → NNReal)
    (hX : ∀ n, AEMeasurable (X n) μ) (hZ : AEMeasurable Z μ)
    (hlaw : ∀ n, μ.map (X n) = gaussianReal 0 (v n))
    (hlim : ∀ᵐ ω ∂μ, Tendsto (fun n => X n ω) atTop (𝓝 (Z ω))) :
    ∃ V : ℝ, 0 ≤ V ∧ μ.map Z = gaussianReal 0 (Real.toNNReal V) ∧
      Tendsto (fun n => (v n:ℝ)) atTop (𝓝 V) := by
  let instMapZProbability : IsProbabilityMeasure (μ.map Z) := inferInstance
  let g : ℝ → ℝ := fun t => (charFun (μ.map Z) t).re
  have hgcont : Continuous g := Complex.continuous_re.comp continuous_charFun
  have hg0 : g 0 = 1 := by simp [g, charFun_zero]
  have hseq : Tendsto (fun n : ℕ => g (1/((n:ℝ)+1))) atTop (𝓝 (1:ℝ)) := by
    have h : Tendsto (fun n : ℕ => g (1/((n:ℝ)+1))) atTop (𝓝 (g 0)) :=
      hgcont.continuousAt.tendsto.comp tendsto_one_div_add_atTop_nhds_zero_nat
    simpa only [hg0] using h
  have hevent : ∀ᶠ n : ℕ in atTop, 0 < g (1/((n:ℝ)+1)) := hseq.eventually (lt_mem_nhds (by norm_num : (0:ℝ)<1))
  obtain ⟨N, hN⟩ := hevent.exists
  let t : ℝ := 1/((N:ℝ)+1)
  have ht : t ≠ 0 := by dsimp [t]; positivity
  have hgt : 0 < g t := hN
  have hdist := tendstoInDistribution_of_ae_tendsto hX hZ hlim
  have hchar := Complex.continuous_re.continuousAt.tendsto.comp (hdist.tendsto_charFun t)
  have hreal (n : ℕ) : (charFun (μ.map (X n)) t).re = Real.exp (-(v n:ℝ)*t^2/2) := by
    rw [hlaw n, charFun_gaussianReal]
    have he : (t:ℂ)*0*Complex.I-(v n:ℂ)*(t:ℂ)^2/2 = (((-(v n:ℝ)*t^2/2):ℝ):ℂ) := by
      push_cast
      ring
    simp only [Complex.ofReal_zero]
    rw [he, ← Complex.ofReal_exp, Complex.ofReal_re]
  have hlog : Tendsto (fun n => Real.log ((charFun (μ.map (X n)) t).re)) atTop (𝓝 (Real.log (g t))) :=
    (Real.continuousAt_log hgt.ne').tendsto.comp hchar
  simp only [hreal, Real.log_exp] at hlog
  let V := (-2/t^2)*Real.log (g t)
  have hv : Tendsto (fun n => (v n:ℝ)) atTop (𝓝 V) := by
    have h := hlog.const_mul (-2/t^2)
    convert h using 1
    funext n
    field_simp
  have hV : 0 ≤ V := ge_of_tendsto hv (Filter.Eventually.of_forall fun n => (v n).coe_nonneg)
  refine ⟨V, hV, ?_, hv⟩
  apply map_gaussianReal_of_ae_limit μ X Z (fun n => (v n:ℝ)) V hX hZ ?_ hv hlim
  intro n
  simpa only [Real.toNNReal_coe] using hlaw n

end
end ASDExplicitGamma.Gaussian
