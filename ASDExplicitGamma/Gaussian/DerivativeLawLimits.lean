module

public import ASDExplicitGamma.Gaussian.RealizationSeries

/-! Gaussian laws pass to genuine almost-sure limits when their variances converge. -/

@[expose] public section
namespace ASDExplicitGamma.Gaussian
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
noncomputable section

/-- Stability of centered real Gaussian laws under actual almost-sure convergence,
with a convergent sequence of covariance quadratic forms. -/
theorem map_gaussianReal_of_ae_limit {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ) (Z : Ω → ℝ) (v : ℕ → ℝ) (V : ℝ)
    (hX : ∀ n, AEMeasurable (X n) μ) (hZ : AEMeasurable Z μ)
    (hlaw : ∀ n, μ.map (X n) = gaussianReal 0 (Real.toNNReal (v n)))
    (hv : Tendsto v atTop (𝓝 V))
    (hlim : ∀ᵐ ω ∂μ, Tendsto (fun n => X n ω) atTop (𝓝 (Z ω))) :
    μ.map Z = gaussianReal 0 (Real.toNNReal V) := by
  have hvNN := tendsto_real_toNNReal hv
  have hchar (t : ℝ) : Tendsto (fun n => charFun (μ.map (X n)) t) atTop
      (𝓝 (charFun (gaussianReal 0 (Real.toNNReal V)) t)) := by
    let f : NNReal → ℂ := fun s => Complex.exp (-(s:ℂ)*(t:ℂ)^2/2)
    have hf : Continuous f := by fun_prop
    have h := hf.continuousAt.tendsto.comp hvNN
    have hs (n : ℕ) : charFun (μ.map (X n)) t = f (Real.toNNReal (v n)) := by
      rw [hlaw n, charFun_gaussianReal]
      simp only [f]
      apply congrArg Complex.exp
      norm_num
      ring_nf
    have ht : charFun (gaussianReal 0 (Real.toNNReal V)) t = f (Real.toNNReal V) := by
      rw [charFun_gaussianReal]
      simp only [f]
      apply congrArg Complex.exp
      norm_num
      ring_nf
    simpa only [hs, ht, Function.comp_def] using h
  have hg : TendstoInDistribution X atTop (fun x : ℝ => x) (fun _ : ℕ => μ)
      (gaussianReal 0 (Real.toNNReal V)) := by
    refine TendstoInDistribution.of_tendsto_charFun (P := fun _ : ℕ => μ)
      (P' := gaussianReal 0 (Real.toNNReal V)) (X' := fun x : ℝ => x) hX (by fun_prop) ?_
    intro t
    simpa only [Measure.map_id'] using hchar t
  have hz : TendstoInDistribution X atTop Z (fun _ : ℕ => μ) μ :=
    tendstoInDistribution_of_ae_tendsto hX hZ hlim
  have heq := tendstoInDistribution_unique X hg hz
  simpa only [Measure.map_id'] using heq.symm

end
end ASDExplicitGamma.Gaussian
