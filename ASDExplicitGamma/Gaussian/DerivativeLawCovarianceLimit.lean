module

public import ASDExplicitGamma.Gaussian.DerivativeLawFamilies

/-! Actual covariance convergence for finite Gaussian families under almost-sure limits. -/

@[expose] public section
namespace ASDExplicitGamma.Gaussian
open MeasureTheory ProbabilityTheory Filter
open scoped Topology BigOperators ENNReal
noncomputable section

 theorem IsCenteredGaussianFamily.memLp {Ω I : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : I → Ω → ℝ} (hX : IsCenteredGaussianFamily μ X) (i : I) (p : ℝ≥0∞) (hp : p ≠ ⊤) : MemLp (X i) p μ := by
  obtain ⟨v,hv⟩ := hX.map_single i
  exact memLp_of_map_gaussianReal (hX.1 i) hv p hp

/-- Joint centered Gaussian limits carry their actual covariance limits. -/
theorem tendsto_integral_product_gaussian_of_ae_limit {Ω I : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : ℕ → I → Ω → ℝ) (Z : I → Ω → ℝ)
    (hX : ∀ n, IsCenteredGaussianFamily μ (X n)) (hZ : ∀ i, AEMeasurable (Z i) μ)
    (hlim : ∀ i, ∀ᵐ ω ∂μ, Tendsto (fun n => X n i ω) atTop (𝓝 (Z i ω))) (i j : I) :
    Tendsto (fun n => ∫ ω, X n i ω*X n j ω ∂μ) atTop (𝓝 (∫ ω, Z i ω*Z j ω ∂μ)) := by
  classical
  have hZg := isCenteredGaussianFamily_ae_limit μ X Z hX hZ hlim
  have hXi (n : ℕ) := (hX n).map_single i
  have hXj (n : ℕ) := (hX n).map_single j
  choose vi hvi using hXi
  choose vj hvj using hXj
  have hsumlaw (n : ℕ) : ∃ v : NNReal, μ.map (fun ω => X n i ω+X n j ω)=gaussianReal 0 v := by
    obtain ⟨v,hv⟩ := (hX n).2 ![i,j] (fun _ => 1)
    exact ⟨v, by simpa only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, one_mul] using hv⟩
  choose vs hvs using hsumlaw
  have hi := tendsto_integral_sq_gaussian_of_ae_limit μ (fun n => X n i) (Z i) vi
    (fun n => (hX n).1 i) (hZ i) hvi (hlim i)
  have hj := tendsto_integral_sq_gaussian_of_ae_limit μ (fun n => X n j) (Z j) vj
    (fun n => (hX n).1 j) (hZ j) hvj (hlim j)
  have hsumlim : ∀ᵐ ω ∂μ, Tendsto (fun n => X n i ω+X n j ω) atTop (𝓝 (Z i ω+Z j ω)) := by
    filter_upwards [hlim i, hlim j] with ω hi hj
    exact hi.add hj
  have hs := tendsto_integral_sq_gaussian_of_ae_limit μ (fun n ω => X n i ω+X n j ω)
    (fun ω => Z i ω+Z j ω) vs (fun n => ((hX n).1 i).add ((hX n).1 j))
    ((hZ i).add (hZ j)) hvs hsumlim
  have hp (n : ℕ) := integral_product_eq_polarization μ ((hX n).memLp i 2 (by simp)) ((hX n).memLp j 2 (by simp))
  have hq := integral_product_eq_polarization μ (hZg.memLp i 2 (by simp)) (hZg.memLp j 2 (by simp))
  simpa only [← hp, ← hq] using ((hs.sub hi).sub hj).div_const 2

end
end ASDExplicitGamma.Gaussian
