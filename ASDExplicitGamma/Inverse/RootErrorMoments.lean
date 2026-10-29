module

public import ASDExplicitGamma.Inverse.RootErrorParts

/-! Both moment bounds for the same literal positive root error, before
finite-energy hybrid comparison and without subtraction of response norms. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Model
open scoped ENNReal
noncomputable section

/-- The actual positive E_l has both source moment alternatives. Its
construction and norm bounds precede every response comparison. -/
theorem positive_root_error_Lp (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (Q : TriadicCube 2) (r : RootRow)
    (hpast : ∀ k ≤ Q.scale-(rootH0 r:ℤ)+40, nativeInductionState M h k)
    (p : ℝ) (hp : 2 ≤ p) (hp256 : p ≤ 256) :
    eLpNorm (positiveRootError M Q r) (ENNReal.ofReal p) (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal (rootMatrixErrorBudget M.gamma p r+rootDensityErrorBudget M.gamma r) ∧
    eLpNorm (positiveRootError M Q r) (ENNReal.ofReal p) (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal (rootMatrixErrorBudget M.gamma p r+rootDensityRetainedBudget M.gamma p r) := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let F := fun ω => ∑' hk, rootMatrixTerm M Q r hk ω
  let D := fun ω => ∑' hk, rootDensityTerm M Q r hk ω
  have hmat := root_matrix_series_Lp M h hM hg Q r p (by linarith only [hp])
  have hden := root_density_series_Lp M h hM hg Q r hpast p hp hp256
  have heq : positiveRootError M Q r =ᵐ[μ] ENNReal.ofReal ∘ (fun ω => F ω+D ω) := by
    filter_upwards [hmat.1,hden.1] with ω hm hd
    exact positive_root_error_eq_parts M Q r ω (Summable.of_norm hm) (Summable.of_norm hd)
  have hnonneg (ω : Cutoff.CutoffSample 2) : 0 ≤ F ω+D ω :=
    add_nonneg (tsum_nonneg (fun hk => root_matrix_term_nonneg M Q r hk ω))
      (tsum_nonneg (fun hk => root_density_term_nonneg M Q r hk ω))
  have he : eLpNorm (positiveRootError M Q r) (ENNReal.ofReal p) μ =
      eLpNorm (fun ω => F ω+D ω) (ENNReal.ofReal p) μ :=
    (eLpNorm_congr_ae heq).trans (eLpNorm_ofReal _ (Filter.Eventually.of_forall hnonneg))
  have htri : eLpNorm (fun ω => F ω+D ω) (ENNReal.ofReal p) μ ≤
      eLpNorm F (ENNReal.ofReal p) μ+eLpNorm D (ENNReal.ofReal p) μ :=
    eLpNorm_add_le (ENNReal.one_le_ofReal.mpr (by linarith only [hp]))
  have ht : 0 ≤ rootTau r := by cases r <;> norm_num [rootTau]
  have hcoef : 0 ≤ rootEdelta r*rootResponseEnvelope (6*rootTau r) := by
    unfold rootEdelta rootResponseEnvelope
    positivity
  have hS : 0 ≤ planarGradientCharge 40 := by unfold planarGradientCharge; positivity
  have hM0 : 0 ≤ rootMatrixErrorBudget M.gamma p r := by
    unfold rootMatrixErrorBudget rootEdelta rootResponseEnvelope
    positivity
  have hZ0 : 0 ≤ rootDensityErrorBudget M.gamma r := by
    apply mul_nonneg hcoef
    rw [← (reset_density_EZ_hasSum M.gamma (planarGradientCharge 40) hg (rootH0 r-38)).tsum_eq]
    apply tsum_nonneg
    intro hk
    unfold resetDensityEZBudget
    positivity
  have hD0 : 0 ≤ rootDensityRetainedBudget M.gamma p r := by
    apply mul_nonneg hcoef
    rw [← (reset_density_budget2_hasSum (rootQ r) p (rootMomentCutoff r) M.gamma
      (planarGradientCharge 40) hg (rootH0 r-38)).tsum_eq]
    exact tsum_nonneg (fun hk => reset_density_budget2_nonneg _ _ _ _ _ (by linarith only [hp]) hS _ hk)
  constructor
  · rw [he]
    apply htri.trans
    apply (add_le_add hmat.2 hden.2.1).trans_eq
    exact (ENNReal.ofReal_add hM0 hZ0).symm
  · rw [he]
    apply htri.trans
    apply (add_le_add hmat.2 hden.2.2).trans_eq
    exact (ENNReal.ofReal_add hM0 hD0).symm

end
end ASDExplicitGamma.Inverse
