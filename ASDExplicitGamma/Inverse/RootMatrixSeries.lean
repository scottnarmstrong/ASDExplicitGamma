module

public import ASDExplicitGamma.Inverse.RootMatrixBudget
public import ASDExplicitGamma.Inverse.StoppedSeriesLp

/-! Complete positive actual matrix-error series before response comparison. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Model
open scoped ENNReal
noncomputable section

/-- Literal positive matrix error summand of the source. -/
def rootMatrixTerm (M : ABKModel 2) (Q : TriadicCube 2) (r : RootRow)
    (hk : ℕ × ℕ) (ω : Cutoff.CutoffSample 2) : ℝ :=
  rootEdelta r*(3:ℝ)^(2*M.gamma*(localizationResetAbscissa (rootH0 r-38) hk.1 hk.2:ℝ))*
    rootMatrixPositiveError M Q r hk ω

/-- Exact source norm envelope, retaining sqrt(v_k). -/
def rootMatrixNormTerm (γ p : ℝ) (r : RootRow) (hk : ℕ × ℕ) : ℝ :=
  (rootEdelta r*256*Real.sqrt p*rootResponseEnvelope (rootTau r))*
    (Real.sqrt (bankLayerWeight hk.2)*(3:ℝ)^(2*γ*(localizationResetAbscissa (rootH0 r-38) hk.1 hk.2:ℝ))*
      (3:ℝ)^(-((localizationResetAbscissa (rootH0 r-38) hk.1 hk.2:ℝ)+1)))

/-- The retained complete source matrix budget is summable; the bound v_k<=1
is used only to prove convergence, leaving the norm budget's exact series. -/
theorem root_matrix_norm_term_hasSum (γ p : ℝ) (hg : γ ≤ gammaZero) (r : RootRow) :
    HasSum (rootMatrixNormTerm γ p r) (rootMatrixErrorBudget γ p r) := by
  let C := rootH0 r-38
  let f := fun hk : ℕ × ℕ => Real.sqrt (bankLayerWeight hk.2)*
    (3:ℝ)^(2*γ*(localizationResetAbscissa C hk.1 hk.2:ℝ))*
      (3:ℝ)^(-((localizationResetAbscissa C hk.1 hk.2:ℝ)+1))
  have hg' : γ ≤ 17/50000 := hg
  have hs := (density_reset_power_hasSum (2*γ) 1 (by linarith only [hg']) C).summable
  have hv (n : ℕ) : Real.sqrt (bankLayerWeight n) ≤ 1 := by
    have hv' : bankLayerWeight n ≤ 1 := by
      simpa only [layerWeight_hasSum.tsum_eq] using
        layerWeight_hasSum.summable.le_tsum n (fun _ _ => bankLayerWeight_nonneg _)
    exact (Real.sqrt_le_one).mpr hv'
  have hf : Summable f := hs.of_nonneg_of_le (fun hk => by dsimp only [f]; positivity) (fun hk => by
    have h0 : 0 ≤ (3:ℝ)^(2*γ*(localizationResetAbscissa C hk.1 hk.2:ℝ))*
      (3:ℝ)^(-((localizationResetAbscissa C hk.1 hk.2:ℝ)+1)) := by positivity
    have hh := mul_le_mul_of_nonneg_right (hv hk.2) h0
    simpa only [f,mul_assoc,one_mul,neg_mul] using hh)
  exact hf.hasSum.mul_left (rootEdelta r*256*Real.sqrt p*rootResponseEnvelope (rootTau r))

theorem root_matrix_term_nonneg (M : ABKModel 2) (Q : TriadicCube 2) (r : RootRow)
    (hk : ℕ × ℕ) (ω : Cutoff.CutoffSample 2) : 0 ≤ rootMatrixTerm M Q r hk ω := by
  apply mul_nonneg
  · unfold rootEdelta
    positivity
  · exact le_max_left 0 _

/-- Every deterministic actual matrix summand has its source norm bound. -/
theorem root_matrix_term_Lp (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (Q : TriadicCube 2) (r : RootRow) (hk : ℕ × ℕ) (p : ℝ) (hp : 1 ≤ p) :
    Measurable (rootMatrixTerm M Q r hk) ∧
      eLpNorm (rootMatrixTerm M Q r hk) (ENNReal.ofReal p) (Cutoff.cutoffSampleLaw M).toMeasure ≤
        ENNReal.ofReal (rootMatrixNormTerm M.gamma p r hk) := by
  have hm := (root_matrix_positive_error_measurable M Q r hk).const_mul
    (rootEdelta r*(3:ℝ)^(2*M.gamma*(localizationResetAbscissa (rootH0 r-38) hk.1 hk.2:ℝ)))
  refine ⟨hm,?_⟩
  let a := rootEdelta r*(3:ℝ)^(2*M.gamma*(localizationResetAbscissa (rootH0 r-38) hk.1 hk.2:ℝ))
  have ha : 0 ≤ a := by dsimp only [a,rootEdelta]; positivity
  have he : rootMatrixTerm M Q r hk=a • rootMatrixPositiveError M Q r hk := by funext ω; rfl
  rw [he,eLpNorm_const_smul,Real.enorm_eq_ofReal ha]
  apply (mul_le_mul_of_nonneg_left (root_matrix_positive_error_Lp M h hM Q r hk p hp)
    (zero_le : (0:ℝ≥0∞) ≤ _)).trans_eq
  rw [← ENNReal.ofReal_mul ha]
  congr 1
  dsimp only [a,rootMatrixNormTerm]
  ring

/-- Complete positive matrix-error series converges absolutely almost
surely and obeys the exact displayed e_M,p, before any root response bound. -/
theorem root_matrix_series_Lp (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (Q : TriadicCube 2) (r : RootRow) (p : ℝ) (hp : 1 ≤ p) :
    let μ := (Cutoff.cutoffSampleLaw M).toMeasure
    let F := rootMatrixTerm M Q r
    (∀ᵐ ω ∂μ, Summable (fun hk => ‖F hk ω‖)) ∧
      eLpNorm (fun ω => ∑' hk, F hk ω) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal (rootMatrixErrorBudget M.gamma p r) := by
  have ht : 0 ≤ rootTau r := by cases r <;> norm_num [rootTau]
  have hG : 0 ≤ rootResponseEnvelope (rootTau r) := by unfold rootResponseEnvelope; positivity
  exact countable_density_series_Lp (Cutoff.cutoffSampleLaw M).toMeasure (ENNReal.ofReal p)
    (ENNReal.one_le_ofReal.mpr hp) (rootMatrixTerm M Q r)
    (fun hk => (root_matrix_term_Lp M h hM Q r hk p hp).1)
    (rootMatrixNormTerm M.gamma p r)
    (fun hk => by unfold rootMatrixNormTerm rootEdelta; positivity)
    _ (root_matrix_norm_term_hasSum M.gamma p hg r)
    (fun hk => (root_matrix_term_Lp M h hM Q r hk p hp).2)

end
end ASDExplicitGamma.Inverse
