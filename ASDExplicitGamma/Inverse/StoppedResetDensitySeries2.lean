module

public import ASDExplicitGamma.Inverse.StoppedResetDensityBudgets
public import ASDExplicitGamma.Inverse.StoppedDensitySumNorm

/-! Complete actual D2 density-error series over deterministic heights and source layers. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Model ASDExplicitGamma.Gaussian
open scoped ENNReal
noncomputable section

/-- Actual nonnegative per-height/layer source density error. -/
def resetDensityTerm2 (A : ABKModel 2) (Q : TriadicCube 2) (H0 : ℕ)
    (τ η q T S : ℝ) (hk : ℕ × ℕ) (ω : Cutoff.CutoffSample 2) : ℝ :=
  (S+1)*(3:ℝ)^(2*A.gamma*(localizationResetAbscissa (H0-38) hk.1 hk.2:ℝ))*
    ∑ e : Fin 3, resetDensityExcess A Q H0 τ η q T 2 hk e ω

/-- The actual D2 summand is measurable and obeys its exact retained PE budget. -/
theorem q3_reset_density_term2_bound
    (A : ABKModel 2) (h : ℝ) (hA : PlanarQ3Gaussian A h) (hg : A.gamma ≤ gammaZero)
    (Q : TriadicCube 2) (H0 : ℕ) (hH : 333 ≤ H0) (τ : ℝ) (hτ : 0 < τ)
    (t : WaveGateTuple) (q : ℝ) (hq0 : 0 ≤ q) (hq : q ≤ 1/10000000000)
    (hfloor : Real.exp (-6000) ≤ q) (hraw : (364*3^80:ℝ)*(3*(61/10:ℝ)/τ)^12 ≤ q)
    (hpast : ∀ k ≤ Q.scale-(H0:ℤ)+40, nativeInductionState A h k)
    (T : ℝ) (hT : 0 ≤ T) (hcut : 200*Real.exp (-T/4) ≤ 26*q)
    (p : ℝ) (hp : 2 ≤ p) (hp256 : p ≤ 256) (S : ℝ) (hS : 0 ≤ S) (hk : ℕ × ℕ) :
    let μ := (Cutoff.cutoffSampleLaw A).toMeasure
    let F := resetDensityTerm2 A Q H0 τ (waveGateEta t) q T S hk
    Measurable F ∧ eLpNorm F (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal (resetDensityBudget2 q p T A.gamma S (H0-38) hk) := by
  let μ := (Cutoff.cutoffSampleLaw A).toMeasure
  let Y := fun e : Fin 3 => resetDensityExcess A Q H0 τ (waveGateEta t) q T 2 hk e
  let a := (S+1)*(3:ℝ)^(2*A.gamma*(localizationResetAbscissa (H0-38) hk.1 hk.2:ℝ))
  have hb (e : Fin 3) := q3_reset_density_bounds A h hA hg Q H0 hH τ hτ t q hq0 hq hfloor hraw hpast
    T hT hcut 2 (Or.inl rfl) p hp hp256 hk e
  have hp0 : 0 ≤ p := by linarith only [hp]
  have ha : 0 ≤ a := mul_nonneg (by linarith only [hS]) (by positivity)
  have hmeas : Measurable (resetDensityTerm2 A Q H0 τ (waveGateEta t) q T S hk) :=
    measurable_const.mul (Finset.measurable_sum _ (fun e _ => (hb e).1))
  refine ⟨hmeas,?_⟩
  have hs := finite_density_sum_Lp μ (ENNReal.ofReal p)
    (ENNReal.one_le_ofReal.mpr (by linarith only [hp])) Y (fun _ => 1)
    (fun e => densityPEEnvelope q 2 p T (resetDensityDepth H0 hk e)) (fun _ => by norm_num)
    (fun e => density_PE_envelope_nonneg q 2 p T hp0 _) (fun e => (hb e).2.1)
  simp only [one_mul] at hs
  have he : resetDensityTerm2 A Q H0 τ (waveGateEta t) q T S hk =
      a • (fun ω => ∑ e : Fin 3, Y e ω) := by funext ω; rfl
  rw [he,eLpNorm_const_smul,Real.enorm_eq_ofReal ha]
  apply (mul_le_mul_of_nonneg_left hs (zero_le : (0:ℝ≥0∞) ≤ _)).trans_eq
  rw [← ENNReal.ofReal_mul ha]
  congr 1
  rw [reset_density_PE_resolution_sum q 2 p T H0 hk]
  unfold resetDensityBudget2
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  dsimp only [a]
  ring

/-- The complete actual density-error series converges absolutely almost
everywhere and has exactly the source D2 norm budget. -/
theorem q3_reset_density_series2_bound
    (A : ABKModel 2) (h : ℝ) (hA : PlanarQ3Gaussian A h) (hg : A.gamma ≤ gammaZero)
    (Q : TriadicCube 2) (H0 : ℕ) (hH : 333 ≤ H0) (τ : ℝ) (hτ : 0 < τ)
    (t : WaveGateTuple) (q : ℝ) (hq0 : 0 ≤ q) (hq : q ≤ 1/10000000000)
    (hfloor : Real.exp (-6000) ≤ q) (hraw : (364*3^80:ℝ)*(3*(61/10:ℝ)/τ)^12 ≤ q)
    (hpast : ∀ k ≤ Q.scale-(H0:ℤ)+40, nativeInductionState A h k)
    (T : ℝ) (hT : 0 ≤ T) (hcut : 200*Real.exp (-T/4) ≤ 26*q)
    (p : ℝ) (hp : 2 ≤ p) (hp256 : p ≤ 256) (S : ℝ) (hS : 0 ≤ S) :
    let μ := (Cutoff.cutoffSampleLaw A).toMeasure
    let F := resetDensityTerm2 A Q H0 τ (waveGateEta t) q T S
    (∀ᵐ ω ∂μ, Summable (fun hk => ‖F hk ω‖)) ∧
      eLpNorm (fun ω => ∑' hk, F hk ω) (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal (densityD2 q p T A.gamma S (H0-38)) := by
  have hb (hk : ℕ × ℕ) := q3_reset_density_term2_bound A h hA hg Q H0 hH τ hτ t q hq0 hq hfloor
    hraw hpast T hT hcut p hp hp256 S hS hk
  exact countable_density_series_Lp (Cutoff.cutoffSampleLaw A).toMeasure (ENNReal.ofReal p)
    (ENNReal.one_le_ofReal.mpr (by linarith only [hp]))
    (resetDensityTerm2 A Q H0 τ (waveGateEta t) q T S) (fun hk => (hb hk).1)
    (resetDensityBudget2 q p T A.gamma S (H0-38))
    (reset_density_budget2_nonneg q p T A.gamma S (by linarith only [hp]) hS _)
    _ (reset_density_budget2_hasSum q p T A.gamma S hg _) (fun hk => (hb hk).2)

end
end ASDExplicitGamma.Inverse
