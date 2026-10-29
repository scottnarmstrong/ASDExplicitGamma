module

public import ASDExplicitGamma.Inverse.StoppedResetDensitySeries2

/-! Complete coarse e_Z density-error bound as an alternative to retained PE. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Model ASDExplicitGamma.Gaussian
open scoped ENNReal
noncomputable section

/-- The exact per-height/layer source coarse density envelope. -/
def resetDensityEZBudget (γ S : ℝ) (C : ℕ) (hk : ℕ × ℕ) : ℝ :=
  ((S+1)*(1+(3:ℝ)^(1/2:ℝ)+(3:ℝ)^(2*(1/2:ℝ))))*
    ((3:ℝ)^(2*γ*(localizationResetAbscissa C hk.1 hk.2:ℝ))*
     (3:ℝ)^(-(1/2:ℝ)*((localizationResetAbscissa C hk.1 hk.2:ℝ)+1)))

/-- The complete e_Z sum before multiplication by E_delta*g(6*tau). -/
def densityEZ (γ S : ℝ) (C : ℕ) : ℝ :=
  ((S+1)*(1+(3:ℝ)^(1/2:ℝ)+(3:ℝ)^(2*(1/2:ℝ))))*
    densityResetPowerSum (2*γ) (1/2) C

/-- Both infinite indices are paid exactly, with no finite scan. -/
theorem reset_density_EZ_hasSum (γ S : ℝ) (hg : γ ≤ gammaZero) (C : ℕ) :
    HasSum (resetDensityEZBudget γ S C) (densityEZ γ S C) := by
  have hg' : γ ≤ 17/50000 := hg
  exact (density_reset_power_hasSum (2*γ) (1/2) (by linarith only [hg']) C).mul_left _

/-- Exact source sum of the three coarse resolution bounds. -/
theorem reset_density_coarse_resolution_sum (H0 : ℕ) (hk : ℕ × ℕ) :
    (∑ e : Fin 3, (3:ℝ)^(-(resetDensityDepth H0 hk e:ℝ)/2)) =
      (1+(3:ℝ)^(1/2:ℝ)+(3:ℝ)^(2*(1/2:ℝ)))*
        (3:ℝ)^(-(1/2:ℝ)*((localizationResetAbscissa (H0-38) hk.1 hk.2:ℝ)+1)) := by
  have hh := localization_resolution_power_sum (1/2) (localizationResetAbscissa (H0-38) hk.1 hk.2:ℝ)
  apply Eq.trans _ hh
  apply Finset.sum_congr rfl
  intro e _
  rw [reset_density_depth_real H0 hk e]
  congr 1
  ring

/-- The actual source summand obeys the coarse envelope as well as PE. -/
theorem q3_reset_density_term2_coarse
    (A : ABKModel 2) (h : ℝ) (hA : PlanarQ3Gaussian A h) (hg : A.gamma ≤ gammaZero)
    (Q : TriadicCube 2) (H0 : ℕ) (hH : 333 ≤ H0) (τ : ℝ) (hτ : 0 < τ)
    (t : WaveGateTuple) (q : ℝ) (hq0 : 0 ≤ q) (hq : q ≤ 1/10000000000)
    (hfloor : Real.exp (-6000) ≤ q) (hraw : (364*3^80:ℝ)*(3*(61/10:ℝ)/τ)^12 ≤ q)
    (hpast : ∀ k ≤ Q.scale-(H0:ℤ)+40, nativeInductionState A h k)
    (T : ℝ) (hT : 0 ≤ T) (hcut : 200*Real.exp (-T/4) ≤ 26*q)
    (p : ℝ) (hp : 2 ≤ p) (hp256 : p ≤ 256) (S : ℝ) (hS : 0 ≤ S) (hk : ℕ × ℕ) :
    eLpNorm (resetDensityTerm2 A Q H0 τ (waveGateEta t) q T S hk) (ENNReal.ofReal p)
      (Cutoff.cutoffSampleLaw A).toMeasure ≤ ENNReal.ofReal (resetDensityEZBudget A.gamma S (H0-38) hk) := by
  let μ := (Cutoff.cutoffSampleLaw A).toMeasure
  let Y := fun e : Fin 3 => resetDensityExcess A Q H0 τ (waveGateEta t) q T 2 hk e
  let a := (S+1)*(3:ℝ)^(2*A.gamma*(localizationResetAbscissa (H0-38) hk.1 hk.2:ℝ))
  have hb (e : Fin 3) := q3_reset_density_bounds A h hA hg Q H0 hH τ hτ t q hq0 hq hfloor hraw hpast
    T hT hcut 2 (Or.inl rfl) p hp hp256 hk e
  have ha : 0 ≤ a := mul_nonneg (by linarith only [hS]) (by positivity)
  have hs := finite_density_sum_Lp μ (ENNReal.ofReal p)
    (ENNReal.one_le_ofReal.mpr (by linarith only [hp])) Y (fun _ => 1)
    (fun e => (3:ℝ)^(-(resetDensityDepth H0 hk e:ℝ)/2)) (fun _ => by norm_num)
    (fun _ => by positivity) (fun e => (hb e).2.2)
  simp only [one_mul] at hs
  have he : resetDensityTerm2 A Q H0 τ (waveGateEta t) q T S hk =
      a • (fun ω => ∑ e : Fin 3, Y e ω) := by funext ω; rfl
  rw [he,eLpNorm_const_smul,Real.enorm_eq_ofReal ha]
  apply (mul_le_mul_of_nonneg_left hs (zero_le : (0:ℝ≥0∞) ≤ _)).trans_eq
  rw [← ENNReal.ofReal_mul ha]
  congr 1
  rw [reset_density_coarse_resolution_sum H0 hk]
  unfold resetDensityEZBudget
  dsimp only [a]
  ring

/-- The complete actual source density-error series also has the coarse e_Z
budget, with exactly its three resolutions and complete reset profile. -/
theorem q3_reset_density_series2_coarse
    (A : ABKModel 2) (h : ℝ) (hA : PlanarQ3Gaussian A h) (hg : A.gamma ≤ gammaZero)
    (Q : TriadicCube 2) (H0 : ℕ) (hH : 333 ≤ H0) (τ : ℝ) (hτ : 0 < τ)
    (t : WaveGateTuple) (q : ℝ) (hq0 : 0 ≤ q) (hq : q ≤ 1/10000000000)
    (hfloor : Real.exp (-6000) ≤ q) (hraw : (364*3^80:ℝ)*(3*(61/10:ℝ)/τ)^12 ≤ q)
    (hpast : ∀ k ≤ Q.scale-(H0:ℤ)+40, nativeInductionState A h k)
    (T : ℝ) (hT : 0 ≤ T) (hcut : 200*Real.exp (-T/4) ≤ 26*q)
    (p : ℝ) (hp : 2 ≤ p) (hp256 : p ≤ 256) (S : ℝ) (hS : 0 ≤ S) :
    eLpNorm (fun ω => ∑' hk, resetDensityTerm2 A Q H0 τ (waveGateEta t) q T S hk ω)
      (ENNReal.ofReal p) (Cutoff.cutoffSampleLaw A).toMeasure ≤
        ENNReal.ofReal (densityEZ A.gamma S (H0-38)) := by
  have hb (hk : ℕ × ℕ) := q3_reset_density_term2_bound A h hA hg Q H0 hH τ hτ t q hq0 hq hfloor
    hraw hpast T hT hcut p hp hp256 S hS hk
  exact (countable_density_series_Lp (Cutoff.cutoffSampleLaw A).toMeasure (ENNReal.ofReal p)
    (ENNReal.one_le_ofReal.mpr (by linarith only [hp]))
    (resetDensityTerm2 A Q H0 τ (waveGateEta t) q T S) (fun hk => (hb hk).1)
    (resetDensityEZBudget A.gamma S (H0-38))
    (fun hk => by unfold resetDensityEZBudget; positivity)
    _ (reset_density_EZ_hasSum A.gamma S hg _)
    (fun hk => q3_reset_density_term2_coarse A h hA hg Q H0 hH τ hτ t q hq0 hq hfloor hraw hpast
      T hT hcut p hp hp256 S hS hk)).2

end
end ASDExplicitGamma.Inverse
