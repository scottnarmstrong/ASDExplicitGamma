module

public import ASDExplicitGamma.Inverse.GaussianDensity
public import ASDExplicitGamma.Inverse.SelectedWave
public import ASDExplicitGamma.Inverse.CorrelatedBudgets
public import ASDExplicitGamma.Inverse.StoppedDensitySumNorm

/-! Actual correlated errors, summed over all deterministic heights and layers. -/

@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open scoped ENNReal
noncomputable section

/-- The literal wave-density error before selecting the root height. -/
def correlatedDensityTerm (M : ABKModel 2) (Q : TriadicCube 2) (N : ℤ)
    (p S a c : ℝ) (weights : (ℕ × ℕ) → ℤ → ℝ) (j : Fin 2) (hk : ℕ × ℕ)
    (ω : Cutoff.CutoffSample 2) : ℝ :=
  let H0 := heightEntrance (orderBand p)
  (S+1)*(localizationResetAbscissa (H0-38) hk.1 hk.2:ℝ)^j.val*
    ∑ e : Fin 3, physicalResetWave M Q N H0 a c weights hk ω*
      Real.sqrt (rootLayerDensityExcess M Q (H0+hk.1) (hk.2+1) e 4 ω)

/-- All actual wave/density correlations are paid at orders 2p and p. -/
theorem correlated_density_term_Lp
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (Q : TriadicCube 2) (p : ℝ) (hp : 2 ≤ p)
    (hpast : ∀ n : ℤ,
      n ≤ Q.scale-342-12*orderBand p → nativeInductionState M h n)
    (N : ℤ) (hN : Q.scale-1 ≤ N) (a c : ℝ)
    (weights : (ℕ × ℕ) → ℤ → ℝ)
    (hw : ∀ hk, ∀ k ∈ Finset.Ioc
      (physicalResetOldLabel Q (heightEntrance (orderBand p)) hk) N,
      0 ≤ weights hk k ∧ weights hk k ≤ 1)
    (S : ℝ) (hS : 0 ≤ S) (j : Fin 2) (hk : ℕ × ℕ) :
    Measurable (correlatedDensityTerm M Q N p S a c weights j hk) ∧
      eLpNorm (correlatedDensityTerm M Q N p S a c weights j hk)
        (ENNReal.ofReal p) (Cutoff.cutoffSampleLaw M).toMeasure ≤
        ENNReal.ofReal (40*(2*p+2)*bandDensityBudget4 (orderBand p) M.gamma S
          (heightEntrance (orderBand p)-38) j hk) := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let k := orderBand p
  let H0 := heightEntrance k
  let Y := fun e : Fin 3 => rootLayerDensityExcess M Q (H0+hk.1) (hk.2+1) e 4
  let W := physicalResetWave M Q N H0 a c weights hk
  let u := (S+1)*(localizationResetAbscissa (H0-38) hk.1 hk.2:ℝ)^j.val
  let b := 40*(2*p+2)*(3:ℝ)^(4*M.gamma*(localizationResetAbscissa (H0-38) hk.1 hk.2:ℝ))
  have hH0 : 333 ≤ H0 := by unfold H0 heightEntrance; omega
  have hpast' : ∀ n ≤ Q.scale-(H0:ℤ)+35, nativeInductionState M h n := by
    intro n hn
    apply hpast n
    unfold H0 heightEntrance at hn
    omega
  have hu : 0 ≤ u := by dsimp only [u]; positivity
  have hb : 0 ≤ b := by dsimp only [b]; positivity
  have hY (e : Fin 3) : Measurable (Y e) :=
    root_density_excess_measurable M Q (H0+hk.1) (hk.2+1) e 4
  have hWm : Measurable W := physical_reset_wave_measurable M Q N H0 a c weights hk
  have hmeas : Measurable (correlatedDensityTerm M Q N p S a c weights j hk) :=
    measurable_const.mul (Finset.measurable_sum _ (fun e _ =>
      hWm.mul (Real.continuous_sqrt.measurable.comp (hY e))))
  refine ⟨hmeas, ?_⟩
  have hW := physical_reset_wave_Lp M h hM Q N hN H0 hH0 hpast' a c weights hw hk
    (2*p) (by linarith only [hp])
  have hn (e : Fin 3) :
      eLpNorm (fun ω => W ω*Real.sqrt (Y e ω)) (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal (b*Real.sqrt
        (bandDensityPowerEnvelope 4 k (resetDensityDepth H0 hk e))) := by
    have hbound := root_layer_density_band_Lp M h hM hγ Q p hp hpast
      (H0+hk.1) (hk.2+1) (by dsimp [H0,k]; omega) (by omega) e 4 (Or.inr rfl)
    rw [layer_reset_density_depth H0 (by omega) hk e] at hbound
    have hC : 0 ≤ bandDensityPowerEnvelope 4 k (resetDensityDepth H0 hk e) := by
      rw [band_density_envelope_eq]
      exact Finset.sum_nonneg fun i _ =>
        mul_nonneg (band_density_coefficient_nonneg 4 k i) (by positivity)
    have hh := physical_wave_sqrt_density_holder μ W (Y e)
      hWm.aestronglyMeasurable (hY e).aestronglyMeasurable (fun ω => le_max_right _ _)
      p _ (by linarith only [hp]) hC hbound
    apply (hh.trans (mul_le_mul_left hW (ENNReal.ofReal (Real.sqrt _)))).trans_eq
    rw [mul_comm _ (ENNReal.ofReal (Real.sqrt _)),
      ← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
    congr 1
    dsimp only [b]
    ring
  have hs := finite_density_sum_Lp μ (ENNReal.ofReal p)
    (ENNReal.one_le_ofReal.mpr (by linarith only [hp]))
    (fun e ω => W ω*Real.sqrt (Y e ω)) (fun _ => 1)
    (fun e => b*Real.sqrt (bandDensityPowerEnvelope 4 k (resetDensityDepth H0 hk e)))
    (fun _ => by norm_num) (fun _ => mul_nonneg hb (Real.sqrt_nonneg _)) hn
  simp only [one_mul] at hs
  have he : correlatedDensityTerm M Q N p S a c weights j hk =
      u • (fun ω => ∑ e : Fin 3, W ω*Real.sqrt (Y e ω)) := by funext ω; rfl
  rw [he, eLpNorm_const_smul, Real.enorm_eq_ofReal hu]
  apply (mul_le_mul_of_nonneg_left hs (zero_le : (0:ℝ≥0∞) ≤ _)).trans
  rw [← ENNReal.ofReal_mul hu, ← Finset.mul_sum]
  apply ENNReal.ofReal_le_ofReal
  have hr := band_density_sqrt_resolution_sum k H0 hk
  rw [← mul_assoc]
  apply (mul_le_mul_of_nonneg_left hr (mul_nonneg hu hb)).trans_eq
  unfold bandDensityBudget4
  dsimp only [u,b]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hex : -densityPERate 4 i*
      ((localizationResetAbscissa (H0-38) hk.1 hk.2:ℝ)+1)/2 =
      -(densityPERate 4 i/2)*((localizationResetAbscissa (H0-38) hk.1 hk.2:ℝ)+1) := by ring
  rw [hex]
  ring

/-- The entire nonnegative error is summed before the height is selected.
The result retains every height, layer, resolution and corrected band power. -/
theorem correlated_density_series_Lp
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (Q : TriadicCube 2) (p : ℝ) (hp : 2 ≤ p)
    (hpast : ∀ n : ℤ,
      n ≤ Q.scale-342-12*orderBand p → nativeInductionState M h n)
    (N : ℤ) (hN : Q.scale-1 ≤ N) (a c : ℝ)
    (weights : (ℕ × ℕ) → ℤ → ℝ)
    (hw : ∀ hk, ∀ k ∈ Finset.Ioc
      (physicalResetOldLabel Q (heightEntrance (orderBand p)) hk) N,
      0 ≤ weights hk k ∧ weights hk k ≤ 1)
    (S : ℝ) (hS : 0 ≤ S) (j : Fin 2) :
    (∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      Summable (fun hk => ‖correlatedDensityTerm M Q N p S a c weights j hk ω‖)) ∧
      eLpNorm (fun ω => ∑' hk, correlatedDensityTerm M Q N p S a c weights j hk ω)
        (ENNReal.ofReal p) (Cutoff.cutoffSampleLaw M).toMeasure ≤
        ENNReal.ofReal (40*(2*p+2)*bandDensitySum4 (orderBand p) M.gamma S
          (heightEntrance (orderBand p)-38) j) := by
  have hb (hk : ℕ × ℕ) := correlated_density_term_Lp M h hM hγ Q p hp hpast N hN
    a c weights hw S hS j hk
  exact countable_density_series_Lp (Cutoff.cutoffSampleLaw M).toMeasure
    (ENNReal.ofReal p) (ENNReal.one_le_ofReal.mpr (by linarith only [hp]))
    (correlatedDensityTerm M Q N p S a c weights j) (fun hk => (hb hk).1)
    (fun hk => 40*(2*p+2)*bandDensityBudget4 (orderBand p) M.gamma S
      (heightEntrance (orderBand p)-38) j hk)
    (fun hk => mul_nonneg (by positivity)
      (band_density_budget4_nonneg _ _ S hS _ j hk))
    _ ((band_density_budget4_hasSum (orderBand p) M.gamma S hγ
      (heightEntrance (orderBand p)-38) j).mul_left (40*(2*p+2))) (fun hk => (hb hk).2)

end
end ASDExplicitGamma.Inverse
