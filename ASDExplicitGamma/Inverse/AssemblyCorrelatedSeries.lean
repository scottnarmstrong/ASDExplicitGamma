module

public import ASDExplicitGamma.Inverse.AssemblyDensity
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
def assemblyCorrelatedDensityTerm (M : ABKModel 2) (Q : TriadicCube 2) (N : ℤ)
    (p S a c : ℝ) (weights : (ℕ × ℕ) → ℤ → ℝ) (j : Fin 2) (hk : ℕ × ℕ)
    (ω : Cutoff.CutoffSample 2) : ℝ :=
  let H0 := (heightEntrance (orderBand p)+5)
  (S+1)*(localizationResetAbscissa (H0-38) hk.1 hk.2:ℝ)^j.val*
    ∑ e : Fin 3, physicalResetWave M Q N H0 a c weights hk ω*
      Real.sqrt (resetDensityExcess M Q H0 resetAllOrderTau (ASDExplicitGamma.Gaussian.waveGateEta .allOrder)
        (allOrderDensity:ℝ) 1324 4 hk e ω)

/-- All actual wave/density correlations are paid at orders 2p and p. -/
theorem assembly_correlated_density_term_Lp
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (Q : TriadicCube 2) (p : ℝ) (hp : 2 ≤ p)
    (hpast : ∀ n : ℤ,
      n ≤ Q.scale-342-12*orderBand p → nativeInductionState M h n)
    (N : ℤ) (hN : Q.scale-1 ≤ N) (a c : ℝ)
    (weights : (ℕ × ℕ) → ℤ → ℝ)
    (hw : ∀ hk, ∀ k ∈ Finset.Ioc
      (physicalResetOldLabel Q ((heightEntrance (orderBand p)+5)) hk) N,
      0 ≤ weights hk k ∧ weights hk k ≤ 1)
    (S : ℝ) (hS : 0 ≤ S) (j : Fin 2) (hk : ℕ × ℕ) :
    Measurable (assemblyCorrelatedDensityTerm M Q N p S a c weights j hk) ∧
      eLpNorm (assemblyCorrelatedDensityTerm M Q N p S a c weights j hk)
        (ENNReal.ofReal p) (Cutoff.cutoffSampleLaw M).toMeasure ≤
        ENNReal.ofReal (40*(2*p+2)*bandDensityBudget4 (orderBand p) M.gamma S
          ((heightEntrance (orderBand p)+5)-38) j hk) := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let k := orderBand p
  let H0 := heightEntrance k+5
  let Y := fun e : Fin 3 => resetDensityExcess M Q H0 resetAllOrderTau
    (ASDExplicitGamma.Gaussian.waveGateEta .allOrder) (allOrderDensity:ℝ) 1324 4 hk e
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
    reset_density_excess_measurable M Q H0 _ _ _ _ _ hk e
  have hWm : Measurable W := physical_reset_wave_measurable M Q N H0 a c weights hk
  have hmeas : Measurable (assemblyCorrelatedDensityTerm M Q N p S a c weights j hk) :=
    measurable_const.mul (Finset.measurable_sum _ (fun e _ =>
      hWm.mul (Real.continuous_sqrt.measurable.comp (hY e))))
  refine ⟨hmeas, ?_⟩
  have hW := physical_reset_wave_Lp M h hM Q N hN H0 hH0 hpast' a c weights hw hk
    (2*p) (by linarith only [hp])
  have hn (e : Fin 3) :
      eLpNorm (fun ω => W ω*Real.sqrt (Y e ω)) (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal (b*Real.sqrt
        (bandDensityPowerEnvelope 4 k (resetDensityDepth H0 hk e))) := by
    have hbound := assembly_geometric_density_band_Lp M h hM hγ Q p hp
      H0 le_rfl hpast 4 (Or.inr rfl) hk e
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
  have he : assemblyCorrelatedDensityTerm M Q N p S a c weights j hk =
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

end
end ASDExplicitGamma.Inverse
