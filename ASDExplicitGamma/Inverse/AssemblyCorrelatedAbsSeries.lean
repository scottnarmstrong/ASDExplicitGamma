module

public import ASDExplicitGamma.Inverse.AssemblyCorrelatedSeries

/-! Absolute values of the complete actual wave-density correlation series. -/

@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open scoped ENNReal
noncomputable section

/-- Absolute value of one actual height/layer correlation payment. -/
def assemblyCorrelatedDensityAbsTerm
    (M : ABKModel 2) (Q : TriadicCube 2) (N : ℤ) (p S a c : ℝ)
    (weights : (ℕ × ℕ) → ℤ → ℝ) (j : Fin 2) (hk : ℕ × ℕ)
    (ω : Cutoff.CutoffSample 2) : ℝ :=
  |assemblyCorrelatedDensityTerm M Q N p S a c weights j hk ω|

/-- The absolute correlation series has the same complete all-height budget.
This is the form used when the signed cross term is absorbed into a positive
trace envelope. -/
theorem assembly_correlated_density_abs_series_Lp
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (Q : TriadicCube 2) (p : ℝ) (hp : 2 ≤ p)
    (hpast : ∀ n : ℤ,
      n ≤ Q.scale-342-12*orderBand p → nativeInductionState M h n)
    (N : ℤ) (hN : Q.scale-1 ≤ N) (a c : ℝ)
    (weights : (ℕ × ℕ) → ℤ → ℝ)
    (hw : ∀ hk, ∀ k ∈ Finset.Ioc
      (physicalResetOldLabel Q ((heightEntrance (orderBand p)+5)) hk) N,
      0 ≤ weights hk k ∧ weights hk k ≤ 1)
    (S : ℝ) (hS : 0 ≤ S) (j : Fin 2) :
    (∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      Summable (fun hk => ‖assemblyCorrelatedDensityAbsTerm M Q N p S a c weights j hk ω‖)) ∧
      eLpNorm (fun ω => ∑' hk,
        assemblyCorrelatedDensityAbsTerm M Q N p S a c weights j hk ω)
        (ENNReal.ofReal p) (Cutoff.cutoffSampleLaw M).toMeasure ≤
        ENNReal.ofReal (40*(2*p+2)*bandDensitySum4 (orderBand p) M.gamma S
          ((heightEntrance (orderBand p)+5)-38) j) := by
  let F := fun hk ω =>
    assemblyCorrelatedDensityAbsTerm M Q N p S a c weights j hk ω
  let B := fun hk => 40*(2*p+2)*bandDensityBudget4 (orderBand p) M.gamma S
    ((heightEntrance (orderBand p)+5)-38) j hk
  have hmeas (hk : ℕ × ℕ) : Measurable (F hk) :=
    (assembly_correlated_density_term_Lp M h hM hγ Q p hp hpast N hN
      a c weights hw S hS j hk).1.abs
  have hbound (hk : ℕ × ℕ) :
      eLpNorm (F hk) (ENNReal.ofReal p) (Cutoff.cutoffSampleLaw M).toMeasure ≤
        ENNReal.ofReal (B hk) := by
    have ht := assembly_correlated_density_term_Lp M h hM hγ Q p hp hpast
      N hN a c weights hw S hS j hk
    have heq : eLpNorm (F hk) (ENNReal.ofReal p)
        (Cutoff.cutoffSampleLaw M).toMeasure =
        eLpNorm (assemblyCorrelatedDensityTerm M Q N p S a c weights j hk)
          (ENNReal.ofReal p) (Cutoff.cutoffSampleLaw M).toMeasure := by
      simpa only [F,assemblyCorrelatedDensityAbsTerm,Real.norm_eq_abs] using
        eLpNorm_norm (assemblyCorrelatedDensityTerm M Q N p S a c weights j hk)
          ht.1.aestronglyMeasurable
    rw [heq]
    simpa only [B] using ht.2
  have hnonneg (hk : ℕ × ℕ) : 0 ≤ B hk := by
    dsimp only [B]
    exact mul_nonneg (by positivity)
      (band_density_budget4_nonneg _ _ S hS _ j hk)
  simpa only [F,B,assemblyCorrelatedDensityAbsTerm] using
    countable_density_series_Lp (Cutoff.cutoffSampleLaw M).toMeasure
      (ENNReal.ofReal p) (ENNReal.one_le_ofReal.mpr (by linarith only [hp])) F hmeas B hnonneg
      (40*(2*p+2)*bandDensitySum4 (orderBand p) M.gamma S
        ((heightEntrance (orderBand p)+5)-38) j)
      ((band_density_budget4_hasSum (orderBand p) M.gamma S hγ
        ((heightEntrance (orderBand p)+5)-38) j).mul_left (40*(2*p+2))) hbound

end
end ASDExplicitGamma.Inverse
