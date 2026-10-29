module

public import ASDExplicitGamma.Inverse.PhysicalGaussianMissingWave

/-! Actual whole-root and exact partial-volume wave bounds in extended Lp form. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Model ASDExplicitGamma.Gaussian
open scoped ENNReal
noncomputable section

/-- The sharper whole-root physical clock, retaining both shell gaps. -/
theorem physical_whole_root_wave_Lp (A : ABKModel 2) (h : ℝ) (hA : PlanarQ3Gaussian A h)
    (j n N : ℤ) (hjn : j ≤ n) (hnN : n ≤ N) (hstate : nativeInductionState A h j)
    (a c : ℝ) (weights : ℤ → ℝ)
    (hw : ∀ k ∈ Finset.Ioc j N, 0 ≤ weights k ∧ weights k ≤ 1)
    (p : ℝ) (hp : 2 ≤ p) :
    eLpNorm (physicalMissingWave A j n N a c weights) (ENNReal.ofReal p) (Cutoff.cutoffSampleLaw A).toMeasure ≤
      ENNReal.ofReal (160*A.gamma*((n-j:ℝ)+p*((N-n:ℝ)+1))*(3:ℝ)^(2*A.gamma*(N-j:ℝ))) := by
  rcases lt_or_eq_of_le (hjn.trans hnN) with hstrict | hEq
  · have hm := physical_missing_wave_memLp A h hA j n N (hjn.trans hnN) a c weights p hp
    have hh := wholeRoot_modelBand_lq_bound hjn hnN hstrict A h hA hstate a c weights hw hp
    simp_rw [normalizedFrobeniusL4Squared_eq_spatialStatistic _ _ (Annealed.sigmaBar A j).2
      (by positivity : (0:ℝ) < (3:ℝ)^n)] at hh
    rw [← ENNReal.ofReal_toReal hm.eLpNorm_ne_top]
    exact ENNReal.ofReal_le_ofReal hh
  · subst N
    have hnj : n=j := le_antisymm hnN hjn
    subst n
    rw [physical_missing_wave_empty]
    simp only [eLpNorm_zero]
    exact zero_le

end
end ASDExplicitGamma.Inverse
