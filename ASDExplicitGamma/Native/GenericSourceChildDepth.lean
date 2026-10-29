module

public import ASDExplicitGamma.Native.GenericSourceChildRationalActual
public import ASDExplicitGamma.Native.GenericSourceDepthRows

/-! Refined child means on coarse source cubes. The completed q1 input is
kept explicit; it is read strictly before the terminal cutoff. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Algsuperdiff.Section3 ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Inverse ASDExplicitGamma.Triadic ASDExplicitGamma.Cold ASDExplicitGamma.Variational
open ASDExplicitGamma.Numerics.Native
noncomputable section

/-- A refined child at gap 9+d lies ten generations below the depth-d
source cube. Translation invariance and genuine mean subadditivity transfer
its bound without any independence or loss in its constant. -/
theorem native_source_depth_child_mean_of_q1
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (m : ℤ)
    (hpast : ∀ k < m, nativeInductionState M h k) (depth : Fin 56)
    (hq1 : (∫ ω, cutoffTraceDefect M (m-((9+depth.val:ℕ):ℤ))
      (m-((9+depth.val:ℕ):ℤ)-1) ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
      theta M*(nativeQstar:ℝ)) :
    (∫ ω, cutoffTraceDefect M m (m-(depth.val:ℤ)) ω
      ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
      theta M*(nativeSourceChildRationalWitness depth:ℝ) := by
  let height := 9+depth.val
  let n := m-(height:ℤ)
  have hnm : n<m := by dsimp [n,height]; omega
  have hp : ∀ k<n, nativeInductionState M h k := fun k hk => hpast k (hk.trans hnm)
  have hh : height ≤ nativeSourceChildAuxHeight (decide (40<height)) := by
    dsimp [nativeSourceChildAuxHeight]
    split_ifs <;> simp_all only [decide_eq_true_eq,not_lt]
    all_goals dsimp [height]; omega
  have hfine := native_source_completed_child_mean_rational_of_q1 M h hM hg n height
    (by dsimp [height]; omega) hp (hpast n hnm) (decide (40<height)) hh hq1
  have hcut : n+(height:ℤ)=m := by dsimp [n]; omega
  rw [hcut] at hfine
  have hsub := coldNativeCellTrace_mean_subadditive M m (originCube 2 (m-(depth.val:ℤ))) 10
  rw [coldNativeCellTrace_integral] at hsub
  have hscale : (originCube 2 (m-(depth.val:ℤ))).scale-((10:ℕ):ℤ)=n-1 := by
    dsimp [originCube,n,height]; omega
  rw [hscale] at hsub
  exact (hsub.trans hfine).trans (mul_le_mul_of_nonneg_left
    ((Rat.cast_le (K := ℝ)).mpr (native_source_child_rational_witness_bound depth))
    (div_nonneg M.shellPrefix.gamma_pos.le (by norm_num [gammaZero])))

/-- Positive extended expectations preserve the refined depth bound. -/
theorem native_source_depth_child_mean_ennreal_of_q1
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (m : ℤ)
    (hpast : ∀ k < m, nativeInductionState M h k) (depth : Fin 56)
    (hq1 : (∫ ω, cutoffTraceDefect M (m-((9+depth.val:ℕ):ℤ))
      (m-((9+depth.val:ℕ):ℤ)-1) ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
      theta M*(nativeQstar:ℝ)) :
    nativeCompletedSourceMean M m depth.val ≤
      ENNReal.ofReal (theta M*(nativeSourceChildRationalWitness depth:ℝ)) := by
  rw [nativeCompletedSourceMean,←ofReal_integral_eq_lintegral_ofReal
    (integrable_cutoffTraceDefect M m (m-(depth.val:ℤ)))
    (Filter.Eventually.of_forall (cutoffTraceDefect_nonneg M m (m-(depth.val:ℤ))))]
  exact ENNReal.ofReal_le_ofReal
    (native_source_depth_child_mean_of_q1 M h hM hg m hpast depth hq1)

end
end ASDExplicitGamma.Native
