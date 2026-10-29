module

public import ASDExplicitGamma.Native.HeatActualIndividualCurveW

public import ASDExplicitGamma.Native.NativeBandWeight

/-! Actual-law positive comparison for exactly the153 individual-cell systems. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Algsuperdiff.Section3 Gaussian Numerics.Native Set
noncomputable section

variable {W : NativeAmp}

/-- The twenty-one actual individual-cell moments in a selected source gap. -/
def nativeIndividualMomentCurve_W (W : NativeAmp) (M : ABKModel 2) (n : ℤ) (index : Fin 153)
    (t : ℝ) (i : Fin 21) : ℝ :=
  nativeSourceBandMomentK_W W M n (nativeConfiguredSystem index).gap i.val t

/-- Actual moments normalized by the producer's a^k z^k, with coordinate0=1. -/
def nativeIndividualNormalizedMomentCurve_W (W : NativeAmp) (M : ABKModel 2) (n : ℤ) (index : Fin 153) :
    ℝ → Fin 21 → ℝ :=
  nativeConfiguredNormalizedMomentCurve index (nativeIndividualMomentCurve_W W M n index)

/-- The physical source curve has exactly the interval regularity needed by
positive comparison. -/
theorem native_individual_curve_regular_W
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (n : ℤ) (index : Fin 153) :
    (∀ i : Fin 21,ContinuousOn (fun t => nativeIndividualMomentCurve_W W M n index t i) (Icc (0:ℝ) 1)) ∧
    (∀ t ∈ Ioo (0:ℝ) 1,∀ i : Fin 21,DifferentiableAt ℝ (fun s => nativeIndividualMomentCurve_W W M n index s i) t) := by
  have hheat (i : Fin 21) := heat_individual_actual_moment_heat_W (W := W) M h hM n
    (nativeConfiguredSystem index).gap i.val (heat_configured_gap_bounds index).1
  refine ⟨fun i => (hheat i).1.mono (fun _ ht => ht.1),?_⟩
  intro t ht i
  exact ((hheat i).2 t ht.1).differentiableAt

/-- Every physical source coordinate obeys the selected raw matrix row. -/
theorem native_individual_curve_raw_rows_W
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (n : ℤ)
    (hpast : ∀ j<n,nativeInductionState M h j) (hstate : nativeInductionState M h n)
    (index : Fin 153) :
    ∀ t ∈ Ioo (0:ℝ) 1,∀ i : Fin 21,i.val ≠ 0 →
      deriv (fun s => nativeIndividualMomentCurve_W W M n index s i) t ≤
        ((nativeConfiguredSystem index).system.diag.getD i.val 0:ℝ)*nativeIndividualMomentCurve_W W M n index t i+
        ((nativeConfiguredSystem index).system.subdiag.getD i.val 0:ℝ)*
          ((3/50:ℝ)*((nativeConfiguredSystem index).system.z:ℝ))*nativeIndividualMomentCurve_W W M n index t (nativePrevious i)+
        ((nativeConfiguredSystem index).system.force.getD i.val 0:ℝ)*nativeConfiguredMomentScale index i := by
  intro t ht i hi
  exact heat_individual_actual_deriv_le_configured_W M h hM hg n hpast hstate index i hi t ht

/-- The153 individual-cell comparisons from proved physical inputs only.
The complete forcing column is retained and the certified time-one result
bounds every actual heat time in the closed unit interval. -/
theorem native_individual_cooperative_comparison_W
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (n : ℤ)
    (hpast : ∀ j<n,nativeInductionState M h j) (hstate : nativeInductionState M h n)
    (index : Fin 153) (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) (i : Fin 21) :
    nativeIndividualNormalizedMomentCurve_W W M n index t i ≤
      nativeVectorReal (nativeConfiguredSystem index).result i := by
  have hreg := native_individual_curve_regular_W (W := W) M h hM n index
  apply nativeConfiguredNormalizedMomentCurve_le_replay_of_raw_on index
    (nativeIndividualMomentCurve_W W M n index) hreg.1 hreg.2
    (fun t _ => heat_individual_actual_moment_zero_W M n _ t)
    (native_individual_curve_raw_rows_W M h hM hg n hpast hstate index)
    ?_ ht.1 ht.2 i
  intro a ha
  exact native_source_band_momentK_start_le_profile_W M h n (nativeConfiguredSystem index).gap
    a.val hg hstate (by omega) (by omega)

end
end ASDExplicitGamma.Native
