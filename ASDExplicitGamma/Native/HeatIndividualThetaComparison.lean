module

public import ASDExplicitGamma.Native.HeatIndividualComparisonW
public import ASDExplicitGamma.Native.HeatIndividualThetaRows
public import ASDExplicitGamma.Native.HeatSourceStartTheta

/-! Theta-scaled actual-law positive comparison for the 153 individual-cell systems: the actual
moments normalized by `(θ · 3/50 · z)^i` are below the endpoint certified result at every heat
time.  The rows are the configured rows after dividing the actual generator row by `θ^i`. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Algsuperdiff.Section3 Gaussian Numerics.Native Set
noncomputable section

variable {W : NativeAmp}

/-- The actual individual moments divided by `θ^i`. -/
def nativeIndividualMomentCurveTheta_W (W : NativeAmp) (M : ABKModel 2) (n : ℤ)
    (index : Fin 153) (t : ℝ) (i : Fin 21) : ℝ :=
  nativeIndividualMomentCurve_W W M n index t i / theta M ^ i.val

theorem native_individual_curve_theta_row_W
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (n : ℤ)
    (hpast : ∀ j<n,nativeInductionState M h j) (hstate : nativeInductionState M h n)
    (index : Fin 153) :
    ∀ t ∈ Ioo (0:ℝ) 1, ∀ i : Fin 21, i.val ≠ 0 →
      deriv (fun s => nativeIndividualMomentCurveTheta_W W M n index s i) t ≤
        ((nativeConfiguredSystem index).system.diag.getD i.val 0:ℝ) *
          nativeIndividualMomentCurveTheta_W W M n index t i +
        ((nativeConfiguredSystem index).system.subdiag.getD i.val 0:ℝ) *
          ((3/50:ℝ)*((nativeConfiguredSystem index).system.z:ℝ)) *
          nativeIndividualMomentCurveTheta_W W M n index t (nativePrevious i) +
        ((nativeConfiguredSystem index).system.force.getD i.val 0:ℝ) *
          nativeConfiguredMomentScale index i := by
  intro t ht i hi
  obtain ⟨hτ0, hτ1⟩ := theta_pos_le_one M hg
  set τ := theta M with hτ
  let height := (nativeConfiguredSystem index).gap
  have hheat := heat_individual_actual_moment_heat_W (W := W) M h hM n height i.val
    (heat_configured_gap_bounds index).1
  have hd : HasDerivAt (fun s => nativeIndividualMomentCurveTheta_W W M n index s i)
      (heatIndividualActualGenerator_W W M h n height i.val t / τ ^ i.val) t := by
    unfold nativeIndividualMomentCurveTheta_W nativeIndividualMomentCurve_W
    exact (hheat.2 t ht.1).div_const _
  rw [hd.deriv]
  have hiR : 1 ≤ i.val := Nat.one_le_iff_ne_zero.mpr hi
  have hrow : heatIndividualActualGenerator_W W M h n height i.val t ≤
      (nativeIndividualRow height i.val (nativeOld height)).2.1 *
        nativeSourceBandMomentK_W W M n height i.val t +
      (3/50:ℝ) * τ * (nativeIndividualRow height i.val (nativeOld height)).1 *
        nativeSourceBandMomentK_W W M n height (i.val-1) t +
      ((3/50:ℝ) * τ) ^ i.val * (nativeIndividualRow height i.val (nativeOld height)).2.2 := by
    by_cases hi1 : i.val=1
    · simpa only [heatIndividualActualGenerator_W,hi,hi1,show (1:ℕ)≠0 by decide,ite_false,ite_true,
        Nat.sub_self,pow_one] using
        native_source_band_mean_generator_le_individual_row_theta_W (W := W) M h hM hg n hpast
          hstate index t ⟨ht.1.le,ht.2.le⟩
    · simpa only [heatIndividualActualGenerator_W,hi,hi1,ite_false] using
        native_source_band_power_generator_le_individual_row_theta_W (W := W) M h hM hg n hpast
          hstate index i.val (by omega) (by omega) t ⟨ht.1.le,ht.2.le⟩
  have hpowpos : 0 < τ ^ i.val := pow_pos hτ0 _
  have hpow1 : 0 < τ ^ (i.val - 1) := pow_pos hτ0 _
  have hpj : τ ^ i.val = τ * τ ^ (i.val - 1) := by
    rw [← pow_succ']; congr 1; omega
  apply native_configured_row_of_individual_source index i hi
    (nativeSourceBandMomentK_W W M n height i.val t / τ ^ i.val)
    (nativeSourceBandMomentK_W W M n height (i.val-1) t / τ ^ (i.val - 1))
  dsimp only
  rw [div_le_iff₀ hpowpos]
  have e1 : (nativeIndividualRow height i.val (nativeOld height)).2.1 *
      (nativeSourceBandMomentK_W W M n height i.val t / τ ^ i.val) * τ ^ i.val =
      (nativeIndividualRow height i.val (nativeOld height)).2.1 *
        nativeSourceBandMomentK_W W M n height i.val t := by field_simp
  have e2 : (3/50:ℝ) * (nativeIndividualRow height i.val (nativeOld height)).1 *
      (nativeSourceBandMomentK_W W M n height (i.val-1) t / τ ^ (i.val - 1)) * τ ^ i.val =
      (3/50:ℝ) * τ * (nativeIndividualRow height i.val (nativeOld height)).1 *
        nativeSourceBandMomentK_W W M n height (i.val-1) t := by
    rw [hpj]; field_simp
  have e3 : (3/50:ℝ) ^ i.val * (nativeIndividualRow height i.val (nativeOld height)).2.2 * τ ^ i.val =
      ((3/50:ℝ) * τ) ^ i.val * (nativeIndividualRow height i.val (nativeOld height)).2.2 := by
    rw [mul_pow]; ring
  calc _ ≤ _ := hrow
    _ = _ := by rw [← e1, ← e2, ← e3]; ring

theorem native_individual_cooperative_comparison_theta_W
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (n : ℤ)
    (hpast : ∀ j<n,nativeInductionState M h j) (hstate : nativeInductionState M h n)
    (index : Fin 153) (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) (i : Fin 21) :
    nativeConfiguredNormalizedMomentCurve index
      (nativeIndividualMomentCurveTheta_W W M n index) t i ≤
      nativeVectorReal (nativeConfiguredSystem index).result i := by
  obtain ⟨hτ0, hτ1⟩ := theta_pos_le_one M hg
  have hreg := native_individual_curve_regular_W (W := W) M h hM n index
  apply nativeConfiguredNormalizedMomentCurve_le_replay_of_raw_on index
    (nativeIndividualMomentCurveTheta_W W M n index)
    (fun a => by
      unfold nativeIndividualMomentCurveTheta_W
      exact (hreg.1 a).div_const _)
    (fun t ht a => by
      unfold nativeIndividualMomentCurveTheta_W
      exact (hreg.2 t ht a).div_const _)
    (fun t _ => by
      unfold nativeIndividualMomentCurveTheta_W nativeIndividualMomentCurve_W
      simp only [Fin.val_zero, pow_zero, div_one]
      exact heat_individual_actual_moment_zero_W M n _ t)
    (native_individual_curve_theta_row_W (W := W) M h hM hg n hpast hstate index)
    ?_ ht.1 ht.2 i
  intro a ha
  have hs := native_source_band_momentK_start_le_profile_theta_W (W := W) M h n
    (nativeConfiguredSystem index).gap a.val hg hstate (by omega) (by omega)
  unfold nativeIndividualMomentCurveTheta_W nativeIndividualMomentCurve_W
  rw [div_le_iff₀ (pow_pos hτ0 _), mul_comm]
  exact hs

end
end ASDExplicitGamma.Native
