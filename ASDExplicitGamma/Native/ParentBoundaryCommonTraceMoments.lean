module

public import ASDExplicitGamma.Native.ParentBoundaryCommonTraceTests
public import ASDExplicitGamma.Native.ParentBoundaryCommonCubeFrame
public import ASDExplicitGamma.Native.ParentBoundaryCommonInitialHistory
public import ASDExplicitGamma.Cold.TwentiethMomentNorm

/-! Actual trace moments and exact initial norms for the common-center heat path. -/

@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Gaussian Inverse Main Model Triadic Cold Algsuperdiff.Section3
open scoped ENNReal
noncomputable section

local instance parentCommonTraceMomentMeasurable (Q : TriadicCube 2) :
    MeasurableSpace (ResponseCoefficient (openCubeSet Q)) := borel _
local instance parentCommonTraceMomentBorel (Q : TriadicCube 2) :
    BorelSpace (ResponseCoefficient (openCubeSet Q)) := ⟨rfl⟩

/-- All C2 polynomial observables have their actual common-center moments. -/
theorem parent_boundary_common_cube_c2_memLp
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    {P Q : TriadicCube 2} {d : ℕ} (hQ : Q ∈ descendantsAtDepth P d)
    (n : ℤ) (height : ℕ) (hheight : 1 ≤ height)
    (Φ : ResponseCoefficient (openCubeSet Q) → ℝ) (hΦ : HasPolynomiallyBoundedC2Derivatives Φ)
    (t p : ℝ) (hp : 2 ≤ p) :
    MemLp (fun ω => Φ (parentBoundaryCommonCubeObserved hQ n height t ω))
      (ENNReal.ofReal p) (Cutoff.cutoffSampleLaw M).toMeasure := by
  have hgrowth : HasPolynomialGrowth Φ := by
    obtain ⟨C,hC,m,hb,_,_⟩ := hΦ.2
    exact ⟨C,hC,m,hb⟩
  exact parent_boundary_common_cube_test_memLp M h hM hQ n height hheight Φ
    hΦ.1.continuous.measurable hgrowth t p hp

/-- Genuine finite moments of the actual common-centered trace and full trace. -/
theorem parent_boundary_common_cube_trace_memLp
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    {P Q : TriadicCube 2} {d : ℕ} (hQ : Q ∈ descendantsAtDepth P d)
    (n : ℤ) (height : ℕ) (hheight : 1 ≤ height) (t p : ℝ) (hp : 2 ≤ p) :
    let T := fun ω => squareTrace Q M.nu (Annealed.sigmaBar M n)
      (parentBoundaryCommonCubeObserved hQ n height t ω)
    MemLp T (ENNReal.ofReal p) (Cutoff.cutoffSampleLaw M).toMeasure ∧
      MemLp (fun ω => T ω+4) (ENNReal.ofReal p) (Cutoff.cutoffSampleLaw M).toMeasure := by
  intro T
  have hΦ := parent_boundary_common_square_trace_polynomial Q M.nu (Annealed.sigmaBar M n)
    M.nu_pos (Annealed.sigmaBar_characterization M n).1
  refine ⟨parent_boundary_common_cube_c2_memLp M h hM hQ n height hheight _ hΦ t p hp,?_⟩
  exact parent_boundary_common_cube_c2_memLp M h hM hQ n height hheight _
    (hasPolynomiallyBoundedC2Derivatives_add hΦ (c2_polynomial_const 4)) t p hp

/-- The twentieth-moment heat root is exactly the actual probability L20 norm. -/
theorem parent_boundary_common_cube_trace_norm_eq_root
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    {P Q : TriadicCube 2} {d : ℕ} (hQ : Q ∈ descendantsAtDepth P d)
    (n : ℤ) (height : ℕ) (hheight : 1 ≤ height) (t : ℝ) :
    let Φ := squareTrace Q M.nu (Annealed.sigmaBar M n)
    lpNorm (fun ω => Φ (parentBoundaryCommonCubeObserved hQ n height t ω)) 20
      (Cutoff.cutoffSampleLaw M).toMeasure =
      (parentBoundaryCommonCubeAverage M hQ n height (fun x => Φ x^(20:ℝ)) t)^((20:ℝ)⁻¹) := by
  intro Φ
  let T := fun ω => Φ (parentBoundaryCommonCubeObserved hQ n height t ω)
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  have hm : MemLp T 20 μ := by
    simpa only [show ENNReal.ofReal (20:ℝ)=(20:ℝ≥0∞) by norm_num] using
      (parent_boundary_common_cube_trace_memLp M h hM hQ n height hheight t 20 (by norm_num)).1
  have hp := cold_lpNorm_twenty_pow hm
  have he : parentBoundaryCommonCubeAverage M hQ n height (fun x => Φ x^(20:ℝ)) t=
      ∫ ω,T ω^(20:ℕ) ∂μ := by
    simp only [parentBoundaryCommonCubeAverage,Real.rpow_ofNat,T,μ]
  rw [he,←hp,←Real.rpow_natCast_mul (lpNorm_nonneg (f := T) (p := 20) (μ := μ))]
  norm_num
  rfl

/-- The initial common-centered trace is literally the completed physical
cutoff trace, with its starting frame unchanged. -/
theorem parent_boundary_common_cube_initial_trace
    (M : ABKModel 2) {P Q : TriadicCube 2} {d : ℕ}
    (hQ : Q ∈ descendantsAtDepth P d) (n : ℤ) (height : ℕ) (ω : Cutoff.CutoffSample 2) :
    squareTrace Q M.nu (Annealed.sigmaBar M n)
      (parentBoundaryCommonCubeObserved hQ n height 0 ω)=historyTrace M n Q ω := by
  have hzero : parentBoundaryCommonCubeObserved hQ n height 0 ω=
      parentBoundaryCommonOpenCellCoefficient hQ (parentBoundaryCommonCubeBand P n height 0 ω) := by
    simp only [parentBoundaryCommonCubeObserved,parentBoundaryCommonCubeCentered,
      parentBoundaryCommonCubeBand,Real.sqrt_zero,zero_smul,add_zero]
  rw [hzero,parent_boundary_common_cube_band_observed_eq M hQ]
  unfold squareTrace historyTrace traceDefect
  rw [parent_boundary_common_cube_band_coarse_frame M Q n height 0 ω (Annealed.sigmaBar M n)
    (Annealed.sigmaBar_characterization M n).1 (d := 0) (by simp)]
  rw [parent_boundary_common_band_coefficient_zero]
  simp only [frameMatrix,inv_one,one_mul,Matrix.trace_smul,smul_eq_mul]

/-- Exact initial probability norm at the observed scale, before any bound. -/
theorem parent_boundary_common_cube_initial_norm
    (M : ABKModel 2) {P Q : TriadicCube 2} {d : ℕ}
    (hQ : Q ∈ descendantsAtDepth P d) (n : ℤ) (height : ℕ) :
    lpNorm (fun ω => squareTrace Q M.nu (Annealed.sigmaBar M n)
      (parentBoundaryCommonCubeObserved hQ n height 0 ω)) 20 (Cutoff.cutoffSampleLaw M).toMeasure =
      lpNorm (cutoffTraceDefect M n Q.scale) 20 (Cutoff.cutoffSampleLaw M).toMeasure := by
  have he : (fun ω => squareTrace Q M.nu (Annealed.sigmaBar M n)
      (parentBoundaryCommonCubeObserved hQ n height 0 ω))=historyTrace M n Q :=
    funext (parent_boundary_common_cube_initial_trace M hQ n height)
  rw [he]
  exact congrArg ENNReal.toReal (history_trace_norm_origin M n Q)

end
end ASDExplicitGamma.Native
