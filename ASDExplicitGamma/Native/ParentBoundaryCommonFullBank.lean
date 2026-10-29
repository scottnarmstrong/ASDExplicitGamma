module

public import ASDExplicitGamma.Native.ParentBoundaryCommonPhysicalYoung
public import ASDExplicitGamma.Native.ParentBoundaryCommonCubeGauge
public import ASDExplicitGamma.Native.ParentBoundaryObserverBandBank
public import ASDExplicitGamma.Native.ParentBoundaryBandRegular
public import ASDExplicitGamma.Native.ParentBoundaryCommonCubeFrame
public import ASDExplicitGamma.Inverse.PureFluxGeneratorRowSource
public import ASDExplicitGamma.Inverse.PureFluxGeneratorCenteredSource
public import ASDExplicitGamma.Inverse.PureFluxGeneratorTiledProjected
public import ASDExplicitGamma.Inverse.PureFluxFeedbackCoefficient
public import ASDExplicitGamma.Gaussian.CovarianceRow
public import ASDExplicitGamma.Native.ParentBoundaryBandTraceMoments

/-! Actual common-center full traces with all original bank inputs discharged. -/

@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Gaussian Inverse Main Triadic Algsuperdiff.Section3
open scoped ENNReal
noncomputable section

/-- Exact full-response trace identity on every translated physical source cube. -/
theorem parent_boundary_common_physical_full_eq
    (M : ABKModel 2) (Q : TriadicCube 2) (n : ℤ) (height : ℕ) (t : ℝ) (ω : Cutoff.CutoffSample 2) :
    nativeSourceFullResponseTrace M Q n (n+(height:ℤ)) (fun _ => Real.sqrt t) ω=
      traceDefect (cubeSet Q) (attenuatedCoefficient M n (n+(height:ℤ)) (fun _ => Real.sqrt t) ω)
        (Annealed.sigmaBar M n)+4 := by
  rw [traceDefect_eq_full_framedTrace]
  unfold nativeSourceFullResponseTrace
  ring

/-- The exact original physical full response has its actual source L128
profile and is a genuine L128 random variable. -/
theorem parent_boundary_common_physical_full_L128
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (hg : M.gamma ≤ gammaZero)
    (Q : TriadicCube 2) (n : ℤ) (height depth : ℕ) (hQ : Q.scale=n-(depth:ℤ))
    (hpast : ∀ k<n,nativeInductionState M h k) (t : ℝ) (ht : t ≤ 1) :
    let U := nativeSourceFullResponseTrace M Q n (n+(height:ℤ)) (fun _ => Real.sqrt t)
    MemLp U 128 (Cutoff.cutoffSampleLaw M).toMeasure ∧
      eLpNorm U 128 (Cutoff.cutoffSampleLaw M).toMeasure ≤ ENNReal.ofReal (parentBoundaryBandTraceCap M height depth) := by
  intro U
  have hcap : eLpNorm U 128 (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal (parentBoundaryBandTraceCap M height depth) := by
    simpa only [U,parentBoundaryBandTraceCap,show ENNReal.ofReal (128:ℝ)=(128:ℝ≥0∞) by norm_num] using
      parent_boundary_band_cell_response_L128 M h hM hg n height depth Q hQ hpast
        (fun _ => Real.sqrt t) (fun _ _ => ⟨Real.sqrt_nonneg _,Real.sqrt_le_one.mpr ht⟩)
  exact ⟨hcap.trans_lt ENNReal.ofReal_lt_top,hcap⟩

end
end ASDExplicitGamma.Native
