module

public import ASDExplicitGamma.Main.EOscillationDepthFiveProfile
public import ASDExplicitGamma.Main.EOscillationCellHistoryTranslationOfHist
public import ASDExplicitGamma.Main.MultiplierMomentsOfHist

/-! Successors of `EOscillationDepthFiveProfile` declarations with the history envelope as a parameter `Hfun`. -/



@[expose] public section

namespace ASDExplicitGamma.Main

attribute [local irreducible] Homogenization.descendantsAtDepth

open MeasureTheory Homogenization Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Inverse ASDExplicitGamma.Model
open ASDExplicitGamma.Native ASDExplicitGamma.Response ASDExplicitGamma.Scalar
open ASDExplicitGamma.Triadic ASDExplicitGamma.Variational
open Algsuperdiff.Section3.Cutoff

noncomputable section

/-- Successor of `main_eosc_shifted_carrier_product_moment` with the history envelope `Hfun`. -/
theorem main_eosc_shifted_carrier_product_moment_ofHist
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (m : ℤ)
    (hpast : ∀ n ≤ m, nativeInductionState M h n)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (U : TriadicCube 2)
    (Hfun : ℝ → ℝ)
    (hHist : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      (∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
        mainOrdinaryTraceMaxHistory M m (originCube 2 (m - 5)) s ω < ⊤) ∧
      MemLp (fun ω => (mainOrdinaryTraceMaxHistory M m (originCube 2 (m - 5)) s ω).toReal) 2
        (Cutoff.cutoffSampleLaw M).toMeasure ∧
      lpNorm (fun ω => (mainOrdinaryTraceMaxHistory M m (originCube 2 (m - 5)) s ω).toReal) 2
        (Cutoff.cutoffSampleLaw M).toMeasure ≤ Hfun s)
    :
    let μ := (Cutoff.cutoffSampleLaw M).toMeasure
    let shift := fun ω : CutoffSample 2 =>
      Cutoff.translateCutoffSample (triadicCubeShift U) ω
    let B := fun ω =>
      (mainCutoffQ3SourceInverseBankMax M m t (shift ω)).toReal
    let M_U := mainPartialInsertedMultiplierHistory M m t ∘ shift
    (∫ ω, B ω * M_U ω ∂μ) ≤
      mainBeta * mainM0 (Hfun t) := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let shift : CutoffSample 2 → CutoffSample 2 := fun ω =>
    Cutoff.translateCutoffSample (triadicCubeShift U) ω
  let B : CutoffSample 2 → ℝ := fun ω =>
    (mainCutoffQ3SourceInverseBankMax M m t (shift ω)).toReal
  let M_U : CutoffSample 2 → ℝ :=
    mainPartialInsertedMultiplierHistory M m t ∘ shift
  have hShifted := main_eosc_shifted_carrier_moments_ofHist (Hfun := Hfun) (hHist := hHist)
    M h hM hγ m hpast t ht U
  have hBMem : MemLp B 2 μ := by simpa only [B, shift, μ] using hShifted.1
  have hBCap : lpNorm B 2 μ ≤ mainBeta := by
    simpa only [B, shift, μ] using hShifted.2.1
  have hMMem : MemLp M_U 2 μ := by
    simpa only [M_U, shift, μ] using hShifted.2.2.1
  have hMCap : lpNorm M_U 2 μ ≤ mainM0 (Hfun t) := by
    simpa only [M_U, shift, μ] using hShifted.2.2.2
  have hBNonneg : 0 ≤ᵐ[μ] B := by
    filter_upwards with ω
    exact ENNReal.toReal_nonneg
  have hMultiplier := main_multiplier_moments_of_main_envelope_h_ofHist (Hfun := Hfun) (hHist := hHist)
    M h hM hγ m hpast t ht.1 ht.2
  have hMRootNonneg : 0 ≤ᵐ[μ]
      mainPartialInsertedMultiplierHistory M m t := hMultiplier.2
  have hmp : MeasurePreserving shift μ μ := by
    exact ⟨Cutoff.measurable_translateCutoffSample (triadicCubeShift U),
      Cutoff.map_translateCutoffSample_cutoffSampleLaw M (triadicCubeShift U)⟩
  have hMNonneg : 0 ≤ᵐ[μ] M_U := by
    change 0 ≤ᵐ[μ]
      (mainPartialInsertedMultiplierHistory M m t ∘ shift)
    exact hmp.quasiMeasurePreserving.ae hMRootNonneg
  have hB2 : MemLp B (ENNReal.ofReal (2 : ℝ)) μ := by
    simpa only [ENNReal.ofReal_ofNat] using hBMem
  have hM2 : MemLp M_U (ENNReal.ofReal (2 : ℝ)) μ := by
    simpa only [ENNReal.ofReal_ofNat] using hMMem
  have hHolder := integral_mul_le_Lp_mul_Lq_of_nonneg
    (show (2 : ℝ).HolderConjugate 2 by constructor <;> norm_num)
    hBNonneg hMNonneg hB2 hM2
  norm_num only [Real.rpow_ofNat] at hHolder
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at hHolder
  have hNormB : Real.sqrt (∫ ω, B ω ^ 2 ∂μ) = lpNorm B 2 μ := by
    rw [← ASDExplicitGamma.Gaussian.rio_lpNorm_two_sq hBMem]
    exact Real.sqrt_sq (lpNorm_nonneg (f := B) (p := 2) (μ := μ))
  have hNormM : Real.sqrt (∫ ω, M_U ω ^ 2 ∂μ) = lpNorm M_U 2 μ := by
    rw [← ASDExplicitGamma.Gaussian.rio_lpNorm_two_sq hMMem]
    exact Real.sqrt_sq (lpNorm_nonneg (f := M_U) (p := 2) (μ := μ))
  have hBeta : 0 ≤ mainBeta := by norm_num [mainBeta]
  calc
    (∫ ω, B ω * M_U ω ∂μ) ≤
        Real.sqrt (∫ ω, B ω ^ 2 ∂μ) *
          Real.sqrt (∫ ω, M_U ω ^ 2 ∂μ) := hHolder
    _ = lpNorm B 2 μ * lpNorm M_U 2 μ := by rw [hNormB, hNormM]
    _ ≤ mainBeta * mainM0 (Hfun t) :=
      mul_le_mul hBCap hMCap
        (lpNorm_nonneg (f := M_U) (p := 2) (μ := μ)) hBeta

end
end ASDExplicitGamma.Main
end
