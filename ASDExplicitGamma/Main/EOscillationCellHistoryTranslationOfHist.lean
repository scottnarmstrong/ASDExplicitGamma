module

public import ASDExplicitGamma.Main.EOscillationCellHistoryTranslation
public import ASDExplicitGamma.Main.MultiplierMomentsOfHist

/-! Successors of `EOscillationCellHistoryTranslation` declarations with the history envelope as a parameter `Hfun`. -/



@[expose] public section

namespace ASDExplicitGamma.Main

attribute [local irreducible] Homogenization.descendantsAtDepth

open Homogenization MeasureTheory ASDExplicitGamma.Gaussian ASDExplicitGamma.Model
  ASDExplicitGamma.Native ASDExplicitGamma.Response ASDExplicitGamma.Scalar
  ASDExplicitGamma.Triadic ASDExplicitGamma.Variational
open Algsuperdiff.Section3 Algsuperdiff.Section3.Cutoff
open scoped ENNReal

noncomputable section

/-- Successor of `main_eosc_shifted_carrier_moments` with the history envelope `Hfun`. -/
theorem main_eosc_shifted_carrier_moments_ofHist
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
    MemLp B 2 μ ∧ lpNorm B 2 μ ≤ mainBeta ∧
      MemLp M_U 2 μ ∧
        lpNorm M_U 2 μ ≤ mainM0 (Hfun t) := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let shift : CutoffSample 2 → CutoffSample 2 := fun ω =>
    Cutoff.translateCutoffSample (triadicCubeShift U) ω
  let rootB : CutoffSample 2 → ℝ := fun ω =>
    (mainCutoffQ3SourceInverseBankMax M m t ω).toReal
  let B : CutoffSample 2 → ℝ := fun ω => rootB (shift ω)
  let rootM : CutoffSample 2 → ℝ := mainPartialInsertedMultiplierHistory M m t
  let M_U : CutoffSample 2 → ℝ := rootM ∘ shift
  have hmp : MeasurePreserving shift μ μ := by
    exact ⟨Cutoff.measurable_translateCutoffSample (triadicCubeShift U),
      Cutoff.map_translateCutoffSample_cutoffSampleLaw M (triadicCubeShift U)⟩
  have hBank := main_q3_source_inverse_bank_and_history M h hM hγ m
    (fun n hn => hpast n hn.le) t ht
  have hBrootMem : MemLp rootB 2 μ := by
    simpa only [rootB] using hBank.2.1
  have hBmem : MemLp B 2 μ := by
    change MemLp (rootB ∘ shift) 2 μ
    exact hBrootMem.comp_measurePreserving hmp
  have hBnorm : lpNorm B 2 μ = lpNorm rootB 2 μ := by
    change (eLpNorm (rootB ∘ shift) 2 μ).toReal =
      (eLpNorm rootB 2 μ).toReal
    rw [eLpNorm_comp_measurePreserving hBrootMem.aestronglyMeasurable hmp]
  have hBcap : lpNorm B 2 μ ≤ mainBeta := by
    rw [hBnorm]
    simpa only [rootB] using hBank.2.2.1
  have hMultiplier := main_multiplier_moments_of_main_envelope_h_ofHist (Hfun := Hfun) (hHist := hHist)
    M h hM hγ m hpast t ht.1 ht.2
  have hMrootMem : MemLp rootM 2 μ := by
    simpa only [rootM] using hMultiplier.1.2
  have hMmem : MemLp M_U 2 μ := by
    change MemLp (rootM ∘ shift) 2 μ
    exact hMrootMem.comp_measurePreserving hmp
  have hMnorm : lpNorm M_U 2 μ = lpNorm rootM 2 μ := by
    change (eLpNorm (rootM ∘ shift) 2 μ).toReal =
      (eLpNorm rootM 2 μ).toReal
    rw [eLpNorm_comp_measurePreserving hMrootMem.aestronglyMeasurable hmp]
  have hMcap : lpNorm M_U 2 μ ≤ mainM0 (Hfun t) := by
    rw [hMnorm]
    simpa only [rootM] using hMultiplier.1.1.2
  exact ⟨by simpa only [B] using hBmem,
    by simpa only [B] using hBcap,
    by simpa only [M_U, rootM, shift, μ] using hMmem,
    by simpa only [M_U, rootM, shift, μ] using hMcap⟩

end
end ASDExplicitGamma.Main
end
