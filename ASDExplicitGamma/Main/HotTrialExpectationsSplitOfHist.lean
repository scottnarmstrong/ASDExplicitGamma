module

public import ASDExplicitGamma.Main.HotTrialExpectationsSplit

/-! Successors of `HotTrialExpectationsSplit` declarations with the history envelope as a parameter `Hfun`. -/



@[expose] public section

namespace ASDExplicitGamma.Main

attribute [local irreducible] Homogenization.descendantsAtDepth

open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Inverse ASDExplicitGamma.Model
open ASDExplicitGamma.Native ASDExplicitGamma.Scalar ASDExplicitGamma.Triadic
open ASDExplicitGamma.Variational ASDExplicitGamma.Response
open scoped ENNReal

noncomputable section

/-- Successor of `main_hot_origin_trace_l2` with the history envelope `Hfun`. -/
theorem main_hot_origin_trace_l2_ofHist
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (m : ℤ)
    (hpast : ∀ n ≤ m, nativeInductionState M h n)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
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
    MemLp (rawCubeFourLoadTrace M m (originCube 2 (m - 5)) t) 2 μ ∧
      lpNorm (rawCubeFourLoadTrace M m (originCube 2 (m - 5)) t) 2 μ ≤
        Hfun t / (1 - mainAlpha) := by
  intro μ
  obtain ⟨hfin, hmem, hnorm⟩ :=
    hHist t ⟨ht.1, ht.2⟩
  have hα := Scalar.inverse_history_discount_range
  have h1 : 0 < 1 - mainAlpha := by
    have : mainAlpha = Scalar.inverseHistoryDiscount := rfl
    linarith [hα.2]
  let Q0 := originCube 2 (m - 5)
  let T := rawCubeFourLoadTrace M m Q0 t
  let Hr : Cutoff.CutoffSample 2 → ℝ :=
    fun ω => (mainOrdinaryTraceMaxHistory M m Q0 t ω).toReal
  let g : Cutoff.CutoffSample 2 → ℝ := (1 - mainAlpha)⁻¹ • Hr
  have hgmem : MemLp g 2 μ := by
    have := hmem.const_mul (1 - mainAlpha)⁻¹
    exact this
  have hTmeas : AEStronglyMeasurable T μ :=
    (main_hot_raw_cube_measurable M m Q0 t).aestronglyMeasurable
  have hbound : ∀ᵐ ω ∂μ, ‖T ω‖ ≤ g ω := by
    filter_upwards [hfin] with ω hω
    have hT0 : 0 ≤ T ω := raw_cube_four_load_trace_nonneg M m Q0 t ⟨ht.1, ht.2⟩ ω
    rw [Real.norm_of_nonneg hT0]
    have := main_hot_cell_trace_le_history M m Q0 t ω hω
    simp only [g, Pi.smul_apply, smul_eq_mul]
    rw [inv_mul_eq_div, le_div_iff₀ h1]
    linarith
  refine ⟨hgmem.mono' hTmeas hbound, ?_⟩
  have hle : eLpNorm T 2 μ ≤ eLpNorm g 2 μ := eLpNorm_mono_ae_real hTmeas hbound
  have hTm : MemLp T 2 μ := hgmem.mono' hTmeas hbound
  change (eLpNorm T 2 μ).toReal ≤ _
  calc
    (eLpNorm T 2 μ).toReal ≤ (eLpNorm g 2 μ).toReal :=
      ENNReal.toReal_mono hgmem.eLpNorm_ne_top hle
    _ = lpNorm g 2 μ := rfl
    _ = (1 - mainAlpha)⁻¹ * lpNorm Hr 2 μ := by
      exact main_hot_lpNorm_smul_nonneg (inv_nonneg.mpr h1.le) Hr 2
    _ ≤ (1 - mainAlpha)⁻¹ * Hfun t :=
      mul_le_mul_of_nonneg_left hnorm (inv_nonneg.mpr h1.le)
    _ = _ := by rw [inv_mul_eq_div, div_eq_mul_inv, mul_comm]

end
end ASDExplicitGamma.Main
end
