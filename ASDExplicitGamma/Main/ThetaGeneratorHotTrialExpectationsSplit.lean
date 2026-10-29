module

public import ASDExplicitGamma.Main.ThetaGeneratorHotTrialExpectationsDrop
public import ASDExplicitGamma.Main.ThetaGeneratorEnvelopeA
public import ASDExplicitGamma.Main.LoadsAndSlopes
public import ASDExplicitGamma.Main.SourcePrefixGates
public import ASDExplicitGamma.Native.SourceRowsInterface
public import ASDExplicitGamma.Inverse.SourceInterfaceRows
public import ASDExplicitGamma.Scalar.MixedSourceCarriers
public import ASDExplicitGamma.Inverse.MixedBridgeConclusion
public import ASDExplicitGamma.Inverse.MixedBridgeLocalTheta
public import ASDExplicitGamma.Inverse.MixedBridgeLocalWeightedTheta
public import ASDExplicitGamma.Inverse.MixedBridgeSharpSlope
public import ASDExplicitGamma.Numerics.Native.Source5
public import ASDExplicitGamma.Main.EnvelopeHTransport
public import ASDExplicitGamma.Inverse.BridgeGlobalBank
public import ASDExplicitGamma.Native.OldSignedRarePowerPayment

/-! Package D, part two: the `L²` size of the hot-trial energy drop and the
positive splits `E[B* Delta]`, `E[B*^2 Delta]` on the actual cutoff law. -/

@[expose] public section

namespace ASDExplicitGamma.Main

attribute [local irreducible] Homogenization.descendantsAtDepth

open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Inverse ASDExplicitGamma.Model
open ASDExplicitGamma.Native ASDExplicitGamma.Scalar ASDExplicitGamma.Triadic
open ASDExplicitGamma.Variational ASDExplicitGamma.Response
open scoped ENNReal

noncomputable section

theorem main_hot_lpNorm_smul_nonneg_Th {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {c : ℝ} (hc : 0 ≤ c) (f : Ω → ℝ) (p : ℝ≥0∞) :
    lpNorm (c • f) p μ = c * lpNorm f p μ := by
  rw [lpNorm_const_smul, coe_nnnorm, Real.norm_of_nonneg hc]

/-- The history dominates the zeroth term: `(1 - alpha) T_Q <= Hbar_Q`. -/
theorem main_hot_cell_trace_le_history_Th
    (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2) (t : ℝ)
    (ω : Cutoff.CutoffSample 2)
    (hfin : mainOrdinaryTraceMaxHistory M m Q t ω < ⊤) :
    (1 - mainAlpha) * rawCubeFourLoadTrace M m Q t ω ≤
      (mainOrdinaryTraceMaxHistory M m Q t ω).toReal := by
  have hα := Scalar.inverse_history_discount_range
  have h1 : 0 ≤ 1 - mainAlpha := by
    have : mainAlpha = Scalar.inverseHistoryDiscount := rfl
    linarith [hα.2]
  rw [← ENNReal.ofReal_le_iff_le_toReal hfin.ne, ENNReal.ofReal_mul h1]
  unfold mainOrdinaryTraceMaxHistory
  refine mul_le_mul_right ?_ _
  have hzero : ENNReal.ofReal (rawCubeFourLoadTrace M m Q t ω) ≤
      mainOrdinaryTraceDepthMax M m Q t 0 ω := by
    unfold mainOrdinaryTraceDepthMax historyFiniteMax
    exact Finset.le_sup (f := fun V =>
      ENNReal.ofReal (rawCubeFourLoadTrace M m V t ω))
      (by simp only [descendantsAtDepth_zero, Finset.mem_singleton])
  calc
    ENNReal.ofReal (rawCubeFourLoadTrace M m Q t ω) =
        ENNReal.ofReal (mainAlpha ^ 0) *
          ENNReal.ofReal (rawCubeFourLoadTrace M m Q t ω) := by simp
    _ ≤ ENNReal.ofReal (mainAlpha ^ 0) *
          mainOrdinaryTraceDepthMax M m Q t 0 ω := mul_le_mul_right hzero _
    _ ≤ ∑' j : ℕ, ENNReal.ofReal (mainAlpha ^ j) *
          mainOrdinaryTraceDepthMax M m Q t j ω :=
      ENNReal.le_tsum (f := fun j : ℕ => ENNReal.ofReal (mainAlpha ^ j) *
          mainOrdinaryTraceDepthMax M m Q t j ω) 0

/-- The `L²` size of the actual trace on the origin depth-five cell, through
the max-based history envelope: `||T|| <= H / (1 - alpha)`. -/
theorem main_hot_origin_trace_l2_Th
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (m : ℤ)
    (hpast : ∀ n ≤ m, nativeInductionState M h n)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    let μ := (Cutoff.cutoffSampleLaw M).toMeasure
    MemLp (rawCubeFourLoadTrace M m (originCube 2 (m - 5)) t) 2 μ ∧
      lpNorm (rawCubeFourLoadTrace M m (originCube 2 (m - 5)) t) 2 μ ≤
        mainEnvelopeH (theta M) M.gamma t / (1 - mainAlpha) := by
  intro μ
  obtain ⟨hfin, hmem, hnorm⟩ :=
    main_ordinary_trace_max_history_memLp_two_le_mainEnvelopeH
      M h hM hγ m hpast t ht.1 ht.2
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
    (main_hot_raw_cube_measurable_Th M m Q0 t).aestronglyMeasurable
  have hbound : ∀ᵐ ω ∂μ, ‖T ω‖ ≤ g ω := by
    filter_upwards [hfin] with ω hω
    have hT0 : 0 ≤ T ω := raw_cube_four_load_trace_nonneg M m Q0 t ⟨ht.1, ht.2⟩ ω
    rw [Real.norm_of_nonneg hT0]
    have := main_hot_cell_trace_le_history_Th M m Q0 t ω hω
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
      exact main_hot_lpNorm_smul_nonneg_Th (inv_nonneg.mpr h1.le) Hr 2
    _ ≤ (1 - mainAlpha)⁻¹ * mainEnvelopeH (theta M) M.gamma t :=
      mul_le_mul_of_nonneg_left hnorm (inv_nonneg.mpr h1.le)
    _ = _ := by rw [inv_mul_eq_div, div_eq_mul_inv, mul_comm]

/-- The bridge carrier `mixedGlobalHistoryMax` is the common complete
inverse maximum `mixedBridgeBstar`. -/
theorem main_hot_bstar_eq_Th
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (ω : Cutoff.CutoffSample 2) :
    mixedGlobalHistoryMax M m t ω = mixedBridgeBstar M m t ω := by
  dsimp [mixedGlobalHistoryMax, mixedObserverRoots, mixedBridgeBstar]
  rw [← mixed_bridge_observer_roots_eq_bank_union m,
    ← mixed_bridge_bstar_eq_bank_finite_history M m t ht ω]
  exact ENNReal.toReal_ofReal (mixed_bridge_bstar_nonneg M m t ω)

end

end ASDExplicitGamma.Main
