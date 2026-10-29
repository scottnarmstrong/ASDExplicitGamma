module

public import ASDExplicitGamma.Native.OldSignedPanelHistoryComparison
public import ASDExplicitGamma.Native.OldSignedCellHistoryTransport
public import ASDExplicitGamma.Numerics.Native.SetupQ1001Proof

/-! Actual cell histories fit the certified OLD q1 panel's history envelope. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Gaussian Scalar Inverse Cold Algsuperdiff.Section3
open Numerics Numerics.Native
open scoped ENNReal
noncomputable section


/-- The literal history envelope in the q1 panel, with its certified setup fields. -/
def oldSignedQ1PanelHistory (t : ℝ) : ℝ :=
  (Real.sqrt (nativeSetupQ1001FieldsR.getD 13 0 +
      nativeSetupQ1001FieldsR.getD 10 0*t)+
    Real.sqrt (2*nativeSetupQ1001FieldsR.getD 0 0*t)*
      ((3:ℝ)^(1/4:ℝ)*Real.sqrt (3683/2500:ℝ)+
        (105:ℝ)^(1/8:ℝ)*Real.sqrt (3/10^46:ℝ)))^2

/-- Exact rational interval gates used to compare the auxiliary history. -/
theorem old_signed_q1_history_setup_lower :
    (2279/1000:ℝ) ≤ nativeSetupQ1001FieldsR.getD 13 0 ∧
    (17/125:ℝ) ≤ nativeSetupQ1001FieldsR.getD 10 0 ∧
    (153/100000:ℝ) ≤ nativeSetupQ1001FieldsR.getD 0 0 := by
  have h0 := (nativeSetupQ1001Fields_sound 13).1
  have hd := (nativeSetupQ1001Fields_sound 10).1
  have hv := (nativeSetupQ1001Fields_sound 0).1
  have h0q : (2279/1000:ℚ) ≤ (nativeSetupQ1001FieldsI.getD 13 nativeZeroInterval).lo := by
    decide +kernel
  have hdq : (17/125:ℚ) ≤ (nativeSetupQ1001FieldsI.getD 10 nativeZeroInterval).lo := by
    decide +kernel
  have hvq : (153/100000:ℚ) ≤ (nativeSetupQ1001FieldsI.getD 0 nativeZeroInterval).lo := by
    decide +kernel
  refine ⟨le_trans ?_ h0, le_trans ?_ hd, le_trans ?_ hv⟩
  · simpa only [Rat.cast_div, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr h0q
  · simpa only [Rat.cast_div, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr hdq
  · simpa only [Rat.cast_div, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr hvq

/-- The full64 auxiliary envelope stays below the unchanged source envelope. -/
theorem old_signed_affine_le_q1_panel_history (t : ℝ) (ht : 0≤t ∧ t≤1) :
    (217/100:ℝ)+(49/100)*t ≤ oldSignedQ1PanelHistory t :=
  old_signed_affine_le_history_profile _ _ _ _ t
    old_signed_q1_history_setup_lower.1 old_signed_q1_history_setup_lower.2.1
    old_signed_q1_history_setup_lower.2.2 old_signed_panel_history_multiplier ht.1 ht.2

private theorem old_signed_cell_scale (n : ℤ) (r : ℕ) (U : TriadicCube 2)
    (hU : U ∈ descendantsAtDepth (originCube 2 n) r) : U.scale = n-(r:ℤ) := by
  exact scale_eq_sub_of_mem_descendantsAtDepth hU

/-- Actual max-based history on every mesh-five cell, with the exact panel
profile and only the model and earlier native states as hypotheses. -/
theorem old_signed_cell_q1_panel_history
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (n : ℤ)
    (hpast : ∀ l ≤ n,nativeInductionState M h l)
    (r : ℕ) (hr : r=5)
    (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth (originCube 2 n) r)
    (t : ℝ) (ht : 0≤t ∧ t≤1) :
    (∀ ω, Main.mainOrdinaryTraceMaxHistory M n U t ω < ⊤) ∧
    MemLp (fun ω => oldSignedMaxTraceHistory U (oldSignedPartialFrameField M n 1 t ω))
      2 (Cutoff.cutoffSampleLaw M).toMeasure ∧
    lpNorm (fun ω => oldSignedMaxTraceHistory U (oldSignedPartialFrameField M n 1 t ω))
      2 (Cutoff.cutoffSampleLaw M).toMeasure ≤ theta M*oldSignedQ1PanelHistory t := by
  have hscale := old_signed_cell_scale n r U hU
  rw [hr] at hscale
  have hcap := old_signed_cell_full64_max_history_transport M h hM hg n hpast U hscale t ht
  have hθ := (cold_theta_pos M).le
  have hfinal : eLpNorm (Main.mainOrdinaryTraceMaxHistory M n U t) 20
      (Cutoff.cutoffSampleLaw M).toMeasure ≤ ENNReal.ofReal (theta M*oldSignedQ1PanelHistory t) := by
    apply hcap.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ hθ))
    exact (add_le_add old_signed_initial_history_rational le_rfl).trans
      (old_signed_affine_le_q1_panel_history t ht)
  exact ⟨old_signed_actual_max_trace_history_finite M n r U hU t,
    old_signed_actual_max_history_L2_of_L20 M n r U hU t _
      (mul_nonneg hθ (sq_nonneg _)) hfinal⟩

end
end ASDExplicitGamma.Native
