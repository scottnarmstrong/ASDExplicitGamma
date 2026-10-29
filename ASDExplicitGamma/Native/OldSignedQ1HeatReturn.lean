module

public import ASDExplicitGamma.Native.OldSignedQ1PanelIdentification
public import ASDExplicitGamma.Native.OldSignedQ1ReturnSetup
public import ASDExplicitGamma.Native.OldSignedQ1InversePayment
public import ASDExplicitGamma.Native.BoundaryChargePanelIntegral
public import ASDExplicitGamma.Native.GenericSourceBandInitial
public import ASDExplicitGamma.Numerics.Native.EndpointQ1001

/-! Integration of the actual OLD signed generator with the full inverse term. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Gaussian Main Triadic Cold Scalar Response Variational Algsuperdiff.Section3 Numerics.Native Set
noncomputable section

/-- The actual unframed q1 mean obeys the full signed panel return. -/
theorem old_signed_q1_band_mean_return
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (n : ℤ)
    (hpast : ∀ l ≤ n,nativeInductionState M h l) :
    nativeSourceBandMean M n 1 1 ≤ theta M*((3/50:ℝ)+nativeSetupQ1001B0R+
      (∫ t in (0:ℝ)..1,nativePanelValue nativeSetupQ1001FieldsR t)+nativeSetupQ1001InvcostR) := by
  let b := q3ModelAmplitude M h (n+1)/(Annealed.sigmaBar M n:ℝ)
  let L := q3ModelLength (n+1)
  let B := oldSignedFlatBoundaryEnergy (originCube 2 n) b L
  let P := fun t => theta M*nativePanelValue nativeSetupQ1001FieldsR t
  let I := fun t => -b^2*(parentBoundaryBandInverseMean M n 1 t-2)
  let F := nativeSourceBandMean M n 1
  let dF := fun t => ∫ ω,nativeSourceBandMeanGenerator M h n 1 t ω ∂(Cutoff.cutoffSampleLaw M).toMeasure
  have hheat := native_source_band_mean_heat_generator M h hM n 1 (by norm_num)
  have hinv := parent_boundary_inverse_band_generator_heat M h hM n 1 (by norm_num)
  have hI : IntervalIntegrable I volume 0 1 := by
    apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
    intro t ht
    exact continuousWithinAt_const.mul (((hinv.1 t ht.1).mono (fun _ hx => hx.1)).sub continuousWithinAt_const)
  have hP : IntervalIntegrable P volume 0 1 :=
    (native_boundary_panel_integrable _ nativeSetupQ1001FieldsR_length nativeSetupQ1001Fields_nonneg).const_mul _
  have hB : IntervalIntegrable (fun _ : ℝ => B) volume 0 1 := intervalIntegrable_const
  have hbill : IntervalIntegrable (fun t => B+P t+I t) volume 0 1 := (hB.add hP).add hI
  have hd : ∀ t ∈ Ioo (0:ℝ) 1,dF t ≤ B+P t+I t := by
    intro t ht
    have hg' := old_signed_q1_generator_expectation M h hM hg n hpast t ⟨ht.1.le,ht.2.le⟩
    have hp := old_signed_q1_payment_panel_bound M h hg n (hpast n le_rfl) t ht.1.le
    change dF t ≤ _ at hg'
    dsimp only [B,P,I]
    linarith only [hg',hp]
  have hh := intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le (by norm_num : (0:ℝ) ≤ 1)
    (show ContinuousOn F (Icc 0 1) from hheat.1.mono (fun _ ht => ht.1))
    (fun t ht => (hheat.2 t ht.1).hasDerivWithinAt)
    ((intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)).mp hbill) hd
  have he : (∫ t in (0:ℝ)..1,B+P t+I t)=B+
      theta M*(∫ t in (0:ℝ)..1,nativePanelValue nativeSetupQ1001FieldsR t)+
      (∫ t in (0:ℝ)..1,I t) := by
    rw [intervalIntegral.integral_add (hB.add hP) hI,intervalIntegral.integral_add hB hP]
    simp only [P,intervalIntegral.integral_const,sub_zero,one_smul,intervalIntegral.integral_const_mul]
  rw [he] at hh
  have h0 := native_source_band_mean_zero_le M h n 1 (hpast n le_rfl)
  have hb := old_signed_q1_flat_boundary_payment M h hg n (hpast n le_rfl)
  have hi := old_signed_q1_inverse_payment M h hM hg n hpast
  change B ≤ _ at hb
  change (∫ t in (0:ℝ)..1,I t) ≤ _ at hi
  dsimp only [F] at hh
  linarith only [hh,h0,hb,hi]

/-- The actual completed trace has the certified exact q1 rational cap. -/
theorem old_signed_q1_completed_mean_return
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (n : ℤ)
    (hpast : ∀ l ≤ n,nativeInductionState M h l) :
    (∫ ω,cutoffTraceDefect M (n+1) n ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
      theta M*(nativeEndpointQ1001Cap:ℝ) := by
  have hf : 0 ≤ nativeSetupQ1001FrameR := by
    rw [old_signed_q1_setup_frame]
    positivity
  have hh := (old_signed_q1_completed_frame M n hg).trans
    (mul_le_mul_of_nonneg_left (old_signed_q1_band_mean_return M h hM hg n hpast) hf)
  have hnum := mul_le_mul_of_nonneg_left nativeEndpointQ1001_bound (cold_theta_pos M).le
  apply hh.trans
  convert hnum using 1
  unfold nativePanelEndpoint
  ring

end
end ASDExplicitGamma.Native
