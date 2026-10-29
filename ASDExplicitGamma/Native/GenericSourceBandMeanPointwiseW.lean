module

public import ASDExplicitGamma.Native.GenericSourceBandFactorsW
public import ASDExplicitGamma.Native.GenericSourceBandMeanBudget
public import ASDExplicitGamma.Inverse.SourceQ3Drift
public import ASDExplicitGamma.Native.GenericSourceBandPowerHeatW

public import ASDExplicitGamma.Native.NativeBandWeight

/-! Actual mean generator summation before Holder and time integration. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Algsuperdiff.Section3 ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Inverse ASDExplicitGamma.Triadic ASDExplicitGamma.Variational ASDExplicitGamma.Response
open scoped ENNReal
noncomputable section

variable {W : NativeAmp}

/-- The actual complete mean source generator at simultaneous band time `t`. -/
def nativeSourceBandMeanGenerator_W (W : NativeAmp) (M : ABKModel 2) (h : ℝ) (n : ℤ)
    (height : ℕ) (t : ℝ) (ω : Cutoff.CutoffSample 2) : ℝ :=
  ∑ i : Fin height, (1/2:ℝ)*((nativeSourceBandCoef_W W n height i)^2 *
    modelCovarianceTrace (modelTraceObservable n M.nu (Annealed.sigmaBar M n))
    (pureFluxMainCubeQ3Directions n (q3ModelAmplitude M h (n+((i.val+1:ℕ):ℤ)))
      (q3ModelLength (n+((i.val+1:ℕ):ℤ)))) (nativeSourceBandScalar_W W n height t ω))

/-- All shell generator terms sum to the exact sharp mean source coefficient
with the same actual D, P*F and P²*F factors. -/
theorem native_source_band_mean_generator_ae_le_W
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (n : ℤ) (height : ℕ)
    (hpast : ∀ j < n, nativeInductionState M h j) (hstate : nativeInductionState M h n)
    (t : ℝ) (ht1 : t ≤ 1) :
    ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      let X := nativeSourceBandScalar_W W n height t ω
      let T := modelTraceObservable n M.nu (Annealed.sigmaBar M n) X
      let F := T+4
      let P := (nativeSourceBandHistory_W W M n height t ω).toReal
      let D := bankInverseTraceObservable n M.nu (Annealed.sigmaBar M n) M.nu_pos
        (Annealed.sigmaBar_characterization M n).1 X
      nativeSourceBandMeanGenerator_W W M h n height t ω ≤
        nativeSourceRawShellVarianceCap M.gamma height*
          ((height:ℝ)*D+2*(521/1000:ℝ)*(P*F)+(1975/1000:ℝ)*(P^2*F)) := by
  have hall : ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure, ∀ i : Fin height,
      let Q := originCube 2 n
      let af := responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M n:ℝ)
        (pureFluxOpenResponseRestriction n (nativeSourceBandScalar_W W n height t ω))
      max (lemmaVTileHistory Q (pureFluxBankSourceDepth (i.val+1)) af)
        (pureFluxSourceTileHistory Q (pureFluxBankSourceDepth (i.val+1)) af) ≤
        (nativeSourceBandHistory_W W M n height t ω).toReal :=
    ae_all_iff.mpr fun i => native_source_band_source_history_ae_le_W M h hM hg n height hpast i.val t ht1
  filter_upwards [hall] with ω hsource
  let X := nativeSourceBandScalar_W W n height t ω
  let σ : ℝ := Annealed.sigmaBar M n
  let T := modelTraceObservable n M.nu σ X
  let F := T+4
  let P := (nativeSourceBandHistory_W W M n height t ω).toReal
  let D := bankInverseTraceObservable n M.nu σ M.nu_pos (Annealed.sigmaBar_characterization M n).1 X
  let v := fun i : ℕ => (q3ModelAmplitude M h (n+((i+1:ℕ):ℤ)))^2/σ^2
  let c := fun i : ℕ => v i*D+2*v i*nativeSourceShellK i*(P*F)+v i*nativeSourceShellMu i*(P^2*F)
  have hT : 0 ≤ T := modelTraceObservable_nonneg n M.nu σ M.nu_pos
    (Annealed.sigmaBar_characterization M n).1 X
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hP : 0 ≤ P := ENNReal.toReal_nonneg
  have hD : 0 ≤ D := native_source_model_inverse_trace_nonneg n M.nu σ M.nu_pos
    (Annealed.sigmaBar_characterization M n).1 X
  have hrow0 (i : Fin height) : (1/2:ℝ)*modelCovarianceTrace (modelTraceObservable n M.nu σ)
      (pureFluxMainCubeQ3Directions n (q3ModelAmplitude M h (n+((i.val+1:ℕ):ℤ)))
        (q3ModelLength (n+((i.val+1:ℕ):ℤ)))) X ≤ c i.val := by
    let af := responseFramePlanarCoefficientField M.nu σ (pureFluxOpenResponseRestriction n X)
    let B := max (lemmaVTileHistory (originCube 2 n) (pureFluxBankSourceDepth (i.val+1)) af)
      (pureFluxSourceTileHistory (originCube 2 n) (pureFluxBankSourceDepth (i.val+1)) af)
    have hB : B ≤ P := hsource i
    have hB0 : 0 ≤ B := le_max_of_le_left
      (lemmaVTileHistory_nonneg (originCube 2 n) (pureFluxBankSourceDepth (i.val+1)) af)
    have hB2 := pow_le_pow_left₀ hB0 hB 2
    have hc := native_source_shell_coefficients_nonneg i.val
    have hK := hc.1; have hμ := hc.2.2
    have hv : 0 ≤ v i.val := by dsimp [v]; positivity
    have hr := source_model_q3_positive_generator_row n (i.val+1) (by omega)
      M.nu σ (q3ModelAmplitude M h (n+((i.val+1:ℕ):ℤ))) M.nu_pos
      (Annealed.sigmaBar_characterization M n).1 X
    have hr' : (1/2:ℝ)*modelCovarianceTrace (modelTraceObservable n M.nu σ)
        (pureFluxMainCubeQ3Directions n (q3ModelAmplitude M h (n+((i.val+1:ℕ):ℤ)))
          (q3ModelLength (n+((i.val+1:ℕ):ℤ)))) X ≤
        v i.val*D+(2*v i.val*nativeSourceShellK i.val*B+v i.val*nativeSourceShellMu i.val*B^2)*F := by
      simpa only [pureFlux_bank_source_rho n (i.val+1) (by omega),
        pureFlux_bank_source_delta n (i.val+1) (by omega),source_lemmaV_B_eq_covariance_B,
        Nat.add_sub_cancel,←native_source_model_inverse_trace_eq_frame_trace n M.nu σ M.nu_pos
          (Annealed.sigmaBar_characterization M n).1 X,
        T,F,D,v,B,af,nativeSourceShellK,nativeSourceShellQ,nativeSourceShellMu] using hr
    have h1 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hB
      (show 0 ≤ 2*v i.val*nativeSourceShellK i.val by positivity)) hF
    have h2 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hB2
      (show 0 ≤ v i.val*nativeSourceShellMu i.val by positivity)) hF
    have hcost : v i.val*D+(2*v i.val*nativeSourceShellK i.val*B+
        v i.val*nativeSourceShellMu i.val*B^2)*F ≤ c i.val := by
      dsimp [c]
      linarith only [h1,h2]
    exact hr'.trans hcost
  have hrow (i : Fin height) : (1/2:ℝ)*((nativeSourceBandCoef_W W n height i)^2 *
      modelCovarianceTrace (modelTraceObservable n M.nu σ)
      (pureFluxMainCubeQ3Directions n (q3ModelAmplitude M h (n+((i.val+1:ℕ):ℤ)))
        (q3ModelLength (n+((i.val+1:ℕ):ℤ)))) X) ≤ c i.val := by
    have hc := native_source_shell_coefficients_nonneg i.val
    have hK := hc.1; have hμ := hc.2.2
    have hv : 0 ≤ v i.val := by dsimp [v]; positivity
    have hci : 0 ≤ c i.val := by dsimp [c]; positivity
    have h2 := nativeWeightedRow_le (W.sq_le_one (nativeSourceBandIndex n height i)) hci (hrow0 i)
    have e : (1/2:ℝ)*((nativeSourceBandCoef_W W n height i)^2 *
      modelCovarianceTrace (modelTraceObservable n M.nu σ)
      (pureFluxMainCubeQ3Directions n (q3ModelAmplitude M h (n+((i.val+1:ℕ):ℤ)))
        (q3ModelLength (n+((i.val+1:ℕ):ℤ)))) X) =
      (W.w (nativeSourceBandIndex n height i))^2 * ((1/2:ℝ)*modelCovarianceTrace (modelTraceObservable n M.nu σ)
      (pureFluxMainCubeQ3Directions n (q3ModelAmplitude M h (n+((i.val+1:ℕ):ℤ)))
        (q3ModelLength (n+((i.val+1:ℕ):ℤ)))) X) := by
      simp only [nativeSourceBandCoef_W]; ring
    rw [e]; exact h2
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hrow i)
  have hbudget := native_source_band_mean_coefficient_budget M h n height hstate D (P*F) (P^2*F) hD
    (mul_nonneg hP hF) (mul_nonneg (sq_nonneg P) hF)
  have hc : (∑ i : Fin height, c i.val) ≤ nativeSourceRawShellVarianceCap M.gamma height*
      ((height:ℝ)*D+2*(521/1000:ℝ)*(P*F)+(1975/1000:ℝ)*(P^2*F)) := by
    rw [Fin.sum_univ_eq_sum_range]
    exact hbudget
  exact hsum.trans hc

end
end ASDExplicitGamma.Native
