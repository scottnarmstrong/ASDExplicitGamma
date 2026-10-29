module

public import ASDExplicitGamma.Native.GenericSourceBandFactors
public import ASDExplicitGamma.Native.GenericSourceBandCoefficientBudget
public import ASDExplicitGamma.Native.GenericSourceBandPowerHeat

/-! Actual p20 generator summation before Holder and time integration. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Algsuperdiff.Section3 ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Inverse ASDExplicitGamma.Triadic ASDExplicitGamma.Variational ASDExplicitGamma.Response
open scoped ENNReal
noncomputable section

/-- The actual complete p20 source generator at simultaneous band time `t`. -/
def nativeSourceBandPowerGenerator (M : ABKModel 2) (h : ℝ) (n : ℤ)
    (height : ℕ) (t : ℝ) (ω : Cutoff.CutoffSample 2) : ℝ :=
  ∑ i : Fin height, modelPowerHeatGenerator (modelTraceObservable n M.nu (Annealed.sigmaBar M n))
    (pureFluxMainCubeQ3Directions n (q3ModelAmplitude M h (n+((i.val+1:ℕ):ℤ)))
      (q3ModelLength (n+((i.val+1:ℕ):ℤ)))) 20 (nativeSourceBandScalar n height t ω)

/-- All shell generator terms sum to the exact sharp p20 source coefficient
with the same actual D, P*F and P²*F factors. -/
theorem native_source_band_power_generator_ae_le
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (n : ℤ) (height : ℕ)
    (hpast : ∀ j < n, nativeInductionState M h j) (hstate : nativeInductionState M h n)
    (t : ℝ) (ht1 : t ≤ 1) :
    ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      let X := nativeSourceBandScalar n height t ω
      let T := modelTraceObservable n M.nu (Annealed.sigmaBar M n) X
      let F := T+4
      let P := (nativeSourceBandHistory M n height t ω).toReal
      let D := bankInverseTraceObservable n M.nu (Annealed.sigmaBar M n) M.nu_pos
        (Annealed.sigmaBar_characterization M n).1 X
      nativeSourceBandPowerGenerator M h n height t ω ≤
        20*T^(19:ℝ)*(nativeSourceRawShellVarianceCap M.gamma height*
          ((39*(height:ℝ)+38*(521/1000:ℝ))*D+2*(521/1000:ℝ)*(P*F)+
            ((1975/1000:ℝ)+38*(1565/1000:ℝ))*(P^2*F))) := by
  have hall : ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure, ∀ i : Fin height,
      let Q := originCube 2 n
      let af := responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M n:ℝ)
        (pureFluxOpenResponseRestriction n (nativeSourceBandScalar n height t ω))
      max (lemmaVTileHistory Q (pureFluxBankSourceDepth (i.val+1)) af)
        (pureFluxSourceTileHistory Q (pureFluxBankSourceDepth (i.val+1)) af) ≤
        (nativeSourceBandHistory M n height t ω).toReal :=
    ae_all_iff.mpr fun i => native_source_band_source_history_ae_le M h hM hg n height hpast i.val t ht1
  filter_upwards [hall] with ω hsource
  let X := nativeSourceBandScalar n height t ω
  let σ : ℝ := Annealed.sigmaBar M n
  let T := modelTraceObservable n M.nu σ X
  let F := T+4
  let P := (nativeSourceBandHistory M n height t ω).toReal
  let D := bankInverseTraceObservable n M.nu σ M.nu_pos (Annealed.sigmaBar_characterization M n).1 X
  let v := fun i : ℕ => (q3ModelAmplitude M h (n+((i+1:ℕ):ℤ)))^2/σ^2
  let c := fun i : ℕ => v i*(39+38*nativeSourceShellK i)*D+
    2*v i*nativeSourceShellK i*(P*F)+(v i*(nativeSourceShellMu i+38*nativeSourceShellQ i))*(P^2*F)
  have hT : 0 ≤ T := modelTraceObservable_nonneg n M.nu σ M.nu_pos
    (Annealed.sigmaBar_characterization M n).1 X
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hP : 0 ≤ P := ENNReal.toReal_nonneg
  have hD : 0 ≤ D := native_source_model_inverse_trace_nonneg n M.nu σ M.nu_pos
    (Annealed.sigmaBar_characterization M n).1 X
  have hscale : 0 ≤ 20*T^(19:ℝ) := by positivity
  have hrow (i : Fin height) : modelPowerHeatGenerator (modelTraceObservable n M.nu σ)
      (pureFluxMainCubeQ3Directions n (q3ModelAmplitude M h (n+((i.val+1:ℕ):ℤ)))
        (q3ModelLength (n+((i.val+1:ℕ):ℤ)))) 20 X ≤ 20*T^(19:ℝ)*c i.val := by
    let af := responseFramePlanarCoefficientField M.nu σ (pureFluxOpenResponseRestriction n X)
    let B := max (lemmaVTileHistory (originCube 2 n) (pureFluxBankSourceDepth (i.val+1)) af)
      (pureFluxSourceTileHistory (originCube 2 n) (pureFluxBankSourceDepth (i.val+1)) af)
    have hB : B ≤ P := hsource i
    have hB0 : 0 ≤ B := le_max_of_le_left
      (lemmaVTileHistory_nonneg (originCube 2 n) (pureFluxBankSourceDepth (i.val+1)) af)
    have hB2 := pow_le_pow_left₀ hB0 hB 2
    have hc := native_source_shell_coefficients_nonneg i.val
    have hK := hc.1; have hQ := hc.2.1; have hμ := hc.2.2
    have hv : 0 ≤ v i.val := by dsimp [v]; positivity
    have hr := raw_trace_model_q3_p20_power_generator_row_tight n (i.val+1) (by omega)
      M.nu σ (q3ModelAmplitude M h (n+((i.val+1:ℕ):ℤ))) M.nu_pos
      (Annealed.sigmaBar_characterization M n).1 X
    have hr' : modelPowerHeatGenerator (modelTraceObservable n M.nu σ)
        (pureFluxMainCubeQ3Directions n (q3ModelAmplitude M h (n+((i.val+1:ℕ):ℤ)))
          (q3ModelLength (n+((i.val+1:ℕ):ℤ)))) 20 X ≤
        20*T^(19:ℝ)*(v i.val*(39+38*nativeSourceShellK i.val)*D+
          2*v i.val*nativeSourceShellK i.val*B*F+
          v i.val*(nativeSourceShellMu i.val+38*nativeSourceShellQ i.val)*B^2*F) := by
      simpa only [pureFlux_bank_source_rho n (i.val+1) (by omega),
        pureFlux_bank_source_delta n (i.val+1) (by omega),source_lemmaV_B_eq_covariance_B,
        Nat.add_sub_cancel,←native_source_model_inverse_trace_eq_frame_trace n M.nu σ M.nu_pos
          (Annealed.sigmaBar_characterization M n).1 X,
        T,F,D,v,B,af,nativeSourceShellK,nativeSourceShellQ,nativeSourceShellMu] using hr
    have h1 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hB
      (show 0 ≤ 2*v i.val*nativeSourceShellK i.val by positivity)) hF
    have h2 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hB2
      (show 0 ≤ v i.val*(nativeSourceShellMu i.val+38*nativeSourceShellQ i.val) by positivity)) hF
    have hcost : v i.val*(39+38*nativeSourceShellK i.val)*D+
        2*v i.val*nativeSourceShellK i.val*B*F+
        v i.val*(nativeSourceShellMu i.val+38*nativeSourceShellQ i.val)*B^2*F ≤ c i.val := by
      dsimp [c]
      linarith only [h1,h2]
    exact hr'.trans (mul_le_mul_of_nonneg_left hcost hscale)
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hrow i)
  rw [←Finset.mul_sum] at hsum
  have hbudget := native_source_band_coefficient_budget M h n height hstate P D F F hP hD hF hF
  have hc : (∑ i : Fin height, c i.val) ≤ nativeSourceRawShellVarianceCap M.gamma height*
      ((39*(height:ℝ)+38*(521/1000:ℝ))*D+2*(521/1000:ℝ)*(P*F)+
        ((1975/1000:ℝ)+38*(1565/1000:ℝ))*(P^2*F)) := by
    rw [Fin.sum_univ_eq_sum_range]
    convert hbudget using 1
    ring
  exact hsum.trans (mul_le_mul_of_nonneg_left hc hscale)

end
end ASDExplicitGamma.Native
