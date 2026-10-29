module

public import ASDExplicitGamma.Native.GenericSourceChildBandInverse
public import ASDExplicitGamma.Native.GenericSourceChildBandMoments
public import ASDExplicitGamma.Native.GenericSourceChildBandMeanBudget
public import ASDExplicitGamma.Inverse.SourceQ3Drift

/-! Actual mean generator summation before Holder and time integration. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Algsuperdiff.Section3 ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Inverse ASDExplicitGamma.Triadic ASDExplicitGamma.Variational ASDExplicitGamma.Response
open scoped ENNReal
noncomputable section

/-- Single-direction deterministic covariance at refined-child shell distance. -/
def nativeSourceChildShellK (i : ℕ) : ℝ :=
  lemmaVH2kn (pureFluxCovarianceRho 1 i) (pureFluxCovarianceDelta 1 i)

/-- Complete feedback coefficient at refined-child shell distance. -/
def nativeSourceChildShellMu (i : ℕ) : ℝ :=
  pureFluxCovarianceMu (pureFluxCovarianceA 1 i) (pureFluxCovarianceB 1 i)

/-- All shell generator terms sum to the exact sharp mean source coefficient
with the same actual D, P*F and P²*F factors. -/
theorem native_source_child_band_mean_generator_ae_le
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (n : ℤ) (height : ℕ)
    (hpast : ∀ j < n, nativeInductionState M h j) (hstate : nativeInductionState M h n)
    (t : ℝ) (ht1 : t ≤ 1) :
    ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      let X := nativeSourceChildBandScalar n height t ω
      let T := modelTraceObservable (n-1) M.nu (Annealed.sigmaBar M n) X
      let F := T+4
      let P := (nativeSourceChildBandHistory M n height t ω).toReal
      let D := bankInverseTraceObservable (n-1) M.nu (Annealed.sigmaBar M n) M.nu_pos
        (Annealed.sigmaBar_characterization M n).1 X
      nativeSourceChildBandMeanGenerator M h n height t ω ≤
        nativeSourceRawShellVarianceCap M.gamma height*
          ((height:ℝ)*D+2*(65399707/10^9:ℝ)*(P*F)+(259713047/10^9:ℝ)*(P^2*F)) := by
  have hall : ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure, ∀ i : Fin height,
      let Q := originCube 2 (n-1)
      let af := responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M n:ℝ)
        (pureFluxOpenResponseRestriction (n-1) (nativeSourceChildBandScalar n height t ω))
      max (lemmaVTileHistory Q (pureFluxBankSourceDepth (i.val+2)) af)
        (pureFluxSourceTileHistory Q (pureFluxBankSourceDepth (i.val+2)) af) ≤
        (nativeSourceChildBandHistory M n height t ω).toReal :=
    ae_all_iff.mpr fun i => native_source_child_band_source_history_ae_le M h hM hg n height hpast i.val t ht1
  filter_upwards [hall] with ω hsource
  let X := nativeSourceChildBandScalar n height t ω
  let σ : ℝ := Annealed.sigmaBar M n
  let T := modelTraceObservable (n-1) M.nu σ X
  let F := T+4
  let P := (nativeSourceChildBandHistory M n height t ω).toReal
  let D := bankInverseTraceObservable (n-1) M.nu σ M.nu_pos (Annealed.sigmaBar_characterization M n).1 X
  let v := fun i : ℕ => (q3ModelAmplitude M h (n+((i+1:ℕ):ℤ)))^2/σ^2
  let c := fun i : ℕ => v i*D+2*v i*nativeSourceChildShellK i*(P*F)+v i*nativeSourceChildShellMu i*(P^2*F)
  have hT : 0 ≤ T := modelTraceObservable_nonneg (n-1) M.nu σ M.nu_pos
    (Annealed.sigmaBar_characterization M n).1 X
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hP : 0 ≤ P := ENNReal.toReal_nonneg
  have hD : 0 ≤ D := native_source_model_inverse_trace_nonneg (n-1) M.nu σ M.nu_pos
    (Annealed.sigmaBar_characterization M n).1 X
  have hrow (i : Fin height) : (1/2:ℝ)*modelCovarianceTrace (modelTraceObservable (n-1) M.nu σ)
      (pureFluxMainCubeQ3Directions (n-1) (q3ModelAmplitude M h (n+((i.val+1:ℕ):ℤ)))
        (q3ModelLength (n+((i.val+1:ℕ):ℤ)))) X ≤ c i.val := by
    let af := responseFramePlanarCoefficientField M.nu σ (pureFluxOpenResponseRestriction (n-1) X)
    let B := max (lemmaVTileHistory (originCube 2 (n-1)) (pureFluxBankSourceDepth (i.val+2)) af)
      (pureFluxSourceTileHistory (originCube 2 (n-1)) (pureFluxBankSourceDepth (i.val+2)) af)
    have hB : B ≤ P := hsource i
    have hB0 : 0 ≤ B := le_max_of_le_left
      (lemmaVTileHistory_nonneg (originCube 2 (n-1)) (pureFluxBankSourceDepth (i.val+2)) af)
    have hB2 := pow_le_pow_left₀ hB0 hB 2
    have hK : 0 ≤ nativeSourceChildShellK i.val := by
      have hr := (pureFlux_covariance_rho_pos 1 i.val).le
      have hd := (pureFlux_covariance_delta_bounds 1 i.val).1
      unfold nativeSourceChildShellK lemmaVH2kn lemmaVH2R1 lemmaVH2C1 lemmaVH2C2
      positivity
    have hμ : 0 ≤ nativeSourceChildShellMu i.val := (pureFlux_covariance_mu_lower _ _).1
    have hv : 0 ≤ v i.val := by dsimp [v]; positivity
    have hlabel : n-1+((i.val+2:ℕ):ℤ)=n+((i.val+1:ℕ):ℤ) := by omega
    have hρ : pureFluxCovarianceRho 0 (i.val+1)=pureFluxCovarianceRho 1 i.val := by
      unfold pureFluxCovarianceRho
      congr 1
      omega
    have hδ : pureFluxCovarianceDelta 0 (i.val+1)=pureFluxCovarianceDelta 1 i.val := by
      simp only [pureFluxCovarianceDelta,hρ]
    have hr := source_model_q3_positive_generator_row (n-1) (i.val+2) (by omega)
      M.nu σ (q3ModelAmplitude M h (n+((i.val+1:ℕ):ℤ))) M.nu_pos
      (Annealed.sigmaBar_characterization M n).1 X
    dsimp only at hr
    rw [pureFlux_bank_source_rho (n-1) (i.val+2) (by omega),
      pureFlux_bank_source_delta (n-1) (i.val+2) (by omega)] at hr
    have hsub : i.val+2-1=i.val+1 := by omega
    have hr' : (1/2:ℝ)*modelCovarianceTrace (modelTraceObservable (n-1) M.nu σ)
        (pureFluxMainCubeQ3Directions (n-1) (q3ModelAmplitude M h (n+((i.val+1:ℕ):ℤ)))
          (q3ModelLength (n+((i.val+1:ℕ):ℤ)))) X ≤
        v i.val*D+(2*v i.val*nativeSourceChildShellK i.val*B+v i.val*nativeSourceChildShellMu i.val*B^2)*F := by
      simpa only [source_lemmaV_B_eq_covariance_B,hsub,
        hlabel,Nat.add_sub_cancel,←native_source_model_inverse_trace_eq_frame_trace (n-1) M.nu σ M.nu_pos
          (Annealed.sigmaBar_characterization M n).1 X,
        T,F,D,v,B,af,nativeSourceChildShellK,nativeSourceChildShellMu,
        pureFluxCovarianceMu,pureFluxCovarianceA,pureFluxCovarianceB,hρ,hδ] using hr
    have h1 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hB
      (show 0 ≤ 2*v i.val*nativeSourceChildShellK i.val by positivity)) hF
    have h2 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hB2
      (show 0 ≤ v i.val*nativeSourceChildShellMu i.val by positivity)) hF
    have hcost : v i.val*D+(2*v i.val*nativeSourceChildShellK i.val*B+
        v i.val*nativeSourceChildShellMu i.val*B^2)*F ≤ c i.val := by
      dsimp [c]
      linarith only [h1,h2]
    exact hr'.trans hcost
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hrow i)
  have hbudget := native_source_child_band_mean_coefficient_budget M h n height hstate D (P*F) (P^2*F) hD
    (mul_nonneg hP hF) (mul_nonneg (sq_nonneg P) hF)
  have hc : (∑ i : Fin height, c i.val) ≤ nativeSourceRawShellVarianceCap M.gamma height*
      ((height:ℝ)*D+2*(65399707/10^9:ℝ)*(P*F)+(259713047/10^9:ℝ)*(P^2*F)) := by
    rw [Fin.sum_univ_eq_sum_range]
    exact hbudget
  exact hsum.trans hc

end
end ASDExplicitGamma.Native
