module

public import ASDExplicitGamma.Native.ParentBoundaryMeanProtectedBank
public import ASDExplicitGamma.Native.ParentBoundaryMeanGenerator
public import ASDExplicitGamma.Native.ParentBoundaryMeanObserverBank
public import ASDExplicitGamma.Native.ParentBoundaryMeanBankProducts

/-! Actual full physical mean heat generators on the parent source cells. -/

@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Gaussian Inverse Main Model Triadic Algsuperdiff.Section3
open scoped ENNReal
noncomputable section

/-- The ACTUAL full uncentered mean shell has its source bank polynomial,
with all inverse histories and inverse traces paid in the same starting
frame. No generator, inverse-bank or trace estimate is assumed. -/
theorem parent_boundary_mean_protected_generator_ae
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (hg : M.gamma ≤ gammaZero)
    (q n : ℤ) (j : ℕ) (hqr : q=n-((5+j:ℕ):ℤ)) (height : ℕ) (hpast : ∀ k<n,nativeInductionState M h k)
    (t : ℝ) (ht : t ≤ 1) (i : Fin height) :
    let s := 5+j+i.val+1
    let sigma : ℝ := Annealed.sigmaBar M n
    let v := (q3ModelAmplitude M h (n+((i.val+1:ℕ):ℤ)))^2/sigma^2
    let L := q3ModelLength (n+((i.val+1:ℕ):ℤ))
    let rho := cubeScaleFactor (originCube 2 q)/L.val
    let kappa := lemmaVH2kn rho rho
    let mu := pureFluxCovarianceMu (pureFluxCovarianceA 0 (s-1)) (pureFluxCovarianceB 0 (s-1))
    let R := (Annealed.sigmaBar M n:ℝ)/(Annealed.sigmaBar M (n-(j:ℤ)):ℝ)
    let P := parentBoundaryCommonSingletonHistory M (originCube 2 q) (n-(j:ℤ)) n height t
    let U := fun ω => modelTraceObservable q M.nu sigma (parentBoundaryObserverBandScalar q n height t ω)+4
    ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      parentBoundaryMeanShellGenerator M h q n height t i ω ≤
        2*v*R*P ω+2*v*kappa*R*(P ω*U ω)+v*mu*R^2*(P ω^2*U ω) := by
  intro s sigma v L rho kappa mu R P U
  let Q := originCube 2 q
  let Φ := modelTraceObservable q M.nu sigma
  have hs : 5 ≤ s := by dsimp [s]; omega
  have hqs : q+(s:ℤ)=n+((i.val+1:ℕ):ℤ) := by dsimp [s]; omega
  have hm : pureFluxBankSourceDepth s=0 := parent_boundary_mean_source_depth_zero s hs
  have hnu := M.nu_pos
  have hsigma := (Annealed.sigmaBar_characterization M n).1
  have hv : 0 ≤ v := div_nonneg (sq_nonneg _) (sq_nonneg _)
  have hrho : 0 ≤ rho := div_nonneg (zpow_pos (by norm_num : (0:ℝ)<3) q).le L.property.le
  have hkappa : 0 ≤ kappa := by
    dsimp only [kappa,lemmaVH2kn,lemmaVH2R1,lemmaVH2C1,lemmaVH2C2]
    positivity
  have hmu : 0 ≤ mu := (pureFlux_covariance_mu_lower _ _).1
  filter_upwards [parent_boundary_mean_protected_source_bank M h hM hg q (n-(j:ℤ)) n (by omega) (by omega) height hpast t ht,
    parent_boundary_mean_protected_inverse_bank M h hM hg q (n-(j:ℤ)) n (by omega) (by omega) height hpast t ht] with ω hbank hinverse
  let X := parentBoundaryObserverBandScalar q n height t ω
  let af := responseFramePlanarCoefficientField M.nu sigma (pureFluxOpenResponseRestriction q X)
  let B := max (lemmaVTileHistory Q 0 af) (pureFluxSourceTileHistory Q 0 af)
  let D := bankInverseTraceObservable q M.nu sigma hnu hsigma X
  have hB : 0 ≤ B := (lemmaVTileHistory_nonneg Q 0 af).trans (le_max_left _ _)
  have hBP : B ≤ R*P ω := hbank
  have hU : 0 ≤ U ω := add_nonneg (modelTraceObservable_nonneg q M.nu sigma hnu hsigma X) (by norm_num)
  have hB2 := pow_le_pow_left₀ hB hBP 2
  have hgen := source_model_q3_positive_generator_row q s (by omega) M.nu sigma
    (q3ModelAmplitude M h (n+((i.val+1:ℕ):ℤ))) hnu hsigma X
  dsimp only at hgen
  rw [hqs,hm] at hgen
  simp only [diagMeshRadius,pow_zero,div_one] at hgen
  rw [←native_source_model_inverse_trace_eq_frame_trace q M.nu sigma hnu hsigma X] at hgen
  change parentBoundaryMeanShellGenerator M h q n height t i ω ≤ v*D+(2*v*kappa*B+v*mu*B^2)*U ω at hgen
  have hinv : D ≤ 2*R*P ω := hinverse
  have h1 := mul_le_mul_of_nonneg_left hinv hv
  have h2 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hBP
    (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤2) hv) hkappa)) hU
  have h3 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hB2 (mul_nonneg hv hmu)) hU
  apply hgen.trans
  have hh := add_le_add h1 (add_le_add h2 h3)
  convert hh using 1 <;> ring

end
end ASDExplicitGamma.Native
