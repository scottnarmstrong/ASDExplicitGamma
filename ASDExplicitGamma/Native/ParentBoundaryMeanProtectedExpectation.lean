module

public import ASDExplicitGamma.Native.ParentBoundaryMeanProtectedGenerator

/-! Actual full physical mean-generator expectations from the proved source banks. -/

@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Gaussian Inverse Main Model Triadic Algsuperdiff.Section3
noncomputable section

/-- Each ACTUAL physical mean shell has the correlated source expectation
bound. The direct physical full-response bound is retained; no centered
trace moment or own-node estimate is a premise. -/
theorem parent_boundary_mean_protected_expectation
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (hg : M.gamma ≤ gammaZero)
    (q n : ℤ) (j : ℕ) (hqr : q=n-((5+j:ℕ):ℤ)) (height : ℕ) (hheight : 1 ≤ height)
    (hpast : ∀ k<n,nativeInductionState M h k) (t : ℝ) (ht : t ≤ 1) (i : Fin height) :
    let s := 5+j+i.val+1
    let sigma : ℝ := Annealed.sigmaBar M n
    let v := (q3ModelAmplitude M h (n+((i.val+1:ℕ):ℤ)))^2/sigma^2
    let L := q3ModelLength (n+((i.val+1:ℕ):ℤ))
    let rho := cubeScaleFactor (originCube 2 q)/L.val
    let kappa := lemmaVH2kn rho rho
    let mu := pureFluxCovarianceMu (pureFluxCovarianceA 0 (s-1)) (pureFluxCovarianceB 0 (s-1))
    let R := (Annealed.sigmaBar M n:ℝ)/(Annealed.sigmaBar M (n-(j:ℤ)):ℝ)
    let F := parentBoundaryBandTraceCap M height (5+j)
    (∫ ω,parentBoundaryMeanShellGenerator M h q n height t i ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
      2*v*R*(3683/2500:ℝ)+2*v*kappa*R*((3683/2500:ℝ)*F)+v*mu*R^2*((3683/2500:ℝ)^2*F) := by
  intro s sigma v L rho kappa mu R F
  let Q := originCube 2 q
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let P := parentBoundaryCommonSingletonHistory M Q (n-(j:ℤ)) n height t
  let U := fun ω => modelTraceObservable q M.nu sigma (parentBoundaryObserverBandScalar q n height t ω)+4
  let J1 := fun ω => P ω*U ω
  let J2 := fun ω => P ω^2*U ω
  let b : ℝ := 3683/2500
  have hq : Q.scale ≤ n-(j:ℤ) := by change q ≤ n-(j:ℤ); omega
  have hgap : n-(j:ℤ)-Q.scale ≤ 5 := by change n-(j:ℤ)-q ≤ 5; omega
  have hscale : Q.scale=n-((5+j:ℕ):ℤ) := hqr
  have hprod := parent_boundary_mean_bank_products M h hM hg Q (n-(j:ℤ)) n hq hgap (by omega) height (5+j) hscale hpast t ht
  have hUeq : U=nativeSourceFullResponseTrace M Q n (n+(height:ℤ)) (fun _ => Real.sqrt t) :=
    funext (parent_boundary_observer_band_full_trace_eq M q n height t)
  dsimp only at hprod
  rw [←hUeq] at hprod
  have hJ1 : Integrable J1 μ ∧ (∫ ω,J1 ω ∂μ) ≤ b*F := by
    simpa only [Nat.zero_add,pow_one] using hprod.2.2 ⟨0,by decide⟩
  have hJ2 : Integrable J2 μ ∧ (∫ ω,J2 ω ∂μ) ≤ b^2*F := hprod.2.2 ⟨1,by decide⟩
  have hR : 0 ≤ R := div_nonneg (Annealed.sigmaBar_characterization M n).1.le (Annealed.sigmaBar_characterization M (n-(j:ℤ))).1.le
  have hv : 0 ≤ v := div_nonneg (sq_nonneg _) (sq_nonneg _)
  have hrho : 0 ≤ rho := div_nonneg (zpow_pos (by norm_num : (0:ℝ)<3) q).le L.property.le
  have hkappa : 0 ≤ kappa := by
    dsimp only [kappa,lemmaVH2kn,lemmaVH2R1,lemmaVH2C1,lemmaVH2C2]
    positivity
  have hmu : 0 ≤ mu := (pureFlux_covariance_mu_lower _ _).1
  have hGi := parent_boundary_mean_shell_generator_integrable M h hM q n height hheight t i
  have hpoint := parent_boundary_mean_protected_generator_ae M h hM hg q n j hqr height hpast t ht i
  dsimp only at hpoint
  have hi := integral_mono_ae hGi
    (((hprod.1.const_mul (2*v*R)).add (hJ1.1.const_mul (2*v*kappa*R))).add (hJ2.1.const_mul (v*mu*R^2))) hpoint
  have hpint : Integrable P μ := hprod.1
  have he12 := integral_add (hpint.const_mul (2*v*R)) (hJ1.1.const_mul (2*v*kappa*R))
  change (∫ ω,2*v*R*P ω+2*v*kappa*R*J1 ω ∂μ)=
    (∫ ω,2*v*R*P ω ∂μ)+(∫ ω,2*v*kappa*R*J1 ω ∂μ) at he12
  have he123 := integral_add ((hpint.const_mul (2*v*R)).add (hJ1.1.const_mul (2*v*kappa*R))) (hJ2.1.const_mul (v*mu*R^2))
  change (∫ ω,2*v*R*P ω+2*v*kappa*R*J1 ω+v*mu*R^2*J2 ω ∂μ)=
    (∫ ω,2*v*R*P ω+2*v*kappa*R*J1 ω ∂μ)+(∫ ω,v*mu*R^2*J2 ω ∂μ) at he123
  change (∫ ω,parentBoundaryMeanShellGenerator M h q n height t i ω ∂μ) ≤
    (∫ ω,2*v*R*P ω+2*v*kappa*R*J1 ω+v*mu*R^2*J2 ω ∂μ) at hi
  rw [he123,he12,integral_const_mul,integral_const_mul,integral_const_mul] at hi
  exact hi.trans (add_le_add (add_le_add
    (mul_le_mul_of_nonneg_left hprod.2.1 (mul_nonneg (mul_nonneg (by norm_num) hv) hR))
    (mul_le_mul_of_nonneg_left hJ1.2 (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hv) hkappa) hR)))
    (mul_le_mul_of_nonneg_left hJ2.2 (mul_nonneg (mul_nonneg hv hmu) (sq_nonneg R))))

end
end ASDExplicitGamma.Native
