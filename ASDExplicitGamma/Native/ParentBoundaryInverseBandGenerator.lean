module

public import ASDExplicitGamma.Native.ParentBoundaryInverseBankGenerator
public import ASDExplicitGamma.Native.ParentBoundaryInverseBank
public import ASDExplicitGamma.Native.GenericSourceBandMoments

/-! The actual simultaneous-band inverse lower generator. Every shell uses
its own physical covariance rows, with one shared complete history. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Algsuperdiff.Section3 Response Scalar Gaussian Main Triadic Variational Inverse
open scoped ENNReal
noncomputable section

/-- Actual finite-band negative covariance coefficient in the starting frame. -/
def parentBoundaryBandInverseClock (M : ABKModel 2) (h : ℝ) (n : ℤ) (height : ℕ) : ℝ :=
  ∑ i : Fin height,(q3ModelAmplitude M h (n+((i.val+1:ℕ):ℤ)))^2/(Annealed.sigmaBar M n:ℝ)^2*
    pureFluxCovarianceMu (pureFluxCovarianceB 0 i.val) (pureFluxCovarianceA 0 i.val)

/-- Literal complete physical inverse generator on the simultaneous band. -/
def parentBoundaryBandInverseGenerator (M : ABKModel 2) (h : ℝ) (n : ℤ)
    (height : ℕ) (t : ℝ) (omega : Cutoff.CutoffSample 2) : ℝ :=
  ∑ i : Fin height,(1/2:ℝ)*modelCovarianceTrace
    (mainInverseObservable n M.nu (Annealed.sigmaBar M n))
    (pureFluxMainCubeQ3Directions n (q3ModelAmplitude M h (n+((i.val+1:ℕ):ℤ)))
      (q3ModelLength (n+((i.val+1:ℕ):ℤ)))) (nativeSourceBandScalar n height t omega)

/-- The actual coefficient of the inverse loss is nonnegative. -/
theorem parent_boundary_inverse_band_clock_nonneg (M : ABKModel 2) (h : ℝ)
    (n : ℤ) (height : ℕ) : 0≤parentBoundaryBandInverseClock M h n height :=
  Finset.sum_nonneg (fun _i _ => mul_nonneg (div_nonneg (sq_nonneg _) (sq_nonneg _))
    (pureFlux_covariance_mu_lower _ _).1)

/-- The actual lower generator has no estimate premise: physical shell
directions, minimizers, source histories and covariance rows are all discharged. -/
theorem parent_boundary_inverse_band_generator_lower
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (n : ℤ) (height : ℕ)
    (hpast : ∀ j<n,nativeInductionState M h j) (t : ℝ) (ht : t≤1) :
    ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      -(parentBoundaryBandInverseClock M h n height*
        (nativeSourceBandHistory M n height t omega).toReal^2*
          mainInverseObservable n M.nu (Annealed.sigmaBar M n)
            (nativeSourceBandScalar n height t omega))≤
        parentBoundaryBandInverseGenerator M h n height t omega := by
  classical
  have hb := native_source_band_local_bank M h hM hg n height hpast t ht
  have hs := (Annealed.sigmaBar_characterization M n).1
  have hobs : mainInverseObservable n M.nu (Annealed.sigmaBar M n)=
      bankInverseTraceObservable n M.nu (Annealed.sigmaBar M n) M.nu_pos hs := by
    funext x
    exact parent_boundary_inverse_observable_eq_bank n M.nu _ M.nu_pos hs x
  filter_upwards [hb.history_finite] with omega hfinite
  have hrow (i : Fin height) := parent_boundary_inverse_bank_generator n (i.val+1) (by omega)
    M.nu (Annealed.sigmaBar M n) (q3ModelAmplitude M h (n+((i.val+1:ℕ):ℤ))) M.nu_pos hs
    (nativeSourceBandScalar n height t omega) (nativeSourceBandHistory M n height t omega).toReal
    ENNReal.toReal_nonneg (fun U hU => native_source_band_mesh_history_le M n height t omega
      (pureFluxBankSourceDepth (i.val+1)) (by unfold pureFluxBankSourceDepth; omega) hfinite.ne hU)
  simp only [Nat.add_sub_cancel,hobs] at hrow ⊢
  unfold parentBoundaryBandInverseGenerator parentBoundaryBandInverseClock
  rw [Finset.sum_mul,Finset.sum_mul,←Finset.sum_neg_distrib]
  apply Finset.sum_le_sum
  intro i _
  simpa only [Nat.add_sub_cancel,hobs] using hrow i

/-- The physical generator is genuinely integrable independently of its
lower bound, by Gaussian polynomial moments of each canonical shell trace. -/
theorem parent_boundary_inverse_band_generator_integrable
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (n : ℤ) (height : ℕ) (hheight : 1≤height) (t : ℝ) :
    Integrable (parentBoundaryBandInverseGenerator M h n height t)
      (Cutoff.cutoffSampleLaw M).toMeasure := by
  let Phi := mainInverseObservable n M.nu (Annealed.sigmaBar M n)
  have hPhi := mainInverseObservable_hasPolynomiallyBoundedC2Derivatives n M.nu
    (Annealed.sigmaBar M n) M.nu_pos (Annealed.sigmaBar_characterization M n).1
  unfold parentBoundaryBandInverseGenerator
  apply integrable_finsetSum Finset.univ
  intro i _
  let b := q3ModelAmplitude M h (n+((i.val+1:ℕ):ℤ))
  let L := q3ModelLength (n+((i.val+1:ℕ):ℤ))
  have htest := source_q3_covariance_trace_regular n b L Phi hPhi
  have hmem := native_source_band_test_memLp M h hM n height hheight
    (modelCovarianceTrace Phi (pureFluxMainCubeQ3Directions n b L)) htest.1 htest.2 t 2 (by norm_num)
  exact (hmem.integrable (by norm_num : (1:ℝ≥0∞)≤ENNReal.ofReal (2:ℝ))).const_mul (1/2:ℝ)

end
end ASDExplicitGamma.Native
