module

public import ASDExplicitGamma.Native.HeatVHEATBracketRefinedGeometry
import ASDExplicitGamma.Gaussian.DerivativeLawValueCovariance
import ASDExplicitGamma.Gaussian.BilinearCovariance
import ASDExplicitGamma.Gaussian.WholeRoot

/-! The actual refined shell law identifies the center-observation variance
with the joint q3 grid-section norm. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open MeasureTheory Homogenization ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Main ASDExplicitGamma.Model ASDExplicitGamma.Triadic
open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open ProbabilityTheory
open scoped RealInnerProductSpace

/-- For any finite family of observation points, a chosen refined shell's
observation variance is the norm square of its corresponding section sum. -/
theorem nativeHeatQ3RefinedCarrierShellObservationVariance_of_kernel
    {I : Type} [Fintype I]
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (m : ℤ) (d : Fin 9)
    (F : NativeHeatQ3RefinedCarrierFreshShellFamily M
      (nativeHeatQ3RefinedCarrierDomain m)
      (nativeHeatQ3RefinedCarrierPhysicalShells m))
    (x : I → nativeHeatQ3RefinedCarrierDomain m)
    (xVec : I → Vec 2)
    (hx : ∀ i, (x i : Vec 2) = xVec i)
    (a : I → ℝ) (v : I → Gaussian.WhiteNoise)
    (hkernel : ∀ i j,
      q3ShellCovariance M h (nativeHeatQ3RefinedCarrierPhysicalShells m d)
        (xVec i) (xVec j) = ⟪v i, v j⟫) :
    ∑' j,
      (nativeHeatQ3FiniteCenterObservation x a
        (F.factor d (F.direction d j))) ^ 2 =
      ‖nativeHeatQ3FiniteSectionSum a v‖ ^ 2 := by
  classical
  let K := nativeHeatQ3RefinedCarrierDomain m
  let k := nativeHeatQ3RefinedCarrierPhysicalShells m d
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let L : C(K, ℝ) →L[ℝ] ℝ := nativeHeatQ3FiniteCenterObservation x a
  let Qcov : ℝ := ∑ i, ∑ j,
    a i * a j * q3ShellCovariance M h k (xVec i) (xVec j)
  have hLgrid (f : C(K, ℝ)) : L f = ∑ i, a i * f (x i) := by
    simp only [L, K, nativeHeatQ3FiniteCenterObservation_apply]
  have hGram : Qcov = ‖nativeHeatQ3FiniteSectionSum a v‖ ^ 2 := by
    have hnorm := nativeHeatQ3FiniteSectionSum_norm_sq a v
    calc
      Qcov = ∑ i, ∑ j, a i * a j * ⟪v i, v j⟫ := by
        simp only [Qcov]
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        rw [hkernel i j]
      _ = ‖nativeHeatQ3FiniteSectionSum a v‖ ^ 2 := hnorm.symm
  have hQnonneg : 0 ≤ Qcov :=
    hGram.symm ▸ sq_nonneg (‖nativeHeatQ3FiniteSectionSum a v‖)
  let coord : Cutoff.CutoffSample 2 → ShellField 2 := fun ω => ω.1 k
  let obs : ShellField 2 → ℝ := fun ξ =>
    ∑ i, a i * shellScalarValue ξ (xVec i)
  let obsFun : C(K, ℝ) → ℝ := fun f => ∑ i, a i * f (x i)
  let Y : Cutoff.CutoffSample 2 → ℝ := fun ω =>
    obsFun (shellFieldScalarRestriction K (ω.1 k))
  have hcoordMeas : Measurable coord :=
    (measurable_pi_apply k).comp measurable_subtype_coe
  have hEvalMeas (i : I) :
      Measurable (fun ξ : ShellField 2 => shellScalarValue ξ (xVec i)) :=
    (shellDerivativeEval_continuous (.value (xVec i))).measurable
  have hobsMeas : Measurable obs := by
    dsimp [obs]
    exact Finset.measurable_sum _ fun i hi =>
      measurable_const.mul (hEvalMeas i)
  have hrestrict (i : I) (ω : Cutoff.CutoffSample 2) :
      shellFieldScalarRestriction K (ω.1 k) (x i) =
        shellScalarValue (ω.1 k) (xVec i) := by
    rw [← hx i]
    rfl
  have hYeq : Y = obs ∘ coord := by
    funext ω
    dsimp [Y, obsFun, obs, coord]
    apply Finset.sum_congr rfl
    intro i hi
    exact congrArg (fun z : ℝ => a i * z) (hrestrict i ω)
  have hobsFunEqL : obsFun = fun f => L f := by
    funext f
    exact (hLgrid f).symm
  let shell : Cutoff.CutoffSample 2 → C(K, ℝ) := fun ω =>
    shellFieldScalarRestriction K (ω.1 k)
  have hsampleMeas : Measurable shell :=
    (measurable_shellFieldScalarRestriction K).comp hcoordMeas
  have hYeqL : Y = fun ω => L (shell ω) := by
    funext ω
    dsimp [Y, shell]
    rw [hobsFunEqL]
  have hLmeas : Measurable (fun f : C(K, ℝ) => L f) := L.continuous.measurable
  have hYmeas : Measurable Y := by
    rw [hYeq]
    exact hobsMeas.comp hcoordMeas
  let ν := (ShellField.shellMarginalLaw M.P k).toMeasure
  have hmap : μ.map coord = ν := by
    simpa [coord, μ, ν] using
      Model.map_freshShell_eq_shellMarginalLaw M (k - 1)
  have hcov (i j : I) :
      (∫ ξ, shellScalarValue ξ (xVec i) * shellScalarValue ξ (xVec j) ∂ν) =
        q3ShellCovariance M h k (xVec i) (xVec j) :=
    q3Shell_value_covariance M h hM k (xVec i) (xVec j)
  let xEval : I → Vec 2 := xVec
  have hq3 := (q3Shell_values_gaussian M h hM k).map_linearCombination_covariance
    (x := xEval) a
  have hobsLaw : ν.map obs = gaussianReal 0 (Real.toNNReal Qcov) := by
    simpa only [ν, Qcov, obs, xEval, hcov] using hq3
  have hYactualLaw : μ.map Y = gaussianReal 0 (Real.toNNReal Qcov) := by
    calc
      μ.map Y = μ.map (obs ∘ coord) := by rw [hYeq]
      _ = (μ.map coord).map obs := (Measure.map_map hobsMeas hcoordMeas).symm
      _ = ν.map obs := by rw [hmap]
      _ = _ := hobsLaw
  let φ : C(K, ℝ) → ℝ := fun f => (L f) ^ 2
  have hφ : Measurable φ := by fun_prop
  have hseriesMeas : Measurable (fun ω =>
      gaussianSeriesLimitE (F.squareSummable d) (F.factor d) ω) :=
    (stronglyMeasurable_gaussianSeriesLimitE (F.squareSummable d)
      (F.factor d)).measurable
  have hpushMoment :
      (∫ ω, (L (gaussianSeriesLimitE (F.squareSummable d)
          (F.factor d) ω)) ^ 2 ∂standardGaussianInfinitePi) =
        ∫ ω, (L (shell ω)) ^ 2 ∂μ := by
    calc
      _ = ∫ f, φ f ∂(standardGaussianInfinitePi.map
          (fun ω => gaussianSeriesLimitE (F.squareSummable d)
            (F.factor d) ω)) := by
        symm
        exact integral_map hseriesMeas.aemeasurable hφ.aestronglyMeasurable
      _ = ∫ f, φ f ∂(μ.map shell) := by rw [← F.law d]
      _ = _ := integral_map hsampleMeas.aemeasurable hφ.aestronglyMeasurable
  have hseriesSecond :=
    integral_observation_sq (F.squareSummable d) (F.factor d) L
  have hvarEq : ∑' j, (L (F.factor d (F.direction d j)) ^ 2) = Qcov := by
    calc
      _ = ∫ ω, (L (gaussianSeriesLimitE (F.squareSummable d)
          (F.factor d) ω)) ^ 2 ∂standardGaussianInfinitePi := hseriesSecond.symm
      _ = ∫ ω, (L (shell ω)) ^ 2 ∂μ := hpushMoment
      _ = Qcov := by
        have hm := integral_sq_of_map_gaussianReal_zero
          hYmeas.aemeasurable hYactualLaw
        rw [Real.coe_toNNReal _ hQnonneg] at hm
        simpa only [hYeqL] using hm
  calc
    _ = Qcov := hvarEq
    _ = ‖nativeHeatQ3FiniteSectionSum a v‖ ^ 2 := hGram

end ASDExplicitGamma.Native
