module

public import ASDExplicitGamma.Native.GenericSourceBandMomentDerivative
public import ASDExplicitGamma.Native.GenericSourceBandRefinedNorms

/-! Refined actual p20 derivative on the simultaneous source path. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Algsuperdiff.Section3 ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Inverse ASDExplicitGamma.Triadic
noncomputable section

/-- The actual simultaneous p20 derivative has the refined coefficient,
with no moment, generator or bank bound left as a premise. -/
theorem native_source_band_moment_derivative_refined
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (n : ℤ) (height : ℕ) (hheight : 1 ≤ height)
    (hpast : ∀ j < n, nativeInductionState M h j) (hstate : nativeInductionState M h n)
    (t : ℝ) (ht : t ∈ Set.Ioo (0:ℝ) 1) (x : ℝ) (hx : 0 ≤ x)
    (htrace : eLpNorm' (fun ω : Cutoff.CutoffSample 2 =>
      modelTraceObservable n M.nu (Annealed.sigmaBar M n) (nativeSourceBandScalar n height t ω))
      20 (Cutoff.cutoffSampleLaw M).toMeasure ≤ ENNReal.ofReal x) :
    deriv (nativeSourceBandMoment M n height) t ≤
      20*nativeSourceBandMoment M n height t^((19:ℝ)/20)*
        nativeSourceRefinedMomentIncrement height (nativeSourceRawShellVarianceCap M.gamma height)
          (nativeSourceFullResponseCap M.gamma height) x := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let σ : ℝ := Annealed.sigmaBar M n
  let X := nativeSourceBandScalar n height t
  let T := fun ω => modelTraceObservable n M.nu σ (X ω)
  let F := fun ω => T ω+4
  let P := fun ω => (nativeSourceBandHistory M n height t ω).toReal
  let D := fun ω => bankInverseTraceObservable n M.nu σ M.nu_pos
    (Annealed.sigmaBar_characterization M n).1 (X ω)
  let e := nativeSourceRawShellVarianceCap M.gamma height
  let b := (3683/2500:ℝ)
  let f := nativeSourceFullResponseCap M.gamma height
  have hg0 := M.shellPrefix.gamma_pos.le
  have he : 0 ≤ e := by dsimp [e,nativeSourceRawShellVarianceCap]; positivity
  have hA : 0 ≤ 39*(height:ℝ)+38*(521/1000:ℝ) := by positivity
  have hB : 0 ≤ 2*(521/1000:ℝ) := by norm_num
  have hC : 0 ≤ (1975/1000:ℝ)+38*(1565/1000:ℝ) := by norm_num
  have hI := native_source_band_power_integral_norm_row M h hM hg n height hheight hpast hstate t ht.2.le
  have hdata := native_source_band_refined_norms M h hM hg n hpast height t ht.2.le x hx htrace
  rcases hdata with ⟨hDnorm,hPFnorm,hP2Fnorm⟩
  have hcoef : e*((39*(height:ℝ)+38*(521/1000:ℝ))*positiveLpNorm μ 20 D+
      2*(521/1000:ℝ)*positiveLpNorm μ 20 (fun ω => P ω*F ω)+
      ((1975/1000:ℝ)+38*(1565/1000:ℝ))*positiveLpNorm μ 20 (fun ω => (P ω)^2*F ω)) ≤
      nativeSourceRefinedMomentIncrement height e f x := by
    have hh := mul_le_mul_of_nonneg_left
      (add_le_add (add_le_add (mul_le_mul_of_nonneg_left hDnorm hA)
        (mul_le_mul_of_nonneg_left hPFnorm hB)) (mul_le_mul_of_nonneg_left hP2Fnorm hC)) he
    convert hh using 1
    dsimp [nativeSourceRefinedMomentIncrement,nativeSourceK,nativeSourceM,nativeSourceQ,nativeSourceB128,f,
      nativeSourceFullResponseCap]
    ring
  have hscale : 0 ≤ 20*nativeSourceBandMoment M n height t^((19:ℝ)/20) := by
    exact mul_nonneg (by norm_num) (Real.rpow_nonneg (native_source_band_moment_nonneg M n height t) _)
  have hd := (native_source_band_moment_heat M h hM n height hheight).2 t ht.1
  rw [hd.deriv]
  exact hI.trans (mul_le_mul_of_nonneg_left hcoef hscale)

end
end ASDExplicitGamma.Native
