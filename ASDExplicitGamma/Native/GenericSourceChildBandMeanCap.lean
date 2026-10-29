module

public import ASDExplicitGamma.Native.GenericSourceChildBandMeanDerivative
public import ASDExplicitGamma.Native.GenericSourceChildBandEndpoint

/-! The actual refined-child mean comparison, retaining its literal q1
initial mean and every rare-product term. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Algsuperdiff.Section3 ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Inverse ASDExplicitGamma.Triadic
noncomputable section

/-- The entire phi1 function is bounded by its endpoint exponential on the
positive half-line, including at zero. -/
theorem native_source_phiOne_le_exp (c : ℝ) (hc : 0 ≤ c) :
    nativeSourcePhiOne c ≤ Real.exp c := by
  rcases hc.eq_or_lt with rfl | hc
  · rw [native_source_phiOne_zero,Real.exp_zero]
  · have hh := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-c)) (Real.exp_pos c).le
    have he : Real.exp (-c)*Real.exp c=1 := by rw [←Real.exp_add]; simp only [neg_add_cancel,Real.exp_zero]
    rw [he] at hh
    apply le_of_mul_le_mul_left (a := c) ?_ hc
    rw [native_source_phiOne_mul]
    linarith only [hh]

/-- The refined heat path satisfies the exact exp/phi1 comparison from its
actual lag-one initial mean. Only the separately quantified uniform trace
cap is needed to pay the rare products. -/
theorem native_source_child_band_mean_exp_phi
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (n : ℤ) (height : ℕ) (hheight : 1 ≤ height)
    (hpast : ∀ j < n, nativeInductionState M h j) (hstate : nativeInductionState M h n)
    (x : ℝ) (hx : 0 ≤ x)
    (htrace : ∀ t ∈ Set.Icc (0:ℝ) 1, eLpNorm'
      (fun ω : Cutoff.CutoffSample 2 => modelTraceObservable (n-1) M.nu (Annealed.sigmaBar M n)
        (nativeSourceChildBandScalar n height t ω)) 20 (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal x) :
    nativeSourceChildBandMean M n height 1 ≤
      (∫ ω, cutoffTraceDefect M n (n-1) ω ∂(Cutoff.cutoffSampleLaw M).toMeasure)*
        Real.exp (nativeSourceRawShellVarianceCap M.gamma height*nativeSourceChildMeanC)+
      nativeSourceChildMeanL height (3/10^46:ℝ) x (nativeSourceRawShellVarianceCap M.gamma height)*
        nativeSourcePhiOne (nativeSourceRawShellVarianceCap M.gamma height*nativeSourceChildMeanC) := by
  let f := nativeSourceChildBandMean M n height
  let df := fun t => ∫ ω, nativeSourceChildBandMeanGenerator M h n height t ω
    ∂(Cutoff.cutoffSampleLaw M).toMeasure
  let e := nativeSourceRawShellVarianceCap M.gamma height
  let c := e*nativeSourceChildMeanC
  let L := nativeSourceChildMeanL height (3/10^46:ℝ) x e
  have he : 0 < e := by
    have hg0 := M.shellPrefix.gamma_pos
    dsimp [e,nativeSourceRawShellVarianceCap]
    positivity
  have hc : 0 < c := mul_pos he (by norm_num [nativeSourceChildMeanC])
  have hheat := native_source_child_band_mean_heat_generator M h hM n height hheight
  apply native_source_scalar_mean_of_interior_derivative f df _ c L hc
    (hheat.1.mono (fun _ ht => ht.1)) (fun t ht => hheat.2 t ht.1)
  · exact le_of_eq (native_source_child_band_mean_zero M n height)
  · intro t ht
    have hd := hheat.2 t ht.1
    dsimp only [df]
    rw [←hd.deriv]
    exact native_source_child_band_mean_derivative M h hM hg n height hheight hpast hstate t ht x hx
      (htrace t ⟨ht.1.le,ht.2.le⟩)

end
end ASDExplicitGamma.Native
