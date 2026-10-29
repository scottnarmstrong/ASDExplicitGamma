module

public import ASDExplicitGamma.Native.GenericSourceChildRationalCast
public import ASDExplicitGamma.Native.GenericSourceChildMeanDegree
public import ASDExplicitGamma.Native.GenericSourceChildExpMajorant

/-! Rational endpoint refined means on the actual law. The completed q1
input is explicit until its boundary-fixed source producer is instantiated. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Algsuperdiff.Section3 ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Inverse ASDExplicitGamma.Numerics.Native
noncomputable section

/-- Actual refined source mean below theta times a rational endpoint,
conditional only on the separate completed q1 source input. Every trace,
variance, differential and bank bound is discharged internally. -/
theorem native_source_completed_child_mean_rational_of_q1
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (n : ℤ) (height : ℕ) (hheight : 1 ≤ height)
    (hpast : ∀ j < n, nativeInductionState M h j) (hstate : nativeInductionState M h n)
    (high : Bool) (hh : height ≤ nativeSourceChildAuxHeight high)
    (hq1 : (∫ ω, cutoffTraceDefect M n (n-1) ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
      theta M*(nativeQstar:ℝ)) :
    (∫ ω, cutoffTraceDefect M (n+(height:ℤ)) (n-1) ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
      theta M*(nativeSourceChildRationalReturn high height:ℝ) := by
  let e := nativeSourceRawShellVarianceCap M.gamma height
  let e0 := nativeSourceGenericVarianceCap (17/50000) height
  let C := nativeSourceChildMeanC
  let c := e*C
  let c0 := e0*C
  let x0 : ℝ := nativeSourceChildAuxNorm high
  let x := theta M*x0
  let L := nativeSourceChildMeanL height (3/10^46:ℝ) x e
  let L0 := nativeSourceChildMeanL height (3/10^46:ℝ) x0 e0
  let a0 : ℝ := nativeQstar
  have hg0 := M.shellPrefix.gamma_pos.le
  have ht0 : 0 ≤ theta M := div_nonneg hg0 (by norm_num [gammaZero])
  have ht1 : theta M ≤ 1 := (div_le_one (by norm_num [gammaZero])).mpr hg
  have hH : nativeSourceChildAuxHeight high ≤ 160 := by cases high <;> norm_num [nativeSourceChildAuxHeight]
  have hheight160 : height ≤ 160 := hh.trans hH
  have hdomain := native_source_child_rational_domains ⟨height,by omega⟩
  have he0 : 0 ≤ e0 := by
    have hd := (Rat.cast_nonneg (K := ℝ)).mpr hdomain.1
    simpa only [native_source_child_rational_variance_cast] using hd
  have hC : 0 ≤ C := by norm_num [C,nativeSourceChildMeanC]
  have hc0 : 0 ≤ c0 := mul_nonneg he0 hC
  have hc01 : c0<1 := by
    have hd := (Rat.cast_lt (K := ℝ)).mpr hdomain.2.2
    simpa only [Rat.cast_mul,Rat.cast_one,native_source_child_rational_variance_cast,
      native_source_child_rational_C_cast] using hd
  have hden : 0 < 1-c0 := sub_pos.mpr hc01
  have he : 0 ≤ e := by dsimp [e,nativeSourceRawShellVarianceCap]; positivity
  have hecap : e ≤ theta M*e0 :=
    (native_source_true_variance_le_generic M.gamma height hg0 hg (by omega)).trans
      (native_source_generic_variance_cap_degree M.gamma (theta M) height hg0 hg rfl (by omega))
  have hc : 0 ≤ c := mul_nonneg he hC
  have hccap : c ≤ theta M*c0 := by
    convert mul_le_mul_of_nonneg_right hecap hC using 1
    ring
  have hx0 : 0 ≤ x0 := by cases high <;> norm_num [x0,nativeSourceChildAuxNorm]
  have hx : 0 ≤ x := mul_nonneg ht0 hx0
  have ha0 : 0 ≤ a0 := by norm_num [a0,nativeQstar]
  have hL0 : 0 ≤ L0 := native_source_child_mean_L_nonneg height _ _ _ (by positivity) hx0 he0
  have hL : L ≤ theta M*L0 := native_source_child_mean_L_degree height (theta M) _ x x0 e e0
    ht0 ht1 (by positivity) hx hx0 le_rfl he0 hecap
  have hnorm := native_source_child_band_uniform_L20_aux M h hM hg n height hheight hpast hstate high hh
  have hmean := native_source_child_band_mean_exp_phi M h hM hg n height hheight hpast hstate x hx hnorm
  have hexp := (native_source_child_exp_majorant c c0 (theta M) hc hc0 hc01 ht0 ht1 hccap).1
  have hphi := (native_source_phiOne_le_exp c hc).trans hexp
  have hu := add_le_add (mul_le_mul_of_nonneg_right hq1 (Real.exp_pos c).le)
    (mul_le_mul_of_nonneg_right hL (native_source_phiOne_nonneg c hc))
  have hv := add_le_add (mul_le_mul_of_nonneg_left hexp (mul_nonneg ht0 ha0))
    (mul_le_mul_of_nonneg_left hphi (mul_nonneg ht0 hL0))
  have hscalar : nativeSourceChildBandMean M n height 1 ≤ theta M*((a0+L0)/(1-c0)) := by
    have hh := hmean.trans (hu.trans hv)
    convert hh using 1
    ring
  have hframe := native_source_child_band_completed_mean_frame M n height hg (by omega)
  have hE := native_source_E_le_endpoint M.gamma height hg0 hg (by omega)
  have hE0 := native_source_E_nonneg M.gamma height hg0 hg (by omega)
  have hbound0 : 0 ≤ theta M*((a0+L0)/(1-c0)) := mul_nonneg ht0 (div_nonneg (add_nonneg ha0 hL0) hden.le)
  have hreturn := hframe.trans ((mul_le_mul_of_nonneg_left hscalar hE0).trans
    (mul_le_mul_of_nonneg_right hE hbound0))
  rw [native_source_child_rational_return_cast]
  convert hreturn using 1
  dsimp [a0,L0,c0,e0,C,x0]
  ring

end
end ASDExplicitGamma.Native
