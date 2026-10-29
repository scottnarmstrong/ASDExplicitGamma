module

public import ASDExplicitGamma.Native.GenericSourceExtraPassBounds
public import ASDExplicitGamma.Native.GenericSourceBandPasses
public import ASDExplicitGamma.Native.GenericSourceBandFrameNorm

/-! The actual one-shell starting norm for the refined child heat path,
using eight genuine moment refinements and its completed true frame. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Algsuperdiff.Section3 ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Inverse ASDExplicitGamma.Triadic ASDExplicitGamma.Variational
open scoped ENNReal
noncomputable section

/-- Eight actual refinements give an auxiliary 246 theta old-frame norm
on the completed one-shell observation cube. -/
theorem native_source_one_shell_eight_pass_L20
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (n : ℤ)
    (hpast : ∀ j < n, nativeInductionState M h j) :
    eLpNorm' (fun ω : Cutoff.CutoffSample 2 =>
      modelTraceObservable (n-1) M.nu (Annealed.sigmaBar M (n-1))
        (nativeSourceBandScalar (n-1) 1 1 ω)) 20 (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal (theta M*246) := by
  have hg0 := M.shellPrefix.gamma_pos.le
  have ht0 : 0 ≤ theta M := div_nonneg hg0 (by norm_num [gammaZero])
  have ht1 : theta M ≤ 1 := (div_le_one (by norm_num [gammaZero])).mpr hg
  have he0 : 0 ≤ nativeSourceRawShellVarianceCap M.gamma 1 := by
    unfold nativeSourceRawShellVarianceCap
    positivity
  have hf0 : 0 ≤ nativeSourceFullResponseCap M.gamma 1 := by
    unfold nativeSourceFullResponseCap rawTraceFullResponseCap
    positivity
  have hecap : nativeSourceRawShellVarianceCap M.gamma 1 ≤ theta M*(77/50000:ℝ) := by
    have h0 := native_source_true_variance_le_generic M.gamma 1 hg0 hg (by norm_num)
    have h1 := native_source_generic_variance_cap_degree M.gamma (theta M) 1 hg0 hg rfl (by norm_num)
    apply h0.trans (h1.trans (mul_le_mul_of_nonneg_left ?_ ht0))
    norm_num [nativeSourceGenericVarianceCap,nativeSourceE]
  have hfcap : nativeSourceFullResponseCap M.gamma 1 ≤ 16000 := by
    have h0 := native_source_generic_full_response_cap_le_bank M.gamma 1 hg0 hg (by norm_num)
    have h1 := native_source_generic_full_response_cap_degree M.gamma 1 hg0 hg (by norm_num)
    apply h0.trans (h1.trans ?_)
    norm_num [nativeSourceGenericFullResponseCap,nativeSourceE]
  have hscalar := native_source_generic_individual_degree_split 1 ht0 ht1
    (mul_nonneg (by norm_num : (0:ℝ)≤3/50) ht0) (by norm_num : (0:ℝ)≤3/50)
    (le_of_eq (by ring)) he0 (by norm_num : (0:ℝ)≤77/50000) hecap
    hf0 (by norm_num : (0:ℝ)≤16000) hfcap 8
  have hpass := native_source_band_generic_passes M h hM hg (n-1)
    (fun j hj => hpast j (by omega)) (hpast (n-1) (by omega)) 1 8 (by norm_num)
      1 (by constructor <;> norm_num)
  exact hpass.trans (ENNReal.ofReal_le_ofReal (hscalar.trans
    (mul_le_mul_of_nonneg_left native_source_extra_pass_eight_cap ht0)))

/-- In the actual completed frame the lag-one source trace has a uniform
auxiliary order-20 cap 250 theta; all starting norm premises are discharged. -/
theorem native_source_child_initial_L20
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (n : ℤ)
    (hpast : ∀ j < n, nativeInductionState M h j) :
    eLpNorm' (cutoffTraceDefect M n (n-1)) 20 (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal (250*theta M) := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let f := fun ω : Cutoff.CutoffSample 2 => modelTraceObservable (n-1) M.nu (Annealed.sigmaBar M (n-1))
    (nativeSourceBandScalar (n-1) 1 1 ω)
  let g := cutoffTraceDefect M n (n-1)
  let eta := nativeSourceFrameEta
  let A := 1+eta
  let C := 8*(1+1/eta)*((11/10:ℝ)*M.gamma*(1:ℝ))^2
  let R := nativeSourceE M.gamma 1
  let x := theta M*246
  have hg0 := M.shellPrefix.gamma_pos.le
  have ht0 : 0 ≤ theta M := div_nonneg hg0 (by norm_num [gammaZero])
  have hx0 : 0 ≤ x := mul_nonneg ht0 (by norm_num)
  have hR : 0 ≤ R := native_source_E_nonneg M.gamma 1 hg0 hg (by norm_num)
  have hA : 0 ≤ A := by norm_num [A,eta,nativeSourceFrameEta]
  have hC : 0 ≤ C := by dsimp [C,eta,nativeSourceFrameEta]; positivity
  have hfm : AEStronglyMeasurable f μ :=
    ((modelTraceObservable_hasPolynomiallyBoundedC2Derivatives (n-1) M.nu (Annealed.sigmaBar M (n-1)) M.nu_pos
      (Annealed.sigmaBar_characterization M (n-1)).1).1.continuous.measurable.comp
        (native_source_band_scalar_measurable (n-1) 1 1)).aestronglyMeasurable
  have hf0 (ω) : 0 ≤ f ω := modelTraceObservable_nonneg (n-1) M.nu (Annealed.sigmaBar M (n-1)) M.nu_pos
    (Annealed.sigmaBar_characterization M (n-1)).1 _
  have hgnonneg (ω) : 0 ≤ g ω := cutoffTraceDefect_nonneg M n (n-1) ω
  have hratio := ASDExplicitGamma.Scalar.sigmaBar_structural_continuity_nat M (n-1) 1
  have hlabel : n-1+((1:ℕ):ℤ)=n := by omega
  rw [hlabel] at hratio
  have hE := native_source_E_ge_three_power M.gamma 1 hg0 hg (by norm_num)
  have hratioR : (Annealed.sigmaBar M n:ℝ)/(Annealed.sigmaBar M (n-1):ℝ) ≤ R :=
    hratio.2.trans (by
      dsimp only [R]
      convert hE using 1
      congr 1
      ring)
  have hpoint (ω) : g ω ≤ R*(A*f ω+C) := by
    have hm := source_cutoff_pathwise_frame_map M (n-1) n (n-1) ω (by omega)
      eta (by norm_num [eta,nativeSourceFrameEta])
    have hgap : (n:ℝ)-((n-1:ℤ):ℝ)=1 := by push_cast; ring
    rw [hgap] at hm
    have he := native_source_band_trace_one M (n-1) 1 ω
    rw [hlabel] at he
    rw [←he] at hm
    simpa only [g,A,f,C,mul_one] using hm.trans
      (mul_le_mul_of_nonneg_right hratioR (add_nonneg (mul_nonneg hA (hf0 ω)) hC))
  have hcap := native_source_affine_L20_cap μ f g hfm hf0 hgnonneg R A C x hR hA hC hx0
    (native_source_one_shell_eight_pass_L20 M h hM hg n hpast) hpoint
  have hdegree := native_source_weak_frame_degree M.gamma (theta M) x 246 1 hg0 hg rfl hx0 le_rfl (by norm_num)
  apply hcap.trans (ENNReal.ofReal_le_ofReal ?_)
  have hfinal : nativeSourceWeakFrame M.gamma 1 x ≤ 250*theta M := by
    apply hdegree.trans
    have hnum : nativeSourceWeakFrame (17/50000) 1 246 ≤ 250 := by
      norm_num [nativeSourceWeakFrame,nativeSourceFrameEta,nativeSourceE]
    exact (mul_le_mul_of_nonneg_left hnum ht0).trans_eq (mul_comm _ _)
  simpa only [nativeSourceWeakFrame,R,A,C,eta,Nat.cast_one,mul_one] using hfinal

end
end ASDExplicitGamma.Native
