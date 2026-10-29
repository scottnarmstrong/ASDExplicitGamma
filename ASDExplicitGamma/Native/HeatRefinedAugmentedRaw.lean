module

public import ASDExplicitGamma.Native.HeatRefinedObserverAugment
public import ASDExplicitGamma.Native.HeatAuxiliaryGaussianLaw
public import ASDExplicitGamma.Native.HeatRefinedRawProfile
public import ASDExplicitGamma.Inverse.ParentGapCenteredDepth

/-! Full128 control on the actual refined physical/auxiliary product law. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ProbabilityTheory Algsuperdiff.Section3
open Gaussian Inverse Triadic Numerics.Native
open scoped ENNReal NNReal
noncomputable section

/-- Norm-level substitution into the actual shear envelope. This analytic
adapter is instantiated below with the proved physical full-response profile. -/
theorem heat_refined_auxiliary_raw_of_physical_cap
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (hg : M.gamma ≤ gammaZero)
    (n : ℤ) (height : ℕ) (hpast : ∀ j<n,nativeInductionState M h j) (t : ℝ) (ht : t ≤ 1)
    (g : (ℕ → ℝ) → ℝ) (hgm : Measurable g) (v : ℝ≥0)
    (hlaw : standardGaussianInfinitePi.map (fun ξ => g ξ/(Annealed.sigmaBar M n:ℝ)) = gaussianReal 0 v)
    (f : ℝ) (hf : 0 ≤ f)
    (hphysical : eLpNorm (fun ω : Cutoff.CutoffSample 2 =>
      modelTraceObservable (n-1) M.nu (Annealed.sigmaBar M n)
        (nativeSourceChildBandScalar n height t ω)+4) 128 (Cutoff.cutoffSampleLaw M).toMeasure ≤ ENNReal.ofReal f) :
    eLpNorm (fun z : Cutoff.CutoffSample 2 × (ℕ → ℝ) =>
      modelTraceObservable (n-1) M.nu (Annealed.sigmaBar M n)
        (heatRefinedObserverShear (n-1) n height t z.1 (g z.2))) 128 (nativeHeatRemainderJointLaw M) ≤
      ENNReal.ofReal ((Real.sqrt f+Real.sqrt (2*((3683/2500:ℝ)+3/10^46)*255*(v:ℝ)))^2) := by
  let T := fun ω : Cutoff.CutoffSample 2 => modelTraceObservable (n-1) M.nu (Annealed.sigmaBar M n)
    (parentBoundaryObserverBandScalar (n-1) n height t ω)
  have hTm : Measurable T :=
    (modelTraceObservable_hasPolynomiallyBoundedC2Derivatives (n-1) M.nu (Annealed.sigmaBar M n)
      M.nu_pos (Annealed.sigmaBar_characterization M n).1).1.continuous.measurable.comp
      (parent_boundary_observer_band_scalar_measurable (n-1) n height t)
  have hT0 (ω) : 0 ≤ T ω := modelTraceObservable_nonneg (n-1) M.nu (Annealed.sigmaBar M n)
    M.nu_pos (Annealed.sigmaBar_characterization M n).1 _
  have hTc : eLpNorm T 128 (Cutoff.cutoffSampleLaw M).toMeasure ≤ ENNReal.ofReal f := by
    apply le_trans (b := eLpNorm (fun ω => T ω+4) 128 (Cutoff.cutoffSampleLaw M).toMeasure)
    · apply eLpNorm_mono_ae hTm.aestronglyMeasurable
      filter_upwards with ω
      rw [Real.norm_of_nonneg (hT0 ω),Real.norm_of_nonneg (by positivity [hT0 ω])]
      linarith
    · exact hphysical
  have hq : originCube 2 (n-1) ∈ descendantsAtDepth (originCube 2 n) 1 := by
    simpa only [Nat.cast_one] using originCube_mem_descendantsAtDepth' 2 n 1
  have ha := heat_refined_observer_augmented_Lp M h hM hg (n-1) n 1 (by norm_num) hq
    height hpast t ht g hgm 128 (by norm_num) le_rfl
  simp only [show 2*(128:ℝ)=256 by norm_num,ENNReal.ofReal_ofNat] at ha
  have hG := (heat_auxiliary_gaussian_raw_norm standardGaussianInfinitePi
    (fun ξ => g ξ/(Annealed.sigmaBar M n:ℝ)) (hgm.div_const _) v hlaw).2
  have hbound := ha.trans (pow_le_pow_left' (add_le_add
    (ENNReal.rpow_le_rpow hTc (by norm_num : (0:ℝ) ≤ 1/2))
    (mul_le_mul' le_rfl hG)) 2)
  refine hbound.trans_eq ?_
  rw [ENNReal.ofReal_rpow_of_nonneg hf (by norm_num : (0:ℝ) ≤ 1/2),
    ENNReal.ofReal_rpow_of_nonneg (by positivity : (0:ℝ) ≤ 2*(3683/2500+3/10^46))
      (by norm_num : (0:ℝ) ≤ 1/2),←Real.sqrt_eq_rpow,←Real.sqrt_eq_rpow,
    ←ENNReal.ofReal_mul (Real.sqrt_nonneg _),←Real.sqrt_mul (by positivity : (0:ℝ) ≤ 2*(3683/2500+3/10^46)),
    ←ENNReal.ofReal_add (Real.sqrt_nonneg _) (Real.sqrt_nonneg _),
    ←ENNReal.ofReal_pow (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
  rw [mul_assoc (2*((3683/2500:ℝ)+3/10^46)) 255 (v:ℝ)]

/-- Actual raw heat control from strict-past states and the genuine Gaussian
marginal law. No physical response or inverse estimate is a premise. -/
theorem heat_refined_auxiliary_raw_L128
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (hg : M.gamma ≤ gammaZero)
    (n : ℤ) (height : ℕ) (hh : height ≤ 1331)
    (hpast : ∀ j<n,nativeInductionState M h j) (t : ℝ) (ht : t ≤ 1)
    (g : (ℕ → ℝ) → ℝ) (hgm : Measurable g) (v : ℝ≥0)
    (hlaw : standardGaussianInfinitePi.map (fun ξ => g ξ/(Annealed.sigmaBar M n:ℝ)) = gaussianReal 0 v) :
    eLpNorm (fun z : Cutoff.CutoffSample 2 × (ℕ → ℝ) =>
      modelTraceObservable (n-1) M.nu (Annealed.sigmaBar M n)
        (heatRefinedObserverShear (n-1) n height t z.1 (g z.2))) 128 (nativeHeatRemainderJointLaw M) ≤
      ENNReal.ofReal ((Real.sqrt ((nativeHeatRQ:ℝ)*nativeSourceGenericFullResponseCap (17/50000) (height+1))+
        Real.sqrt (2*((3683/2500:ℝ)+3/10^46)*255*(v:ℝ)))^2) := by
  have hf := native_source_generic_full_response_cap_nonneg (17/50000) (height+1)
    (by norm_num) le_rfl (by omega)
  exact heat_refined_auxiliary_raw_of_physical_cap M h hM hg n height hpast t ht g hgm v hlaw _
    (mul_nonneg (by norm_num [nativeHeatRQ,nativeE,nativeGamma]) hf)
    (heat_refined_child_physical_L128 M h hM hg n height hh hpast t ht)

end
end ASDExplicitGamma.Native
