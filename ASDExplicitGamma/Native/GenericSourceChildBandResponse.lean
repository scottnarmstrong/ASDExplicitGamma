module

public import ASDExplicitGamma.Native.GenericSourceChildBandInverse
public import ASDExplicitGamma.Native.GenericSourceBankAdapter

/-! Actual full128 bank in the child observation cube and old completed frame. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Algsuperdiff.Section3 ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Inverse ASDExplicitGamma.Triadic ASDExplicitGamma.Response
open ASDExplicitGamma.Variational
open scoped ENNReal
noncomputable section

/-- The outward full128 trace at child scale, keeping both the terminal
height offset and the two-generation root-relative exponent. -/
def nativeSourceChildFullResponseCap (gamma : ℝ) (height : ℕ) : ℝ :=
  4*((1009309/500000:ℝ)+gamma*(32474*((height:ℝ)+2)+11483216))*
    (3:ℝ)^((2*(height:ℝ)+8)*gamma)

/-- The actual child scalar trace is the literal attenuated physical full
trace in the same completed old frame. -/
theorem native_source_child_band_full_response_identity (M : ABKModel 2) (n : ℤ) (height : ℕ)
    (t : ℝ) (ω : Cutoff.CutoffSample 2) :
    modelTraceObservable (n-1) M.nu (Annealed.sigmaBar M n) (nativeSourceChildBandScalar n height t ω)+4 =
      nativeSourceFullResponseTrace M (originCube 2 (n-1)) n (n+(height:ℤ)) (fun _ => Real.sqrt t) ω := by
  have hae : responsePlanarCoefficientField M.nu
      (ContinuousMap.linearIsometryBoundedOfCompact (closure (cubeSet (originCube 2 (n-1)))) ℝ ℝ
        (nativeSourceChildBandScalar n height t ω)) =ᵐ[volume.restrict (cubeSet (originCube 2 (n-1)))]
      attenuatedCoefficient M n (n+(height:ℤ)) (fun _ => Real.sqrt t) ω :=
    (ae_restrict_mem (μ := volume) (measurableSet_cubeSet (originCube 2 (n-1)))).mono
      (fun x hx => native_source_child_band_coefficient_on_cube M n height t ω x hx)
  unfold modelTraceObservable
  rw [traceDefect_eq_framedTrace,coarseBlockMatrix_congr_of_ae_eq hae]
  unfold nativeSourceFullResponseTrace
  ring

/-- The actual attenuated full128 bank on the child cube uses only states
strictly before the old cutoff. No completed state at the terminal is needed. -/
theorem native_source_child_band_full_response_L128
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (n : ℤ) (height : ℕ)
    (hpast : ∀ j < n, nativeInductionState M h j) (t : ℝ) (ht1 : t ≤ 1) :
    eLpNorm (fun ω : Cutoff.CutoffSample 2 =>
      modelTraceObservable (n-1) M.nu (Annealed.sigmaBar M n) (nativeSourceChildBandScalar n height t ω)+4)
      128 (Cutoff.cutoffSampleLaw M).toMeasure ≤ ENNReal.ofReal (nativeSourceChildFullResponseCap M.gamma height) := by
  let Q := originCube 2 (n-1)
  let w : ℤ → ℝ := fun _ => Real.sqrt t
  have hw : ∀ j ∈ Finset.Ioc n (n+(height:ℤ)), 0 ≤ w j ∧ w j ≤ 1 :=
    fun _ _ => ⟨Real.sqrt_nonneg t,Real.sqrt_le_one.mpr ht1⟩
  have hh := full_response_bank128_outward M h hM hg Q
    (fun j hj => hpast j (by change j ≤ n-1-337 at hj; omega))
    (n+(height:ℤ)) n (by change n-1-1 ≤ n+(height:ℤ); omega)
    (sourceBandWeights n w)
    (source_band_weights_bounds (Q.scale-342) n (n+(height:ℤ)) w hw)
  have he : (fun ω => rootTraceObservable M Q (Q.scale-342) (n+(height:ℤ)) n
      (sourceBandWeights n w) ω/4) =
      (fun ω => nativeSourceFullResponseTrace M Q n (n+(height:ℤ)) w ω/4) := by
    funext ω
    unfold rootTraceObservable nativeSourceFullResponseTrace
    rw [full_response_coefficient_promote M _ n (n+(height:ℤ)) (by change n-1-342 ≤ n; omega) (by omega)]
  rw [he] at hh
  have hD : ((n+(height:ℤ):ℤ):ℝ)-(Q.scale:ℝ)+1=(height:ℝ)+2 := by
    change ((n+(height:ℤ):ℤ):ℝ)-((n-1:ℤ):ℝ)+1=(height:ℝ)+2
    push_cast
    ring
  have hgap : |((n-Q.scale+1:ℤ):ℝ)|=2 := by
    change |((n-(n-1)+1:ℤ):ℝ)|=2
    norm_num
  rw [hD,hgap,show ENNReal.ofReal (128:ℝ)=(128:ℝ≥0∞) by norm_num] at hh
  have hfun : nativeSourceFullResponseTrace M Q n (n+(height:ℤ)) w =
      (4:ℝ) • (fun ω => nativeSourceFullResponseTrace M Q n (n+(height:ℤ)) w ω/4) := by
    funext ω
    simp only [Pi.smul_apply,smul_eq_mul]
    ring
  have htrace : (fun ω : Cutoff.CutoffSample 2 =>
      modelTraceObservable (n-1) M.nu (Annealed.sigmaBar M n) (nativeSourceChildBandScalar n height t ω)+4) =
      nativeSourceFullResponseTrace M Q n (n+(height:ℤ)) w :=
    funext (native_source_child_band_full_response_identity M n height t)
  rw [htrace,hfun,eLpNorm_const_smul,Real.enorm_eq_ofReal (by norm_num : (0:ℝ)≤4)]
  apply (mul_le_mul' le_rfl hh).trans
  rw [←ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤4)]
  apply ENNReal.ofReal_le_ofReal
  unfold nativeSourceChildFullResponseCap
  have hexp : 2*M.gamma*((height:ℝ)+2)+2*M.gamma*2=(2*(height:ℝ)+8)*M.gamma := by ring
  rw [hexp]
  norm_num
  exact le_of_eq (by ring)

end
end ASDExplicitGamma.Native
