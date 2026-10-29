module

public import ASDExplicitGamma.Native.GenericSourceFullResponse
public import ASDExplicitGamma.Inverse.HybridFullTraceComparison
public import ASDExplicitGamma.Inverse.GoodCellResponse
public import ASDExplicitGamma.Inverse.FullResponseTrace
public import ASDExplicitGamma.Inverse.FullResponseAttenuatedBank

/-! The exact attenuated full-trace input from IN-FULL-RESPONSE-BANK, in the
concrete form consumed by the generic source profiles. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Inverse
open ASDExplicitGamma.Response ASDExplicitGamma.Variational
open scoped ENNReal

/-- The unnormalized full response trace in the completed `m` frame for an
actual deterministic attenuation. -/
noncomputable def nativeSourceFullResponseTrace
    (M : ABKModel 2) (Q : TriadicCube 2) (m J : ℤ)
    (weights : ℤ → ℝ) (ω : Cutoff.CutoffSample 2) : ℝ :=
  Matrix.trace (toFullBlockMat (frameMatrix (Annealed.sigmaBar M m : ℝ)
    (coarseBlockMatrix (cubeSet Q) (attenuatedCoefficient M m J weights ω))))

/-- The actual completed-law attenuation satisfies the p128 bank using only
states strictly earlier than its completed base. No response estimate is an
input premise; the protected root prefix is supplied from that earlier past. -/
theorem native_source_full_response_L128_actual
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (Q : TriadicCube 2) (height : ℕ)
    (hpast : ∀ n < Q.scale, nativeInductionState M h n)
    (weights : ℤ → ℝ)
    (hw : ∀ j ∈ Finset.Ioc Q.scale (Q.scale+(height:ℤ)), 0 ≤ weights j ∧ weights j ≤ 1) :
    eLpNorm (nativeSourceFullResponseTrace M Q Q.scale (Q.scale+(height:ℤ)) weights)
      (ENNReal.ofReal 128) (Cutoff.cutoffSampleLaw M).toMeasure ≤
        ENNReal.ofReal (rawTraceFullResponseCap M.gamma height) := by
  have hh := full_response_bank128_outward M h hM hg Q
    (fun n hn => hpast n (by omega)) (Q.scale+(height:ℤ)) Q.scale (by omega)
    (sourceBandWeights Q.scale weights)
    (source_band_weights_bounds (Q.scale-342) Q.scale (Q.scale+(height:ℤ)) weights hw)
  dsimp only at hh
  have he : (fun ω => rootTraceObservable M Q (Q.scale-342) (Q.scale+(height:ℤ)) Q.scale
      (sourceBandWeights Q.scale weights) ω/4) =
      (fun ω => nativeSourceFullResponseTrace M Q Q.scale (Q.scale+(height:ℤ)) weights ω/4) := by
    funext ω
    unfold rootTraceObservable nativeSourceFullResponseTrace
    rw [full_response_coefficient_promote M _ Q.scale (Q.scale+(height:ℤ)) (by omega) (by omega)]
  rw [he] at hh
  have hD : ((Q.scale+(height:ℤ):ℤ):ℝ)-(Q.scale:ℝ)+1=(height:ℝ)+1 := by
    push_cast
    ring
  rw [hD,sub_self,zero_add,Int.cast_one,abs_one] at hh
  have hfun : nativeSourceFullResponseTrace M Q Q.scale (Q.scale+(height:ℤ)) weights =
      (4:ℝ) • (fun ω => nativeSourceFullResponseTrace M Q Q.scale (Q.scale+(height:ℤ)) weights ω/4) := by
    funext ω
    simp only [Pi.smul_apply,smul_eq_mul]
    ring
  rw [hfun,eLpNorm_const_smul,Real.enorm_eq_ofReal (by norm_num : (0:ℝ)≤4)]
  apply (mul_le_mul' le_rfl hh).trans
  rw [← ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤4),raw_trace_full_response_cap_eq_profile]
  apply ENNReal.ofReal_le_ofReal
  unfold fullResponseAttenuatedOutwardProfile
  have hexp : 2*M.gamma*((height:ℝ)+1)+2*M.gamma*1 = (2*(height:ℝ)+4)*M.gamma := by ring
  rw [hexp]
  exact le_of_eq (by ring)

end ASDExplicitGamma.Native
