module

public import ASDExplicitGamma.Inverse.FullResponseExports
public import ASDExplicitGamma.Inverse.RawShellBankCaps

/-! The actual unnormalized p=128 attenuation bank used by the later estimates and SHEAR. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Model ASDExplicitGamma.Variational
open scoped ENNReal
noncomputable section

/-- The complete deterministic-attenuation version of the source f_h bank.
The full trace is used here, so the source factor four is retained. -/
theorem full_response_attenuated_bank128
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (Q : TriadicCube 2) (height : ℕ) (m : ℤ)
    (hm : Q.scale-342 ≤ m) (hmN : m ≤ Q.scale+(height:ℤ))
    (hpast : ∀ n ≤ Q.scale+(height:ℤ)-303, nativeInductionState M h n)
    (weights : ℤ → ℝ)
    (hw : ∀ j ∈ Finset.Ioc m (Q.scale+(height:ℤ)), 0 ≤ weights j ∧ weights j ≤ 1) :
    eLpNorm (rootTraceObservable M Q m (Q.scale+(height:ℤ)) Q.scale weights)
      (ENNReal.ofReal 128) (Cutoff.cutoffSampleLaw M).toMeasure ≤
        ENNReal.ofReal (rawTraceFullResponseCap M.gamma height) := by
  have hh := full_response_completed_bank128 M h hM hg Q
    (Q.scale+(height:ℤ)) Q.scale m (by omega) hm hmN hpast weights hw
  dsimp only at hh
  have hD : ((Q.scale+(height:ℤ):ℤ):ℝ)-(Q.scale:ℝ)+1=(height:ℝ)+1 := by
    push_cast
    ring
  rw [hD,sub_self,zero_add,Int.cast_one,abs_one] at hh
  have he : rootTraceObservable M Q m (Q.scale+(height:ℤ)) Q.scale weights =
      (4:ℝ) • (fun ω => rootTraceObservable M Q m (Q.scale+(height:ℤ)) Q.scale weights ω/4) := by
    funext ω
    simp only [Pi.smul_apply,smul_eq_mul]
    ring
  rw [he,eLpNorm_const_smul,Real.enorm_eq_ofReal (by norm_num : (0:ℝ)≤4)]
  apply (mul_le_mul' le_rfl hh).trans
  rw [← ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤4),raw_trace_full_response_cap_eq_profile]
  apply ENNReal.ofReal_le_ofReal
  unfold fullResponseAttenuatedOutwardProfile
  have hexp : 2*M.gamma*((height:ℝ)+1)+2*M.gamma*1 = (2*(height:ℝ)+4)*M.gamma := by ring
  rw [hexp]
  exact le_of_eq (by ring)

/-- The literal partial-shell law a_(K+h-1)+sqrt(s) j_(K+h) satisfies
f_h uniformly on s∈[0,1], in the same true K frame. -/
theorem full_response_partial_bank128
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (Q : TriadicCube 2) (height : ℕ)
    (hpast : ∀ n ≤ Q.scale+(height:ℤ)-303, nativeInductionState M h n)
    (s : ℝ) (hs : s ∈ Set.Icc (0:ℝ) 1) :
    eLpNorm (fun ω => Matrix.trace (toFullBlockMat (frameMatrix (Annealed.sigmaBar M Q.scale:ℝ)
      (coarseBlockMatrix (cubeSet Q) (fun x =>
        Cutoff.coefficientCutoff M.nu (Q.scale+(height:ℤ)-1) ω x+
          Real.sqrt s • (ω.val (Q.scale+(height:ℤ))).forgetShell x)))))
      (ENNReal.ofReal 128) (Cutoff.cutoffSampleLaw M).toMeasure ≤
        ENNReal.ofReal (rawTraceFullResponseCap M.gamma height) := by
  have hh := full_response_attenuated_bank128 M h hM hg Q height (Q.scale+(height:ℤ)-1)
    (by omega) (by omega) hpast (fun _ => Real.sqrt s)
    (by intro j _; exact ⟨Real.sqrt_nonneg s,(Real.sqrt_le_one).mpr hs.2⟩)
  have he : rootTraceObservable M Q (Q.scale+(height:ℤ)-1) (Q.scale+(height:ℤ)) Q.scale
      (fun _ => Real.sqrt s) =
      (fun ω => Matrix.trace (toFullBlockMat (frameMatrix (Annealed.sigmaBar M Q.scale:ℝ)
        (coarseBlockMatrix (cubeSet Q) (fun x =>
          Cutoff.coefficientCutoff M.nu (Q.scale+(height:ℤ)-1) ω x+
            Real.sqrt s • (ω.val (Q.scale+(height:ℤ))).forgetShell x))))) := by
    funext ω
    unfold rootTraceObservable
    rw [full_response_coefficient_partial]
  rw [he] at hh
  exact hh

end
end ASDExplicitGamma.Inverse
