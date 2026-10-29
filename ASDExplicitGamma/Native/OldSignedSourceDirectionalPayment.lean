module

public import ASDExplicitGamma.Native.OldSignedSourceInverseSplit
public import ASDExplicitGamma.Native.OldSignedSourceDirectionalLaw

/-! Correlated inverse-weighted directional payments on the actual OLD source cells. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Scalar Inverse Variational Algsuperdiff.Section3 Numerics.Inverse
open scoped ENNReal
noncomputable section

/-- Every source cell has the sharp half-trace baseline and the full correlated
rare payment at each depth, with bank and trace inputs supplied by native states. -/
theorem old_signed_source_directional_payment
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (n : ℤ) (r : ℕ) (hr : r ≤ 5)
    (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth (originCube 2 n) r)
    (t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1)
    (hstates : ∀ l ≤ n,nativeInductionState M h l) (j : ℕ) (e : Vec 2) :
    let q := fun ω => vecDot e (matVecMul (oldSignedPairedDepthMatrix U j
      (oldSignedPartialFrameField M n 1 t ω)) e)
    let b := fun ω => lemmaVInverseDepthMax U (oldSignedPartialFrameField M n 1 t ω) j
    Integrable (fun ω => b ω*q ω) (Cutoff.cutoffSampleLaw M).toMeasure ∧
    (∫ ω,b ω*q ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
      ((inverseBankCap .localInverse:ℝ)*bankDepthFrame M j/2*
        (∫ ω,rawWeakTraceSequence M n U t ω j ∂(Cutoff.cutoffSampleLaw M).toMeasure)+
        inverseBankDepthReserve .localInverse M j*
          (theta M*(invTraceM:ℝ)*(1+(j:ℝ))^2*(3:ℝ)^(6*gammaZero*j)))*vecNormSq e := by
  intro q b
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let R := oldSignedSourceDepthRemainder M n t U j
  let c := (inverseBankCap .localInverse:ℝ)*bankDepthFrame M j
  let C := theta M*(invTraceM:ℝ)*(1+(j:ℝ))^2*(3:ℝ)^(6*gammaZero*j)
  let T := fun ω => rawWeakTraceSequence M n U t ω j
  have hscale : U.scale=n-(r:ℤ) := by
    simpa only [originCube] using scale_eq_sub_of_mem_descendantsAtDepth hU
  have hb := old_signed_source_depth_block_bank M h hM hg n t ht
    (fun l hl => hstates l hl.le) r hr U hscale j
  have hT2 := old_signed_source_cell_trace_sequence_L2 M h hM hg n r hr t ht hstates U hscale j
  have htheta : 0 ≤ theta M := div_nonneg M.shellPrefix.gamma_pos.le (by norm_num [gammaZero])
  have hMrat : 0 ≤ invTraceM := by rw [invTrace_coefficient.1]; positivity
  have hM0 : 0 ≤ (invTraceM:ℝ) := by exact_mod_cast hMrat
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hε : 0 ≤ inverseBankDepthReserve .localInverse M j := by
    unfold inverseBankDepthReserve inverseBankReserve
    exact mul_nonneg (mul_nonneg (by norm_num) (bankDepthFrame_pos M j).le)
      (Real.rpow_nonneg (by norm_num) _)
  have hq := old_signed_source_directional_integrable M n r U hU t ht j e
  have hq0 (ω) := (old_signed_source_directional_nonneg_le M n r U hU t ω j e).1
  have hqT (ω) := (old_signed_source_directional_nonneg_le M n r U hU t ω j e).2
  have hrare := old_signed_rare_directional_integrable_bound R T q
    (inverseBankDepthReserve .localInverse M j) C (vecNormSq e) 1 (by norm_num)
    hε hC (vecNormSq_nonneg e) hb.remainder_nonneg
    (fun ω => raw_weak_trace_sequence_nonneg M n U t ht ω j) hq0 hqT
    hb.remainder_measurable.aestronglyMeasurable (old_signed_source_trace_integrable M n U t ht j).1
    hq.1 hb.remainder_L128 hT2
  simp only [pow_one] at hrare
  have hmajor : Integrable (fun ω => (c+R ω)*q ω) μ := by
    simp_rw [add_mul]
    exact (hq.const_mul c).add hrare.1
  have hbound : (∫ ω,(c+R ω)*q ω ∂μ) ≤
      (c/2*(∫ ω,T ω ∂μ)+inverseBankDepthReserve .localInverse M j*C)*vecNormSq e := by
    simp_rw [add_mul]
    rw [integral_add (hq.const_mul c) hrare.1,integral_const_mul]
    have hmean : (∫ ω,q ω ∂μ)=(1/2:ℝ)*(∫ ω,T ω ∂μ)*vecNormSq e :=
      old_signed_source_directional_mean M n r U hU t ht j e
    rw [hmean]
    exact (add_le_add le_rfl hrare.2).trans_eq (by ring)
  have hsplit := old_signed_source_inverse_split M h hM hg n t ht
    (fun l hl => hstates l hl.le) r hr U hU j
  have hle : ∀ᵐ ω ∂μ,b ω*q ω ≤ (c+R ω)*q ω := by
    filter_upwards [hsplit] with ω hω
    exact mul_le_mul_of_nonneg_right hω (hq0 ω)
  have hi : Integrable (fun ω => b ω*q ω) μ := hmajor.mono_nonneg
    ((old_signed_source_inverse_measurable M n r U hU t ht j).aestronglyMeasurable.mul hq.1)
    (Filter.Eventually.of_forall (fun ω => mul_nonneg (lemmaVInverseDepthMax_nonneg _ _ _) (hq0 ω))) hle
  exact ⟨hi,(integral_mono_ae hi hmajor hle).trans hbound⟩

end
end ASDExplicitGamma.Native
