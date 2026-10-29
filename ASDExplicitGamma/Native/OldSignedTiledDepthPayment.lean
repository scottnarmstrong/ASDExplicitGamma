module

public import ASDExplicitGamma.Native.OldSignedTiledDepthBank
public import ASDExplicitGamma.Native.OldSignedTiledTraceLaw
public import ASDExplicitGamma.Native.OldSignedSourceHistoryStationarity

/-! Correlated depthwise payment for the whole OLD source tiling. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Scalar Variational Inverse Algsuperdiff.Section3 Numerics.Inverse
noncomputable section

/-- The shifted parent trace and the local source trace have the same mean. -/
theorem old_signed_tiled_trace_mean_eq (M : ABKModel 2) (n : ℤ) (r j : ℕ)
    (t : ℝ) (ht : 0≤t ∧ t≤1) :
    (∫ ω,rawWeakTraceSequence M n (originCube 2 n) t ω (r+j)
      ∂(Cutoff.cutoffSampleLaw M).toMeasure)=
    ∫ ω,rawWeakTraceSequence M n (originCube 2 (n-(r:ℤ))) t ω j
      ∂(Cutoff.cutoffSampleLaw M).toMeasure := by
  rw [old_signed_source_trace_mean_eq_depth M n _ t ht (r+j),
    old_signed_source_trace_mean_eq_depth M n _ t ht j]
  congr 1
  funext ω
  congr 1
  change n-((r+j:ℕ):ℤ)=n-(r:ℤ)-(j:ℤ)
  push_cast
  ring

/-- The genuine inverse maximum times the whole tiled trace is integrable.
Twice the common directional budget pays its deterministic trace term and
the correlated reserve, with room for one further rare payment. -/
theorem old_signed_tiled_depth_payment
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (n : ℤ) (r : ℕ) (hr : r ≤ 5)
    (t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1)
    (hstates : ∀ l ≤ n,nativeInductionState M h l) (j : ℕ) :
    let b := fun ω => lemmaVInverseDepthMax (originCube 2 n)
      (oldSignedPartialFrameField M n 1 t ω) (r+j)
    let T := fun ω => rawWeakTraceSequence M n (originCube 2 n) t ω (r+j)
    Integrable (fun ω => b ω*T ω) (Cutoff.cutoffSampleLaw M).toMeasure ∧
      (∫ ω,b ω*T ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
        2*oldSignedSourceHistoryBudget M n (originCube 2 (n-(r:ℤ))) t j := by
  intro b T
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let R := oldSignedTiledDepthRemainder M n t r j
  let c := (inverseBankCap .localInverse:ℝ)*bankDepthFrame M j
  let C := theta M*(invTraceM:ℝ)*(1+(j:ℝ))^2*(3:ℝ)^(6*gammaZero*j)
  let ε := inverseBankDepthReserve .localInverse M j
  have hb := old_signed_tiled_depth_block_bank M h hM hg n t ht
    (fun l hl => hstates l hl.le) r hr j
  have hT := old_signed_actual_trace_depth_integrable M n t ht (r+j)
  have hT0 (ω) : 0 ≤ T ω := raw_weak_trace_sequence_nonneg M n _ t ht ω (r+j)
  have hT2 := old_signed_tiled_trace_sequence_L2 M h hM hg n r hr t ht hstates j
  have htheta : 0 ≤ theta M := div_nonneg M.shellPrefix.gamma_pos.le (by norm_num [gammaZero])
  have hMrat : 0 ≤ invTraceM := by rw [invTrace_coefficient.1]; positivity
  have hM0 : 0 ≤ (invTraceM:ℝ) := by exact_mod_cast hMrat
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hε : 0 ≤ ε := by
    unfold ε inverseBankDepthReserve inverseBankReserve
    exact mul_nonneg (mul_nonneg (by norm_num) (bankDepthFrame_pos M j).le)
      (Real.rpow_nonneg (by norm_num) _)
  have hrare := old_signed_rare_trace_integrable_bound R T ε C 1 (by norm_num) hε hC
    hb.remainder_nonneg hT0 hb.remainder_measurable.aestronglyMeasurable hT.1 hb.remainder_L128 hT2
  simp only [pow_one] at hrare
  have hmajor : Integrable (fun ω => (c+R ω)*T ω) μ := by
    simp_rw [add_mul]
    exact (hT.const_mul c).add hrare.1
  have hsplit := old_signed_tiled_depth_inverse_split M h hM hg n t ht
    (fun l hl => hstates l hl.le) r hr j
  have hle : ∀ᵐ ω ∂μ,b ω*T ω ≤ (c+R ω)*T ω := by
    filter_upwards [hsplit] with ω hω
    exact mul_le_mul_of_nonneg_right hω (hT0 ω)
  have hi : Integrable (fun ω => b ω*T ω) μ := hmajor.mono_nonneg
    ((old_signed_depth_inverse_measurable M n t ht (r+j)).aestronglyMeasurable.mul hT.1)
    (Filter.Eventually.of_forall (fun ω => mul_nonneg (lemmaVInverseDepthMax_nonneg _ _ _) (hT0 ω))) hle
  refine ⟨hi,(integral_mono_ae hi hmajor hle).trans ?_⟩
  simp_rw [add_mul]
  rw [integral_add (hT.const_mul c) hrare.1,integral_const_mul]
  have hmean := old_signed_tiled_trace_mean_eq M n r j t ht
  change (∫ ω,T ω ∂μ)=_ at hmean
  rw [hmean]
  unfold oldSignedSourceHistoryBudget
  dsimp only [c,ε,C] at hrare ⊢
  linarith only [hrare.2,mul_nonneg hε hC]

end
end ASDExplicitGamma.Native
