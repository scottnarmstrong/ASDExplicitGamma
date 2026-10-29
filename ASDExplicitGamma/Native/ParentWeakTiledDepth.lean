module

public import ASDExplicitGamma.Native.ParentBoundaryBandTiledDepthBank
public import ASDExplicitGamma.Native.ParentBoundaryBandHistoryStationarity
public import ASDExplicitGamma.Native.ParentWeakRareSeries

/-! Correlated depthwise payment for the whole OLD source tiling. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Scalar Variational Inverse Algsuperdiff.Section3 Numerics.Inverse
noncomputable section

/-- Whole-tiling depth payment retaining the full leading trace mean and a theta-scaled correlated remainder. -/
theorem parent_weak_tiled_depth_payment
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (n : ℤ) (height : ℕ) (hheight : 1≤height) (hh16 : height≤16) (r : ℕ) (hr : r ≤ 5)
    (U0 : TriadicCube 2) (hU0 : U0∈descendantsAtDepth (originCube 2 n) r)
    (t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1)
    (hpast : ∀ l<n,nativeInductionState M h l) (hstate : nativeInductionState M h n) (j : ℕ) :
    let b := fun ω => lemmaVInverseDepthMax (originCube 2 n)
      (parentBoundaryBandFrameField M n height t ω) (r+j)
    let T := fun ω => parentBoundaryBandCellTrace M n height t (originCube 2 n) (r+j) ω
    Integrable (fun ω => b ω*T ω) (Cutoff.cutoffSampleLaw M).toMeasure ∧
      (∫ ω,b ω*T ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
        (inverseBankCap .localInverse:ℝ)*bankDepthFrame M j*
          (∫ ω,parentBoundaryBandCellTrace M n height t U0 j ω ∂(Cutoff.cutoffSampleLaw M).toMeasure)+
          inverseBankDepthReserve .localInverse M j*parentWeakRareTraceCap M j := by
  intro b T
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let R := parentBoundaryBandTiledDepthRemainder M n height t r j
  let c := (inverseBankCap .localInverse:ℝ)*bankDepthFrame M j
  let C := parentWeakRareTraceCap M j
  let ε := inverseBankDepthReserve .localInverse M j
  have hb := parent_boundary_band_tiled_depth_block_bank M h hM hg n height t ht hpast r hr j
  have hT := parent_boundary_band_trace_sequence_integrable M h hM n height hheight 0
    (originCube 2 n) (by simp [descendantsAtDepth_zero]) t (r+j)
  have hT0 (ω) : 0 ≤ T ω := by
    unfold T parentBoundaryBandCellTrace descendantsAverage
    exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
      (Finset.sum_nonneg (fun V _ => parent_boundary_band_trace_nonneg M n height t V ω))
  have hT2 := parent_weak_tiled_trace_L2 M h hM hg n height hheight hh16 hpast hstate r hr t ht j
  have hC : 0≤C := parent_weak_rare_trace_cap_nonneg M j
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
  have hsplit := parent_boundary_band_tiled_depth_inverse_split M h hM hg n height t ht hpast r hr j
  have hle : ∀ᵐ ω ∂μ,b ω*T ω ≤ (c+R ω)*T ω := by
    filter_upwards [hsplit] with ω hω
    exact mul_le_mul_of_nonneg_right hω (hT0 ω)
  have hbmeas : Measurable b := by
    have hm := history_finite_max_measurable (Finset.univ : Finset ↥(descendantsAtDepth (originCube 2 n) (r+j)))
      (fun V omega => ENNReal.ofReal (rootInverseResponse M V.1 n (n+(height:ℤ)) (fun _ => Real.sqrt t) omega))
      (fun V => ENNReal.continuous_ofReal.measurable.comp
        (root_inverse_response_measurable M n (n+(height:ℤ)) (fun _ => Real.sqrt t) V.1))
    have he : b=(fun omega => (bankFiniteRootResponseMax (descendantsAtDepth (originCube 2 n) (r+j))
        M n (n+(height:ℤ)) (fun _ => Real.sqrt t) omega).toReal) := by
      funext omega
      rw [parent_boundary_band_inverse_depth_ennreal,ENNReal.toReal_ofReal (lemmaVInverseDepthMax_nonneg _ _ _)]
    rw [he]
    exact ENNReal.measurable_toReal.comp hm
  have hi : Integrable (fun ω => b ω*T ω) μ := hmajor.mono_nonneg
    (hbmeas.aestronglyMeasurable.mul hT.1)
    (Filter.Eventually.of_forall (fun ω => mul_nonneg (lemmaVInverseDepthMax_nonneg _ _ _) (hT0 ω))) hle
  refine ⟨hi,(integral_mono_ae hi hmajor hle).trans ?_⟩
  simp_rw [add_mul]
  rw [integral_add (hT.const_mul c) hrare.1,integral_const_mul]
  have hmean : (∫ omega,parentBoundaryBandCellTrace M n height t (originCube 2 n) (r+j) omega ∂μ)=
      ∫ omega,parentBoundaryBandCellTrace M n height t U0 j omega ∂μ := by
    rw [parent_boundary_band_trace_mean_depth M h hM n height hheight 0 (originCube 2 n)
      (by simp [descendantsAtDepth_zero]),
      parent_boundary_band_trace_mean_depth M h hM n height hheight r U0 hU0]
    simp only [Nat.cast_zero,sub_zero,Nat.cast_add,sub_add_eq_sub_sub]
  change (∫ ω,T ω ∂μ)=_ at hmean
  rw [hmean]
  exact add_le_add le_rfl hrare.2

end
end ASDExplicitGamma.Native
