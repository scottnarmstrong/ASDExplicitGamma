module

public import ASDExplicitGamma.Native.ParentWeakRareSeries
public import ASDExplicitGamma.Native.OldSignedSourceDirectionalPayment

/-! Sharp directional depth payments with the theta-linear rare reserve. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Cold Scalar Inverse Variational Algsuperdiff.Section3 Numerics.Inverse
open scoped ENNReal
noncomputable section

/-- Every source cell has the sharp half-trace baseline and the full correlated
rare payment at each depth, with bank and trace inputs supplied by native states. -/
theorem parent_weak_directional_depth_payment
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (n : ℤ) (height : ℕ) (hheight : 1≤height) (hh16 : height≤16) (r : ℕ) (hr : r ≤ 5)
    (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth (originCube 2 n) r)
    (t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1)
    (hpast : ∀ l<n,nativeInductionState M h l) (hstate : nativeInductionState M h n) (j : ℕ) (e : Vec 2) :
    let q := fun ω => vecDot e (matVecMul (oldSignedPairedDepthMatrix U j
      (parentBoundaryBandFrameField M n height t ω)) e)
    let b := fun ω => lemmaVInverseDepthMax U (parentBoundaryBandFrameField M n height t ω) j
    Integrable (fun ω => b ω*q ω) (Cutoff.cutoffSampleLaw M).toMeasure ∧
    (∫ ω,b ω*q ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
      ((inverseBankCap .localInverse:ℝ)*bankDepthFrame M j/2*
        (∫ ω,parentBoundaryBandCellTrace M n height t U j ω ∂(Cutoff.cutoffSampleLaw M).toMeasure)+
        inverseBankDepthReserve .localInverse M j*
          (parentWeakRareTraceCap M j))*vecNormSq e := by
  intro q b
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let R := parentBoundaryBandDepthRemainder M n height t U j
  let c := (inverseBankCap .localInverse:ℝ)*bankDepthFrame M j
  let C := parentWeakRareTraceCap M j
  let T := fun ω => parentBoundaryBandCellTrace M n height t U j ω
  have hscale : U.scale=n-(r:ℤ) := by
    simpa only [originCube] using scale_eq_sub_of_mem_descendantsAtDepth hU
  have hb := parent_boundary_band_depth_block_bank M h hM hg n height hpast t ht.2 r hr U hscale j
  have hT2 : eLpNorm T 2 μ ≤ ENNReal.ofReal C := by
    apply (parent_weak_cell_trace_L2 M h hM hg n height hheight hh16 hpast hstate r hr U hU t ht j).trans
      (ENNReal.ofReal_le_ofReal ?_)
    unfold C parentWeakRareTraceCap
    have hh := mul_le_mul_of_nonneg_right (by norm_num : (10:ℝ)^17≤10^20)
      (mul_nonneg (cold_theta_pos M).le (inv_nonneg.mpr (pow_nonneg inverse_history_discount_range.1.le j)))
    convert hh using 1 <;> ring
  have hC : 0 ≤ C := parent_weak_rare_trace_cap_nonneg M j
  have hε : 0 ≤ inverseBankDepthReserve .localInverse M j := by
    unfold inverseBankDepthReserve inverseBankReserve
    exact mul_nonneg (mul_nonneg (by norm_num) (bankDepthFrame_pos M j).le)
      (Real.rpow_nonneg (by norm_num) _)
  have hq := parent_boundary_band_directional_integrable M h hM n height hheight r U hU t j e
  have hq0 (ω) := (parent_boundary_band_directional_nonneg_le M n height r U hU t ω j e).1
  have hqT (ω) := (parent_boundary_band_directional_nonneg_le M n height r U hU t ω j e).2
  have hrare := old_signed_rare_directional_integrable_bound R T q
    (inverseBankDepthReserve .localInverse M j) C (vecNormSq e) 1 (by norm_num)
    hε hC (vecNormSq_nonneg e) hb.remainder_nonneg
    (fun omega => by
      unfold T parentBoundaryBandCellTrace descendantsAverage
      exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
        (Finset.sum_nonneg (fun V _ => parent_boundary_band_trace_nonneg M n height t V omega))) hq0 hqT
    hb.remainder_measurable.aestronglyMeasurable (parent_boundary_band_trace_sequence_integrable M h hM n height hheight r U hU t j).1
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
      parent_boundary_band_directional_mean M h hM n height hheight r U hU t j e
    rw [hmean]
    exact (add_le_add le_rfl hrare.2).trans_eq (by ring)
  have hsplit := parent_boundary_band_cell_inverse_split M h hM hg n height hpast t ht.2 r hr U hU j
  have hle : ∀ᵐ ω ∂μ,b ω*q ω ≤ (c+R ω)*q ω := by
    filter_upwards [hsplit] with ω hω
    exact mul_le_mul_of_nonneg_right hω (hq0 ω)
  have hbmeas : Measurable b := by
    have he : b=(fun omega => (bankFiniteRootResponseMax (descendantsAtDepth U j) M n
        (n+(height:ℤ)) (fun _ => Real.sqrt t) omega).toReal) := by
      funext omega
      rw [parent_boundary_band_cell_depth_max_eq M n height r t U hU omega j,
        ENNReal.toReal_ofReal (lemmaVInverseDepthMax_nonneg _ _ _)]
    rw [he]
    exact ENNReal.measurable_toReal.comp (history_finite_max_measurable
      (Finset.univ : Finset ↥(descendantsAtDepth U j))
      (fun V omega => ENNReal.ofReal (rootInverseResponse M V.1 n (n+(height:ℤ))
        (fun _ => Real.sqrt t) omega))
      (fun V => ENNReal.continuous_ofReal.measurable.comp
        (root_inverse_response_measurable M n (n+(height:ℤ)) (fun _ => Real.sqrt t) V.1)))
  have hi : Integrable (fun ω => b ω*q ω) μ := hmajor.mono_nonneg
    (hbmeas.aestronglyMeasurable.mul hq.1)
    (Filter.Eventually.of_forall (fun ω => mul_nonneg (lemmaVInverseDepthMax_nonneg _ _ _) (hq0 ω))) hle
  exact ⟨hi,(integral_mono_ae hi hmajor hle).trans hbound⟩

end
end ASDExplicitGamma.Native
