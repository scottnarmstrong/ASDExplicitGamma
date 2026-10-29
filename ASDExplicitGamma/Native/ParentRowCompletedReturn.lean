module

public import ASDExplicitGamma.Native.ParentRowFrames
public import ASDExplicitGamma.Native.ParentRowHeatReturn
public import ASDExplicitGamma.Native.ParentBoundaryFrameReturn

/-! True-frame restoration and exact certified comparison for the parent rows. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Gaussian Main Triadic Scalar Response Variational Algsuperdiff.Section3 Numerics.Native Set
noncomputable section

/-- Every selected frame is the exact structural endpoint factor. -/
theorem parent_row_frame_eq (j : Fin 16) :
    parentRowFrame j=(3:ℝ)^(2*gammaZero*((j.val+1:ℕ):ℝ)) := by
  fin_cases j <;> simp only [parentRowFrame,nativeConfiguredParentEndpoint,nativeParentEndpointCertificates,
    nativeParent001EndpointCertificate,nativeParent002EndpointCertificate,nativeParent003EndpointCertificate,nativeParent004EndpointCertificate,nativeParent005EndpointCertificate,nativeParent006EndpointCertificate,nativeParent007EndpointCertificate,nativeParent008EndpointCertificate,nativeParent009EndpointCertificate,nativeParent010EndpointCertificate,nativeParent011EndpointCertificate,nativeParent012EndpointCertificate,nativeParent013EndpointCertificate,nativeParent014EndpointCertificate,nativeParent015EndpointCertificate,nativeParent016EndpointCertificate,
    List.getD_cons_zero,List.getD_cons_succ]
  · simpa only [Nat.reduceAdd,Nat.cast_ofNat,Nat.cast_one] using parent_row_frame_001
  · simpa only [Nat.reduceAdd,Nat.cast_ofNat,Nat.cast_one] using parent_row_frame_002
  · simpa only [Nat.reduceAdd,Nat.cast_ofNat,Nat.cast_one] using parent_row_frame_003
  · simpa only [Nat.reduceAdd,Nat.cast_ofNat,Nat.cast_one] using parent_row_frame_004
  · simpa only [Nat.reduceAdd,Nat.cast_ofNat,Nat.cast_one] using parent_row_frame_005
  · simpa only [Nat.reduceAdd,Nat.cast_ofNat,Nat.cast_one] using parent_row_frame_006
  · simpa only [Nat.reduceAdd,Nat.cast_ofNat,Nat.cast_one] using parent_row_frame_007
  · simpa only [Nat.reduceAdd,Nat.cast_ofNat,Nat.cast_one] using parent_row_frame_008
  · simpa only [Nat.reduceAdd,Nat.cast_ofNat,Nat.cast_one] using parent_row_frame_009
  · simpa only [Nat.reduceAdd,Nat.cast_ofNat,Nat.cast_one] using parent_row_frame_010
  · simpa only [Nat.reduceAdd,Nat.cast_ofNat,Nat.cast_one] using parent_row_frame_011
  · simpa only [Nat.reduceAdd,Nat.cast_ofNat,Nat.cast_one] using parent_row_frame_012
  · simpa only [Nat.reduceAdd,Nat.cast_ofNat,Nat.cast_one] using parent_row_frame_013
  · simpa only [Nat.reduceAdd,Nat.cast_ofNat,Nat.cast_one] using parent_row_frame_014
  · simpa only [Nat.reduceAdd,Nat.cast_ofNat,Nat.cast_one] using parent_row_frame_015
  · simpa only [Nat.reduceAdd,Nat.cast_ofNat,Nat.cast_one] using parent_row_frame_016


/-- Nonnegativity of the exact structural frame. -/
theorem parent_row_frame_nonneg (j : Fin 16) : 0≤parentRowFrame j := by
  rw [parent_row_frame_eq]
  positivity

/-- Restore the actual completed frame, with no endpoint estimate premise. -/
theorem parent_row_completed_frame (M : ABKModel 2) (hg : M.gamma≤gammaZero)
    (m : ℤ) (j : Fin 16) :
    nativeCompletedSourceMean M m (j.val+1) ≤ ENNReal.ofReal
      (parentRowFrame j*nativeSourceBandMean M (m-((j.val+1:ℕ):ℤ)) (j.val+1) 1) := by
  let n := m-((j.val+1:ℕ):ℤ)
  have hframe : (3:ℝ)^(2*M.gamma*((j.val+1:ℕ):ℝ))≤parentRowFrame j := by
    rw [parent_row_frame_eq]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hg (by norm_num)) (Nat.cast_nonneg _))
  have hmean : 0≤nativeSourceBandMean M n (j.val+1) 1 := by
    apply integral_nonneg
    intro ω
    exact modelTraceObservable_nonneg n M.nu (Annealed.sigmaBar M n) M.nu_pos
      (Annealed.sigmaBar_characterization M n).1 _
  have hh := parent_boundary_completed_mean_frame M n (j.val+1)
  have hn : n+((j.val+1:ℕ):ℤ)=m := by dsimp [n]; omega
  rw [hn] at hh
  exact hh.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hframe hmean))

/-- All sixteen actual rows fit their exact caps once the physical generator
payment is supplied. This is an assembly helper, not the final theorem. -/
theorem parent_row_completed_bound_of_generator
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (m : ℤ)
    (hpast : ∀ k<m,nativeInductionState M h k) (j : Fin 16)
    (hrow : ∀ t ∈ Ioo (0:ℝ) 1,
      let n := m-((j.val+1:ℕ):ℤ)
      (∫ ω,nativeSourceBandMeanGenerator M h n (j.val+1) t ω
        ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
      theta M*(parentRowB0 j+nativePanelValue (parentRowFields j) t)-
        parentBoundaryBandDirichletEnergy M h n (j.val+1)*
          (parentBoundaryBandInverseMean M n (j.val+1) t-2)) :
    nativeCompletedSourceMean M m (j.val+1) ≤
      ENNReal.ofReal (theta M*((nativeBoundaryParentCaps.getD (j.val+1) 0:ℚ):ℝ)) := by
  have hr := parent_row_band_return_of_generator M h hM hg m hpast j hrow
  apply (parent_row_completed_frame M hg m j).trans
  apply ENNReal.ofReal_le_ofReal
  apply (mul_le_mul_of_nonneg_left hr (parent_row_frame_nonneg j)).trans
  have ht : 0≤theta M := div_nonneg M.shellPrefix.gamma_pos.le (by norm_num [gammaZero])
  have hn := mul_le_mul_of_nonneg_left (parent_row_endpoint_bound j) ht
  convert hn using 1
  ring

end
end ASDExplicitGamma.Native
