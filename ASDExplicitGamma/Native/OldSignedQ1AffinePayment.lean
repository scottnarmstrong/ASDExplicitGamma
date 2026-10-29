module

public import ASDExplicitGamma.Native.OldSignedAffineMeanLossCap
public import ASDExplicitGamma.Native.OldSignedAffineTraceMeans
public import ASDExplicitGamma.Main.AffineScalarReduction

/-! Source-derived stationary affine payment for the actual OLD q1 panel. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Gaussian Triadic Main Inverse Cold Algsuperdiff.Section3
noncomputable section

/-- The actual affine expectation is paid by the depth-five trace mean,
the unchanged inverse bank and the sharp flat mean-loss allowance. -/
theorem old_signed_q1_affine_payment_at_depth
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (n : ℤ)
    (hpast : ∀ l≤n,nativeInductionState M h l)
    (r : ℕ) (hr : r=5) (t : ℝ) (ht : 0≤t ∧ t≤1) (b : ℝ) (L : {l : ℝ // 0<l}) :
    (∫ ω,oldSignedFlatAffineContribution (originCube 2 n) r
      (oldSignedPartialFrameField M n 1 t ω) b L ∂(Cutoff.cutoffSampleLaw M).toMeasure)≤
      (b^2/2)*(theta M*oldSignedQ1PanelMean t)+2*b^2*((3683/2500:ℝ)-1)+
      (4+2*Real.sqrt 2)*(31.2:ℝ)*((cubeScaleFactor (originCube 2 n)/3^r)^2*b^2/L.val^2)/9 := by
  let Q := originCube 2 n
  obtain ⟨U,hU⟩ := descendantsAtDepth_nonempty Q r
  have hscale : U.scale=n-5 := by
    have hs := scale_eq_sub_of_mem_descendantsAtDepth hU
    change U.scale=n-(r:ℤ) at hs
    simpa only [hr,Nat.cast_ofNat] using hs
  have hp := (parent_boundary_band_block_mean M h hM n 1 (by norm_num) r U hU t true).1
  have hq := (parent_boundary_band_block_mean M h hM n 1 (by norm_num) r U hU t false).1
  have hbank := old_signed_affine_inverse_scalar_le M h hM hg n
    (fun l hl => hpast l hl.le) r (by omega) U hU t ht
  have htrace := old_signed_affine_block_trace_mean M h hM n r U hU t ht
  rw [old_signed_q1_source_mean_eq M n U hscale t ht 0] at htrace
  simp only [Nat.add_zero] at htrace
  rw [old_signed_block_mean_eq_depth M n r U hU t true] at hp htrace
  rw [old_signed_block_mean_eq_depth M n r U hU t false] at hq hbank htrace
  have hmean := old_signed_actual_q1_panel_mean M h hM hg n hpast t ht
  have hmean0 : 0≤theta M*oldSignedQ1PanelMean t := by
    unfold oldSignedQ1PanelMean
    exact mul_nonneg (cold_theta_pos M).le (add_nonneg
      (le_trans (by norm_num) old_signed_q1_mean_setup_lower.1)
      (mul_nonneg ht.1 (le_trans (by norm_num) old_signed_q1_mean_setup_lower.2.1)))
  apply main_affine_scalar_reduction (b^2) (oldSignedFlatBoundaryEnergy Q b L) (2*b^2)
    (3683/2500) (theta M*oldSignedQ1PanelMean t) (inSourceMeanActual M n 5 t)
    (2*parentBoundaryBandBlockMean M n 1 t (originCube 2 (n-(r:ℤ))) false)
    (parentBoundaryBandBlockMean M n 1 t (originCube 2 (n-(r:ℤ))) true-1)
    (parentBoundaryBandBlockMean M n 1 t (originCube 2 (n-(r:ℤ))) false-1)
    (oldSignedFlatL2Size Q Q b L true^2) (oldSignedFlatL2Size Q Q b L false^2)
    (descendantsAverage Q r (fun U => oldSignedFlatMeanSize Q U b L true^2))
    (descendantsAverage Q r (fun U => oldSignedFlatMeanSize Q U b L false^2))
    (oldSignedFlatMeanLoss Q r b L true) (oldSignedFlatMeanLoss Q r b L false) _
    ((cubeScaleFactor Q/3^r)^2*b^2/L.val^2)
    (old_signed_flat_boundary_energy_bounds Q b L).1
    (old_signed_flat_boundary_energy_bounds Q b L).2 (le_refl _) (by norm_num) hmean0 hmean
    (by linarith only [hbank]) (by linarith only [hp]) (by linarith only [hq])
    htrace (by ring) (old_signed_joint_flat_l2_identity Q b L)
    (old_signed_flat_l2_difference Q b L)
    (old_signed_flat_mean_partition_identity Q r b L true)
    (old_signed_flat_mean_partition_identity Q r b L false)
    (old_signed_flat_mean_loss_nonneg Q r b L true)
    (old_signed_flat_mean_loss_nonneg Q r b L false)
    (old_signed_affine_scalar_expectation M h hM n r t b L)
    (old_signed_flat_mean_loss_pair_cap Q r b L)

/-- The source depth-five affine payment, with every estimate supplied internally. -/
theorem old_signed_q1_affine_payment
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (n : ℤ)
    (hpast : ∀ l≤n,nativeInductionState M h l)
    (t : ℝ) (ht : 0≤t ∧ t≤1) (b : ℝ) (L : {l : ℝ // 0<l}) :
    (∫ ω,oldSignedFlatAffineContribution (originCube 2 n) 5
      (oldSignedPartialFrameField M n 1 t ω) b L ∂(Cutoff.cutoffSampleLaw M).toMeasure)≤
      (b^2/2)*(theta M*oldSignedQ1PanelMean t)+2*b^2*((3683/2500:ℝ)-1)+
      (4+2*Real.sqrt 2)*(31.2:ℝ)*((cubeScaleFactor (originCube 2 n)/3^5)^2*b^2/L.val^2)/9 :=
  old_signed_q1_affine_payment_at_depth M h hM hg n hpast 5 rfl t ht b L

end
end ASDExplicitGamma.Native
