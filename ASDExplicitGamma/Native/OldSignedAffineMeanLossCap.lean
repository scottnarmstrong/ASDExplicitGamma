module

public import ASDExplicitGamma.Native.OldSignedFlatVariancePartition
public import ASDExplicitGamma.Native.OldSignedFlatProfileCaps

/-! The exact flat affine mean loss with the certified Poincaré allowance. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Gaussian Triadic Main
noncomputable section

/-- The difference of the two complete flat energies is precisely the
harmonic boundary energy retained by the signed generator. -/
theorem old_signed_flat_l2_difference (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0<l}) :
    oldSignedFlatL2Size Q Q b L true^2-oldSignedFlatL2Size Q Q b L false^2=
      oldSignedFlatBoundaryEnergy Q b L := by
  have hh := old_signed_joint_flat_l2_identity Q b L
  have hm : oldSignedFlatL2Size Q Q b L false^2=
      ∑' n,oldSignedFlatDirichletModeEnergy Q b L n := by
    rw [old_signed_flat_l2_size_sq]
    simp only [oldSignedFlatInput,Bool.false_eq_true,ite_false,old_signed_flat_minus_l2_mode]
  rw [oldSignedFlatBoundaryEnergy,(old_signed_flat_boundary_energy_trace Q b L).tsum_eq]
  rw [hm] at hh ⊢
  linarith only [hh]

/-- Both actual mean losses fit the affine allowance with its exact 31.2
covariance coefficient and the sharp cell Poincaré factor. -/
theorem old_signed_flat_mean_loss_pair_cap (Q : TriadicCube 2) (r : ℕ) (b : ℝ)
    (L : {l : ℝ // 0<l}) :
    oldSignedFlatMeanLoss Q r b L true+oldSignedFlatMeanLoss Q r b L false≤
      (4+2*Real.sqrt 2)*(31.2:ℝ)*((cubeScaleFactor Q/3^r)^2*b^2/L.val^2)/9 := by
  have hh := add_le_add (old_signed_flat_mean_loss_gradient_cap Q r b L true)
    (old_signed_flat_mean_loss_gradient_cap Q r b L false)
  simp only [ite_true,Bool.false_eq_true,ite_false,one_mul] at hh
  have hs : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  have hid : (cubeScaleFactor Q/(Real.pi*3^r))^2*((1+Real.sqrt 2)^2*mainFlatSigmaSq b L)+
      (cubeScaleFactor Q/(Real.pi*3^r))^2*mainFlatSigmaSq b L=
      ((cubeScaleFactor Q/3^r)/Real.pi)^2*((4+2*Real.sqrt 2)*mainFlatSigmaSq b L) := by
    rw [div_mul_eq_div_div]
    ring_nf
    rw [hs]
    ring
  rw [hid] at hh
  have hd : 0≤cubeScaleFactor Q/3^r := le_of_lt (by unfold cubeScaleFactor; positivity)
  have hp : ((cubeScaleFactor Q/3^r)/Real.pi)^2≤((cubeScaleFactor Q/3^r)/3)^2 :=
    pow_le_pow_left₀ (div_nonneg hd Real.pi_pos.le)
      (div_le_div_of_nonneg_left hd (by norm_num) Real.pi_gt_three.le) 2
  calc
    _ ≤ ((cubeScaleFactor Q/3^r)/Real.pi)^2*((4+2*Real.sqrt 2)*mainFlatSigmaSq b L) := hh
    _ ≤ ((cubeScaleFactor Q/3^r)/3)^2*((4+2*Real.sqrt 2)*mainFlatSigmaSq b L) :=
      mul_le_mul_of_nonneg_right hp (by unfold mainFlatSigmaSq; positivity)
    _ = _ := by unfold mainFlatSigmaSq; ring

end
end ASDExplicitGamma.Native
