module

public import ASDExplicitGamma.Native.ParentBoundaryBandDepthBank

/-! Actual descendant inverse maxima and their depthwise OLD bank remainders. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Gaussian Inverse Algsuperdiff.Section3
open scoped ENNReal
noncomputable section

/-- The remainder of the actual depth-j descendant block maximum. -/
def parentBoundaryBandTiledDepthRemainder (M : ABKModel 2) (n : ℤ) (height : ℕ) (t : ℝ) (r j : ℕ) :
    Cutoff.CutoffSample 2 → ℝ :=
  inverseBankDepthBlockRemainder .localInverse (descendantsAtDepth (originCube 2 n) (r+j))
    M n (n+(height:ℤ)) (fun _ => Real.sqrt t) j

/-- The bank pays the whole depth-(r+j) tiling at local depth j.
Its existing population allowance already includes every source cell for r ≤ 5. -/
theorem parent_boundary_band_tiled_depth_block_bank
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (n : ℤ) (height : ℕ) (t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1)
    (hpast : ∀ l<n,nativeInductionState M h l) (r : ℕ) (hr : r ≤ 5) (j : ℕ) :
    InverseBankDepthBlockConclusion M .localInverse (descendantsAtDepth (originCube 2 n) (r+j))
      n (n+(height:ℤ)) (fun _ => Real.sqrt t) j := by
  have hscale : ∀ U ∈ descendantsAtDepth (originCube 2 n) (r+j),
      U.scale ≤ n-(j:ℤ) ∧ (n-(j:ℤ))-U.scale ≤ 5 := by
    intro U hU
    have hh := scale_eq_sub_of_mem_descendantsAtDepth hU
    change U.scale=n-((r+j:ℕ):ℤ) at hh
    omega
  have hcard : (descendantsAtDepth (originCube 2 n) (r+j)).card ≤ 6*9^(45+j) := by
    rw [descendantsAtDepth_card,show (3^2:ℕ)=9 by norm_num]
    exact (pow_le_pow_right₀ (by norm_num : (1:ℕ) ≤ 9)
      (by omega : r+j ≤ 45+j)).trans (by omega)
  exact inverse_bank_depth_block M h hM hg .localInverse _ n (n+(height:ℤ))
    (by omega) _ (fun _ _ => ⟨Real.sqrt_nonneg t,Real.sqrt_le_one.mpr ht.2⟩) j
    hscale hcard hpast (bank_inverse_mean_inputs_of_states M h hM hg n hpast).2

/-- The actual fixed-frame inverse maximum has the bank split, with its own
correlated depthwise remainder retained. -/
theorem parent_boundary_band_tiled_depth_inverse_split
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (n : ℤ) (height : ℕ) (t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1)
    (hpast : ∀ l<n,nativeInductionState M h l) (r : ℕ) (hr : r ≤ 5) (j : ℕ) :
    ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      lemmaVInverseDepthMax (originCube 2 n) (parentBoundaryBandFrameField M n height t ω) (r+j) ≤
        (inverseBankCap .localInverse:ℝ)*bankDepthFrame M j+
          parentBoundaryBandTiledDepthRemainder M n height t r j ω := by
  have hb := parent_boundary_band_tiled_depth_block_bank M h hM hg n height t ht hpast r hr j
  have hc : 0 ≤ (inverseBankCap .localInverse:ℝ)*bankDepthFrame M j :=
    mul_nonneg (by norm_num [inverseBankCap]) (bankDepthFrame_pos M j).le
  filter_upwards [hb.block_le] with ω hω
  rw [parent_boundary_band_inverse_depth_ennreal M n height t ω (r+j)] at hω
  rw [←ENNReal.ofReal_add hc (hb.remainder_nonneg ω)] at hω
  exact (ENNReal.ofReal_le_ofReal_iff (add_nonneg hc (hb.remainder_nonneg ω))).mp hω

end
end ASDExplicitGamma.Native
