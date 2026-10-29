module

public import ASDExplicitGamma.Scalar.UpperCellEnergyEndpointCertificate
public import ASDExplicitGamma.Scalar.UpperCellEnergySignal

/-! The precise physical floor-block allowance is dominated by NU-SC-UPPER-ERROR. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Algsuperdiff.Section3
open ASDExplicitGamma.Numerics.Scalar ASDExplicitGamma.Numerics.Mirror
noncomputable section

/-- Natural block height and its source integer floor define the same scale. -/
theorem upper_cell_physical_block_range (M : ABKModel 2) (hg : M.gamma ≤ gammaZero) :
    0 ≤ M.gamma*(⌊(17/50:ℝ)/M.gamma⌋.toNat:ℝ) ∧
      M.gamma*(⌊(17/50:ℝ)/M.gamma⌋.toNat:ℝ) ≤ 17/50 := by
  have hf : 0 ≤ ⌊(17/50:ℝ)/M.gamma⌋ := Int.floor_nonneg.mpr
    (div_nonneg (by norm_num) M.shellPrefix.gamma_pos.le)
  have he : (⌊(17/50:ℝ)/M.gamma⌋.toNat:ℝ) = (⌊(17/50:ℝ)/M.gamma⌋:ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hf
  rw [he]
  have hb := frame_floor_bounds M.gamma M.shellPrefix.gamma_pos hg
  exact ⟨le_trans (by norm_num : (0:ℝ)≤16983/50000) hb.1.le,hb.2⟩

/-- The error used in the actual projected-cell triangle is bounded directly
by the exact certified expression, and hence strictly below 681/10000. -/
theorem upper_cell_physical_error_certificate (M : ABKModel 2) (hg : M.gamma ≤ gammaZero) :
    upperCellErrorProfile M.gamma (M.gamma*(⌊(17/50:ℝ)/M.gamma⌋.toNat:ℝ)) ≤
      evalReal scalarRealEnv upperErrorExpr ∧
    upperCellErrorProfile M.gamma (M.gamma*(⌊(17/50:ℝ)/M.gamma⌋.toNat:ℝ)) < 681/10000 := by
  have hb := upper_cell_physical_block_range M hg
  have hh := upper_cell_error_profile_le M.gamma _ M.shellPrefix.gamma_pos.le hg hb.1 hb.2
  rw [upper_cell_error_profile_endpoint] at hh
  exact ⟨hh,hh.trans_lt upper_error_bounds.1⟩

end
end ASDExplicitGamma.Scalar
