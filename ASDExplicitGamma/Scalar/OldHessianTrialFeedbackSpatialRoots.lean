module

public import ASDExplicitGamma.Native.OldSignedCellAverageCauchy

/-! Constant-one spatial roots for the actual mixed derivative factors. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization Native
noncomputable section
attribute [local irreducible] Homogenization.descendantsAtDepth

/-- A common inverse bank is factored only after bounding the literal
cell product. The source and paired parent roots retain the same averaging. -/
theorem old_hessian_feedback_spatial_roots (Q : TriadicCube 2) (fine : ℕ)
    (K B S G : OldSignedCellIndex Q fine → ℝ) (κ β D : ℝ)
    (hκ : 0≤κ) (hβ : 0≤β) (hD : 0≤D)
    (hKB : ∀ U,K U*B U≤κ*β) (hS : ∀ U,0≤S U) (hG : ∀ U,0≤G U) :
    oldSignedCellAverage Q fine (fun U => K U*(Real.sqrt 2+Real.sqrt (G U))*
      ((D*B U)*Real.sqrt (S U)))≤
    (κ*D*β)*(Real.sqrt 2*Real.sqrt (oldSignedCellAverage Q fine S)+
      Real.sqrt (oldSignedCellAverage Q fine G)*Real.sqrt (oldSignedCellAverage Q fine S)) := by
  have hcell U : K U*(Real.sqrt 2+Real.sqrt (G U))*((D*B U)*Real.sqrt (S U))≤
      (κ*D*β)*((Real.sqrt 2+Real.sqrt (G U))*Real.sqrt (S U)) := by
    calc
      _ = (D*(K U*B U))*((Real.sqrt 2+Real.sqrt (G U))*Real.sqrt (S U)) := by ring
      _ ≤ (D*(κ*β))*((Real.sqrt 2+Real.sqrt (G U))*Real.sqrt (S U)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hKB U) hD)
          (mul_nonneg (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))
      _ = _ := by ring
  have hh := old_signed_cell_average_mono Q fine hcell
  rw [old_signed_cell_average_mul] at hh
  have hmean := old_signed_cell_average_le_root Q fine (fun U => Real.sqrt (S U))
  simp only [Real.sq_sqrt (hS _)] at hmean
  have hcross := old_signed_cell_average_root_cauchy Q fine G S hG hS
  have hsp : oldSignedCellAverage Q fine (fun U => (Real.sqrt 2+Real.sqrt (G U))*Real.sqrt (S U))≤
      Real.sqrt 2*Real.sqrt (oldSignedCellAverage Q fine S)+
        Real.sqrt (oldSignedCellAverage Q fine G)*Real.sqrt (oldSignedCellAverage Q fine S) := by
    simp_rw [add_mul]
    rw [old_signed_cell_average_add,old_signed_cell_average_mul]
    exact add_le_add (mul_le_mul_of_nonneg_left hmean (Real.sqrt_nonneg 2)) hcross
  exact hh.trans (mul_le_mul_of_nonneg_left hsp (mul_nonneg (mul_nonneg hκ hD) hβ))

end
end ASDExplicitGamma.Scalar
