module

public import ASDExplicitGamma.Native.OldSignedCellAverageCauchy

/-! Spatial aggregation of the four-term OLD flat block. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization
noncomputable section

/-- The flat cross and corrector cross retain their separate joint spatial
energies; no maximum over cells replaces the physical averages. -/
theorem old_signed_cell_flat_block_bound (Q : TriadicCube 2) (r : ℕ)
    (p T y op om A : OldSignedCellIndex Q r → ℝ) (B J : ℝ)
    (hp : ∀ U,0≤p U) (hT : ∀ U,0≤T U)
    (hJ : oldSignedCellAverage Q r p≤J) :
    oldSignedCellAverage Q r (fun U =>
      2*Real.sqrt (p U)*op U+B*op U^2+
      2*Real.sqrt (2*T U)*(y U*om U)+A U*om U^2)≤
      2*Real.sqrt J*Real.sqrt (oldSignedCellAverage Q r (fun U => op U^2))+
      B*oldSignedCellAverage Q r (fun U => op U^2)+
      (2*Real.sqrt 2)*Real.sqrt (oldSignedCellAverage Q r (fun U => T U*y U^2))*
        Real.sqrt (oldSignedCellAverage Q r (fun U => om U^2))+
      oldSignedCellAverage Q r (fun U => A U*om U^2) := by
  have hpC := old_signed_cell_average_cauchy Q r (fun U => Real.sqrt (p U)) op
  simp only [Real.sq_sqrt (hp _)] at hpC
  have hpC' := hpC.trans (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hJ) (Real.sqrt_nonneg _))
  have hTC := old_signed_cell_average_cauchy Q r (fun U => Real.sqrt (T U)*y U) om
  simp only [mul_pow,Real.sq_sqrt (hT _)] at hTC
  have hid : (fun U => 2*Real.sqrt (p U)*op U+B*op U^2+
      2*Real.sqrt (2*T U)*(y U*om U)+A U*om U^2)=
    (fun U => 2*(Real.sqrt (p U)*op U)+B*op U^2+
      (2*Real.sqrt 2)*((Real.sqrt (T U)*y U)*om U)+A U*om U^2) := by
    funext U
    rw [Real.sqrt_mul (by norm_num : (0:ℝ)≤2)]
    ring
  rw [hid]
  simp only [old_signed_cell_average_add,old_signed_cell_average_mul]
  have hh := add_le_add (add_le_add (add_le_add
    (mul_le_mul_of_nonneg_left hpC' (by norm_num : (0:ℝ)≤2)) (le_refl (B*oldSignedCellAverage Q r (fun U => op U^2))))
    (mul_le_mul_of_nonneg_left hTC (mul_nonneg (by norm_num : (0:ℝ)≤2) (Real.sqrt_nonneg (2:ℝ))))) (le_refl (oldSignedCellAverage Q r (fun U => A U*om U^2)))
  exact hh.trans_eq (by ring)

end
end ASDExplicitGamma.Native
