module

public import ASDExplicitGamma.Native.OldSignedCellAverageCauchy

/-! Spatial OLD mixed terms paid by the joint energy before probability averaging. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization
noncomputable section

/-- A square-energy cap yields the exact spatial root cap. -/
theorem old_signed_cell_root_cap (Q : TriadicCube 2) (r : ℕ)
    (f : OldSignedCellIndex Q r → ℝ) (k W : ℝ) (hk : 0≤k)
    (hcap : oldSignedCellAverage Q r (fun U => f U^2)≤k^2*W) :
    Real.sqrt (oldSignedCellAverage Q r (fun U => f U^2))≤k*Real.sqrt W := by
  exact (Real.sqrt_le_sqrt hcap).trans_eq (by rw [Real.sqrt_mul (sq_nonneg k),Real.sqrt_sq hk])

/-- A complete mixed term contracts against its joint second energy. -/
theorem old_signed_cell_mixed_root_bound (Q : TriadicCube 2) (r : ℕ)
    (f E : OldSignedCellIndex Q r → ℝ) (k W : ℝ) (hk : 0≤k)
    (hE : ∀ U,0≤E U) (hcap : oldSignedCellAverage Q r (fun U => f U^2)≤k^2*W) :
    oldSignedCellAverage Q r (fun U => f U*Real.sqrt (E U))≤
      k*Real.sqrt W*Real.sqrt (oldSignedCellAverage Q r E) := by
  have hh := old_signed_cell_average_cauchy Q r f (fun U => Real.sqrt (E U))
  simp only [Real.sq_sqrt (hE _)] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right (old_signed_cell_root_cap Q r f k W hk hcap)
    (Real.sqrt_nonneg _))

/-- Quadratic OLD-source energy and both disjoint mixed terms are aggregated
without separating their correlated probability factors. -/
theorem old_signed_cell_source_mixed_bound (Q : TriadicCube 2) (r : ℕ)
    (d E F : OldSignedCellIndex Q r → ℝ) (B k W : ℝ)
    (hB : 0≤B) (hk : 0≤k) (hE : ∀ U,0≤E U) (hF : ∀ U,0≤F U)
    (hd : oldSignedCellAverage Q r (fun U => d U^2)≤k^2*W) :
    oldSignedCellAverage Q r (fun U => B*d U^2+
      2*(d U*(Real.sqrt (E U)+Real.sqrt (F U))))≤
      B*k^2*W+2*(k*Real.sqrt W*(Real.sqrt (oldSignedCellAverage Q r E)+
        Real.sqrt (oldSignedCellAverage Q r F))) := by
  have he := old_signed_cell_mixed_root_bound Q r d E k W hk hE hd
  have hf := old_signed_cell_mixed_root_bound Q r d F k W hk hF hd
  simp_rw [mul_add (d _)]
  rw [old_signed_cell_average_add,old_signed_cell_average_mul,
    old_signed_cell_average_mul,old_signed_cell_average_add]
  have hh := add_le_add (mul_le_mul_of_nonneg_left hd hB)
    (mul_le_mul_of_nonneg_left (add_le_add he hf) (by norm_num : (0:ℝ)≤2))
  exact hh.trans_eq (by ring)

end
end ASDExplicitGamma.Native
