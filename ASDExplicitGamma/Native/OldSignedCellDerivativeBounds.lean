module

public import ASDExplicitGamma.Native.OldSignedCellAverageCauchy

/-! Spatial aggregation of the complete OLD derivative feedback block. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization
noncomputable section

/-- Two root second-moment bounds pay the actual spatial product. -/
theorem old_signed_cell_product_root_caps (Q : TriadicCube 2) (r : ℕ)
    (f g : OldSignedCellIndex Q r → ℝ) (F G : ℝ) (hF : 0≤F)
    (hf : Real.sqrt (oldSignedCellAverage Q r (fun U => f U^2))≤F)
    (hg : Real.sqrt (oldSignedCellAverage Q r (fun U => g U^2))≤G) :
    oldSignedCellAverage Q r (fun U => f U*g U)≤F*G :=
  (old_signed_cell_average_cauchy Q r f g).trans
    (mul_le_mul hf hg (Real.sqrt_nonneg _) hF)

/-- An additive constant in a derivative multiplier is paid without losing
the sharp root coefficient of the fluctuating factor. -/
theorem old_signed_cell_offset_product_root_caps (Q : TriadicCube 2) (r : ℕ)
    (f g : OldSignedCellIndex Q r → ℝ) (a F G : ℝ) (ha : 0≤a) (hF : 0≤F)
    (hf : Real.sqrt (oldSignedCellAverage Q r (fun U => f U^2))≤F)
    (hg : Real.sqrt (oldSignedCellAverage Q r (fun U => g U^2))≤G) :
    oldSignedCellAverage Q r (fun U => (a+f U)*g U)≤(a+F)*G := by
  simp_rw [add_mul]
  rw [old_signed_cell_average_add,old_signed_cell_average_mul]
  have hmean := (old_signed_cell_average_le_root Q r g).trans hg
  exact (add_le_add (mul_le_mul_of_nonneg_left hmean ha)
    (old_signed_cell_product_root_caps Q r f g F G hF hf hg)).trans_eq (by ring)

/-- The three derivative feedback terms retain both affine loads, the OLD
source cross, and the reciprocal offset. All spatial factors are aggregated
before any probability estimate is applied. -/
theorem old_signed_cell_derivative_feedback_bound (Q : TriadicCube 2) (r : ℕ)
    (G d p q op e : OldSignedCellIndex Q r → ℝ)
    (kappa DB g δ P N O E : ℝ) (hkappa : 0≤kappa) (hDB : 0≤DB) (hg : 0≤g)
    (hG : Real.sqrt (oldSignedCellAverage Q r (fun U => G U^2))≤g)
    (hd : Real.sqrt (oldSignedCellAverage Q r (fun U => d U^2))≤δ)
    (hp : Real.sqrt (oldSignedCellAverage Q r (fun U => p U^2))≤P)
    (hq : Real.sqrt (oldSignedCellAverage Q r (fun U => q U^2))≤N)
    (hop : Real.sqrt (oldSignedCellAverage Q r (fun U => op U^2))≤O)
    (he : Real.sqrt (oldSignedCellAverage Q r (fun U => e U^2))≤E) :
    oldSignedCellAverage Q r (fun U =>
      2*(kappa*G U*(p U+DB*op U))+
      2*(kappa*(Real.sqrt 2+G U)*(DB*d U))+
      2*(kappa*(Real.sqrt 2+G U)*(q U+e U)))≤
      2*kappa*(g*(P+DB*O)+DB*(Real.sqrt 2+g)*δ+(Real.sqrt 2+g)*(N+E)) := by
  have hGp := old_signed_cell_product_root_caps Q r G p g P hg hG hp
  have hGo := old_signed_cell_product_root_caps Q r G op g O hg hG hop
  have hGd := old_signed_cell_offset_product_root_caps Q r G d (Real.sqrt 2) g δ
    (Real.sqrt_nonneg _) hg hG hd
  have hGq := old_signed_cell_offset_product_root_caps Q r G q (Real.sqrt 2) g N
    (Real.sqrt_nonneg _) hg hG hq
  have hGe := old_signed_cell_offset_product_root_caps Q r G e (Real.sqrt 2) g E
    (Real.sqrt_nonneg _) hg hG he
  have hid : (fun U =>
      2*(kappa*G U*(p U+DB*op U))+
      2*(kappa*(Real.sqrt 2+G U)*(DB*d U))+
      2*(kappa*(Real.sqrt 2+G U)*(q U+e U)))=
    (fun U => (2*kappa)*(G U*p U)+((2*kappa)*DB)*(G U*op U)+
      ((2*kappa)*DB)*((Real.sqrt 2+G U)*d U)+
      (2*kappa)*((Real.sqrt 2+G U)*q U)+(2*kappa)*((Real.sqrt 2+G U)*e U)) := by
    funext U
    ring
  rw [hid]
  simp only [old_signed_cell_average_add,old_signed_cell_average_mul]
  have h2k : 0≤2*kappa := mul_nonneg (by norm_num) hkappa
  have h2kD := mul_nonneg h2k hDB
  have hh := add_le_add (add_le_add (add_le_add
    (add_le_add (mul_le_mul_of_nonneg_left hGp h2k) (mul_le_mul_of_nonneg_left hGo h2kD))
      (mul_le_mul_of_nonneg_left hGd h2kD)) (mul_le_mul_of_nonneg_left hGq h2k))
        (mul_le_mul_of_nonneg_left hGe h2k)
  exact hh.trans_eq (by ring)

end
end ASDExplicitGamma.Native
