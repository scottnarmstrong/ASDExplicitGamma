module

public import ASDExplicitGamma.Native.OldSignedCellDerivativeBounds

/-! Joint spatial roots for the original minus correction feedback. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization Native
noncomputable section
attribute [local irreducible] Homogenization.descendantsAtDepth

/-- The reciprocal constant and the actual paired energy are contracted
against each of the three correction factors on the same cells. -/
theorem old_hessian_minus_feedback_spatial (Q : TriadicCube 2) (r : ℕ)
    (K G P H O : OldSignedCellIndex Q r → ℝ) (κ A F o : ℝ)
    (hκ : 0≤κ) (ho : 0≤o) (hK : ∀ U,K U≤κ)
    (hG : ∀ U,0≤G U) (hP : ∀ U,0≤P U) (hH : ∀ U,0≤H U) (hO : ∀ U,0≤O U)
    (hPavg : oldSignedCellAverage Q r P≤A)
    (hHO : oldSignedCellAverage Q r (fun U => H U*O U^2)≤F)
    (hOsq : oldSignedCellAverage Q r (fun U => O U^2)≤o^2) :
    oldSignedCellAverage Q r (fun U => K U*(Real.sqrt 2+Real.sqrt (G U))*
      (Real.sqrt (P U)+(Real.sqrt (H U)+1)*O U))≤
      κ*(Real.sqrt 2+Real.sqrt (oldSignedCellAverage Q r G))*(Real.sqrt A+Real.sqrt F+o) := by
  let R := Real.sqrt (oldSignedCellAverage Q r G)
  have hGr : Real.sqrt (oldSignedCellAverage Q r (fun U => (Real.sqrt (G U))^2))≤R := by
    simp only [Real.sq_sqrt (hG _)]; exact le_rfl
  have hpr : Real.sqrt (oldSignedCellAverage Q r (fun U => (Real.sqrt (P U))^2))≤Real.sqrt A := by
    simp only [Real.sq_sqrt (hP _)]; exact Real.sqrt_le_sqrt hPavg
  have hhr : Real.sqrt (oldSignedCellAverage Q r (fun U => (Real.sqrt (H U)*O U)^2))≤Real.sqrt F := by
    simp only [mul_pow,Real.sq_sqrt (hH _)]
    exact Real.sqrt_le_sqrt hHO
  have hor : Real.sqrt (oldSignedCellAverage Q r (fun U => O U^2))≤o :=
    (Real.sqrt_le_sqrt hOsq).trans_eq (Real.sqrt_sq ho)
  have cap (f : OldSignedCellIndex Q r → ℝ) (d : ℝ)
      (hf : Real.sqrt (oldSignedCellAverage Q r (fun U => f U^2))≤d) :=
    old_signed_cell_offset_product_root_caps Q r (fun U => Real.sqrt (G U)) f (Real.sqrt 2) R d
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hGr hf
  have hp := cap _ _ hpr
  have hh := cap _ _ hhr
  have hhO := cap _ _ hor
  have hcell U : K U*(Real.sqrt 2+Real.sqrt (G U))*(Real.sqrt (P U)+(Real.sqrt (H U)+1)*O U)≤
      κ*((Real.sqrt 2+Real.sqrt (G U))*Real.sqrt (P U)+
        (Real.sqrt 2+Real.sqrt (G U))*(Real.sqrt (H U)*O U)+
        (Real.sqrt 2+Real.sqrt (G U))*O U) := by
    calc
      _ = K U*((Real.sqrt 2+Real.sqrt (G U))*Real.sqrt (P U)+
        (Real.sqrt 2+Real.sqrt (G U))*(Real.sqrt (H U)*O U)+
        (Real.sqrt 2+Real.sqrt (G U))*O U) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (hK U) (add_nonneg (add_nonneg
          (mul_nonneg (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))
          (mul_nonneg (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
            (mul_nonneg (Real.sqrt_nonneg _) (hO U))))
          (mul_nonneg (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) (hO U)))
  have ha := old_signed_cell_average_mono Q r hcell
  rw [old_signed_cell_average_mul,old_signed_cell_average_add,old_signed_cell_average_add] at ha
  exact ha.trans ((mul_le_mul_of_nonneg_left (add_le_add (add_le_add hp hh) hhO) hκ).trans_eq (by dsimp only [R]; ring))

end
end ASDExplicitGamma.Scalar
