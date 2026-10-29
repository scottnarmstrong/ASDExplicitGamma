module

public import ASDExplicitGamma.Scalar.UpperCellEnergyDescendantComparison
public import ASDExplicitGamma.Variational.AdapterConstantSkew

/-! The baseline-preserving cost of changing the constant skew gauge. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization Response Variational

/-- The planar load shear costs at most 1+|g|+g² in its squared Euclidean norm. -/
theorem upper_cell_gauge_magnitude (g : ℝ) (P : BlockVec 2) :
    blockVecDot (constantSkewLoad g P) (constantSkewLoad g P) ≤ 
      (1+|g|+g^2)*blockVecDot P P := by
  rcases P with ⟨p,q⟩
  let c := q 0*p 1-q 1*p 0
  let s := p 0^2+p 1^2+q 0^2+q 1^2
  have hc : 2*|c| ≤ s := by
    have hh : |c| ≤ s/2 := by
      apply abs_le.mpr
      constructor <;> dsimp [c,s] <;>
        nlinarith only [sq_nonneg (q 0+p 1),sq_nonneg (q 1-p 0),
          sq_nonneg (q 0-p 1),sq_nonneg (q 1+p 0)]
    linarith only [hh]
  have hgc : 2*(g*c) ≤ |g| *s := by
    have ha := le_abs_self (g*c)
    rw [abs_mul] at ha
    have hb := mul_le_mul_of_nonneg_left hc (abs_nonneg g)
    nlinarith only [ha,hb]
  have hq : 0 ≤ g^2*(q 0^2+q 1^2) := mul_nonneg (sq_nonneg g)
    (add_nonneg (sq_nonneg _) (sq_nonneg _))
  simp [constantSkewLoad,blockVecDot,vecDot,matVecMul,Fin.sum_univ_two,responsePlanarJ]
  dsimp [c,s] at hgc
  nlinarith only [hgc,hq]

/-- A centered-band gauge difference bounded by 2F has the exact source
polynomial cost, without an extra constant on the unperturbed term. -/
theorem upper_cell_gauge_magnitude_of_bound
    (g F : ℝ) (hF : 0 ≤ F) (hg : |g| ≤ 2*F) (P : BlockVec 2) :
    blockVecDot (constantSkewLoad g P) (constantSkewLoad g P) ≤ 
      (1+2*F+4*F^2)*blockVecDot P P := by
  have hs := (sq_le_sq₀ (abs_nonneg g) (mul_nonneg (by norm_num) hF)).2 hg
  rw [sq_abs] at hs
  have hp : 1+|g|+g^2 ≤  1+2*F+4*F^2 := by nlinarith only [hg,hs]
  exact (upper_cell_gauge_magnitude g P).trans
    (mul_le_mul_of_nonneg_right hp (blockVecDot_nonneg P))

end ASDExplicitGamma.Scalar
