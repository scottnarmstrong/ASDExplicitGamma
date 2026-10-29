module

public import ASDExplicitGamma.Scalar.ViscosityMinimum

/-! SC-NU-MONOTONICITY: compare the actual top coarse blocks at fixed skew law. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization

/-- The actual affine minima inherit the fixed-skew viscosity comparison. -/
theorem fixed_skew_mu_comparison (Q : TriadicCube 2) (a b : CoeffField 2)
    (nu r La Lb : ℝ) (hnu : 0 < nu) (hr : 0 < r) (hr1 : r ≤ 1)
    (ha : IsEllipticFieldOn nu La (cubeSet Q) a)
    (hb : IsEllipticFieldOn (r*nu) Lb (cubeSet Q) b)
    (hsa : ∀ x ∈ cubeSet Q, symmPart (a x)=nu • (1:Mat 2))
    (hsb : ∀ x ∈ cubeSet Q, symmPart (b x)=(r*nu) • (1:Mat 2))
    (hk : ∀ x ∈ cubeSet Q, skewPart (a x)=skewPart (b x)) (P : BlockVec 2) :
    r*Mu (cubeSet Q) P a ≤ Mu (cubeSet Q) P b ∧
      Mu (cubeSet Q) P b ≤ r⁻¹*Mu (cubeSet Q) P a := by
  have hcomp (X : BlockState 2) (x) (hx : x ∈ cubeSet Q) :=
    fixed_skew_block_energy_comparison (a x) (b x) nu r hnu hr hr1
      (hsa x hx) (hsb x hx) (hk x hx) (X.potential x) (X.flux x)
  have hl := molecular_mu_comparison Q a b ha hb r hr.le (fun X x hx => by
    have h := (hcomp X x hx).1
    change r*((1/2:ℝ)*_) ≤ (1/2:ℝ)*_
    change r*blockVecDot (X.eval x) (blockMatVecMul (blockCoeffField a x) (X.eval x)) ≤
      blockVecDot (X.eval x) (blockMatVecMul (blockCoeffField b x) (X.eval x)) at h
    nlinarith only [h]) P
  have hu := molecular_mu_comparison Q b a hb ha r hr.le (fun X x hx => by
    have h := mul_le_mul_of_nonneg_left (hcomp X x hx).2 hr.le
    rw [← mul_assoc,mul_inv_cancel₀ hr.ne',one_mul] at h
    change r*((1/2:ℝ)*_) ≤ (1/2:ℝ)*_
    change r*blockVecDot (X.eval x) (blockMatVecMul (blockCoeffField b x) (X.eval x)) ≤
      blockVecDot (X.eval x) (blockMatVecMul (blockCoeffField a x) (X.eval x)) at h
    nlinarith only [h]) P
  refine ⟨hl,?_⟩
  apply (mul_le_mul_iff_of_pos_left hr).mp
  rw [← mul_assoc,mul_inv_cancel₀ hr.ne',one_mul]
  exact hu

/-- SC-NU-MONOTONICITY in the source top-block Loewner convention. -/
theorem fixed_skew_top_block_comparison (Q : TriadicCube 2) (a b : CoeffField 2)
    (nu r La Lb : ℝ) (hnu : 0 < nu) (hr : 0 < r) (hr1 : r ≤ 1)
    (ha : IsEllipticFieldOn nu La (cubeSet Q) a)
    (hb : IsEllipticFieldOn (r*nu) Lb (cubeSet Q) b)
    (hsa : ∀ x ∈ cubeSet Q, symmPart (a x)=nu • (1:Mat 2))
    (hsb : ∀ x ∈ cubeSet Q, symmPart (b x)=(r*nu) • (1:Mat 2))
    (hk : ∀ x ∈ cubeSet Q, skewPart (a x)=skewPart (b x)) :
    MatLoewnerLE (r • (coarseBlockMatrix (cubeSet Q) a).upperLeft)
      (coarseBlockMatrix (cubeSet Q) b).upperLeft ∧
    MatLoewnerLE (coarseBlockMatrix (cubeSet Q) b).upperLeft
      (r⁻¹ • (coarseBlockMatrix (cubeSet Q) a).upperLeft) := by
  have h (p : Vec 2) := fixed_skew_mu_comparison Q a b nu r La Lb hnu hr hr1 ha hb hsa hsb hk (p,0)
  constructor
  · intro p
    have hh := (h p).1
    rw [Variational.mu_eq_half_coarseBlockMatrix_elliptic_triCube hnu ha,
      Variational.mu_eq_half_coarseBlockMatrix_elliptic_triCube (mul_pos hr hnu) hb] at hh
    simpa only [blockVecDot,blockMatVecMul,matVecMul_zero,add_zero,vecDot_zero_left,
      smul_matVecMul,vecDot_smul_right,mul_left_comm] using hh
  · intro p
    have hh := (h p).2
    rw [Variational.mu_eq_half_coarseBlockMatrix_elliptic_triCube hnu ha,
      Variational.mu_eq_half_coarseBlockMatrix_elliptic_triCube (mul_pos hr hnu) hb] at hh
    simpa only [blockVecDot,blockMatVecMul,matVecMul_zero,add_zero,vecDot_zero_left,
      smul_matVecMul,vecDot_smul_right,mul_left_comm] using hh

end ASDExplicitGamma.Scalar
