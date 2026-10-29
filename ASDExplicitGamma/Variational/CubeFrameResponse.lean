module

public import ASDExplicitGamma.Variational.CubeResponse
public import ASDExplicitGamma.Variational.TraceDefect

/-! The source response identity in a fixed positive scalar frame. -/
@[expose] public section
namespace ASDExplicitGamma.Variational
open Homogenization

theorem frame_load_quadratic (A : BlockMat 2) (P : BlockVec 2) (s : ℝ) (hs : s ≠ 0) :
    blockVecDot (s⁻¹ • P.1,s • P.2)
      (blockMatVecMul A (s⁻¹ • P.1,s • P.2)) =
    blockVecDot P (blockMatVecMul (frameMatrix (s^2) A) P) := by
  simp only [blockVecDot,blockMatVecMul,frameMatrix,vecDot_add_right,
    vecDot_smul_left,vecDot_smul_right,matVecMul_smul,smul_matVecMul]
  field_simp [hs]

/-- The frame-scaled identity, with the exact reciprocal square-root load. -/
theorem cube_response_quadratic_frame (Q : TriadicCube 2) (a : CoeffField 2)
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (sigma : ℝ) (hsigma : 0 < sigma) (p q : Vec 2) :
    ResponseJ (openCubeSet Q) ((Real.sqrt sigma)⁻¹ • p) (Real.sqrt sigma • q) a =
      (1/2 : ℝ)*blockVecDot (-p,q)
        (blockMatVecMul (frameMatrix sigma (coarseBlockMatrix (openCubeSet Q) a)) (-p,q))-
      vecDot p q := by
  have hs : Real.sqrt sigma ≠ 0 := (Real.sqrt_pos.mpr hsigma).ne'
  have hs2 : (Real.sqrt sigma)^2 = sigma := Real.sq_sqrt hsigma.le
  rw [cube_response_quadratic Q a hEll]
  have hneg : -((Real.sqrt sigma)⁻¹ • p) = (Real.sqrt sigma)⁻¹ • (-p) := by
    simp only [smul_neg]
  rw [hneg,frame_load_quadratic _ (-p,q) _ hs,hs2]
  simp only [vecDot_smul_left,vecDot_smul_right]
  field_simp [hs]

end ASDExplicitGamma.Variational
