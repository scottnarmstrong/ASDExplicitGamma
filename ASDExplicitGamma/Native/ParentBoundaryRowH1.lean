module

public import ASDExplicitGamma.Native.ParentBoundaryRowWeak

/-! The complete physical covariance row as a genuine scalar H1 function. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Scalar ASDExplicitGamma.Triadic
noncomputable section

/-- An actual C1 Hilbert row acting on an actual Hilbert H1 field, with
its proved product weak derivative and L2 membership. -/
def parentBoundaryRowH1 {E I : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [Countable I]
    (e : HilbertBasis I ℝ E) (Q : TriadicCube 2) (b : Vec 2 → E) (hb : ContDiff ℝ 1 b)
    (u : HilbertH1Function (openCubeSet Q) E) : H1Function (openCubeSet Q) where
  toFun x := inner ℝ (b x) (u.toFun x)
  grad x i := inner ℝ (b x) (u.grad x i) +
    inner ℝ ((fderiv ℝ b x) (basisVec i)) (u.toFun x)
  memL2 := (innerSL ℝ).memLp_of_bilin 2
    (parent_boundary_continuous_memLp_top_open Q b hb.continuous) u.memL2
  gradMemL2 i := ((innerSL ℝ).memLp_of_bilin 2
    (parent_boundary_continuous_memLp_top_open Q b hb.continuous) (u.gradMemL2 i)).add
      ((innerSL ℝ).memLp_of_bilin 2
        (parent_boundary_continuous_memLp_top_open Q _
          ((hb.continuous_fderiv (by norm_num)).clm_apply continuous_const)) u.memL2)
  hasWeakGradient := parent_boundary_row_product_weak e Q b hb u

end
end ASDExplicitGamma.Native
