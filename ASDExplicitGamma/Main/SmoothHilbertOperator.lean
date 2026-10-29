module

public import ASDExplicitGamma.Main.RankOneMultiplier

/-! Genuine smooth operator fields as weak W^{1,∞} multipliers. -/

@[expose] public section
namespace ASDExplicitGamma.Main
open Homogenization MeasureTheory ASDExplicitGamma.Triadic
open scoped RealInnerProductSpace

/-- Smooth bounded-on-cube operator fields carry their actual weak derivatives.
No Sobolev or norm estimate is stored as an assumed field. -/
noncomputable def mainSmoothHilbertOperator {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (Q : TriadicCube 2) (b : Vec 2 → E →L[ℝ] F) (hb : ContDiff ℝ 1 b) :
    HilbertOperatorW1Infinity Q E F where
  toFun := b
  grad x i := (fderiv ℝ b x) (basisVec i)
  memLp_top := main_continuous_memLp_top Q hb.continuous
  gradMemLp_top i := main_continuous_memLp_top Q
    ((hb.continuous_fderiv (by norm_num)).clm_apply continuous_const)
  hasWeakGradient e v := by
    let l : (E →L[ℝ] F) →L[ℝ] ℝ := (innerSL ℝ v).comp (ContinuousLinearMap.apply ℝ F e)
    have hs : ContDiff ℝ 1 (fun x => inner ℝ v (b x e)) := l.contDiff.comp hb
    have he : (fun x i => (fderiv ℝ (fun y => inner ℝ v (b y e)) x) (basisVec i)) =
        fun x i => inner ℝ v (((fderiv ℝ b x) (basisVec i)) e) := by
      funext x i
      have h := l.hasFDerivAt.comp x
        ((hb.differentiable (by norm_num)).differentiableAt.hasFDerivAt)
      exact congrArg (fun T : Vec 2 →L[ℝ] ℝ => T (basisVec i)) h.fderiv
    rw [← he]
    exact HasWeakGradientOn.of_contDiff hs

end ASDExplicitGamma.Main
