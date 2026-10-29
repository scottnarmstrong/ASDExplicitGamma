module

public import ASDExplicitGamma.Main.RankOneMultiplier

/-! Actual C1 white rows as weak W^{1,∞} multipliers. This is the
scalar contraction counterpart of the existing rank-one multiplier. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Triadic ASDExplicitGamma.Main
noncomputable section

/-- A genuine C1 Hilbert coefficient acts on its input by its literal
inner product; its weak derivatives are the actual differentiated row. -/
def oldSignedRowMultiplier {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (Q : TriadicCube 2)
    (b : Vec 2 → E) (hb : ContDiff ℝ 1 b) : HilbertOperatorW1Infinity Q E ℝ where
  toFun x := innerSL ℝ (b x)
  grad x i := innerSL ℝ ((fderiv ℝ b x) (basisVec i))
  memLp_top := main_continuous_memLp_top Q ((innerSL ℝ).continuous.comp hb.continuous)
  gradMemLp_top i := main_continuous_memLp_top Q
    ((innerSL ℝ).continuous.comp ((hb.continuous_fderiv (by norm_num)).clm_apply continuous_const))
  hasWeakGradient e v := by
    let l : E →L[ℝ] ℝ := v • innerSL ℝ e
    have hs : ContDiff ℝ 1 (fun x => l (b x)) := l.contDiff.comp hb
    have hd x : HasFDerivAt (fun y => l (b y)) (l.comp (fderiv ℝ b x)) x :=
      l.hasFDerivAt.comp x ((hb.differentiable (by norm_num)).differentiableAt.hasFDerivAt)
    have hw := HasWeakGradientOn.of_contDiff hs (U := openCubeSet Q)
    have hv : (fun x => inner ℝ v ((innerSL ℝ (b x)) e))=(fun x => l (b x)) := by
      funext x
      simp only [innerSL_apply_apply,real_inner_comm (b x) e,Real.inner_apply,
        l,smul_apply,smul_eq_mul]
    have hg : (fun x i => inner ℝ v ((innerSL ℝ ((fderiv ℝ b x) (basisVec i))) e))=
        (fun x i => (fderiv ℝ (fun y => l (b y)) x) (basisVec i)) := by
      funext x i
      rw [(hd x).fderiv]
      simp only [ContinuousLinearMap.comp_apply,innerSL_apply_apply,
        real_inner_comm ((fderiv ℝ b x) (basisVec i)) e,Real.inner_apply,
        l,smul_apply,smul_eq_mul]
    change HasWeakGradientOn (openCubeSet Q) (fun x => inner ℝ v ((innerSL ℝ (b x)) e))
      (fun x i => inner ℝ v ((innerSL ℝ ((fderiv ℝ b x) (basisVec i))) e))
    rw [hv,hg]
    exact hw

/-- No loss in the actual row operator norm. -/
theorem old_signed_row_multiplier_norm {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (Q : TriadicCube 2)
    (b : Vec 2 → E) (hb : ContDiff ℝ 1 b) (x : Vec 2) :
    ‖(oldSignedRowMultiplier Q b hb).toFun x‖=‖b x‖ := innerSL_apply_norm ℝ _

/-- No loss in any actual derivative row operator norm. -/
theorem old_signed_row_multiplier_gradient_norm {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (Q : TriadicCube 2)
    (b : Vec 2 → E) (hb : ContDiff ℝ 1 b) (x : Vec 2) (i : Fin 2) :
    ‖(oldSignedRowMultiplier Q b hb).grad x i‖=‖(fderiv ℝ b x) (basisVec i)‖ := innerSL_apply_norm ℝ _

end
end ASDExplicitGamma.Native
