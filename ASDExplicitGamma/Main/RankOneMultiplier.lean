module

public import ASDExplicitGamma.Triadic.HilbertProductSource
public import Homogenization.Sobolev.H1.BasicLemmas
public import Mathlib.Analysis.Normed.Operator.Mul

/-! Actual smooth vector multipliers as operator-valued weak W^{1,∞} fields. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Homogenization MeasureTheory ASDExplicitGamma.Triadic
open scoped ENNReal RealInnerProductSpace

/-- Continuity on the physical cube gives a genuine essential-supremum
bound, including for operator-valued coefficients. -/
theorem main_continuous_memLp_top {F : Type*} [NormedAddCommGroup F]
    (Q : TriadicCube 2) {b : Vec 2 → F} (hb : Continuous b) :
    MemLp b ⊤ (normalizedCubeMeasure Q) := by
  obtain ⟨C, hC⟩ := (isBounded_cubeSet Q).isCompact_closure.exists_bound_of_continuousOn hb.continuousOn
  apply MemLp.of_bound hb.aestronglyMeasurable C
  filter_upwards [hilbert_ae_cubeSet Q] with x hx
  exact hC x (subset_closure hx)

/-- A vector coefficient acts on scalars by the literal rank-one map.
All weak derivatives and W^{1,∞} membership are supplied internally. -/
noncomputable def mainRankOneMultiplier {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [CompleteSpace F] (Q : TriadicCube 2)
    (b : Vec 2 → F) (hb : ContDiff ℝ 1 b) : HilbertOperatorW1Infinity Q ℝ F where
  toFun x := ContinuousLinearMap.toSpanSingleton ℝ (b x)
  grad x i := ContinuousLinearMap.toSpanSingleton ℝ ((fderiv ℝ b x) (basisVec i))
  memLp_top := main_continuous_memLp_top Q
    ((ContinuousLinearMap.toSpanSingletonLIE ℝ F).continuous.comp hb.continuous)
  gradMemLp_top i := main_continuous_memLp_top Q
    ((ContinuousLinearMap.toSpanSingletonLIE ℝ F).continuous.comp
      ((hb.continuous_fderiv (by norm_num)).clm_apply continuous_const))
  hasWeakGradient e v := by
    change HasWeakGradientOn (openCubeSet Q) (fun x => inner ℝ v (e • b x))
      (fun x i => inner ℝ v (e • (fderiv ℝ b x) (basisVec i)))
    let l : F →L[ℝ] ℝ := innerSL ℝ v
    have hs : ContDiff ℝ 1 (fun x => inner ℝ v (e • b x)) :=
      l.contDiff.comp (contDiff_const.smul hb)
    have heq : (fun x i => (fderiv ℝ (fun y => inner ℝ v (e • b y)) x) (basisVec i)) =
        (fun x i => inner ℝ v (e • (fderiv ℝ b x) (basisVec i))) := by
      funext x i
      have hd := l.hasFDerivAt.comp x
        (((hb.differentiable (by norm_num)).differentiableAt).hasFDerivAt.const_smul e)
      have h := congrArg (fun D : Vec 2 →L[ℝ] ℝ => D (basisVec i)) hd.fderiv
      simpa only [ContinuousLinearMap.comp_apply, smul_apply, l,
        innerSL_apply_apply, Function.comp_def, Pi.smul_apply] using h
    rw [← heq]
    exact HasWeakGradientOn.of_contDiff hs

/-- Rank-one operator norm retains the vector Hilbert norm exactly. -/
theorem mainRankOneMultiplier_norm {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [CompleteSpace F] (Q : TriadicCube 2)
    (b : Vec 2 → F) (hb : ContDiff ℝ 1 b) (x : Vec 2) :
    ‖(mainRankOneMultiplier Q b hb).toFun x‖ = ‖b x‖ :=
  ContinuousLinearMap.norm_toSpanSingleton _

/-- The spatial Frobenius derivative keeps every source derivative coordinate. -/
theorem mainRankOneMultiplier_gradient_norm {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [CompleteSpace F] (Q : TriadicCube 2)
    (b : Vec 2 → F) (hb : ContDiff ℝ 1 b) (x : Vec 2) (i : Fin 2) :
    ‖(mainRankOneMultiplier Q b hb).grad x i‖ = ‖(fderiv ℝ b x) (basisVec i)‖ :=
  ContinuousLinearMap.norm_toSpanSingleton _

end ASDExplicitGamma.Main
