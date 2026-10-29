module

public import ASDExplicitGamma.Triadic.PlanarMultiplier
public import ASDExplicitGamma.Triadic.PlanarNeumannBridge
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-! The planar `J∇h` multiplier and its zero-trace product/Poincaré bound. -/

@[expose] public section

noncomputable section

open Homogenization MeasureTheory
open scoped BigOperators ENNReal

namespace ASDExplicitGamma.Triadic

private theorem fin2_eq_one_of_ne_zero {i : Fin 2} (hi : i ≠ 0) : i = 1 := by
  apply Fin.ext
  have hval : i.val ≠ 0 := by
    intro hval
    apply hi
    exact Fin.ext hval
  omega

private noncomputable def planarJGradientW1 {Q : TriadicCube 2}
    (h : PlanarW2Infinity Q) : PlanarW1Infinity Q where
  component := fun i => if i = 0 then -(h.gradient.component 1) else h.gradient.component 0
  component_memLp_top := by
    intro i
    by_cases hi : i = 0
    · subst i
      have hEq : (-(h.gradient.component 1).toFun) =ᵐ[normalizedCubeMeasure Q]
          (fun x => -(h.gradient.component 1).toFun x) :=
        Filter.Eventually.of_forall fun x => rfl
      simpa [H1Function.neg_toFun] using
        (MeasureTheory.memLp_congr_ae hEq).mp
          ((h.gradient.component_memLp_top 1).neg)
    · have hi1 : i = 1 := fin2_eq_one_of_ne_zero hi
      subst i
      simpa using h.gradient.component_memLp_top 0
  derivative_memLp_top := by
    intro i j
    by_cases hi : i = 0
    · subst i
      have hEq : (-fun x => (h.gradient.component 1).grad x j) =ᵐ[
          normalizedCubeMeasure Q] (fun x => -(h.gradient.component 1).grad x j) :=
        Filter.Eventually.of_forall fun x => rfl
      simpa [H1Function.neg_grad] using
        (MeasureTheory.memLp_congr_ae hEq).mp
          ((h.gradient.derivative_memLp_top 1 j).neg)
    · have hi1 : i = 1 := fin2_eq_one_of_ne_zero hi
      subst i
      simpa using h.gradient.derivative_memLp_top 0 j

private theorem planarEuclideanNorm_quarterTurn (v : Fin 2 → ℝ) :
    planarEuclideanNorm (planarQuarterTurn v) = planarEuclideanNorm v := by
  unfold planarEuclideanNorm planarQuarterTurn
  apply congrArg Real.sqrt
  simp [Fin.sum_univ_two]
  ring

private theorem planarFrobeniusNorm_quarterTurnRows (A : Fin 2 → Fin 2 → ℝ) :
    planarFrobeniusNorm (fun i j => planarQuarterTurn (fun k => A k j) i) =
      planarFrobeniusNorm A := by
  unfold planarFrobeniusNorm planarQuarterTurn
  apply congrArg Real.sqrt
  simp [Fin.sum_univ_two]
  ring

private theorem planarW1Value_planarJGradientW1 {Q : TriadicCube 2}
    (h : PlanarW2Infinity Q) :
    planarW1Value (planarJGradientW1 h) = planarJGradient h := by
  funext x i
  by_cases hi : i = 0
  · subst i
    simp [planarW1Value, planarJGradientW1, planarJGradient,
      planarQuarterTurn, h.gradient_eq]
  · have hi1 : i = 1 := fin2_eq_one_of_ne_zero hi
    subst i
    simp [planarW1Value, planarJGradientW1, planarJGradient,
      planarQuarterTurn, h.gradient_eq]

private theorem planarW1Derivative_planarJGradientW1 {Q : TriadicCube 2}
    (h : PlanarW2Infinity Q) (x : Vec 2) :
    planarW1Derivative (planarJGradientW1 h) x =
      fun i j => planarQuarterTurn (fun k => planarW1Derivative h.gradient x k j) i := by
  funext i j
  by_cases hi : i = 0
  · subst i
    simp [planarW1Derivative, planarJGradientW1, planarQuarterTurn,
      Pi.neg_apply]
  · have hi1 : i = 1 := fin2_eq_one_of_ne_zero hi
    subst i
    simp [planarW1Derivative, planarJGradientW1, planarQuarterTurn]

private theorem planarJGradientW1_valueLInf {Q : TriadicCube 2}
    (h : PlanarW2Infinity Q) :
    planarW1ValueLInf (planarJGradientW1 h) = planarGradientLInf h := by
  have hfun : (fun x => planarEuclideanNorm
      (planarW1Value (planarJGradientW1 h) x)) =
      (fun x => planarEuclideanNorm (planarW1Value h.gradient x)) := by
    funext x
    rw [planarW1Value_planarJGradientW1]
    have hgrad : planarJGradient h x =
        planarQuarterTurn (planarW1Value h.gradient x) := by
      funext i
      by_cases hi : i = 0
      · subst i
        simp [planarJGradient, planarW1Value, planarQuarterTurn, h.gradient_eq]
      · have hi1 : i = 1 := fin2_eq_one_of_ne_zero hi
        subst i
        simp [planarJGradient, planarW1Value, planarQuarterTurn, h.gradient_eq]
    rw [hgrad, planarEuclideanNorm_quarterTurn]
  rw [planarW1ValueLInf, planarGradientLInf, planarW1ValueLInf, hfun]

private theorem planarJGradientW1_derivativeLInf {Q : TriadicCube 2}
    (h : PlanarW2Infinity Q) :
    planarW1DerivativeFrobeniusLInf (planarJGradientW1 h) =
      planarHessianFrobeniusLInf h := by
  have hfun : (fun x => planarFrobeniusNorm
      (planarW1Derivative (planarJGradientW1 h) x)) =
      (fun x => planarFrobeniusNorm (planarW1Derivative h.gradient x)) := by
    funext x
    rw [planarW1Derivative_planarJGradientW1]
    exact planarFrobeniusNorm_quarterTurnRows _
  rw [planarW1DerivativeFrobeniusLInf,
    planarHessianFrobeniusLInf, planarW1DerivativeFrobeniusLInf, hfun]

/-- The planar product/Poincaré estimate with the exact positive-Haar
Dirichlet constant and vector-valued weak-gradient norm. -/
theorem planar_product_poincare (Q : TriadicCube 2)
    (u : H10Function (openCubeSet Q)) (h : PlanarW2Infinity Q) :
    vectorPositiveHaarNorm Q
        (fun x i => planarJGradient h x i * u.toH1Function.toFun x) ≤
      (cubeScaleFactor Q * planarFD * planarGradientLInf h +
        cubeScaleFactor Q ^ 2 * planarCD * planarC1 *
          planarHessianFrobeniusLInf h) *
        vectorWeakHaarNorm Q (fun x i => u.toH1Function.grad x i) := by
  let b := planarJGradientW1 h
  have hMnonneg : 0 ≤ planarW1ValueLInf b := by
    dsimp [b]
    rw [planarJGradientW1_valueLInf]
    dsimp [planarGradientLInf, planarW1ValueLInf]
    positivity
  have hDnonneg : 0 ≤ planarW1DerivativeFrobeniusLInf b := by
    dsimp [b]
    rw [planarJGradientW1_derivativeLInf]
    dsimp [planarHessianFrobeniusLInf, planarW1DerivativeFrobeniusLInf]
    positivity
  have hFD : 0 ≤ planarFD := by dsimp [planarFD]; positivity
  have hCD : 0 ≤ planarCD := by dsimp [planarCD]; positivity
  have hC1 : 0 ≤ planarC1 := Real.sqrt_nonneg _
  have hdirP := dirichlet_positiveHaar_bridge Q u
  have hdirL2 := dirichlet_L2_bridge Q u
  have hmul := vectorPositiveHaarNorm_mul_le Q b u.toH1Function
  have hvalue : planarW1Value b = planarJGradient h := by
    exact planarW1Value_planarJGradientW1 h
  have hnormEq : vectorPositiveHaarNorm Q
      (fun x i => planarW1Value b x i * u.toH1Function.toFun x) =
      vectorPositiveHaarNorm Q
        (fun x i => planarJGradient h x i * u.toH1Function.toFun x) := by
    congr 1
    funext x i
    rw [hvalue]
  rw [← hnormEq]
  calc
    vectorPositiveHaarNorm Q
        (fun x i => planarW1Value b x i * u.toH1Function.toFun x) ≤
      planarW1ValueLInf b * positiveHaarNorm Q u.toH1Function.toFun +
        cubeScaleFactor Q * planarC1 *
          planarW1DerivativeFrobeniusLInf b *
            Real.sqrt (energy Q u.toH1Function.toFun) := hmul
    _ ≤ planarW1ValueLInf b *
          (cubeScaleFactor Q * planarFD *
            vectorWeakHaarNorm Q (fun x i => u.toH1Function.grad x i)) +
        cubeScaleFactor Q * planarC1 *
          planarW1DerivativeFrobeniusLInf b *
            (cubeScaleFactor Q * planarCD *
              vectorWeakHaarNorm Q (fun x i => u.toH1Function.grad x i)) := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_left hdirP hMnonneg
          · have hcoef : 0 ≤ cubeScaleFactor Q * planarC1 *
                planarW1DerivativeFrobeniusLInf b :=
              mul_nonneg (mul_nonneg (cubeScaleFactor_pos' Q).le hC1) hDnonneg
            exact mul_le_mul_of_nonneg_left hdirL2 hcoef
    _ = (cubeScaleFactor Q * planarFD * planarGradientLInf h +
          cubeScaleFactor Q ^ 2 * planarCD * planarC1 *
            planarHessianFrobeniusLInf h) *
          vectorWeakHaarNorm Q (fun x i => u.toH1Function.grad x i) := by
            rw [planarJGradientW1_valueLInf, planarJGradientW1_derivativeLInf]
            ring

end ASDExplicitGamma.Triadic

end
