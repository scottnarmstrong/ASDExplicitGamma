module

public import ASDExplicitGamma.Scalar.OldHessianTrialColumnRestriction
public import ASDExplicitGamma.Main.Q3W2Jets
public import ASDExplicitGamma.Native.OldSignedShearGauge

/-! The actual retained coarse product phi div H, with its complete fine
positive norm and the genuine coarse column polynomial. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Main Triadic Gaussian Variational
noncomputable section

/-- The retained physical product in the mixed source. -/
def oldHessianCoarseProduct (Q : TriadicCube 2) (b : ℝ) (L : {l : ℝ // 0<l})
    (u : H10Function (openCubeSet Q)) (w : WhiteNoise) : Vec 2 → Vec 2 :=
  fun x => u.toH1Function x •
    lemmaVPlanarWeakColumnDivergence (mainQ3DirectionW2 Q b L w).value x

/-- Literal physical identification, including the column-divergence sign. -/
theorem old_hessian_coarse_product_value (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0<l}) (u : H10Function (openCubeSet Q)) (w : WhiteNoise) :
    oldHessianCoarseProduct Q b L u w = fun x => -planarQuarterTurn
      (fun i => u.toH1Function x*(fderiv ℝ (q3Convolution b L h3Zero w) x) (basisVec i)) := by
  funext x i
  change (u.toH1Function x • -(matVecMul Response.responsePlanarJ
    (fun k => (fderiv ℝ (q3Convolution b L h3Zero w) x) (basisVec k)))) i = _
  fin_cases i <;> simp [matVecMul,Response.responsePlanarJ,planarQuarterTurn,Fin.sum_univ_two]

/-- Signs and the planar rotation preserve the entire positive energy on
every fine cell, including the root coefficient. -/
theorem old_hessian_coarse_product_energy (Q U : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0<l}) (u : H10Function (openCubeSet Q)) (w : WhiteNoise) :
    vectorPositiveHaarEnergy U (oldHessianCoarseProduct Q b L u w) =
      vectorPositiveHaarEnergy U (fun x i => u.toH1Function x*
        (fderiv ℝ (q3Convolution b L h3Zero w) x) (basisVec i)) := by
  rw [old_hessian_coarse_product_value]
  unfold vectorPositiveHaarEnergy
  simp only [Fin.sum_univ_two,Pi.neg_apply,planarQuarterTurn,ite_true,
    show (1:Fin 2)≠0 by decide,ite_false,primalEnergy_neg]
  ring

/-- The retained product has genuine L2 membership and complete positive
Haar convergence on every actual fine descendant. Large parent constants
are used only for qualitative finiteness, never for the coarse payment. -/
theorem old_hessian_coarse_product_regular (Q : TriadicCube 2) (depth : ℕ) (b : ℝ)
    (L : {l : ℝ // 0<l}) (u : H10Function (openCubeSet Q)) (j : whiteBasisIndex)
    (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth Q depth) (i : Fin 2) :
    MemLp (fun x => oldHessianCoarseProduct Q b L u (whiteBasis j) x i) 2
      (normalizedCubeMeasure U) ∧
    Summable (fun k : ℕ => (Real.sqrt 3)^(k+1)*energy U (cubeIncrement U (k+1)
      (fun x => oldHessianCoarseProduct Q b L u (whiteBasis j) x i))) := by
  have he0 : (fun x => oldHessianCoarseProduct Q b L u (whiteBasis j) x 0)=
      (fun x => u.toH1Function x*
        (fderiv ℝ (q3Convolution b L h3Zero (whiteBasis j)) x) (basisVec 1)) := by
    rw [old_hessian_coarse_product_value]
    funext x
    simp [planarQuarterTurn]
  have he1 : (fun x => oldHessianCoarseProduct Q b L u (whiteBasis j) x 1)=
      (fun x => -(u.toH1Function x*
        (fderiv ℝ (q3Convolution b L h3Zero (whiteBasis j)) x) (basisVec 0))) := by
    rw [old_hessian_coarse_product_value]
    funext x
    simp [planarQuarterTurn]
  have hq : (0:ℝ)<Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  fin_cases i
  · change MemLp (fun x => oldHessianCoarseProduct Q b L u (whiteBasis j) x 0) 2
      (normalizedCubeMeasure U) ∧ Summable (fun k : ℕ => (Real.sqrt 3)^(k+1)*energy U
        (cubeIncrement U (k+1) (fun x => oldHessianCoarseProduct Q b L u (whiteBasis j) x 0)))
    rw [he0]
    have hh := old_hessian_column_coordinate_regular whiteBasis b L Q u j 1
    exact ⟨memLp_on_descendant_of_memLp hU hh.1,
      old_hessian_positive_descendant_summable Q depth hq hh.1 hh.2 U hU⟩
  · change MemLp (fun x => oldHessianCoarseProduct Q b L u (whiteBasis j) x 1) 2
      (normalizedCubeMeasure U) ∧ Summable (fun k : ℕ => (Real.sqrt 3)^(k+1)*energy U
        (cubeIncrement U (k+1) (fun x => oldHessianCoarseProduct Q b L u (whiteBasis j) x 1)))
    rw [he1]
    have hh := old_hessian_column_coordinate_regular whiteBasis b L Q u j 0
    refine ⟨(memLp_on_descendant_of_memLp hU hh.1).neg,?_⟩
    simp_rw [cubeIncrement_neg,energy_neg]
    exact old_hessian_positive_descendant_summable Q depth hq hh.1 hh.2 U hU

/-- Complete fine-broken norm of the literal retained product. The source's
coarse side/length ratio enters only this column term. -/
theorem old_hessian_coarse_product_broken (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0<l}) (u : H10Function (openCubeSet Q)) :
    let E := fun j : whiteBasisIndex => descendantsAverage Q 1 (fun U =>
      vectorPositiveHaarEnergy U (oldHessianCoarseProduct Q b L u (whiteBasis j)))
    Summable E ∧ (∑' j,E j) ≤
      (Real.sqrt 2*((503/200:ℝ)*(cubeScaleFactor Q/L.1)+
        (2031/500:ℝ)*(cubeScaleFactor Q/L.1)^2)*|b|)^2*
          vectorWeakHaarEnergy Q u.toH1Function.grad := by
  intro E
  have he : E=(fun j => descendantsAverage Q 1 (fun U => vectorPositiveHaarEnergy U
      (fun x i => u.toH1Function x*
        (fderiv ℝ (q3Convolution b L h3Zero (whiteBasis j)) x) (basisVec i)))) := by
    funext j
    unfold E
    simp_rw [old_hessian_coarse_product_energy]
  rw [he]
  have hh := old_hessian_column_broken_energy whiteBasis b L Q u
  refine ⟨hh.1,hh.2.trans ?_⟩
  have hc := mul_le_mul_of_nonneg_right
    (old_hessian_column_polynomial (Triadic.cubeScaleFactor_pos' Q).le b L.1 L.2)
    (Real.sqrt_nonneg (vectorWeakHaarEnergy Q u.toH1Function.grad))
  have hR := (Triadic.cubeScaleFactor_pos' Q).le
  have h0 : 0≤planarC0 := Real.sqrt_nonneg _
  have h1 : 0≤planarC1 := Real.sqrt_nonneg _
  have hn : 0≤oldSignedDerivativeKappa (cubeScaleFactor Q) (Real.sqrt 2*b) L.1*
      vectorWeakHaarNorm Q u.toH1Function.grad := by
    unfold oldSignedDerivativeKappa vectorWeakHaarNorm
    positivity
  have hb := pow_le_pow_left₀ hn hc 2
  simpa only [vectorWeakHaarNorm,mul_pow,Real.sq_sqrt (vectorWeakHaarEnergy_nonneg Q _)] using hb

end
end ASDExplicitGamma.Scalar
