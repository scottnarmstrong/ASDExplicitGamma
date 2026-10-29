module

public import ASDExplicitGamma.Native.OldSignedDerivativeConstants
public import ASDExplicitGamma.Native.OldSignedRemainderCovarianceVector
public import ASDExplicitGamma.Main.HilbertCoordinateMembership

/-! AN (3.2) for literal finite physical column-divergence rows and
arbitrary distinct actual H10 potentials in the white directions. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Gaussian ASDExplicitGamma.Main
open ASDExplicitGamma.Triadic ASDExplicitGamma.Inverse ASDExplicitGamma.Response
noncomputable section

/-- The physical derivative gradient row before its column-divergence rotation. -/
def oldSignedDerivativeGradientRow {I : Type*} (e : HilbertBasis I ℝ WhiteNoise)
    (s : Finset I) (b : ℝ) (L : {l : ℝ // 0 < l}) (Q : TriadicCube 2)
    (u : I → H10Function (openCubeSet Q)) (x : Vec 2) (k : Fin 2) : ℝ :=
  ∑ n : s,(u n).toH1Function x*q3Convolution b L (mainQ3JetIndex (.first k)) (e n) x

/-- The literal sum phi_j div(H_j), with divergence taken down columns. -/
def oldSignedDerivativeRow {I : Type*} (e : HilbertBasis I ℝ WhiteNoise)
    (s : Finset I) (b : ℝ) (L : {l : ℝ // 0 < l}) (Q : TriadicCube 2)
    (u : I → H10Function (openCubeSet Q)) (x : Vec 2) (k : Fin 2) : ℝ :=
  ∑ n : s,(u n).toH1Function x*(∑ j : Fin 2,responsePlanarJ j k*
    q3Convolution b L (mainQ3JetIndex (.first j)) (e n) x)

/-- The existing actual row operator has precisely these distinct-potential
physical coordinates, rather than a common source substituted afterward. -/
theorem old_signed_derivative_gradient_row_operator {I : Type*} (e : HilbertBasis I ℝ WhiteNoise)
    (s : Finset I) (b : ℝ) (L : {l : ℝ // 0 < l}) (Q : TriadicCube 2)
    (u : I → H10Function (openCubeSet Q)) (x : Vec 2) (k : Fin 2) :
    ((pureFluxQ3DerivativeRow e s b L Q).toFun x
      ((oldSignedDirichletFamily Q (fun n : s => u n)).toFun x)).ofLp k=
      oldSignedDerivativeGradientRow e s b L Q u x k := by
  rw [pureFluxQ3DerivativeRow_apply]
  rfl

/-- The column divergence of psi J is -J grad psi. Both the sign and the
rotation occur before any covariance or norm estimate. -/
theorem old_signed_derivative_row_rotation {I : Type*} (e : HilbertBasis I ℝ WhiteNoise)
    (s : Finset I) (b : ℝ) (L : {l : ℝ // 0 < l}) (Q : TriadicCube 2)
    (u : I → H10Function (openCubeSet Q)) :
    oldSignedDerivativeRow e s b L Q u=fun x =>
      planarQuarterTurn (fun k => -oldSignedDerivativeGradientRow e s b L Q u x k) := by
  funext x k
  fin_cases k <;> simp [oldSignedDerivativeRow,oldSignedDerivativeGradientRow,
    responsePlanarJ,Fin.sum_univ_two,planarQuarterTurn]

/-- Global sign preserves the actual vector positive norm. -/
theorem old_signed_vector_positive_neg (Q : TriadicCube 2) (F : Vec 2 → Vec 2) :
    vectorPositiveHaarNorm Q (fun x k => -F x k)=vectorPositiveHaarNorm Q F := by
  simp only [vectorPositiveHaarNorm,vectorPositiveHaarEnergy,primalEnergy_neg]

/-- Exact derivative-only row estimate AN (3.2) with the actual sharp q3
row variances, for every finite subfamily of the complete physical white basis. -/
theorem old_signed_derivative_row_bound {I : Type*} (e : HilbertBasis I ℝ WhiteNoise)
    (s : Finset I) (b : ℝ) (L : {l : ℝ // 0 < l}) (Q : TriadicCube 2)
    (u : I → H10Function (openCubeSet Q)) :
    (∀ k,Summable (fun j => (Real.sqrt 3)^(j+1)*energy Q
      (cubeIncrement Q (j+1) (fun x => oldSignedDerivativeRow e s b L Q u x k)))) ∧
    vectorPositiveHaarNorm Q (oldSignedDerivativeRow e s b L Q u)≤
      oldSignedDerivativeKappa (cubeScaleFactor Q) b L.1*
        Real.sqrt (∑ n : s,vectorWeakHaarNorm Q (fun x k => (u n).toH1Function.grad x k)^2) := by
  let F := oldSignedDirichletFamily Q (fun n : s => u n)
  let B := pureFluxQ3DerivativeRow e s b L Q
  let G := oldSignedDerivativeGradientRow e s b L Q u
  have hm : MemLp (fun x => B.toFun x (F.toFun x)) 2 (normalizedCubeMeasure Q) :=
    B.product_memLp (F.memL2_normalized Q)
  have ht := old_signed_derivative_row_product e Q b L s u
  have he : (fun x => WithLp.toLp 2 (G x))=fun x => B.toFun x (F.toFun x) := by
    funext x
    apply PiLp.ext
    intro k
    exact (old_signed_derivative_gradient_row_operator e s b L Q u x k).symm
  have hcoord k : (fun x => ((B.toFun x) (F.toFun x)).ofLp k)=fun x => G x k := by
    funext x
    exact old_signed_derivative_gradient_row_operator e s b L Q u x k
  have hscalar k : MemLp (fun x => G x k) 2 (normalizedCubeMeasure Q) := by
    have hc := (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) k).comp_memLp' hm
    change MemLp (fun x => ((B.toFun x) (F.toFun x)).ofLp k) 2 (normalizedCubeMeasure Q) at hc
    rw [hcoord] at hc
    exact hc
  have hseries k : Summable (fun j => (Real.sqrt 3)^(j+1)*energy Q
      (cubeIncrement Q (j+1) (fun x => G x k))) := by
    have hc := main_hilbert_coordinate_summable Q hm ht.1 k
    rw [hcoord] at hc
    exact hc
  have hn := ht.2
  rw [←he,main_hilbertPositive_eq_vectorPositive Q hscalar hseries] at hn
  have hk := mul_le_mul_of_nonneg_right
    (old_signed_derivative_row_coefficient_le_kappa (Triadic.cubeScaleFactor_pos' Q).le b L.1)
    (Real.sqrt_nonneg (∑ n : s,vectorWeakHaarNorm Q (fun x k => (u n).toH1Function.grad x k)^2))
  rw [old_signed_derivative_row_rotation]
  refine ⟨positive_series_quarterTurn Q (fun x k => -G x k) (fun k => ?_),?_⟩
  · simp_rw [cubeIncrement_neg,energy_neg]
    exact hseries k
  · rw [vectorPositiveHaarNorm_quarterTurn,old_signed_vector_positive_neg]
    exact hn.trans hk

end
end ASDExplicitGamma.Native
