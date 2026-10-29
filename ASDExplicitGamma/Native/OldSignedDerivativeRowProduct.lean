module

public import ASDExplicitGamma.Native.OldSignedDirichletFamily
public import ASDExplicitGamma.Inverse.PureFluxGeneratorRowOperator

/-! Actual derivative-only physical covariance row on distinct zero-trace
potentials, retaining the sharp row covariance eigenvalues. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Gaussian ASDExplicitGamma.Main
open ASDExplicitGamma.Triadic ASDExplicitGamma.Inverse
noncomputable section

/-- The existing sharper Dirichlet bridges give this derivative-only bill. -/
def oldSignedDerivativeRowCoefficient (r b L : ℝ) : ℝ :=
  r*planarFD*Real.sqrt ((78/5)*b^2/L^2)+
    r^2*planarCD*planarC1*Real.sqrt ((23244/25)*b^2/L^4)

/-- The genuine q3 derivative row acting on distinct zero-boundary
potentials obeys the derivative-only positive-Haar bound. No Gaussian
sample supremum, transposed column bound or common-potential premise occurs. -/
theorem old_signed_derivative_row_product {I : Type*} (e : HilbertBasis I ℝ WhiteNoise)
    (Q : TriadicCube 2) (b : ℝ) (L : {l : ℝ // 0 < l}) (s : Finset I)
    (u : I → H10Function (openCubeSet Q)) :
    let F := oldSignedDirichletFamily Q (fun n : s => u n)
    let B := pureFluxQ3DerivativeRow e s b L Q
    Summable (fun j => (Real.sqrt 3)^(j+1)*hilbertEnergy Q
      (hilbertCubeIncrement Q (j+1) (fun x => B.toFun x (F.toFun x)))) ∧
    hilbertPositiveHaarNorm Q (Real.sqrt 3) (fun x => B.toFun x (F.toFun x))≤
      oldSignedDerivativeRowCoefficient (cubeScaleFactor Q) b L.1*
        Real.sqrt (∑ n : s,vectorWeakHaarNorm Q (fun x k => (u n).toH1Function.grad x k)^2) := by
  intro F B
  have hq : 1<Real.sqrt 3 := by
    nlinarith only [Real.sq_sqrt (by norm_num : (0:ℝ)≤3),Real.sqrt_nonneg (3:ℝ)]
  have hq9 : Real.sqrt 3<9 := by
    nlinarith only [Real.sq_sqrt (by norm_num : (0:ℝ)≤3),Real.sqrt_nonneg (3:ℝ)]
  have hp := (old_signed_hilbert_h1_positive_bound Q F).1
  have hM : 0≤(78/5:ℝ)*b^2/L.1^2 := by positivity
  have hD : 0≤(23244/25:ℝ)*b^2/L.1^4 := by positivity
  have hm : ∀ᵐ x ∂normalizedCubeMeasure Q,‖B.toFun x‖≤Real.sqrt ((78/5)*b^2/L.1^2) :=
    Filter.Eventually.of_forall (pureFluxQ3DerivativeRow_norm_le e s b L Q)
  have hd : ∀ᵐ x ∂normalizedCubeMeasure Q,∀ v : EuclideanSpace ℝ s,
      (∑ i,‖B.grad x i v‖^2)≤(Real.sqrt ((23244/25)*b^2/L.1^4))^2*‖v‖^2 := by
    filter_upwards with x v
    rw [Real.sq_sqrt hD]
    exact pureFluxQ3DerivativeRow_combined_gradient_le e s b L Q x v
  have ht := pureFlux_positive_product_of_combined_bounds B hq hq9 (F.memL2_normalized Q) hp
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hm hd
  have hc1 : Real.sqrt (haarPoincareM2 (Real.sqrt 3))=planarC1 := by
    unfold haarPoincareM2
    rw [mul_comm (1-Real.sqrt 3/9)]
    rfl
  rw [hc1] at ht
  have hR : 0≤cubeScaleFactor Q*planarC1*Real.sqrt ((23244/25)*b^2/L.1^4) :=
    mul_nonneg (mul_nonneg (Triadic.cubeScaleFactor_pos' Q).le (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  have hh := add_le_add
    (mul_le_mul_of_nonneg_left (old_signed_dirichlet_family_positive_bound Q (fun n : s => u n))
      (Real.sqrt_nonneg ((78/5)*b^2/L.1^2)))
    (mul_le_mul_of_nonneg_left (old_signed_dirichlet_family_l2_bound Q (fun n : s => u n)) hR)
  refine ⟨ht.1,ht.2.trans (hh.trans_eq ?_)⟩
  unfold oldSignedDerivativeRowCoefficient
  ring

end
end ASDExplicitGamma.Native
