module

public import ASDExplicitGamma.Native.OldSignedPhysicalDerivativeFeedback
public import ASDExplicitGamma.Native.OldSignedFiniteSumLimit

/-! Genuine complete-mode OLD physical feedback. Summability is proved
from bounds on all finite subfamilies, before the signed real sum is used. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Main ASDExplicitGamma.Triadic
noncomputable section

/-- Complete physical derivative feedback for a square-summable family of
actual zero-boundary cell potentials. The series is summable, rather than
a real tsum whose nonsummable case could silently totalize to zero. -/
theorem old_signed_complete_physical_derivative_feedback {I A : Type*} [Fintype A]
    (e : HilbertBasis I ℝ WhiteNoise) (Q : TriadicCube 2)
    (b : ℝ) (L : {l : ℝ // 0<l})
    (u : I → A → H10Function (openCubeSet Q)) (g : A → H1Function (openCubeSet Q))
    (hu : ∀ a,Summable (fun n => vectorWeakHaarNorm Q (u n a).toH1Function.grad^2)) :
    let f := fun n => ∑ a : A,volumeAverage (openCubeSet Q) (fun x => vecDot
      (q3Convolution b L h3Zero (e n) x • matVecMul responsePlanarJ ((u n a).toH1Function.grad x))
      ((g a).grad x))
    Summable f ∧ |∑' n,f n|≤
      oldSignedDerivativeKappa (cubeScaleFactor Q) b L.1*
        Real.sqrt (∑ a : A,vectorWeakHaarNorm Q (g a).grad^2)*
        Real.sqrt (∑ a : A,∑' n,vectorWeakHaarNorm Q (u n a).toH1Function.grad^2) := by
  intro f
  apply old_signed_real_sum_of_finite_bound
  intro s
  have h := old_signed_finite_physical_derivative_feedback e s Q b L u g
  have he : (∑ a : A,∑ n : s,vectorWeakHaarNorm Q (u n a).toH1Function.grad^2)≤
      ∑ a : A,∑' n,vectorWeakHaarNorm Q (u n a).toH1Function.grad^2 := by
    apply Finset.sum_le_sum
    intro a _
    rw [Finset.sum_coe_sort s (fun n => vectorWeakHaarNorm Q (u n a).toH1Function.grad^2)]
    exact (hu a).sum_le_tsum s (fun n _ => sq_nonneg _)
  have hp : 0≤oldSignedDerivativeKappa (cubeScaleFactor Q) b L.1*
      Real.sqrt (∑ a : A,vectorWeakHaarNorm Q (g a).grad^2) :=
    mul_nonneg (old_signed_derivative_kappa_nonneg (Triadic.cubeScaleFactor_pos' Q).le b L.1)
      (Real.sqrt_nonneg _)
  have hb := h.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt he) hp)
  have hs : (∑ a : A,∑ n : s,volumeAverage (openCubeSet Q) (fun x => vecDot
      (q3Convolution b L h3Zero (e n) x • matVecMul responsePlanarJ ((u n a).toH1Function.grad x))
      ((g a).grad x)))=∑ n ∈ s,f n := by
    rw [Finset.sum_comm]
    exact Finset.sum_coe_sort s f
  rw [hs] at hb
  exact hb

end
end ASDExplicitGamma.Native
