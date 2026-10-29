module

public import ASDExplicitGamma.Native.OldSignedQ3DerivativePairing

/-! Finite physical OLD feedback, with distinct zero-boundary potentials
for every white direction, controlled by the sharp derivative-only row. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Main ASDExplicitGamma.Triadic
noncomputable section

/-- Summing the exact physical cancellation gives precisely the literal
finite derivative row, before applying any weak/positive norm inequality. -/
theorem old_signed_finite_physical_derivative_pairing {I : Type*}
    (e : HilbertBasis I ℝ WhiteNoise) (s : Finset I) (Q : TriadicCube 2)
    (b : ℝ) (L : {l : ℝ // 0<l}) (u : I → H10Function (openCubeSet Q))
    (g : H1Function (openCubeSet Q)) :
    (∑ n : s,volumeAverage (openCubeSet Q) (fun x => vecDot
      (q3Convolution b L h3Zero (e n) x • matVecMul responsePlanarJ ((u n).toH1Function.grad x))
      (g.grad x)))=
      ∑ k : Fin 2,pairing Q (fun x => g.grad x k)
        (fun x => oldSignedDerivativeRow e s b L Q u x k) := by
  classical
  have hmem (n : I) (k : Fin 2) : MemLp
      (fun x => (u n).toH1Function x*oldSignedQ3ColumnDivergence b L (e n) x k)
      2 (normalizedCubeMeasure Q) := by
    have hc : Continuous (fun x => oldSignedQ3ColumnDivergence b L (e n) x k) := by
      apply continuous_finsetSum
      intro j _
      exact continuous_const.mul (q3Convolution_continuous b L (mainQ3JetIndex (.first j)) (e n))
    exact (u n).toH1Function.memL2_normalizedCubeMeasure.fun_mul (main_continuous_memLp_top Q hc)
  have hint (n : I) (k : Fin 2) : Integrable
      (fun x => (u n).toH1Function x*oldSignedQ3ColumnDivergence b L (e n) x k*g.grad x k)
      (normalizedCubeMeasure Q) :=
    (hmem n k).integrable_mul (g.grad_memL2_normalizedCubeMeasure k)
  have hone (n : I) : volumeAverage (openCubeSet Q) (fun x => vecDot
      (q3Convolution b L h3Zero (e n) x • matVecMul responsePlanarJ ((u n).toH1Function.grad x))
      (g.grad x))=
      ∑ k : Fin 2,∫ x,(u n).toH1Function x*oldSignedQ3ColumnDivergence b L (e n) x k*g.grad x k
        ∂normalizedCubeMeasure Q := by
    rw [old_signed_q3_zero_trace_pairing Q b L (e n) (u n) g]
    unfold volumeAverage
    rw [volume_openCubeSet_toReal,←integral_normalized_eq_open]
    change (∫ x,∑ k : Fin 2,(u n).toH1Function x*
      oldSignedQ3ColumnDivergence b L (e n) x k*g.grad x k ∂normalizedCubeMeasure Q)=_
    exact integral_finsetSum Finset.univ (fun k _ => hint n k)
  simp_rw [hone]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [pairing,cubeAverage_eq_integral_normalizedCubeMeasure]
  rw [←integral_finsetSum Finset.univ (fun n : s => fun _ => hint n k)]
  apply integral_congr_ae
  filter_upwards with x
  simp only [oldSignedDerivativeRow,oldSignedQ3ColumnDivergence,Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Joint physical feedback for every finite load and white-mode family.
All direction-dependent first potentials and reciprocal tests remain in
this same actual cell. -/
theorem old_signed_finite_physical_derivative_feedback {I A : Type*} [Fintype A]
    (e : HilbertBasis I ℝ WhiteNoise) (s : Finset I) (Q : TriadicCube 2)
    (b : ℝ) (L : {l : ℝ // 0<l})
    (u : I → A → H10Function (openCubeSet Q)) (g : A → H1Function (openCubeSet Q)) :
    |∑ a : A,∑ n : s,volumeAverage (openCubeSet Q) (fun x => vecDot
      (q3Convolution b L h3Zero (e n) x • matVecMul responsePlanarJ ((u n a).toH1Function.grad x))
      ((g a).grad x))|≤
      oldSignedDerivativeKappa (cubeScaleFactor Q) b L.1*
        Real.sqrt (∑ a : A,vectorWeakHaarNorm Q (g a).grad^2)*
        Real.sqrt (∑ a : A,∑ n : s,vectorWeakHaarNorm Q (u n a).toH1Function.grad^2) := by
  have he (a : A) := old_signed_finite_physical_derivative_pairing e s Q b L (fun n => u n a) (g a)
  have hs := Finset.sum_congr (s₁ := Finset.univ) rfl (fun a _ => he a)
  rw [hs]
  exact old_signed_derivative_feedback_bound e s b L Q g u

end
end ASDExplicitGamma.Native
