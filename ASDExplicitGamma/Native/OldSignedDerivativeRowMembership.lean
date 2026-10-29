module

public import ASDExplicitGamma.Native.OldSignedDerivativeRow

/-! Genuine spatial membership of every finite physical derivative row,
prior to applying weak/positive duality to the feedback. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Gaussian ASDExplicitGamma.Main ASDExplicitGamma.Triadic
open ASDExplicitGamma.Response
noncomputable section

/-- Every literal finite derivative row coordinate belongs to spatial L2. -/
theorem old_signed_derivative_row_memLp {I : Type*} (e : HilbertBasis I ℝ WhiteNoise)
    (s : Finset I) (b : ℝ) (L : {l : ℝ // 0 < l}) (Q : TriadicCube 2)
    (u : I → H10Function (openCubeSet Q)) (k : Fin 2) :
    MemLp (fun x => oldSignedDerivativeRow e s b L Q u x k) 2 (normalizedCubeMeasure Q) := by
  have hc n : Continuous (fun x => ∑ j : Fin 2,responsePlanarJ j k*
      q3Convolution b L (mainQ3JetIndex (.first j)) (e n) x) := by
    apply continuous_finsetSum
    intro j _
    exact continuous_const.mul (q3Convolution_continuous b L (mainQ3JetIndex (.first j)) (e n))
  have ht n : MemLp (fun x => (u n).toH1Function x*(∑ j : Fin 2,responsePlanarJ j k*
      q3Convolution b L (mainQ3JetIndex (.first j)) (e n) x)) 2 (normalizedCubeMeasure Q) :=
    (u n).toH1Function.memL2_normalizedCubeMeasure.fun_mul (main_continuous_memLp_top Q (hc n))
  simpa only [oldSignedDerivativeRow,Finset.sum_apply] using
    (memLp_finsetSum Finset.univ (fun n : s => fun _ => ht n))

/-- The actual derivative-only source coefficient is nonnegative. -/
theorem old_signed_derivative_kappa_nonneg {r : ℝ} (hr : 0≤r) (b L : ℝ) :
    0≤oldSignedDerivativeKappa r b L := by
  unfold oldSignedDerivativeKappa
  have h0 : 0≤planarC0 := Real.sqrt_nonneg _
  have h1 : 0≤planarC1 := Real.sqrt_nonneg _
  positivity

end
end ASDExplicitGamma.Native
