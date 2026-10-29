module

public import ASDExplicitGamma.Native.OldSignedPhysicalModeTesting
public import ASDExplicitGamma.Native.OldSignedFlatModeDecomposition

/-! Exact spatial testing of the actual output-rotated harmonic covariance
and integrability of every literal finite physical mode pairing. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Gaussian ASDExplicitGamma.Main ASDExplicitGamma.Triadic
open ASDExplicitGamma.Response
noncomputable section

/-- Actual output-rotated harmonic mode, as a genuine scalar H1 function. -/
def oldSignedOutputRemainderH1 (Q : TriadicCube 2) (b : ℝ) (L : {l : ℝ // 0 < l})
    (plus : Bool) (n : whiteBasisIndex) (i k : Fin 2) : H1Function (openCubeSet Q) :=
  ∑ l : Fin 2,responsePlanarJ k l • oldSignedRemainderCoordinate Q b L plus n (i,l)

/-- Its H1 representative is the literal source output rotation. -/
theorem old_signed_output_remainder_h1_toFun (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (plus : Bool) (n : whiteBasisIndex) (i k : Fin 2) :
    (oldSignedOutputRemainderH1 Q b L plus n i k).toFun=
      fun x => matVecMul responsePlanarJ (fun l => oldSignedRemainderCoordinate Q b L plus n (i,l) x) k := by
  simp only [oldSignedOutputRemainderH1,Fin.sum_univ_two,H1Function.add_toFun,H1Function.smul_toFun]
  funext x
  simp only [matVecMul,Fin.sum_univ_two]

/-- The actual rotated harmonic covariance passes through its L2 spatial
test, with the physical output sign unchanged. -/
theorem old_signed_rotated_remainder_covariance_integral (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (plus : Bool) (i k : Fin 2) (r : Vec 2 → ℝ)
    (hr : MemLp r 2 (normalizedCubeMeasure Q)) :
    HasSum (fun n : whiteBasisIndex => ∫ x,r x*
      q3Convolution b L h3Zero (whiteBasis n) x*
        matVecMul responsePlanarJ (fun l => oldSignedRemainderCoordinate Q b L plus n (i,l) x) k
          ∂normalizedCubeMeasure Q)
      (∫ x,r x*oldSignedRemainderCovarianceField Q b L plus i x k ∂normalizedCubeMeasure Q) := by
  fin_cases k
  · simpa [matVecMul,responsePlanarJ,Fin.sum_univ_two,
      oldSignedRemainderCovarianceField,planarQuarterTurn,integral_neg] using
      (old_signed_remainder_covariance_integral Q b L plus (i,1) r hr).neg
  · simpa [matVecMul,responsePlanarJ,Fin.sum_univ_two,
      oldSignedRemainderCovarianceField,planarQuarterTurn] using
      old_signed_remainder_covariance_integral Q b L plus (i,0) r hr

end
end ASDExplicitGamma.Native
