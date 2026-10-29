module

public import ASDExplicitGamma.Native.OldSignedOldErrorPotentialSeries
public import ASDExplicitGamma.Native.OldSignedCompleteCellFeedback

/-! The complete physical derivative feedback of the actual OLD-error
piece R, with convergence supplied by its proved physical construction. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Scalar ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Triadic
noncomputable section

/-- The complete actual R feedback satisfies the sharp derivative row
bound. All cell potentials and reciprocal tests are constructed from the
same physical data, and the signed series is proved genuinely summable. -/
theorem old_signed_complete_old_error_feedback {A : Type*} [Fintype A]
    (m : ℤ) (mesh : ℕ) (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet (originCube 2 m))) (P : A → BlockVec 2)
    (b : ℝ) (L : {l : ℝ // 0<l})
    (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth (originCube 2 m) mesh) :
    let Q := originCube 2 m
    let hsub := openCubeSet_subset_of_mem_descendantsAtDepth hU
    let R := fun n a => oldSignedCellResidual Q U hsub nu sigma hnu hsigma k
      (oldSignedFrameOldErrorSource Q mesh nu sigma hnu hsigma k b L n (P a))
      (old_signed_frame_old_error_source_memL2 Q mesh nu sigma hnu hsigma k b L n (P a))
    let u := fun n a => oldSignedCellErrorPotential Q U hsub mesh nu sigma hnu hsigma k b L n (P a)
    let g := fun a => oldSignedCellReciprocalPotential Q U hsub nu sigma hnu hsigma k (P a)
    let f := fun n => ∑ a : A,oldSignedEnergyPairing U nu sigma (oldSignedCellCoefficient Q U hsub k)
      (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k (P a))
      (oldSignedPointwiseShear (q3Convolution b L h3Zero (whiteBasis n)) (R n a))
    Summable f ∧ |∑' n,f n|≤
      oldSignedDerivativeKappa (cubeScaleFactor U) b L.1*
        Real.sqrt (∑ a : A,vectorWeakHaarNorm U (g a).grad^2)*
        Real.sqrt (∑ a : A,∑' n,vectorWeakHaarNorm U (u n a).toH1Function.grad^2) := by
  intro Q hsub R u g f
  let F := fun n a => oldSignedFrameOldErrorSource Q mesh nu sigma hnu hsigma k b L n (P a)
  have hF (n : whiteBasisIndex) (a : A) : MemBlockL2 (openCubeSet Q) (F n a) :=
    old_signed_frame_old_error_source_memL2 Q mesh nu sigma hnu hsigma k b L n (P a)
  have hu (a : A) : Summable (fun n => vectorWeakHaarNorm U
      (oldSignedCellFirstCorrector Q U hsub nu sigma hnu hsigma k (F n a) (hF n a)).toH1Function.grad^2) :=
    old_signed_old_error_cell_potential_summable m mesh nu sigma hnu hsigma k (P a) b L U hU
  have hh := old_signed_complete_cell_correction_feedback Q U hsub nu sigma hnu hsigma k P b L F hF hu
  have hz (n : whiteBasisIndex) (a : A) :
      oldSignedPointwiseShear (q3Convolution b L h3Zero (whiteBasis n)) (F n a)=0 := by
    funext x
    change (0,-(_ • matVecMul responsePlanarJ 0))=(0,0)
    rw [matVecMul_zero,smul_zero,neg_zero]
  let fc := fun n => ∑ a : A,oldSignedEnergyPairing U nu sigma (oldSignedCellCoefficient Q U hsub k)
    (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k (P a))
    (oldSignedPointwiseShear (q3Convolution b L h3Zero (whiteBasis n))
      ((R n a : Vec 2 → BlockVec 2)-F n a))
  have hfc : fc=f := by
    funext n
    apply Finset.sum_congr rfl
    intro a _
    rw [map_sub,hz,sub_zero]
  have hresult : Summable fc ∧ |∑' n,fc n|≤
      oldSignedDerivativeKappa (cubeScaleFactor U) b L.1*
        Real.sqrt (∑ a : A,vectorWeakHaarNorm U (g a).grad^2)*
        Real.sqrt (∑ a : A,∑' n,vectorWeakHaarNorm U (u n a).toH1Function.grad^2) := hh
  rw [hfc] at hresult
  exact hresult

end
end ASDExplicitGamma.Native
