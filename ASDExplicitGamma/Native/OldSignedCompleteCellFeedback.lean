module

public import ASDExplicitGamma.Native.OldSignedCellCorrectionFeedback
public import ASDExplicitGamma.Native.OldSignedCompleteDerivativeFeedback

/-! Complete physical feedback of the actual weighted cell corrections.
The infinite signed series is proved summable from actual potential energies. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Scalar ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Triadic
noncomputable section

/-- Complete feedback of the same actual cell corrections and parent
minimizers. Square-summability is an internal convergence input, to be
supplied by the quantitative source projection bounds at the assembly. -/
theorem old_signed_complete_cell_correction_feedback {A : Type*} [Fintype A]
    (Q U : TriadicCube 2) (hU : openCubeSet U ⊆ openCubeSet Q)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (P : A → BlockVec 2)
    (b : ℝ) (L : {l : ℝ // 0<l})
    (F : whiteBasisIndex → A → Vec 2 → BlockVec 2)
    (hF : ∀ n a,MemBlockL2 (openCubeSet Q) (F n a)) :
    let R := fun n a => oldSignedCellResidual Q U hU nu sigma hnu hsigma k (F n a) (hF n a)
    let u := fun n a => oldSignedCellFirstCorrector Q U hU nu sigma hnu hsigma k (F n a) (hF n a)
    let g := fun a => oldSignedCellReciprocalPotential Q U hU nu sigma hnu hsigma k (P a)
    let f := fun n => ∑ a : A,oldSignedEnergyPairing U nu sigma (oldSignedCellCoefficient Q U hU k)
      (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k (P a))
      (oldSignedPointwiseShear (q3Convolution b L h3Zero (whiteBasis n))
        ((R n a : Vec 2 → BlockVec 2)-F n a))
    (∀ a,Summable (fun n => vectorWeakHaarNorm U (u n a).toH1Function.grad^2)) →
      Summable f ∧ |∑' n,f n|≤
        oldSignedDerivativeKappa (cubeScaleFactor U) b L.1*
          Real.sqrt (∑ a : A,vectorWeakHaarNorm U (g a).grad^2)*
          Real.sqrt (∑ a : A,∑' n,vectorWeakHaarNorm U (u n a).toH1Function.grad^2) := by
  intro R u g f hu
  have h := old_signed_complete_physical_derivative_feedback whiteBasis U b L u g hu
  have he (n : whiteBasisIndex) (a : A) :
      oldSignedEnergyPairing U nu sigma (oldSignedCellCoefficient Q U hU k)
        (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k (P a))
        (oldSignedPointwiseShear (q3Convolution b L h3Zero (whiteBasis n))
          ((R n a : Vec 2 → BlockVec 2)-F n a))=
        -volumeAverage (openCubeSet U) (fun x => vecDot
          (q3Convolution b L h3Zero (whiteBasis n) x •
            matVecMul responsePlanarJ ((u n a).toH1Function.grad x)) ((g a).grad x)) :=
    old_signed_cell_correction_shear_pairing Q U hU nu sigma hnu hsigma k (P a) b L n (F n a) (hF n a)
  have hf : f=fun n => -(∑ a : A,volumeAverage (openCubeSet U) (fun x => vecDot
      (q3Convolution b L h3Zero (whiteBasis n) x •
        matVecMul responsePlanarJ ((u n a).toH1Function.grad x)) ((g a).grad x))) := by
    funext n
    dsimp only [f]
    simp_rw [he]
    rw [Finset.sum_neg_distrib]
  rw [hf]
  refine ⟨h.1.neg,?_⟩
  simpa only [tsum_neg,abs_neg] using h.2

end
end ASDExplicitGamma.Native
