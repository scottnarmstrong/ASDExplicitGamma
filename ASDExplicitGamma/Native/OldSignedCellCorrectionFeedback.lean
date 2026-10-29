module

public import ASDExplicitGamma.Native.OldSignedCellReciprocalPotential
public import ASDExplicitGamma.Native.OldSignedCellPotentials
public import ASDExplicitGamma.Native.OldSignedPhysicalDerivativeFeedback

/-! The derivative-only bound on the actual weighted cell corrections,
using the restricted parent reciprocal potentials from source recovery. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Scalar ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Triadic
noncomputable section

/-- Exact signed feedback of one actual weighted cell correction, with
its first potential and the restricted parent reciprocal test constructed. -/
theorem old_signed_cell_correction_shear_pairing (Q U : TriadicCube 2)
    (hU : openCubeSet U ⊆ openCubeSet Q) (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (P : BlockVec 2)
    (b : ℝ) (L : {l : ℝ // 0<l}) (n : whiteBasisIndex)
    (F : Vec 2 → BlockVec 2) (hF : MemBlockL2 (openCubeSet Q) F) :
    let R := oldSignedCellResidual Q U hU nu sigma hnu hsigma k F hF
    let phi := oldSignedCellFirstCorrector Q U hU nu sigma hnu hsigma k F hF
    let g := oldSignedCellReciprocalPotential Q U hU nu sigma hnu hsigma k P
    oldSignedEnergyPairing U nu sigma (oldSignedCellCoefficient Q U hU k)
      (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k P)
      (oldSignedPointwiseShear (q3Convolution b L h3Zero (whiteBasis n))
        ((R : Vec 2 → BlockVec 2)-F))=
      -volumeAverage (openCubeSet U) (fun x => vecDot
        (q3Convolution b L h3Zero (whiteBasis n) x •
          matVecMul responsePlanarJ (phi.toH1Function.grad x)) (g.grad x)) := by
  intro R phi g
  have hR : MemBlockL2 (openCubeSet U) R := R.property
  have hdiff := hR.sub (hF.mono_measure (Measure.restrict_mono_set volume hU))
  rw [old_signed_cell_canonical_shear_pairing Q U hU nu sigma hnu hsigma k P b L n hdiff]
  simp only [phi,old_signed_cell_first_corrector_grad]
  rfl

end
end ASDExplicitGamma.Native
