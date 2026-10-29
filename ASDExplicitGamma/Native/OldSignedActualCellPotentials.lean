module

public import ASDExplicitGamma.Native.OldSignedCellPotentials
public import ASDExplicitGamma.Native.OldSignedTrialFields

/-! The genuine zero-boundary first potentials of all three actual local
OLD trial pieces, selected from the proved weighted cell variations. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Scalar ASDExplicitGamma.Gaussian
noncomputable section

/-- First potential of the actual projected plus-flat source A. -/
def oldSignedCellPlusPotential (Q U : TriadicCube 2) (hU : openCubeSet U ⊆ openCubeSet Q)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma) (k : ResponseCoefficient (openCubeSet Q))
    (b : ℝ) (L : {l : ℝ // 0<l}) (n : whiteBasisIndex) (i : Fin 2) : H10Function (openCubeSet U) :=
  oldSignedCellFirstCorrector Q U hU nu sigma hnu hsigma k (oldSignedFlatPlusBlock Q b L n i)
    (old_signed_flat_plus_block_memL2 Q b L n i)

/-- Its gradient is the complete first block of A, since Uplus is pure second. -/
theorem old_signed_cell_plus_potential_grad (Q U : TriadicCube 2) (hU : openCubeSet U ⊆ openCubeSet Q)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma) (k : ResponseCoefficient (openCubeSet Q))
    (b : ℝ) (L : {l : ℝ // 0<l}) (n : whiteBasisIndex) (i : Fin 2) :
    (oldSignedCellPlusPotential Q U hU nu sigma hnu hsigma k b L n i).toH1Function.grad=
      fun x => (oldSignedCellResidual Q U hU nu sigma hnu hsigma k (oldSignedFlatPlusBlock Q b L n i)
        (old_signed_flat_plus_block_memL2 Q b L n i) x).1 := by
  rw [oldSignedCellPlusPotential,old_signed_cell_first_corrector_grad]
  funext x
  exact sub_zero _

/-- First potential of the actual projected localized OLD-error source R. -/
def oldSignedCellErrorPotential (Q U : TriadicCube 2) (hU : openCubeSet U ⊆ openCubeSet Q)
    (mesh : ℕ) (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma) (k : ResponseCoefficient (openCubeSet Q))
    (b : ℝ) (L : {l : ℝ // 0<l}) (n : whiteBasisIndex) (P : BlockVec 2) : H10Function (openCubeSet U) :=
  oldSignedCellFirstCorrector Q U hU nu sigma hnu hsigma k
    (oldSignedFrameOldErrorSource Q mesh nu sigma hnu hsigma k b L n P)
    (old_signed_frame_old_error_source_memL2 Q mesh nu sigma hnu hsigma k b L n P)

/-- The entire first block of R has zero-boundary potential; its input is pure second. -/
theorem old_signed_cell_error_potential_grad (Q U : TriadicCube 2) (hU : openCubeSet U ⊆ openCubeSet Q)
    (mesh : ℕ) (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma) (k : ResponseCoefficient (openCubeSet Q))
    (b : ℝ) (L : {l : ℝ // 0<l}) (n : whiteBasisIndex) (P : BlockVec 2) :
    (oldSignedCellErrorPotential Q U hU mesh nu sigma hnu hsigma k b L n P).toH1Function.grad=
      fun x => (oldSignedCellResidual Q U hU nu sigma hnu hsigma k
        (oldSignedFrameOldErrorSource Q mesh nu sigma hnu hsigma k b L n P)
        (old_signed_frame_old_error_source_memL2 Q mesh nu sigma hnu hsigma k b L n P) x).1 := by
  rw [oldSignedCellErrorPotential,old_signed_cell_first_corrector_grad]
  funext x
  exact sub_zero _

/-- First potential of Z-Uminus, keeping the actual flat source separate. -/
def oldSignedCellMinusPotential (Q U : TriadicCube 2) (hU : openCubeSet U ⊆ openCubeSet Q)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma) (k : ResponseCoefficient (openCubeSet Q))
    (b : ℝ) (L : {l : ℝ // 0<l}) (n : whiteBasisIndex) (i : Fin 2) : H10Function (openCubeSet U) :=
  oldSignedCellFirstCorrector Q U hU nu sigma hnu hsigma k (oldSignedFlatMinusBlock Q b L n i)
    (old_signed_flat_minus_block_memL2 Q b L n i)

/-- The minus correction gradient is Z.first-Uminus.first, retaining the
flat part whose covariance contributes the signed reciprocal block. -/
theorem old_signed_cell_minus_potential_grad (Q U : TriadicCube 2) (hU : openCubeSet U ⊆ openCubeSet Q)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma) (k : ResponseCoefficient (openCubeSet Q))
    (b : ℝ) (L : {l : ℝ // 0<l}) (n : whiteBasisIndex) (i : Fin 2) :
    (oldSignedCellMinusPotential Q U hU nu sigma hnu hsigma k b L n i).toH1Function.grad=
      fun x => (oldSignedCellResidual Q U hU nu sigma hnu hsigma k (oldSignedFlatMinusBlock Q b L n i)
        (old_signed_flat_minus_block_memL2 Q b L n i) x).1-(oldSignedFlatMinusBlock Q b L n i x).1 :=
  old_signed_cell_first_corrector_grad Q U hU nu sigma hnu hsigma k _ _

end
end ASDExplicitGamma.Native
