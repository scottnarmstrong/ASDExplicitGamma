module

public import ASDExplicitGamma.Native.OldSignedFlatCellBounds
public import ASDExplicitGamma.Native.OldSignedTrialFields

/-! Uniform notation for the two actual patched flat families. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Gaussian
noncomputable section

/-- Both physical flat inputs are square-integrable on the parent. -/
theorem old_signed_flat_input_memL2 (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0<l}) (plus : Bool) (n : whiteBasisIndex) (i : Fin 2) :
    MemBlockL2 (openCubeSet Q) (oldSignedFlatInput Q b L plus n i) := by
  cases plus
  · exact old_signed_flat_minus_block_memL2 Q b L n i
  · exact old_signed_flat_plus_block_memL2 Q b L n i

/-- The actual patched flat residual for either physical input family. -/
def oldSignedPatchedFlat (Q : TriadicCube 2) (depth : ℕ) (nu sigma : ℝ)
    (hnu : 0<nu) (hsigma : 0<sigma) (k : ResponseCoefficient (openCubeSet Q))
    (b : ℝ) (L : {l : ℝ // 0<l}) (plus : Bool) (n : whiteBasisIndex) (i : Fin 2) :
    Vec 2 → BlockVec 2 :=
  oldSignedLocalResidual Q depth nu sigma hnu hsigma k (oldSignedFlatInput Q b L plus n i)
    (old_signed_flat_input_memL2 Q b L plus n i)

/-- True selects the actual plus trial field. -/
theorem old_signed_patched_flat_true (Q : TriadicCube 2) (depth : ℕ) (nu sigma : ℝ)
    (hnu : 0<nu) (hsigma : 0<sigma) (k : ResponseCoefficient (openCubeSet Q))
    (b : ℝ) (L : {l : ℝ // 0<l}) (n : whiteBasisIndex) (i : Fin 2) :
    oldSignedPatchedFlat Q depth nu sigma hnu hsigma k b L true n i=
      oldSignedPatchedPlus Q depth nu sigma hnu hsigma k b L n i := rfl

/-- False selects the actual minus trial field. -/
theorem old_signed_patched_flat_false (Q : TriadicCube 2) (depth : ℕ) (nu sigma : ℝ)
    (hnu : 0<nu) (hsigma : 0<sigma) (k : ResponseCoefficient (openCubeSet Q))
    (b : ℝ) (L : {l : ℝ // 0<l}) (n : whiteBasisIndex) (i : Fin 2) :
    oldSignedPatchedFlat Q depth nu sigma hnu hsigma k b L false n i=
      oldSignedPatchedMinus Q depth nu sigma hnu hsigma k b L n i := rfl

end
end ASDExplicitGamma.Native
