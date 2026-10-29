module

public import ASDExplicitGamma.Native.OldSignedOldErrorSource
public import ASDExplicitGamma.Native.OldSignedLocalTrialVariation

/-! The actual fixed-frame fields of the OLD signed local trial. All
projections act on the same parent coefficient and actual finite partition. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Scalar ASDExplicitGamma.Main ASDExplicitGamma.Gaussian ASDExplicitGamma.Response
noncomputable section

/-- The canonical parent affine minimizer in the actual true scalar frame. -/
def oldSignedFrameCanonicalField (Q : TriadicCube 2) (nu sigma : ℝ)
    (hnu : 0<nu) (hsigma : 0<sigma) (k : ResponseCoefficient (openCubeSet Q)) (P : BlockVec 2) :
    BlockL2 (openCubeSet Q) :=
  oldSignedCanonicalAffineField Q (responseFramePlanarCoefficientField nu sigma k)
    (responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet Q) nu sigma hnu hsigma k) P

/-- The actual localized old-error source in this same frame. -/
def oldSignedFrameOldErrorSource (Q : TriadicCube 2) (mesh : ℕ) (nu sigma : ℝ)
    (hnu : 0<nu) (hsigma : 0<sigma) (k : ResponseCoefficient (openCubeSet Q))
    (b : ℝ) (L : {l : ℝ // 0 < l}) (n : whiteBasisIndex) (P : BlockVec 2) : Vec 2 → BlockVec 2 :=
  oldSignedOldErrorSource Q mesh (responseFramePlanarCoefficientField nu sigma k)
    (responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet Q) nu sigma hnu hsigma k) b L n P

/-- Actual source L2 membership, supplied by the physical construction. -/
theorem old_signed_frame_old_error_source_memL2 (Q : TriadicCube 2) (mesh : ℕ) (nu sigma : ℝ)
    (hnu : 0<nu) (hsigma : 0<sigma) (k : ResponseCoefficient (openCubeSet Q))
    (b : ℝ) (L : {l : ℝ // 0 < l}) (n : whiteBasisIndex) (P : BlockVec 2) :
    MemBlockL2 (openCubeSet Q) (oldSignedFrameOldErrorSource Q mesh nu sigma hnu hsigma k b L n P) :=
  old_signed_old_error_source_memL2 Q mesh _ _ b L n P

/-- The projected top flat input A on the actual finite cell partition. -/
def oldSignedPatchedPlus (Q : TriadicCube 2) (depth : ℕ) (nu sigma : ℝ)
    (hnu : 0<nu) (hsigma : 0<sigma) (k : ResponseCoefficient (openCubeSet Q))
    (b : ℝ) (L : {l : ℝ // 0 < l}) (n : whiteBasisIndex) (i : Fin 2) : Vec 2 → BlockVec 2 :=
  oldSignedLocalResidual Q depth nu sigma hnu hsigma k (oldSignedFlatPlusBlock Q b L n i)
    (old_signed_flat_plus_block_memL2 Q b L n i)

/-- The projected bottom flat input Z on the identical partition. -/
def oldSignedPatchedMinus (Q : TriadicCube 2) (depth : ℕ) (nu sigma : ℝ)
    (hnu : 0<nu) (hsigma : 0<sigma) (k : ResponseCoefficient (openCubeSet Q))
    (b : ℝ) (L : {l : ℝ // 0 < l}) (n : whiteBasisIndex) (i : Fin 2) : Vec 2 → BlockVec 2 :=
  oldSignedLocalResidual Q depth nu sigma hnu hsigma k (oldSignedFlatMinusBlock Q b L n i)
    (old_signed_flat_minus_block_memL2 Q b L n i)

/-- The projected actual localized old-error source R. -/
def oldSignedPatchedOldError (Q : TriadicCube 2) (depth mesh : ℕ) (nu sigma : ℝ)
    (hnu : 0<nu) (hsigma : 0<sigma) (k : ResponseCoefficient (openCubeSet Q))
    (b : ℝ) (L : {l : ℝ // 0 < l}) (n : whiteBasisIndex) (P : BlockVec 2) : Vec 2 → BlockVec 2 :=
  oldSignedLocalResidual Q depth nu sigma hnu hsigma k
    (oldSignedFrameOldErrorSource Q mesh nu sigma hnu hsigma k b L n P)
    (old_signed_frame_old_error_source_memL2 Q mesh nu sigma hnu hsigma k b L n P)

end
end ASDExplicitGamma.Native
