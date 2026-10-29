module

public import ASDExplicitGamma.Native.OldSignedActualTrialVariation

/-! Actual separate top and bottom candidates for the OLD physical trial. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Scalar ASDExplicitGamma.Gaussian
noncomputable section

/-- Top candidate A+R on the fixed finite partition. -/
def oldSignedTopTrial (Q : TriadicCube 2) (depth mesh : ℕ) (nu sigma : ℝ)
    (hnu : 0<nu) (hsigma : 0<sigma) (k : ResponseCoefficient (openCubeSet Q))
    (b : ℝ) (L : {l : ℝ // 0<l}) (n : whiteBasisIndex) (i : Fin 2) : Vec 2 → BlockVec 2 :=
  oldSignedPatchedPlus Q depth nu sigma hnu hsigma k b L n i+
    oldSignedPatchedOldError Q depth mesh nu sigma hnu hsigma k b L n (basisVec i,0)

/-- Bottom candidate R-Z, retaining the negative flat tangent. -/
def oldSignedBottomTrial (Q : TriadicCube 2) (depth mesh : ℕ) (nu sigma : ℝ)
    (hnu : 0<nu) (hsigma : 0<sigma) (k : ResponseCoefficient (openCubeSet Q))
    (b : ℝ) (L : {l : ℝ // 0<l}) (n : whiteBasisIndex) (i : Fin 2) : Vec 2 → BlockVec 2 :=
  oldSignedPatchedOldError Q depth mesh nu sigma hnu hsigma k b L n (0,basisVec i)-
    oldSignedPatchedMinus Q depth nu sigma hnu hsigma k b L n i

/-- The actual top candidate has genuine parent L2 membership. -/
theorem old_signed_top_trial_memL2 (Q : TriadicCube 2) (depth mesh : ℕ) (nu sigma : ℝ)
    (hnu : 0<nu) (hsigma : 0<sigma) (k : ResponseCoefficient (openCubeSet Q))
    (b : ℝ) (L : {l : ℝ // 0<l}) (n : whiteBasisIndex) (i : Fin 2) :
    MemBlockL2 (openCubeSet Q) (oldSignedTopTrial Q depth mesh nu sigma hnu hsigma k b L n i) :=
  (old_signed_local_residual_memLp Q depth nu sigma hnu hsigma k _
    (old_signed_flat_plus_block_memL2 Q b L n i)).add
    (old_signed_local_residual_memLp Q depth nu sigma hnu hsigma k _
      (old_signed_frame_old_error_source_memL2 Q mesh nu sigma hnu hsigma k b L n (basisVec i,0)))

/-- The actual bottom candidate has genuine parent L2 membership. -/
theorem old_signed_bottom_trial_memL2 (Q : TriadicCube 2) (depth mesh : ℕ) (nu sigma : ℝ)
    (hnu : 0<nu) (hsigma : 0<sigma) (k : ResponseCoefficient (openCubeSet Q))
    (b : ℝ) (L : {l : ℝ // 0<l}) (n : whiteBasisIndex) (i : Fin 2) :
    MemBlockL2 (openCubeSet Q) (oldSignedBottomTrial Q depth mesh nu sigma hnu hsigma k b L n i) :=
  (old_signed_local_residual_memLp Q depth nu sigma hnu hsigma k _
    (old_signed_frame_old_error_source_memL2 Q mesh nu sigma hnu hsigma k b L n (0,basisVec i))).sub
    (old_signed_local_residual_memLp Q depth nu sigma hnu hsigma k _
      (old_signed_flat_minus_block_memL2 Q b L n i))

end
end ASDExplicitGamma.Native
