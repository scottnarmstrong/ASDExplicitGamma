module

public import ASDExplicitGamma.Native.OldSignedPhysicalTrial
public import ASDExplicitGamma.Native.OldSignedTrialCandidates

/-! AN (4.2) instantiated with both actual finite-partition candidates.
Only physical source data and positivity are inputs; admissibility is proved. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Scalar ASDExplicitGamma.Gaussian
noncomputable section

/-- Half of the directional Hessian in the physical direction sigma psi. -/
def oldSignedPhysicalHessian (Q : TriadicCube 2) (nu sigma : ℝ)
    (hnu : 0<nu) (hsigma : 0<sigma) (k : ResponseCoefficient (openCubeSet Q))
    (P : BlockVec 2) (b : ℝ) (L : {l : ℝ // 0<l}) (n : whiteBasisIndex) : ℝ :=
  let H := oldSignedPhysicalCoefficient Q sigma b L n
  (1/2:ℝ)*fderiv ℝ (fun z => fderiv ℝ
    (responseFrameEnergyObservable (measurableSet_openCubeSet Q)
      (by rw [volume_openCubeSet_toReal]; exact cubeVolume_pos Q)
      nu sigma hnu hsigma P) z H) k H

/-- The signed physical trial value, with feedback kept before estimation. -/
def oldSignedPhysicalTrialValue (Q : TriadicCube 2) (nu sigma : ℝ)
    (hnu : 0<nu) (hsigma : 0<sigma) (k : ResponseCoefficient (openCubeSet Q))
    (P : BlockVec 2) (b : ℝ) (L : {l : ℝ // 0<l}) (n : whiteBasisIndex)
    {F : Vec 2 → BlockVec 2} (hF : MemBlockL2 (openCubeSet Q) F) : ℝ :=
  let hU := measurableSet_openCubeSet Q
  let hv : 0<(volume (openCubeSet Q)).toReal := by
    rw [volume_openCubeSet_toReal]; exact cubeVolume_pos Q
  let D := responseFrameEnergyData hU hv nu sigma hnu hsigma k
  let R := responseEnergyUp D (toHilbertBlockL2OfBlockField hF)
  ‖R‖^2+2*inner ℝ (responseFrameEnergyBaseMinimizer hU hv nu sigma hnu hsigma k P)
    (responseFrameEnergyShearFamily hU hv nu sigma hnu hsigma k
      (oldSignedPhysicalCoefficient Q sigma b L n) R)

/-- Actual top-load physical Hessian trial A+R, without assumed estimates. -/
theorem old_signed_actual_top_hessian_trial (Q : TriadicCube 2) (depth mesh : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0<l})
    (n : whiteBasisIndex) (i : Fin 2) :
    oldSignedPhysicalHessian Q nu sigma hnu hsigma k (basisVec i,0) b L n ≤
      oldSignedPhysicalTrialValue Q nu sigma hnu hsigma k (basisVec i,0) b L n
        (old_signed_top_trial_memL2 Q depth mesh nu sigma hnu hsigma k b L n i) :=
  old_signed_physical_trial_bound Q nu sigma hnu hsigma k b L n (basisVec i,0)
    (old_signed_top_trial_memL2 Q depth mesh nu sigma hnu hsigma k b L n i)
    (old_signed_actual_top_trial_variation Q depth mesh nu sigma hnu hsigma k b L n i)

/-- Actual bottom-load physical Hessian trial R-Z. The negative tangent
and signed reciprocal-block contribution remain available to the assembly. -/
theorem old_signed_actual_bottom_hessian_trial (Q : TriadicCube 2) (depth mesh : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0<l})
    (n : whiteBasisIndex) (i : Fin 2) :
    oldSignedPhysicalHessian Q nu sigma hnu hsigma k (0,basisVec i) b L n ≤
      oldSignedPhysicalTrialValue Q nu sigma hnu hsigma k (0,basisVec i) b L n
        (old_signed_bottom_trial_memL2 Q depth mesh nu sigma hnu hsigma k b L n i) :=
  old_signed_physical_trial_bound Q nu sigma hnu hsigma k b L n (0,basisVec i)
    (old_signed_bottom_trial_memL2 Q depth mesh nu sigma hnu hsigma k b L n i)
    (old_signed_actual_bottom_trial_variation Q depth mesh nu sigma hnu hsigma k b L n i)

end
end ASDExplicitGamma.Native
