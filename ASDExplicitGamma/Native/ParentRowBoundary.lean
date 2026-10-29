module

public import ASDExplicitGamma.Native.ParentBoundaryBandTiledDepthBank
public import ASDExplicitGamma.Native.ParentBoundaryBandHistoryStationarity
public import ASDExplicitGamma.Native.ParentBoundaryBandTraceMoments
public import ASDExplicitGamma.Native.OldSignedSourceDirectionalPayment
public import ASDExplicitGamma.Native.ParentBoundaryBandWeak
public import ASDExplicitGamma.Native.OldSignedNonnegativeSeriesIntegral
public import ASDExplicitGamma.Native.ParentBoundaryBandSpatialProxy
public import ASDExplicitGamma.Native.OldSignedSqrtProductExpectation
public import ASDExplicitGamma.Native.ParentBoundaryChargeProxy

/-! Separate paired-boundary norms for the actual OLD parent field.
The reciprocal charge uses sqrt(2 xi), on the unchanged parent minimizers. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Gaussian Main Triadic Variational Inverse Algsuperdiff.Section3
noncomputable section

/-- The complete covariance RMS on the actual comparison tiling, for each sign. -/
def parentRowBeta (n : ℤ) (depth : ℕ) (b : ℝ) (L : {l : ℝ // 0<l})
    (plus : Bool) : ℝ :=
  Real.sqrt (descendantsAverage (originCube 2 n) depth (fun U =>
    parentBoundaryCenteredBeta (originCube 2 n) U b L plus^2))

/-- The two signs are charged separately using the already-proved primal and
joint weak moments; no source-patch or additional reciprocal cap is assumed. -/
theorem parent_row_paired_charge (m : ℤ) (depth : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet (originCube 2 m)))
    (b : ℝ) (L : {l : ℝ // 0<l})
    :
    let Q := originCube 2 m
    let a := responseFramePlanarCoefficientField nu sigma k
    let xi := rawWeakTraceProxy (fun j => lemmaVInverseDepthMax Q a (depth+j))
      (fun j => descendantsAverage Q (depth+j) (fun U => traceDefect (openCubeSet U) a 1))
    let betaPlus := parentRowBeta m depth b L true
    let betaMinus := parentRowBeta m depth b L false
    2*descendantsAverage Q depth (fun U => parentBoundaryCenteredBeta Q U b L true*
      oldSignedPrimalErrorSize Q U nu sigma hnu hsigma k)+
    2*descendantsAverage Q depth (fun U => parentBoundaryCenteredBeta Q U b L false*
      oldSignedReciprocalErrorSize Q U nu sigma hnu hsigma k) ≤
    2*betaPlus*Real.sqrt xi+2*betaMinus*Real.sqrt (2*xi) := by
  intro Q a xi betaPlus betaMinus
  let V := fun U => oldSignedPrimalErrorSize Q U nu sigma hnu hsigma k
  let G := fun U => oldSignedReciprocalErrorSize Q U nu sigma hnu hsigma k
  have hV := parent_boundary_primal_broken_weak_bound Q depth nu sigma hnu hsigma k
  have hVG := parent_boundary_joint_broken_weak_bound Q depth nu sigma hnu hsigma k
  have hG : descendantsAverage Q depth (fun U => G U^2)≤2*xi :=
    (descendantsAverage_le (fun U _ => le_add_of_nonneg_left (sq_nonneg (V U)))).trans hVG
  have htop := parent_boundary_descendant_cauchy Q depth
    (fun U => parentBoundaryCenteredBeta Q U b L true) V
    (fun _ _ => Real.sqrt_nonneg _) (fun _ _ => Real.sqrt_nonneg _)
  have hbottom := parent_boundary_descendant_cauchy Q depth
    (fun U => parentBoundaryCenteredBeta Q U b L false) G
    (fun _ _ => Real.sqrt_nonneg _) (fun _ _ => Real.sqrt_nonneg _)
  have htop' := htop.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hV) (Real.sqrt_nonneg _))
  have hbottom' := hbottom.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hG) (Real.sqrt_nonneg _))
  have hh := add_le_add (mul_le_mul_of_nonneg_left htop' (by norm_num : (0:ℝ)≤2))
    (mul_le_mul_of_nonneg_left hbottom' (by norm_num : (0:ℝ)≤2))
  simpa only [betaPlus,betaMinus,parentRowBeta,mul_assoc] using hh

/-- The actual two-sign charge envelope on the simultaneous band. -/
def parentRowChargeEnvelope (M : ABKModel 2) (n : ℤ) (height depth : ℕ)
    (t b : ℝ) (L : {l : ℝ // 0<l}) (omega : Cutoff.CutoffSample 2) : ℝ :=
  let xi := parentBoundaryBandWeakProxy M n height depth t omega
  2*parentRowBeta n depth b L true*Real.sqrt xi+
    2*parentRowBeta n depth b L false*Real.sqrt (2*xi)

/-- The literal physical centered charges obey their separate-sign envelope. -/
theorem parent_row_actual_paired_charge
    (M : ABKModel 2) (n : ℤ) (height depth : ℕ) (t b : ℝ)
    (L : {l : ℝ // 0<l})
    (omega : Cutoff.CutoffSample 2) :
    let Q := originCube 2 n
    let sigma : ℝ := Annealed.sigmaBar M n
    let k := pureFluxOpenResponseRestriction n (nativeSourceBandScalar n height t omega)
    2*descendantsAverage Q depth (fun U => parentBoundaryCenteredBeta Q U b L true*
      oldSignedPrimalErrorSize Q U M.nu sigma M.nu_pos (Annealed.sigmaBar_characterization M n).1 k)+
    2*descendantsAverage Q depth (fun U => parentBoundaryCenteredBeta Q U b L false*
      oldSignedReciprocalErrorSize Q U M.nu sigma M.nu_pos (Annealed.sigmaBar_characterization M n).1 k)≤
      parentRowChargeEnvelope M n height depth t b L omega := by
  intro Q sigma k
  have hh := parent_row_paired_charge n depth M.nu sigma M.nu_pos
    (Annealed.sigmaBar_characterization M n).1 k b L
  dsimp only at hh
  have hproxy := parent_boundary_band_proxy_eq M n height depth t omega
  dsimp only [parentBoundaryBandFrameField] at hproxy
  dsimp only [sigma,k] at hh
  rw [hproxy] at hh
  exact hh

end
end ASDExplicitGamma.Native
