module

public import ASDExplicitGamma.Native.OldSignedSourceMultiplier
public import ASDExplicitGamma.Native.OldSignedErrorProfiles
public import ASDExplicitGamma.Native.OldSignedPartitionSeries

/-! The complete actual OLD source bound in terms of the same parent
first-gradient error. No affine load is added to the centered source. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Gaussian Main Triadic Variational Inverse
noncomputable section

/-- The literal localized OLD source equals the uncentered q3 row of the
actual zero-trace canonical first correction, in the spatial positive energy. -/
theorem old_signed_old_source_row_energy_eq (n : ℤ) (mesh : ℕ) (a : CoeffField 2)
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam (openCubeSet (originCube 2 n)) a)
    (P : BlockVec 2) (b : ℝ) (L : {l : ℝ // 0<l}) (l : whiteBasisIndex) :
    descendantsAverage (originCube 2 n) mesh (fun U => vectorPositiveHaarNorm U
      (fun x => (oldSignedOldErrorSource (originCube 2 n) mesh a hEll b L l P x).2)^2)=
    pureFluxMainQ3RowEnergy n b 1 L mesh 0
      (oldSignedCanonicalFirstCorrector (originCube 2 n) a hEll P) l := by
  simp only [pureFluxMainQ3RowEnergy,pureFluxMainQ3BasisFrameMultiplier,inv_one,one_smul,
    old_signed_zero_affine_potential]
  apply congrArg (descendantsAverage (originCube 2 n) mesh)
  funext U
  rw [vectorPositiveHaarNorm,Real.sq_sqrt (vectorPositiveHaarEnergy_nonneg U _)]
  simp only [oldSignedOldErrorSource,oldSignedLocalizedPotentialShear,
    vectorPositiveHaarEnergy,Pi.neg_apply,primalEnergy_neg]

/-- One complete actual OLD source load is controlled by k_a squared
times the tiled weak energy of its actual parent first-gradient error. -/
theorem old_signed_old_source_load_energy_bound (n : ℤ) (mesh : ℕ) (a : CoeffField 2)
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam (openCubeSet (originCube 2 n)) a)
    (P : BlockVec 2) (b : ℝ) (L : {l : ℝ // 0<l}) :
    (∑' l,descendantsAverage (originCube 2 n) mesh (fun U => vectorPositiveHaarNorm U
      (fun x => (oldSignedOldErrorSource (originCube 2 n) mesh a hEll b L l P x).2)^2))≤
    oldSignedSourceMultiplier (originCube 2 n) mesh b L^2*
      lemmaVTiledWeakEnergy (originCube 2 n) mesh
        (fun x => (oldSignedCanonicalAffineField (originCube 2 n) a hEll P x).1-P.1) := by
  simp_rw [old_signed_old_source_row_energy_eq]
  have hh := (old_signed_q3_row_energy_bound n b L mesh 0
    (oldSignedCanonicalFirstCorrector (originCube 2 n) a hEll P)).2
  simpa only [old_signed_zero_affine_potential,old_signed_canonical_first_corrector_grad] using hh

end
end ASDExplicitGamma.Native
