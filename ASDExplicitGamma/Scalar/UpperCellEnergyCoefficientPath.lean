module

public import ASDExplicitGamma.Scalar.UpperCellEnergyPhysicalMeanSplit
public import ASDExplicitGamma.Inverse.ResponseCoefficients

/-! Exact equality of the normalized physical coefficient and the sensitivity
path built from the actual OLD cutoff and the same scalar fresh band. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Algsuperdiff.Section3
open Algsuperdiff.Frozen.Assumptions Response Inverse Gaussian Triadic
noncomputable section

/-- The finite fresh response coefficient is exactly the difference of the
two completed cutoffs, with any fixed normalization. -/
theorem upper_cell_normalized_cutoff_band
    (Q : TriadicCube 2) (n terminal : ℤ) (hn : n ≤ terminal) (c : ℝ)
    (ω : Cutoff.CutoffSample 2) :
    c • oldCutoffSkewCoefficient terminal Q ω =
      c • oldCutoffSkewCoefficient n Q ω + laterResponseCoefficient Q n terminal (fun _ => c) ω := by
  ext x
  change c*Cutoff.cutoff terminal ω x.val 1 0 =
    c*Cutoff.cutoff n ω x.val 1 0 + laterScalarBand n terminal (fun _ => c) ω x.val
  have hc := congrArg (fun a : RegCoeffField 2 => a x.val 1 0) (Cutoff.cutoff_add_finiteShellIncrement ω hn)
  change Cutoff.cutoff n ω x.val 1 0 + Cutoff.finiteShellIncrement ω.val n terminal x.val 1 0 =
    Cutoff.cutoff terminal ω x.val 1 0 at hc
  rw [←hc,Cutoff.finiteShellIncrement_apply_entry,mul_add,Finset.mul_sum]
  rfl

/-- Centering the ODE path is precisely removal of the physical fresh mean
skew at the fixed frame, on the whole closed observation cube. -/
theorem upper_cell_centered_response_path
    (Q : TriadicCube 2) (n terminal : ℤ) (hn : n ≤ terminal)
    (sigma : ℝ) (hsigma : 0 < sigma) (ω : Cutoff.CutoffSample 2) (g : ℝ) :
    sensitivityResponseCoefficientPath (sigma⁻¹ • oldCutoffSkewCoefficient n Q ω)
      (laterResponseCoefficient Q n terminal (fun _ => sigma⁻¹) ω +
        BoundedContinuousFunction.const (closure (openCubeSet Q)) (-g)) 1 =
      sigma⁻¹ • (oldCutoffSkewCoefficient terminal Q ω -
        BoundedContinuousFunction.const (closure (openCubeSet Q)) (sigma*g)) := by
  simp only [sensitivityResponseCoefficientPath,one_smul]
  rw [←add_assoc,←upper_cell_normalized_cutoff_band Q n terminal hn sigma⁻¹ ω]
  ext x
  change sigma⁻¹ * oldCutoffSkewCoefficient terminal Q ω x + -g =
    sigma⁻¹ * (oldCutoffSkewCoefficient terminal Q ω x - sigma*g)
  field_simp [hsigma.ne']
  ring

/-- The sensitivity Book matrix at normalized physical data is the actual
fixed-frame variational coarse matrix on the same open cube. -/
theorem upper_cell_normalized_book_matrix
    (Q : TriadicCube 2) (nu sigma : ℝ) (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) :
    Book.Ch02.coarseBlockMatrix (Book.Ch02.cubeDomain Q)
      (sensitivityBookCoeffOn Q (nu/sigma) (div_pos hnu hsigma) (sigma⁻¹ • k)) =
      coarseBlockMatrix (openCubeSet Q) (responseFramePlanarCoefficientField nu sigma k) := by
  have hEll : IsEllipticFieldOn
      (sensitivityBookCoeffOn Q (nu/sigma) (div_pos hnu hsigma) (sigma⁻¹ • k)).lam
      (sensitivityBookCoeffOn Q (nu/sigma) (div_pos hnu hsigma) (sigma⁻¹ • k)).Lam
      (openCubeSet Q)
      (sensitivityBookCoeffOn Q (nu/sigma) (div_pos hnu hsigma) (sigma⁻¹ • k)).toCoeffField := by
    simpa [sensitivityBookCoeffOn,div_one] using
      responseFramePlanarCoefficientField_isElliptic
        (measurableSet_openCubeSet Q) (nu/sigma) 1 (div_pos hnu hsigma) one_pos (sigma⁻¹ • k)
  rw [ASDExplicitGamma.Variational.energyMap_coarseBlockMatrix_eq _ _ hEll]
  apply coarseBlockMatrix_congr_of_ae_eq
  filter_upwards [ae_restrict_mem (measurableSet_openCubeSet Q)] with x hx
  change responsePlanarCoefficient ((nu/sigma)/1)
    (responseCoefficientExtension (sigma⁻¹ • k) x/1) =
      responsePlanarCoefficient (nu/sigma) (responseCoefficientExtension k x/sigma)
  rw [div_one,div_one,responseCoefficientExtension_smul_on (sigma⁻¹) k hx]
  congr 1
  simp only [div_eq_mul_inv,mul_comm]

end
end ASDExplicitGamma.Scalar
