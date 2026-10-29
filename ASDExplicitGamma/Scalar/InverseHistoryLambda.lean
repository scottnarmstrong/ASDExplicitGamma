module

public import ASDExplicitGamma.Scalar.InverseHistory
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Homogenization.Book.Ch04.CoeffFamily

/-! Identification of the complete quarter-discount history with the paper's literal lambda quantity. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization Variational

/-- The same inverse operator maximum in the depth and absolute-scale conventions. -/
theorem inverse_history_depth_max_eq (Q : TriadicCube 2) (a : RegCoeffField 2)
    (ha : Book.Ch04.AELocallyUniformlyEllipticField a) (d : ℕ) :
    Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale-(d:ℤ))
      (Book.Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha)=
      lemmaVInverseDepthMax Q a.toFun d := by
  have hk : Q.scale-(d:ℤ)≤Q.scale := sub_le_self _ (by omega)
  have hd : descendantsAtScale Q (Q.scale-(d:ℤ))=descendantsAtDepth Q d := by
    rw [descendantsAtScale_eq_descendantsAtDepth Q hk]
    simp
  unfold Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale lemmaVInverseDepthMax
  rw [hd]
  congr 1

/-- The real source inverse-lambda is precisely the reused complete real history. -/
theorem inverse_lambda_eq_history (Q : TriadicCube 2) (a : RegCoeffField 2)
    (ha : Book.Ch04.AELocallyUniformlyEllipticField a) :
    (Book.Ch02.lambdaSqFinite Q (1/8) 2
      (Book.Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha))⁻¹=
      lemmaVInverseHistory Q a.toFun ((3:ℝ)^(1/4:ℝ)) := by
  unfold Book.Ch02.lambdaSqFinite
  simp only [Real.rpow_eq_pow]
  norm_num only [show -(2/(2:ℝ))=(-1:ℝ) by norm_num,show (2:ℝ)/2=1 by norm_num,
    Real.rpow_one,Real.rpow_neg_one,inv_inv]
  simp_rw [inverse_history_depth_max_eq]
  unfold Book.Ch02.geometricWeight Book.Ch02.geometricDiscount lemmaVInverseHistory
  simp only [Real.rpow_eq_pow]
  have he (d : ℕ) : (3:ℝ)^(-(1/8:ℝ)*2*(d:ℝ))=(((3:ℝ)^(1/4:ℝ))⁻¹)^d := by
    rw [← Real.rpow_neg (by norm_num : (0:ℝ)≤3),← Real.rpow_natCast,
      ← Real.rpow_mul (by norm_num : (0:ℝ)≤3)]
    congr 1
    ring
  simp_rw [he]
  have hc : (3:ℝ)^(-(1/8:ℝ)*2)=((3:ℝ)^(1/4:ℝ))⁻¹ := by
    convert inverse_history_discount_eq using 1
    norm_num [inverseHistoryDiscount]
  rw [hc]
  simp_rw [mul_assoc]
  rw [tsum_mul_left]

end ASDExplicitGamma.Scalar
