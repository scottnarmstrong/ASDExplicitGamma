module

public import ASDExplicitGamma.Triadic.SensitivityDerivative
public import ASDExplicitGamma.Variational.LemmaVH1
public import Homogenization.Book.Ch02.MultiscaleEllipticity

/-! The inverse lambda history at the quarter scale used by sensitivity. -/

@[expose] public section

namespace ASDExplicitGamma.Triadic

open Homogenization ASDExplicitGamma.Variational

noncomputable section

private theorem sensitivity_inverse_history_depth_max_eq
    (Q : TriadicCube 2) (a : RegCoeffField 2)
    (ha : Book.Ch04.AELocallyUniformlyEllipticField a) (d : ℕ) :
    Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q
      (Q.scale - (d : ℤ))
      (Book.Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha) =
      lemmaVInverseDepthMax Q a.toFun d := by
  have hk : Q.scale - (d : ℤ) ≤ Q.scale := sub_le_self _ (by omega)
  have hd : descendantsAtScale Q (Q.scale - (d : ℤ)) =
      descendantsAtDepth Q d := by
    rw [descendantsAtScale_eq_descendantsAtDepth Q hk]
    simp
  unfold Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale lemmaVInverseDepthMax
  rw [hd]
  congr 1

/-- The inverse finite-exponent lambda at `s=1/4`, `q=2` is the same
inverse-operator history used by the H1 response estimate. -/
theorem sensitivity_inverse_lambda_quarter_eq_history
    (Q : TriadicCube 2) (a : RegCoeffField 2)
    (ha : Book.Ch04.AELocallyUniformlyEllipticField a) :
    (Book.Ch02.lambdaSqFinite Q (1/4) 2
      (Book.Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha))⁻¹ =
      lemmaVInverseHistory Q a.toFun (Real.sqrt 3) := by
  unfold Book.Ch02.lambdaSqFinite
  simp only [Real.rpow_eq_pow]
  norm_num only [show -(2/(2:ℝ))=(-1:ℝ) by norm_num,
    show (2:ℝ)/2=1 by norm_num, Real.rpow_one, Real.rpow_neg_one, inv_inv]
  simp_rw [sensitivity_inverse_history_depth_max_eq Q a ha]
  unfold Book.Ch02.geometricWeight Book.Ch02.geometricDiscount lemmaVInverseHistory
  simp only [Real.rpow_eq_pow]
  have hbase : Real.rpow 3 (-(1/4:ℝ)*2) = (Real.sqrt 3)⁻¹ := by
    rw [show -(1/4:ℝ)*2 = -(1/2:ℝ) by ring]
    calc
      Real.rpow 3 (-(1/2:ℝ)) = (Real.rpow 3 (1/2:ℝ))⁻¹ := by
        exact Real.rpow_neg (by norm_num : (0:ℝ)≤3) (1/2:ℝ)
      _ = (Real.sqrt 3)⁻¹ := by rw [Real.sqrt_eq_rpow]; rfl
  have he (d : ℕ) :
      (3:ℝ)^(-(1/4:ℝ)*2*(d:ℝ)) = ((Real.sqrt 3)⁻¹)^d := by
    change Real.rpow 3 (-(1/4:ℝ)*2*(d:ℝ)) = ((Real.sqrt 3)⁻¹)^d
    calc
      Real.rpow 3 (-(1/4:ℝ)*2*(d:ℝ)) =
          Real.rpow 3 ((-(1/4:ℝ)*2)*(d:ℝ)) := by rfl
      _ = (Real.rpow 3 (-(1/4:ℝ)*2)) ^ (d:ℝ) :=
        Real.rpow_mul (by norm_num : (0:ℝ)≤3) _ _
      _ = (Real.rpow 3 (-(1/4:ℝ)*2)) ^ d := by rw [Real.rpow_natCast]
      _ = ((Real.sqrt 3)⁻¹)^d := by rw [hbase]
  simp_rw [he]
  have hc : (3:ℝ)^(-(1/4:ℝ)*2) = (Real.sqrt 3)⁻¹ := by
    change Real.rpow 3 (-(1/4:ℝ)*2) = (Real.sqrt 3)⁻¹
    exact hbase
  rw [hc]
  simp_rw [mul_assoc]
  rw [tsum_mul_left]

/-- For every `0<u≤1/4`, the inverse-lambda history dominates the quarter-scale
history. -/
theorem sensitivity_inverse_lambda_ge_quarter
    (Q : TriadicCube 2) (a : RegCoeffField 2)
    (ha : Book.Ch04.AELocallyUniformlyEllipticField a)
    (u : ℝ) (hu : 0 < u) (hu4 : u ≤ 1/4) :
    (Book.Ch02.lambdaSqFinite Q u 2
      (Book.Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha))⁻¹ ≥
      lemmaVInverseHistory Q a.toFun (Real.sqrt 3) := by
  let family := Book.Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha
  have hposu : 0 < Book.Ch02.lambdaSqFinite Q u 2 family :=
    Book.Ch02.lambdaSq_finite_pos Q family hu (by norm_num)
  have hpos4 : 0 < Book.Ch02.lambdaSqFinite Q (1/4) 2 family :=
    Book.Ch02.lambdaSq_finite_pos Q family (by norm_num) (by norm_num)
  have hmono : Book.Ch02.lambdaSqFinite Q u 2 family ≤
      Book.Ch02.lambdaSqFinite Q (1/4) 2 family := by
    by_cases heq : u = 1/4
    · rw [heq]
    · have hlt : u < 1/4 := lt_of_le_of_ne hu4 heq
      exact Book.Ch02.lambdaSq_finite_mono Q family hu hlt (by norm_num)
  have hinv : (Book.Ch02.lambdaSqFinite Q (1/4) 2 family)⁻¹ ≤
      (Book.Ch02.lambdaSqFinite Q u 2 family)⁻¹ :=
    (inv_le_inv₀ hpos4 hposu).2 hmono
  rw [sensitivity_inverse_lambda_quarter_eq_history Q a ha] at hinv
  exact hinv

end

end ASDExplicitGamma.Triadic
