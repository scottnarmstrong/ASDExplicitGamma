module

public import ASDExplicitGamma.Variational.LemmaVH1
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! The complete extended inverse history with the source quarter-power discount. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization Variational
open scoped ENNReal

/-- The source discount alpha=3^(-1/4); it is not the half-power Lemma-V discount. -/
noncomputable def inverseHistoryDiscount : ℝ := (3:ℝ)^(-(1/4:ℝ))

/-- The inverse of the quarter-power base is exactly the source discount. -/
theorem inverse_history_discount_eq : inverseHistoryDiscount=((3:ℝ)^(1/4:ℝ))⁻¹ := by
  exact Real.rpow_neg (by norm_num : (0:ℝ)≤3) (1/4:ℝ)

/-- The geometric discount is strictly between zero and one. -/
theorem inverse_history_discount_range : 0 < inverseHistoryDiscount ∧ inverseHistoryDiscount < 1 := by
  constructor
  · exact Real.rpow_pos_of_pos (by norm_num) _
  · exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)

/-- Qualitative ellipticity supplies the complete source sum, without a numerical history cap. -/
theorem inverse_history_weighted_summable (Q : TriadicCube 2) (a : CoeffField 2)
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) (sigma : ℝ) :
    Summable (fun d : ℕ => inverseHistoryDiscount^d*sigma*lemmaVInverseDepthMax Q a d) := by
  have hq : 1<(3:ℝ)^(1/4:ℝ) := Real.one_lt_rpow (by norm_num) (by norm_num)
  have h := (lemmaVInverseHistory_summable Q hEll hq).mul_left sigma
  rw [inverse_history_discount_eq]
  convert h using 1
  funext d
  ring

end ASDExplicitGamma.Scalar
