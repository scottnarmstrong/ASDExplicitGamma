module

public import ASDExplicitGamma.Scalar.DefectCapR
public import ASDExplicitGamma.Scalar.SmoothFeedbackActualHyp
public import ASDExplicitGamma.Scalar.SmoothFeedbackActualAgg
public import ASDExplicitGamma.Main.SourcePrefixGates
public import ASDExplicitGamma.Cold.NativeThetaScaling

/-! Model link: the physical defect value `defectFdefR` at the model constants is at
most the certified R-defect tree `quarticDefectRExpr`.  The three arguments are
capped separately and `defectLambda` is monotone in them. -/

@[expose] public section
namespace ASDExplicitGamma.Scalar

open ASDExplicitGamma.Numerics.Scalar
open ASDExplicitGamma.Numerics.Mirror
open ASDExplicitGamma.Main ASDExplicitGamma.Native
open ASDExplicitGamma.Numerics.MainReturn
open Algsuperdiff.Section3

noncomputable section

theorem defectA_nonneg : 0 ≤ defectA := by unfold defectA; positivity

theorem deltaN_nonneg : 0 ≤ lambda8DeltaN := by
  unfold lambda8DeltaN lambda8Rho; positivity

theorem lambda_mono {a a' x x' m m' : ℝ} (ha : 0 ≤ a) (hx : 0 ≤ x) (hm : 0 ≤ m)
    (haa : a ≤ a') (hxx : x ≤ x') (hmm : m ≤ m') :
    defectLambda a x m (14103 / 10000) (5 / 10 ^ 24) ≤
      defectLambda a' x' m' (14103 / 10000) (5 / 10 ^ 24) := by
  have hA := defectA_nonneg
  have hdn := deltaN_nonneg
  have hx' : 0 ≤ x' := hx.trans hxx
  have hm' : 0 ≤ m' := hm.trans hmm
  have ha' : 0 ≤ a' := ha.trans haa
  unfold defectLambda consumerL gapEps graW eraW
  apply pow_le_pow_left₀ (by positivity)
  gcongr

theorem fdefR_mono {a a' x x' m m' : ℝ} (ha : 0 ≤ a) (hx : 0 ≤ x) (hm : 0 ≤ m)
    (haa : a ≤ a') (hxx : x ≤ x') (hmm : m ≤ m') (R : ℝ) :
    defectFdefR a x m (14103 / 10000) (5 / 10 ^ 24) (14103 / 10000) (5 / 10 ^ 24) R ≤
      defectFdefR a' x' m' (14103 / 10000) (5 / 10 ^ 24) (14103 / 10000) (5 / 10 ^ 24) R := by
  have h := lambda_mono ha hx hm haa hxx hmm
  unfold defectFdefR
  have hA := defectA_nonneg
  gcongr

theorem meanPrefix_eq : mainSourceMeanPrefix = evalReal scalarRealEnv lowerA5Expr := by
  simp only [mainSourceMeanPrefix, observer1Panel0Data, lowerA5Expr, evalReal, sc]

theorem inversePrefix_eq : (observer1Panel0Data.initialInverseMean : ℝ) =
    evalReal scalarRealEnv lowerXiExpr := by
  simp only [observer1Panel0Data, lowerXiExpr, evalReal, sc]

theorem xi_cap (M : ABKModel 2) (h : ℝ) (hγ : M.gamma ≤ gammaZero) (i : ℤ) :
    xi'' M h i ≤ evalReal scalarRealEnv lowerXiExpr := by
  rw [← inversePrefix_eq]
  unfold xi'' mainEnvelopeXi mainSourceInversePrefix
  have hθ := Cold.cold_theta_le_one M hγ
  have hθ0 : 0 ≤ theta M := div_nonneg M.shellPrefix.gamma_pos.le (by unfold gammaZero; norm_num)
  have : (1 / 10 ^ 12 : ℝ) * theta M ≤ 1 / 10 ^ 12 := by nlinarith
  linarith

theorem mainH0_le : mainH0 ≤ 5423 / 2500 := by
  unfold mainH0
  have h4 : ((3 : ℝ) ^ (3 / 4 : ℝ)) ^ 4 = 27 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    norm_num
  have hc : (3 : ℝ) ^ (3 / 4 : ℝ) ≤ 5423 / 2379 := by
    refine le_of_pow_le_pow_left₀ (n := 4) (by norm_num) (by norm_num) ?_
    rw [h4]; norm_num
  linarith

theorem mstar_cap (M : ABKModel 2) :
    mStar' M ≤ evalReal scalarRealEnv lowerMExpr := by
  have hH : mainEnvelopeH (theta M) M.gamma 0 = mainH0 := by
    unfold mainEnvelopeH
    have : 0 ≤ mainH0 := by unfold mainH0; positivity
    simp [Real.sq_sqrt this]
  unfold mStar'
  rw [hH]
  have h0 := mainH0_le
  have h1 : (0:ℝ) ≤ mainH0 := by unfold mainH0; positivity
  simp only [mainM0, lowerMExpr, evalReal, sc]
  push_cast
  have : Real.sqrt (2 * mainH0) ≤ Real.sqrt (5423 / 2500 * 2) := Real.sqrt_le_sqrt (by linarith)
  nlinarith [this]

theorem drop_defect_cap_R (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (i : ℤ) (hpast : ∀ n ≤ i, nativeInductionState M h n) :
    defectFdefR mainSourceMeanPrefix (xi'' M h i) (mStar' M) (14103 / 10000) (5 / 10 ^ 24)
        (14103 / 10000) (5 / 10 ^ 24) roughR ≤
      evalReal scalarRealEnv quarticDefectRExpr := by
  have _ := hM
  have _ := hpast
  rw [← defect_fdefR_eq_certificate]
  exact fdefR_mono (by rw [meanPrefix_eq]; norm_num [evalReal, lowerA5Expr, sc])
    (xi_nonneg M h hγ i) (mStar_nonneg M) (le_of_eq meanPrefix_eq)
    (xi_cap M h hγ i) (mstar_cap M) roughR

end
end ASDExplicitGamma.Scalar
