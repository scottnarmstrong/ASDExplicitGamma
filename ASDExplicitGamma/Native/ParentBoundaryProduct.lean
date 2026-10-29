module

public import ASDExplicitGamma.Native.ParentBoundaryPositive
public import ASDExplicitGamma.Native.OldSignedFiniteMinkowski
public import ASDExplicitGamma.Native.OldSignedCellAverage
public import ASDExplicitGamma.Main.RankOneMultiplier
public import ASDExplicitGamma.Main.Q3FiniteColumn

/-! Whole-parent source columns on the independent fine comparison mesh.
Covariance modes are collected in one Hilbert multiplier before any bound. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Triadic ASDExplicitGamma.Variational
open ASDExplicitGamma.Main ASDExplicitGamma.Gaussian
open scoped BigOperators
noncomputable section

/-- The product bound on a cell applies to the restriction of the actual
parent potential. No zero trace on this fine cell is required. -/
theorem parent_boundary_cell_product
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (U : TriadicCube 2) (u : H1Function (openCubeSet U))
    (b : Vec 2 → E) (hb : ContDiff ℝ 1 b)
    (M D : ℝ) (hM : 0 ≤ M) (hD : 0 ≤ D)
    (hvalue : ∀ x, ‖b x‖ ≤ M)
    (hgrad : ∀ x, (∑ i : Fin 2, ‖(fderiv ℝ b x) (basisVec i)‖^2) ≤ D^2) :
    hilbertPositiveHaarNorm U (Real.sqrt 3) (fun x => u.toFun x • b x) ≤
      M*positiveHaarNorm U u.toFun +
        cubeScaleFactor U*(715/1000:ℝ)*D*Real.sqrt (energy U u.toFun) := by
  have hq1 : 1 < Real.sqrt (3:ℝ) := by
    nlinarith only [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3), Real.sqrt_nonneg (3:ℝ)]
  have hq9 : Real.sqrt (3:ℝ) < 9 := by
    nlinarith only [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3), Real.sqrt_nonneg (3:ℝ)]
  have hP := positiveHaarIncrementSeries_summable U
    u.memL2_normalizedCubeMeasure u.grad_memL2_normalizedCubeMeasure u.hasWeakGradient
  have hPh : Summable (fun k => (Real.sqrt 3)^(k+1)*
      hilbertEnergy U (hilbertCubeIncrement U (k+1) u.toFun)) := by
    simpa only [hilbertCubeIncrement_real, hilbertEnergy_real] using hP
  have hh := hilbert_positive_product_of_bounds (mainRankOneMultiplier U b hb) hq1 hq9
    u.memL2_normalizedCubeMeasure hPh hM hD
    (Filter.Eventually.of_forall (fun x => by
      rw [mainRankOneMultiplier_norm]; exact hvalue x))
    (Filter.Eventually.of_forall (fun x => by
      simp only [mainRankOneMultiplier_gradient_norm]; exact hgrad x))
  have hquarter : Real.sqrt (haarPoincareM2 (Real.sqrt 3)) = planarC1 := by
    simpa only [show 2*(1/4:ℝ)=1/2 by norm_num, ← Real.sqrt_eq_rpow] using haarPoincareM_quarter
  have hbound : hilbertPositiveHaarNorm U (Real.sqrt 3) (fun x => u.toFun x • b x) ≤
      M*positiveHaarNorm U u.toFun + cubeScaleFactor U*planarC1*D*Real.sqrt (energy U u.toFun) := by
    simpa only [mainRankOneMultiplier, ContinuousLinearMap.toSpanSingleton_apply,
      hilbertPositiveHaarNorm, hilbertPrimalEnergy_real, positiveHaarNorm,
      hilbertL2Norm, hilbertEnergy_real, hquarter] using hh.2
  have hc : planarC1 ≤ (715/1000:ℝ) :=
    native_boundary_planarC1_le.trans (by norm_num)
  exact hbound.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc (Triadic.cubeScaleFactor_pos' U).le) hD)
      (Real.sqrt_nonneg _)))

/-- Source (3.1) for a genuine deterministic Hilbert-valued multiplier.
All fine cells restrict the same H10 parent potential. -/
theorem parent_boundary_h10_product_broken
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (Q : TriadicCube 2) (j : ℕ) (u : H10Function (openCubeSet Q))
    (b : Vec 2 → E) (hb : ContDiff ℝ 1 b)
    (M D : ℝ) (hM : 0 ≤ M) (hD : 0 ≤ D)
    (hvalue : ∀ x, ‖b x‖ ≤ M)
    (hgrad : ∀ x, (∑ i : Fin 2, ‖(fderiv ℝ b x) (basisVec i)‖^2) ≤ D^2) :
    Real.sqrt (descendantsAverage Q j (fun U =>
      hilbertPositiveHaarNorm U (Real.sqrt 3) (fun x => u.toH1Function.toFun x • b x)^2)) ≤
      (M*Real.sqrt ((52/100:ℝ)^2*cubeScaleFactor Q^2 +
          (662/1000:ℝ)^2*(cubeScaleFactor Q/(3:ℝ)^j)^2) +
        (372/1000:ℝ)*cubeScaleFactor Q*(cubeScaleFactor Q/(3:ℝ)^j)*D) *
          Real.sqrt (lemmaVTiledWeakEnergy Q j u.toH1Function.grad) := by
  classical
  let r := cubeScaleFactor Q/(3:ℝ)^j
  let W := lemmaVTiledWeakEnergy Q j u.toH1Function.grad
  let A := (52/100:ℝ)^2*cubeScaleFactor Q^2+(662/1000:ℝ)^2*r^2
  let P := fun U => positiveHaarNorm U u.toH1Function.toFun
  let H := fun U => hilbertPositiveHaarNorm U (Real.sqrt 3) (fun x => u.toH1Function.toFun x • b x)
  let F := fun U => energy U u.toH1Function.toFun
  let w : OldSignedCellIndex Q j → ℝ := fun _ => ((descendantsAtDepth Q j).card : ℝ)⁻¹
  have hr : 0 ≤ r := div_nonneg (Triadic.cubeScaleFactor_pos' Q).le (pow_nonneg (by norm_num) _)
  have hW : 0 ≤ W := lemmaVTiledWeakEnergy_nonneg Q j _
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hlocal (U : OldSignedCellIndex Q j) :
      H U.val ≤ M*Real.sqrt (P U.val^2)+(r*(715/1000)*D)*Real.sqrt (F U.val) := by
    have hh := parent_boundary_cell_product U.val
      (u.toH1Function.restrictToOpenSubcube U.property) b hb M D hM hD hvalue hgrad
    have hp : 0 ≤ P U.val := Real.sqrt_nonneg _
    simpa only [H1Function.restrictToOpenSubcube_toFun,
      cubeScaleFactor_descendant_eq_div_pow U.property, Real.sqrt_sq hp, mul_assoc,
      H, P, F, r] using hh
  have havg (f : TriadicCube 2 → ℝ) :
      (∑ U : OldSignedCellIndex Q j, w U*f U.val) = descendantsAverage Q j f := by
    simp only [w, ← Finset.mul_sum]
    exact old_signed_cell_average_eq_descendantsAverage Q j f
  have hh := old_signed_finite_weighted_sqrt_energy_bound w
    (fun U => P U.val^2) (fun U => F U.val) (fun U => H U.val)
    (fun _ => by dsimp [w]; positivity) hM
    (mul_nonneg (mul_nonneg hr (by norm_num)) hD)
    (fun _ => sq_nonneg _) (fun U => energy_nonneg U.val _)
    (fun _ => Real.sqrt_nonneg _) hlocal
  rw [havg (fun U => H U^2), havg (fun U => P U^2), havg F] at hh
  have hP := Real.sqrt_le_sqrt (parent_boundary_h10_broken_positive_sq Q j u)
  have hE := parent_boundary_h10_l2_sq Q j u
  have hEnorm : Real.sqrt (energy Q u.toH1Function.toFun) ≤
      (52/100:ℝ)*cubeScaleFactor Q*Real.sqrt W := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨mul_nonneg (mul_nonneg (by norm_num) (Triadic.cubeScaleFactor_pos' Q).le)
      (Real.sqrt_nonneg W), ?_⟩
    simpa only [mul_pow, Real.sq_sqrt hW, W, mul_assoc] using hE
  have hEavg : descendantsAverage Q j F = energy Q u.toH1Function.toFun :=
    (energy_eq_descendantsAverage Q j u.toH1Function.memL2_normalizedCubeMeasure).symm
  rw [hEavg] at hh
  rw [Real.sqrt_mul hA] at hP
  have hcoeff : (r*(715/1000)*D)*((52/100:ℝ)*cubeScaleFactor Q) ≤
      (372/1000:ℝ)*cubeScaleFactor Q*r*D := by
    have hc := mul_le_mul_of_nonneg_right
      (by norm_num : (715/1000:ℝ)*(52/100) ≤ 372/1000)
      (mul_nonneg (mul_nonneg (Triadic.cubeScaleFactor_pos' Q).le hr) hD)
    convert hc using 1 <;> ring
  apply hh.trans
  calc
    _ ≤ M*(Real.sqrt A*Real.sqrt W)+(r*(715/1000)*D)*
        ((52/100:ℝ)*cubeScaleFactor Q*Real.sqrt W) :=
      add_le_add (mul_le_mul_of_nonneg_left hP hM)
        (mul_le_mul_of_nonneg_left hEnorm (by positivity))
    _ ≤ (M*Real.sqrt A+(372/1000:ℝ)*cubeScaleFactor Q*r*D)*Real.sqrt W := by
      have hc := mul_le_mul_of_nonneg_right hcoeff (Real.sqrt_nonneg W)
      nlinarith only [hc]

/-- Physical q3 finite covariance source columns satisfy the parent
multiplier bound with the actual full derivative traces31.2 and1859.52.
The entire covariance family is one Hilbert column before taking norms. -/
theorem parent_boundary_q3_finite_source
    {ι : Type*} (e : HilbertBasis ι ℝ WhiteNoise) (s : Finset ι)
    (Q : TriadicCube 2) (j : ℕ) (u : H10Function (openCubeSet Q))
    (b : ℝ) (L : {l : ℝ // 0<l}) :
    Real.sqrt (descendantsAverage Q j (fun U => hilbertPositiveHaarNorm U (Real.sqrt 3)
      (fun x => u.toH1Function.toFun x • mainQ3FiniteColumn e s b L x)^2)) ≤
      (Real.sqrt ((156/5:ℝ)*b^2/L.1^2) *
          Real.sqrt ((52/100:ℝ)^2*cubeScaleFactor Q^2 +
            (662/1000:ℝ)^2*(cubeScaleFactor Q/(3:ℝ)^j)^2) +
        (372/1000:ℝ)*cubeScaleFactor Q*(cubeScaleFactor Q/(3:ℝ)^j)*
          Real.sqrt ((46488/25:ℝ)*b^2/L.1^4)) *
        Real.sqrt (lemmaVTiledWeakEnergy Q j u.toH1Function.grad) := by
  apply parent_boundary_h10_product_broken Q j u (mainQ3FiniteColumn e s b L)
    (mainQ3FiniteColumn_contDiff e s b L) _ _ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  · intro x
    apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt (by positivity : (0:ℝ) ≤ (156/5:ℝ)*b^2/L.1^2)]
    exact mainQ3FiniteColumn_norm_sq_le e s b L x
  · intro x
    rw [Real.sq_sqrt (by positivity : (0:ℝ) ≤ (46488/25:ℝ)*b^2/L.1^4)]
    exact mainQ3FiniteColumn_derivative_sq_le e s b L x

end
end ASDExplicitGamma.Native
