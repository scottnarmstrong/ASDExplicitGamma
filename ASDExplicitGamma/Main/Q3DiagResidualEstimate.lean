module

public import ASDExplicitGamma.Main.Q3DiagResidualLocal
public import ASDExplicitGamma.Triadic.PositiveNormAggregation

/-! Broken-norm aggregation of the actual q3 covariance residual. -/

@[expose] public section
namespace ASDExplicitGamma.Main
open Homogenization MeasureTheory ASDExplicitGamma.Gaussian ASDExplicitGamma.Triadic
open ASDExplicitGamma.Variational
open scoped BigOperators

local instance mainQ3DiagEstimateFiniteMeasure (Q : TriadicCube 2) :
    IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
  (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume

/-- Exact pre-rounding source remainder coefficient. -/
noncomputable def mainQ3RemainderExact (r b L : ℝ) : ℝ :=
  r*(1/Real.sqrt 3+planarC1+2/Real.pi+1/2)*Real.sqrt ((156/5)*b^2/L^2)+
    r^2*planarC1*(planarC0+1/2)*Real.sqrt ((46488/25)*b^2/L^4)

/-- Actual centered covariance residuals satisfy the exact broken source bound.
All three DIAG estimates, covariance moments and product memberships are
conclusions of previously proved theorems, not hypotheses of this result. -/
theorem main_q3_diag_residual_estimate {ι : Type*} (e : HilbertBasis ι ℝ WhiteNoise)
    (s : Finset ι) (b : ℝ) (L : {l : ℝ // 0 < l}) (Q : TriadicCube 2) (j : ℕ)
    (p : Vec 2) (u : H10Function (openCubeSet Q)) :
    let φ := lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) p u
    (∀ U ∈ descendantsAtDepth Q j, Summable (fun k => (Real.sqrt 3)^(k+1)*hilbertEnergy U
      (hilbertCubeIncrement U (k+1) (mainQ3DiagResidualColumn e s b L Q j φ U)))) ∧
    Real.sqrt (descendantsAverage Q j (fun U => hilbertPrimalEnergy U (Real.sqrt 3)
      (mainQ3DiagResidualColumn e s b L Q j φ U))) ≤
      mainQ3RemainderExact (diagMeshRadius Q j) b L.1*Real.sqrt (lemmaVTiledWeakEnergy Q j φ.grad) := by
  intro φ
  let I := diagInterpolant Q j
  let z := φ-I φ
  let r := diagMeshRadius Q j
  let σ := Real.sqrt ((156/5)*b^2/L.1^2)
  let τ := Real.sqrt ((46488/25)*b^2/L.1^4)
  let A := r*(1/Real.sqrt 3+planarC1)*σ
  let C := r*planarC1*τ
  let E := fun U => hilbertPrimalEnergy U (Real.sqrt 3) (mainQ3DiagResidualColumn e s b L Q j φ U)
  have hr : 0 ≤ r := (diagMeshRadius_pos Q j).le
  have hσ : 0 ≤ σ := Real.sqrt_nonneg _
  have hτ : 0 ≤ τ := Real.sqrt_nonneg _
  have hc1 : 0 ≤ planarC1 := Real.sqrt_nonneg _
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hC : 0 ≤ C := mul_nonneg (mul_nonneg hr hc1) hτ
  have hlocal (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth Q j) :=
    main_q3_diag_residual_local e s b L Q j p u U hU
  refine ⟨fun U hU => (hlocal U hU).1, ?_⟩
  have hEn (U : TriadicCube 2) : 0 ≤ E U := by
    unfold E hilbertPrimalEnergy
    exact add_nonneg (hilbertEnergy_nonneg U _)
      (tsum_nonneg fun k => mul_nonneg (by positivity) (hilbertEnergy_nonneg U _))
  have hagg := sqrt_descendantsAverage_energy_bound_three Q j E
    (fun U => vectorPositiveHaarEnergy U (I φ).grad)
    (fun U => primalEnergy U (Real.sqrt 3) z.toFun)
    (fun U => energy U z.toFun) hA hσ hC
    (fun U _ => hEn U) (fun U _ => vectorPositiveHaarEnergy_nonneg U _)
    (fun U _ => primalEnergy_nonneg U _ (Real.sqrt_nonneg _) _)
    (fun U _ => energy_nonneg U _)
    (fun U hU => (hlocal U hU).2)
  have hp := diagInterpolant_gradient_estimate Q j p u
  have hzP := diagInterpolant_residual_positive_estimate Q j p u
  have hzL := diagInterpolant_residual_L2_estimate Q j p u
  have henergy : descendantsAverage Q j (fun U => energy U z.toFun) = energy Q z.toFun :=
    (energy_eq_descendantsAverage Q j z.memL2_normalizedCubeMeasure).symm
  rw [henergy] at hagg
  have heF : descendantsAverage Q j (fun U => vectorPositiveHaarEnergy U (I φ).grad) =
      lemmaVTiledPositiveEnergy Q j (I φ).grad := rfl
  have heG : descendantsAverage Q j (fun U => primalEnergy U (Real.sqrt 3) z.toFun) =
      diagTiledScalarPositiveEnergy Q j z.toFun := rfl
  rw [heF, heG] at hagg
  refine hagg.trans ?_
  calc
    _ ≤ A*Real.sqrt (lemmaVTiledWeakEnergy Q j φ.grad)+
        σ*(r*(2/Real.pi+1/2)*Real.sqrt (lemmaVTiledWeakEnergy Q j φ.grad))+
        C*(r*(planarC0+1/2)*Real.sqrt (lemmaVTiledWeakEnergy Q j φ.grad)) := by
      apply add_le_add
      · exact add_le_add (mul_le_mul_of_nonneg_left hp hA) (mul_le_mul_of_nonneg_left hzP hσ)
      · exact mul_le_mul_of_nonneg_left hzL hC
    _ = _ := by unfold A C r σ τ mainQ3RemainderExact; ring

end ASDExplicitGamma.Main
