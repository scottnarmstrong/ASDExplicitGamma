module

public import ASDExplicitGamma.Cold.PlateauRecurrence
public import ASDExplicitGamma.Cold.PlateauNumericTerms

/-! # Actual P1--P6 recurrence as the checked fixed-threshold mean update -/

@[expose] public section
noncomputable section
open MeasureTheory Homogenization
open ASDExplicitGamma.Triadic
open scoped BigOperators
namespace ASDExplicitGamma.Cold
open ASDExplicitGamma.Numerics.Cold

/-- The actual plateau recurrence, with source history and exact source graph candidates,
produces the fixed-threshold scaled mean inequality consumed by the triangular induction.
The all-depth cell means are retained separately: fine cells may have negative native lag. -/
theorem cold_plateau_numeric_step {Q : TriadicCube 2} {Ω : Type*}
    [MeasurableSpace Ω] {ℙ : Measure Ω} [IsProbabilityMeasure ℙ]
    (F : ColdPlateauFamily Q Ω) {J r4 : ℕ} (hJ : 2 ≤ J) (hr4 : r4 = 4)
    (hj : 2*J ∈ coldUpdatedLags) {θ : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1)
    {D : Ω → ℝ} (hD : Measurable D) (hDn : ∀ᵐ ω ∂ℙ, 0 ≤ D ω)
    (h20 : Integrable (fun ω => D ω^20) ℙ)
    (hMoment : (∫ ω, D ω^20 ∂ℙ) ≤ (θ*(coldHistoryAt (2*J):ℝ))^20)
    (hV : ∀ k, AEStronglyMeasurable (F.projectedGraph (2*(k+1))) ℙ)
    (hroot : ∀ᵐ ω ∂ℙ, (F.atDepth 0).parentTrace ω ≤ D ω)
    (hmax : ∀ᵐ ω ∂ℙ, ∀ r, ∀ R, (F.atDepth r).cellTrace R ω ≤ (3:ℝ)^((r:ℝ)/4)*D ω)
    (hInt4 : ColdRecoveryIntegrable (F.atDepth r4) ℙ)
    (hcell : ∀ r R, Integrable ((F.atDepth r).cellTrace R) ℙ)
    (hG : ∀ k < J, Integrable (fun ω => squareOwnGraphEnergy Q (F.cells (2*(k+1)) ω)) ℙ)
    (hGcap : ∀ k < J, (∫ ω, squareOwnGraphEnergy Q (F.cells (2*(k+1)) ω) ∂ℙ) ≤
      coldSelectedGraphCap θ (2*J-2*(k+1)))
    {μsmall μ : ℕ → ℝ}
    (hstat : ∀ r R, ∫ ω, (F.atDepth r).cellTrace R ω ∂ℙ = μsmall r)
    (hnear : ∀ r ≤ 2*J, μsmall r = μ (2*J-r))
    (hparent : (∫ ω, (F.atDepth 0).parentTrace ω ∂ℙ) = μ (2*J)) :
    coldExactDenominator (2*J)*μ (2*J) ≤ coldExactWeightedMeans μ (2*J)+
      θ*((coldGraphContribution (2*J):ℝ)+(coldBadHistory (2*J):ℝ)) := by
  have hp := cold_plateau_parameters (2*J) hj
  have hc : (0:ℝ) < ((paramsForLag (2*J)).c:ℝ) := Rat.cast_pos.mpr hp.1
  have hc1 : ((paramsForLag (2*J)).c:ℝ) < 1 := by exact_mod_cast hp.2.1
  have ht : (0:ℝ) < ((paramsForLag (2*J)).t:ℝ) := Rat.cast_pos.mpr hp.2.2.1
  have hη : (0:ℝ) < ((paramsForLag (2*J)).eta:ℝ) := Rat.cast_pos.mpr hp.2.2.2.1
  have hξ : (0:ℝ) < (coldXi (2*J):ℝ) := Rat.cast_pos.mpr hp.2.2.2.2.1
  have h := plateau_recurrence F hJ hr4 hc hc1 ht hη hξ hD hDn h20 hMoment hV hroot hmax
    hInt4 hcell hG hstat
  dsimp only at h
  have hcst := plateau_constants_numeric (2*J)
  rw [← hcst.1,← hcst.2.1,← hcst.2.2.1,← hcst.2.2.2] at h
  rw [plateau_denominator_numeric (by omega),hparent] at h
  have hmeans : (∑ k ∈ Finset.range J,
      plateauLagCoefficient (coldCT (2*J):ℝ) (coldCD (2*J):ℝ)
        (1+1/((paramsForLag (2*J)).t:ℝ)) (coldG0 (2*J):ℝ) (coldG1 (2*J):ℝ) (coldXi (2*J):ℝ) k*
          μsmall (2*(k+1))) = coldExactWeightedMeans μ (2*J) := by
    rw [← plateau_mean_term_numeric μ J]
    apply Finset.sum_congr rfl
    intro k hk
    rw [hnear _ (by have hh := Finset.mem_range.mp hk; omega)]
  rw [hmeans] at h
  have hCT : 0 ≤ (coldCT (2*J):ℝ) := by rw [hcst.1]; positivity
  have hg1 : 0 ≤ (coldG1 (2*J):ℝ) := by rw [hcst.2.2.2]; positivity
  have hα : 0 ≤ 1+1/((paramsForLag (2*J)).t:ℝ) := by positivity
  have hgraph : (coldCT (2*J):ℝ)*(1+((paramsForLag (2*J)).t:ℝ))*
      (∑ k ∈ Finset.range J, plateauEvenWeight k*
        (∫ ω, squareOwnGraphEnergy Q (F.cells (2*(k+1)) ω) ∂ℙ)) ≤
      θ*(coldGraphContribution (2*J):ℝ) := by
    have hs := Finset.sum_le_sum (s := Finset.range J) (fun k hk => mul_le_mul_of_nonneg_left
      ((hGcap k (Finset.mem_range.mp hk)).trans (cold_selected_graph_table_scaled hθ hθ1
        (by have hjb := cold_updated_lag_bounds (2*J) hj; have hh := Finset.mem_range.mp hk; omega)))
      (plateauEvenWeight_nonneg k))
    have hm := mul_le_mul_of_nonneg_left hs (mul_nonneg hCT (by positivity : 0 ≤ 1+((paramsForLag (2*J)).t:ℝ)))
    apply hm.trans_eq
    rw [← plateau_graph_term_numeric J]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  let B : ℝ := (55/4:ℝ)*(coldCT (2*J):ℝ)*(coldG1 (2*J):ℝ)*(1+1/((paramsForLag (2*J)).t:ℝ))*
    (coldHistoryAt (2*J):ℝ)^20/(coldXi (2*J):ℝ)^18
  have hB : 0 ≤ B := div_nonneg
    (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hCT) hg1) hα)
      (pow_nonneg (Rat.cast_nonneg.mpr hp.2.2.2.2.2) 20)) (pow_nonneg hξ.le 18)
  have hbad := cold_bad_charge_le_scale hθ hθ1 hB
  have he : (55/4:ℝ)*(coldCT (2*J):ℝ)*(coldG1 (2*J):ℝ)*(1+1/((paramsForLag (2*J)).t:ℝ))*
      (θ*(coldHistoryAt (2*J):ℝ))^20/(coldXi (2*J):ℝ)^18 = θ^20*B := by dsimp only [B]; ring
  have hb : (55/4:ℝ)*(coldCT (2*J):ℝ)*(coldG1 (2*J):ℝ)*(1+1/((paramsForLag (2*J)).t:ℝ))*
      (θ*(coldHistoryAt (2*J):ℝ))^20/(coldXi (2*J):ℝ)^18 ≤ θ*(coldBadHistory (2*J):ℝ) := by
    rw [he]
    simpa only [B,plateau_bad_term_numeric] using hbad
  linarith only [h,hgraph,hb]

end ASDExplicitGamma.Cold
