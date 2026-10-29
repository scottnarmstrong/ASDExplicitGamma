module

public import ASDExplicitGamma.Native.OldSignedQ1MeanEnvelope
public import ASDExplicitGamma.Native.OldSignedSourceHistoryStationarity
public import ASDExplicitGamma.Native.OldSignedDirectionalRareReserve
public import ASDExplicitGamma.Native.OldSignedTiledHistoryPayment

/-! The complete correlated weak-history budget fits the unchanged q1 panel. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Gaussian Scalar Inverse Cold Variational Algsuperdiff.Section3
open Numerics.Inverse
noncomputable section

/-- The source-cell mean is the actual depth-five-plus-j insertion mean. -/
theorem old_signed_q1_source_mean_eq (M : ABKModel 2) (n : ℤ)
    (U : TriadicCube 2) (hU : U.scale=n-5) (t : ℝ) (ht : 0≤t ∧ t≤1) (j : ℕ) :
    (∫ ω,rawWeakTraceSequence M n U t ω j ∂(Cutoff.cutoffSampleLaw M).toMeasure)=
      inSourceMeanActual M n (5+j) t := by
  rw [old_signed_source_trace_mean_eq_depth M n U t ht j,hU]
  have he : n-5-(j:ℤ)=n-((5+j:ℕ):ℤ) := by push_cast; ring
  rw [he]
  rfl

/-- The complete directional half-trace and rare budget, doubled, fits Xi.
This estimate includes the entire infinite depth sum and its correlated reserve. -/
theorem old_signed_q1_source_history_affine_budget
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (n : ℤ)
    (hpast : ∀ l≤n,nativeInductionState M h l)
    (U : TriadicCube 2) (hU : U.scale=n-5) (t : ℝ) (ht : 0≤t ∧ t≤1) :
    2*((1-inverseHistoryDiscount^2)*∑' j : ℕ,inverseHistoryDiscount^(2*j)*
      oldSignedSourceHistoryBudget M n U t j)≤theta M*((23/100:ℝ)+(9/500)*t+1/10^12) := by
  let A := fun j : ℕ => inverseHistoryDiscount^(2*j)*bankDepthFrame M j*
    inSourceMeanActual M n (5+j) t
  let R := fun j : ℕ => inverseHistoryDiscount^(2*j)*inverseBankDepthReserve .localInverse M j*
    (theta M*(invTraceM:ℝ)*(1+(j:ℝ))^2*(3:ℝ)^(6*gammaZero*j))
  let d := 1-inverseHistoryDiscount^2
  have hA := old_signed_actual_weighted_mean_transport M h hM hg n hpast t ht
  have hR : Summable R := old_signed_depth_rare_summable M hg
  have he : (∑' j : ℕ,inverseHistoryDiscount^(2*j)*oldSignedSourceHistoryBudget M n U t j)=
      (3683/2500:ℝ)/2*(∑' j,A j)+(∑' j,R j) := by
    calc
      _ = ∑' j : ℕ,((3683/2500:ℝ)/2*A j+R j) := by
        apply tsum_congr
        intro j
        unfold oldSignedSourceHistoryBudget
        rw [old_signed_q1_source_mean_eq M n U hU t ht j]
        norm_num only [inverseBankCap]
        dsimp only [A,R]
        ring
      _ = _ := by rw [(hA.1.mul_left ((3683/2500:ℝ)/2)).tsum_add hR,tsum_mul_left]
  have hd : 0≤d := sub_nonneg.mpr
    (pow_le_one₀ inverse_history_discount_range.1.le inverse_history_discount_range.2.le)
  have hR0 : 0≤∑' j,R j := tsum_nonneg (fun j => by
    dsimp only [R]
    apply mul_nonneg
    · exact mul_nonneg (pow_nonneg inverse_history_discount_range.1.le _)
        (by unfold inverseBankDepthReserve inverseBankReserve bankDepthFrame; positivity)
    · exact mul_nonneg (mul_nonneg (mul_nonneg (cold_theta_pos M).le
        (by rw [invTrace_coefficient.1]; positivity)) (sq_nonneg _))
        (Real.rpow_nonneg (by norm_num) _))
  have hrare : 2*d*(∑' j,R j)≤(1/10^12:ℝ)*theta M :=
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by norm_num : (2:ℝ)≤13) hd) hR0).trans
      (old_signed_directional_rare_delta M hg)
  rw [he]
  calc
    _ = d*(3683/2500)*(∑' j,A j)+2*d*(∑' j,R j) := by dsimp only [d]; ring
    _ ≤ theta M*((23/100:ℝ)+(9/500)*t)+(1/10^12:ℝ)*theta M := add_le_add hA.2 hrare
    _ = theta M*((23/100:ℝ)+(9/500)*t+1/10^12) := by ring

/-- The complete directional budget is below the exact unchanged Xi field. -/
theorem old_signed_q1_source_history_budget
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (n : ℤ)
    (hpast : ∀ l≤n,nativeInductionState M h l)
    (U : TriadicCube 2) (hU : U.scale=n-5) (t : ℝ) (ht : 0≤t ∧ t≤1) :
    2*((1-inverseHistoryDiscount^2)*∑' j : ℕ,inverseHistoryDiscount^(2*j)*
      oldSignedSourceHistoryBudget M n U t j)≤theta M*oldSignedQ1PanelXi t :=
  (old_signed_q1_source_history_affine_budget M h hM hg n hpast U hU t ht).trans
    (mul_le_mul_of_nonneg_left (old_signed_affine_le_q1_panel_xi t ht.1) (cold_theta_pos M).le)

/-- Actual tiled weak history is integrable and paid by the exact Xi field. -/
theorem old_signed_actual_q1_panel_weak
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (n : ℤ)
    (hpast : ∀ l≤n,nativeInductionState M h l) (t : ℝ) (ht : 0≤t ∧ t≤1) :
    Integrable (oldSignedActualTiledWeakProxy M n 5 t) (Cutoff.cutoffSampleLaw M).toMeasure ∧
    (∫ ω,oldSignedActualTiledWeakProxy M n 5 t ω ∂(Cutoff.cutoffSampleLaw M).toMeasure)≤
      theta M*oldSignedQ1PanelXi t := by
  have hh := old_signed_tiled_history_payment M h hM hg n 5 (by norm_num) t ht hpast
  exact ⟨hh.1,hh.2.trans (old_signed_q1_source_history_budget M h hM hg n hpast
    (originCube 2 (n-5)) rfl t ht)⟩

end
end ASDExplicitGamma.Native
