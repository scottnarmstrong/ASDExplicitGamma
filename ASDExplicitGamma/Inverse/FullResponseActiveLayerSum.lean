module

public import ASDExplicitGamma.Inverse.FullResponseActiveLayerMean
public import ASDExplicitGamma.Inverse.FullResponseActiveReferenceSum

/-! All three actual parent-density resolutions on a full-response layer. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Triadic
open scoped ENNReal
noncomputable section

/-- The complete spatial parent mean/density payment on a deterministic layer. -/
def fullResponseActiveLayerDensity (M : ABKModel 2) (Q : TriadicCube 2)
    (H n : ℕ) (N : ℤ) (weights : ℤ → ℝ) (ω : Cutoff.CutoffSample 2) : ℝ :=
  ∑ e : Fin 3, ∑ U ∈ whitneyRootLayer Q H n,
    ((volume (cubeSet U)).toReal/(volume (cubeSet Q)).toReal)*
      (fullResponseTraceC0+fullResponseTraceC1*
        (fullResponseParentWaveMean M U (Q.scale-342) N weights ω)^2)*
      cubeAverage U (fun x =>
        (layerResolutionDiameter M Q H (rootTau .full) (waveGateEta .full) n e ω x)^2)

/-- Summing the existing sharp spatial Holder comparison over the three
actual resolutions gives exactly the source active mean and D2/D4 excess. -/
theorem full_response_active_layer_density_le
    (M : ABKModel 2) (Q : TriadicCube 2) (hk : ℕ × ℕ) (q T : ℝ)
    (N : ℤ) (weights : ℤ → ℝ) (ω : Cutoff.CutoffSample 2) :
    let Y := fun m e => resetDensityExcess M Q 377 (rootTau .full)
      (waveGateEta .full) q T m hk e ω
    fullResponseActiveLayerDensity M Q (377+hk.1) (hk.2+1) N weights ω ≤
      fullResponseTraceC0*(3*bankLayerWeight hk.2*densityMomentBudget q 2 T+
        ∑ e : Fin 3, Y 2 e)+
      fullResponseTraceC1*fullResponseLayerWaveFourth M Q 377 hk
        (Q.scale-342) N weights ω*
          (3*Real.sqrt (bankLayerWeight hk.2)*Real.sqrt (densityMomentBudget q 4 T)+
            ∑ e : Fin 3, Real.sqrt (Y 4 e)) := by
  dsimp only
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun e _ =>
    full_response_active_layer_mean_add_excess M Q 377 (by norm_num) hk q T e
      (Q.scale-342) N weights ω)
  apply hh.trans_eq
  rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum,
    Finset.sum_add_distrib,Finset.sum_add_distrib]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  ring

/-- Every parent layer payment is nonnegative. -/
theorem full_response_active_layer_density_nonneg
    (M : ABKModel 2) (Q : TriadicCube 2) (H n : ℕ) (N : ℤ)
    (weights : ℤ → ℝ) (ω : Cutoff.CutoffSample 2) :
    0 ≤ fullResponseActiveLayerDensity M Q H n N weights ω := by
  unfold fullResponseActiveLayerDensity
  apply Finset.sum_nonneg
  intro e _
  apply Finset.sum_nonneg
  intro U _
  apply mul_nonneg
  · have hc0 : 0 ≤ fullResponseTraceC0 := by
      unfold fullResponseTraceC0 rootTau
      positivity
    have hc1 : 0 ≤ fullResponseTraceC1 := by
      unfold fullResponseTraceC1 rootTau
      positivity
    exact mul_nonneg (div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
      (add_nonneg hc0 (mul_nonneg hc1 (sq_nonneg _)))
  · unfold cubeAverage
    exact mul_nonneg (inv_nonneg.mpr (cubeVolume_pos U).le)
      (integral_nonneg (fun _ => sq_nonneg _))

end
end ASDExplicitGamma.Inverse
