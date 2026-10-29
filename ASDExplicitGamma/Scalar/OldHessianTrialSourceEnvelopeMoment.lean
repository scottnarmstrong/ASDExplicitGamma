module

public import ASDExplicitGamma.Scalar.OldHessianTrialSourceEnvelope
public import ASDExplicitGamma.Scalar.OldHessianTrialCertifiedTraceMoments
public import ASDExplicitGamma.Scalar.OldHessianTrialSquareExpectation

/-! Correlated annealed source-square bounds with the actual scalar banks. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational Gaussian Inverse Main Cold Algsuperdiff.Section3
noncomputable section

/-- Endpoint bound for the coarse trace in every source-square payment. -/
def oldHessianCoarseTraceMomentCap (k : ℕ) : ℝ :=
  (14103/10000:ℝ)^k*((nativeSourceExactMeanCaps.getD 4 0:ℚ):ℝ)+
    rareExpansionTail (14103/10000:ℝ) (5/10^24:ℝ) ((5423/2500:ℝ)/(1-19/25)) k

/-- All required bank-weighted source-square envelopes are integrable and
paid by the same trace and OLD weak moments, with constant-one Minkowski. -/
theorem old_hessian_actual_source_envelope_moment
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (N : ℤ)
    (hpast : ∀ l<N,nativeInductionState M h l) (m : ℤ) (hm : m<N)
    (b : ℝ) (L : {l : ℝ // 0<l}) (k : ℕ) (hk : k≤3) :
    Integrable (fun ω => oldHessianGroupedBank M m ω^k*oldHessianSourceEnvelope M m b L ω)
      (Cutoff.cutoffSampleLaw M).toMeasure ∧
    (∫ ω,oldHessianGroupedBank M m ω^k*oldHessianSourceEnvelope M m b L ω
      ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
      (oldSignedSourceMultiplier (originCube 2 (m+129)) 134 b L*
          Real.sqrt (oldHessianCoarseTraceMomentCap (k+1))+
        (oldHessianCoarseColumnCoefficient (originCube 2 (m+129)) 133 b L*inverseHistoryDiscount)*
          Real.sqrt ((14103/10000:ℝ)^k*(mixedXiPreCap M+(1/10^12:ℝ)*theta M)))^2 := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let B := oldHessianGroupedBank M m
  let T := oldHessianSourceTrace M m 4
  let Θ := oldHessianGroupedOldTheta M m
  let a := oldSignedSourceMultiplier (originCube 2 (m+129)) 134 b L
  let c := oldHessianCoarseColumnCoefficient (originCube 2 (m+129)) 133 b L*inverseHistoryDiscount
  let f := fun ω => B ω^(k+1)*T ω
  let g := fun ω => B ω^k*Θ ω
  have hB (ω) : 0≤B ω := ENNReal.toReal_nonneg
  have hT (ω) : 0≤T ω := old_hessian_source_trace_nonneg M m 4 ω
  have hΘ (ω) : 0≤Θ ω := by
    change 0≤oldHessianGroupedOldTheta M m ω
    rw [old_hessian_grouped_old_theta_series]
    exact tsum_nonneg (fun j => old_hessian_grouped_old_theta_term_nonneg M m j ω)
  have ha : 0≤a := old_hessian_source_multiplier_nonneg _ _ b L
  have hc : 0≤c := by
    unfold c oldHessianCoarseColumnCoefficient
    have hQ := Triadic.cubeScaleFactor_pos' (originCube 2 (m+129))
    have hL := L.property
    have hα := inverse_history_discount_range.1.le
    positivity
  have hf := old_hessian_endpoint_trace_moment M h hM hg N hpast m hm 4 (Or.inl rfl) (k+1) (by omega)
  have hgθ := old_hessian_grouped_old_theta_moments M h hM hg N hpast m hm k hk
  have hh := old_hessian_square_expectation μ f g a c hf.1 hgθ.2.1
    (fun ω => mul_nonneg (pow_nonneg (hB ω) _) (hT ω))
    (fun ω => mul_nonneg (pow_nonneg (hB ω) _) (hΘ ω)) ha hc
  have he : (fun ω => B ω^k*oldHessianSourceEnvelope M m b L ω)=
      (fun ω => (a*Real.sqrt (f ω)+c*Real.sqrt (g ω))^2) := by
    funext ω
    unfold oldHessianSourceEnvelope
    rw [Real.sqrt_mul (sq_nonneg inverseHistoryDiscount),
      Real.sqrt_sq inverse_history_discount_range.1.le]
    simp only [←mul_assoc]
    change B ω^k*(a*Real.sqrt (B ω*T ω)+c*Real.sqrt (Θ ω))^2=_
    rw [old_hessian_weighted_root_square _ _ _ _ _ (pow_nonneg (hB ω) k)]
    have hp : B ω^k*(B ω*T ω)=f ω := by dsimp only [f]; rw [pow_succ]; ring
    rw [hp]
  refine ⟨he.symm ▸ hh.1,?_⟩
  rw [he]
  exact hh.2.trans (pow_le_pow_left₀
    (add_nonneg (mul_nonneg ha (Real.sqrt_nonneg _)) (mul_nonneg hc (Real.sqrt_nonneg _)))
    (add_le_add (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hf.2) ha)
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hgθ.2.2) hc)) 2)

end
end ASDExplicitGamma.Scalar
