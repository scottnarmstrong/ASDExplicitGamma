module

public import ASDExplicitGamma.Native.HeatVHEATDriftConfiguredCoefficients
public import ASDExplicitGamma.Native.HeatVHEATDriftSourceExpectation

/-! Configured refined coefficients in the actual source expectation. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ProbabilityTheory Gaussian Algsuperdiff.Section3 Numerics.Native
open scoped ENNReal NNReal
noncomputable section

/-- Increasing the two drift coefficients increases the complete leading
and rare payment, including the zero actual heat-norm endpoint. -/
theorem heatVHEATDrift_payment_mono_coefficients
    (k : ℕ) (e K C K' C' b eps X F L : ℝ)
    (he : 0 ≤ e) (hb : 0 ≤ b) (heps : 0 ≤ eps) (hX : 0 ≤ X) (hF : 0 ≤ F) (hL : 0 ≤ L)
    (hK : K ≤ K') (hC : C ≤ C') :
    (k:ℝ)*e*(2*K*b+C*b^2)*L+heatVHEATDriftFirstLine k e K C b eps X F ≤
      (k:ℝ)*e*(2*K'*b+C'*b^2)*L+heatVHEATDriftFirstLine k e K' C' b eps X F := by
  have hJ (j l : ℕ) : 0 ≤ nativeHeatVHEATJ eps X F 20 j l := by
    unfold nativeHeatVHEATJ
    split_ifs
    · exact mul_nonneg (pow_nonneg heps _) (pow_nonneg hX _)
    · exact mul_nonneg (mul_nonneg (pow_nonneg heps _) (pow_nonneg hX _))
        (Real.rpow_nonneg (div_nonneg hF hX) _)
  have h1 : 0 ≤ 4*nativeHeatVHEATJ eps X F 20 1 (k-1)+nativeHeatVHEATJ eps X F 20 1 k :=
    add_nonneg (mul_nonneg (by norm_num) (hJ _ _)) (hJ _ _)
  have h2 : 0 ≤ 4*nativeHeatVHEATJ eps X F 20 2 (k-1)+nativeHeatVHEATJ eps X F 20 2 k :=
    add_nonneg (mul_nonneg (by norm_num) (hJ _ _)) (hJ _ _)
  have hke : 0 ≤ (k:ℝ)*e := mul_nonneg (Nat.cast_nonneg _) he
  apply add_le_add
  · apply mul_le_mul_of_nonneg_right _ hL
    apply mul_le_mul_of_nonneg_left _ hke
    exact add_le_add (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hK (by norm_num)) hb)
      (mul_le_mul_of_nonneg_right hC (sq_nonneg _))
  · unfold heatVHEATDriftFirstLine
    apply mul_le_mul_of_nonneg_left _ hke
    apply add_le_add
    · apply mul_le_mul_of_nonneg_right _ h1
      exact add_le_add (mul_le_mul_of_nonneg_left hK (by norm_num))
        (mul_le_mul_of_nonneg_left hC (mul_nonneg (by norm_num) hb))
    · exact mul_le_mul_of_nonneg_right hC h2

/-- The actual refined source drift expectation with the source's configured
K and M. The exact nine-shell sums are first proved on the physical geometry,
then bounded by the existing complete source covariance certificates. -/
theorem nativeHeat_vheat_drift_configured_expectation {I : Type*}
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (hg : M.gamma ≤ gammaZero)
    (n : ℤ) (hpast : ∀ l<n,nativeInductionState M h l) (hstate : nativeInductionState M h n)
    (t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1) (k : ℕ) (hk : 1 ≤ k) (hk20 : k ≤ 20)
    (s : Finset I) (w : I → ℝ) (hw : ∀ i∈s,0 ≤ w i) (hw1 : ∑ i∈s,w i=1)
    (x : I → Vec 2) (g : I → (ℕ → ℝ) → ℝ) (hgm : ∀ i∈s,Measurable (g i))
    (v : I → ℝ≥0)
    (hlaw : ∀ i∈s,standardGaussianInfinitePi.map
      (fun ξ => g i ξ/(Annealed.sigmaBar M n:ℝ))=gaussianReal 0 (v i)) :
    let μ := nativeHeatRemainderJointLaw M
    let A := heatRefinedTraceAverage s w M n 9 t x g
    let X := heatVHEATDriftSourceXExtended s M n t x g
    let F := heatRefinedRawEnvelope 9 (heatVHEATDriftAuxVariance s v)
    X < ⊤ ∧ Integrable (heatVHEATDriftSource s w M h n t k x g) μ ∧
    (∫ z,heatVHEATDriftSource s w M h n t k x g z ∂μ) ≤
      (k:ℝ)*heatVHEATDriftE9 M*
        (2*(nativeHeatK:ℝ)*(3683/2500)+(nativeHeatM:ℝ)*(3683/2500)^2)*
        ((∫ z,A z^k ∂μ)+4*(∫ z,A z^(k-1) ∂μ))+
      heatVHEATDriftFirstLine k (heatVHEATDriftE9 M)
        nativeHeatK nativeHeatM (3683/2500) (3/10^46) X.toReal F := by
  dsimp only
  have hf := nativeHeat_vheat_drift_expectation M h hM hg n hpast hstate t ht k hk hk20
    s w hw hw1 x g hgm v hlaw
  have he : 0 ≤ heatVHEATDriftE9 M := by
    unfold heatVHEATDriftE9
    exact mul_nonneg (mul_nonneg (by norm_num) M.shellPrefix.gamma_pos.le)
      (Real.rpow_pos_of_pos (by norm_num) _).le
  have hA (z) : 0 ≤ heatRefinedTraceAverage s w M n 9 t x g z :=
    Finset.sum_nonneg (fun i hi => mul_nonneg (hw i hi)
      ((heat_refined_translated_trace_measurable_nonneg M n 9 t (x i) (g i) (hgm i hi)).2 z))
  have hc := heatVHEATDrift_source_sums_le_configured n
  refine ⟨hf.1,hf.2.1,hf.2.2.trans ?_⟩
  apply heatVHEATDrift_payment_mono_coefficients
    k (heatVHEATDriftE9 M) (heatVHEATDriftKActual n) heatVHEATDriftCActual
    nativeHeatK nativeHeatM (3683/2500) (3/10^46)
    (heatVHEATDriftSourceXExtended s M n t x g).toReal
    (heatRefinedRawEnvelope 9 (heatVHEATDriftAuxVariance s v)) _
    he (by norm_num) (by norm_num) ENNReal.toReal_nonneg (sq_nonneg _)
    (add_nonneg (integral_nonneg (fun z => pow_nonneg (hA z) _))
      (mul_nonneg (by norm_num) (integral_nonneg (fun z => pow_nonneg (hA z) _)))) hc.1 hc.2

end
end ASDExplicitGamma.Native
