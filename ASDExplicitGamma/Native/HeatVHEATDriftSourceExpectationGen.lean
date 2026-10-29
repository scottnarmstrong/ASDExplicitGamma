module

public import ASDExplicitGamma.Native.HeatVHEATDriftSourceExpectation
public import ASDExplicitGamma.Native.HeatVHEATSourceCarrierGen
public import ASDExplicitGamma.Native.HeatVHEATRefinedShellLawGen
public import ASDExplicitGamma.Native.HeatVHEATDriftSourceClocksGen
public import ASDExplicitGamma.Native.HeatVHEATRefinedSourceProfilesGen
public import ASDExplicitGamma.Native.HeatVHEATRefinedSourceTransportGen
public import ASDExplicitGamma.Native.HeatVHEATDriftSourceGeometryGen
public import ASDExplicitGamma.Native.HeatVHEATDriftSourceBankGen
public import ASDExplicitGamma.Native.HeatVHEATDriftBankIdentityGen
public import ASDExplicitGamma.Native.HeatVHEATDriftBankMeasurableGen
public import ASDExplicitGamma.Native.HeatVHEATDriftSourceIntegrandGen
public import ASDExplicitGamma.Native.HeatVHEATDriftSourceNormsGen

/-! The `ns`-shell generalization of `HeatVHEATDriftSourceExpectation`. -/

@[expose] public section


namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ProbabilityTheory Gaussian Algsuperdiff.Section3
open scoped ENNReal NNReal
noncomputable section

variable (ns : ℕ)

/-- The actual nine-shell drift/mixed expectation, with the literal finite
coefficient sums, exact leading moments, and complete first-line J bill.
All trace and rare norm inputs are proved from the native states and actual
Gaussian marginal laws. No estimate premise, child independence, positive
padding of X, or maximum of the physical rare factors is used. -/
theorem nativeHeat_vheat_drift_expectation_Gen (hns : ns ≤ 1331) {I : Type*}
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (hg : M.gamma ≤ gammaZero)
    (n : ℤ) (hpast : ∀ l<n,nativeInductionState M h l) (hstate : nativeInductionState M h n)
    (t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1) (k : ℕ) (hk : 1 ≤ k) (hk20 : k ≤ 20)
    (s : Finset I) (w : I → ℝ) (hw : ∀ i∈s,0 ≤ w i) (hw1 : ∑ i∈s,w i=1)
    (x : I → Vec 2) (g : I → (ℕ → ℝ) → ℝ) (hgm : ∀ i∈s,Measurable (g i))
    (v : I → ℝ≥0)
    (hlaw : ∀ i∈s,standardGaussianInfinitePi.map
      (fun ξ => g i ξ/(Annealed.sigmaBar M n:ℝ))=gaussianReal 0 (v i)) :
    let μ := nativeHeatRemainderJointLaw M
    let A := heatRefinedTraceAverage s w M n ns t x g
    let X := (heatVHEATDriftSourceXExtendedGen ns) s M n t x g
    let F := heatRefinedRawEnvelope ns (heatVHEATDriftAuxVariance s v)
    X < ⊤ ∧ Integrable ((heatVHEATDriftSourceGen ns) s w M h n t k x g) μ ∧
    (∫ z,(heatVHEATDriftSourceGen ns) s w M h n t k x g z ∂μ) ≤
      (k:ℝ)*(heatVHEATDriftEGen ns) M*
        (2*(heatVHEATDriftKActualGen ns) n*(3683/2500)+(heatVHEATDriftCActualGen ns)*(3683/2500)^2)*
        ((∫ z,A z^k ∂μ)+4*(∫ z,A z^(k-1) ∂μ))+
      heatVHEATDriftFirstLine k ((heatVHEATDriftEGen ns) M)
        ((heatVHEATDriftKActualGen ns) n) (heatVHEATDriftCActualGen ns) (3683/2500)
        (3/10^46) X.toReal F := by
  let heatJointProbability : IsProbabilityMeasure (nativeHeatRemainderJointLaw M) :=
    inferInstanceAs (IsProbabilityMeasure ((Cutoff.cutoffSampleLaw M).toMeasure.prod standardGaussianInfinitePi))
  dsimp only
  have hn := (heatVHEATDrift_source_norms_Gen ns hns) M h hM hg n hpast t ht.2 s w hw hw1 x g hgm v hlaw
  have hT (i : I) (hi : i∈s) :=
    heat_refined_translated_trace_measurable_nonneg M n ns t (x i) (g i) (hgm i hi)
  have hR (i : I) := heat_refined_translated_rare_profiles M h hM hg n ns hpast t ht.2 (x i)
  have hA := heat_refined_average_profiles M h hM hg n ns hns hpast t ht.2
    s w hw hw1 x g hgm v (heatVHEATDriftAuxVariance s v) hlaw
    (fun i hi => by exact_mod_cast (Finset.le_sup (f := v) hi))
  have he : 0 ≤ (heatVHEATDriftEGen ns) M := by
    unfold heatVHEATDriftEGen
    exact mul_nonneg (mul_nonneg (by norm_num) M.shellPrefix.gamma_pos.le)
      (Real.rpow_pos_of_pos (by norm_num) _).le
  have hc := (heatVHEATDrift_source_sums_nonneg_Gen ns) n
  have hf := heatVHEATDrift_full_average_integral_nonneg_cap
    (nativeHeatRemainderJointLaw M) s w hw hw1
    (fun i => heatRefinedTranslatedRare M n ns t (x i))
    (fun i => heatRefinedTranslatedTrace M n ns t (x i) (g i))
    (heatRefinedTraceAverage s w M n ns t x g) (fun _ => rfl)
    (fun i _ => (hR i).1.aestronglyMeasurable) (fun i hi => (hT i hi).1.aestronglyMeasurable)
    hA.1.aestronglyMeasurable (fun i _ => (hR i).2.1) (fun i hi => (hT i hi).2) hA.2.1
    k hk hk20 ((heatVHEATDriftEGen ns) M) ((heatVHEATDriftKActualGen ns) n) (heatVHEATDriftCActualGen ns)
    (3683/2500) (3/10^46) ((heatVHEATDriftSourceXExtendedGen ns) s M n t x g).toReal
    (heatRefinedRawEnvelope ns (heatVHEATDriftAuxVariance s v))
    he hc.1 hc.2 (by norm_num) (by norm_num) ENNReal.toReal_nonneg (sq_nonneg _)
    hn.2.1 hn.2.2.2.1 hn.2.2.1 hn.2.2.2.2.2 hn.2.2.2.2.1
  have hb := (heatVHEATDrift_source_ae_majorant_Gen ns) M h hM hg n hpast hstate t ht.2 k s w hw x g
  have hi := hf.1.mono_nonneg
    ((heatVHEATDrift_source_measurable_Gen ns) s w M h n t k x g hgm).aestronglyMeasurable
    (hb.mono (fun _ hz => hz.1)) (hb.mono (fun _ hz => hz.2))
  exact ⟨hn.1,hi,(integral_mono_ae hi hf.1 (hb.mono (fun _ hz => hz.2))).trans hf.2⟩

end
end ASDExplicitGamma.Native
