module

public import ASDExplicitGamma.Native.HeatVHEATDriftBankMeasurable
public import ASDExplicitGamma.Native.HeatVHEATDriftSourceGeometry
public import ASDExplicitGamma.Native.HeatVHEATDriftFullNonneg
public import ASDExplicitGamma.Native.HeatRefinedFamilyProfiles

/-! The actual refined drift row, before any expectation or norm estimate. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Gaussian Algsuperdiff.Section3
noncomputable section

/-- The centered drift/mixed profile on the common physical and auxiliary
law. The diagonal center term is excluded only after exact cancellation by
the carrier owner. All children retain their actual coupled fields. -/
def heatVHEATDriftSource {I : Type*} (s : Finset I) (w : I → ℝ)
    (M : ABKModel 2) (h : ℝ) (n : ℤ) (t : ℝ) (k : ℕ)
    (x : I → Vec 2) (g : I → (ℕ → ℝ) → ℝ)
    (z : Cutoff.CutoffSample 2 × (ℕ → ℝ)) : ℝ :=
  ∑ i∈s,w i*((k:ℝ)*(heatRefinedTraceAverage s w M n 9 t x g z)^(k-1)*
    (∑ d : Fin 9,
      (2*heatVHEATDriftVariance M h n d*heatVHEATDriftKappa n d*
        heatVHEATDriftBank M n 9 t (Cutoff.translateCutoffSample (x i) z.1) (g i z.2) d+
       heatVHEATDriftVariance M h n d*heatVHEATDriftMu d*
        (heatVHEATDriftBank M n 9 t (Cutoff.translateCutoffSample (x i) z.1) (g i z.2) d)^2))*
    (heatRefinedTranslatedTrace M n 9 t (x i) (g i) z+4))

/-- Actual source-row measurability requires only measurability of the
auxiliary coordinates, not a bank or response estimate. -/
theorem heatVHEATDrift_source_measurable {I : Type*}
    (s : Finset I) (w : I → ℝ) (M : ABKModel 2) (h : ℝ) (n : ℤ) (t : ℝ) (k : ℕ)
    (x : I → Vec 2) (g : I → (ℕ → ℝ) → ℝ) (hgm : ∀ i∈s,Measurable (g i)) :
    Measurable (heatVHEATDriftSource s w M h n t k x g) := by
  have hT (i : I) (hi : i∈s) :=
    (heat_refined_translated_trace_measurable_nonneg M n 9 t (x i) (g i) (hgm i hi)).1
  have hA : Measurable (heatRefinedTraceAverage s w M n 9 t x g) :=
    Finset.measurable_sum s (fun i hi => (hT i hi).const_mul _)
  apply Finset.measurable_sum s
  intro i hi
  have hB := heatVHEATDrift_translated_bank_measurable M n 9 t (x i) (g i)
  exact ((((hA.pow_const (k-1)).const_mul _).mul
    (Finset.measurable_sum Finset.univ (fun d _ =>
      ((hB d).const_mul _).add (((hB d).pow_const 2).const_mul _)))).mul
        ((hT i hi).add_const 4)).const_mul _

/-- The actual nine-shell source row is nonnegative and is bounded by the
complete polynomial majorant on the original bank event. -/
theorem heatVHEATDrift_source_ae_majorant {I : Type*}
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (hg : M.gamma ≤ gammaZero)
    (n : ℤ) (hpast : ∀ l<n,nativeInductionState M h l) (hstate : nativeInductionState M h n)
    (t : ℝ) (ht : t ≤ 1) (k : ℕ)
    (s : Finset I) (w : I → ℝ) (hw : ∀ i∈s,0 ≤ w i)
    (x : I → Vec 2) (g : I → (ℕ → ℝ) → ℝ) :
    ∀ᵐ z ∂nativeHeatRemainderJointLaw M,
      0 ≤ heatVHEATDriftSource s w M h n t k x g z ∧
      heatVHEATDriftSource s w M h n t k x g z ≤
        ∑ i∈s,w i*heatVHEATDriftFull k (heatVHEATDriftE9 M)
          (heatVHEATDriftKActual n) heatVHEATDriftCActual (3683/2500)
          (heatRefinedTranslatedRare M n 9 t (x i) z)
          (heatRefinedTraceAverage s w M n 9 t x g z)
          (heatRefinedTranslatedTrace M n 9 t (x i) (g i) z) := by
  have hb := heatVHEATDrift_bank_family_ae_le M h hM hg n 9 hpast t ht s x g
  have he : 0 ≤ heatVHEATDriftE9 M := by
    unfold heatVHEATDriftE9
    exact mul_nonneg (mul_nonneg (by norm_num) M.shellPrefix.gamma_pos.le) (Real.rpow_pos_of_pos (by norm_num) _).le
  filter_upwards [hb] with z hz
  have hT (i : I) : 0 ≤ heatRefinedTranslatedTrace M n 9 t (x i) (g i) z :=
    modelTraceObservable_nonneg _ _ _ M.nu_pos (Annealed.sigmaBar_characterization M n).1 _
  have hA : 0 ≤ heatRefinedTraceAverage s w M n 9 t x g z :=
    Finset.sum_nonneg (fun i hi => mul_nonneg (hw i hi) (hT i))
  constructor
  · apply Finset.sum_nonneg
    intro i hi
    apply mul_nonneg (hw i hi)
    apply mul_nonneg _ (by linarith [hT i])
    apply mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hA _))
    apply Finset.sum_nonneg
    intro d _
    have hv := (heatVHEATDrift_source_variance_le M h n hstate d).1
    have hc := heatVHEATDrift_source_coefficients_nonneg n d
    have hB := heatVHEATDrift_bank_nonneg M n 9 t (Cutoff.translateCutoffSample (x i) z.1) (g i z.2) d
    exact add_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hv) hc.1) hB)
      (mul_nonneg (mul_nonneg hv hc.2) (sq_nonneg _))
  · apply Finset.sum_le_sum
    intro i hi
    apply mul_le_mul_of_nonneg_left _ (hw i hi)
    have hs := heatVHEATDrift_shell_sum_le Finset.univ
      (heatVHEATDriftVariance M h n) (heatVHEATDriftKappa n) heatVHEATDriftMu
      (fun d => heatVHEATDriftBank M n 9 t (Cutoff.translateCutoffSample (x i) z.1) (g i z.2) d)
      (heatVHEATDriftE9 M) (3683/2500) (heatRefinedTranslatedRare M n 9 t (x i) z) he
      (fun d _ => heatVHEATDrift_source_variance_le M h n hstate d)
      (fun d _ => (heatVHEATDrift_source_coefficients_nonneg n d).1)
      (fun d _ => (heatVHEATDrift_source_coefficients_nonneg n d).2)
      (fun d _ => ⟨heatVHEATDrift_bank_nonneg M n 9 t _ (g i z.2) d,hz i hi d⟩)
    have hTp : 0 ≤ heatRefinedTranslatedTrace M n 9 t (x i) (g i) z+4 := by linarith [hT i]
    have hm := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hs
        (mul_nonneg (Nat.cast_nonneg k) (pow_nonneg hA (k-1)))) hTp
    refine hm.trans_eq ?_
    unfold heatVHEATDriftFull heatVHEATDriftKActual heatVHEATDriftCActual
    ring

end
end ASDExplicitGamma.Native
