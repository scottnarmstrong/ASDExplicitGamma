module

public import ASDExplicitGamma.Native.OldSignedSourceHistoryBudget
public import ASDExplicitGamma.Native.OldSignedNonnegativeSeriesIntegral
public import ASDExplicitGamma.Native.OldSignedDirectionalWeakProxy

/-! The complete actual inverse-weighted directional history, with honest
integrability and the annealed half-trace budget. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Inverse Variational Algsuperdiff.Section3
noncomputable section

/-- The actual directional history term, on the common OLD descendant tiling. -/
def oldSignedSourceDirectionalHistoryTerm (M : ABKModel 2) (n : ℤ) (U : TriadicCube 2) (t : ℝ)
    (e : Vec 2) (j : ℕ) (ω : Cutoff.CutoffSample 2) : ℝ :=
  inverseHistoryDiscount^(2*j)*
    (lemmaVInverseDepthMax U (oldSignedPartialFrameField M n 1 t ω) j*
      vecDot e (matVecMul (oldSignedPairedDepthMatrix U j
        (oldSignedPartialFrameField M n 1 t ω)) e))

/-- Every actual directional term is nonnegative. -/
theorem old_signed_source_directional_history_term_nonneg
    (M : ABKModel 2) (n : ℤ) (r : ℕ) (U : TriadicCube 2)
    (hU : U ∈ descendantsAtDepth (originCube 2 n) r) (t : ℝ) (e : Vec 2) (j : ℕ)
    (ω : Cutoff.CutoffSample 2) : 0 ≤ oldSignedSourceDirectionalHistoryTerm M n U t e j ω :=
  mul_nonneg (pow_nonneg inverse_history_discount_range.1.le _)
    (mul_nonneg (lemmaVInverseDepthMax_nonneg _ _ _)
      (old_signed_source_directional_nonneg_le M n r U hU t ω j e).1)

/-- The directional series converges samplewise by domination by the actual
complete trace proxy, before any expectation is taken. -/
theorem old_signed_source_directional_history_summable
    (M : ABKModel 2) (n : ℤ) (r : ℕ) (U : TriadicCube 2)
    (hU : U ∈ descendantsAtDepth (originCube 2 n) r) (t : ℝ)
    (e : Vec 2) (ω : Cutoff.CutoffSample 2) :
    Summable (fun j => oldSignedSourceDirectionalHistoryTerm M n U t e j ω) := by
  let a := oldSignedPartialFrameField M n 1 t ω
  have hEll := (responseFramePlanarCoefficientField_isElliptic
    (measurableSet_openCubeSet (originCube 2 n)) M.nu (Annealed.sigmaBar M n) M.nu_pos
    (Annealed.sigmaBar_characterization M n).1 (oldSignedPartialResponseCoefficient n 1 t ω)).mono
    (measurableSet_openCubeSet U) (openCubeSet_subset_of_mem_descendantsAtDepth hU)
  have hs := (old_signed_weak_trace_proxy_summable U a hEll).mul_right (vecNormSq e)
  apply Summable.of_nonneg_of_le
    (fun j => old_signed_source_directional_history_term_nonneg M n r U hU t e j ω) _ hs
  intro j
  have hh := mul_le_mul_of_nonneg_left
    (old_signed_source_directional_nonneg_le M n r U hU t ω j e).2
    (mul_nonneg (pow_nonneg inverse_history_discount_range.1.le (2*j))
      (lemmaVInverseDepthMax_nonneg U a j))
  rw [←old_signed_source_trace_depth M n r U hU t ω j] at hh
  exact (by simpa only [oldSignedSourceDirectionalHistoryTerm,mul_assoc,a] using hh)

/-- The complete inverse-weighted directional history has a finite expectation,
paid by half the deterministic trace history plus the full correlated reserve. -/
theorem old_signed_source_directional_history_payment
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (n : ℤ) (r : ℕ) (hr : r ≤ 5)
    (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth (originCube 2 n) r)
    (t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1)
    (hstates : ∀ l ≤ n,nativeInductionState M h l) (e : Vec 2) :
    Integrable (fun ω => ∑' j,oldSignedSourceDirectionalHistoryTerm M n U t e j ω)
      (Cutoff.cutoffSampleLaw M).toMeasure ∧
    (∫ ω,∑' j,oldSignedSourceDirectionalHistoryTerm M n U t e j ω
      ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
      (∑' j : ℕ,inverseHistoryDiscount^(2*j)*oldSignedSourceHistoryBudget M n U t j)*vecNormSq e := by
  have hf (j : ℕ) := old_signed_source_directional_payment M h hM hg n r hr U hU t ht hstates j e
  have hh := old_signed_nonnegative_series_integral (Cutoff.cutoffSampleLaw M).toMeasure
    (oldSignedSourceDirectionalHistoryTerm M n U t e)
    (fun j => (inverseHistoryDiscount^(2*j)*oldSignedSourceHistoryBudget M n U t j)*vecNormSq e)
    (fun j => (hf j).1.const_mul _)
    (old_signed_source_directional_history_term_nonneg M n r U hU t e)
    (old_signed_source_directional_history_summable M n r U hU t e)
    ((old_signed_source_history_budget_summable M h hM hg n r hr U
      (by simpa only [originCube] using scale_eq_sub_of_mem_descendantsAtDepth hU) t ht hstates).mul_right _) (by
      intro j
      unfold oldSignedSourceDirectionalHistoryTerm
      rw [integral_const_mul]
      have hle := mul_le_mul_of_nonneg_left (hf j).2
        (pow_nonneg inverse_history_discount_range.1.le (2*j))
      simpa only [oldSignedSourceHistoryBudget,mul_assoc] using hle)
  rw [tsum_mul_right] at hh
  exact hh

/-- The normalized physical directional proxy has the same complete
half-trace budget; no infinite extended history is converted to zero. -/
theorem old_signed_source_directional_proxy_payment
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (n : ℤ) (r : ℕ) (hr : r ≤ 5)
    (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth (originCube 2 n) r)
    (t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1)
    (hstates : ∀ l ≤ n,nativeInductionState M h l) (e : Vec 2) :
    Integrable (fun ω => oldSignedDirectionalProxy U
      (oldSignedPartialFrameField M n 1 t ω) e) (Cutoff.cutoffSampleLaw M).toMeasure ∧
    (∫ ω,oldSignedDirectionalProxy U (oldSignedPartialFrameField M n 1 t ω) e
      ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
      ((1-inverseHistoryDiscount^2)*
        ∑' j : ℕ,inverseHistoryDiscount^(2*j)*oldSignedSourceHistoryBudget M n U t j)*vecNormSq e := by
  have hh := old_signed_source_directional_history_payment M h hM hg n r hr U hU t ht hstates e
  have hc : 0 ≤ 1-inverseHistoryDiscount^2 :=
    sub_nonneg.mpr (pow_le_one₀ inverse_history_discount_range.1.le inverse_history_discount_range.2.le)
  have he (ω : Cutoff.CutoffSample 2) : oldSignedDirectionalProxy U
      (oldSignedPartialFrameField M n 1 t ω) e =
      (1-inverseHistoryDiscount^2)*∑' j,oldSignedSourceDirectionalHistoryTerm M n U t e j ω := by
    simp only [oldSignedDirectionalProxy,rawWeakTraceProxy,oldSignedSourceDirectionalHistoryTerm,mul_assoc]
  simp_rw [he]
  refine ⟨hh.1.const_mul _,?_⟩
  rw [integral_const_mul]
  exact (mul_le_mul_of_nonneg_left hh.2 hc).trans_eq (by ring)

end
end ASDExplicitGamma.Native
