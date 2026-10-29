module

public import ASDExplicitGamma.Native.ParentBoundaryCommonSingletonBank
public import ASDExplicitGamma.Native.ParentBoundaryCommonFullBank
public import ASDExplicitGamma.Native.ParentBoundaryRareMixedHolder

/-! Actual mean-generator bank/full-response products in every protected source frame. -/

@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Gaussian Inverse Main Model Triadic Algsuperdiff.Section3
open scoped ENNReal
noncomputable section

private theorem parent_mean_const_one_norm
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ℝ≥0∞) (hp0 : p ≠ 0) (hptop : p ≠ ⊤) : eLpNorm (fun _ : Ω => (1:ℝ)) p μ=1 := by
  rw [eLpNorm_const' _ hp0 hptop]
  simp only [enorm_one,measure_univ,ENNReal.one_rpow,mul_one]

private theorem parent_mean_bank_product_holder
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P U : Ω → ℝ) (hP0 : ∀ ω,0 ≤ P ω) (hU0 : ∀ ω,0 ≤ U ω)
    (hP128 : MemLp P 128 μ) (hU128 : MemLp U 128 μ)
    (b F : ℝ) (hb : 0 ≤ b) (hF : 0 ≤ F)
    (hPcap : eLpNorm P 128 μ ≤ ENNReal.ofReal b) (hUcap : eLpNorm U 128 μ ≤ ENNReal.ofReal F)
    (j : Fin 2) :
    Integrable (fun ω => P ω^(j.val+1)*U ω) μ ∧
      (∫ ω,P ω^(j.val+1)*U ω ∂μ) ≤ b^(j.val+1)*F := by
  have hm := parent_boundary_rare_mixed_product_holder μ (fun _ => 1) U P (fun _ => by norm_num)
    hU0 hP0 (memLp_const 1) hU128 hP128 b F hb hF hPcap hUcap j
  rw [parent_mean_const_one_norm μ 20 (by norm_num) (by norm_num)] at hm
  simpa only [one_pow,one_mul,ENNReal.toReal_one] using hm

/-- The ACTUAL original protected singleton bank has its first mean and
its correlated P*F/P^2*F source bounds. Every input is discharged from the
model, strict past and the actual full-response producer, with no norm cap
or independence premise. -/
theorem parent_boundary_mean_bank_products
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (hg : M.gamma ≤ gammaZero)
    (Q : TriadicCube 2) (m n : ℤ) (hQm : Q.scale ≤ m) (hgap : m-Q.scale ≤ 5) (hmn : m ≤ n)
    (height depth : ℕ) (hscale : Q.scale=n-(depth:ℤ))
    (hpast : ∀ k<n,nativeInductionState M h k) (t : ℝ) (ht : t ≤ 1) :
    let P := parentBoundaryCommonSingletonHistory M Q m n height t
    let U := nativeSourceFullResponseTrace M Q n (n+(height:ℤ)) (fun _ => Real.sqrt t)
    let μ := (Cutoff.cutoffSampleLaw M).toMeasure
    Integrable P μ ∧ (∫ ω,P ω ∂μ) ≤ (3683/2500:ℝ) ∧
      ∀ j : Fin 2,Integrable (fun ω => P ω^(j.val+1)*U ω) μ ∧
        (∫ ω,P ω^(j.val+1)*U ω ∂μ) ≤ (3683/2500:ℝ)^(j.val+1)*parentBoundaryBandTraceCap M height depth := by
  intro P U μ
  have hP0 (ω) : 0 ≤ P ω := ENNReal.toReal_nonneg
  have hU0 (ω) : 0 ≤ U ω := by
    dsimp only [U]
    rw [parent_boundary_common_physical_full_eq]
    exact add_nonneg (parent_boundary_band_trace_nonneg M n height t Q ω) (by norm_num)
  have hPcap := parent_boundary_common_singleton_history_L128 M h hM hg Q m n hQm hgap hmn height hpast t ht
  have hP128 : MemLp P 128 μ := hPcap.trans_lt ENNReal.ofReal_lt_top
  have hU128 := parent_boundary_common_physical_full_L128 M h hM hg Q n height depth hscale hpast t ht
  have hone : eLpNorm (fun _ : Cutoff.CutoffSample 2 => (1:ℝ)) 128 μ ≤ ENNReal.ofReal 1 := by
    rw [parent_mean_const_one_norm μ 128 (by norm_num) (by norm_num)]
    norm_num
  have hfirst := parent_mean_bank_product_holder μ P (fun _ => 1) hP0 (fun _ => by norm_num)
    hP128 (memLp_const 1) (3683/2500) 1 (by norm_num) (by norm_num) hPcap hone ⟨0,by decide⟩
  refine ⟨?_,?_,?_⟩
  · simpa only [Nat.zero_add,pow_one,mul_one] using hfirst.1
  · simpa only [Nat.zero_add,pow_one,mul_one] using hfirst.2
  · intro j
    exact parent_mean_bank_product_holder μ P U hP0 hU0 hP128 hU128.1 (3683/2500) _ (by norm_num)
      (parent_boundary_band_trace_cap_nonneg M height depth) hPcap hU128.2 j

end
end ASDExplicitGamma.Native
