module

public import ASDExplicitGamma.Native.OldSignedHistoryMoments

/-! Matrix and corrector moment payments from the same OLD maximum history. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open MeasureTheory
open scoped ENNReal
noncomputable section

/-- The matrix majorant retains its sharp `1+2C+sqrt(2C)` L2 coefficient. -/
theorem old_signed_matrix_majorant_L2 {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (H : Ω → ℝ) (C : ℝ)
    (hH : MemLp H 2 μ) (hH0 : ∀ ω,0≤H ω) (hC : 0≤C)
    (hcap : lpNorm H 2 μ ≤ C) :
    MemLp (fun ω => 1+2*H ω+Real.sqrt (2*H ω)) 2 μ ∧
    lpNorm (fun ω => 1+2*H ω+Real.sqrt (2*H ω)) 2 μ ≤
      1+2*C+Real.sqrt (2*C) := by
  have hmean := (old_signed_history_first_second_moments μ H C hH hH0 hC hcap).1
  have hi : Integrable H μ := hH.integrable (by norm_num)
  have hroot := old_signed_sqrt_L2 μ (fun ω => 2*H ω) (hi.const_mul 2)
    (fun ω => mul_nonneg (by norm_num) (hH0 ω))
  have hrootcap : lpNorm (fun ω => Real.sqrt (2*H ω)) 2 μ ≤ Real.sqrt (2*C) := by
    rw [hroot.2,integral_const_mul]
    exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hmean (by norm_num))
  have htwo : MemLp (fun ω => 2*H ω) 2 μ := hH.const_mul 2
  have hfirst : MemLp (fun ω => 1+2*H ω) 2 μ := (memLp_const (1:ℝ)).add htwo
  refine ⟨hfirst.add hroot.1,?_⟩
  have hnormtwo : lpNorm (fun ω => 2*H ω) 2 μ = 2*lpNorm H 2 μ := by
    change lpNorm ((2:ℝ) • H) 2 μ = _
    rw [lpNorm_const_smul]
    norm_num
  have hnormone : lpNorm (fun _ : Ω => (1:ℝ)) 2 μ = 1 := by
    rw [lpNorm_const' (by norm_num) (by norm_num)]
    simp only [norm_one,probReal_univ,Real.one_rpow,mul_one]
  have hfirstcap := lpNorm_add_le (g := fun ω => 2*H ω)
    (memLp_const (1:ℝ) : MemLp (fun _ : Ω => (1:ℝ)) 2 μ) (by norm_num)
  have htotal := lpNorm_add_le (g := fun ω => Real.sqrt (2*H ω)) hfirst (by norm_num)
  simp only [hnormone,hnormtwo] at hfirstcap
  exact htotal.trans (add_le_add (hfirstcap.trans
    (add_le_add le_rfl (mul_le_mul_of_nonneg_left hcap (by norm_num : (0:ℝ)≤2)))) hrootcap)

/-- The correlated corrector product is paid by the same C, without any
independence or extra fourth-moment assumption. -/
theorem old_signed_matrix_history_product {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (H : Ω → ℝ) (C : ℝ)
    (hH : MemLp H 2 μ) (hH0 : ∀ ω,0≤H ω) (hC : 0≤C)
    (hcap : lpNorm H 2 μ ≤ C) :
    Integrable (fun ω => (1+2*H ω+Real.sqrt (2*H ω))*H ω) μ ∧
    (∫ ω,(1+2*H ω+Real.sqrt (2*H ω))*H ω ∂μ) ≤
      (1+2*C+Real.sqrt (2*C))*C := by
  let F := fun ω => 1+2*H ω+Real.sqrt (2*H ω)
  have hF := old_signed_matrix_majorant_L2 μ H C hH hH0 hC hcap
  have hF0 (ω : Ω) : 0≤F ω := by
    exact add_nonneg (add_nonneg (by norm_num) (mul_nonneg (by norm_num) (hH0 ω)))
      (Real.sqrt_nonneg _)
  have hc : Real.HolderConjugate 2 2 := Real.holderConjugate_iff.mpr (by norm_num)
  have hh := integral_mul_le_Lp_mul_Lq_of_nonneg hc
    (Filter.Eventually.of_forall hF0) (Filter.Eventually.of_forall hH0)
    (show MemLp F (ENNReal.ofReal 2) μ by simpa only [ENNReal.ofReal_ofNat] using hF.1)
    (show MemLp H (ENNReal.ofReal 2) μ by simpa only [ENNReal.ofReal_ofNat] using hH)
  have hh' : (∫ ω,F ω*H ω ∂μ) ≤ lpNorm F 2 μ*lpNorm H 2 μ := by
    rw [old_signed_lpNorm_two μ F hF.1,old_signed_lpNorm_two μ H hH]
    simpa only [Real.rpow_ofNat,←Real.sqrt_eq_rpow] using hh
  exact ⟨hF.1.integrable_mul hH,hh'.trans
    (mul_le_mul hF.2 hcap lpNorm_nonneg (by positivity))⟩

end
end ASDExplicitGamma.Native
