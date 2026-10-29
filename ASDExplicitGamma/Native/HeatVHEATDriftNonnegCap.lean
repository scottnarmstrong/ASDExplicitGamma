module

public import ASDExplicitGamma.Native.HeatVHEATDriftZeroCap
public import ASDExplicitGamma.Native.HeatVHEATDriftAverage

/-! Actual norm caps may vanish: no positive padding is inserted in X. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open MeasureTheory
open scoped ENNReal
noncomputable section

/-- The complete first-line J payment for every nonnegative actual X. -/
theorem heatVHEATDrift_rare_integral_nonneg_cap
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (R A T : Ω → ℝ)
    (hR : AEStronglyMeasurable R μ) (hA : AEStronglyMeasurable A μ) (hT : AEStronglyMeasurable T μ)
    (hR0 : ∀ ω,0 ≤ R ω) (hA0 : ∀ ω,0 ≤ A ω) (hT0 : ∀ ω,0 ≤ T ω)
    (k : ℕ) (hk : 1 ≤ k) (hk20 : k ≤ 20)
    (e_h K C b eps X F : ℝ) (heh : 0 ≤ e_h) (hK : 0 ≤ K) (hC : 0 ≤ C) (hb : 0 ≤ b)
    (heps : 0 ≤ eps) (hX : 0 ≤ X) (hF : 0 ≤ F)
    (hR128 : eLpNorm R 128 μ ≤ ENNReal.ofReal eps)
    (hA20 : eLpNorm A 20 μ ≤ ENNReal.ofReal X) (hT20 : eLpNorm T 20 μ ≤ ENNReal.ofReal X)
    (hA128 : eLpNorm A 128 μ ≤ ENNReal.ofReal F) (hT128 : eLpNorm T 128 μ ≤ ENNReal.ofReal F) :
    Integrable (fun ω => heatVHEATDriftRare k e_h K C b (R ω) (A ω) (T ω)) μ ∧
      (∫ ω,heatVHEATDriftRare k e_h K C b (R ω) (A ω) (T ω) ∂μ) ≤
        heatVHEATDriftFirstLine k e_h K C b eps X F  := by
  by_cases hpos : 0 < X
  · exact heatVHEATDrift_rare_integral μ R A T hR hA hT hR0 hA0 hT0
      k hk hk20 e_h K C b eps X F heh hK hC hb heps hpos hF hR128 hA20 hT20 hA128 hT128
  · have hx : X=0 := le_antisymm (le_of_not_gt hpos) hX
    subst X
    have hAzero : A =ᵐ[μ] 0 := (eLpNorm_eq_zero_iff (by norm_num : (20:ℝ≥0∞)≠0)).mp
      (le_antisymm (by simpa only [ENNReal.ofReal_zero] using hA20) bot_le)
    have hTzero : T =ᵐ[μ] 0 := (eLpNorm_eq_zero_iff (by norm_num : (20:ℝ≥0∞)≠0)).mp
      (le_antisymm (by simpa only [ENNReal.ofReal_zero] using hT20) bot_le)
    exact heatVHEATDrift_rare_zero_cap μ R A T hR hR0 hAzero hTzero k hk
      e_h K C b eps F heh hK hC hb heps hF hR128

/-- Each descendant keeps its own correlated rare factor. A normalized
finite average pays exactly one E-first-line, without a population maximum. -/
theorem heatVHEATDrift_rare_average_nonneg_cap
    {Ω I : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (s : Finset I) (w : I → ℝ) (hw : ∀ i∈s,0 ≤ w i) (hw1 : ∑ i∈s,w i=1)
    (R T : I → Ω → ℝ) (A : Ω → ℝ)
    (hR : ∀ i∈s,AEStronglyMeasurable (R i) μ) (hT : ∀ i∈s,AEStronglyMeasurable (T i) μ)
    (hA : AEStronglyMeasurable A μ)
    (hR0 : ∀ i∈s,∀ ω,0 ≤ R i ω) (hT0 : ∀ i∈s,∀ ω,0 ≤ T i ω) (hA0 : ∀ ω,0 ≤ A ω)
    (k : ℕ) (hk : 1 ≤ k) (hk20 : k ≤ 20)
    (e_h K C b eps X F : ℝ) (heh : 0 ≤ e_h) (hK : 0 ≤ K) (hC : 0 ≤ C) (hb : 0 ≤ b)
    (heps : 0 ≤ eps) (hX : 0 ≤ X) (hF : 0 ≤ F)
    (hR128 : ∀ i∈s,eLpNorm (R i) 128 μ ≤ ENNReal.ofReal eps)
    (hA20 : eLpNorm A 20 μ ≤ ENNReal.ofReal X)
    (hT20 : ∀ i∈s,eLpNorm (T i) 20 μ ≤ ENNReal.ofReal X)
    (hA128 : eLpNorm A 128 μ ≤ ENNReal.ofReal F)
    (hT128 : ∀ i∈s,eLpNorm (T i) 128 μ ≤ ENNReal.ofReal F) :
    Integrable (fun ω => ∑ i∈s,w i*heatVHEATDriftRare k e_h K C b (R i ω) (A ω) (T i ω)) μ ∧
    (∫ ω,∑ i∈s,w i*heatVHEATDriftRare k e_h K C b (R i ω) (A ω) (T i ω) ∂μ) ≤
      heatVHEATDriftFirstLine k e_h K C b eps X F := by
  have hi (i : I) (hi : i∈s) := heatVHEATDrift_rare_integral_nonneg_cap μ (R i) A (T i)
    (hR i hi) hA (hT i hi) (hR0 i hi) hA0 (hT0 i hi) k hk hk20
    e_h K C b eps X F heh hK hC hb heps hX hF (hR128 i hi) hA20 (hT20 i hi) hA128 (hT128 i hi)
  refine ⟨integrable_finsetSum s (fun i hi' => (hi i hi').1.const_mul (w i)),?_⟩
  rw [integral_finsetSum s (fun i hi' => (hi i hi').1.const_mul (w i))]
  simp_rw [integral_const_mul]
  calc
    _ ≤ ∑ i∈s,w i*heatVHEATDriftFirstLine k e_h K C b eps X F :=
      Finset.sum_le_sum (fun i hi' => mul_le_mul_of_nonneg_left (hi i hi').2 (hw i hi'))
    _ = _ := by rw [←Finset.sum_mul,hw1,one_mul]


end
end ASDExplicitGamma.Native
