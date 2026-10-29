module

public import ASDExplicitGamma.Native.HeatVHEATDriftFullIntegral
public import ASDExplicitGamma.Native.HeatVHEATDriftNonnegCap
public import ASDExplicitGamma.Native.HeatVHEATDriftShells

/-! Complete drift expectation: exact leading moments plus the correlated
first-line VHEAT bill, with actual finite shell sums retained. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open MeasureTheory
open scoped ENNReal
noncomputable section

/-- The complete normalized drift expectation keeps the actual average's
moments in the leading term. Every remaining monomial is paid by the exact
J first line; no child independence or population maximum is introduced. -/
theorem heatVHEATDrift_full_average_integral_nonneg_cap
    {Ω I : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (s : Finset I) (w : I → ℝ) (hw : ∀ i∈s,0 ≤ w i) (hw1 : ∑ i∈s,w i=1)
    (R T : I → Ω → ℝ) (A : Ω → ℝ) (havg : ∀ ω,A ω=∑ i∈s,w i*T i ω)
    (hR : ∀ i∈s,AEStronglyMeasurable (R i) μ) (hT : ∀ i∈s,AEStronglyMeasurable (T i) μ)
    (hA : AEStronglyMeasurable A μ)
    (hR0 : ∀ i∈s,∀ ω,0 ≤ R i ω) (hT0 : ∀ i∈s,∀ ω,0 ≤ T i ω) (hA0 : ∀ ω,0 ≤ A ω)
    (k : ℕ) (hk : 1 ≤ k) (hk20 : k ≤ 20)
    (e K C b eps X F : ℝ) (he : 0 ≤ e) (hK : 0 ≤ K) (hC : 0 ≤ C) (hb : 0 ≤ b)
    (heps : 0 ≤ eps) (hX : 0 ≤ X) (hF : 0 ≤ F)
    (hR128 : ∀ i∈s,eLpNorm (R i) 128 μ ≤ ENNReal.ofReal eps)
    (hA20 : eLpNorm A 20 μ ≤ ENNReal.ofReal X)
    (hT20 : ∀ i∈s,eLpNorm (T i) 20 μ ≤ ENNReal.ofReal X)
    (hA128 : eLpNorm A 128 μ ≤ ENNReal.ofReal F)
    (hT128 : ∀ i∈s,eLpNorm (T i) 128 μ ≤ ENNReal.ofReal F) :
    Integrable (fun ω => ∑ i∈s,w i*heatVHEATDriftFull k e K C b (R i ω) (A ω) (T i ω)) μ ∧
    (∫ ω,∑ i∈s,w i*heatVHEATDriftFull k e K C b (R i ω) (A ω) (T i ω) ∂μ) ≤
      (k:ℝ)*e*(2*K*b+C*b^2)*((∫ ω,A ω^k ∂μ)+4*(∫ ω,A ω^(k-1) ∂μ))+
        heatVHEATDriftFirstLine k e K C b eps X F := by
  let c := (k:ℝ)*e*(2*K*b+C*b^2)
  let rare := fun ω => ∑ i∈s,w i*heatVHEATDriftRare k e K C b (R i ω) (A ω) (T i ω)
  have hr := heatVHEATDrift_rare_average_nonneg_cap μ s w hw hw1 R T A hR hT hA hR0 hT0 hA0
    k hk hk20 e K C b eps X F he hK hC hb heps hX hF hR128 hA20 hT20 hA128 hT128
  have hpow (l : ℕ) (hl : l ≤ 20) : Integrable (fun ω => A ω^l) μ := by
    simpa only [pow_zero,mul_one] using (nativeHeat_trace_mixed_product μ A A hA hA hA0 hA0
      X X hX hX hA20 hA20 l 0 (by omega)).1
  have hlead : Integrable (fun ω => c*(A ω^k+4*A ω^(k-1))) μ :=
    ((hpow k hk20).add ((hpow (k-1) (by omega)).const_mul 4)).const_mul c
  have hsplit : (fun ω => ∑ i∈s,w i*heatVHEATDriftFull k e K C b (R i ω) (A ω) (T i ω))=
      (fun ω => c*(A ω^k+4*A ω^(k-1))+rare ω) := by
    funext ω
    have hid := heatVHEATDrift_leading_average_identity s w (fun i => T i ω) k hk
      (e*(2*K*b+C*b^2))
    rw [←havg ω,hw1,mul_one] at hid
    calc
      _ = (∑ i∈s,w i*((k:ℝ)*(e*(2*K*b+C*b^2))*A ω^(k-1)*(T i ω+4)))+rare ω := by
        rw [←Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        dsimp only [heatVHEATDriftFull,heatVHEATDriftRare]
        ring
      _ = _ := by rw [hid]; dsimp only [c]; ring
  rw [hsplit]
  refine ⟨hlead.add hr.1,?_⟩
  rw [integral_add hlead hr.1,integral_const_mul,
    integral_add (hpow k hk20) ((hpow (k-1) (by omega)).const_mul 4),integral_const_mul]
  exact add_le_add le_rfl hr.2

end
end ASDExplicitGamma.Native
