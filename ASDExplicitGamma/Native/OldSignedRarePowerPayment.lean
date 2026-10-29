module

public import ASDExplicitGamma.Native.OldSignedRarePowerExpansion

/-! Complete correlated rare-power payment for the OLD panel. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open MeasureTheory Inverse
open scoped ENNReal
noncomputable section

/-- Every term of the fourth-order rare tail is integrable and paid by
Holder at orders 128 and 2 on the same probability space. -/
theorem old_signed_rare_power_tail_payment
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (R T : Ω → ℝ) (b ε C : ℝ) (k : ℕ) (hk : k ≤ 4)
    (hb : 0≤b) (hε : 0≤ε) (hC : 0≤C)
    (hR0 : ∀ ω,0≤R ω) (hT0 : ∀ ω,0≤T ω)
    (hRm : AEStronglyMeasurable R μ) (hTm : AEStronglyMeasurable T μ)
    (hR128 : eLpNorm R 128 μ ≤ ENNReal.ofReal ε)
    (hT2 : eLpNorm T 2 μ ≤ ENNReal.ofReal C) :
    Integrable (fun ω => rareExpansionTail b (R ω) (T ω) k) μ ∧
      (∫ ω,rareExpansionTail b (R ω) (T ω) k ∂μ) ≤ rareExpansionTail b ε C k := by
  have hi (i : ℕ) (hi : i ∈ Finset.Icc 1 k) :=
    old_signed_rare_trace_integrable_bound R T ε C i ((Finset.mem_Icc.mp hi).2.trans hk)
      hε hC hR0 hT0 hRm hTm hR128 hT2
  have hint (i : ℕ) (hi' : i ∈ Finset.Icc 1 k) : Integrable
      (fun ω => (Nat.choose k i:ℝ)*b^(k-i)*R ω^i*T ω) μ := by
    simpa only [mul_assoc] using (hi i hi').1.const_mul ((Nat.choose k i:ℝ)*b^(k-i))
  refine ⟨integrable_finsetSum _ hint,?_⟩
  unfold rareExpansionTail
  rw [integral_finsetSum _ hint]
  apply Finset.sum_le_sum
  intro i hi'
  have hc : 0≤(Nat.choose k i:ℝ)*b^(k-i) := mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hb _)
  calc
    _ = ((Nat.choose k i:ℝ)*b^(k-i))*(∫ ω,R ω^i*T ω ∂μ) := by
      rw [←integral_const_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun _ => by ring)
    _ ≤ ((Nat.choose k i:ℝ)*b^(k-i))*(ε^i*C) :=
      mul_le_mul_of_nonneg_left (hi i hi').2 hc
    _ = _ := by ring

/-- The source's literal coefficient thirteen pays every non-leading
binomial term through order four at the fixed history-bank reserve. -/
theorem old_signed_rare_power_thirteen (ε C : ℝ) (hε : 0≤ε)
    (hε1 : ε≤1/1000) (hC : 0≤C) (k : ℕ) (hk : k≤4) :
    rareExpansionTail (3683/2500) ε C k ≤ 13*ε*C := by
  have he2 : ε^2 ≤ ε*(1/1000) := by nlinarith only [mul_nonneg hε (sub_nonneg.mpr hε1)]
  have he3 : ε^3 ≤ ε*(1/1000)^2 := by
    calc
      _ = ε^2*ε := by ring
      _ ≤ (ε*(1/1000))*ε := mul_le_mul_of_nonneg_right he2 hε
      _ = ε^2*(1/1000) := by ring
      _ ≤ (ε*(1/1000))*(1/1000) := mul_le_mul_of_nonneg_right he2 (by norm_num)
      _ = _ := by ring
  have he4 : ε^4 ≤ ε*(1/1000)^3 := by
    calc
      _ = ε^3*ε := by ring
      _ ≤ (ε*(1/1000)^2)*ε := mul_le_mul_of_nonneg_right he3 hε
      _ = ε^2*(1/1000)^2 := by ring
      _ ≤ (ε*(1/1000))*(1/1000)^2 := mul_le_mul_of_nonneg_right he2 (by norm_num)
      _ = _ := by ring
  have hh : rareExpansionTail (3683/2500) ε 1 k ≤ 13*ε := by
    unfold rareExpansionTail
    interval_cases k <;> norm_num [Finset.sum_Icc_succ_top,Nat.choose] <;>
      nlinarith only [hε,he2,he3,he4]
  have heq : rareExpansionTail (3683/2500) ε C k =
      rareExpansionTail (3683/2500) ε 1 k*C := by
    unfold rareExpansionTail
    simp only [mul_one,Finset.sum_mul]
  rw [heq]
  exact mul_le_mul_of_nonneg_right hh hC

/-- A measurable nonnegative history below its bank split inherits genuine
integrability and the complete correlated rare bill, including order four. -/
theorem old_signed_rare_history_power_payment
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (B R T : Ω → ℝ) (b ε C : ℝ) (k : ℕ) (hk : k≤4)
    (hb : 0≤b) (hε : 0≤ε) (hC : 0≤C)
    (hB0 : ∀ ω,0≤B ω) (hR0 : ∀ ω,0≤R ω) (hT0 : ∀ ω,0≤T ω)
    (hBm : AEStronglyMeasurable B μ) (hRm : AEStronglyMeasurable R μ)
    (hTm : AEStronglyMeasurable T μ)
    (hbound : ∀ᵐ ω ∂μ,B ω≤b+R ω)
    (hR128 : eLpNorm R 128 μ ≤ ENNReal.ofReal ε)
    (hT2 : eLpNorm T 2 μ ≤ ENNReal.ofReal C) :
    Integrable (fun ω => B ω^k*T ω) μ ∧
      (∫ ω,B ω^k*T ω ∂μ) ≤ b^k*(∫ ω,T ω ∂μ)+rareExpansionTail b ε C k := by
  have ht := old_signed_rare_power_tail_payment R T b ε C k hk hb hε hC hR0 hT0
    hRm hTm hR128 hT2
  have hT : Integrable T μ := by
    simpa only [pow_zero,one_mul] using
      (old_signed_rare_trace_integrable_bound R T ε C 0 (by omega) hε hC hR0 hT0
        hRm hTm hR128 hT2).1
  have hmajor : Integrable (fun ω => b^k*T ω+rareExpansionTail b (R ω) (T ω) k) μ :=
    (hT.const_mul _).add ht.1
  have hpoint : ∀ᵐ ω ∂μ,B ω^k*T ω≤b^k*T ω+rareExpansionTail b (R ω) (T ω) k := by
    filter_upwards [hbound] with ω hω
    rw [←old_signed_rare_power_binomial b (R ω) (T ω) k hk]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (hB0 ω) hω k) (hT0 ω)
  have hi : Integrable (fun ω => B ω^k*T ω) μ := hmajor.mono_nonneg
    ((hBm.pow k).mul hTm) (Filter.Eventually.of_forall
      (fun ω => mul_nonneg (pow_nonneg (hB0 ω) k) (hT0 ω))) hpoint
  refine ⟨hi,?_⟩
  calc
    _ ≤ ∫ ω,b^k*T ω+rareExpansionTail b (R ω) (T ω) k ∂μ :=
      integral_mono_ae hi hmajor hpoint
    _ = b^k*(∫ ω,T ω ∂μ)+(∫ ω,rareExpansionTail b (R ω) (T ω) k ∂μ) := by
      rw [integral_add (hT.const_mul _) ht.1,integral_const_mul]
    _ ≤ _ := add_le_add le_rfl ht.2

end
end ASDExplicitGamma.Native
