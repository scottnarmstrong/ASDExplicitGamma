module

public import ASDExplicitGamma.Native.HeatConfiguredRareMoments
public import ASDExplicitGamma.Native.HeatIndividualBillRounding

/-! Complete OLD split integration into a selected individual matrix row. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Numerics.Native MeasureTheory
open scoped ENNReal
noncomputable section

/-- Every ordinary moment through degree20 is integrable under the supplied
finite OLD L20 cap, including the augmented constant coordinate. -/
theorem heat_individual_power_integrable
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : Ω → ℝ) (hT : AEStronglyMeasurable T μ) (hT0 : ∀ z,0 ≤ T z)
    (X : ℝ) (h20 : eLpNorm' T 20 μ ≤ ENNReal.ofReal X)
    (k : ℕ) (hk : k ≤ 20) : Integrable (fun z => T z^k) μ := by
  have hn : eLpNorm T 20 μ = eLpNorm' T 20 μ := by
    simpa only [ENNReal.toReal_ofNat] using
      eLpNorm_eq_eLpNorm' (p:=(20:ℝ≥0∞)) (by norm_num) (by norm_num) hT
  have hm : MemLp T 20 μ := memLp_iff.mpr ((hn.le.trans h20).trans_lt ENNReal.ofReal_lt_top)
  have hm' : MemLp T (k:ℝ≥0∞) μ := hm.mono_exponent (by exact_mod_cast hk)
  simpa only [Real.norm_eq_abs,abs_of_nonneg (hT0 _)] using hm'.integrable_norm_pow'

/-- The full OLD source bill is paid by the selected rounded individual row.
Only physical trace/reserve profiles are inputs; all rare Holder estimates,
306 root certificates, coefficient rounding and integrability are proved here. -/
theorem heat_configured_individual_bill_integral_le
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (index : Fin 153) (R T : Ω → ℝ)
    (hR : AEStronglyMeasurable R μ) (hT : AEStronglyMeasurable T μ)
    (hR0 : ∀ z,0 ≤ R z) (hT0 : ∀ z,0 ≤ T z)
    (k : ℕ) (hk : 1 ≤ k) (hk20 : k ≤ 20)
    (hRc : eLpNorm' R 128 μ ≤ ENNReal.ofReal (nativeEps:ℝ))
    (h20 : eLpNorm' T 20 μ ≤ ENNReal.ofReal ((nativeOld (nativeConfiguredSystem index).gap).x:ℝ))
    (h128 : eLpNorm' T 128 μ ≤ ENNReal.ofReal ((nativeOld (nativeConfiguredSystem index).gap).f:ℝ)) :
    let height := (nativeConfiguredSystem index).gap
    let old := nativeOld height
    let c : ℝ := 1975/1000+2*((k-1:ℕ):ℝ)*(1565/1000)
    let d : ℝ := 2*(height:ℝ)+4*((k:ℝ)-1)*((height:ℝ)+521/1000)
    let row := nativeIndividualRow height k old
    Integrable (fun z => heatIndividualSourceBill k old.e d (521/1000) c nativeB (T z) (R z)) μ ∧
    (∫ z,heatIndividualSourceBill k old.e d (521/1000) c nativeB (T z) (R z) ∂μ) ≤
      (nativeA:ℝ)*(row.1:ℝ)*(∫ z,T z^(k-1) ∂μ)+
        (row.2.1:ℝ)*(∫ z,T z^k ∂μ)+(nativeA:ℝ)^k*(row.2.2:ℝ) := by
  let height := (nativeConfiguredSystem index).gap
  let old := nativeOld height
  let c : ℝ := 1975/1000+2*((k-1:ℕ):ℝ)*(1565/1000)
  let d : ℝ := 2*(height:ℝ)+4*((k:ℝ)-1)*((height:ℝ)+521/1000)
  have he := (heat_configured_individual_old_valid index).1
  have hkR : (1:ℝ) ≤ k := by exact_mod_cast hk
  have hkm : 0 ≤ (k:ℝ)-1 := sub_nonneg.mpr hkR
  have hprev := heat_individual_power_integrable μ T hT hT0 old.x h20 (k-1) (by omega)
  have hcur := heat_individual_power_integrable μ T hT hT0 old.x h20 k hk20
  have hrare := heat_configured_individual_rare_moment μ index R T hR hT hR0 hT0
  have h1p := hrare (0:Fin 2) (k-1) (by omega) hRc h20 h128
  have h1 := hrare (0:Fin 2) k hk20 hRc h20 h128
  have h2p := hrare (1:Fin 2) (k-1) (by omega) hRc h20 h128
  have h2 := hrare (1:Fin 2) k hk20 hRc h20 h128
  norm_num only [Fin.val_zero,Fin.val_one,pow_one] at h1p h1 h2p h2
  have hb := heat_individual_source_bill_integral_le μ k old.e d (521/1000) c nativeB T R
    (by exact_mod_cast he) (by dsimp [d]; positivity) (by norm_num)
    (by dsimp [c]; positivity) (by norm_num [nativeB]) hprev hcur _ _ _ _ h1p h1 h2p h2
  refine ⟨hb.1,hb.2.trans ?_⟩
  have hr := heat_individual_bill_le_rounded_row height k old
    (∫ z,T z^(k-1) ∂μ) (∫ z,T z^k ∂μ)
    (integral_nonneg fun z => pow_nonneg (hT0 z) _)
    (integral_nonneg fun z => pow_nonneg (hT0 z) _)
  dsimp only at hr
  push_cast at hr
  exact hr

end
end ASDExplicitGamma.Native
