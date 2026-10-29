module

public import ASDExplicitGamma.Native.HeatConfiguredBillIntegral

/-! Physical source-row integration into the selected individual coefficients. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Numerics.Native MeasureTheory
open scoped ENNReal
noncomputable section

/-- Consumer of the individual-cell source identity. The inverse-trace bank
and rare split are paid before integrating; the complete resulting bill is
converted to the rounded configured coefficients internally. This analysis
interface still requires the actual source law and its OLD trace profiles. -/
theorem heat_individual_generator_integral_le_source_row
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (index : Fin 153) (R T P D G : Ω → ℝ)
    (hR : AEStronglyMeasurable R μ) (hT : AEStronglyMeasurable T μ)
    (hR0 : ∀ z,0 ≤ R z) (hT0 : ∀ z,0 ≤ T z)
    (k : ℕ) (hk : 1 ≤ k) (hk20 : k ≤ 20)
    (hRc : eLpNorm' R 128 μ ≤ ENNReal.ofReal (nativeEps:ℝ))
    (h20 : eLpNorm' T 20 μ ≤ ENNReal.ofReal ((nativeOld (nativeConfiguredSystem index).gap).x:ℝ))
    (h128 : eLpNorm' T 128 μ ≤ ENNReal.ofReal ((nativeOld (nativeConfiguredSystem index).gap).f:ℝ))
    (hG : Integrable G μ)
    (hbank : ∀ᵐ z ∂μ,0 ≤ P z ∧ D z ≤ 2*P z ∧ P z ≤ (nativeB:ℝ)+R z)
    (hsource : ∀ᵐ z ∂μ,G z ≤
      (k:ℝ)*T z^(k-1)*((nativeOld (nativeConfiguredSystem index).gap).e:ℝ)*
        ((((2*(k:ℝ)-1)*((nativeConfiguredSystem index).gap:ℝ)+2*((k:ℝ)-1)*(521/1000))*D z)+
          2*(521/1000)*(P z*(T z+4))+
          (1975/1000+2*((k-1:ℕ):ℝ)*(1565/1000))*(P z^2*(T z+4)))) :
    let row := nativeIndividualRow (nativeConfiguredSystem index).gap k
      (nativeOld (nativeConfiguredSystem index).gap)
    (∫ z,G z ∂μ) ≤ (row.2.1:ℝ)*(∫ z,T z^k ∂μ)+
      (3/50:ℝ)*(row.1:ℝ)*(∫ z,T z^(k-1) ∂μ)+(3/50:ℝ)^k*(row.2.2:ℝ) := by
  let height := (nativeConfiguredSystem index).gap
  let old := nativeOld height
  let a : ℝ := (2*(k:ℝ)-1)*(height:ℝ)+2*((k:ℝ)-1)*(521/1000)
  let c : ℝ := 1975/1000+2*((k-1:ℕ):ℝ)*(1565/1000)
  let d : ℝ := 2*(height:ℝ)+4*((k:ℝ)-1)*((height:ℝ)+521/1000)
  have hkR : (1:ℝ) ≤ k := by exact_mod_cast hk
  have hkm : 0 ≤ (k:ℝ)-1 := sub_nonneg.mpr hkR
  have h2k : 0 ≤ 2*(k:ℝ)-1 := by linarith
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hd : 2*a=d := by dsimp [a,d]; ring
  have he : 0 ≤ (old.e:ℝ) := by exact_mod_cast (heat_configured_individual_old_valid index).1
  have hbill := heat_configured_individual_bill_integral_le μ index R T hR hT hR0 hT0
    k hk hk20 hRc h20 h128
  have hpoint : ∀ᵐ z ∂μ,G z ≤ heatIndividualSourceBill k old.e d (521/1000) c nativeB (T z) (R z) := by
    filter_upwards [hsource,hbank] with z hs hb
    have hp := heat_individual_source_le_bill k hk old.e a (521/1000) c nativeB
      (T z) (P z) (D z) (R z) he ha (by norm_num) (by dsimp [c]; positivity)
      (hT0 z) hb.1 hb.2.1 hb.2.2
    rw [hd] at hp
    apply hs.trans
    convert hp using 1 <;> ring
  have hI := (integral_mono_ae hG hbill.1 hpoint).trans hbill.2
  dsimp only at hI ⊢
  simpa only [nativeA, Rat.cast_div,Rat.cast_ofNat,add_comm,add_left_comm,add_assoc] using hI

end
end ASDExplicitGamma.Native
