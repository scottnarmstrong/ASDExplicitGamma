module

public import ASDExplicitGamma.Native.HeatIndividualSplit

/-! The complete individual rare bill after taking expectations. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open MeasureTheory
noncomputable section

/-- Integrate the literal split bill; no rare monomial disappears. -/
theorem heat_individual_source_bill_integral {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (k : ℕ) (e d κ c b : ℝ) (T R : Ω → ℝ)
    (hprev : Integrable (fun z => T z^(k-1)) μ)
    (hcur : Integrable (fun z => T z^k) μ)
    (h1p : Integrable (fun z => R z*T z^(k-1)) μ)
    (h1 : Integrable (fun z => R z*T z^k) μ)
    (h2p : Integrable (fun z => R z^2*T z^(k-1)) μ)
    (h2 : Integrable (fun z => R z^2*T z^k) μ) :
    Integrable (fun z => heatIndividualSourceBill k e d κ c b (T z) (R z)) μ ∧
    (∫ z,heatIndividualSourceBill k e d κ c b (T z) (R z) ∂μ) =
      (k:ℝ)*e*((d*b+4*(2*κ*b+c*b^2))*(∫ z,T z^(k-1) ∂μ)+
        (2*κ*b+c*b^2)*(∫ z,T z^k ∂μ)+d*(∫ z,R z*T z^(k-1) ∂μ)+
        (2*κ+2*b*c)*(4*(∫ z,R z*T z^(k-1) ∂μ)+(∫ z,R z*T z^k ∂μ))+
        c*(4*(∫ z,R z^2*T z^(k-1) ∂μ)+(∫ z,R z^2*T z^k ∂μ))) := by
  have ha := hprev.const_mul (d*b+4*(2*κ*b+c*b^2))
  have hb := hcur.const_mul (2*κ*b+c*b^2)
  have hd := h1p.const_mul d
  have hr1 := ((h1p.const_mul 4).add h1).const_mul (2*κ+2*b*c)
  have hr2 := ((h2p.const_mul 4).add h2).const_mul c
  refine ⟨((((ha.add hb).add hd).add hr1).add hr2).const_mul ((k:ℝ)*e),?_⟩
  have hab := integral_add ha hb
  have habd := integral_add (ha.add hb) hd
  have habdr := integral_add ((ha.add hb).add hd) hr1
  have hall := integral_add (((ha.add hb).add hd).add hr1) hr2
  have hrare1 := integral_add (h1p.const_mul 4) h1
  have hrare2 := integral_add (h2p.const_mul 4) h2
  simp only [Pi.add_apply] at hab habd habdr hall hrare1 hrare2
  simp only [heatIndividualSourceBill,integral_const_mul]
  rw [hall,habdr,habd,hab]
  simp only [integral_const_mul]
  rw [hrare1,hrare2]
  simp only [integral_const_mul]

/-- Four separately certified rare moments pay the entire source error.
The two ordinary moments remain as the current and predecessor coordinates. -/
theorem heat_individual_source_bill_integral_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (k : ℕ) (e d κ c b : ℝ) (T R : Ω → ℝ)
    (he : 0 ≤ e) (hd : 0 ≤ d) (hκ : 0 ≤ κ) (hc : 0 ≤ c) (hb : 0 ≤ b)
    (hprev : Integrable (fun z => T z^(k-1)) μ)
    (hcur : Integrable (fun z => T z^k) μ)
    (J1p J1 J2p J2 : ℝ)
    (h1p : Integrable (fun z => R z*T z^(k-1)) μ ∧ (∫ z,R z*T z^(k-1) ∂μ) ≤ J1p)
    (h1 : Integrable (fun z => R z*T z^k) μ ∧ (∫ z,R z*T z^k ∂μ) ≤ J1)
    (h2p : Integrable (fun z => R z^2*T z^(k-1)) μ ∧ (∫ z,R z^2*T z^(k-1) ∂μ) ≤ J2p)
    (h2 : Integrable (fun z => R z^2*T z^k) μ ∧ (∫ z,R z^2*T z^k ∂μ) ≤ J2) :
    Integrable (fun z => heatIndividualSourceBill k e d κ c b (T z) (R z)) μ ∧
    (∫ z,heatIndividualSourceBill k e d κ c b (T z) (R z) ∂μ) ≤
      (k:ℝ)*e*((d*b+4*(2*κ*b+c*b^2))*(∫ z,T z^(k-1) ∂μ)+
        (2*κ*b+c*b^2)*(∫ z,T z^k ∂μ)+d*J1p+
        (2*κ+2*b*c)*(4*J1p+J1)+c*(4*J2p+J2)) := by
  obtain ⟨hI,hEq⟩ := heat_individual_source_bill_integral μ k e d κ c b T R
    hprev hcur h1p.1 h1.1 h2p.1 h2.1
  refine ⟨hI,?_⟩
  rw [hEq]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply add_le_add
  · apply add_le_add
    · exact add_le_add le_rfl (mul_le_mul_of_nonneg_left h1p.2 hd)
    · exact mul_le_mul_of_nonneg_left
        (add_le_add (mul_le_mul_of_nonneg_left h1p.2 (by norm_num)) h1.2) (by positivity)
  · exact mul_le_mul_of_nonneg_left
      (add_le_add (mul_le_mul_of_nonneg_left h2p.2 (by norm_num)) h2.2) hc

end
end ASDExplicitGamma.Native
