module

public import ASDExplicitGamma.Native.HeatRemainderControlErrorIntegrals

/-! Complete correlated first-line VHEAT payments. These generic analytic
lemmas retain their displayed norm data; actual source exports discharge it. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open MeasureTheory
open scoped ENNReal
noncomputable section

/-- The complete rare drift/mixed integrand, before any expectation or
spatial sum. Both the child trace and predecessor moment are retained. -/
def heatVHEATDriftRare (k : ℕ) (e_h K C b R A T : ℝ) : ℝ :=
  (k:ℝ)*e_h*((2*K+2*b*C)*R+C*R^2)*(A^(k-1)*(T+4))

/-- The literal first line of VHEAT(7), with no term suppressed at k=1
or at the top interpolation degree. -/
def heatVHEATDriftFirstLine (k : ℕ) (e_h K C b eps X F : ℝ) : ℝ :=
  (k:ℝ)*e_h*((2*K+2*b*C)*(4*nativeHeatVHEATJ eps X F 20 1 (k-1)+
    nativeHeatVHEATJ eps X F 20 1 k)+C*(4*nativeHeatVHEATJ eps X F 20 2 (k-1)+
    nativeHeatVHEATJ eps X F 20 2 k))

/-- On any joint probability law, the entire non-leading drift/mixed bill
has exactly the first-line J payment. No independence is used. -/
theorem heatVHEATDrift_rare_integral
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (R A T : Ω → ℝ)
    (hR : AEStronglyMeasurable R μ) (hA : AEStronglyMeasurable A μ) (hT : AEStronglyMeasurable T μ)
    (hR0 : ∀ ω,0 ≤ R ω) (hA0 : ∀ ω,0 ≤ A ω) (hT0 : ∀ ω,0 ≤ T ω)
    (k : ℕ) (hk : 1 ≤ k) (hk20 : k ≤ 20)
    (e_h K C b eps X F : ℝ) (heh : 0 ≤ e_h) (hK : 0 ≤ K) (hC : 0 ≤ C) (hb : 0 ≤ b)
    (heps : 0 ≤ eps) (hX : 0 < X) (hF : 0 ≤ F)
    (hR128 : eLpNorm R 128 μ ≤ ENNReal.ofReal eps)
    (hA20 : eLpNorm A 20 μ ≤ ENNReal.ofReal X) (hT20 : eLpNorm T 20 μ ≤ ENNReal.ofReal X)
    (hA128 : eLpNorm A 128 μ ≤ ENNReal.ofReal F) (hT128 : eLpNorm T 128 μ ≤ ENNReal.ofReal F) :
    Integrable (fun ω => heatVHEATDriftRare k e_h K C b (R ω) (A ω) (T ω)) μ ∧
      (∫ ω,heatVHEATDriftRare k e_h K C b (R ω) (A ω) (T ω) ∂μ) ≤
        heatVHEATDriftFirstLine k e_h K C b eps X F := by
  have h1 := nativeHeat_rare_linear_error_integral μ R A T hR hA hT hR0 hA0 hT0
    eps X F heps hX hF hR128 hA20 hT20 hA128 hT128 1 (k-1) (by norm_num) (by omega)
  have h2 := nativeHeat_rare_linear_error_integral μ R A T hR hA hT hR0 hA0 hT0
    eps X F heps hX hF hR128 hA20 hT20 hA128 hT128 2 (k-1) le_rfl (by omega)
  have he : (fun ω => heatVHEATDriftRare k e_h K C b (R ω) (A ω) (T ω))=
      (fun ω => ((k:ℝ)*e_h*(2*K+2*b*C))*(R ω^1*(A ω^(k-1)*(T ω+4)))+
        ((k:ℝ)*e_h*C)*(R ω^2*(A ω^(k-1)*(T ω+4)))) := by
    funext ω
    unfold heatVHEATDriftRare
    ring
  rw [he]
  have hi := (h1.1.const_mul ((k:ℝ)*e_h*(2*K+2*b*C))).add (h2.1.const_mul ((k:ℝ)*e_h*C))
  refine ⟨hi,?_⟩
  rw [integral_add (h1.1.const_mul _) (h2.1.const_mul _),integral_const_mul,integral_const_mul]
  have hkc : 0 ≤ (k:ℝ)*e_h := mul_nonneg (Nat.cast_nonneg _) heh
  have hcoef : 0 ≤ 2*K+2*b*C := add_nonneg (mul_nonneg (by norm_num) hK)
    (mul_nonneg (mul_nonneg (by norm_num) hb) hC)
  have hh := add_le_add (mul_le_mul_of_nonneg_left h1.2 (mul_nonneg hkc hcoef))
    (mul_le_mul_of_nonneg_left h2.2 (mul_nonneg hkc hC))
  simp only [Nat.sub_add_cancel hk] at hh
  exact hh.trans_eq (by unfold heatVHEATDriftFirstLine; ring)

end
end ASDExplicitGamma.Native
