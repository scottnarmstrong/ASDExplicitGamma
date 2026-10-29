module

public import ASDExplicitGamma.Scalar.UpperCellEnergySensitivityPayment

/-! Cauchy payment for correlated nonnegative principal and RESET energies. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open MeasureTheory
noncomputable section

/-- The square root of a nonnegative integrable energy belongs to L2. -/
theorem upper_cell_sqrt_energy_memLp {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (E : Ω → ℝ) (hE : Integrable E μ) (hE0 : ∀ ω, 0≤E ω) :
    MemLp (fun ω => Real.sqrt (E ω)) 2 μ := by
  have hm := Real.continuous_sqrt.comp_aestronglyMeasurable hE.aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq hm).mpr
  simpa only [Real.sq_sqrt (hE0 _)] using hE

/-- No independence is needed for the cross term between the actual principal
and residual energy. Their first moments suffice. -/
theorem upper_cell_integrated_cross {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (E R : Ω → ℝ) (hE : Integrable E μ) (hR : Integrable R μ)
    (hE0 : ∀ ω, 0≤E ω) (hR0 : ∀ ω, 0≤R ω) :
    Integrable (fun ω => Real.sqrt (E ω*R ω)) μ ∧
      (∫ ω, Real.sqrt (E ω*R ω) ∂μ) ≤
        Real.sqrt ((∫ ω,E ω ∂μ)*(∫ ω,R ω ∂μ)) := by
  have he := upper_cell_sqrt_energy_memLp μ E hE hE0
  have hr := upper_cell_sqrt_energy_memLp μ R hR hR0
  have hi := he.integrable_mul hr
  have hs := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (Filter.Eventually.of_forall (fun ω => Real.sqrt_nonneg (E ω)))
    (Filter.Eventually.of_forall (fun ω => Real.sqrt_nonneg (R ω)))
    (show MemLp (fun ω => Real.sqrt (E ω)) (ENNReal.ofReal 2) μ by norm_num; exact he)
    (show MemLp (fun ω => Real.sqrt (R ω)) (ENNReal.ofReal 2) μ by norm_num; exact hr)
  have heq : (fun ω => Real.sqrt (E ω*R ω)) =
      (fun ω => Real.sqrt (E ω)*Real.sqrt (R ω)) := by
    funext ω
    exact Real.sqrt_mul (hE0 ω) _
  rw [heq]
  refine ⟨hi, ?_⟩
  simp only [Real.rpow_two, Real.sq_sqrt (hE0 _), Real.sq_sqrt (hR0 _),
    ←Real.sqrt_eq_rpow] at hs
  exact hs.trans_eq (Real.sqrt_mul (integral_nonneg hE0) _).symm

/-- Integrate the actual pointwise energy triangle, proving integrability of
its left side from the two component first moments. -/
theorem upper_cell_integrated_triangle {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (T E R : Ω → ℝ) (hT : AEStronglyMeasurable T μ)
    (hE : Integrable E μ) (hR : Integrable R μ)
    (hT0 : ∀ ω, 0≤T ω) (hE0 : ∀ ω, 0≤E ω) (hR0 : ∀ ω, 0≤R ω)
    (hb : ∀ᵐ ω ∂μ, T ω ≤ E ω+2*Real.sqrt (E ω*R ω)+R ω) :
    Integrable T μ ∧ (∫ ω,T ω ∂μ) ≤
      (∫ ω,E ω ∂μ)+2*Real.sqrt ((∫ ω,E ω ∂μ)*(∫ ω,R ω ∂μ))+(∫ ω,R ω ∂μ) := by
  have hc := upper_cell_integrated_cross μ E R hE hR hE0 hR0
  have hep : Integrable (fun ω => E ω+2*Real.sqrt (E ω*R ω)) μ := hE.add (hc.1.const_mul 2)
  have hu : Integrable (fun ω => E ω+2*Real.sqrt (E ω*R ω)+R ω) μ := hep.add hR
  have hi : Integrable T μ := hu.mono' hT (hb.mono (fun ω hh => by
    rwa [Real.norm_of_nonneg (hT0 ω)]))
  refine ⟨hi, ?_⟩
  have hh := integral_mono_ae hi hu hb
  rw [integral_add hep hR,
    integral_add hE (hc.1.const_mul 2), integral_const_mul] at hh
  linarith only [hh,hc.2]

end
end ASDExplicitGamma.Scalar
