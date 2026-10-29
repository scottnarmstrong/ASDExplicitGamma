module

public import ASDExplicitGamma.Scalar.UpperCellEnergyResetSignedKernel
public import ASDExplicitGamma.Model.StationaryPhysicalTests

/-! Physical weak-gradient testing of strong stationary horizontal derivatives. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Algsuperdiff.Probability.Stationary
open Algsuperdiff.Section3.Provider.Corrector
noncomputable section
variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] [AddAction (Vec d) Ω]
variable {μ : Measure Ω} [SFinite μ]
variable [MeasurableConstVAdd (Vec d) Ω] [MeasurableVAdd₂ (Vec d) Ω]
variable [VAddInvariantMeasure (Vec d) Ω μ]

/-- Every actual strong horizontal derivative satisfies the physical weak
derivative identity against each compact smooth test, almost surely. -/
theorem upper_cell_reset_horizontal_physical_test
    {X Y : Ω → ℝ} (hXm : StronglyMeasurable X) (hX : MemLp X 2 μ)
    (hYm : StronglyMeasurable Y) (hY : MemLp Y 2 μ) (i : Fin d)
    (hD : HasDerivAt (fun t : ℝ => koopman (t • basisVec i) (hX.toLp X)) (hY.toLp Y) 0)
    {psi : Vec d → ℝ} (hpsi : ContDiff ℝ (⊤ : ℕ∞) psi) (hc : HasCompactSupport psi) :
    ∀ᵐ ω ∂μ, (∫ x,realize X ω x*fderiv ℝ psi x (basisVec i))=
      -(∫ x,realize Y ω x*psi x) := by
  have hh := upper_cell_reset_signed_kernel_derivative
    (kernelReflect psi) (contDiff_kernelReflect hpsi) (hasCompactSupport_kernelReflect hc)
    i hXm hX hYm hY hD
  filter_upwards [hh] with ω hω
  have hl : mollify (kernelDeriv (kernelReflect psi) i) X ω=
      -(∫ x,realize X ω x*fderiv ℝ psi x (basisVec i)) := by
    rw [mollify,←integral_neg_eq_self (fun y => kernelDeriv (kernelReflect psi) i y • X ((-y) +ᵥ ω)),
      ←integral_neg]
    apply integral_congr_ae
    filter_upwards [] with x
    rw [kernelDeriv_kernelReflect hpsi i]
    simp only [kernelReflect,neg_neg,realize,kernelDeriv,smul_eq_mul,neg_mul]
    ring
  have hr : mollify (kernelReflect psi) Y ω=∫ x,realize Y ω x*psi x := by
    rw [mollify,←integral_neg_eq_self (fun y => kernelReflect psi y • Y ((-y) +ᵥ ω))]
    apply integral_congr_ae
    filter_upwards [] with x
    simp only [kernelReflect,neg_neg,realize,smul_eq_mul]
    ring
  rw [hl,hr] at hω
  exact (neg_eq_iff_eq_neg.mp hω)

end
end ASDExplicitGamma.Scalar
