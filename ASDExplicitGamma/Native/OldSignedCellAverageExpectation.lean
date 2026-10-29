module

public import ASDExplicitGamma.Native.OldSignedCellAverage
public import ASDExplicitGamma.Native.OldSignedSqrtProductExpectation

/-! Integration of the actual dependent cell family. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory
noncomputable section

/-- A finite physical cell average of integrable profiles is integrable. -/
theorem old_signed_cell_average_integrable {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Q : TriadicCube 2) (r : ℕ)
    (f : OldSignedCellIndex Q r → Ω → ℝ) (hf : ∀ U,Integrable (f U) μ) :
    Integrable (fun ω => oldSignedCellAverage Q r (fun U => f U ω)) μ := by
  unfold oldSignedCellAverage
  exact (integrable_finsetSum _ (fun U _ => hf U)).const_mul _

/-- The expectation commutes with the whole partition, including the
membership proofs carried by the actual coefficient restrictions. -/
theorem old_signed_cell_average_integral {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Q : TriadicCube 2) (r : ℕ)
    (f : OldSignedCellIndex Q r → Ω → ℝ) (hf : ∀ U,Integrable (f U) μ) :
    (∫ ω,oldSignedCellAverage Q r (fun U => f U ω) ∂μ)=
      oldSignedCellAverage Q r (fun U => ∫ ω,f U ω ∂μ) := by
  unfold oldSignedCellAverage
  rw [integral_const_mul,integral_finsetSum _ (fun U _ => hf U)]

/-- Uniform cell moments pay deterministic spatial weights after averaging;
there is no independence premise. -/
theorem old_signed_cell_weighted_expectation {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Q : TriadicCube 2) (r : ℕ)
    (f : OldSignedCellIndex Q r → Ω → ℝ) (a : OldSignedCellIndex Q r → ℝ)
    (C : ℝ) (hf : ∀ U,Integrable (f U) μ)
    (ha : ∀ U,0≤a U) (hcap : ∀ U,(∫ ω,f U ω ∂μ)≤C) :
    Integrable (fun ω => oldSignedCellAverage Q r (fun U => f U ω*a U)) μ ∧
    (∫ ω,oldSignedCellAverage Q r (fun U => f U ω*a U) ∂μ)≤
      C*oldSignedCellAverage Q r a := by
  have hi U : Integrable (fun ω => f U ω*a U) μ := (hf U).mul_const _
  refine ⟨old_signed_cell_average_integrable μ Q r _ hi,?_⟩
  rw [old_signed_cell_average_integral μ Q r _ hi,←old_signed_cell_average_mul]
  apply old_signed_cell_average_mono
  intro U
  rw [integral_mul_const]
  exact mul_le_mul_of_nonneg_right (hcap U) (ha U)

end
end ASDExplicitGamma.Native
