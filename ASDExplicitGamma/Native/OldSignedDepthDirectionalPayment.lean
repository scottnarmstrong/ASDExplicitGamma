module

public import ASDExplicitGamma.Native.OldSignedDepthBlockBank
public import ASDExplicitGamma.Native.OldSignedBankDirectionalRare

/-! Actual inverse-weighted directional half-trace payments at every depth. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Inverse Variational Algsuperdiff.Section3 Numerics.Inverse
open scoped ENNReal
noncomputable section

/-- The actual framed inverse-depth maximum is measurable, via its literal
finite bank maximum; no almost-sure truncation is introduced. -/
theorem old_signed_depth_inverse_measurable (M : ABKModel 2) (n : ℤ) (t : ℝ)
    (ht : 0 ≤ t ∧ t ≤ 1) (j : ℕ) :
    Measurable (fun ω => lemmaVInverseDepthMax (originCube 2 n)
      (oldSignedPartialFrameField M n 1 t ω) j) := by
  have hm := history_finite_max_measurable
    (Finset.univ : Finset ↥(descendantsAtDepth (originCube 2 n) j))
    (fun U ω => ENNReal.ofReal (rootInverseResponse M U.1 n (n+(1:ℕ))
      (bankPartialInsertionWeights n 1 t) ω))
    (fun U => ENNReal.continuous_ofReal.measurable.comp
      (root_inverse_response_measurable M n (n+(1:ℕ)) (bankPartialInsertionWeights n 1 t) U.1))
  have heq : (fun ω => (bankFiniteRootResponseMax (descendantsAtDepth (originCube 2 n) j)
      M n (n+(1:ℕ)) (bankPartialInsertionWeights n 1 t) ω).toReal)=
      (fun ω => lemmaVInverseDepthMax (originCube 2 n) (oldSignedPartialFrameField M n 1 t ω) j) := by
    funext ω
    rw [old_signed_depth_block_max_eq M n t ht ω j,
      ENNReal.toReal_ofReal (lemmaVInverseDepthMax_nonneg _ _ _)]
  rw [←heq]
  exact ENNReal.measurable_toReal.comp hm

end
end ASDExplicitGamma.Native
