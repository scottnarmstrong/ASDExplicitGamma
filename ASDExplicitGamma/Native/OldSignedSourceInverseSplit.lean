module

public import ASDExplicitGamma.Native.OldSignedSourceDepthBank

/-! Actual source inverse maxima are measurable and obey the depthwise split. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Inverse Variational Algsuperdiff.Section3
open scoped ENNReal
noncomputable section

/-- The source inverse maximum is the real value of a finite bank maximum. -/
theorem old_signed_source_inverse_measurable (M : ABKModel 2) (n : ℤ) (r : ℕ)
    (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth (originCube 2 n) r)
    (t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1) (j : ℕ) :
    Measurable (fun ω => lemmaVInverseDepthMax U (oldSignedPartialFrameField M n 1 t ω) j) := by
  have hm := history_finite_max_measurable (Finset.univ : Finset ↥(descendantsAtDepth U j))
    (fun V ω => ENNReal.ofReal (rootInverseResponse M V.1 n (n+(1:ℕ))
      (bankPartialInsertionWeights n 1 t) ω))
    (fun V => ENNReal.continuous_ofReal.measurable.comp
      (root_inverse_response_measurable M n (n+(1:ℕ)) (bankPartialInsertionWeights n 1 t) V.1))
  have he : (fun ω => (bankFiniteRootResponseMax (descendantsAtDepth U j)
      M n (n+(1:ℕ)) (bankPartialInsertionWeights n 1 t) ω).toReal)=
      (fun ω => lemmaVInverseDepthMax U (oldSignedPartialFrameField M n 1 t ω) j) := by
    funext ω
    rw [old_signed_source_depth_block_max_eq M n r U hU t ht ω j,
      ENNReal.toReal_ofReal (lemmaVInverseDepthMax_nonneg _ _ _)]
  rw [←he]
  exact ENNReal.measurable_toReal.comp hm

/-- The same baseline-plus-rare split holds for each actual source descendant,
with no estimate assumed and no loss of the depthwise population reserve. -/
theorem old_signed_source_inverse_split
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (n : ℤ) (t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1)
    (hpast : ∀ l<n,nativeInductionState M h l) (r : ℕ) (hr : r ≤ 5)
    (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth (originCube 2 n) r) (j : ℕ) :
    ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      lemmaVInverseDepthMax U (oldSignedPartialFrameField M n 1 t ω) j ≤
        (inverseBankCap .localInverse:ℝ)*bankDepthFrame M j+
          oldSignedSourceDepthRemainder M n t U j ω := by
  have hb := old_signed_source_depth_block_bank M h hM hg n t ht hpast r hr U
    (by simpa only [originCube] using scale_eq_sub_of_mem_descendantsAtDepth hU) j
  have hc : 0 ≤ (inverseBankCap .localInverse:ℝ)*bankDepthFrame M j :=
    mul_nonneg (by norm_num [inverseBankCap]) (bankDepthFrame_pos M j).le
  filter_upwards [hb.block_le] with ω hω
  rw [old_signed_source_depth_block_max_eq M n r U hU t ht ω j] at hω
  rw [←ENNReal.ofReal_add hc (hb.remainder_nonneg ω)] at hω
  exact (ENNReal.ofReal_le_ofReal_iff (add_nonneg hc (hb.remainder_nonneg ω))).mp hω

end
end ASDExplicitGamma.Native
