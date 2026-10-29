module

public import ASDExplicitGamma.Native.OldSignedCompletedQ1
public import ASDExplicitGamma.Native.GenericSourceChildRows
public import ASDExplicitGamma.Native.GenericSourceEndpointActual

/-! Refined and generic OLD rows with the completed q1 producer discharged. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Gaussian Algsuperdiff.Section3 Numerics.Native
noncomputable section

/-- The refined completed means follow from strict previous native states;
the completed q1 input is proved internally at earlier cutoffs. -/
theorem native_source_child_mean_rows
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (m : ℤ)
    (hpast : ∀ k < m,nativeInductionState M h k) (r : Fin 6) :
    nativeCompletedSourceMean M m r.val ≤
      ENNReal.ofReal (theta M*(nativeCompletedPrefixOldMean r:ℝ)) := by
  apply native_source_child_mean_rows_of_q1 M h hM hg m hpast r
  intro k hk
  exact native_completed_q1_integral_carried M h hM hg k
    (fun l hl => hpast l (hl.trans hk))

/-- The refined weak rows retain the complete tail and rare companion,
with no q1 or source-estimate premise. -/
theorem native_source_child_weak_rows
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (m : ℤ)
    (hpast : ∀ k < m,nativeInductionState M h k) (r : Fin 6) :
    nativeCompletedSourceWeak M m r.val ≤
      ENNReal.ofReal (theta M*(nativeCompletedPrefixOldXi r:ℝ)) := by
  apply native_source_child_weak_rows_of_q1 M h hM hg m hpast r
  intro k hk
  exact native_completed_q1_integral_carried M h hM hg k
    (fun l hl => hpast l (hl.trans hk))

/-- NA-GENERIC-SOURCE-ROWS: actual finite generic means, complete generic weak
rows and both refined six-row families on the entire smaller-gamma ray.
The only assumptions are source data and strict previous native states. -/
theorem native_source_generic_rows
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (m : ℤ)
    (hpast : ∀ k < m,nativeInductionState M h k) :
    (∀ depth : ℕ,9+depth ≤ 1332 → nativeCompletedSourceMean M m depth ≤
      ENNReal.ofReal (theta M*nativeSourceGenericMeanProfile (17/50000) 1 (9+depth))) ∧
    (∀ r : Fin 6,nativeCompletedSourceWeak M m r.val ≤
      ENNReal.ofReal (theta M*nativeSourceWeakInverseCharge
        (nativeSourceGenericCompleteMeanRow (17/50000) 1 r.val 1285)
        (nativeSourceGenericCompleteWeakRow (17/50000) 1 r.val 1285))) ∧
    (∀ r : Fin 6,nativeCompletedSourceMean M m r.val ≤
      ENNReal.ofReal (theta M*(nativeCompletedPrefixOldMean r:ℝ))) ∧
    (∀ r : Fin 6,nativeCompletedSourceWeak M m r.val ≤
      ENNReal.ofReal (theta M*(nativeCompletedPrefixOldXi r:ℝ))) := by
  refine ⟨fun depth hd => native_source_depth_generic_mean_endpoint M h hM hg m hpast depth hd,
    fun r => native_source_generic_weak_actual_endpoint M h hM hg m hpast r.val (by omega),
    native_source_child_mean_rows M h hM hg m hpast,
    native_source_child_weak_rows M h hM hg m hpast⟩

end
end ASDExplicitGamma.Native
