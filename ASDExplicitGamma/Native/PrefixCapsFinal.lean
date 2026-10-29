module

public import ASDExplicitGamma.Native.ParentRowFinalComposition
public import ASDExplicitGamma.Native.GenericSourceUnconditionalRows
public import ASDExplicitGamma.Native.SmallerGammaWeak
public import ASDExplicitGamma.Native.PrefixCapsArithmetic

/-! Actual-law completed-prefix caps at an earlier completed source label.
The outer induction target supplies the native depth-zero row; every positive
parent depth is proved by the boundary-fixed OLD return. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Gaussian Algsuperdiff.Section3 Numerics.Native
noncomputable section

/-- NA-COMPLETED-PREFIX-CAPS: all six exact mean and weak rows on the actual
completed law. The chronology fixes m below the outer induction target N; thus the native
ordinary mean at m is already a standing earlier-label state coordinate.
The weak comparison retains the complete mean tail and rare L20 companion. -/
theorem native_completed_prefix_caps
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (N : ℤ)
    (hpast : ∀ k < N, nativeInductionState M h k) (m : ℤ) (hm : m < N) :
    (∀ r : Fin 6, nativeCompletedSourceMean M m r.val ≤
      ENNReal.ofReal (theta M*((nativeCompletedMeanRows.getD r.val 0 : ℚ) : ℝ))) ∧
    (∀ r : Fin 6, nativeCompletedSourceWeak M m r.val ≤
      ENNReal.ofReal (theta M*((nativeCompletedWeakRows.getD r.val 0 : ℚ) : ℝ))) := by
  have hprevious : ∀ k < m, nativeInductionState M h k :=
    fun k hk => hpast k (hk.trans hm)
  have hmean := (hpast m hm).1
  have hgeneric := native_source_generic_rows M h hM hg m hprevious
  have hparent := fun j => native_completed_parent_bound M h hM hg m hprevious j
  constructor
  · exact native_source_mean_prefix_continuation M m hmean hgeneric hparent
  · apply native_source_completed_weak_continuation M h hM hg m hprevious hmean
    · intro k hk
      exact native_completed_q1_bound M h hM hg k
        (fun l hl => hprevious l (hl.trans hk))
    · exact hparent

/-- Outward six-digit displays, derived after the exact-rational actual-law
comparison. The exact rows remain the primary consumer interface. -/
theorem native_completed_prefix_display_bounds
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (N : ℤ)
    (hpast : ∀ k < N, nativeInductionState M h k) (m : ℤ) (hm : m < N) :
    (∀ r : Fin 6, nativeCompletedSourceMean M m r.val ≤
      ENNReal.ofReal (theta M*((nativeCompletedMeanCaps.getD r.val 0 : ℚ) : ℝ))) ∧
    (∀ r : Fin 6, nativeCompletedSourceWeak M m r.val ≤
      ENNReal.ofReal (theta M*((nativeCompletedWeakCaps.getD r.val 0 : ℚ) : ℝ))) := by
  have hh := native_completed_prefix_caps M h hM hg N hpast m hm
  have ht : 0 ≤ theta M :=
    div_nonneg M.shellPrefix.gamma_pos.le (by norm_num [gammaZero])
  exact ⟨fun r => (hh.1 r).trans (native_completed_prefix_display_caps _ ht r).1,
    fun r => (hh.2 r).trans (native_completed_prefix_display_caps _ ht r).2⟩

end
end ASDExplicitGamma.Native
