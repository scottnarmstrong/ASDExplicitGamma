module

public import ASDExplicitGamma.Native.PrefixCapsFinal

/-! The source continuation with all q1 and parent producer inputs discharged
at a completed source label strictly below the outer induction target. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Gaussian Algsuperdiff.Section3 Numerics.Native
noncomputable section

/-- NA-SOURCE-SMALLER-GAMMA on the actual completed law. The native mean at m
is an earlier-label state coordinate; every q1 and parent return is proved
internally. No numerical cap, transport estimate or prefix result is assumed. -/
theorem native_source_smaller_gamma
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (N : ℤ)
    (hpast : ∀ k < N, nativeInductionState M h k) (m : ℤ) (hm : m < N) :
    NativeSourceSmallerGammaBounds M m := by
  have hprevious : ∀ k < m, nativeInductionState M h k :=
    fun k hk => hpast k (hk.trans hm)
  apply native_source_smaller_gamma_of_q1_parent M h hM hg m hprevious
    (hpast m hm).1
  · intro k hk
    exact native_completed_q1_bound M h hM hg k
      (fun l hl => hpast l ((hl.trans_le hk).trans hm))
  · exact fun j => native_completed_parent_bound M h hM hg m hprevious j

end
end ASDExplicitGamma.Native
