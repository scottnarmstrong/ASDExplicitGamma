module

public import ASDExplicitGamma.Scalar.MolecularStartup

@[expose] public section

namespace ASDExplicitGamma.Scalar

open Algsuperdiff.Section3

/-- The joint molecular base retains the variance threshold and the full frozen
native state on the same completed-label left half-line. -/
theorem joint_molecular_base (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) :
    ∃ K : ℤ, ∀ n : ℤ, n ≤ K →
      shellVarianceSum h M.gamma n / M.nu ^ 2 ≤ theta M / 400 ∧
        nativeInductionState M h n := by
  obtain ⟨K, hK⟩ := molecular_startup M h hM hγ
  obtain ⟨V, hV⟩ := exists_startup_variance_halfLine M h
  refine ⟨min K V, ?_⟩
  intro n hn
  exact ⟨hV n (hn.trans (min_le_right _ _)), hK n (hn.trans (min_le_left _ _))⟩

end ASDExplicitGamma.Scalar
