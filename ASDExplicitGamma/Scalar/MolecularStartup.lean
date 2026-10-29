module

public import ASDExplicitGamma.Scalar.MolecularStartupCoordinates
public import ASDExplicitGamma.Scalar.MolecularStartupCorridor

@[expose] public section

namespace ASDExplicitGamma.Scalar

open Algsuperdiff.Section3

/-- One completed-label left half-line lies in the exact frozen native state.
All coordinates are produced by molecular estimates, without an induction-step premise. -/
theorem molecular_startup (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) :
    ∃ K : ℤ, ∀ n : ℤ, n ≤ K → nativeInductionState M h n := by
  obtain ⟨K, hK⟩ := exists_startup_variance_halfLine M h
  refine ⟨K, ?_⟩
  intro n hn
  obtain ⟨ho, hs, hr, hH, hb⟩ := molecular_startup_coordinates M h hM hγ n (hK n hn)
  obtain ⟨hν, hl, hu⟩ := molecular_startup_scalar_corridor M h hM hγ n (hK n hn)
  exact ⟨ho, hs, hr, hH, hb, hν, hl, hu⟩

end ASDExplicitGamma.Scalar
