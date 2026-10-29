module

-- Ported from GMCExplicitDelta Haar/PoincareCoeff.lean (Apache-2.0).
-- Generalizes the port in ASDExplicitGamma.Triadic.PoincareCoeff to arbitrary sine sets.
public import ASDExplicitGamma.Triadic.PoincareCoeff

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology Homogenization
open ASDExplicitGamma.Triadic.Torus

namespace ASDExplicitGamma.Cold

variable {d : ℕ}

/-- Differentiating the sine coordinate of a mixed box mode. -/
theorem hasDerivAt_modeFactor_sin_set {d : ℕ} (a : Fin d → ℝ) (ℓ : ℝ)
    (n : Fin d → ℤ) (i : Fin d) (O : Finset (Fin d)) (hi : i ∈ O) (t : ℝ) :
    HasDerivAt (modeFactor a ℓ O n i)
      (Real.pi * n i / ℓ * modeFactor a ℓ (O.erase i) n i t) t := by
  have he : modeFactor a ℓ O n i = modeFactor a ℓ {i} n i := by
    funext u
    simp [modeFactor, hi]
  rw [he]
  simpa [modeFactor] using hasDerivAt_modeFactor_sin a ℓ n i t

end ASDExplicitGamma.Cold
