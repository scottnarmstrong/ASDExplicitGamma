module

public import ASDExplicitGamma.Variational.LemmaVHaar

/-! Null-set invariance of the scalar energies used in the source cell reconstruction. -/

@[expose] public section

namespace ASDExplicitGamma.Triadic

open Homogenization MeasureTheory

noncomputable section

/-- Every exact Haar increment depends only on the cell equivalence class. -/
theorem diagCubeIncrement_congr_ae {d : ℕ} (Q : TriadicCube d) (k : ℕ)
    {f g : Vec d → ℝ} (hfg : f =ᵐ[volume.restrict (cubeSet Q)] g) :
    cubeIncrement Q k f = cubeIncrement Q k g := by
  have hp := ASDExplicitGamma.Variational.lemmaV_cubeProjection_congr_ae Q
  cases k with
  | zero => simpa only [cubeIncrement_zero] using hp 0 hfg
  | succ k => rw [cubeIncrement_succ, cubeIncrement_succ, hp k hfg, hp (k+1) hfg]

/-- Positive Haar energies depend only on the source field in the cell. -/
theorem diagPrimalEnergy_congr_ae {d : ℕ} (Q : TriadicCube d) (q : ℝ)
    {f g : Vec d → ℝ} (hfg : f =ᵐ[volume.restrict (cubeSet Q)] g) :
    primalEnergy Q q f = primalEnergy Q q g := by
  have hi (k : ℕ) := diagCubeIncrement_congr_ae Q k hfg
  unfold primalEnergy
  simp only [hi]

/-- Scalar L2 energy is insensitive to changes on cell-null sets. -/
theorem diagEnergy_congr_ae {d : ℕ} (Q : TriadicCube d)
    {f g : Vec d → ℝ} (hfg : f =ᵐ[volume.restrict (cubeSet Q)] g) :
    energy Q f = energy Q g := by
  unfold energy pairing cubeAverage
  congr 1
  apply integral_congr_ae
  filter_upwards [hfg] with x hx
  rw [hx]

end

end ASDExplicitGamma.Triadic
