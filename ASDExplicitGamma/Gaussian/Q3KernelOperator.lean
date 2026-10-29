module

public import ASDExplicitGamma.Gaussian.H3KernelSections
public import ASDExplicitGamma.Gaussian.H3KernelBound

/-! # The actual q3 derivative-coordinate operators and their Hilbert–Schmidt norms -/

@[expose] public section

open MeasureTheory Homogenization Set
open scoped Topology RealInnerProductSpace

namespace ASDExplicitGamma.Gaussian

section
variable (U : Set (Vec 2)) [IsFiniteMeasure (volume.restrict U)]
  (b : ℝ) (L : {l : ℝ // 0 < l})

theorem q3Section_memLp (a : H3Index) :
    MemLp (q3Section b L a) 2 (volume.restrict U) := by
  apply MemLp.of_bound (q3Section_continuous b L a).aestronglyMeasurable
    ‖q3Section b L a 0‖
  exact Filter.Eventually.of_forall fun x => le_of_eq <| by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [gaussQ3Section_norm_sq, gaussQ3Section_norm_sq]

/-- This is the physical, Hilbert-valued kernel, as an L² function of the spatial variable. -/
noncomputable def q3SpatialKernel (a : H3Index) : Lp WhiteNoise 2 (volume.restrict U) :=
  (q3Section_memLp U b L a).toLp (q3Section b L a)

/-- A derivative coordinate of convolution with a white-noise input. -/
noncomputable def q3Coordinate (a : H3Index) : WhiteNoise →L[ℝ] Lp ℝ 2 (volume.restrict U) :=
  hilbertKernel (volume.restrict U) (q3SpatialKernel U b L a)

theorem q3Coordinate_ae (a : H3Index) (u : WhiteNoise) :
    q3Coordinate U b L a u =ᵐ[volume.restrict U] fun x => ⟪u, q3Section b L a x⟫ := by
  filter_upwards [hilbertKernel_ae (volume.restrict U) (q3SpatialKernel U b L a) u,
    (q3Section_memLp U b L a).coeFn_toLp] with x hx hfx
  change _ = ⟪u, q3SpatialKernel U b L a x⟫ at hx
  change q3SpatialKernel U b L a x = q3Section b L a x at hfx
  change hilbertKernel (volume.restrict U) (q3SpatialKernel U b L a) u x = _
  rw [hx, hfx]

/-- Assemble the ten actual derivative-coordinate operators before checking weak compatibility. -/
noncomputable def q3JetOperator : WhiteNoise →L[ℝ] H3Jet U :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : H3Index => Lp ℝ 2 (volume.restrict U))).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (q3Coordinate U b L))

end
end ASDExplicitGamma.Gaussian
