module

public import ASDExplicitGamma.Gaussian.H3Space
public import ASDExplicitGamma.Gaussian.HilbertKernel

/-! # The ten-coordinate Hilbert–Schmidt identity for Sobolev kernel operators -/

@[expose] public section

open MeasureTheory Homogenization
open scoped Topology

namespace ASDExplicitGamma.Gaussian

section
variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  (U : Set (Vec 2))
  (S : W →L[ℝ] h3Space U)
  (F : H3Index → Lp W 2 (volume.restrict U))
  (hS : ∀ u a, (S u).1 a = hilbertKernel (volume.restrict U) (F a) u)

include F hS

theorem h3Kernel_norm_sq (u : W) :
    ‖S u‖ ^ 2 = ∑ a : H3Index, ‖hilbertKernel (volume.restrict U) (F a) u‖ ^ 2 := by
  change ‖(S u).1‖ ^ 2 = _
  rw [h3Jet_norm_sq]
  simp_rw [hS]

/-- The Sobolev operator is Hilbert–Schmidt for every orthonormal input family once its
actual weak derivative coordinates are identified with their L² kernels. -/
theorem h3Kernel_summable {ι : Type*} (e : ι → W) (he : Orthonormal ℝ e) :
    Summable (fun i => ‖S (e i)‖ ^ 2) := by
  simp_rw [h3Kernel_norm_sq U S F hS]
  exact summable_sum fun a _ => hilbertKernel_summable (volume.restrict U) (F a) e he

end
end ASDExplicitGamma.Gaussian
