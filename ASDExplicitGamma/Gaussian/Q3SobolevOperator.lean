module

public import ASDExplicitGamma.Gaussian.Q3KernelOperator
public import ASDExplicitGamma.Gaussian.Q3ConvolutionRegularity

/-! # The actual q3 Hilbert–Schmidt operator into ordinary weak H³ -/

@[expose] public section

open MeasureTheory Homogenization Set Filter
open scoped Topology RealInnerProductSpace

namespace ASDExplicitGamma.Gaussian

section
variable (U : Set (Vec 2)) [IsFiniteMeasure (volume.restrict U)]
  (b : ℝ) (L : {l : ℝ // 0 < l})

theorem q3Convolution_fderiv_basis (a : H3Index)
    (ha : a.1.1.val + a.1.2.val ≤ 2) (u : WhiteNoise) (x : Vec 2) (i : Fin 2) :
    fderiv ℝ (q3Convolution b L a u) x (basisVec i) =
      q3Convolution b L (h3Next a i ha) u x := by
  rw [(q3Convolution_hasFDerivAt b L a ha u x).fderiv]
  fin_cases i <;> simp [basisVec, ContinuousLinearMap.proj_apply]

/-- The ten coordinates are actual weak derivatives, including order three. -/
theorem q3JetOperator_mem (u : WhiteNoise) : q3JetOperator U b L u ∈ h3Space U := by
  rw [mem_h3Space_iff]
  intro a i ha φ hφ hcomp hsupp
  have hweak := HasWeakPartialDerivOn.of_contDiff (U := U) (i := i)
    (q3Convolution_contDiff_one b L a ha u)
  have hh := hweak φ hφ hcomp hsupp
  simp_rw [q3Convolution_fderiv_basis b L a ha u] at hh
  have he (c : H3Index) := q3Coordinate_ae U b L c u
  change (∫ x in U, q3Coordinate U b L a u x * fderiv ℝ φ x (basisVec i)) =
    -(∫ x in U, q3Coordinate U b L (h3Next a i ha) u x * φ x)
  calc
    _ = ∫ x in U, q3Convolution b L a u x * fderiv ℝ φ x (basisVec i) := by
      apply integral_congr_ae
      filter_upwards [he a] with x hx
      rw [hx]
      rfl
    _ = _ := hh
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards [he (h3Next a i ha)] with x hx
      rw [hx]
      rfl

/-- The physical q3 convolution, with all ten compatible ordinary L² derivatives. -/
noncomputable def q3SobolevOperator : WhiteNoise →L[ℝ] h3Space U :=
  (q3JetOperator U b L).codRestrict (h3Space U) (q3JetOperator_mem U b L)

/-- No extra compatibility premise is needed in the actual q3 Hilbert–Schmidt theorem. -/
theorem q3SobolevOperator_summable {ι : Type*} (e : ι → WhiteNoise)
    (he : Orthonormal ℝ e) : Summable (fun j => ‖q3SobolevOperator U b L (e j)‖ ^ 2) :=
  h3Kernel_summable U (q3SobolevOperator U b L) (q3SpatialKernel U b L)
    (fun _ _ => rfl) e he

end
end ASDExplicitGamma.Gaussian
