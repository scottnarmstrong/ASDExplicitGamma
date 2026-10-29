module

public import ASDExplicitGamma.Native.ParentRowPhysicalScales
public import ASDExplicitGamma.Cold.NativeThetaScaling

/-! Complete band covariance roots before source multiplier aggregation. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization Gaussian Main Triadic Cold Algsuperdiff.Section3
noncomputable section

/-- Any nonnegative covariance coefficient factors through the exact even
mesh moment, preserving sqrt(theta) without a shell-count loss. -/
theorem parent_row_band_covariance_root
    (M : ABKModel 2) (h : ℝ) (hg : M.gamma≤gammaZero) (n : ℤ)
    (hstate : nativeInductionState M h n) (height p : ℕ) (c : ℝ) (hc : 0≤c) :
    Real.sqrt (∑ i : Fin height,c*(cubeScaleFactor (originCube 2 n)/3^5)^(2*p)*
      (q3ModelAmplitude M h (n+((i.val+1:ℕ):ℤ))/(Annealed.sigmaBar M n:ℝ))^2/
        (q3ModelLength (n+((i.val+1:ℕ):ℤ))).val^(2*p))≤
      Real.sqrt (theta M)*Real.sqrt
        (c*parentRowWeightedClock (fun k => (1/9)^(p*(k+6))) height) := by
  have hh := mul_le_mul_of_nonneg_left
    (parent_row_mesh_moment_bound M h hg n hstate height p) hc
  have he : c*parentRowMeshMoment M h n height p=
      ∑ i : Fin height,c*(cubeScaleFactor (originCube 2 n)/3^5)^(2*p)*
        (q3ModelAmplitude M h (n+((i.val+1:ℕ):ℤ))/(Annealed.sigmaBar M n:ℝ))^2/
          (q3ModelLength (n+((i.val+1:ℕ):ℤ))).val^(2*p) := by
    unfold parentRowMeshMoment
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he] at hh
  have he' : c*(theta M*parentRowWeightedClock (fun k => (1/9)^(p*(k+6))) height)=
      theta M*(c*parentRowWeightedClock (fun k => (1/9)^(p*(k+6))) height) := by ring
  rw [he'] at hh
  exact (Real.sqrt_le_sqrt hh).trans_eq (Real.sqrt_mul (cold_theta_pos M).le _)

end
end ASDExplicitGamma.Native
