module

public import ASDExplicitGamma.Scalar.OldHessianTrialNodalDuality
public import ASDExplicitGamma.Scalar.OldHessianTrialRotatedReceiver
public import ASDExplicitGamma.Scalar.CoefficientFlux

/-! The actual mixed principal covariance has the sharp one-half full-trace
payment, retaining the local reciprocal jumps in the fine top comparison. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational
noncomputable section

/-- The genuine zero-parent-trace potential of the coarse bottom comparison. -/
def oldHessianMixedPotential (Q : TriadicCube 2) (coarse : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (i : Fin 2) : H10Function (openCubeSet Q) :=
  oldSignedCanonicalFirstCorrector Q (responseFramePlanarCoefficientField nu sigma k)
    (responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet Q)
      nu sigma hnu hsigma k) (0,basisVec i)-
    oldHessianCoarsePotential Q coarse nu sigma hnu hsigma k (basisVec i)

theorem old_hessian_mixed_potential_gradient (Q : TriadicCube 2) (coarse : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (i : Fin 2) :
    (oldHessianMixedPotential Q coarse nu sigma hnu hsigma k i).toH1Function.grad=
      oldHessianPatchFirst Q coarse nu sigma hnu hsigma k (0,basisVec i) :=
  old_hessian_coarse_split_gradient Q coarse nu sigma hnu hsigma k (basisVec i)

/-- Reciprocal patch differences are genuinely square integrable on the
parent, including all fine interfaces, before applying broken duality. -/
theorem old_hessian_patch_reciprocal_memLp (Q : TriadicCube 2) (depth : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (P : BlockVec 2) (i : Fin 2) :
    MemLp (fun x => oldHessianPatchReciprocal Q depth nu sigma hnu hsigma k P x i) 2
      (normalizedCubeMeasure Q) := by
  have hm := (Lp.memLp (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k P)).sub
    (old_signed_local_residual_memLp Q depth nu sigma hnu hsigma k (fun _ => P) (memLp_const P))
  exact memLp_normalized_of_memL2On (memScalarL2_coord_of_memVectorL2
    (memVectorL2_snd_of_memBlockL2 (scalar_coefficient_flux_memL2 Q _
      (responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet Q)
        nu sigma hnu hsigma k) hm)) i)

/-- The principal covariance is bounded by exactly half the full fine
trace times the original fine history. No covariance or energy bound is assumed. -/
theorem old_hessian_actual_principal_half (Q : TriadicCube 2) (coarse : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) :
    let u := oldHessianMixedPotential Q coarse nu sigma hnu hsigma k
    let G := fun i : Fin 2 => oldHessianPatchReciprocal Q (coarse+1) nu sigma hnu hsigma k (basisVec i,0)
    |∑ i : Fin 2,cubeAverage Q (fun x => vecDot (oldHessianRotatedReceiver G i x)
      ((diagInterpolant Q (coarse+1) (u i).toH1Function).grad x))| ≤
      oldHessianFineInverseHistory Q (coarse+1) nu sigma k*
        descendantsAverage Q (coarse+1) (fun U =>
          traceDefect (openCubeSet U) (responseFramePlanarCoefficientField nu sigma k) 1)/2 := by
  intro u G
  have hh := old_hessian_nodal_family_duality_half Q (coarse+1) u
    (oldHessianRotatedReceiver G)
    (old_hessian_rotated_receiver_memLp Q G (fun i j =>
      old_hessian_patch_reciprocal_memLp Q (coarse+1) nu sigma hnu hsigma k (basisVec i,0) j))
  rw [old_hessian_rotated_receiver_weak] at hh
  have hu (i : Fin 2) : (u i).toH1Function.grad=
      oldHessianPatchFirst Q coarse nu sigma hnu hsigma k (0,basisVec i) :=
    old_hessian_mixed_potential_gradient Q coarse nu sigma hnu hsigma k i
  simp_rw [hu] at hh
  rw [add_comm (∑ i : Fin 2,lemmaVTiledWeakEnergy Q (coarse+1) (G i))
    (∑ i : Fin 2,lemmaVTiledWeakEnergy Q (coarse+1)
      (oldHessianPatchFirst Q coarse nu sigma hnu hsigma k (0,basisVec i)))] at hh
  exact hh.trans (div_le_div_of_nonneg_right
    (old_hessian_principal_joint_weak_budget Q coarse nu sigma hnu hsigma k) (by norm_num))

end
end ASDExplicitGamma.Scalar
