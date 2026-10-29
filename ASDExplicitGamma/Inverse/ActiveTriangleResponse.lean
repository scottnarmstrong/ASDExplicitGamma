module

public import ASDExplicitGamma.Inverse.TriangleResponseSum
public import ASDExplicitGamma.Inverse.RestrictedResponseCoefficients

/-! The actual active good-simplex response in its parent's true frame.
Sensitivity is used only on the contained cubes. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open Algsuperdiff.Section3.Provider Algsuperdiff.Section3.Provider.Multiscale
open ASDExplicitGamma.Triadic ASDExplicitGamma.Response
noncomputable section

/-- The exact source active-simplex cap. The target is the actual full-UV
attenuated coefficient on the actual physical Kuhn triangle. The complete
contained-cube response majorant was proved before applying subadditivity. -/
theorem good_parent_active_triangle_response (M : ABKModel 2)
    {Q U : TriadicCube 2} {a : ℕ} (hU : U ∈ descendantsAtDepth Q a) (ha : a ≤ 2)
    (pi : Equiv.Perm (Fin 2)) (r : RootRow)
    (m J : ℤ) (hn : Q.scale+40 ≤ m) (hm : m ≤ J) (weights : ℤ → ℝ)
    (hw : ∀ k ∈ Finset.Ioc m J, 0 ≤ weights k ∧ weights k ≤ 1)
    (ω : Cutoff.CutoffSample 2)
    (hgood : ω ∉ cellFailure M (rootTau r) (ASDExplicitGamma.Gaussian.waveGateEta (rootWaveTuple r)) Q)
    (v : Vec 2) :
    (Annealed.sigmaBar M (Q.scale+40):ℝ)*dotProduct v
      ((coarseBlockMatrix (Whitney.KuhnCell.mk U pi).openCarrier
        (attenuatedCoefficient M m J weights ω)).lowerRight.mulVec v) ≤
      rootEdelta r*rootResponseEnvelope (6*rootTau r)*dotProduct v v := by
  let n := Q.scale+40
  let σ := (Annealed.sigmaBar M n:ℝ)
  let k := oldResponseCoefficient Q n ω+
    laterResponseCoefficient Q n J (sourceBandWeights m weights) ω
  let T := kuhnCellDomain (Whitney.KuhnCell.mk U pi)
  have hT : (T:Set (Vec 2)) ⊆ openCubeSet Q :=
    (Whitney.KuhnCell.openCarrier_subset_openCubeSet _).trans
      (openCubeSet_subset_of_mem_descendantsAtDepth hU)
  let aQ := sensitivityBookCoeffOn Q M.nu M.nu_pos k
  let aT := restrictCoeffOn aQ hT
  have hcmp := triangle_root_full_response_le U pi aT 0 v
  have hTe : Book.Ch02.coarseBlockMatrix T aT =
      coarseBlockMatrix (Whitney.KuhnCell.mk U pi).openCarrier
        (attenuatedCoefficient M m J weights ω) :=
    attenuated_domain_matrix_eq M Q n m J hn hm weights ω T hT
  have hCe (P : ↥(triangleCubePartition U.scale pi)) :
      Book.Ch02.coarseBlockMatrix (Book.Ch02.cubeDomain (triangleRootCube U pi P))
        (triangleRootCubeCoeff U pi aT P)=
      coarseBlockMatrix (cubeSet (triangleRootCube U pi P))
        (attenuatedCoefficient M m J weights ω) := by
    have hP : openCubeSet (triangleRootCube U pi P) ⊆ openCubeSet Q :=
      (triangle_root_cube_subset U pi P).trans hT
    have hh := attenuated_domain_matrix_eq M Q n m J hn hm weights ω
      (Book.Ch02.cubeDomain (triangleRootCube U pi P)) hP
    change Book.Ch02.coarseBlockMatrix _ (restrictCoeffOn aQ hP)=_ at hh
    change Book.Ch02.coarseBlockMatrix _ (restrictCoeffOn (restrictCoeffOn aQ hT) _)=_
    rw [show restrictCoeffOn (restrictCoeffOn aQ hT) (triangle_root_cube_subset U pi P)=
      restrictCoeffOn aQ hP from rfl,hh]
    exact (coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube _ _).symm
  change ENNReal.ofReal (blockVecDot (0,v) (blockMatVecMul (Book.Ch02.coarseBlockMatrix T aT) (0,v))) ≤ _ at hcmp
  rw [hTe] at hcmp
  simp_rw [hCe,← lower_right_quadratic] at hcmp
  have hσ : 0 ≤ σ := (Annealed.sigmaBar_characterization M n).1.le
  have hh := mul_le_mul_right hcmp (ENNReal.ofReal σ)
  rw [← ENNReal.ofReal_mul hσ,← ENNReal.tsum_mul_left] at hh
  have hrhs : (∑' P : ↥(triangleCubePartition U.scale pi), ENNReal.ofReal σ*
      ENNReal.ofReal (((volume (openCubeSet (triangleRootCube U pi P))).toReal /
        (volume (Whitney.KuhnCell.mk U pi).openCarrier).toReal)*dotProduct v
          ((coarseBlockMatrix (cubeSet (triangleRootCube U pi P))
            (attenuatedCoefficient M m J weights ω)).lowerRight.mulVec v))) ≤
      ENNReal.ofReal (rootEdelta r*rootResponseEnvelope (6*rootTau r)*dotProduct v v) := by
    have he (P : ↥(triangleCubePartition U.scale pi)) : ENNReal.ofReal σ*
        ENNReal.ofReal (((volume (openCubeSet (triangleRootCube U pi P))).toReal /
          (volume (Whitney.KuhnCell.mk U pi).openCarrier).toReal)*dotProduct v
            ((coarseBlockMatrix (cubeSet (triangleRootCube U pi P))
              (attenuatedCoefficient M m J weights ω)).lowerRight.mulVec v))=
        ENNReal.ofReal (((volume (openCubeSet (triangleRootCube U pi P))).toReal /
          (volume (Whitney.KuhnCell.mk U pi).openCarrier).toReal)*
            (σ*dotProduct v ((coarseBlockMatrix (cubeSet (triangleRootCube U pi P))
              (attenuatedCoefficient M m J weights ω)).lowerRight.mulVec v))) := by
      rw [← ENNReal.ofReal_mul hσ]
      congr 1
      ring
    simp_rw [he]
    exact good_parent_triangle_response_sum M hU ha pi r m J hn hm weights hw ω hgood v
  have hcap := hh.trans hrhs
  apply (ENNReal.ofReal_le_ofReal_iff (show 0 ≤ rootEdelta r*
    rootResponseEnvelope (6*rootTau r)*dotProduct v v by
      have ht : 0 ≤ rootTau r := by cases r <;> norm_num [rootTau]
      have hv : 0 ≤ dotProduct v v := Finset.sum_nonneg (fun _ _ => mul_self_nonneg _)
      unfold rootEdelta rootResponseEnvelope
      positivity)).mp hcap

end
end ASDExplicitGamma.Inverse
