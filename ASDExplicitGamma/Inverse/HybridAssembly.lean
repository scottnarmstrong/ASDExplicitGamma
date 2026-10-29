module

public import ASDExplicitGamma.Inverse.SensitivityAssembly
public import ASDExplicitGamma.Inverse.RestrictedResponseCoefficients
public import ASDExplicitGamma.Inverse.ContainedTriangleRootResponse

/-! The actual active-cell response of the hybrid assembly, proved from
the source good event and the complete contained-triangle budget. -/

@[expose] public section
namespace ASDExplicitGamma.Inverse

open Homogenization MeasureTheory Algsuperdiff.Section3
open Algsuperdiff.Section3.Provider Algsuperdiff.Section3.Provider.Multiscale
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Triadic ASDExplicitGamma.Response ASDExplicitGamma.Model
open scoped ENNReal

noncomputable section

/-- The actual contained-cube response sum on a physical Kuhn triangle.
This is the dissection with the proved all-order sensitivity prefactor. -/
theorem reset_good_parent_triangle_response_sum (M : ABKModel 2)
    {Q U : TriadicCube 2} {a : ℕ} (hU : U ∈ descendantsAtDepth Q a)
    (ha : a ≤ 2) (pi : Equiv.Perm (Fin 2))
    (m J : ℤ) (hn : Q.scale+40 ≤ m) (hm : m ≤ J) (weights : ℤ → ℝ)
    (hw : ∀ k ∈ Finset.Ioc m J, 0 ≤ weights k ∧ weights k ≤ 1)
    (ω : Cutoff.CutoffSample 2)
    (hgood : ω ∉ cellFailure M resetAllOrderTau (waveGateEta .allOrder) Q)
    (v : Vec 2) :
    (∑' P : ↥(triangleCubePartition U.scale pi), ENNReal.ofReal
      (((volume (openCubeSet (triangleRootCube U pi P))).toReal /
        (volume (Whitney.KuhnCell.mk U pi).openCarrier).toReal) *
          ((Annealed.sigmaBar M (Q.scale+40):ℝ) * dotProduct v
            ((coarseBlockMatrix (cubeSet (triangleRootCube U pi P))
              (attenuatedCoefficient M m J weights ω)).lowerRight.mulVec v)))) ≤
      ENNReal.ofReal (rootAssemblySensitivity *
        rootResponseEnvelope (6*resetAllOrderTau) * dotProduct v v) := by
  classical
  let f := fun P : ↥(triangleCubePartition U.scale pi) => ENNReal.ofReal
    (((volume (openCubeSet (triangleRootCube U pi P))).toReal /
      (volume (Whitney.KuhnCell.mk U pi).openCarrier).toReal) *
        ((Annealed.sigmaBar M (Q.scale+40):ℝ) * dotProduct v
          ((coarseBlockMatrix (cubeSet (triangleRootCube U pi P))
            (attenuatedCoefficient M m J weights ω)).lowerRight.mulVec v)))
  let c := fun P : TriadicCube 2 =>
    ((volume (openCubeSet (rootTranslateCube U P))).toReal /
      (volume (Whitney.KuhnCell.mk U pi).openCarrier).toReal) *
        ((Annealed.sigmaBar M (Q.scale+40):ℝ) * dotProduct v
          ((coarseBlockMatrix (cubeSet (rootTranslateCube U P))
            (attenuatedCoefficient M m J weights ω)).lowerRight.mulVec v))
  have hc (i : ℕ) (P : TriadicCube 2) (hP : P ∈ triangleFirstCubes U.scale pi i) :
      0 ≤ c P := by
    have hd := mem_descendantsAtDepth_add hU
      (triangle_first_root_descendant U pi i hP)
    exact mul_nonneg (div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
      (mul_nonneg (Annealed.sigmaBar_characterization M (Q.scale+40)).1.le
        (attenuated_descendant_pure_flux_nonneg M hd (Q.scale+40) m J hn hm weights ω v))
  have hbudget := reset_good_parent_triangle_response_budget M hU ha pi m J hn hm
    weights hw ω hgood v
  have hC0 (i : ℕ) :
      0 ≤ ∑ P ∈ triangleFirstCubes U.scale pi i, c P := Finset.sum_nonneg (hc i)
  have he : (∑' P, f P) = ENNReal.ofReal
      (∑' i : ℕ, ∑ P ∈ triangleFirstCubes U.scale pi i, c P) := by
    rw [← (triangleFirstEquiv U.scale pi).tsum_eq f, ENNReal.tsum_sigma']
    rw [ENNReal.ofReal_tsum_of_nonneg hC0 hbudget.1]
    apply tsum_congr
    intro i
    rw [ENNReal.ofReal_sum_of_nonneg (hc i)]
    have hh := Finset.sum_coe_sort (triangleFirstCubes U.scale pi i)
      (fun P => ENNReal.ofReal (c P))
    change (∑' P : ↥(triangleFirstCubes U.scale pi i), ENNReal.ofReal (c P)) = _
    rw [tsum_fintype]
    exact hh
  change (∑' P, f P) ≤ _
  rw [he]
  exact ENNReal.ofReal_le_ofReal hbudget.2

/-- The actual full-UV response on a good parent is bounded on its
physical Kuhn triangle by the source `g(6 tau)` cap. -/
theorem reset_good_parent_active_triangle_response (M : ABKModel 2)
    {Q U : TriadicCube 2} {a : ℕ} (hU : U ∈ descendantsAtDepth Q a)
    (ha : a ≤ 2) (pi : Equiv.Perm (Fin 2))
    (m J : ℤ) (hn : Q.scale+40 ≤ m) (hm : m ≤ J) (weights : ℤ → ℝ)
    (hw : ∀ k ∈ Finset.Ioc m J, 0 ≤ weights k ∧ weights k ≤ 1)
    (ω : Cutoff.CutoffSample 2)
    (hgood : ω ∉ cellFailure M resetAllOrderTau (waveGateEta .allOrder) Q)
    (v : Vec 2) :
    (Annealed.sigmaBar M (Q.scale+40):ℝ) * dotProduct v
      ((coarseBlockMatrix (Whitney.KuhnCell.mk U pi).openCarrier
        (attenuatedCoefficient M m J weights ω)).lowerRight.mulVec v) ≤
      rootAssemblySensitivity * rootResponseEnvelope (6*resetAllOrderTau) *
        dotProduct v v := by
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
        (triangleRootCubeCoeff U pi aT P) =
      coarseBlockMatrix (cubeSet (triangleRootCube U pi P))
        (attenuatedCoefficient M m J weights ω) := by
    have hP : openCubeSet (triangleRootCube U pi P) ⊆ openCubeSet Q :=
      (triangle_root_cube_subset U pi P).trans hT
    have hh := attenuated_domain_matrix_eq M Q n m J hn hm weights ω
      (Book.Ch02.cubeDomain (triangleRootCube U pi P)) hP
    change Book.Ch02.coarseBlockMatrix _
      (restrictCoeffOn aQ hP) = _ at hh
    change Book.Ch02.coarseBlockMatrix _
      (restrictCoeffOn (restrictCoeffOn aQ hT) _) = _
    rw [show restrictCoeffOn (restrictCoeffOn aQ hT)
      (triangle_root_cube_subset U pi P) = restrictCoeffOn aQ hP from rfl, hh]
    exact (coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube _ _).symm
  change ENNReal.ofReal (blockVecDot (0,v)
      (blockMatVecMul (Book.Ch02.coarseBlockMatrix T aT) (0,v))) ≤ _ at hcmp
  rw [hTe] at hcmp
  simp_rw [hCe, ← lower_right_quadratic] at hcmp
  have hσ : 0 ≤ σ := (Annealed.sigmaBar_characterization M n).1.le
  have hh := mul_le_mul_right hcmp (ENNReal.ofReal σ)
  rw [← ENNReal.ofReal_mul hσ, ← ENNReal.tsum_mul_left] at hh
  have hrhs :
      (∑' P : ↥(triangleCubePartition U.scale pi), ENNReal.ofReal σ *
        ENNReal.ofReal (((volume (openCubeSet (triangleRootCube U pi P))).toReal /
          (volume (Whitney.KuhnCell.mk U pi).openCarrier).toReal) * dotProduct v
            ((coarseBlockMatrix (cubeSet (triangleRootCube U pi P))
              (attenuatedCoefficient M m J weights ω)).lowerRight.mulVec v))) ≤
      ENNReal.ofReal (rootAssemblySensitivity *
        rootResponseEnvelope (6*resetAllOrderTau) * dotProduct v v) := by
    have he (P : ↥(triangleCubePartition U.scale pi)) :
        ENNReal.ofReal σ * ENNReal.ofReal (((volume (openCubeSet
          (triangleRootCube U pi P))).toReal /
          (volume (Whitney.KuhnCell.mk U pi).openCarrier).toReal) * dotProduct v
            ((coarseBlockMatrix (cubeSet (triangleRootCube U pi P))
              (attenuatedCoefficient M m J weights ω)).lowerRight.mulVec v)) =
        ENNReal.ofReal (((volume (openCubeSet (triangleRootCube U pi P))).toReal /
          (volume (Whitney.KuhnCell.mk U pi).openCarrier).toReal) *
            (σ * dotProduct v ((coarseBlockMatrix
              (cubeSet (triangleRootCube U pi P))
              (attenuatedCoefficient M m J weights ω)).lowerRight.mulVec v))) := by
      rw [← ENNReal.ofReal_mul hσ]
      congr 1
      ring
    simp_rw [he]
    exact reset_good_parent_triangle_response_sum M hU ha pi m J hn hm weights hw ω hgood v
  have hcap := hh.trans hrhs
  apply (ENNReal.ofReal_le_ofReal_iff
    (show 0 ≤ rootAssemblySensitivity *
      rootResponseEnvelope (6*resetAllOrderTau) * dotProduct v v by
        have ht : 0 ≤ resetAllOrderTau := by
          norm_num [resetAllOrderTau, Numerics.Wave.allOrderTau]
        have hv : 0 ≤ dotProduct v v :=
          Finset.sum_nonneg (fun _ _ => mul_self_nonneg _)
        have hδ : 0 ≤ rootAssemblySensitivity :=
          root_assembly_sensitivity_pos.le
        have henv : 0 ≤ rootResponseEnvelope (6*resetAllOrderTau) := by
          unfold rootResponseEnvelope
          have hrad : 0 ≤ (6*resetAllOrderTau)*(6*resetAllOrderTau+2) :=
            mul_nonneg (by positivity) (by linarith)
          positivity
        exact mul_nonneg (mul_nonneg hδ henv) hv)).mp hcap

end
end ASDExplicitGamma.Inverse
