module

public import ASDExplicitGamma.Inverse.TriangleResponseBudget

/-! The complete physical contained-cube response sum, indexed by the same
partition used in countable variational subadditivity. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open Algsuperdiff.Section3.Provider
noncomputable section

/-- The actual contained-cube response budget on the literal variational
partition, with no remaining depth regrouping or convergence premise. -/
theorem good_parent_triangle_response_sum (M : ABKModel 2)
    {Q U : TriadicCube 2} {a : ℕ} (hU : U ∈ descendantsAtDepth Q a) (ha : a ≤ 2)
    (pi : Equiv.Perm (Fin 2)) (r : RootRow)
    (m J : ℤ) (hn : Q.scale+40 ≤ m) (hm : m ≤ J) (weights : ℤ → ℝ)
    (hw : ∀ k ∈ Finset.Ioc m J, 0 ≤ weights k ∧ weights k ≤ 1)
    (ω : Cutoff.CutoffSample 2)
    (hgood : ω ∉ cellFailure M (rootTau r) (ASDExplicitGamma.Gaussian.waveGateEta (rootWaveTuple r)) Q)
    (v : Vec 2) :
    (∑' P : ↥(triangleCubePartition U.scale pi), ENNReal.ofReal
      (((volume (openCubeSet (triangleRootCube U pi P))).toReal /
        (volume (Whitney.KuhnCell.mk U pi).openCarrier).toReal)*
          ((Annealed.sigmaBar M (Q.scale+40):ℝ)*dotProduct v ((coarseBlockMatrix
            (cubeSet (triangleRootCube U pi P)) (attenuatedCoefficient M m J weights ω)).lowerRight.mulVec v)))) ≤
      ENNReal.ofReal (rootEdelta r*rootResponseEnvelope (6*rootTau r)*dotProduct v v) := by
  classical
  let f := fun P : ↥(triangleCubePartition U.scale pi) => ENNReal.ofReal
    (((volume (openCubeSet (triangleRootCube U pi P))).toReal /
      (volume (Whitney.KuhnCell.mk U pi).openCarrier).toReal)*
        ((Annealed.sigmaBar M (Q.scale+40):ℝ)*dotProduct v ((coarseBlockMatrix
          (cubeSet (triangleRootCube U pi P)) (attenuatedCoefficient M m J weights ω)).lowerRight.mulVec v)))
  let c := fun P : TriadicCube 2 =>
    ((volume (openCubeSet (rootTranslateCube U P))).toReal /
      (volume (Whitney.KuhnCell.mk U pi).openCarrier).toReal)*
        ((Annealed.sigmaBar M (Q.scale+40):ℝ)*dotProduct v ((coarseBlockMatrix
          (cubeSet (rootTranslateCube U P)) (attenuatedCoefficient M m J weights ω)).lowerRight.mulVec v))
  have hc (i : ℕ) (P : TriadicCube 2) (hP : P ∈ triangleFirstCubes U.scale pi i) : 0 ≤ c P := by
    have hd := mem_descendantsAtDepth_add hU (triangle_first_root_descendant U pi i hP)
    exact mul_nonneg (div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
      (mul_nonneg (Annealed.sigmaBar_characterization M (Q.scale+40)).1.le
        (attenuated_descendant_pure_flux_nonneg M hd (Q.scale+40) m J hn hm weights ω v))
  have hbudget := good_parent_triangle_response_budget M hU ha pi r m J hn hm weights hw ω hgood v
  have hC0 (i : ℕ) : 0 ≤ ∑ P ∈ triangleFirstCubes U.scale pi i, c P := Finset.sum_nonneg (hc i)
  have he : (∑' P, f P)=ENNReal.ofReal (∑' i : ℕ, ∑ P ∈ triangleFirstCubes U.scale pi i, c P) := by
    rw [← (triangleFirstEquiv U.scale pi).tsum_eq f,ENNReal.tsum_sigma']
    rw [ENNReal.ofReal_tsum_of_nonneg hC0 hbudget.1]
    apply tsum_congr
    intro i
    rw [ENNReal.ofReal_sum_of_nonneg (hc i)]
    have hh := Finset.sum_coe_sort (triangleFirstCubes U.scale pi i) (fun P => ENNReal.ofReal (c P))
    change (∑' P : ↥(triangleFirstCubes U.scale pi i), ENNReal.ofReal (c P))=_
    rw [tsum_fintype]
    exact hh
  change (∑' P, f P) ≤ _
  rw [he]
  exact ENNReal.ofReal_le_ofReal hbudget.2

end
end ASDExplicitGamma.Inverse
