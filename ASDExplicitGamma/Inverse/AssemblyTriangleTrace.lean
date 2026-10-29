module

public import ASDExplicitGamma.Inverse.AssemblyDescendantTrace
public import ASDExplicitGamma.Inverse.FullResponseActiveTriangle

/-! Old trace budgets on actual physical Kuhn triangles. -/

@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open Algsuperdiff.Section3.Provider Algsuperdiff.Section3.Provider.Multiscale
open ASDExplicitGamma.Variational ASDExplicitGamma.Triadic ASDExplicitGamma.Response
noncomputable section

/-- On a good parent, the complete physical contained-cube family has a
summable normalized old full trace. The planar raw-history payment is
`1+2*sqrt(3)*tau`, before the later shear and wave terms. -/
theorem assembly_parent_triangle_old_trace_budget (M : ABKModel 2)
    {Q U : TriadicCube 2} {a : ℕ} (hU : U ∈ descendantsAtDepth Q a) (ha : a ≤ 2)
    (pi : Equiv.Perm (Fin 2))
    (ω : Cutoff.CutoffSample 2)
    (hgood : ω ∉ cellFailure M resetAllOrderTau
      (ASDExplicitGamma.Gaussian.waveGateEta .allOrder) Q) :
    let C := fun i : ℕ => ∑ P ∈ triangleFirstCubes U.scale pi i,
      ((volume (openCubeSet (rootTranslateCube U P))).toReal /
        (volume (Whitney.KuhnCell.mk U pi).openCarrier).toReal) *
        (Matrix.trace (toFullBlockMat (frameMatrix (Annealed.sigmaBar M (Q.scale+40) : ℝ)
          (coarseBlockMatrix (cubeSet (rootTranslateCube U P))
            (Cutoff.coefficientCutoff M.nu (Q.scale+40) ω).toFun))) / 4)
    Summable C ∧ (∑' i, C i) ≤ 1+2*Real.sqrt 3*resetAllOrderTau := by
  classical
  let n := Q.scale+40
  let w := fun P : TriadicCube 2 =>
    (volume (openCubeSet (rootTranslateCube U P))).toReal /
      (volume (Whitney.KuhnCell.mk U pi).openCarrier).toReal
  let D := fun P : TriadicCube 2 => historyOperatorDefect M n (rootTranslateCube U P) ω
  let B := fun i : ℕ => ∑ P ∈ triangleFirstCubes U.scale pi i, w P*D P
  let C := fun i : ℕ => ∑ P ∈ triangleFirstCubes U.scale pi i,
    w P*(Matrix.trace (toFullBlockMat (frameMatrix (Annealed.sigmaBar M n : ℝ)
      (coarseBlockMatrix (cubeSet (rootTranslateCube U P))
        (Cutoff.coefficientCutoff M.nu n ω).toFun))) / 4)
  let mass := fun i : ℕ => 2*(1/3:ℝ)^(i+1)
  have hτ : 0 ≤ resetAllOrderTau := by norm_num [resetAllOrderTau,Numerics.Wave.allOrderTau]
  have hB := triangle_good_parent_history_budget M n hU ha pi resetAllOrderTau hτ ω
    (good_cell_raw_history M Q resetAllOrderTau
      (ASDExplicitGamma.Gaussian.waveGateEta .allOrder) ω hgood)
  have hw0 (P : TriadicCube 2) : 0 ≤ w P := by
    dsimp only [w]
    exact div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  have hC0 (i : ℕ) : 0 ≤ C i := by
    apply Finset.sum_nonneg
    intro P hP
    exact mul_nonneg (hw0 P)
      (old_full_normalized_trace_nonneg M n (rootTranslateCube U P) ω)
  have hC (i : ℕ) : C i ≤ mass i+B i := by
    let S := triangleFirstCubes U.scale pi i
    have hsum : (∑ P ∈ S, w P*(1+D P)) =
        (∑ P ∈ S, w P)+(∑ P ∈ S, w P*D P) := by
      calc
        _ = ∑ P ∈ S, (w P+w P*D P) := by
          apply Finset.sum_congr rfl
          intro P hP
          ring
        _ = _ := Finset.sum_add_distrib
    calc
      C i ≤ ∑ P ∈ S, w P*(1+D P) := by
        apply Finset.sum_le_sum
        intro P hP
        have hh := old_full_normalized_trace_le_one_add_defect M n
          (rootTranslateCube U P) ω
        have hlin :
            Matrix.trace (toFullBlockMat (frameMatrix (Annealed.sigmaBar M n : ℝ)
              (coarseBlockMatrix (cubeSet (rootTranslateCube U P))
                (Cutoff.coefficientCutoff M.nu n ω).toFun))) / 4 ≤ 1+D P := by
          simpa only [D,n] using hh
        exact mul_le_mul_of_nonneg_left hlin (hw0 P)
      _ = mass i+B i := by
        dsimp only [B,D,mass]
        rw [hsum, triangle_root_first_weights]
  have hmaj : Summable (fun i : ℕ => mass i+B i) :=
    triangle_first_masses_hasSum.summable.add hB.1
  have hCs := hmaj.of_nonneg_of_le hC0 hC
  refine ⟨hCs, ?_⟩
  calc
    (∑' i : ℕ, C i) ≤ ∑' i : ℕ, (mass i+B i) := hCs.tsum_le_tsum hC hmaj
    _ = 1+∑' i : ℕ, B i := by
      dsimp only [mass]
      rw [triangle_first_masses_hasSum.summable.tsum_add hB.1,
        triangle_first_masses_hasSum.tsum_eq]
    _ ≤ 1+2*Real.sqrt 3*resetAllOrderTau := by linarith only [hB.2]


end
end ASDExplicitGamma.Inverse
