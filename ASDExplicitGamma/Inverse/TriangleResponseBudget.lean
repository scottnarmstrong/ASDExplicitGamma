module

public import ASDExplicitGamma.Inverse.TriangleHistoryBudget
public import ASDExplicitGamma.Inverse.TargetResponsePositive

/-! Complete actual contained-cube response budget for an active good
simplex. The source g(6 tau) is retained without a simplex sensitivity input. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open Algsuperdiff.Section3.Provider
noncomputable section

/-- The complete exact first-depth mass distribution has total mass one. -/
theorem triangle_first_masses_hasSum :
    HasSum (fun i : ℕ => 2*(1/3:ℝ)^(i+1)) 1 := by
  have hh := (hasSum_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/3)
    (by norm_num : (1/3:ℝ) < 1)).mul_left (2/3:ℝ)
  convert hh using 1
  · funext i
    rw [pow_succ]
    ring
  · norm_num

/-- The actual full response series of all contained cubes is summable and
bounded by E_delta*g(6 tau)*|v|^2 in the good parent's true old frame. This
also supplies finite energy before any countable variational gluing. -/
theorem good_parent_triangle_response_budget (M : ABKModel 2)
    {Q U : TriadicCube 2} {a : ℕ} (hU : U ∈ descendantsAtDepth Q a) (ha : a ≤ 2)
    (pi : Equiv.Perm (Fin 2)) (r : RootRow)
    (m J : ℤ) (hn : Q.scale+40 ≤ m) (hm : m ≤ J) (weights : ℤ → ℝ)
    (hw : ∀ k ∈ Finset.Ioc m J, 0 ≤ weights k ∧ weights k ≤ 1)
    (ω : Cutoff.CutoffSample 2)
    (hgood : ω ∉ cellFailure M (rootTau r) (ASDExplicitGamma.Gaussian.waveGateEta (rootWaveTuple r)) Q)
    (v : Vec 2) :
    let C := fun i : ℕ => ∑ P ∈ triangleFirstCubes U.scale pi i,
      ((volume (openCubeSet (rootTranslateCube U P))).toReal /
        (volume (Whitney.KuhnCell.mk U pi).openCarrier).toReal)*
          ((Annealed.sigmaBar M (Q.scale+40):ℝ)*
            dotProduct v ((coarseBlockMatrix (cubeSet (rootTranslateCube U P))
              (attenuatedCoefficient M m J weights ω)).lowerRight.mulVec v))
    Summable C ∧ (∑' i, C i) ≤ rootEdelta r*rootResponseEnvelope (6*rootTau r)*dotProduct v v := by
  classical
  let n := Q.scale+40
  let w := fun P : TriadicCube 2 => (volume (openCubeSet (rootTranslateCube U P))).toReal /
    (volume (Whitney.KuhnCell.mk U pi).openCarrier).toReal
  let D := fun P => historyOperatorDefect M n (rootTranslateCube U P) ω
  let B := fun i : ℕ => ∑ P ∈ triangleFirstCubes U.scale pi i, w P*D P
  let C := fun i : ℕ => ∑ P ∈ triangleFirstCubes U.scale pi i,
    w P*((Annealed.sigmaBar M n:ℝ)*dotProduct v ((coarseBlockMatrix
      (cubeSet (rootTranslateCube U P)) (attenuatedCoefficient M m J weights ω)).lowerRight.mulVec v))
  let mass := fun i : ℕ => 2*(1/3:ℝ)^(i+1)
  have hτ : 1 ≤ rootTau r := by cases r <;> norm_num [rootTau]
  have hB := triangle_good_parent_history_budget M n hU ha pi (rootTau r)
    (le_trans (by norm_num) hτ) ω (good_cell_raw_history M Q _ _ ω hgood)
  have hE : 0 ≤ rootEdelta r := (Real.exp_pos _).le
  have hv : 0 ≤ dotProduct v v := Finset.sum_nonneg (fun _ _ => mul_self_nonneg _)
  have hw0 (P : TriadicCube 2) : 0 ≤ w P := div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  have hC0 (i : ℕ) : 0 ≤ C i := by
    apply Finset.sum_nonneg
    intro P hP
    have hd := mem_descendantsAtDepth_add hU (triangle_first_root_descendant U pi i hP)
    exact mul_nonneg (hw0 P) (mul_nonneg (Annealed.sigmaBar_characterization M n).1.le
      (attenuated_descendant_pure_flux_nonneg M hd n m J hn hm weights ω v))
  have hC (i : ℕ) : C i ≤ rootEdelta r*(2*(mass i+B i)*dotProduct v v) := by
    calc
      C i ≤ ∑ P ∈ triangleFirstCubes U.scale pi i,
        rootEdelta r*(2*(w P+w P*D P)*dotProduct v v) := by
        apply Finset.sum_le_sum
        intro P hP
        have hd := mem_descendantsAtDepth_add hU (triangle_first_root_descendant U pi i hP)
        have hh := mul_le_mul_of_nonneg_left
          (good_parent_descendant_linear_cap M hd r m J hn hm weights hw ω hgood v) (hw0 P)
        exact hh.trans_eq (by dsimp only [D,n]; ring)
      _ = rootEdelta r*(2*((∑ P ∈ triangleFirstCubes U.scale pi i, w P)+B i)*dotProduct v v) := by
        dsimp only [B]
        rw [← Finset.mul_sum,← Finset.sum_mul,← Finset.mul_sum,Finset.sum_add_distrib]
      _ = _ := by rw [show (∑ P ∈ triangleFirstCubes U.scale pi i, w P)=mass i from
        triangle_root_first_weights U pi i]
  have hmaj : Summable (fun i => rootEdelta r*(2*(mass i+B i)*dotProduct v v)) :=
    (((triangle_first_masses_hasSum.summable.add hB.1).mul_left 2).mul_right (dotProduct v v)).mul_left _
  have hCs := hmaj.of_nonneg_of_le hC0 hC
  refine ⟨hCs,?_⟩
  apply (hCs.tsum_le_tsum hC hmaj).trans
  have he : (∑' i, rootEdelta r*(2*(mass i+B i)*dotProduct v v))=
      rootEdelta r*(2*(1+∑' i, B i)*dotProduct v v) := by
    rw [tsum_mul_left,tsum_mul_right,tsum_mul_left,
      triangle_first_masses_hasSum.summable.tsum_add hB.1,triangle_first_masses_hasSum.tsum_eq]
  rw [he]
  have hadd : 1+(∑' i, B i) ≤ 1+2*Real.sqrt 3*rootTau r := by linarith only [hB.2]
  have hbudget := (mul_le_mul_of_nonneg_left hadd (by norm_num : (0:ℝ) ≤ 2)).trans
    (planar_linear_average_le_envelope _ hτ)
  have hh := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hbudget hv) hE
  simpa only [mul_assoc] using hh

end
end ASDExplicitGamma.Inverse
