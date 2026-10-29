module

public import ASDExplicitGamma.Variational.LemmaVH2SingleFamily

/-! The canonical deterministic covariance-defect H2 route with no witness premise. -/

@[expose] public section
namespace ASDExplicitGamma.Variational
open Homogenization MeasureTheory ASDExplicitGamma.Triadic
open scoped BigOperators
noncomputable section

local instance lemmaVH2SingleFiniteMeasure (Q : TriadicCube 2) :
    IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
  (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume

 theorem lemmaVH2RowConstant_single (r S L : ℝ) :
    lemmaVH2RowConstant r ((lemmaVH2R1/4)*(S/L)^2)
      ((lemmaVH2R1/Real.sqrt 2)*(S/L)/L) (lemmaVH2R1*Real.sqrt 2/L^2) =
      lemmaVH2kn (S/L) (r/L) := by
  unfold lemmaVH2RowConstant lemmaVH2kn
  simp only [div_pow]
  ring

 theorem lemmaV_H2_single (Q : TriadicCube 2) (j : ℕ) {L : ℝ} (hL : 0 < L)
    (p : Vec 2) (u : H10Function (openCubeSet Q)) (t : Finset ℕ) (c : ℕ → ℝ) :
    let φ := lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) p u
    let I := diagInterpolant Q j
    let η := q3CovarianceDefectFamily Q L
    (∀ R ∈ descendantsAtDepth Q j, ∀ b, Summable (fun n => (Real.sqrt 3)^(n+1)*energy R
      (cubeIncrement R (n+1) (fun x => lemmaVRowCombination I (fun l => (η l).value) φ t c x b)))) ∧
    Real.sqrt (lemmaVTiledPositiveEnergy Q j (lemmaVRowCombination I (fun l => (η l).value) φ t c)) ≤
      lemmaVH2kn (cubeScaleFactor Q/L) (diagMeshRadius Q j/L)*Real.sqrt (∑ l ∈ t, c l^2)*
        Real.sqrt (lemmaVTiledWeakEnergy Q j φ.grad) := by
  intro φ I η
  have hS := (ASDExplicitGamma.Triadic.cubeScaleFactor_pos' Q).le
  have hA : 0 ≤ (lemmaVH2R1/4)*(cubeScaleFactor Q/L)^2 := by unfold lemmaVH2R1; positivity
  have hG : 0 ≤ (lemmaVH2R1/Real.sqrt 2)*(cubeScaleFactor Q/L)/L := by unfold lemmaVH2R1; positivity
  have hH : 0 ≤ lemmaVH2R1*Real.sqrt 2/L^2 := by unfold lemmaVH2R1; positivity
  have hval : ∀ᵐ x ∂normalizedCubeMeasure Q,
      |(q3CovarianceDefectWitness Q L (cubeCenter Q)).value.toFun x| ≤ (lemmaVH2R1/4)*(cubeScaleFactor Q/L)^2 := by
    filter_upwards [hilbert_ae_cubeSet Q] with x hx
    exact q3CovarianceDefect_value_cap Q L hx
  have hgrad : ∀ᵐ x ∂normalizedCubeMeasure Q,
      planarEuclideanNorm (planarW1Value (q3CovarianceDefectWitness Q L (cubeCenter Q)).gradient x) ≤
        (lemmaVH2R1/Real.sqrt 2)*(cubeScaleFactor Q/L)/L := by
    filter_upwards [hilbert_ae_cubeSet Q] with x hx
    exact q3CovarianceDefect_gradient_cap Q hL hx
  have hb := lemmaVH2_row_bound_smul Q j (q3CovarianceDefectWitness Q L (cubeCenter Q)) p u
    (singleDirectionCoefficient t c) hA hG hH hval hgrad
    (Filter.Eventually.of_forall (q3CovarianceDefect_hessian_cap Q hL (cubeCenter Q)))
  dsimp only at hb
  rw [lemmaVH2RowConstant_single] at hb
  have hr := lemmaVRowCombination_linearCombination I (q3CovarianceDefectFamily Q L) φ t c
  rw [q3CovarianceDefectFamily_combination_value] at hr
  change _ ∧ _
  rw [hr]
  have hκ : 0 ≤ lemmaVH2kn (cubeScaleFactor Q/L) (diagMeshRadius Q j/L) := by
    rw [← lemmaVH2RowConstant_single]
    exact lemmaVH2RowConstant_nonneg (diagMeshRadius_pos Q j).le hA hG hH
  refine ⟨hb.1,hb.2.trans ?_⟩
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (singleDirectionCoefficient_abs_le t c) hκ) (Real.sqrt_nonneg _)

end
end ASDExplicitGamma.Variational
