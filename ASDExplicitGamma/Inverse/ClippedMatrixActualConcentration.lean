module

public import ASDExplicitGamma.Inverse.ClippedMatrixColors
public import ASDExplicitGamma.Inverse.ClippedMatrixEntryCap
public import ASDExplicitGamma.Inverse.ClippedMatrixConcentration

/-! Actual clipped-cell matrix concentration, with all analytic and
independence inputs discharged on the original cutoff law. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory ProbabilityTheory Algsuperdiff.Section3
open scoped ENNReal Matrix.Norms.Elementwise
noncomputable section

/-- The old matrix family obeys the source Hoeffding bound before any
cluster selection. Every clipping bound and same-color independence fact is
derived from the actual model; later sensitivity stays outside this sum. -/
theorem clipped_actual_cells_matrix_Lp {I : Type*} [Fintype I]
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (j : ℤ) (τ : ℝ) (hτ : 0 ≤ τ)
    (Q : I → TriadicCube 2) (hs : ∀ i, (Q i).scale=j) (hinj : Function.Injective Q)
    (w : I → ℝ) (p : ℝ) (hp : 1 ≤ p) :
    let μ := (Cutoff.cutoffSampleLaw M).toMeasure
    let Y := fun i => clippedCellMatrix M (j+40) (Q i) τ
    eLpNorm (fun ω => ‖Matrix.toEuclideanCLM (n := BlockCoord 2) (𝕜 := ℝ)
      (∑ i, w i • (Y i ω-∫ ζ, Y i ζ ∂μ))‖) (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal (128*(1+τ+Real.sqrt (τ*(τ+2)))*Real.sqrt p*
        Real.sqrt (∑ i, (w i)^2)*(3:ℝ)^40) := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let Y := fun i => clippedCellMatrix M (j+40) (Q i) τ
  let G := 1+τ+Real.sqrt (τ*(τ+2))
  let color := fun i => clippedCellColor (Q i)
  have hh := clipped_colored_matrix_Lp μ Y color
    (fun c => clipped_cell_matrices_colored_independent M h hM j τ Q hs hinj c)
    (fun i => clipped_cell_matrix_measurable M (j+40) (Q i) τ) G (by dsimp only [G]; positivity)
    (fun i a b => Filter.Eventually.of_forall (fun ω => clipped_cell_matrix_entry_abs_le M (j+40) (Q i) τ hτ ω a b))
    w p hp
  have hev (i : I) (a b : BlockCoord 2) : (∫ ζ, Y i ζ ∂μ) a b=∫ ζ, Y i ζ a b ∂μ := by
    let L : FullBlockMat 2 →ₗ[ℝ] ℝ :=
      { toFun := fun A => A a b
        map_add' := fun A B => rfl
        map_smul' := fun c A => rfl }
    let E : FullBlockMat 2 →L[ℝ] ℝ := ⟨L,L.continuous_of_finiteDimensional⟩
    exact (E.integral_comp_comm (clipped_cell_matrix_integrable M (j+40) (Q i) τ)).symm
  have he (ω : Cutoff.CutoffSample 2) :
      (fun a b => ∑ i, w i*(Y i ω a b-∫ ζ, Y i ζ a b ∂μ)) =
      ∑ i, w i • (Y i ω-∫ ζ, Y i ζ ∂μ) := by
    ext a b
    simp only [Matrix.sum_apply,Matrix.smul_apply,Matrix.sub_apply,smul_eq_mul,hev]
  have hefun : (fun ω => ‖Matrix.toEuclideanCLM (n := BlockCoord 2) (𝕜 := ℝ)
      (fun a b => ∑ i, w i*(Y i ω a b-∫ ζ, Y i ζ a b ∂μ))‖) =
      fun ω => ‖Matrix.toEuclideanCLM (n := BlockCoord 2) (𝕜 := ℝ) (∑ i, w i • (Y i ω-∫ ζ, Y i ζ ∂μ))‖ :=
    funext (fun ω => congrArg (fun A : FullBlockMat 2 => ‖Matrix.toEuclideanCLM (n := BlockCoord 2) (𝕜 := ℝ) A‖) (he ω))
  dsimp only at hh
  rw [hefun] at hh
  apply hh.trans_eq
  congr 1
  have hcard : (Fintype.card (BlockCoord 2):ℝ)=4 := by norm_num [BlockCoord]
  have hc : (Fintype.card ClippedCellColor:ℝ)=(4*(3:ℝ)^40)^2 := by
    rw [clipped_cell_color_card]
    norm_cast
  rw [hcard,hc,Real.sqrt_sq (by positivity : 0 ≤ 4*(3:ℝ)^40)]
  dsimp only [G]
  ring

end
end ASDExplicitGamma.Inverse
