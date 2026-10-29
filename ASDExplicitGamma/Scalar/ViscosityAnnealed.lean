module

public import ASDExplicitGamma.Scalar.ViscosityCutoff
public import ASDExplicitGamma.Scalar.LawScalarLimit

/-! Fixed-law viscosity comparison for the actual annealed scalar diffusivity. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization Variational Book MeasureTheory Filter
open Algsuperdiff.Section3

/-- The finite-volume annealed top entry inherits the genuine pathwise viscosity comparison. -/
theorem annealed_top_entry_viscosity_comparison (M : ABKModel 2) (r : ℝ)
    (hr : 0 < r) (hr1 : r ≤ 1) (n k : ℤ) :
    r*(Ch04.annealedBlockMatrixAtScale (Cutoff.coefficientCutoffLaw M n) k).upperLeft 0 0 ≤
      (Ch04.annealedBlockMatrixAtScale
        (Cutoff.coefficientCutoffLaw (modelWithViscosity M (r*M.nu) (mul_pos hr M.nu_pos)) n) k).upperLeft 0 0 ∧
    (Ch04.annealedBlockMatrixAtScale
      (Cutoff.coefficientCutoffLaw (modelWithViscosity M (r*M.nu) (mul_pos hr M.nu_pos)) n) k).upperLeft 0 0 ≤
      r⁻¹*(Ch04.annealedBlockMatrixAtScale (Cutoff.coefficientCutoffLaw M n) k).upperLeft 0 0 := by
  simp only [annealed_top_entry_cutoff_samples]
  let N := modelWithViscosity M (r*M.nu) (mul_pos hr M.nu_pos)
  have hI := integrable_cutoff_top_entry M n k 0 0
  have hN := integrable_cutoff_top_entry N n k 0 0
  have hm : (Cutoff.cutoffSampleLaw N).toMeasure=(Cutoff.cutoffSampleLaw M).toMeasure := rfl
  rw [hm] at hN
  have hb (ω : Cutoff.CutoffSample 2) := cutoff_top_block_viscosity_comparison M r hr hr1 n (originCube 2 k) ω
  have hd (ω : Cutoff.CutoffSample 2) :
      r*(coarseBlockMatrix (cubeSet (originCube 2 k)) (Cutoff.coefficientCutoff M.nu n ω).toFun).upperLeft 0 0 ≤
      (coarseBlockMatrix (cubeSet (originCube 2 k)) (Cutoff.coefficientCutoff N.nu n ω).toFun).upperLeft 0 0 ∧
      (coarseBlockMatrix (cubeSet (originCube 2 k)) (Cutoff.coefficientCutoff N.nu n ω).toFun).upperLeft 0 0 ≤
      r⁻¹*(coarseBlockMatrix (cubeSet (originCube 2 k)) (Cutoff.coefficientCutoff M.nu n ω).toFun).upperLeft 0 0 := by
    have hl := (hb ω).1 (Pi.single (0:Fin 2) 1)
    have hu := (hb ω).2 (Pi.single (0:Fin 2) 1)
    simp [vecDot,matVecMul,Matrix.smul_apply,Pi.single_apply] at hl hu
    dsimp only [N,modelWithViscosity]
    exact ⟨by linarith only [hl],by linarith only [hu]⟩
  constructor
  · rw [← integral_const_mul]
    exact integral_mono_ae (hI.const_mul r) hN (Eventually.of_forall fun ω => (hd ω).1)
  · rw [← integral_const_mul]
    exact integral_mono_ae hN (hI.const_mul r⁻¹) (Eventually.of_forall fun ω => (hd ω).2)

/-- True fixed-law scalar viscosity comparison, with no annealed bound premise. -/
theorem sigmaBar_viscosity_comparison (M : ABKModel 2) (r : ℝ)
    (hr : 0 < r) (hr1 : r ≤ 1) (n : ℤ) :
    r*(Annealed.sigmaBar M n : ℝ) ≤
      (Annealed.sigmaBar (modelWithViscosity M (r*M.nu) (mul_pos hr M.nu_pos)) n : ℝ) ∧
    (Annealed.sigmaBar (modelWithViscosity M (r*M.nu) (mul_pos hr M.nu_pos)) n : ℝ) ≤
      r⁻¹*(Annealed.sigmaBar M n : ℝ) := by
  have hM := annealed_top_entry_tendsto_sigmaBar M n
  have hN := annealed_top_entry_tendsto_sigmaBar (modelWithViscosity M (r*M.nu) (mul_pos hr M.nu_pos)) n
  constructor
  · exact le_of_tendsto_of_tendsto (hM.const_mul r) hN
      (Eventually.of_forall fun k => (annealed_top_entry_viscosity_comparison M r hr hr1 n (k:ℤ)).1)
  · exact le_of_tendsto_of_tendsto hN (hM.const_mul r⁻¹)
      (Eventually.of_forall fun k => (annealed_top_entry_viscosity_comparison M r hr hr1 n (k:ℤ)).2)

end ASDExplicitGamma.Scalar
