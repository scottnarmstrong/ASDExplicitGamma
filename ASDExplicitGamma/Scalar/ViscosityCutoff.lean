module

public import ASDExplicitGamma.Scalar.ViscosityComparison
public import ASDExplicitGamma.Scalar.LawAnnealedShift

/-! Fixed-shell-law viscosity comparison on genuine lower-infinite cutoff samples. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization Variational MeasureTheory Book
open Algsuperdiff.Section3

/-- The skew part of the physical cutoff is independent of viscosity. -/
theorem skew_part_cutoff_coefficient (ν : ℝ) (n : ℤ) (ω : Cutoff.CutoffSample 2) (x : Vec 2) :
    skewPart (Cutoff.coefficientCutoff ν n ω x)=Cutoff.cutoff n ω x := by
  have hs := Cutoff.cutoff_skew n ω x
  ext i j
  have hij := congrFun (congrFun hs i) j
  change Cutoff.cutoff n ω x j i= -Cutoff.cutoff n ω x i j at hij
  simp only [Cutoff.coefficientCutoff_apply,skewPart,matTranspose,Matrix.transpose_apply,
    Matrix.smul_apply,Matrix.sub_apply,Matrix.add_apply,Matrix.one_apply,smul_eq_mul]
  by_cases he : i=j
  · subst he
    simp only [ite_true] at *
    linarith
  · simp only [he,Ne.symm he,ite_false,mul_zero,zero_add]
    linarith

/-- The source fixed-viscosity matrix comparison holds on every actual sample. -/
theorem cutoff_top_block_viscosity_comparison (M : ABKModel 2) (r : ℝ)
    (hr : 0 < r) (hr1 : r ≤ 1) (n : ℤ) (Q : TriadicCube 2) (ω : Cutoff.CutoffSample 2) :
    MatLoewnerLE (r • (coarseBlockMatrix (cubeSet Q) (Cutoff.coefficientCutoff M.nu n ω).toFun).upperLeft)
      (coarseBlockMatrix (cubeSet Q) (Cutoff.coefficientCutoff (r*M.nu) n ω).toFun).upperLeft ∧
    MatLoewnerLE (coarseBlockMatrix (cubeSet Q) (Cutoff.coefficientCutoff (r*M.nu) n ω).toFun).upperLeft
      (r⁻¹ • (coarseBlockMatrix (cubeSet Q) (Cutoff.coefficientCutoff M.nu n ω).toFun).upperLeft) := by
  obtain ⟨La,ha⟩ := cutoff_isEllipticFieldOn_cube M n ω Q
  obtain ⟨Lb,hb⟩ := cutoff_isEllipticFieldOn_cube (modelWithViscosity M (r*M.nu) (mul_pos hr M.nu_pos)) n ω Q
  apply fixed_skew_top_block_comparison Q _ _ M.nu r La Lb M.nu_pos hr hr1 ha hb
  · intro x _
    exact Cutoff.symmPart_coefficientCutoff M.nu n ω x
  · intro x _
    exact Cutoff.symmPart_coefficientCutoff (r*M.nu) n ω x
  · intro x _
    rw [skew_part_cutoff_coefficient,skew_part_cutoff_coefficient]

/-- The literal cutoff top-block entry is integrable, with no moment estimate premise. -/
theorem integrable_cutoff_top_entry (M : ABKModel 2) (n k : ℤ) (i j : Fin 2) :
    Integrable (fun ω : Cutoff.CutoffSample 2 =>
      (coarseBlockMatrix (cubeSet (originCube 2 k)) (Cutoff.coefficientCutoff M.nu n ω).toFun).upperLeft i j)
      (Cutoff.cutoffSampleLaw M).toMeasure := by
  have hi := Provider.Annealed.coefficientCutoffLaw_integrable_blockMatEntry_coarseBlockMatrix
    M n (originCube 2 k) (Sum.inl i) (Sum.inl j)
  change Integrable (fun a : RegCoeffField 2 =>
    (coarseBlockMatrix (cubeSet (originCube 2 k)) a.toFun).upperLeft i j)
      (Cutoff.coefficientCutoffLaw M n) at hi
  rw [Cutoff.coefficientCutoffLaw_eq_map] at hi
  exact (integrable_map_measure hi.aestronglyMeasurable
    (Cutoff.measurable_coefficientCutoff M.nu n).aemeasurable).mp hi

end ASDExplicitGamma.Scalar
