module

public import ASDExplicitGamma.Inverse.UnitFluxNorm
public import ASDExplicitGamma.Inverse.TargetResponsePositive

/-! From uniform actual root energies to the true framed inverse operator norm. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Triadic
open scoped ENNReal
noncomputable section

/-- Uniform unit-energy bounds for the actual target imply the literal
root inverse operator norm bound. Positivity, symmetry and the true-frame
identification are proved internally from the genuine Book coefficient. -/
theorem root_norm_le_of_all_unit_energies (M : ABKModel 2) (Q : TriadicCube 2)
    (m J : ℤ) (hm : m ≤ J) (weights : ℤ → ℝ) (ω : Cutoff.CutoffSample 2) (B : ℝ≥0∞)
    (hcap : ∀ q : Vec 2, dotProduct q q=1 → ENNReal.ofReal
      ((Annealed.sigmaBar M m:ℝ)*dotProduct q ((coarseBlockMatrix (cubeSet Q)
        (attenuatedCoefficient M m J weights ω)).lowerRight.mulVec q)) ≤ B) :
    ENNReal.ofReal (rootInverseResponse M Q m J weights ω) ≤ B := by
  let A := coarseBlockMatrix (cubeSet Q) (attenuatedCoefficient M m J weights ω)
  let σ := (Annealed.sigmaBar M m:ℝ)
  let C := σ • A.lowerRight
  have hσ : 0 < σ := (Annealed.sigmaBar_characterization M m).1
  have he := attenuated_sensitivity_matrix_eq M Q m m J le_rfl hm weights ω
  have hsym : IsSymmetricBlockMat A := by
    change IsSymmetricBlockMat (coarseBlockMatrix (cubeSet Q) (attenuatedCoefficient M m J weights ω))
    rw [← he]
    exact Book.Ch02.isSymmetricBlockMat_coarseBlockMatrix _ _
  have hHerm : C.IsHermitian := by
    ext i j
    have hh := hsym (Sum.inr j) (Sum.inr i)
    change A.lowerRight j i=A.lowerRight i j at hh
    simp only [C,Matrix.conjTranspose_apply,Matrix.smul_apply,smul_eq_mul,star_trivial]
    rw [hh]
  have hq (q : Vec 2) : dotProduct q (C.mulVec q)=σ*dotProduct q (A.lowerRight.mulVec q) := by
    simp only [C,Matrix.smul_mulVec,dotProduct_smul,smul_eq_mul]
  have hpos (q : Vec 2) : 0 ≤ dotProduct q (C.mulVec q) := by
    rw [hq]
    have hh := book_pure_flux_nonneg (Book.Ch02.cubeDomain Q)
      (sensitivityBookCoeffOn Q M.nu M.nu_pos (oldResponseCoefficient Q m ω+
        laterResponseCoefficient Q m J (sourceBandWeights m weights) ω)) q
    rw [he] at hh
    exact mul_nonneg hσ.le hh
  have hh := symmetric_norm_of_unit_extended_bound C hHerm hpos B (by
    intro q hunit
    rw [hq]
    exact hcap q hunit)
  have hn : ‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) C‖=rootInverseResponse M Q m J weights ω := by
    rw [show C=σ • A.lowerRight from rfl,map_smul,norm_smul,Real.norm_eq_abs,abs_of_pos hσ]
    rfl
  rwa [hn] at hh

end
end ASDExplicitGamma.Inverse
