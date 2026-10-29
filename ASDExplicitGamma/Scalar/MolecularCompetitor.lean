module

public import ASDExplicitGamma.Variational.AdapterMu
public import ASDExplicitGamma.Response.FrameAlgebra
public import Homogenization.CoarseGraining.SharpBlockBounds.DiagonalSandwich

@[expose] public section

namespace ASDExplicitGamma.Scalar

open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Variational

/-- Constant potential and flux fields are admissible at their own load. -/
def molecularConstantState (P : BlockVec 2) : BlockState 2 :=
  { potential := fun _ => P.1
    flux := fun _ => P.2 }

private theorem molecularConstantState_admissible (U : Set (Vec 2)) (P : BlockVec 2) :
    IsBlockMuAdmissible U P (molecularConstantState P) := by
  have hp : (fun x => (molecularConstantState P).potential x - P.1) = 0 := by
    funext x; simp [molecularConstantState]
  have hq : (fun x => (molecularConstantState P).flux x - P.2) = 0 := by
    funext x; simp [molecularConstantState]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hp]; exact MemLp.zero
  · rw [hp]; exact isPotentialZeroTraceOn_zero
  · rw [hq]; exact MemLp.zero
  · rw [hq]; exact isSolenoidalZeroNormalTraceOn_zero

/-- Actual variational comparison with a prescribed admissible competitor. -/
theorem Mu_le_competitor {U : Set (Vec 2)} {a : CoeffField 2} {ν Λ : ℝ}
    (hU : MeasurableSet U) (hEll : IsEllipticFieldOn ν Λ U a)
    (P : BlockVec 2) (X : BlockState 2) (hX : IsBlockMuAdmissible U P X) :
    Mu U P a ≤ volumeAverage U (blockEnergyDensity a X) := by
  have hb : BddBelow (muValueSet U P a) := by
    refine ⟨0, ?_⟩
    rintro s ⟨Y, _, rfl⟩
    apply volumeAverage_nonneg_of_nonneg_on hU
    intro x hx
    exact mul_nonneg (by norm_num)
      (blockMatrixOfCoeff_quadratic_nonneg (hEll.2 x hx) (Y.eval x))
  exact csInf_le hb (muValueSet_mem hX)

/-- Constant competitors bound every diagonal entry of the actual coarse matrix. -/
theorem coarse_diagonal_le_constant {Q : TriadicCube 2} {a : CoeffField 2} {ν Λ : ℝ}
    (hEll : IsEllipticFieldOn ν Λ (cubeSet Q) a) (α : BlockCoord 2) :
    blockMatEntry (coarseBlockMatrix (cubeSet Q) a) α α ≤
      2 * volumeAverage (cubeSet Q) (blockEnergyDensity a (molecularConstantState (blockBasis α))) := by
  have hc := Mu_le_competitor (measurableSet_cubeSet Q) hEll (blockBasis α)
    (molecularConstantState (blockBasis α)) (molecularConstantState_admissible _ _)
  have hd : blockMatEntry (coarseBlockMatrix (cubeSet Q) a) α α =
      2 * Mu (cubeSet Q) (blockBasis α) a := by
    cases α <;> simp [blockMatEntry, coarseBlockMatrix, coarseBlockEntry]
  rw [hd]
  linarith only [hc]

private theorem planar_constant_energy (ν κ : ℝ) (hν : ν ≠ 0)
    (P : BlockVec 2) (x : Vec 2) :
    blockEnergyDensity (fun _ => responsePlanarCoefficient ν κ) (molecularConstantState P) x =
      (1 / 2 : ℝ) * responseFrameEnergyDensity ν 1 κ P := by
  have h := responseFrameEnergyDensity_eq_blockMatrix ν 1 κ hν (by norm_num) P
  have hf (A : BlockMat 2) : frameMatrix 1 A = A := by cases A; simp [frameMatrix]
  rw [hf] at h
  exact congrArg (fun z : ℝ => (1 / 2 : ℝ) * z) h.symm

private theorem planar_constant_top_energy (ν κ : ℝ) (hν : ν ≠ 0) (i : Fin 2) (x : Vec 2) :
    blockEnergyDensity (fun _ => responsePlanarCoefficient ν κ)
      (molecularConstantState (blockBasis (Sum.inl i))) x = (1 / 2 : ℝ) * (ν + κ ^ 2 / ν) := by
  rw [planar_constant_energy ν κ hν]
  fin_cases i <;>
    simp [responseFrameEnergyDensity, blockBasis, vecNormSq, vecDot, matVecMul,
      responsePlanarJ, Fin.sum_univ_two, Pi.single_apply] <;> ring

private theorem planar_constant_bottom_energy (ν κ : ℝ) (hν : ν ≠ 0) (i : Fin 2) (x : Vec 2) :
    blockEnergyDensity (fun _ => responsePlanarCoefficient ν κ)
      (molecularConstantState (blockBasis (Sum.inr i))) x = (1 / 2 : ℝ) / ν := by
  rw [planar_constant_energy ν κ hν]
  fin_cases i <;>
    simp [responseFrameEnergyDensity, blockBasis, vecNormSq, vecDot, matVecMul,
      responsePlanarJ, Pi.single_apply] <;> ring

/-- Source constant-competitor bound for the bottom block, with the molecular ν. -/
theorem molecular_lowerRight_diagonal_le {Q : TriadicCube 2} {ν Λ : ℝ}
    (hν : 0 < ν) (κ : Vec 2 → ℝ)
    (hEll : IsEllipticFieldOn ν Λ (cubeSet Q) (fun x => responsePlanarCoefficient ν (κ x)))
    (i : Fin 2) :
    (coarseBlockMatrix (cubeSet Q) (fun x => responsePlanarCoefficient ν (κ x))).lowerRight i i ≤ ν⁻¹ := by
  have hc := coarse_diagonal_le_constant hEll (Sum.inr i)
  have he : blockEnergyDensity (fun x => responsePlanarCoefficient ν (κ x))
      (molecularConstantState (blockBasis (Sum.inr i))) = fun _ => (1 / 2 : ℝ) / ν := by
    funext x
    exact planar_constant_bottom_energy ν (κ x) hν.ne' i x
  rw [he, volumeAverage_const (volume_cubeSet_toReal_pos Q).ne'] at hc
  change (coarseBlockMatrix (cubeSet Q) (fun x => responsePlanarCoefficient ν (κ x))).lowerRight i i ≤
    2 * ((1 / 2 : ℝ) / ν) at hc
  have heq : 2 * ((1 / 2 : ℝ) / ν) = ν⁻¹ := by ring
  rw [heq] at hc
  exact hc

/-- The averaged top-load constant competitor has the exact stream-square cost. -/
theorem molecular_upperLeft_diagonal_le {Q : TriadicCube 2} {ν Λ : ℝ}
    (hν : 0 < ν) (κ : Vec 2 → ℝ)
    (hEll : IsEllipticFieldOn ν Λ (cubeSet Q) (fun x => responsePlanarCoefficient ν (κ x)))
    (hκ : IntegrableOn (fun x => κ x ^ 2) (cubeSet Q)) (i : Fin 2) :
    (coarseBlockMatrix (cubeSet Q) (fun x => responsePlanarCoefficient ν (κ x))).upperLeft i i ≤
      ν + volumeAverage (cubeSet Q) (fun x => κ x ^ 2) / ν := by
  have hc := coarse_diagonal_le_constant hEll (Sum.inl i)
  have he : blockEnergyDensity (fun x => responsePlanarCoefficient ν (κ x))
      (molecularConstantState (blockBasis (Sum.inl i))) =
        fun x => (1 / 2 : ℝ) * (ν + κ x ^ 2 / ν) := by
    funext x
    exact planar_constant_top_energy ν (κ x) hν.ne' i x
  rw [he] at hc
  have hav : volumeAverage (cubeSet Q) (fun x => (1 / 2 : ℝ) * (ν + κ x ^ 2 / ν)) =
      (1 / 2 : ℝ) * (ν + volumeAverage (cubeSet Q) (fun x => κ x ^ 2) / ν) := by
    unfold volumeAverage
    rw [integral_const_mul, integral_add (integrable_const ν) (hκ.div_const ν),
      integral_div, integral_const]
    simp only [Measure.real, Measure.restrict_apply_univ, smul_eq_mul]
    let v : ℝ := (volume (cubeSet Q)).toReal
    have hv : v ≠ 0 := (volume_cubeSet_toReal_pos Q).ne'
    change v⁻¹ * ((1 / 2 : ℝ) * (v * ν + (∫ x in cubeSet Q, κ x ^ 2) / ν)) =
      (1 / 2 : ℝ) * (ν + (v⁻¹ * (∫ x in cubeSet Q, κ x ^ 2)) / ν)
    field_simp [hv, hν.ne']
  rw [hav] at hc
  change (coarseBlockMatrix (cubeSet Q) (fun x => responsePlanarCoefficient ν (κ x))).upperLeft i i ≤
    2 * ((1 / 2 : ℝ) * (ν + volumeAverage (cubeSet Q) (fun x => κ x ^ 2) / ν)) at hc
  linarith only [hc]

/-- Exact trace-defect constant-competitor bound at an arbitrary positive frame.
The molecular coefficient ν and the frame σ are distinct parameters. -/
theorem molecular_traceDefect_competitor {Q : TriadicCube 2} {ν Λ σ : ℝ}
    (hν : 0 < ν) (hσ : 0 < σ) (κ : Vec 2 → ℝ)
    (hEll : IsEllipticFieldOn ν Λ (cubeSet Q) (fun x => responsePlanarCoefficient ν (κ x)))
    (hκ : IntegrableOn (fun x => κ x ^ 2) (cubeSet Q)) :
    traceDefect (cubeSet Q) (fun x => responsePlanarCoefficient ν (κ x)) σ ≤
      2 * (σ - ν) ^ 2 / (ν * σ) +
        2 * volumeAverage (cubeSet Q) (fun x => κ x ^ 2) / (ν * σ) := by
  have htop := add_le_add (molecular_upperLeft_diagonal_le hν κ hEll hκ 0)
    (molecular_upperLeft_diagonal_le hν κ hEll hκ 1)
  have hbottom := add_le_add (molecular_lowerRight_diagonal_le hν κ hEll 0)
    (molecular_lowerRight_diagonal_le hν κ hEll 1)
  have ht := mul_le_mul_of_nonneg_left htop (inv_nonneg.mpr hσ.le)
  have hb := mul_le_mul_of_nonneg_left hbottom hσ.le
  unfold traceDefect
  simp only [Matrix.trace, Matrix.diag, Fin.sum_univ_two]
  have halg : σ⁻¹ * (ν + volumeAverage (cubeSet Q) (fun x => κ x ^ 2) / ν +
      (ν + volumeAverage (cubeSet Q) (fun x => κ x ^ 2) / ν)) + σ * (ν⁻¹ + ν⁻¹) - 4 =
      2 * (σ - ν) ^ 2 / (ν * σ) +
        2 * volumeAverage (cubeSet Q) (fun x => κ x ^ 2) / (ν * σ) := by
    field_simp [hν.ne', hσ.ne']
    ring
  rw [← halg]
  linarith only [ht, hb]

end ASDExplicitGamma.Scalar
