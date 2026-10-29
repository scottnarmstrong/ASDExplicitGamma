module

public import ASDExplicitGamma.Scalar.UpperCellEnergyPhysicalSquareMoment
public import ASDExplicitGamma.Scalar.UpperCellEnergyFourthMoment

/-! The actual physical principal load meets the fourth-moment cap. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Algsuperdiff.Section3
open scoped ENNReal
noncomputable section

/-- The literal squared physical load has L2 norm at most four. -/
theorem upper_cell_physical_load_square_cap
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (n : ℤ) (hg : M.gamma ≤ gammaZero) (hstate : nativeInductionState M h n)
    {e : Vec 2} (he : Book.Ch02.vecNorm e = 1) (Q : TriadicCube 2) :
    let height := ⌊(17/50:ℝ)/M.gamma⌋.toNat
    let S := fun ω => 1+∑ i : Fin 2,
      (upperCellPhysicalPotentialMean M n (n+height) (Annealed.sigmaBar M n:ℝ)⁻¹ e Q ω i)^2
    MemLp S 2 (Cutoff.cutoffSampleLaw M).toMeasure ∧
      lpNorm S 2 (Cutoff.cutoffSampleLaw M).toMeasure ≤ 4 := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let height := ⌊(17/50:ℝ)/M.gamma⌋.toNat
  let X := upperCellPhysicalPotentialMean M n (n+height) (Annealed.sigmaBar M n:ℝ)⁻¹ e Q
  have hs := upper_cell_physical_square_moment M h hM n height (Annealed.sigmaBar M n:ℝ)⁻¹ e Q
  have hz := upper_cell_potential_variance_gate M h hM n hg hstate he
  have hconst : MemLp (fun _ : Cutoff.CutoffSample 2 => (1:ℝ)) 2 μ := memLp_const 1
  refine ⟨hconst.add hs.1, ?_⟩
  have hadd := lpNorm_add_le (g := fun ω => ∑ i : Fin 2, (X ω i)^2) hconst (by norm_num)
  have hnorm : lpNorm (fun _ : Cutoff.CutoffSample 2 => (1:ℝ)) 2 μ = 1 := by simp
  rw [hnorm] at hadd
  have hsq : Real.sqrt 3 ≤ 2 := (Real.sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hcap := hs.2.trans (mul_le_mul_of_nonneg_left hz.le (Real.sqrt_nonneg 3))
  have hcap' := hcap.trans (mul_le_mul_of_nonneg_right hsq (by norm_num : (0:ℝ)≤9/10))
  exact hadd.trans (by linarith only [hcap'])

/-- L4 at most two for the exact physical spatial mean in the trial field.
Only the completed left state enters; there is no future-state premise. -/
theorem upper_cell_physical_load_magnitude_L4
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (n : ℤ) (hg : M.gamma ≤ gammaZero) (hstate : nativeInductionState M h n)
    {e : Vec 2} (he : Book.Ch02.vecNorm e = 1) (Q : TriadicCube 2) :
    let P := upperCellPhysicalLoadMagnitude M n (n+⌊(17/50:ℝ)/M.gamma⌋.toNat)
      (Annealed.sigmaBar M n:ℝ)⁻¹ e Q
    MemLp P 4 (Cutoff.cutoffSampleLaw M).toMeasure ∧
      eLpNorm P 4 (Cutoff.cutoffSampleLaw M).toMeasure ≤ 2 := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let height := ⌊(17/50:ℝ)/M.gamma⌋.toNat
  let X := upperCellPhysicalPotentialMean M n (n+height) (Annealed.sigmaBar M n:ℝ)⁻¹ e Q
  let G := fun ω => 1+∑ i : Fin 2, (X ω i)^2
  let P := upperCellPhysicalLoadMagnitude M n (n+height) (Annealed.sigmaBar M n:ℝ)⁻¹ e Q
  have hs := upper_cell_physical_load_square_cap M h hM n hg hstate he Q
  have hG : ∀ ω, 0 ≤ G ω := fun ω => add_nonneg zero_le_one
    (Finset.sum_nonneg (fun i _ => sq_nonneg (X ω i)))
  have hP : AEStronglyMeasurable P μ :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hs.1.aestronglyMeasurable
  have heq : (fun ω => ‖P ω‖^2) = G := by
    funext ω
    change ‖Real.sqrt (G ω)‖^2 = G ω
    rw [Real.norm_eq_abs,sq_abs,Real.sq_sqrt (hG ω)]
  have hsq : MemLp (fun ω => ‖P ω‖^2) 2 μ := by rw [heq]; exact hs.1
  have hcap : lpNorm (fun ω => ‖P ω‖^2) 2 μ ≤ 4 := by rw [heq]; exact hs.2
  have hh := upper_cell_fourth_moment_from_square μ P hP hsq hcap
  refine ⟨hh.1, ?_⟩
  rw [←ofReal_lpNorm hh.1]
  exact (ENNReal.ofReal_le_ofReal hh.2).trans_eq (by norm_num)

end
end ASDExplicitGamma.Scalar
