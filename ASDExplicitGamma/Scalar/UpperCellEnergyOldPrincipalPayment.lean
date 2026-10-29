module

public import ASDExplicitGamma.Scalar.UpperCellEnergyOldQuadraticExpectation
public import ASDExplicitGamma.Scalar.UpperCellEnergyPhysicalOldQuadratic

/-! The principal OLD payment retains the single half-trace charge. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Variational Algsuperdiff.Section3
open Algsuperdiff.Probability.Stationary
noncomputable section

/-- Scalar block diagonals pay the two actual load energies separately. -/
theorem upper_cell_diagonal_quadratic (a b : ℝ) (e w : Vec 2) :
    blockVecDot (e,w) (blockMatVecMul
      (Book.Ch02.blockDiag (a • (1:Mat 2)) (b • (1:Mat 2))) (e,w)) =
      a*vecDot e e+b*(∑ i : Fin 2, (w i)^2) := by
  simp [blockVecDot, blockMatVecMul, Book.Ch02.blockDiag, vecDot, matVecMul,
    Fin.sum_univ_two]
  ring

/-- The actual framed OLD quadratic at the fresh physical load is integrable
and costs 1+z plus the shared half-trace cap, not (1+z) times that cap. -/
theorem upper_cell_old_principal_payment
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (N : ℤ)
    (hpast : ∀ k < N, nativeInductionState M h k) (n : ℤ) (hn : n < N)
    {e : Vec 2} (he : Book.Ch02.vecNorm e = 1) :
    let height := ⌊(17/50:ℝ)/M.gamma⌋.toNat
    let Q := originCube 2 (n-14)
    let sigma := (Annealed.sigmaBar M n:ℝ)
    let P := fun ω => (e, upperCellPhysicalPotentialMean M n (n+height) sigma⁻¹ e Q ω)
    let E := fun ω => blockVecDot (P ω) (blockMatVecMul
      (frameMatrix sigma (coarseBlockMatrix (cubeSet Q) (Cutoff.coefficientCutoff M.nu n ω).toFun)) (P ω))
    let z := (shellVarianceSum h M.gamma (n+height)-shellVarianceSum h M.gamma n)/(2*sigma^2)
    Integrable E (Cutoff.cutoffSampleLaw M).toMeasure ∧
      (∫ ω, E ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤ 1+z+safeDepth14EndpointCap/2 := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let height := ⌊(17/50:ℝ)/M.gamma⌋.toNat
  let Q := originCube 2 (n-14)
  let sigma := (Annealed.sigmaBar M n:ℝ)
  let W := upperCellPhysicalPotentialMean M n (n+height) sigma⁻¹ e Q
  let S := fun ω => ∑ i : Fin 2, (W ω i)^2
  let z := (shellVarianceSum h M.gamma (n+height)-shellVarianceSum h M.gamma n)/(2*sigma^2)
  have hx := upper_cell_old_quadratic_expectation M n (n+height) sigma⁻¹ e Q sigma
  refine ⟨hx.1, ?_⟩
  rw [hx.2]
  obtain ⟨a,b,ha,hb,hab,hmean⟩ := upper_cell_old_mean_excesses M h hM hg N hpast n hn
  have hm := hmean 0
  rw [translateSet_zero] at hm
  rw [hm]
  simp_rw [upper_cell_diagonal_quadratic]
  have he2 : vecDot e e = 1 := by
    have hh := Book.Ch02.vecNorm_sq_eq_vecNormSq e
    rw [he] at hh
    simpa only [one_pow,vecNormSq] using hh.symm
  rw [he2, mul_one]
  have hi : Integrable S μ := integrable_finset_sum _ (fun i _ => by
    have hi := (upper_cell_physical_mean_coordinate_energy M n (n+height) sigma⁻¹ e Q i).1
    exact (memLp_two_iff_integrable_sq hi.aestronglyMeasurable).mp hi)
  rw [integral_add (integrable_const _) (hi.const_mul _), integral_const, integral_const_mul]
  simp only [Measure.real, measure_univ, ENNReal.toReal_one, one_smul]
  have hz : (∫ ω, S ω ∂μ) ≤ z := by
    have hh := upper_cell_physical_mean_energy M n (n+height) sigma⁻¹ e Q
    rw [upper_cell_potential_variance_signal M h hM n height he] at hh
    exact hh
  have hz1 : z ≤ 1 := by
    have hh := upper_cell_potential_variance_gate M h hM n hg (hpast n hn) he
    rw [upper_cell_potential_variance_signal M h hM n height he] at hh
    exact hh.le.trans (by norm_num)
  have hpay := mul_le_mul_of_nonneg_left hz (add_nonneg zero_le_one hb)
  have hbz := upper_cell_old_weighted_excess_le a b z safeDepth14EndpointCap hb hz1 hab
  nlinarith only [hpay,hbz]

end
end ASDExplicitGamma.Scalar
