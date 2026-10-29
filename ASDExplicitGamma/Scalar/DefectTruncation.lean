module

public import ASDExplicitGamma.Scalar.DefectJoint
public import ASDExplicitGamma.Scalar.DefectAssembly
public import ASDExplicitGamma.Scalar.PsdTiledChaos
public import ASDExplicitGamma.Scalar.ChaosInfiniteInputMap
public import ASDExplicitGamma.Scalar.ChaosBilinearMoments

/-! Uniform-in-truncation bound for the NEW-bank-weighted tiled energy of the defect
source, on the product of the old marginal and the fresh Gaussian coordinates. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar

open MeasureTheory ProbabilityTheory ASDExplicitGamma.Gaussian Homogenization
  ASDExplicitGamma.Variational
open scoped ENNReal

/-- Fibre bounds in the Gaussian coordinates: for symmetric `B` the energy `H` of the
truncated source has mean `≤ Λ` and `L^{128/127}` norm `≤ C_p Λ` on `stdGaussian`. -/
theorem fibre_bounds (Q : TriadicCube 2) (m : ℕ) {n : ℕ}
    (B : Fin n → Fin n → TiledHaarField Q m) (hB : ∀ i j, B i j = B j i) (K : ℝ)
    (hK : tiledPositiveEnergy Q m (∑ i, B i i) +
        2 * ∑ i, ∑ j, tiledPositiveEnergy Q m (B i j) ≤ K) :
    let f : EuclideanSpace ℝ (Fin n) → ℝ := fun y =>
      tiledPositiveEnergy Q m (psdDefectSource B (fun i => y i))
    Integrable f (stdGaussian (EuclideanSpace ℝ (Fin n))) ∧
      ∫ y, f y ∂stdGaussian (EuclideanSpace ℝ (Fin n)) ≤ K ∧
      eLpNorm f (ENNReal.ofReal (128 / 127)) (stdGaussian (EuclideanSpace ℝ (Fin n))) ≤
        ENNReal.ofReal ((1 + Real.sqrt 15) ^ (2 / (128 : ℝ)) * K) := by
  intro f
  obtain ⟨h1, h2, h3⟩ := tiledPositiveEnergy_defect_chaos Q m B hB 128 (by norm_num)
  have hq : (128 : ℝ) / (128 - 1) = 128 / 127 := by norm_num
  rw [hq] at h3
  have h2' : ∫ y, f y ∂stdGaussian (EuclideanSpace ℝ (Fin n)) ≤ K := h2.trans hK
  refine ⟨h1, h2', h3.trans ?_⟩
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_mul_of_nonneg_left h2' (by positivity)

theorem tiled_defect_measurable (Q : TriadicCube 2) (m : ℕ) {n : ℕ}
    (B : Fin n → Fin n → TiledHaarField Q m) :
    Measurable (fun y : EuclideanSpace ℝ (Fin n) =>
      tiledPositiveEnergy Q m (psdDefectSource B (fun i => y i))) := by
  refine measurable_of_tendsto_metrizable (f := fun K y =>
    (tiledPartialForm Q m K).form (psdDefectSource B (fun i => y i))
      (psdDefectSource B (fun i => y i))) (fun K => ?_) ?_
  · exact ((psdDefectSource_form_continuous (tiledPartialForm Q m K) B).comp
      (by fun_prop : Continuous (fun y : EuclideanSpace ℝ (Fin n) => (fun i => y i)))).measurable
  · rw [tendsto_pi_nhds]
    intro y
    exact tiledPartialForm_tendsto Q m _

end ASDExplicitGamma.Scalar
