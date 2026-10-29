module

public import ASDExplicitGamma.Scalar.PsdChaos
public import ASDExplicitGamma.Scalar.PsdTiledHaar

/-! Chaos comparison for the tiled positive-Haar energy of a symmetric quadratic
Gaussian defect source (Euclidean Gaussian model). -/
@[expose] public section
namespace ASDExplicitGamma.Scalar

open MeasureTheory ProbabilityTheory ASDExplicitGamma.Gaussian Filter Topology
  Homogenization
open scoped BigOperators ENNReal

theorem euclid_map (n : ℕ) :
    (standardGaussianPi n).map (WithLp.toLp 2) = stdGaussian (EuclideanSpace ℝ (Fin n)) := by
  simpa only [standardGaussianPi] using (map_pi_eq_stdGaussian (ι := Fin n))

theorem euclid_integral (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : Measurable f) :
    ∫ y, f y ∂stdGaussian (EuclideanSpace ℝ (Fin n)) =
      ∫ x, f (WithLp.toLp 2 x) ∂standardGaussianPi n := by
  rw [← euclid_map n]
  exact integral_map (by fun_prop) hf.aestronglyMeasurable

theorem euclid_integrable (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : Measurable f)
    (h : Integrable (fun x => f (WithLp.toLp 2 x)) (standardGaussianPi n)) :
    Integrable f (stdGaussian (EuclideanSpace ℝ (Fin n))) := by
  rw [← euclid_map n]
  exact (integrable_map_measure hf.aestronglyMeasurable (by fun_prop)).2 h

variable (Q : TriadicCube 2) (m : ℕ)

/-- Chaos comparison for the tiled positive-Haar energy of a symmetric quadratic source. -/
theorem tiledPositiveEnergy_defect_chaos {n : ℕ} (B : Fin n → Fin n → TiledHaarField Q m)
    (hB : ∀ i j, B i j = B j i) (p : ℝ) (hp : 2 ≤ p) :
    let μ := stdGaussian (EuclideanSpace ℝ (Fin n))
    let Y : EuclideanSpace ℝ (Fin n) → ℝ := fun y =>
      tiledPositiveEnergy Q m (psdDefectSource B (fun i => y i))
    Integrable Y μ ∧
      (∫ y, Y y ∂μ) ≤ tiledPositiveEnergy Q m (∑ i, B i i) +
          2 * ∑ i, ∑ j, tiledPositiveEnergy Q m (B i j) ∧
      eLpNorm Y (ENNReal.ofReal (p / (p - 1))) μ ≤
        ENNReal.ofReal ((1 + Real.sqrt 15) ^ (2 / p) * ∫ y, Y y ∂μ) := by
  intro μ Y
  have hcont : ∀ K, Continuous (fun y : EuclideanSpace ℝ (Fin n) =>
      (tiledPartialForm Q m K).form (psdDefectSource B (fun i => y i))
        (psdDefectSource B (fun i => y i))) := by
    intro K
    have := psdDefectSource_form_continuous (tiledPartialForm Q m K) B
    exact this.comp (by fun_prop : Continuous (fun y : EuclideanSpace ℝ (Fin n) => (fun i => y i)))
  have hint : ∀ K, Integrable (fun y : EuclideanSpace ℝ (Fin n) =>
      (tiledPartialForm Q m K).form (psdDefectSource B (fun i => y i))
        (psdDefectSource B (fun i => y i))) μ := by
    intro K
    exact euclid_integrable n _ (hcont K).measurable
      (psdDefectSource_form_integrable (tiledPartialForm Q m K) B)
  set C0 := tiledPositiveEnergy Q m (∑ i, B i i) +
          2 * ∑ i, ∑ j, tiledPositiveEnergy Q m (B i j) with hC0
  have hbound : ∀ K, ∫ y : EuclideanSpace ℝ (Fin n),
      (tiledPartialForm Q m K).form (psdDefectSource B (fun i => y i))
        (psdDefectSource B (fun i => y i)) ∂μ ≤ C0 := by
    intro K
    rw [euclid_integral n _ (hcont K).measurable]
    refine (psdDefectSource_gaussian_energy_le (tiledPartialForm Q m K) B).trans ?_
    have h1 := tiledPartialForm_le Q m K (∑ i, B i i)
    have h2 : ∑ i, ∑ j, (tiledPartialForm Q m K).form (B i j) (B i j) ≤
        ∑ i, ∑ j, tiledPositiveEnergy Q m (B i j) :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => tiledPartialForm_le Q m K _
    rw [hC0]
    linarith
  have hchaos : ∀ K, eLpNorm (fun y : EuclideanSpace ℝ (Fin n) =>
        (tiledPartialForm Q m K).form (psdDefectSource B (fun i => y i))
          (psdDefectSource B (fun i => y i))) (ENNReal.ofReal (p / (p - 1))) μ ≤
      ENNReal.ofReal ((1 + Real.sqrt 15) ^ (2 / p) * ∫ y : EuclideanSpace ℝ (Fin n),
        (tiledPartialForm Q m K).form (psdDefectSource B (fun i => y i))
          (psdDefectSource B (fun i => y i)) ∂μ) := by
    intro K
    exact psd_ofMaps_defect_chaos _ _ _ _ B hB p hp
  exact psd_limit_chaos (tiledPartialForm Q m) (tiledPositiveEnergy Q m)
    (fun K a => tiledPartialForm_le Q m K a) (fun a => tiledPartialForm_tendsto Q m a)
    B p hp C0 hcont hint hbound hchaos

end ASDExplicitGamma.Scalar
