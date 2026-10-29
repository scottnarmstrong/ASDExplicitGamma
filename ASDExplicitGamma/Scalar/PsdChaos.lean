module

public import ASDExplicitGamma.Scalar.PsdFormMaps
public import ASDExplicitGamma.Scalar.PsdWick
public import ASDExplicitGamma.Scalar.ChaosHilbertMoment
public import ASDExplicitGamma.Scalar.ChaosInfiniteInputMap
public import ASDExplicitGamma.Scalar.ChaosBilinearMoments
public import ASDExplicitGamma.Gaussian.NonnegativeFatou

/-! Chaos moment comparison for the quartic Gaussian envelope of a positive-semidefinite
form: a weighted finite sum of Hilbert envelopes. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar

open MeasureTheory ProbabilityTheory ASDExplicitGamma.Gaussian Filter Topology
open scoped BigOperators RealInnerProductSpace ENNReal

section Hilbert

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]

theorem finite_defect_eq_hilbert_envelope {n : ℕ} (B : Fin n → Fin n → W)
    (x : Fin n → ℝ) :
    finiteHilbertGaussianEnvelope (∑ i : Fin n, B i i) B (WithLp.toLp 2 x) =
      ‖defectSource B x‖ ^ 2 := by
  have hdiag : (∑ i : Fin n, B i i) =
      ∑ i : Fin n, ∑ j : Fin n, (if i = j then (1 : ℝ) else 0) • B i j := by
    simp
  have hquad : (∑ i : Fin n, B i i) +
      finiteHilbertGaussianQuadratic B (WithLp.toLp 2 x) = defectSource B x := by
    change (∑ i : Fin n, B i i) +
        ∑ i : Fin n, ∑ j : Fin n,
          (x i * x j - (if i = j then (1 : ℝ) else 0)) • B i j =
      ∑ i : Fin n, ∑ j : Fin n, (x i * x j) • B i j
    have hsum :
        (∑ i : Fin n, ∑ j : Fin n,
          (x i * x j - (if i = j then (1 : ℝ) else 0)) • B i j) =
        (∑ i : Fin n, ∑ j : Fin n, (x i * x j) • B i j) -
          (∑ i : Fin n, ∑ j : Fin n, (if i = j then (1 : ℝ) else 0) • B i j) := by
      calc
        _ = ∑ i : Fin n,
            ((∑ j : Fin n, (x i * x j) • B i j) -
              (∑ j : Fin n, (if i = j then (1 : ℝ) else 0) • B i j)) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro j _
          rw [sub_smul]
        _ = _ := by rw [Finset.sum_sub_distrib]
    rw [hsum, hdiag]
    abel
  simp only [finiteHilbertGaussianEnvelope]
  rw [hquad]

/-- Chaos comparison for the Hilbert norm-squared of a symmetric quadratic defect. -/
theorem hilbert_defect_chaos {n : ℕ} (B : Fin n → Fin n → W) (hB : ∀ i j, B i j = B j i)
    (p : ℝ) (hp : 2 ≤ p) :
    eLpNorm (fun y : EuclideanSpace ℝ (Fin n) => ‖defectSource B (fun i => y i)‖ ^ 2)
        (ENNReal.ofReal (p / (p - 1))) (stdGaussian (EuclideanSpace ℝ (Fin n))) ≤
      ENNReal.ofReal ((1 + Real.sqrt 15) ^ (2 / p) *
        ∫ y, ‖defectSource B (fun i => y i)‖ ^ 2 ∂stdGaussian (EuclideanSpace ℝ (Fin n))) := by
  have h := finite_hilbert_gaussian_envelope_conjugate_bound (∑ i : Fin n, B i i) B hB p hp
  have e : (fun y : EuclideanSpace ℝ (Fin n) => ‖defectSource B (fun i => y i)‖ ^ 2) =
      finiteHilbertGaussianEnvelope (∑ i : Fin n, B i i) B := by
    funext y
    exact (finite_defect_eq_hilbert_envelope B (fun i => y i)).symm
  rw [e]
  exact h

end Hilbert

section Forms

variable {P : Type*} [AddCommGroup P] [Module ℝ P]
  {ι : Type*} {H : ι → Type*} [∀ j, NormedAddCommGroup (H j)]
  [∀ j, InnerProductSpace ℝ (H j)]

theorem map_defectSource {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    (Φ : P →ₗ[ℝ] W) {n : ℕ} (B : Fin n → Fin n → P) (x : Fin n → ℝ) :
    Φ (psdDefectSource B x) = defectSource (fun i j => Φ (B i j)) x := by
  simp only [psdDefectSource, defectSource, map_sum, map_smul]

theorem psd_ofMaps_defect_chaos (s : Finset ι) (Φ : ∀ j, P →ₗ[ℝ] H j) (w : ι → ℝ)
    (hw : ∀ j, 0 ≤ w j) {n : ℕ} (B : Fin n → Fin n → P) (hB : ∀ i j, B i j = B j i)
    (p : ℝ) (hp : 2 ≤ p) :
    let β := PsdForm.ofMaps s Φ w hw
    let Y : EuclideanSpace ℝ (Fin n) → ℝ := fun y =>
      β.form (psdDefectSource B (fun i => y i)) (psdDefectSource B (fun i => y i))
    eLpNorm Y (ENNReal.ofReal (p / (p - 1))) (stdGaussian (EuclideanSpace ℝ (Fin n))) ≤
      ENNReal.ofReal ((1 + Real.sqrt 15) ^ (2 / p) *
        ∫ y, Y y ∂stdGaussian (EuclideanSpace ℝ (Fin n))) := by
  intro β Y
  let μ := stdGaussian (EuclideanSpace ℝ (Fin n))
  let Yj : ι → EuclideanSpace ℝ (Fin n) → ℝ := fun j y =>
    ‖defectSource (fun i k => Φ j (B i k)) (fun i => y i)‖ ^ 2
  have hYj_hilb : ∀ j, Yj j = finiteHilbertGaussianEnvelope
      (∑ i : Fin n, Φ j (B i i)) (fun i k => Φ j (B i k)) := by
    intro j
    funext y
    exact (finite_defect_eq_hilbert_envelope (fun i k => Φ j (B i k)) (fun i => y i)).symm
  have hsymm : ∀ j i k, Φ j (B i k) = Φ j (B k i) := fun j i k => by rw [hB i k]
  have hint : ∀ j, Integrable (Yj j) μ := by
    intro j
    rw [hYj_hilb j]
    exact integrable_finite_hilbert_gaussian_envelope _ _ (hsymm j)
  have hcont : ∀ j, Continuous (Yj j) := by
    intro j
    rw [hYj_hilb j]
    exact continuous_finite_hilbert_gaussian_envelope _ _
  have hY : Y = fun y => ∑ j ∈ s, w j * Yj j y := by
    funext y
    simp only [Y]
    rw [PsdForm.ofMaps_apply_self]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_defectSource]
  have hchaos : ∀ j, eLpNorm (Yj j) (ENNReal.ofReal (p / (p - 1))) μ ≤
      ENNReal.ofReal ((1 + Real.sqrt 15) ^ (2 / p) * ∫ y, Yj j y ∂μ) := by
    intro j
    exact hilbert_defect_chaos (fun i k => Φ j (B i k)) (hsymm j) p hp
  have hq : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (p / (p - 1)) := by
    rw [← ENNReal.ofReal_one]
    apply ENNReal.ofReal_le_ofReal
    rw [le_div_iff₀ (by linarith)]
    linarith
  have hintY : ∫ y, Y y ∂μ = ∑ j ∈ s, w j * ∫ y, Yj j y ∂μ := by
    rw [hY]
    rw [integral_finsetSum _ (fun j _ => (hint j).const_mul (w j))]
    exact Finset.sum_congr rfl fun j _ => integral_const_mul _ _
  have hC : 0 ≤ (1 + Real.sqrt 15) ^ (2 / p) := by positivity
  have hI0 : ∀ j, 0 ≤ ∫ y, Yj j y ∂μ := fun j => integral_nonneg fun y => sq_nonneg _
  calc eLpNorm Y (ENNReal.ofReal (p / (p - 1))) μ
      = eLpNorm (∑ j ∈ s, fun y => w j * Yj j y) (ENNReal.ofReal (p / (p - 1))) μ := by
        rw [hY]
        congr 1
        funext y
        simp [Finset.sum_apply]
    _ ≤ ∑ j ∈ s, eLpNorm (fun y => w j * Yj j y) (ENNReal.ofReal (p / (p - 1))) μ :=
        eLpNorm_sum_le hq
    _ ≤ ∑ j ∈ s, ENNReal.ofReal (w j * ((1 + Real.sqrt 15) ^ (2 / p) * ∫ y, Yj j y ∂μ)) := by
        refine Finset.sum_le_sum fun j _ => ?_
        have h1 : (fun y => w j * Yj j y) = w j • Yj j := by
          funext y; simp
        rw [h1, eLpNorm_const_smul, Real.enorm_eq_ofReal (hw j)]
        rw [ENNReal.ofReal_mul (hw j)]
        gcongr
        exact hchaos j
    _ = ENNReal.ofReal (∑ j ∈ s, w j * ((1 + Real.sqrt 15) ^ (2 / p) * ∫ y, Yj j y ∂μ)) := by
        rw [ENNReal.ofReal_sum_of_nonneg]
        intro j _
        exact mul_nonneg (hw j) (mul_nonneg hC (hI0 j))
    _ = _ := by
        rw [hintY, Finset.mul_sum]
        congr 1
        refine Finset.sum_congr rfl fun j _ => by ring

end Forms

section Limit

variable {P : Type*} [AddCommGroup P] [Module ℝ P]

/-- Chaos comparison for the monotone limit `q` of forms each satisfying it. -/
theorem psd_limit_chaos {n : ℕ} (β : ℕ → PsdForm P) (q : P → ℝ)
    (hmono : ∀ K a, (β K).form a a ≤ q a)
    (hlim : ∀ a, Tendsto (fun K => (β K).form a a) atTop (𝓝 (q a)))
    (B : Fin n → Fin n → P) (p : ℝ) (hp : 2 ≤ p) (C0 : ℝ)
    (hcont : ∀ K, Continuous (fun y : EuclideanSpace ℝ (Fin n) =>
      (β K).form (psdDefectSource B (fun i => y i)) (psdDefectSource B (fun i => y i))))
    (hint : ∀ K, Integrable (fun y : EuclideanSpace ℝ (Fin n) =>
      (β K).form (psdDefectSource B (fun i => y i)) (psdDefectSource B (fun i => y i)))
      (stdGaussian (EuclideanSpace ℝ (Fin n))))
    (hbound : ∀ K, ∫ y : EuclideanSpace ℝ (Fin n),
      (β K).form (psdDefectSource B (fun i => y i)) (psdDefectSource B (fun i => y i))
        ∂stdGaussian (EuclideanSpace ℝ (Fin n)) ≤ C0)
    (hchaos : ∀ K, eLpNorm (fun y : EuclideanSpace ℝ (Fin n) =>
        (β K).form (psdDefectSource B (fun i => y i)) (psdDefectSource B (fun i => y i)))
        (ENNReal.ofReal (p / (p - 1))) (stdGaussian (EuclideanSpace ℝ (Fin n))) ≤
      ENNReal.ofReal ((1 + Real.sqrt 15) ^ (2 / p) * ∫ y : EuclideanSpace ℝ (Fin n),
        (β K).form (psdDefectSource B (fun i => y i)) (psdDefectSource B (fun i => y i))
          ∂stdGaussian (EuclideanSpace ℝ (Fin n)))) :
    let μ := stdGaussian (EuclideanSpace ℝ (Fin n))
    let Y : EuclideanSpace ℝ (Fin n) → ℝ := fun y => q (psdDefectSource B (fun i => y i))
    Integrable Y μ ∧ (∫ y, Y y ∂μ) ≤ C0 ∧
      eLpNorm Y (ENNReal.ofReal (p / (p - 1))) μ ≤
        ENNReal.ofReal ((1 + Real.sqrt 15) ^ (2 / p) * ∫ y, Y y ∂μ) := by
  intro μ Y
  let YK : ℕ → EuclideanSpace ℝ (Fin n) → ℝ := fun K y =>
    (β K).form (psdDefectSource B (fun i => y i)) (psdDefectSource B (fun i => y i))
  have hlimY : ∀ y, Tendsto (fun K => YK K y) atTop (𝓝 (Y y)) := fun y => hlim _
  have hmeas : Measurable Y :=
    measurable_of_tendsto_metrizable (f := YK) (fun K => (hcont K).measurable)
      (tendsto_pi_nhds.mpr hlimY)
  obtain ⟨hYint, hYle⟩ := Gaussian.integrable_integral_le_of_ae_tendsto_nonneg μ
    (f := YK) (g := Y) (C := C0) hint
    (fun K => Filter.Eventually.of_forall fun y => (β K).nonneg _)
    hmeas.aestronglyMeasurable (Filter.Eventually.of_forall hlimY) hbound
  refine ⟨hYint, hYle, ?_⟩
  have hIK : ∀ K, ∫ y, YK K y ∂μ ≤ ∫ y, Y y ∂μ := fun K =>
    integral_mono (hint K) hYint (fun y => hmono K _)
  have hq : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (p / (p - 1)) := by
    rw [← ENNReal.ofReal_one]
    apply ENNReal.ofReal_le_ofReal
    rw [le_div_iff₀ (by linarith)]
    linarith
  have hlim' := MeasureTheory.Lp.eLpNorm_lim_le_liminf_eLpNorm (p := ENNReal.ofReal (p / (p - 1))) (μ := μ)
    (f := YK) (fun K => (hcont K).aestronglyMeasurable) Y hmeas.aestronglyMeasurable
    (Filter.Eventually.of_forall hlimY)
  refine hlim'.trans ?_
  refine Filter.liminf_le_of_frequently_le' (Filter.Frequently.of_forall fun K => ?_)
  refine (hchaos K).trans ?_
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_mul_of_nonneg_left (hIK K) (by positivity)

end Limit

end ASDExplicitGamma.Scalar
