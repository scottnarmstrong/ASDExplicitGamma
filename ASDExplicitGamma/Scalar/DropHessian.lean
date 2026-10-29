module

public import ASDExplicitGamma.Scalar.DropBounds

/-! Scaled parity for SC-ONE-SHELL-RECIPROCAL-DROP: the four resolvent terms at the
actual operators are dominated by `c ‖y‖^k`. -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open MeasureTheory Homogenization
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Model ASDExplicitGamma.Response
open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open scoped InnerProduct InnerProductSpace Topology ENNReal

noncomputable section

/-- Pointwise domination of the four terms by a single constant. -/
theorem drop_term_bounds {K : Set (Vec 2)} [CompactSpace K]
    (Q : TriadicCube 2) (hQ : closure (openCubeSet Q) ⊆ K)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ) (e : Vec 2) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ x y : C(K, ℝ),
      ‖physicalParityLinearObservable Q ν σ hν hσ (physicalResponseRestriction Q hQ) e
        (x, y)‖ ≤ c * ‖y‖ ∧
      ‖physicalParityHessianObservable Q ν σ hν hσ (physicalResponseRestriction Q hQ) e
        (x, y)‖ ≤ c * ‖y‖ ^ 2 ∧
      ‖physicalParityCubicObservable Q ν σ hν hσ (physicalResponseRestriction Q hQ) e
        (x, y)‖ ≤ c * ‖y‖ ^ 3 ∧
      ‖physicalParityQuarticObservable Q ν σ hν hσ (physicalResponseRestriction Q hQ) e
        (x, y)‖ ≤ c * ‖y‖ ^ 4 := by
  let R := physicalResponseRestriction Q hQ
  let A := physicalParityCoefficient Q σ hσ R
  let α := ν / σ
  let hα : 0 < α := div_pos hν hσ
  let β : ℝ := α⁻¹
  let J := pureFluxParity (Y := HilbertVectorL2 (openCubeSet Q))
    (X := (physicalPotentialSpace Q).toSubmodule)
  let f : pureFluxPair (Y := HilbertVectorL2 (openCubeSet Q))
      (X := (physicalPotentialSpace Q).toSubmodule) :=
    pureFluxLoad (Y := HilbertVectorL2 (openCubeSet Q))
      (X := (physicalPotentialSpace Q).toSubmodule) (physicalConstantLoad Q e)
  have hβ : 0 ≤ β := inv_nonneg.mpr hα.le
  have hAnorm (y : C(K, ℝ)) : ‖A y‖ ≤ ‖y‖ / σ :=
    (physicalProjectedCoefficient_opNorm_le' Q σ hσ (R y)).trans
      (div_le_div_of_nonneg_right (physicalResponseRestriction_norm_le Q hQ y) hσ.le)
  let k0 : ℝ := ‖J‖ * (β * ‖f‖) ^ 2
  have hk0 : 0 ≤ k0 := by positivity
  let c1 : ℝ := k0 * σ⁻¹
  let c2 : ℝ := k0 * (σ⁻¹ * β * σ⁻¹)
  let c3 : ℝ := k0 * (σ⁻¹ * β * σ⁻¹ * β * σ⁻¹)
  let c4 : ℝ := k0 * (σ⁻¹ * β * σ⁻¹) ^ 2 * β
  have hσi : 0 ≤ σ⁻¹ := inv_nonneg.mpr hσ.le
  have hc1 : 0 ≤ c1 := by positivity
  have hc2 : 0 ≤ c2 := by positivity
  have hc3 : 0 ≤ c3 := by positivity
  have hc4 : 0 ≤ c4 := by positivity
  refine ⟨c1 + c2 + c3 + c4, by positivity, fun x y => ?_⟩
  have hB : ‖pureFluxBlockInverse α hα (A x)‖ ≤ β := pureFluxBlockInverse_opNorm_le hα (A x)
  have hN : ‖pureFluxBlockInverse α hα (A x + A y)‖ ≤ β :=
    pureFluxBlockInverse_opNorm_le hα (A x + A y)
  have hC : ‖pureFluxBlockOperator 0 (A y)‖ ≤ ‖y‖ / σ :=
    (pureFluxBlockInserted_opNorm_le (A y)).trans (hAnorm y)
  have hκ : 0 ≤ ‖y‖ / σ := div_nonneg (norm_nonneg _) hσ.le
  obtain ⟨h1, h2, h3, h4⟩ := drop_g1_bounds (pureFluxBlockInverse α hα (A x)) J
    (pureFluxBlockInverse α hα (A x + A y)) (pureFluxBlockOperator 0 (A y)) f hβ hκ hB hN hC
  have hy : 0 ≤ ‖y‖ := norm_nonneg _
  refine ⟨?_, ?_, ?_, ?_⟩
  · change ‖hilbertG1LinearTerm (pureFluxBlockInverse α hα (A x)) J f
      (pureFluxBlockOperator 0 (A y))‖ ≤ _
    refine h1.trans ?_
    have : ‖J‖ * (β * ‖f‖) ^ 2 * (‖y‖ / σ) = c1 * ‖y‖ := by
      simp only [c1, k0]; field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_right (by linarith) hy
  · change ‖hilbertG1HessianTerm (pureFluxBlockInverse α hα (A x)) J f
      (pureFluxBlockOperator 0 (A y))‖ ≤ _
    refine h2.trans ?_
    have : ‖J‖ * (β * ‖f‖) ^ 2 * (‖y‖ / σ * β * (‖y‖ / σ)) = c2 * ‖y‖ ^ 2 := by
      simp only [c2, k0]; field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  · change ‖hilbertG1CubicTerm (pureFluxBlockInverse α hα (A x)) J f
      (pureFluxBlockOperator 0 (A y))‖ ≤ _
    refine h3.trans ?_
    have : ‖J‖ * (β * ‖f‖) ^ 2 * (‖y‖ / σ * β * (‖y‖ / σ) * β * (‖y‖ / σ)) = c3 * ‖y‖ ^ 3 := by
      simp only [c3, k0]; field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  · change ‖hilbertG1QuarticTerm (pureFluxBlockInverse α hα (A x)) J f
      (pureFluxBlockOperator 0 (A y)) (pureFluxBlockInverse α hα (A x + A y))‖ ≤ _
    refine h4.trans ?_
    have : ‖J‖ * (β * ‖f‖) ^ 2 * (‖y‖ / σ * β * (‖y‖ / σ)) ^ 2 * β = c4 * ‖y‖ ^ 4 := by
      simp only [c4, k0]; field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)

/-- Integrability of the four terms at the scaled insertion `(a, s • G)`, `|s| ≤ 1`, and the
fourth-moment bound of the quartic remainder. -/
theorem drop_scaled_terms {K : Set (Vec 2)} [CompactSpace K]
    (Q : TriadicCube 2) (hQ : closure (openCubeSet Q) ⊆ K)
    (M : ABKModel 2) (m : ℤ) (σ : ℝ) (hσ : 0 < σ) (e : Vec 2)
    (h : ℝ) (hM : PlanarQ3Gaussian M h) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ s : ℝ, |s| ≤ 1 →
      Integrable (fun p : C(K, ℝ) × C(K, ℝ) =>
        physicalParityLinearObservable Q M.nu σ M.nu_pos hσ
          (physicalResponseRestriction Q hQ) e (p.1, s • p.2))
        (physicalParityProductLaw M m) ∧
      Integrable (fun p : C(K, ℝ) × C(K, ℝ) =>
        physicalParityHessianObservable Q M.nu σ M.nu_pos hσ
          (physicalResponseRestriction Q hQ) e (p.1, s • p.2))
        (physicalParityProductLaw M m) ∧
      Integrable (fun p : C(K, ℝ) × C(K, ℝ) =>
        physicalParityCubicObservable Q M.nu σ M.nu_pos hσ
          (physicalResponseRestriction Q hQ) e (p.1, s • p.2))
        (physicalParityProductLaw M m) ∧
      Integrable (fun p : C(K, ℝ) × C(K, ℝ) =>
        physicalParityQuarticObservable Q M.nu σ M.nu_pos hσ
          (physicalResponseRestriction Q hQ) e (p.1, s • p.2))
        (physicalParityProductLaw M m) ∧
      |∫ p : C(K, ℝ) × C(K, ℝ),
        physicalParityQuarticObservable Q M.nu σ M.nu_pos hσ
          (physicalResponseRestriction Q hQ) e (p.1, s • p.2)
        ∂(physicalParityProductLaw M m)| ≤ c * s ^ 4 := by
  obtain ⟨c, hc0, hc⟩ := drop_term_bounds Q hQ M.nu σ M.nu_pos hσ e
  obtain ⟨hlinC, hhessC, hcubC, hquartC, _⟩ :=
    physicalParity_observables_continuous' Q hQ M.nu σ M.nu_pos hσ e
  let μold : Measure (C(K, ℝ)) := physicalParityOldMarginal M m
  let μfresh : Measure (C(K, ℝ)) := physicalParityFreshMarginal M m
  haveI : IsFiniteMeasure μold := by
    change IsFiniteMeasure ((Cutoff.cutoffSampleLaw M).toMeasure.map (olderField K m))
    infer_instance
  haveI : IsFiniteMeasure μfresh := by
    change IsFiniteMeasure ((Cutoff.cutoffSampleLaw M).toMeasure.map
      (physicalParityFreshField (K := K) m))
    infer_instance
  have hFreshPoly : Integrable (fun z : C(K, ℝ) => (1 + ‖z‖) ^ 4) μfresh :=
    physicalParity_fresh_fourth_integrable' M h hM (K := K) m
  have hPoly : Integrable (fun p : C(K, ℝ) × C(K, ℝ) => (1 + ‖p.2‖) ^ 4)
      (μold.prod μfresh) := hFreshPoly.comp_snd μold
  have hMom : Integrable (fun p : C(K, ℝ) × C(K, ℝ) => ‖p.2‖ ^ 4) (μold.prod μfresh) := by
    refine hPoly.mono' (by fun_prop) ?_
    filter_upwards with p
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) (by linarith [norm_nonneg p.2]) 4
  have hM4 : 0 ≤ ∫ p : C(K, ℝ) × C(K, ℝ), ‖p.2‖ ^ 4 ∂(μold.prod μfresh) :=
    integral_nonneg fun p => by positivity
  refine ⟨c * ∫ p : C(K, ℝ) × C(K, ℝ), ‖p.2‖ ^ 4 ∂(μold.prod μfresh), mul_nonneg hc0 hM4,
    fun s hs => ?_⟩
  have hsc : Continuous (fun p : C(K, ℝ) × C(K, ℝ) => (p.1, s • p.2)) := by fun_prop
  have hpow (p : C(K, ℝ) × C(K, ℝ)) {k : ℕ} (hk : k ≤ 4) : ‖s • p.2‖ ^ k ≤ (1 + ‖p.2‖) ^ 4 := by
    have hn : ‖s • p.2‖ ≤ ‖p.2‖ := by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_of_le_one_left (norm_nonneg _) hs
    have h1 : 1 ≤ 1 + ‖p.2‖ := by linarith [norm_nonneg p.2]
    calc ‖s • p.2‖ ^ k ≤ (1 + ‖p.2‖) ^ k :=
          pow_le_pow_left₀ (norm_nonneg _) (by linarith) k
      _ ≤ (1 + ‖p.2‖) ^ 4 := pow_le_pow_right₀ h1 hk
  have dom (F : C(K, ℝ) × C(K, ℝ) → ℝ) (hF : Continuous F) {k : ℕ} (hk : k ≤ 4)
      (hb : ∀ x y : C(K, ℝ), ‖F (x, y)‖ ≤ c * ‖y‖ ^ k) :
      Integrable (fun p : C(K, ℝ) × C(K, ℝ) => F (p.1, s • p.2)) (μold.prod μfresh) := by
    refine (hPoly.const_mul c).mono' (hF.comp hsc).aestronglyMeasurable ?_
    filter_upwards with p
    calc ‖F (p.1, s • p.2)‖ ≤ c * ‖s • p.2‖ ^ k := hb _ _
      _ ≤ c * (1 + ‖p.2‖) ^ 4 := mul_le_mul_of_nonneg_left (hpow p hk) hc0
  refine ⟨dom _ hlinC (k := 1) (by norm_num) (fun x y => by simpa using (hc x y).1),
    dom _ hhessC (k := 2) (by norm_num) (fun x y => (hc x y).2.1),
    dom _ hcubC (k := 3) (by norm_num) (fun x y => (hc x y).2.2.1),
    dom _ hquartC (k := 4) (by norm_num) (fun x y => (hc x y).2.2.2), ?_⟩
  have hq4 : ∀ p : C(K, ℝ) × C(K, ℝ),
      ‖physicalParityQuarticObservable Q M.nu σ M.nu_pos hσ
        (physicalResponseRestriction Q hQ) e (p.1, s • p.2)‖ ≤ (c * s ^ 4) * ‖p.2‖ ^ 4 := by
    intro p
    refine ((hc p.1 (s • p.2)).2.2.2).trans ?_
    rw [norm_smul, Real.norm_eq_abs, mul_pow]
    have : |s| ^ 4 = s ^ 4 := by
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, pow_mul, sq_abs]
    rw [this]
    nlinarith [pow_nonneg (norm_nonneg p.2) 4]
  calc |∫ p : C(K, ℝ) × C(K, ℝ), _ ∂(μold.prod μfresh)|
      = ‖∫ p : C(K, ℝ) × C(K, ℝ), physicalParityQuarticObservable Q M.nu σ M.nu_pos hσ
          (physicalResponseRestriction Q hQ) e (p.1, s • p.2) ∂(μold.prod μfresh)‖ :=
        (Real.norm_eq_abs _).symm
    _ ≤ ∫ p : C(K, ℝ) × C(K, ℝ), (c * s ^ 4) * ‖p.2‖ ^ 4 ∂(μold.prod μfresh) :=
        norm_integral_le_of_norm_le (hMom.const_mul _) (Filter.Eventually.of_forall hq4)
    _ = (c * s ^ 4) * ∫ p : C(K, ℝ) × C(K, ℝ), ‖p.2‖ ^ 4 ∂(μold.prod μfresh) := by
        rw [integral_const_mul]
    _ = _ := by ring

end

end ASDExplicitGamma.Scalar
