module

public import ASDExplicitGamma.Gaussian.SupMeanCompactPairConcentration
public import ASDExplicitGamma.Gaussian.NormSquareMoment

/-! Exponential integrability and moments of a correlated compact tensor pair. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open MeasureTheory ProbabilityTheory Gaussian
open scoped ENNReal
noncomputable section

/-- The countable Gaussian representation controls the MGF of the actual compact
pair supremum, including its exponential integrability. -/
theorem upper_cell_compact_pair_mgf {Ω K E F : Type*} [MeasurableSpace Ω]
    [TopologicalSpace K] [CompactSpace K] [Nonempty K] [SecondCountableTopology K]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [SecondCountableTopology E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [SecondCountableTopology F]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : Ω → C(K,E)) (W : Ω → C(K,F))
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hZ : Integrable (fun ω => ‖Z ω‖) μ) (hW : Integrable (fun ω => ‖W ω‖) μ)
    (hg : IsCenteredGaussianFamily μ
      (fun n ω => supMeanCompactPairProjection (Z ω) (W ω) a b n))
    (L lam : ℝ) (hL : 0 ≤ L)
    (hv : ∀ n, Var[(fun ω => supMeanCompactPairProjection (Z ω) (W ω) a b n); μ] ≤ L^2) :
    Integrable (fun ω => Real.exp (lam *
      (a*‖Z ω‖+b*‖W ω‖-∫ y, (a*‖Z y‖+b*‖W y‖) ∂μ))) μ ∧
    (∫ ω, Real.exp (lam *
      (a*‖Z ω‖+b*‖W ω‖-∫ y, (a*‖Z y‖+b*‖W y‖) ∂μ)) ∂μ) ≤
      Real.exp (lam^2*L^2/2) := by
  have he : gaussianRealizationSup (fun n ω =>
      supMeanCompactPairProjection (Z ω) (W ω) a b n) =
      (fun ω => a*‖Z ω‖+b*‖W ω‖) := by
    funext ω
    exact (supMean_compact_pair_eq_countable (Z ω) (W ω) a b ha hb).symm
  have hi := (hZ.const_mul a).add (hW.const_mul b)
  have hf : ∀ᵐ ω ∂μ, BddAbove (Set.range fun n =>
      supMeanCompactPairProjection (Z ω) (W ω) a b n) := by
    apply Filter.Eventually.of_forall
    intro ω
    refine ⟨a*‖Z ω‖+b*‖W ω‖, ?_⟩
    rintro y ⟨n,rfl⟩
    exact add_le_add (mul_le_mul_of_nonneg_left (supMean_compact_projection_le (Z ω) _) ha)
      (mul_le_mul_of_nonneg_left (supMean_compact_projection_le (W ω) _) hb)
  have hh := supMean_gaussian_countable_mgf μ _ hg L lam hL hv
    (by rw [he]; exact hi) hf
  simpa only [he] using hh

/-- A nonnegative integrable variable with the centered Gaussian MGF has all
positive moments. The mean and fluctuation are combined before physical scaling. -/
theorem upper_cell_nonneg_gaussian_moment {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : Ω → ℝ)
    (hZ0 : ∀ ω, 0 ≤ Z ω) (hZ : Integrable Z μ) (L p : ℝ)
    (hL : 0 < L) (hp : 1 ≤ p)
    (hmgf : ∀ lam : ℝ,
      Integrable (fun ω => Real.exp (lam*(Z ω-∫ y, Z y ∂μ))) μ ∧
      (∫ ω, Real.exp (lam*(Z ω-∫ y, Z y ∂μ)) ∂μ) ≤ Real.exp (lam^2*L^2/2)) :
    MemLp Z (ENNReal.ofReal p) μ ∧
    (eLpNorm Z (ENNReal.ofReal p) μ).toReal^2 ≤
      2*(∫ y, Z y ∂μ)^2 + 2*p*L^2 := by
  have hp0 : 0 < p := lt_of_lt_of_le (by norm_num) hp
  have hc : 0 < Real.sqrt p * L := mul_pos (Real.sqrt_pos.mpr hp0) hL
  have hs : (Real.sqrt p)^2 = p := Real.sq_sqrt hp0.le
  have he : (p / (Real.sqrt p * L))^2 * L^2 / 2 ≤ p := by
    have hroot : Real.sqrt p ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hp0)
    field_simp
    nlinarith only [hs, hp0, sq_nonneg L, sq_nonneg p]
  have hm := hmgf (p / (Real.sqrt p * L))
  have hf := positivePart_lpNorm_sq_le_of_exp μ hp0 hc
    (hZ.aestronglyMeasurable.sub aestronglyMeasurable_const) hm.1
    (hm.2.trans (Real.exp_le_exp.mpr he))
  have hh := lpNorm_sq_le_mean_add_positivePart μ hp hZ0 hZ hf.1
  refine ⟨hh.1, hh.2.trans ?_⟩
  have hfs : (eLpNorm (fun ω => max (Z ω - ∫ y, Z y ∂μ) 0)
      (ENNReal.ofReal p) μ).toReal^2 ≤ p*L^2 := by
    simpa only [mul_pow, hs, Pi.sub_apply] using hf.2
  nlinarith only [hfs]

end
end ASDExplicitGamma.Scalar
