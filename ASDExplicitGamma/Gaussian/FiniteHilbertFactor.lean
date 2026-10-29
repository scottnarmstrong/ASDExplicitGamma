module

public import ASDExplicitGamma.Gaussian.BandFactor
public import ASDExplicitGamma.Gaussian.H3Centering

/-! # Finite direct sums of possibly different Hilbert covariance factors -/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace ASDExplicitGamma.Gaussian

section
variable {b : ℕ} (V : Fin b → Type*) [∀ i, NormedAddCommGroup (V i)]
  [∀ i, NormedSpace ℝ (V i)]

abbrev FiniteHilbert := PiLp 2 V

noncomputable def finiteFactor {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (T : ∀ i, V i →L[ℝ] F) : FiniteHilbert V →L[ℝ] F :=
  ∑ i, (T i).comp (PiLp.proj 2 V i)

noncomputable def finiteDirections [NeZero b] (v : ∀ i, ℕ → V i) (j : ℕ) : FiniteHilbert V :=
  PiLp.single 2 (bandIndex b j).1 (v (bandIndex b j).1 (bandIndex b j).2)

theorem finiteFactor_single {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (T : ∀ i, V i →L[ℝ] F) (i : Fin b) (z : V i) :
    finiteFactor V T (PiLp.single 2 i z) = T i z := by
  classical
  simp only [finiteFactor, sum_apply, ContinuousLinearMap.comp_apply]
  change (∑ j, T j ((PiLp.single 2 i z : FiniteHilbert V) j)) = _
  rw [Finset.sum_eq_single i]
  · rw [PiLp.single_eq_same]
  · intro j _ hji
    rw [PiLp.single_eq_of_ne 2 hji, map_zero]
  · simp

omit [∀ i, NormedSpace ℝ (V i)] in
theorem finiteDirections_summable [NeZero b] (v : ∀ i, ℕ → V i)
    (hv : ∀ i, Summable (fun j => ‖v i j‖ ^ 2)) :
    Summable (fun j => ‖finiteDirections V v j‖ ^ 2) := by
  have hp : Summable (fun p : Fin b × ℕ => ‖v p.1 p.2‖ ^ 2) := by
    rw [summable_prod_of_nonneg (fun _ => sq_nonneg _)]
    exact ⟨hv, Summable.of_finite⟩
  simpa only [Function.comp_def, finiteDirections, PiLp.norm_single] using
    (bandIndex b).summable_iff.mpr hp

/-- Every physical band observation has the sum of the independent shell variances. -/
theorem finiteFactor_covariance [NeZero b] {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (v : ∀ i, ℕ → V i) (hv : ∀ i, Summable (fun j => ‖v i j‖ ^ 2))
    (T : ∀ i, V i →L[ℝ] F) (L : F →L[ℝ] ℝ) :
    (∑' j, (L (finiteFactor V T (finiteDirections V v j))) ^ 2) =
      ∑ i, ∑' j, (L (T i (v i j))) ^ 2 := by
  have hs (i : Fin b) : Summable (fun j => (L (T i (v i j))) ^ 2) := by
    simpa only [ContinuousLinearMap.comp_apply, Real.norm_eq_abs, sq_abs] using
      summable_sq_norm_gaussianDirections (hv i) (L.comp (T i))
  have hp : Summable (fun p : Fin b × ℕ => (L (T p.1 (v p.1 p.2))) ^ 2) := by
    rw [summable_prod_of_nonneg (fun _ => sq_nonneg _)]
    exact ⟨hs, Summable.of_finite⟩
  simp only [finiteDirections, finiteFactor_single]
  rw [(bandIndex b).tsum_eq (fun p : Fin b × ℕ => (L (T p.1 (v p.1 p.2))) ^ 2), hp.tsum_prod' hs]
  exact tsum_fintype _

end
end ASDExplicitGamma.Gaussian
