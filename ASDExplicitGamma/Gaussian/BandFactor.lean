module

public import ASDExplicitGamma.Gaussian.ObservedCovariance
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Probability.Independence.CharacteristicFunction

/-! # One Hilbert covariance factor for a finite family of fresh shells -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal

namespace ASDExplicitGamma.Gaussian

/-- Hilbert direct sum of the finitely many shell factors. -/
abbrev BandHilbert (b : ℕ) := PiLp 2 (fun _ : Fin b => GaussianFactorL2 ℕ)

/-- Enumeration retains the shell label and the Gaussian direction label. -/
def bandIndex (b : ℕ) [NeZero b] : ℕ ≃ Fin b × ℕ :=
  (Nat.divModEquiv b).trans (Equiv.prodComm ℕ (Fin b))

/-- The joint factor, before any child restriction or centering is applied. -/
noncomputable def bandFactor {b : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : Fin b → GaussianFactorL2 ℕ →L[ℝ] E) : BandHilbert b →L[ℝ] E :=
  ∑ i, (T i).comp (PiLp.proj 2 (fun _ : Fin b => GaussianFactorL2 ℕ) i)

/-- Directions in different shells occupy orthogonal Hilbert coordinates. -/
noncomputable def bandDirections {b : ℕ} [NeZero b]
    (v : Fin b → ℕ → GaussianFactorL2 ℕ) (j : ℕ) : BandHilbert b :=
  PiLp.single 2 (bandIndex b j).1 (v (bandIndex b j).1 (bandIndex b j).2)

theorem bandFactor_single {b : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : Fin b → GaussianFactorL2 ℕ →L[ℝ] E) (i : Fin b) (z : GaussianFactorL2 ℕ) :
    bandFactor T (PiLp.single 2 i z) = T i z := by
  classical
  simp only [bandFactor, sum_apply, ContinuousLinearMap.comp_apply]
  change (∑ j, T j ((PiLp.single 2 i z : BandHilbert b) j)) = _
  rw [Finset.sum_eq_single i]
  · rw [PiLp.single_eq_same]
  · intro j _ hji
    rw [PiLp.single_eq_of_ne 2 hji, map_zero]
  · simp

/-- A finite band still has a square-summable Hilbert direction family. -/
theorem bandDirections_summable {b : ℕ} [NeZero b]
    (v : Fin b → ℕ → GaussianFactorL2 ℕ) (hv : ∀ i, Summable (fun j => ‖v i j‖ ^ 2)) :
    Summable (fun j => ‖bandDirections v j‖ ^ 2) := by
  have hp : Summable (fun p : Fin b × ℕ => ‖v p.1 p.2‖ ^ 2) := by
    rw [summable_prod_of_nonneg (fun _ => sq_nonneg _)]
    exact ⟨hv, Summable.of_finite⟩
  simpa only [Function.comp_def, bandDirections, PiLp.norm_single] using (bandIndex b).summable_iff.mpr hp

/-- The covariance contraction of the band is the sum of the shell contractions. -/
theorem bandFactor_covariance {b : ℕ} [NeZero b] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : Fin b → ℕ → GaussianFactorL2 ℕ) (hv : ∀ i, Summable (fun j => ‖v i j‖ ^ 2))
    (T : Fin b → GaussianFactorL2 ℕ →L[ℝ] E) (L : E →L[ℝ] ℝ) :
    (∑' j, (L (bandFactor T (bandDirections v j))) ^ 2) =
      ∑ i, ∑' j, (L (T i (v i j))) ^ 2 := by
  have hs (i : Fin b) : Summable (fun j => (L (T i (v i j))) ^ 2) := by
    simpa only [ContinuousLinearMap.comp_apply, Real.norm_eq_abs, sq_abs] using
      summable_sq_norm_gaussianDirections (hv i) (L.comp (T i))
  have hp : Summable (fun p : Fin b × ℕ => (L (T p.1 (v p.1 p.2))) ^ 2) := by
    rw [summable_prod_of_nonneg (fun _ => sq_nonneg _)]
    exact ⟨hs, Summable.of_finite⟩
  simp only [bandDirections, bandFactor_single]
  rw [(bandIndex b).tsum_eq (fun p : Fin b × ℕ => (L (T p.1 (v p.1 p.2))) ^ 2), hp.tsum_prod' hs]
  exact tsum_fintype _

/-- A finite sum of independent centered scalar Gaussians has the summed variance. -/
theorem independent_gaussian_sum_law {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
    (ρ : Measure Ω) [IsProbabilityMeasure ρ] (X : ι → Ω → ℝ) (s : ι → ℝ≥0)
    (hX : ∀ i, Measurable (X i)) (hi : iIndepFun X ρ)
    (hlaw : ∀ i, ρ.map (X i) = gaussianReal 0 (s i)) :
    ρ.map (fun ω => ∑ i, X i ω) = gaussianReal 0 (∑ i, s i) := by
  apply Measure.ext_of_charFun
  ext t
  rw [hi.charFun_map_fun_sum_eq_prod (fun i => (hX i).aemeasurable)]
  simp only [Finset.prod_apply, hlaw, charFun_gaussianReal, Complex.ofReal_zero,
    zero_mul, mul_zero, zero_sub]
  rw [← Complex.exp_sum]
  congr 1
  simp only [NNReal.coe_sum, Complex.ofReal_sum, Finset.sum_neg_distrib,
    Finset.sum_div, Finset.sum_mul]

end ASDExplicitGamma.Gaussian
