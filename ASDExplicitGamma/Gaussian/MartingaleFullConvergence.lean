module

public import ASDExplicitGamma.Gaussian.IndependentMartingale
public import Mathlib.Probability.Martingale.Convergence
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-! # Full almost-sure convergence from a strong martingale subsequence -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal

namespace ASDExplicitGamma.Gaussian

/-- Scalar convergence of distances to a countable dense set upgrades one strongly convergent
subsequence of an L¹-bounded martingale to convergence of the full sequence. -/
theorem martingale_ae_tendsto_of_subseq {Ω E : Type*} {m : MeasurableSpace Ω}
    (μ : Measure Ω) [IsProbabilityMeasure μ] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [SecondCountableTopology E] {ℱ : Filtration ℕ m} (S : ℕ → Ω → E)
    (hS : Martingale S ℱ μ) (R : ℝ≥0) (hR : ∀ n, eLpNorm (S n) 1 μ ≤ R)
    (X : Ω → E) (ns : ℕ → ℕ) (hns : Tendsto ns atTop atTop)
    (hsub : ∀ᵐ ω ∂μ, Tendsto (fun n => S (ns n) ω) atTop (𝓝 (X ω))) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => S n ω) atTop (𝓝 (X ω)) := by
  obtain ⟨a, ha⟩ := TopologicalSpace.exists_dense_seq (α := E)
  have hshift (j : ℕ) : Martingale (fun n ω => S n ω - a j) ℱ μ :=
    hS.sub (martingale_const ℱ μ (a j))
  have hnorm (j : ℕ) : Submartingale (fun n ω => ‖S n ω - a j‖) ℱ μ :=
    martingale_norm_submartingale μ _ (hshift j) (fun n => (hshift j).integrable n)
  have hb (j n : ℕ) : eLpNorm (fun ω => ‖S n ω - a j‖) 1 μ ≤ (R + ‖a j‖₊ : ℝ≥0) := by
    have hsm : AEStronglyMeasurable (fun ω => S n ω - a j) μ :=
      (((hS.1 n).mono (ℱ.le n)).sub stronglyMeasurable_const).aestronglyMeasurable
    rw [eLpNorm_norm (fun ω => S n ω - a j) hsm]
    calc
      _ ≤ eLpNorm (S n) 1 μ + eLpNorm (fun _ : Ω => a j) 1 μ := eLpNorm_sub_le le_rfl
      _ ≤ R + eLpNorm (fun _ : Ω => a j) 1 μ := add_le_add (hR n) le_rfl
      _ = _ := by simp [eLpNorm_const', enorm_eq_nnnorm]
  have hae : ∀ᵐ ω ∂μ, ∀ j : ℕ, ∃ c, Tendsto (fun n => ‖S n ω - a j‖) atTop (𝓝 c) :=
    ae_all_iff.mpr fun j => (hnorm j).exists_ae_tendsto_of_bdd (hb j)
  filter_upwards [hae, hsub] with ω hω hs
  have hd (j : ℕ) : Tendsto (fun n => dist (S n ω) (a j)) atTop (𝓝 (dist (X ω) (a j))) := by
    obtain ⟨c, hc⟩ := hω j
    have hsc := (hs.sub_const (a j)).norm
    have he : c = ‖X ω - a j‖ := tendsto_nhds_unique (hc.comp hns) hsc
    rw [he] at hc
    simpa only [dist_eq_norm] using hc
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨j, hj⟩ := ha.exists_dist_lt (X ω) (show 0 < ε / 3 by linarith)
  have hsmall := (hd j).eventually_lt_const (show dist (X ω) (a j) < 2 * ε / 3 by linarith)
  filter_upwards [hsmall] with n hn
  exact (dist_triangle_right (S n ω) (X ω) (a j)).trans_lt (by linarith)

end ASDExplicitGamma.Gaussian
