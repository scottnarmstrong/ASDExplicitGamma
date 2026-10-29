module

public import ASDExplicitGamma.Gaussian.SquareBounds

/-! Finite weighted estimates in the common physical shell covariance space. -/

@[expose] public section
namespace ASDExplicitGamma.Gaussian
open Homogenization MeasureTheory ASDExplicitGamma.Inverse ASDExplicitGamma.Main
  ASDExplicitGamma.Response ASDExplicitGamma.Triadic ASDExplicitGamma.Variational
  ASDExplicitGamma.Model
open scoped BigOperators
noncomputable section

/-- The actual finite weighted family retains every covariance cross term.
Nonnegative weights suffice; normalized weights are an immediate specialization. -/
theorem square_shell_weighted_generator_bracket {ι : Type*}
    (s : Finset ι) (w : ι → ℝ) (Q : ι → TriadicCube 2) (j : ι → ℕ)
    (ν σ b : ℝ) (hν : 0 < ν) (hσ : 0 < σ) (L : {l : ℝ // 0 < l})
    (hw : ∀ a ∈ s, 0 ≤ w a)
    (hratio : ∀ a ∈ s, diagMeshRadius (Q a) (j a) / L.1 ≤ 1 / 243)
    (k : (a : ι) → ResponseCoefficient (openCubeSet (Q a))) :
    let T := fun a => squareTrace (Q a) ν σ (k a)
    let B := fun a => pureFluxSourceTileHistory (Q a) (j a)
      (responseFramePlanarCoefficientField ν σ (k a))
    let H := fun a => squareQ3Directions (Q a) b L
    let d := fun a n => fderiv ℝ (squareTrace (Q a) ν σ) (k a) (H a n)
    let Y := ∑ a ∈ s, w a * T a
    let ℒ := ∑ a ∈ s, w a * B a ^ 2 * (T a + 4)
    (1 / 2 : ℝ) * (∑ a ∈ s,
        w a * modelCovarianceTrace (squareTrace (Q a) ν σ) (H a) (k a)) ≤
      19 * (b ^ 2 / σ ^ 2) * ℒ ∧
    Summable (fun n => (∑ a ∈ s, w a * d a n) ^ 2) ∧
    (∑' n, (∑ a ∈ s, w a * d a n) ^ 2) ≤
      16 * (b ^ 2 / σ ^ 2) * Y * ℒ := by
  intro T B H d Y ℒ
  have hlocal (a : ι) (ha : a ∈ s) :=
    square_shell_generator_bracket (Q a) (j a) ν σ b hν hσ L (hratio a ha) (k a)
  have hT (a : ι) (_ha : a ∈ s) : 0 ≤ T a :=
    traceDefect_nonneg_of_ellipticFieldOn_triCube (div_pos hν hσ)
      (lemmaV_frameCoefficient_isEllipticOn (measurableSet_cubeSet (Q a))
        ν σ hν hσ (k a)) (by norm_num)
  have hgen := weighted_generator_of_local s w T B
    (fun a => (1 / 2 : ℝ) * modelCovarianceTrace (squareTrace (Q a) ν σ) (H a) (k a))
    (b ^ 2 / σ ^ 2) hw (fun a ha => (hlocal a ha).1)
  have hfinite (t : Finset ℕ) :
      (∑ n ∈ t, (∑ a ∈ s, w a * d a n) ^ 2) ≤
        16 * (b ^ 2 / σ ^ 2) * Y * ℒ := by
    let G : ι → EuclideanSpace ℝ t := fun a =>
      WithLp.toLp 2 (fun n => d a n)
    have hG (a : ι) (ha : a ∈ s) :
        ‖G a‖ ^ 2 ≤ 16 * (b ^ 2 / σ ^ 2) * T a * (B a ^ 2 * (T a + 4)) := by
      rw [EuclideanSpace.real_norm_sq_eq]
      have hf : (∑ n : t, (G a).ofLp n ^ 2) = ∑ n ∈ t, d a n ^ 2 := by
        simp only [G, WithLp.ofLp_toLp]
        exact Finset.sum_coe_sort t (fun n : ℕ => d a n ^ 2)
      rw [hf]
      have hbound := ((hlocal a ha).2.1.sum_le_tsum t
        (fun _ _ => sq_nonneg _)).trans (hlocal a ha).2.2
      convert hbound using 1 <;> ring
    have hg := weighted_bracket_of_local s w T B G (b ^ 2 / σ ^ 2)
      hw hT (by positivity) hG
    have hcoord (n : t) :
        (∑ a ∈ s, w a • G a).ofLp n = ∑ a ∈ s, w a * d a n := by
      simp [G]
    have heq : ‖∑ a ∈ s, w a • G a‖ ^ 2 =
        ∑ n ∈ t, (∑ a ∈ s, w a * d a n) ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      simp_rw [hcoord]
      exact Finset.sum_coe_sort t (fun n : ℕ => (∑ a ∈ s, w a * d a n) ^ 2)
    rw [heq] at hg
    exact hg
  have hnonneg (n : ℕ) : 0 ≤ (∑ a ∈ s, w a * d a n) ^ 2 := sq_nonneg _
  refine ⟨?_, summable_of_sum_le hnonneg hfinite,
    Real.tsum_le_of_sum_le hnonneg hfinite⟩
  calc
    _ = ∑ a ∈ s, w a * ((1 / 2 : ℝ) *
        modelCovarianceTrace (squareTrace (Q a) ν σ) (H a) (k a)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      ring
    _ ≤ _ := hgen

end
end ASDExplicitGamma.Gaussian
