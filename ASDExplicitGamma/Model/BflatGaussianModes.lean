module

public import ASDExplicitGamma.Gaussian.Q3ModelH3Realization
public import ASDExplicitGamma.Gaussian.ObservedCovariance
public import ASDExplicitGamma.Model.BflatProjection
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.Prod

/-! # Actual Gaussian covariance of B-flat square observations -/

@[expose] public section

open MeasureTheory Homogenization
open scoped Topology RealInnerProductSpace

namespace ASDExplicitGamma.Model

abbrev bflatClosedRectangle :=
  ASDExplicitGamma.Gaussian.closedRectangle (-1 / 2) (1 / 2) (-1 / 2) (1 / 2)

noncomputable instance instBflatClosedRectangleMeasureSpace :
    MeasureSpace bflatClosedRectangle := Measure.Subtype.measureSpace

noncomputable instance instBflatClosedRectangleFinite :
    IsFiniteMeasure (volume : Measure bflatClosedRectangle) := by
  refine ⟨?_⟩
  rw [Measure.Subtype.volume_univ
    (ASDExplicitGamma.Gaussian.closedRectangle_isCompact
      (-1/2) (1/2) (-1/2) (1/2)).isClosed.nullMeasurableSet]
  exact (ASDExplicitGamma.Gaussian.closedRectangle_isCompact
    (-1/2) (1/2) (-1/2) (1/2)).measure_lt_top

/-- Integration against a continuous square weight, represented as an L² inner product. -/
noncomputable def bflatObservation (w : C(bflatClosedRectangle, ℝ)) :
    C(bflatClosedRectangle, ℝ) →L[ℝ] ℝ :=
  (innerSL ℝ (ContinuousMap.toLp 2 (volume : Measure bflatClosedRectangle) ℝ w)).comp
    (ContinuousMap.toLp 2 (volume : Measure bflatClosedRectangle) ℝ)

theorem bflatObservation_apply (w f : C(bflatClosedRectangle, ℝ)) :
    bflatObservation w f = ∫ x : bflatClosedRectangle, f x * w x := by
  change inner ℝ (ContinuousMap.toLp 2 (volume : Measure bflatClosedRectangle) ℝ w)
    (ContinuousMap.toLp 2 (volume : Measure bflatClosedRectangle) ℝ f) = _
  rw [ContinuousMap.inner_toLp]
  simp only [starRingEnd_apply, star_trivial]

private theorem bflat_integral_const {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsFiniteMeasure ν] (c : ℝ) :
    ∫ _ : X, c ∂ν = ν.real Set.univ * c := by
  rw [integral_const, smul_eq_mul]

/-- The exact covariance of any two continuous square observations of the actual
product-q3 H³ Gaussian realization. The series is integrated using its summable
direction norms, then the already proved pointwise kernel covariance is applied. -/
theorem bflatObservation_covariance {ι : Type*} [Countable ι]
    (e : HilbertBasis ι ℝ Gaussian.WhiteNoise)
    (β : ℝ) (L : {l : ℝ // 0 < l})
    (w z : C(bflatClosedRectangle, ℝ)) :
    (∑' n : ℕ,
      bflatObservation w (Gaussian.q3H3RangeValue (-1/2) (1/2) (-1/2) (1/2) β L
        (Gaussian.q3H3Directions (-1/2) (1/2) (-1/2) (1/2) β L e n)) *
      bflatObservation z (Gaussian.q3H3RangeValue (-1/2) (1/2) (-1/2) (1/2) β L
        (Gaussian.q3H3Directions (-1/2) (1/2) (-1/2) (1/2) β L e n))) =
    ∫ p : bflatClosedRectangle × bflatClosedRectangle,
      β^2 * ASDExplicitGamma.q3Cov ((p.1.1 0 - p.2.1 0) / L.1) *
        ASDExplicitGamma.q3Cov ((p.1.1 1 - p.2.1 1) / L.1) * w p.1 * z p.2
      ∂((volume : Measure bflatClosedRectangle).prod volume) := by
  let T := Gaussian.q3H3RangeValue (-1/2) (1/2) (-1/2) (1/2) β L
  let d := Gaussian.q3H3Directions (-1/2) (1/2) (-1/2) (1/2) β L e
  let f (n : ℕ) : C(bflatClosedRectangle, ℝ) := T (d n)
  let F (n : ℕ) (p : bflatClosedRectangle × bflatClosedRectangle) : ℝ :=
    (f n p.1 * w p.1) * (f n p.2 * z p.2)
  let μ : Measure bflatClosedRectangle := volume
  let μ₂ := μ.prod μ
  have hD : Summable (fun n : ℕ => ‖d n‖ ^ 2) := by
    dsimp [d]
    exact Gaussian.q3H3Directions_summable (-1/2) (1/2) (-1/2) (1/2) β L e
  have hFcont (n : ℕ) : Continuous (F n) := by
    change Continuous (fun p : bflatClosedRectangle × bflatClosedRectangle =>
      (f n p.1 * w p.1) * (f n p.2 * z p.2))
    fun_prop
  have hFint (n : ℕ) : Integrable (F n) μ₂ :=
    (hFcont n).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  let C : ℝ := Gaussian.rectangleSobolevConstant (-1/2) (1/2) (-1/2) (1/2)
  have hCnonneg : 0 ≤ C := by
    dsimp [C, Gaussian.rectangleSobolevConstant]
    exact Real.sqrt_nonneg _
  have hTbound (n : ℕ) : ‖f n‖ ≤ C * ‖d n‖ := by
    change ‖T (d n)‖ ≤ C * ‖d n‖
    change ‖(Gaussian.q3H3RangeC1 (-1/2) (1/2) (-1/2) (1/2) β L (d n)) 0‖ ≤ _
    calc
      _ ≤ ‖Gaussian.q3H3RangeC1 (-1/2) (1/2) (-1/2) (1/2) β L (d n)‖ :=
        norm_le_pi_norm _ 0
      _ ≤ C * ‖d n‖ := Gaussian.q3H3RangeC1_norm_le
        (-1/2) (1/2) (-1/2) (1/2) β (by norm_num) (by norm_num) L (d n)
  have hFbound (n : ℕ) (p : bflatClosedRectangle × bflatClosedRectangle) :
      ‖F n p‖ ≤ (C^2 * ‖w‖ * ‖z‖) * ‖d n‖^2 := by
    dsimp [F]
    rw [abs_mul, abs_mul, abs_mul]
    have hfx : |f n p.1| ≤ C * ‖d n‖ := by
      calc
        |f n p.1| = ‖f n p.1‖ := by rw [Real.norm_eq_abs]
        _ ≤ ‖f n‖ := ContinuousMap.norm_coe_le_norm _ _
        _ ≤ C * ‖d n‖ := hTbound n
    have hfy : |f n p.2| ≤ C * ‖d n‖ := by
      calc
        |f n p.2| = ‖f n p.2‖ := by rw [Real.norm_eq_abs]
        _ ≤ ‖f n‖ := ContinuousMap.norm_coe_le_norm _ _
        _ ≤ C * ‖d n‖ := hTbound n
    have hw : |w p.1| ≤ ‖w‖ := by
      calc
        |w p.1| = ‖w p.1‖ := by rw [Real.norm_eq_abs]
        _ ≤ ‖w‖ := ContinuousMap.norm_coe_le_norm _ _
    have hz : |z p.2| ≤ ‖z‖ := by
      calc
        |z p.2| = ‖z p.2‖ := by rw [Real.norm_eq_abs]
        _ ≤ ‖z‖ := ContinuousMap.norm_coe_le_norm _ _
    have hnTd : 0 ≤ C * ‖d n‖ := mul_nonneg hCnonneg (norm_nonneg _)
    have hleft := mul_le_mul hfx hw (abs_nonneg _) hnTd
    have hright := mul_le_mul hfy hz (abs_nonneg _) hnTd
    calc
      |f n p.1| * |w p.1| * (|f n p.2| * |z p.2|) =
          (|f n p.1| * |w p.1|) * (|f n p.2| * |z p.2|) := by ring
      _ ≤ ((C * ‖d n‖) * ‖w‖) * ((C * ‖d n‖) * ‖z‖) :=
        mul_le_mul hleft hright
          (mul_nonneg (abs_nonneg (f n p.2)) (abs_nonneg (z p.2)))
          (mul_nonneg hnTd (norm_nonneg w))
      _ = (C^2 * ‖w‖ * ‖z‖) * ‖d n‖^2 := by ring
  have hFsum : Summable (fun n : ℕ => ∫ p, ‖F n p‖ ∂μ₂) := by
    apply Summable.of_nonneg_of_le
      (fun n => integral_nonneg (fun p => norm_nonneg (F n p)))
      (fun n => ?_)
      (hD.mul_left ((μ₂.real Set.univ) * (C^2 * ‖w‖ * ‖z‖)))
    calc
      ∫ p, ‖F n p‖ ∂μ₂ ≤ ∫ p, (C^2 * ‖w‖ * ‖z‖) * ‖d n‖^2 ∂μ₂ := by
        apply integral_mono (hFint n).norm (integrable_const _)
        intro p
        exact hFbound n p
      _ = (μ₂.real Set.univ) * ((C^2 * ‖w‖ * ‖z‖) * ‖d n‖^2) := by
        exact bflat_integral_const μ₂ _
      _ = (μ₂.real Set.univ) * (C^2 * ‖w‖ * ‖z‖) * ‖d n‖^2 := by ring
  have hsumint := integral_tsum_of_summable_integral_norm hFint hFsum
  have hpoint (p : bflatClosedRectangle × bflatClosedRectangle) :
      (∑' n : ℕ, F n p) =
        β^2 * ASDExplicitGamma.q3Cov ((p.1.1 0 - p.2.1 0) / L.1) *
          ASDExplicitGamma.q3Cov ((p.1.1 1 - p.2.1 1) / L.1) * w p.1 * z p.2 := by
    change (∑' n : ℕ, (f n p.1 * w p.1) * (f n p.2 * z p.2)) = _
    calc
      _ = (∑' n : ℕ, f n p.1 * f n p.2) * (w p.1 * z p.2) := by
        rw [← tsum_mul_right]
        apply tsum_congr
        intro n
        ring
      _ = _ := by
        have hcov := Gaussian.q3H3Directions_covariance (-1/2) (1/2) (-1/2) (1/2) β
          (by norm_num) (by norm_num) L e p.1 p.2
        change (∑' n : ℕ, T (d n) p.1 * T (d n) p.2) = _ at hcov
        rw [hcov]
        ring
  calc
    _ = ∑' n : ℕ, ∫ p, F n p ∂μ₂ := by
      apply tsum_congr
      intro n
      change bflatObservation w (T (d n)) * bflatObservation z (T (d n)) = _
      rw [bflatObservation_apply, bflatObservation_apply]
      symm
      exact integral_prod_mul (fun x => T (d n) x * w x) (fun y => T (d n) y * z y)
    _ = ∫ p, ∑' n : ℕ, F n p ∂μ₂ := hsumint
    _ = _ := by
      rw [show (fun p : bflatClosedRectangle × bflatClosedRectangle =>
        ∑' n : ℕ, F n p) = fun p => β^2 * ASDExplicitGamma.q3Cov
          ((p.1.1 0 - p.2.1 0) / L.1) * ASDExplicitGamma.q3Cov
          ((p.1.1 1 - p.2.1 1) / L.1) * w p.1 * z p.2 from funext hpoint]

end ASDExplicitGamma.Model
