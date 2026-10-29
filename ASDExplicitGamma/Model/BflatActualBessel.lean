module

public import ASDExplicitGamma.Model.BflatModeObservation
public import ASDExplicitGamma.Gaussian.Q3H3Series
public import ASDExplicitGamma.Gaussian.BilinearCovariance

/-! # Actual Bessel lower bounds for q3 Gaussian projections -/

@[expose] public section

open MeasureTheory Homogenization
open scoped BigOperators RealInnerProductSpace

namespace ASDExplicitGamma.Model

noncomputable instance instBflatQ3H3RangeInnerProductSpace (β : ℝ)
    (L : {l : ℝ // 0 < l}) :
    InnerProductSpace ℝ (Gaussian.Q3H3Range (-1/2) (1/2) (-1/2) (1/2) β L) :=
  Gaussian.instQ3H3RangeInnerProductSpace (-1/2) (1/2) (-1/2) (1/2) β L

noncomputable abbrev bflatDirichletClosedSubmodule :=
  Homogenization.PotentialZeroTraceHilbert.closedSubmodule
    (M := Homogenization.PotentialSolenoidalL2Data.ofSubmoduleClosures
      bflatSquareObservationDomain)

noncomputable def bflatProjectedSourceLinear (i : Fin 2) (β : ℝ)
    (L : {l : ℝ // 0 < l}) :
    Gaussian.Q3H3Range (-1/2) (1/2) (-1/2) (1/2) β L →L[ℝ]
      HilbertVectorL2 bflatSquareObservationDomain :=
  (bflatDirichletClosedSubmodule.toSubmodule.starProjection).comp
    ((bflatSourceFieldClass i).comp
      (Gaussian.q3H3RangeValue (-1/2) (1/2) (-1/2) (1/2) β L))

noncomputable def bflatModeObservationLinear (i : Fin 2) (m n : ℕ) (β : ℝ)
    (L : {l : ℝ // 0 < l}) :
    Gaussian.Q3H3Range (-1/2) (1/2) (-1/2) (1/2) β L →L[ℝ] ℝ :=
  (bflatObservation (bflatModeObservationWeight i m n)).comp
    (Gaussian.q3H3RangeValue (-1/2) (1/2) (-1/2) (1/2) β L)

noncomputable def bflatModeSeriesVariance {ι : Type*} [Countable ι]
    (e : HilbertBasis ι ℝ Gaussian.WhiteNoise) (i : Fin 2) (m n : ℕ)
    (β : ℝ) (L : {l : ℝ // 0 < l}) : ℝ :=
  ∑' k : ℕ,
    (bflatModeObservationLinear i m n β L
      (Gaussian.q3H3Directions (-1/2) (1/2) (-1/2) (1/2) β L e k)) ^ 2

theorem bflatModeSeriesVariance_eq_covariance_integral {ι : Type*} [Countable ι]
    (e : HilbertBasis ι ℝ Gaussian.WhiteNoise) (i : Fin 2) (m n : ℕ)
    (β : ℝ) (L : {l : ℝ // 0 < l}) :
    bflatModeSeriesVariance e i m n β L =
      ∫ p : bflatClosedRectangle × bflatClosedRectangle,
        β^2 * ASDExplicitGamma.q3Cov ((p.1.1 0 - p.2.1 0) / L.1) *
          ASDExplicitGamma.q3Cov ((p.1.1 1 - p.2.1 1) / L.1) *
          bflatModeObservationWeight i m n p.1 * bflatModeObservationWeight i m n p.2
        ∂((volume : Measure bflatClosedRectangle).prod volume) := by
  unfold bflatModeSeriesVariance bflatModeObservationLinear
  simpa only [ContinuousLinearMap.comp_apply, pow_two] using
    bflatObservation_covariance e β L
      (bflatModeObservationWeight i m n) (bflatModeObservationWeight i m n)

end ASDExplicitGamma.Model
