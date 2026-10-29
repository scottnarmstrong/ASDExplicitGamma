module

public import ASDExplicitGamma.Model.BflatActualBessel
public import ASDExplicitGamma.Model.Q3DerivativeSmooth
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.MeanValue
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! # Covariance modes of the actual B-flat Dirichlet observations -/

@[expose] public section

open MeasureTheory Homogenization
open ASDExplicitGamma.Triadic
open scoped RealInnerProductSpace

namespace ASDExplicitGamma.Model

private theorem bflatProductCovariance_integrable (ell : ℝ) (f g h k : C(ℝ, ℝ)) :
    Integrable (fun p : bflatClosedRectangle × bflatClosedRectangle =>
      ASDExplicitGamma.q3Cov ((p.1.1 0 - p.2.1 0) / ell) * f (p.1.1 0) * g (p.2.1 0) *
        (ASDExplicitGamma.q3Cov ((p.1.1 1 - p.2.1 1) / ell) * h (p.1.1 1) * k (p.2.1 1)))
      (volume.prod volume) := by
  have hq : Continuous ASDExplicitGamma.q3Cov :=
    ASDExplicitGamma.Model.q3Cov_contDiff_two.continuous
  have hleftVec : Continuous (fun p : bflatClosedRectangle × bflatClosedRectangle => p.1.1) :=
    continuous_subtype_val.comp continuous_fst
  have hrightVec : Continuous (fun p : bflatClosedRectangle × bflatClosedRectangle => p.2.1) :=
    continuous_subtype_val.comp continuous_snd
  have hx0 : Continuous (fun p : bflatClosedRectangle × bflatClosedRectangle => p.1.1 0) :=
    (continuous_apply 0).comp hleftVec
  have hy0 : Continuous (fun p : bflatClosedRectangle × bflatClosedRectangle => p.2.1 0) :=
    (continuous_apply 0).comp hrightVec
  have hx1 : Continuous (fun p : bflatClosedRectangle × bflatClosedRectangle => p.1.1 1) :=
    (continuous_apply 1).comp hleftVec
  have hy1 : Continuous (fun p : bflatClosedRectangle × bflatClosedRectangle => p.2.1 1) :=
    (continuous_apply 1).comp hrightVec
  have hc : Continuous (fun p : bflatClosedRectangle × bflatClosedRectangle =>
      ASDExplicitGamma.q3Cov ((p.1.1 0 - p.2.1 0) / ell) * f (p.1.1 0) * g (p.2.1 0) *
        (ASDExplicitGamma.q3Cov ((p.1.1 1 - p.2.1 1) / ell) * h (p.1.1 1) * k (p.2.1 1))) := by
    exact (((((hq.comp ((hx0.sub hy0).div_const ell)).mul (f.continuous.comp hx0)).mul
      (g.continuous.comp hy0)).mul
      (((hq.comp ((hx1.sub hy1).div_const ell)).mul (h.continuous.comp hx1)).mul
        (k.continuous.comp hy1))))
  exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- The product-q3 covariance integral of separated coordinate weights factors into
the corresponding one-dimensional interval covariance forms. -/
theorem bflatProductCovariance_factorization (ell : ℝ)
    (f g h k : C(ℝ, ℝ)) :
    (∫ p : bflatClosedRectangle × bflatClosedRectangle,
      ASDExplicitGamma.q3Cov ((p.1.1 0 - p.2.1 0) / ell) * f (p.1.1 0) * g (p.2.1 0) *
        (ASDExplicitGamma.q3Cov ((p.1.1 1 - p.2.1 1) / ell) * h (p.1.1 1) * k (p.2.1 1))
      ∂(volume.prod volume)) =
    (∫ x in Set.Icc (-1/2 : ℝ) (1/2), ∫ y in Set.Icc (-1/2 : ℝ) (1/2),
        ASDExplicitGamma.q3Cov ((x - y) / ell) * f x * g y) *
      (∫ x in Set.Icc (-1/2 : ℝ) (1/2), ∫ y in Set.Icc (-1/2 : ℝ) (1/2),
        ASDExplicitGamma.q3Cov ((x - y) / ell) * h x * k y) := by
  let F : Vec 2 → Vec 2 → ℝ := fun x y =>
    ASDExplicitGamma.q3Cov ((x 0 - y 0) / ell) * f (x 0) * g (y 0) *
      (ASDExplicitGamma.q3Cov ((x 1 - y 1) / ell) * h (x 1) * k (y 1))
  let A : ℝ → ℝ → ℝ := fun x y =>
    ASDExplicitGamma.q3Cov ((x-y)/ell) * f x * g y
  let B : ℝ → ℝ → ℝ := fun x y =>
    ASDExplicitGamma.q3Cov ((x-y)/ell) * h x * k y
  have hq : Continuous ASDExplicitGamma.q3Cov :=
    ASDExplicitGamma.Model.q3Cov_contDiff_two.continuous
  have hFcont : Continuous (Function.uncurry F) := by
    dsimp [F]
    fun_prop (disch := assumption)
  have hGcont : Continuous (fun x : Vec 2 =>
      ∫ y in Gaussian.closedRectangle (-1/2) (1/2) (-1/2) (1/2), F x y) := by
    apply continuous_parametric_integral_of_continuous hFcont
    exact Gaussian.closedRectangle_isCompact _ _ _ _
  have hclosed : MeasurableSet
      (Gaussian.closedRectangle (-1/2) (1/2) (-1/2) (1/2)) :=
    (Gaussian.closedRectangle_isCompact _ _ _ _).isClosed.measurableSet
  have hproduct := bflatProductCovariance_integrable ell f g h k
  have hiterated :
      (∫ x : bflatClosedRectangle,
        ∫ y : bflatClosedRectangle, F x.1 y.1 ∂volume ∂volume) =
        ∫ p : bflatClosedRectangle × bflatClosedRectangle, F p.1.1 p.2.1
          ∂(volume.prod volume) :=
    (integral_prod (fun p : bflatClosedRectangle × bflatClosedRectangle =>
      F p.1.1 p.2.1) hproduct).symm
  have hinner (x : Vec 2) :
      (∫ y : bflatClosedRectangle, F x y.1) =
        ∫ y in Gaussian.closedRectangle (-1/2) (1/2) (-1/2) (1/2), F x y := by
    rw [integral_subtype hclosed]
  have houter :
      (∫ x : bflatClosedRectangle,
        ∫ y : bflatClosedRectangle, F x.1 y.1 ∂volume ∂volume) =
        ∫ x in Gaussian.closedRectangle (-1/2) (1/2) (-1/2) (1/2),
          ∫ y in Gaussian.closedRectangle (-1/2) (1/2) (-1/2) (1/2),
            F x y ∂volume ∂volume := by
    calc
      _ = ∫ x : bflatClosedRectangle,
          ∫ y in Gaussian.closedRectangle (-1/2) (1/2) (-1/2) (1/2),
            F x.1 y ∂volume ∂volume := by
        congr 1
        funext x
        exact hinner x.1
      _ = _ := by
        exact integral_subtype hclosed
          (fun x : Vec 2 =>
            ∫ y in Gaussian.closedRectangle (-1/2) (1/2) (-1/2) (1/2), F x y)
  have hinnerCoords (x y : ℝ) :
      (∫ z in Gaussian.closedRectangle (-1/2) (1/2) (-1/2) (1/2),
        F ![x,y] z ∂volume) =
        ∫ u in Set.Icc (-1/2 : ℝ) (1/2), ∫ v in Set.Icc (-1/2 : ℝ) (1/2),
          F ![x,y] ![u,v] := by
    rw [← Gaussian.rectangle_restrict_eq]
    exact Gaussian.rectangle_integral_eq (-1/2) (1/2) (-1/2) (1/2)
      (fun z => F ![x,y] z) (by
        dsimp [F]
        fun_prop (disch := assumption))
  have hcoords :
      (∫ x in Gaussian.closedRectangle (-1/2) (1/2) (-1/2) (1/2),
        ∫ y in Gaussian.closedRectangle (-1/2) (1/2) (-1/2) (1/2),
          F x y ∂volume ∂volume) =
        ∫ x in Set.Icc (-1/2 : ℝ) (1/2), ∫ y in Set.Icc (-1/2 : ℝ) (1/2),
          ∫ u in Set.Icc (-1/2 : ℝ) (1/2), ∫ v in Set.Icc (-1/2 : ℝ) (1/2),
            F ![x,y] ![u,v] := by
    calc
      _ = ∫ x in Gaussian.openRectangle (-1/2) (1/2) (-1/2) (1/2),
          ∫ y in Gaussian.closedRectangle (-1/2) (1/2) (-1/2) (1/2),
            F x y ∂volume ∂volume := by
        rw [← Gaussian.rectangle_restrict_eq]
      _ = ∫ x in Set.Icc (-1/2 : ℝ) (1/2), ∫ y in Set.Icc (-1/2 : ℝ) (1/2),
          ∫ z in Gaussian.closedRectangle (-1/2) (1/2) (-1/2) (1/2),
            F ![x,y] z ∂volume :=
        Gaussian.rectangle_integral_eq (-1/2) (1/2) (-1/2) (1/2)
          (fun x => ∫ z in Gaussian.closedRectangle (-1/2) (1/2) (-1/2) (1/2),
            F x z ∂volume) hGcont
      _ = _ := by
        simp_rw [hinnerCoords]
  have hfactor :
      (∫ x in Set.Icc (-1/2 : ℝ) (1/2), ∫ y in Set.Icc (-1/2 : ℝ) (1/2),
        ∫ u in Set.Icc (-1/2 : ℝ) (1/2), ∫ v in Set.Icc (-1/2 : ℝ) (1/2), F ![x,y] ![u,v]) =
        (∫ x in Set.Icc (-1/2 : ℝ) (1/2), ∫ u in Set.Icc (-1/2 : ℝ) (1/2), A x u) *
          (∫ y in Set.Icc (-1/2 : ℝ) (1/2), ∫ v in Set.Icc (-1/2 : ℝ) (1/2), B y v) := by
    let μ : Measure ℝ := volume.restrict (Set.Icc (-1/2 : ℝ) (1/2))
    change (∫ x, ∫ y, ∫ u, ∫ v, A x u * B y v ∂μ ∂μ ∂μ ∂μ) = _
    calc
      _ = ∫ x, ∫ y, ∫ u, A x u * (∫ v, B y v ∂μ) ∂μ ∂μ ∂μ := by
        congr 1
        funext x
        congr 1
        funext y
        congr 1
        funext u
        rw [integral_const_mul]
      _ = ∫ x, ∫ y, (∫ u, A x u ∂μ) * (∫ v, B y v ∂μ) ∂μ ∂μ := by
        congr 1
        funext x
        congr 1
        funext y
        rw [integral_mul_const]
      _ = ∫ x, (∫ u, A x u ∂μ) * (∫ y, ∫ v, B y v ∂μ ∂μ) ∂μ := by
        congr 1
        funext x
        rw [integral_const_mul]
      _ = _ := by rw [integral_mul_const]
  calc
    _ = ∫ x : bflatClosedRectangle,
        ∫ y : bflatClosedRectangle, F x.1 y.1 ∂volume ∂volume := hiterated.symm
    _ = _ := by rw [houter, hcoords, hfactor]

theorem bflatModeObservationWeight_zero_apply (m n : ℕ) (x : bflatClosedRectangle) :
    bflatModeObservationWeight 0 m n x =
      (2 * Real.pi * (n + 1 : ℕ) /
          Real.sqrt (Real.pi^2 * ((m + 1 : ℕ)^2 + (n + 1 : ℕ)^2))) *
        (Real.sin (Real.pi * (m + 1 : ℕ) * (x.1 0 + 1/2)) *
          Real.cos (Real.pi * (n + 1 : ℕ) * (x.1 1 + 1/2))) := by
  simp [bflatModeObservationWeight, bflatModeDerivative, cubeFreq, cubeEig,
    Torus.boxMode, cubeCorner, cubeScaleFactor, bflatUnitSquare, bflatSquareModeIndex,
    Torus.natVec, bflatJEntry]
  ring_nf

theorem bflatModeObservationWeight_one_apply (m n : ℕ) (x : bflatClosedRectangle) :
    bflatModeObservationWeight 1 m n x =
      -(2 * Real.pi * (m + 1 : ℕ) /
          Real.sqrt (Real.pi^2 * ((m + 1 : ℕ)^2 + (n + 1 : ℕ)^2))) *
        (Real.cos (Real.pi * (m + 1 : ℕ) * (x.1 0 + 1/2)) *
          Real.sin (Real.pi * (n + 1 : ℕ) * (x.1 1 + 1/2))) := by
  simp [bflatModeObservationWeight, bflatModeDerivative, cubeFreq, cubeEig,
    Torus.boxMode, cubeCorner, cubeScaleFactor, bflatUnitSquare, bflatSquareModeIndex,
    Torus.natVec, bflatJEntry]
  ring_nf

end ASDExplicitGamma.Model
