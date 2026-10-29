module

public import ASDExplicitGamma.Triadic.PlanarPositiveGradient
public import ASDExplicitGamma.Triadic.VectorHaar
import Homogenization.Sobolev.Foundations.ZeroTraceAverages
import Homogenization.Sobolev.Foundations.CubePoisson.AnalyticInput

/-! Vector-valued duality estimates used by the planar Dirichlet bridges. -/

@[expose] public section

noncomputable section

open Homogenization MeasureTheory
open scoped BigOperators ENNReal

namespace ASDExplicitGamma.Triadic

/-- Every component of the weak gradient of a zero-trace function has zero
average on the cube. -/
theorem cubeAverage_h10_gradient_eq_zero (Q : TriadicCube 2)
    (u : H10Function (openCubeSet Q)) (i : Fin 2) :
    cubeAverage Q (fun x => u.toH1Function.grad x i) = 0 := by
  have hfinite : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) := by
    simpa [volumeMeasureOn] using
      (Homogenization.isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume
  have hz : u.toH1Function.averageGradient = 0 :=
    @Homogenization.H10Function.averageGradient_eq_zero 2 (openCubeSet Q) hfinite u
  have hzi := congrFun hz i
  rw [cubeAverage_eq_integralAverage_openCubeSet Q]
  simpa [H1Function.averageGradient] using hzi

/-- The normalized `L²` pairing of finite-dimensional vector fields. -/
noncomputable def vectorPairing (Q : TriadicCube 2) {m : ℕ}
    (F G : Vec 2 → Fin m → ℝ) : ℝ :=
  ∑ i, pairing Q (fun x => F x i) (fun x => G x i)

/-- Coordinatewise scalar Haar duality combines into vector Haar duality. -/
theorem abs_vectorPairing_le_vectorPositiveHaarNorm_mul_vectorWeakHaarNorm
    (Q : TriadicCube 2) {m : ℕ} {F G : Vec 2 → Fin m → ℝ}
    (hF : ∀ i, MemLp (fun x => F x i) 2 (normalizedCubeMeasure Q))
    (hG : ∀ i, MemLp (fun x => G x i) 2 (normalizedCubeMeasure Q))
    (hFpos : ∀ i, Summable (fun k => (Real.sqrt 3) ^ (k + 1) *
      energy Q (cubeIncrement Q (k + 1) (fun x => F x i)))) :
    |vectorPairing Q F G| ≤
      vectorPositiveHaarNorm Q F * vectorWeakHaarNorm Q G := by
  have hcoord : ∀ i,
      |pairing Q (fun x => F x i) (fun x => G x i)| ≤
        positiveHaarNorm Q (fun x => F x i) * weakHaarNorm Q (fun x => G x i) := by
    intro i
    exact weak_positive_pairing_le Q (hF i) (hG i) (hFpos i)
  have hsumabs :
      |∑ i, pairing Q (fun x => F x i) (fun x => G x i)| ≤
        ∑ i, |pairing Q (fun x => F x i) (fun x => G x i)| :=
    Finset.abs_sum_le_sum_abs _ _
  have hsumprod :
      ∑ i, |pairing Q (fun x => F x i) (fun x => G x i)| ≤
        ∑ i, positiveHaarNorm Q (fun x => F x i) *
          weakHaarNorm Q (fun x => G x i) :=
    Finset.sum_le_sum fun i _ => hcoord i
  have hcs :
      (∑ i, positiveHaarNorm Q (fun x => F x i) *
        weakHaarNorm Q (fun x => G x i)) ^ 2 ≤
        (∑ i, positiveHaarNorm Q (fun x => F x i) ^ 2) *
          ∑ i, weakHaarNorm Q (fun x => G x i) ^ 2 := by
    exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ _ _
  have hsq : |vectorPairing Q F G| ^ 2 ≤
      vectorPositiveHaarNorm Q F ^ 2 * vectorWeakHaarNorm Q G ^ 2 := by
    have hnonneg : 0 ≤ |vectorPairing Q F G| := abs_nonneg _
    have hsumle : |vectorPairing Q F G| ≤
        ∑ i, positiveHaarNorm Q (fun x => F x i) *
          weakHaarNorm Q (fun x => G x i) := hsumabs.trans hsumprod
    have hsumNonneg : 0 ≤
        ∑ i, positiveHaarNorm Q (fun x => F x i) *
          weakHaarNorm Q (fun x => G x i) :=
      Finset.sum_nonneg fun i _ => mul_nonneg (Real.sqrt_nonneg _)
        (Real.sqrt_nonneg _)
    calc
      |vectorPairing Q F G| ^ 2 ≤
          (∑ i, positiveHaarNorm Q (fun x => F x i) *
            weakHaarNorm Q (fun x => G x i)) ^ 2 :=
          sq_le_sq' (by linarith) hsumle
      _ ≤ (∑ i, positiveHaarNorm Q (fun x => F x i) ^ 2) *
            ∑ i, weakHaarNorm Q (fun x => G x i) ^ 2 := hcs
      _ = vectorPositiveHaarNorm Q F ^ 2 * vectorWeakHaarNorm Q G ^ 2 := by
            rw [← vectorPositiveHaarNorm_sq, ← vectorWeakHaarNorm_sq]
  have hP : 0 ≤ vectorPositiveHaarNorm Q F := Real.sqrt_nonneg _
  have hK : 0 ≤ vectorWeakHaarNorm Q G := Real.sqrt_nonneg _
  have hprod : 0 ≤ vectorPositiveHaarNorm Q F * vectorWeakHaarNorm Q G :=
    mul_nonneg hP hK
  exact (sq_le_sq₀ (abs_nonneg _) hprod).mp (by simpa [mul_pow] using hsq)

end ASDExplicitGamma.Triadic

end
