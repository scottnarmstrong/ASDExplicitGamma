module

public import ASDExplicitGamma.Native.ParentBoundaryRestriction
public import ASDExplicitGamma.Triadic.HilbertPoincareNumerics

/-! Mixed parent/fine-cell positive norm control for the actual H10 parent
potential. Its restrictions are H1, with no artificial zero cell trace. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Triadic ASDExplicitGamma.Variational
open scoped BigOperators
noncomputable section

/-- A full positive norm on an arbitrary cell keeps its L2 energy once and
controls only the residual series by the same cell's weak-gradient energy. -/
theorem parent_boundary_h1_positive_sq
    (Q : TriadicCube 2) (u : H1Function (openCubeSet Q)) :
    positiveHaarNorm Q u.toFun^2 ≤ energy Q u.toFun +
      (662/1000:ℝ)^2 * cubeScaleFactor Q^2 * vectorWeakHaarEnergy Q u.grad := by
  let q : ℝ := Real.sqrt 3
  let K := vectorWeakHaarEnergy Q u.grad
  let C := cubeScaleFactor Q^2 * planarC0^2 * K
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hqsq : q^2 = 3 := Real.sq_sqrt (by norm_num)
  have hq1 : 1 < q := by nlinarith only [hqsq, hq0]
  have hq2 : q ≤ 2 := by nlinarith only [hqsq, hq0]
  have hK : 0 ≤ K := vectorWeakHaarEnergy_nonneg Q _
  have hs := positiveHaarResidualSeries_summable Q
    u.memL2_normalizedCubeMeasure u.grad_memL2_normalizedCubeMeasure u.hasWeakGradient
  have hgeom : Summable (fun j : ℕ => C*(1/3:ℝ)^j) :=
    (summable_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/3) (by norm_num)).mul_left C
  have hterm (j : ℕ) : q^j * energy Q (fun x => u.toFun x-cubeProjection Q j u.toFun x) ≤
      C*(1/3:ℝ)^j := by
    have hh := mul_le_mul_of_nonneg_left (h1_residual_weak_bound Q j u) (pow_nonneg hq0 j)
    apply hh.trans_eq
    change q^j * (cubeScaleFactor Q^2 / 9^j * planarC0^2 * q^j * K) = _
    calc
      _ = C * (q^j*q^j/9^j) := by dsimp [C]; ring
      _ = C * ((q*q)/9)^j := by rw [div_pow, mul_pow]
      _ = _ := by rw [show q*q/9=(1/3:ℝ) by nlinarith only [hqsq]]
  have hsum := hs.tsum_le_tsum hterm hgeom
  rw [tsum_mul_left, tsum_geometric_of_lt_one
    (by norm_num : (0:ℝ) ≤ 1/3) (by norm_num)] at hsum
  norm_num only [show (1-(1/3:ℝ))⁻¹=3/2 by norm_num] at hsum
  have hp : positiveHaarNorm Q u.toFun^2 = energy Q u.toFun +
      (q-1) * ∑' j : ℕ, q^j * energy Q (fun x => u.toFun x-cubeProjection Q j u.toFun x) := by
    rw [positiveHaarNorm, Real.sq_sqrt
      (primalEnergy_nonneg Q (Real.sqrt 3) (Real.sqrt_nonneg _) u.toFun)]
    exact primalEnergy_eq_abel Q hq1 u.memL2_normalizedCubeMeasure hs
  have hc0 : planarC0 ≤ (1/2:ℝ) := planarC0_decimal_bounds.2.le.trans (by norm_num)
  have hc0sq := pow_le_pow_left₀ (show 0 ≤ planarC0 from Real.sqrt_nonneg _) hc0 2
  have hprod := mul_le_mul (show q-1 ≤ (1:ℝ) by linarith only [hq2])
    hc0sq (sq_nonneg planarC0) (by norm_num : (0:ℝ) ≤ 1)
  have hcoef : (q-1)*planarC0^2*(3/2:ℝ) ≤ (662/1000:ℝ)^2 := by
    exact (mul_le_mul_of_nonneg_right hprod (by norm_num : (0:ℝ) ≤ 3/2)).trans (by norm_num)
  calc
    _ = _ := hp
    _ ≤ energy Q u.toFun + (q-1)*(C*(3/2)) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hsum (sub_nonneg.mpr hq1.le))
    _ = energy Q u.toFun + ((q-1)*planarC0^2*(3/2))*cubeScaleFactor Q^2*K := by
      dsimp [C]; ring
    _ ≤ energy Q u.toFun + (662/1000:ℝ)^2*cubeScaleFactor Q^2*K :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hcoef (sq_nonneg _)) hK)

/-- Source (2.1): the positive norm on fine cells of a genuine parent H10
potential is controlled by its broken weak gradient with independent parent
and cell scales. The same potential is restricted to every cell. -/
theorem parent_boundary_h10_broken_positive_sq
    (Q : TriadicCube 2) (j : ℕ) (u : H10Function (openCubeSet Q)) :
    descendantsAverage Q j (fun U => positiveHaarNorm U u.toH1Function.toFun^2) ≤
      ((52/100:ℝ)^2*cubeScaleFactor Q^2 +
        (662/1000:ℝ)^2*(cubeScaleFactor Q/(3:ℝ)^j)^2) *
          lemmaVTiledWeakEnergy Q j u.toH1Function.grad := by
  have hlocal (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth Q j) :
      positiveHaarNorm U u.toH1Function.toFun^2 ≤ energy U u.toH1Function.toFun +
        (662/1000:ℝ)^2*(cubeScaleFactor Q/(3:ℝ)^j)^2 *
          vectorWeakHaarEnergy U u.toH1Function.grad := by
    have hh := parent_boundary_h1_positive_sq U (u.toH1Function.restrictToOpenSubcube hU)
    simpa only [H1Function.restrictToOpenSubcube_toFun,
      H1Function.restrictToOpenSubcube_grad, cubeScaleFactor_descendant_eq_div_pow hU] using hh
  have havg := descendantsAverage_le hlocal
  rw [descendantsAverage_add, descendantsAverage_mul_left,
    ← energy_eq_descendantsAverage Q j u.toH1Function.memL2_normalizedCubeMeasure] at havg
  change descendantsAverage Q j (fun U => positiveHaarNorm U u.toH1Function.toFun^2) ≤
    energy Q u.toH1Function.toFun + (662/1000:ℝ)^2*(cubeScaleFactor Q/(3:ℝ)^j)^2 *
      lemmaVTiledWeakEnergy Q j u.toH1Function.grad at havg
  refine havg.trans ?_
  calc
    _ ≤ (52/100:ℝ)^2*cubeScaleFactor Q^2*lemmaVTiledWeakEnergy Q j u.toH1Function.grad +
        (662/1000:ℝ)^2*(cubeScaleFactor Q/(3:ℝ)^j)^2 *
          lemmaVTiledWeakEnergy Q j u.toH1Function.grad :=
      add_le_add (parent_boundary_h10_l2_sq Q j u) le_rfl
    _ = _ := by ring

end
end ASDExplicitGamma.Native
