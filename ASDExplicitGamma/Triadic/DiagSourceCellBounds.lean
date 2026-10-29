module

public import ASDExplicitGamma.Triadic.DiagSourcePolynomial
public import ASDExplicitGamma.Triadic.DiagCellPolynomialBounds
public import ASDExplicitGamma.Triadic.DiagEnergyCongr

/-! Sharp local cell bounds for the actual concrete DIAG interpolant. -/

@[expose] public section

namespace ASDExplicitGamma.Triadic

open Homogenization MeasureTheory
open scoped BigOperators Fin.CommRing

noncomputable section

/-- The actual interpolant's weak derivatives equal the reconstructed derivatives. -/
theorem diagInterpolant_h10_cell_grad_ae (Q : TriadicCube 2) (j : ℕ)
    (u : H10Function (openCubeSet Q)) (k : Fin 2 → Fin (3^j)) (i : Fin 2) :
    (fun x => (diagInterpolant Q j u.toH1Function).grad x i) =ᵐ[volume.restrict (cubeSet (diagMeshCell Q j k))]
      (fun x => (diagBilinearH1 (diagMeshCell Q j k) (diagSourceCellCoefficients Q j u.toH1Function k)).grad x i) := by
  rw [volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]
  apply diagH1_grad_eq_polynomial (diagMeshCell Q j k)
    ((diagInterpolant Q j u.toH1Function).restrictToOpenSubcube (diagMeshCell_mem Q j k))
  intro x hx
  apply diagInterpolant_h10_cell_polynomial Q j u k x
  rw [openCubeSet_eq_box] at hx
  intro a
  exact ⟨(hx a (by trivial)).1.le, (hx a (by trivial)).2.le⟩

/-- Actual cell positive energy of each gradient component. -/
theorem diagInterpolant_h10_cell_gradient_bound (Q : TriadicCube 2) (j : ℕ)
    (u : H10Function (openCubeSet Q)) (k : Fin 2 → Fin (3^j)) (i : Fin 2) :
    let N := 3^j
    let instPeriodNonzero : NeZero (2*N) := ⟨by positivity⟩
    primalEnergy (diagMeshCell Q j k) (Real.sqrt 3)
      (fun x => (diagInterpolant Q j u.toH1Function).grad x i) ≤
      diagNodalGradientBudget (diagPeriodLag N) (diagAxisLag i) (diagAxisLag (diagOtherCoordinate i))
        (diagOddGrid N (diagSourceMeans Q j u.toH1Function)) (diagPeriodEmbed k) /
        diagMeshRadius Q j ^ 2 := by
  intro N instPeriodNonzero
  rw [diagPrimalEnergy_congr_ae _ _ (diagInterpolant_h10_cell_grad_ae Q j u k i)]
  have h := diagBilinearPolynomial_derivative_positive_le (diagMeshCell Q j k)
    (diagSourceCellCoefficients Q j u.toH1Function k) i
  rw [diagMeshCell_side] at h
  fin_cases i <;> simpa [diagSourceCellCoefficients, diagNodalGradientBudget,
    diagNodalCoefficients, diagOtherCoordinate, mul_comm] using h

/-- Shift only the mean coefficient by the actual source cell mean. -/
def diagSourceResidualCoefficients (Q : TriadicCube 2) (j : ℕ)
    (v : H1Function (openCubeSet Q)) (k : Fin 2 → Fin (3^j)) : Fin 4 → ℝ :=
  Function.update (diagSourceCellCoefficients Q j v k) 0
    (diagSourceCellCoefficients Q j v k 0-diagSourceMeans Q j v k)

/-- The interpolated-minus-cell-mean field is exactly its shifted cell polynomial. -/
theorem diagInterpolant_h10_minus_mean_ae (Q : TriadicCube 2) (j : ℕ)
    (u : H10Function (openCubeSet Q)) (k : Fin 2 → Fin (3^j)) :
    (fun x => (diagInterpolant Q j u.toH1Function).toFun x-cubeProjection Q j u.toH1Function.toFun x)
      =ᵐ[volume.restrict (cubeSet (diagMeshCell Q j k))]
      diagBilinearPolynomial (diagMeshCell Q j k) (diagSourceResidualCoefficients Q j u.toH1Function k) := by
  apply (ae_restrict_mem (measurableSet_cubeSet _)).mono
  intro x hx
  change (diagInterpolant Q j u.toH1Function).toFun x - cubeProjection Q j u.toH1Function.toFun x = _
  rw [cubeProjection_eq_cubeAverage_of_mem_descendantsAtDepth _ (diagMeshCell_mem Q j k) hx,
    diagInterpolant_h10_cell_polynomial Q j u k x (by
      rw [cubeSet_eq_box] at hx
      intro i
      exact ⟨(hx i (by trivial)).1, (hx i (by trivial)).2.le⟩),
    diagBilinearPolynomial_explicit, diagBilinearPolynomial_explicit]
  simp [diagSourceResidualCoefficients, diagSourceMeans]
  ring

/-- The source mean array is unchanged on the original cells by odd reflection. -/
theorem diagOddGrid_embed {N : ℕ} (m : (Fin 2 → Fin N) → ℝ) (k : Fin 2 → Fin N) :
    diagOddGrid N m (diagPeriodEmbed k) = m k := by
  unfold diagOddGrid diagPeriodEmbed
  simp only [diagReflectIndex_inl]
  have hs (i : Fin 2) : diagReflectSign N (diagReflectionEquiv N (Sum.inl (k i))) = 1 :=
    ite_eq_left (k i).isLt
  rw [hs, hs, one_mul, one_mul]

/-- The actual scalar positive-energy half-gain budget on one source tile. -/
theorem diagInterpolant_h10_cell_residual_positive_bound (Q : TriadicCube 2) (j : ℕ)
    (u : H10Function (openCubeSet Q)) (k : Fin 2 → Fin (3^j)) :
    let N := 3^j
    let instPeriodNonzero : NeZero (2*N) := ⟨by positivity⟩
    primalEnergy (diagMeshCell Q j k) (Real.sqrt 3)
      (fun x => (diagInterpolant Q j u.toH1Function).toFun x-cubeProjection Q j u.toH1Function.toFun x) ≤
      diagNodalResidualBudget (diagPeriodLag N) (diagAxisLag 0) (diagAxisLag 1)
        (diagOddGrid N (diagSourceMeans Q j u.toH1Function)) (diagPeriodEmbed k) := by
  intro N instPeriodNonzero
  rw [diagPrimalEnergy_congr_ae _ _ (diagInterpolant_h10_minus_mean_ae Q j u k)]
  have h := diagBilinearPolynomial_positive_le (diagMeshCell Q j k)
    (diagSourceResidualCoefficients Q j u.toH1Function k)
  simpa [diagSourceResidualCoefficients, diagSourceCellCoefficients,
    diagNodalResidualBudget, diagOddGrid_embed] using h

/-- The actual interpolant gradient has a convergent positive Haar series
on every source tile; no real-tsum default is used as a convergence claim. -/
theorem diagInterpolant_h10_cell_gradient_summable (Q : TriadicCube 2) (j : ℕ)
    (u : H10Function (openCubeSet Q)) (k : Fin 2 → Fin (3^j)) (i : Fin 2) :
    Summable (fun n => (Real.sqrt 3)^(n+1)*energy (diagMeshCell Q j k)
      (cubeIncrement (diagMeshCell Q j k) (n+1)
        (fun x => (diagInterpolant Q j u.toH1Function).grad x i))) := by
  let R := diagMeshCell Q j k
  let c := diagSourceCellCoefficients Q j u.toH1Function k
  let w := diagBilinearH1 R (diagBilinearDerivativeCoefficients R c i)
  have hg : (fun x => (diagBilinearH1 R c).grad x i) = w.toFun :=
    diagBilinearH1_grad_polynomial R c i
  have hae := diagInterpolant_h10_cell_grad_ae Q j u k i
  rw [hg] at hae
  have hs := positiveHaarIncrementSeries_summable R w.memL2_normalizedCubeMeasure
    w.grad_memL2_normalizedCubeMeasure w.hasWeakGradient
  change Summable (fun n => (Real.sqrt 3)^(n+1)*energy R
    (cubeIncrement R (n+1) (fun x => (diagInterpolant Q j u.toH1Function).grad x i)))
  simpa only [diagCubeIncrement_congr_ae R _ hae] using hs

end

end ASDExplicitGamma.Triadic
