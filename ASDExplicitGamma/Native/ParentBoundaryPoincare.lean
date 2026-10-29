module

public import ASDExplicitGamma.Native.ParentBoundarySineTest

/-! The sharp actual H10 Dirichlet Poincare clock from complete sine Parseval. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Triadic ASDExplicitGamma.Triadic.Torus
noncomputable section

/-- Exact sign grouping retains all Fourier coefficients, including all
nonzero signed frequencies in the complete source norm. -/
theorem parent_boundary_finite_signed_poincare (Q : TriadicCube 2)
    (u : H10Function (openCubeSet Q)) (T : Finset (Fin 2 → ℤ)) :
    ∑ p ∈ T, dirichletFourierCoeff Q u.toH1Function.toFun p ^ 2 ≤
      cubeScaleFactor Q^2/(2*Real.pi^2)*
        ∑ i : Fin 2,energy Q (fun x => u.toH1Function.grad x i) := by
  let c : (Fin 2 → ℕ) → ℝ := fun q =>
    dirichletFourierCoeff Q u.toH1Function.toFun (natVec q)
  let A := T.image natAbsVec
  let S := A.filter fun q => ∀ i, q i ≠ 0
  have hgroup : ∑ p ∈ T, dirichletFourierCoeff Q u.toH1Function.toFun p ^ 2 ≤
      ∑ q ∈ A, modeMult q * c q ^ 2 := by
    calc
      ∑ p ∈ T, dirichletFourierCoeff Q u.toH1Function.toFun p ^ 2 =
          ∑ p ∈ T,
            dirichletFourierCoeff Q u.toH1Function.toFun
              (natVec (natAbsVec p)) ^ 2 := by
                apply Finset.sum_congr rfl
                intro p hp
                exact dirichletFourierCoeff_sq_natAbsVec Q u.toH1Function.toFun p
      _ ≤ ∑ q ∈ A, modeMult q * c q ^ 2 := by
            exact sum_le_sum_image_natAbsVec T (fun q => c q ^ 2)
              (fun q => sq_nonneg (c q))
  have hremove : ∑ q ∈ A, modeMult q * c q ^ 2 =
      ∑ q ∈ S, modeMult q * c q ^ 2 := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro q hq hnot
    have hcoords : ¬ ∀ i, q i ≠ 0 := by
      intro hpos
      exact hnot (Finset.mem_filter.mpr ⟨hq, hpos⟩)
    obtain ⟨i, hi⟩ := not_forall.mp hcoords
    have hi' : q i = 0 := by omega
    have hzero : (natVec q) i = 0 := by simp [natVec, hi']
    have hc : c q = 0 := by
      exact dirichletFourierCoeff_eq_zero_of_coord_zero Q
        u.toH1Function.toFun (natVec q) i hzero
    simp [c, hc]
  have hS : ∀ q ∈ S, ∀ i, q i ≠ 0 := by
    intro q hq
    exact (Finset.mem_filter.mp hq).2
  have hfinite := parent_boundary_finite_sine_poincare Q u S hS
  calc
    ∑ p ∈ T, dirichletFourierCoeff Q u.toH1Function.toFun p ^ 2
        ≤ ∑ q ∈ A, modeMult q * c q ^ 2 := hgroup
    _ = ∑ q ∈ S, modeMult q * c q ^ 2 := hremove
    _ ≤ cubeScaleFactor Q^2/(2*Real.pi^2)*
        ∑ i : Fin 2,energy Q (fun x => u.toH1Function.grad x i) := by
          simpa [c] using hfinite

/-- The sharp `L²` Dirichlet bridge for zero-trace `H¹` data. -/
theorem parent_boundary_dirichlet_poincare (Q : TriadicCube 2)
    (u : H10Function (openCubeSet Q)) :
    energy Q u.toH1Function.toFun ≤
      cubeScaleFactor Q^2/(2*Real.pi^2)*
        ∑ i : Fin 2,energy Q (fun x => u.toH1Function.grad x i) := by
  have huNorm : MemLp u.toH1Function.toFun 2 (normalizedCubeMeasure Q) :=
    memLp_normalized_of_memL2On u.toH1Function.memL2
  have huBox : MemLp u.toH1Function.toFun 2
      (Torus.boxMeasure (cubeCorner Q) (cubeScaleFactor Q)) := by
    rw [boxMeasure_eq_normalizedCubeMeasure Q]
    exact huNorm
  have hparseval := hasSum_sq_dirichletFourierCoeff Q huBox
  rw [boxMeasure_eq_normalizedCubeMeasure Q] at hparseval
  rw [energy_eq_integral_sq Q, ← hparseval.tsum_eq]
  refine Real.tsum_le_of_sum_le (fun p => sq_nonneg
      (dirichletFourierCoeff Q u.toH1Function.toFun p)) ?_
  intro T
  exact parent_boundary_finite_signed_poincare Q u T


end
end ASDExplicitGamma.Native
