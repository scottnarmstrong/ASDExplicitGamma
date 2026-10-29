module

public import ASDExplicitGamma.Scalar.OldHessianTrialBrokenPairing
public import ASDExplicitGamma.Native.OldSignedSeriesPairingBudget

/-! Complete correlated fine-cell and mode pairing, with constant one. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational
noncomputable section
attribute [local irreducible] Homogenization.descendantsAtDepth

/-- A single vector column contracts through its exact fine-cell weights. -/
theorem old_hessian_broken_vector_pairing (Q : TriadicCube 2) (fine : ℕ)
    (G F : OldSignedCellIndex Q fine → Vec 2 → Vec 2)
    (hG : ∀ U k,MemLp (fun x => G U x k) 2 (normalizedCubeMeasure U.val))
    (hF : ∀ U k,MemLp (fun x => F U x k) 2 (normalizedCubeMeasure U.val))
    (hpos : ∀ U k,Summable (fun j => (Real.sqrt 3)^(j+1)*energy U.val
      (cubeIncrement U.val (j+1) (fun x => F U x k)))) :
    |oldSignedCellAverage Q fine (fun U => cubeAverage U.val (fun x => vecDot (G U x) (F U x)))|≤
      Real.sqrt (oldSignedCellAverage Q fine (fun U => vectorWeakHaarEnergy U.val (G U)))*
        Real.sqrt (oldSignedCellAverage Q fine (fun U => vectorPositiveHaarEnergy U.val (F U))) := by
  have hcell (U : OldSignedCellIndex Q fine) : |cubeAverage U.val (fun x => vecDot (G U x) (F U x))|≤
      Real.sqrt (vectorWeakHaarEnergy U.val (G U))*Real.sqrt (vectorPositiveHaarEnergy U.val (F U)) := by
    rw [lemmaV_cubeAverage_vecDot_eq_vectorPairing U.val (hG U) (hF U)]
    exact old_signed_vector_haar_pairing_bound U.val (G U) (F U) (hG U) (hF U) (hpos U)
  exact ((old_signed_cell_average_abs_le Q fine _).trans (old_signed_cell_average_mono Q fine hcell)).trans
    (old_signed_cell_average_root_cauchy Q fine _ _
      (fun U => vectorWeakHaarEnergy_nonneg U.val _) (fun U => vectorPositiveHaarEnergy_nonneg U.val _))

/-- Complete physical-mode pairing has genuine absolute summability and
its two full spatial energy budgets, before probability is contracted. -/
theorem old_hessian_broken_mode_pairing {ι : Type*} (Q : TriadicCube 2) (fine : ℕ)
    (G F : ι → OldSignedCellIndex Q fine → Vec 2 → Vec 2)
    (hG : ∀ p U k,MemLp (fun x => G p U x k) 2 (normalizedCubeMeasure U.val))
    (hF : ∀ p U k,MemLp (fun x => F p U x k) 2 (normalizedCubeMeasure U.val))
    (hpos : ∀ p U k,Summable (fun j => (Real.sqrt 3)^(j+1)*energy U.val
      (cubeIncrement U.val (j+1) (fun x => F p U x k))))
    (hGs : Summable (fun p => oldSignedCellAverage Q fine (fun U => vectorWeakHaarEnergy U.val (G p U))))
    (hFs : Summable (fun p => oldSignedCellAverage Q fine (fun U => vectorPositiveHaarEnergy U.val (F p U)))) :
    Summable (fun p => oldSignedCellAverage Q fine (fun U => cubeAverage U.val
      (fun x => vecDot (G p U x) (F p U x)))) ∧
    |∑' p,oldSignedCellAverage Q fine (fun U => cubeAverage U.val (fun x => vecDot (G p U x) (F p U x)))|≤
      Real.sqrt (∑' p,oldSignedCellAverage Q fine (fun U => vectorWeakHaarEnergy U.val (G p U)))*
        Real.sqrt (∑' p,oldSignedCellAverage Q fine (fun U => vectorPositiveHaarEnergy U.val (F p U))) := by
  have hG0 p : 0≤oldSignedCellAverage Q fine (fun U => vectorWeakHaarEnergy U.val (G p U)) :=
    old_signed_cell_average_nonneg _ _ _ (fun U => vectorWeakHaarEnergy_nonneg U.val _)
  have hF0 p : 0≤oldSignedCellAverage Q fine (fun U => vectorPositiveHaarEnergy U.val (F p U)) :=
    old_signed_cell_average_nonneg _ _ _ (fun U => vectorPositiveHaarEnergy_nonneg U.val _)
  have hh := old_signed_series_pairing_budget
    (fun p => Real.sqrt (oldSignedCellAverage Q fine (fun U => vectorWeakHaarEnergy U.val (G p U))))
    (fun p => Real.sqrt (oldSignedCellAverage Q fine (fun U => vectorPositiveHaarEnergy U.val (F p U))))
    (fun p => oldSignedCellAverage Q fine (fun U => cubeAverage U.val (fun x => vecDot (G p U x) (F p U x))))
    (fun _ => Real.sqrt_nonneg _) (fun _ => Real.sqrt_nonneg _)
    (by simpa only [Real.sq_sqrt (hG0 _)] using hGs)
    (by simpa only [Real.sq_sqrt (hF0 _)] using hFs)
    (fun p => old_hessian_broken_vector_pairing Q fine (G p) (F p) (hG p) (hF p) (hpos p))
  simpa only [Real.sq_sqrt (hG0 _),Real.sq_sqrt (hF0 _)] using hh

end
end ASDExplicitGamma.Scalar
