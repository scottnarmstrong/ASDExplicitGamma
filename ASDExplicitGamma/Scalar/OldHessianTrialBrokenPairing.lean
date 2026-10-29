module

public import ASDExplicitGamma.Native.OldSignedCovarianceCellPairing
public import ASDExplicitGamma.Native.OldSignedCellAverageCauchy
public import ASDExplicitGamma.Variational.LemmaVTiles

/-! Constant-one spatial K/P pairing for genuine varying fine-cell receivers. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational
noncomputable section
attribute [local irreducible] Homogenization.descendantsAtDepth

/-- The complete two-load cell pairing contracts through both physical
spatial and load weights without a coordinate-count factor. -/
theorem old_hessian_broken_load_pairing (Q : TriadicCube 2) (fine : ℕ)
    (G F : OldSignedCellIndex Q fine → Fin 2 → Vec 2 → Vec 2)
    (hG : ∀ U i k,MemLp (fun x => G U i x k) 2 (normalizedCubeMeasure U.val))
    (hF : ∀ U i k,MemLp (fun x => F U i x k) 2 (normalizedCubeMeasure U.val))
    (hpos : ∀ U i k,Summable (fun j => (Real.sqrt 3)^(j+1)*energy U.val
      (cubeIncrement U.val (j+1) (fun x => F U i x k)))) :
    |oldSignedCellAverage Q fine (fun U => ∑ i : Fin 2,cubeAverage U.val
      (fun x => vecDot (G U i x) (F U i x)))|≤
      Real.sqrt (∑ i : Fin 2,oldSignedCellAverage Q fine (fun U => vectorWeakHaarEnergy U.val (G U i)))*
        Real.sqrt (∑ i : Fin 2,oldSignedCellAverage Q fine (fun U => vectorPositiveHaarEnergy U.val (F U i))) := by
  have hcell (U : OldSignedCellIndex Q fine) : |∑ i : Fin 2,cubeAverage U.val
      (fun x => vecDot (G U i x) (F U i x))|≤
      Real.sqrt (∑ i : Fin 2,vectorWeakHaarEnergy U.val (G U i))*
        Real.sqrt (∑ i : Fin 2,vectorPositiveHaarEnergy U.val (F U i)) := by
    have he (i : Fin 2) := lemmaV_cubeAverage_vecDot_eq_vectorPairing U.val (hG U i) (hF U i)
    simp_rw [he]
    have hh := old_signed_load_haar_pairing_bound U.val (G U) (F U) (hG U) (hF U) (hpos U)
    simpa only [vectorPairing,vectorWeakHaarNorm,vectorPositiveHaarNorm,
      Real.sq_sqrt (vectorWeakHaarEnergy_nonneg U.val _),
      Real.sq_sqrt (vectorPositiveHaarEnergy_nonneg U.val _)] using hh
  have hh := (old_signed_cell_average_abs_le Q fine _).trans (old_signed_cell_average_mono Q fine hcell)
  have hcs := old_signed_cell_average_root_cauchy Q fine
    (fun U => ∑ i : Fin 2,vectorWeakHaarEnergy U.val (G U i))
    (fun U => ∑ i : Fin 2,vectorPositiveHaarEnergy U.val (F U i))
    (fun U => Finset.sum_nonneg (fun i _ => vectorWeakHaarEnergy_nonneg U.val _))
    (fun U => Finset.sum_nonneg (fun i _ => vectorPositiveHaarEnergy_nonneg U.val _))
  rw [old_signed_cell_average_sum,old_signed_cell_average_sum] at hcs
  exact hh.trans hcs

end
end ASDExplicitGamma.Scalar
