module

public import ASDExplicitGamma.Scalar.CellResponseTest

/-! Cauchy–Schwarz for the actual cell energy, without an inequality premise. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization Response MeasureTheory
open scoped RealInnerProductSpace

/-- Every genuine symmetric coercive realization satisfies the exact energy Cauchy inequality. -/
theorem scalar_realized_energy_cauchy {U : Set (Vec 2)} {a : CoeffField 2}
    (M : MuHilbertRealization U a) (X Y : HilbertBlockL2 U) :
    (M.energyBilin X Y)^2 ≤ M.energyBilin X X*M.energyBilin Y Y := by
  let D := responseEnergyHilbertData M
  have h := real_inner_mul_inner_self_le (responseEnergyUp D X) (responseEnergyUp D Y)
  change M.energyBilin X Y*M.energyBilin X Y ≤ M.energyBilin X X*M.energyBilin Y Y at h
  simpa only [pow_two] using h

/-- The cell's bilinear form is the genuine averaged field pairing. -/
theorem scalar_cell_bilinear_field (Q : TriadicCube 2) (a : CoeffField 2) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) {F G : Vec 2 → BlockVec 2}
    (hF : MemBlockL2 (openCubeSet Q) F) (hG : MemBlockL2 (openCubeSet Q) G) :
    (scalarCellSystem Q a hEll).toMuHilbertRealization.energyBilin
      (toHilbertBlockL2OfBlockField hF) (toHilbertBlockL2OfBlockField hG)=
      volumeAverage (openCubeSet Q) (fun x => blockVecDot (G x) (blockMatVecMul (blockCoeffField a x) (F x))) := by
  let finiteScalarCellBilinear : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume
  exact (scalarCellSystem Q a hEll).toMuOperatorRealization.energyBilin_eq_volumeAverage_swap_of_memBlockL2 hG hF

/-- Cauchy–Schwarz on the literal normalized cell energy. -/
theorem scalar_cell_field_cauchy (Q : TriadicCube 2) (a : CoeffField 2) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) {F G : Vec 2 → BlockVec 2}
    (hF : MemBlockL2 (openCubeSet Q) F) (hG : MemBlockL2 (openCubeSet Q) G) :
    (volumeAverage (openCubeSet Q) (fun x => blockVecDot (G x) (blockMatVecMul (blockCoeffField a x) (F x))))^2 ≤
      volumeAverage (openCubeSet Q) (fun x => blockVecDot (F x) (blockMatVecMul (blockCoeffField a x) (F x)))*
      volumeAverage (openCubeSet Q) (fun x => blockVecDot (G x) (blockMatVecMul (blockCoeffField a x) (G x))) := by
  let finiteScalarFieldCauchy : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume
  have h := scalar_realized_energy_cauchy (scalarCellSystem Q a hEll).toMuHilbertRealization
    (toHilbertBlockL2OfBlockField hF) (toHilbertBlockL2OfBlockField hG)
  simpa only [scalar_cell_bilinear_field] using h

end ASDExplicitGamma.Scalar
