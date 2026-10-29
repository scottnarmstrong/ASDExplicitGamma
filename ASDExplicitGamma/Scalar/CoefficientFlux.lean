module

public import ASDExplicitGamma.Scalar.CellEnergyCauchy

/-! Genuine L2 control of the exchanged doubled coefficient field. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization Response MeasureTheory

/-- The literal doubled coefficient action on a physical field. -/
noncomputable def scalarCoefficientFlux (a : CoeffField 2) (Z : Vec 2 → BlockVec 2) (x : Vec 2) : BlockVec 2 :=
  blockMatVecMul (blockCoeffField a x) (Z x)

/-- Qualitative coefficient ellipticity supplies actual L2 control of the exchanged field. -/
theorem scalar_coefficient_flux_memL2 (Q : TriadicCube 2) (a : CoeffField 2) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) {Z : Vec 2 → BlockVec 2}
    (hZ : MemBlockL2 (openCubeSet Q) Z) : MemBlockL2 (openCubeSet Q) (scalarCoefficientFlux a Z) := by
  let B := rawBlockCoeffOperatorField hEll
  let H := toHilbertBlockL2OfBlockField hZ
  have hm : MemBlockL2 (openCubeSet Q) (fun x => (B.applyFn H x).toBlockVec) :=
    (HilbertBlockVec.continuousLinearEquivBlockVec 2).toContinuousLinearMap.comp_memLp' (B.memHilbertBlockL2_applyFn H)
  apply hm.ae_eq
  filter_upwards [ae_restrict_mem (measurableSet_openCubeSet Q),coeFn_toHilbertBlockL2OfBlockField hZ] with x hx hz
  simp only [B,PointwiseHilbertBlockOperatorField.applyFn,rawBlockCoeffOperatorField,
    HilbertBlockVec.applyBlockMat_apply,HilbertBlockVec.toBlockVec_ofBlockVec]
  rw [hz]
  simp only [hilbertifyBlockField,HilbertBlockVec.toBlockVec_ofBlockVec,scalarCoefficientFlux,blockCoeffField]
  congr 2
  simp [restrictCoeffField,hx]

/-- The true coefficient energy density is integrable for every admissible L2 field. -/
theorem scalar_coefficient_energy_integrable (Q : TriadicCube 2) (a : CoeffField 2) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) {Z : Vec 2 → BlockVec 2}
    (hZ : MemBlockL2 (openCubeSet Q) Z) :
    IntegrableOn (fun x => blockVecDot (Z x) (scalarCoefficientFlux a Z x)) (openCubeSet Q) := by
  let state : BlockState 2 := ⟨fun x => (Z x).1,fun x => (Z x).2⟩
  have hs : MemBlockL2 (openCubeSet Q) state.eval := hZ
  have hi : IntegrableOn (blockPairingIntegrand a state state) (openCubeSet Q) :=
    blockPairingIntegrand_integrableOn_of_memBlockL2_of_isEllipticFieldOn
      (a := a) (X := state) (Y := state) hs hs hEll
  change IntegrableOn (blockPairingIntegrand a state state) (openCubeSet Q)
  exact hi

/-- Every actual local coefficient energy average is nonnegative. -/
theorem scalar_coefficient_energy_average_nonneg (Q : TriadicCube 2) (a : CoeffField 2) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) (Z : Vec 2 → BlockVec 2) :
    0 ≤ volumeAverage (openCubeSet Q) (fun x => blockVecDot (Z x) (scalarCoefficientFlux a Z x)) := by
  apply mul_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg)
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem (measurableSet_openCubeSet Q)] with x hx
  by_cases hz : Z x=0
  · change 0 ≤ blockVecDot (Z x) (blockMatVecMul (blockMatrixOfCoeff (a x)) (Z x))
    rw [hz]
    simp [blockVecDot,vecDot]
  · exact (blockMatrixOfCoeff_quadratic_pos_of_isEllipticMatrix (hEll.2 x hx) hz).le

end ASDExplicitGamma.Scalar
