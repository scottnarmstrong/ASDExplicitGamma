module

public import ASDExplicitGamma.Scalar.CutoffProjection
public import Homogenization.Sobolev.Foundations.H1Graph.Graph

/-! The literal cell-average operator for the physical UPPER band load. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization Response MeasureTheory
noncomputable section

local instance upperCellResetMeanFinite (Q : TriadicCube 2) :
    IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
  (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume

local instance upperCellResetMeanMeasurable (Q : TriadicCube 2) :
    MeasurableSpace (HilbertBlockL2 (openCubeSet Q)) := borel _

local instance upperCellResetMeanBorel (Q : TriadicCube 2) :
    BorelSpace (HilbertBlockL2 (openCubeSet Q)) := ⟨rfl⟩

def upperCellResetCoordinate (c : BlockCoord 2) : HilbertBlockVec 2 →L[ℝ] ℝ :=
  match c with
  | .inl i => ((ContinuousLinearMap.proj i).comp
      (ContinuousLinearMap.fst ℝ (Vec 2) (Vec 2))).comp
        (HilbertBlockVec.continuousLinearEquivBlockVec 2).toContinuousLinearMap
  | .inr i => ((ContinuousLinearMap.proj i).comp
      (ContinuousLinearMap.snd ℝ (Vec 2) (Vec 2))).comp
        (HilbertBlockVec.continuousLinearEquivBlockVec 2).toContinuousLinearMap

/-- The actual normalized cell-average value of a Hilbert block field. -/
def upperCellResetMeanValue (Q : TriadicCube 2) :
    HilbertBlockL2 (openCubeSet Q) →L[ℝ] BlockVec 2 :=
  (ContinuousLinearMap.pi (fun i =>
    (integralAverageCLM (U := openCubeSet Q)).comp
      ((upperCellResetCoordinate (.inl i)).compLpL 2 (volumeMeasureOn (openCubeSet Q))))).prod
    (ContinuousLinearMap.pi (fun i =>
      (integralAverageCLM (U := openCubeSet Q)).comp
        ((upperCellResetCoordinate (.inr i)).compLpL 2 (volumeMeasureOn (openCubeSet Q)))))

/-- The literal constant field equal to the physical load's cell average. -/
def upperCellResetMeanField (Q : TriadicCube 2) :
    HilbertBlockL2 (openCubeSet Q) →L[ℝ] HilbertBlockL2 (openCubeSet Q) :=
  (blockVecToHilbertBlockL2Const (U := openCubeSet Q)).comp (upperCellResetMeanValue Q)

private theorem upper_cell_reset_average_compLpL
    (Q : TriadicCube 2) (L : HilbertBlockVec 2 →L[ℝ] ℝ)
    (F : HilbertBlockL2 (openCubeSet Q)) :
    integralAverageCLM (U := openCubeSet Q) ((L.compLpL 2 (volumeMeasureOn (openCubeSet Q))) F)=
      cubeAverage Q (fun x => L (F x)) := by
  rw [integralAverageCLM_apply,cubeAverage_eq_integralAverage_openCubeSet]
  unfold integralAverage
  congr 1
  apply integral_congr_ae
  exact ContinuousLinearMap.coeFn_compLpL (p := 2) (μ := volumeMeasureOn (openCubeSet Q)) (L := L) (f := F)

/-- Every coordinate of the exported mean is the physical normalized cube
average, independent of the chosen L2 representative. -/
theorem upper_cell_reset_mean_value_coordinate
    (Q : TriadicCube 2) (F : HilbertBlockL2 (openCubeSet Q)) (c : BlockCoord 2) :
    toFullBlockVec (upperCellResetMeanValue Q F) c=
      cubeAverage Q (fun x => toFullBlockVec (F x).toBlockVec c) := by
  cases c with
  | inl i => simpa [upperCellResetMeanValue,upperCellResetCoordinate,toFullBlockVec] using
      upper_cell_reset_average_compLpL Q (upperCellResetCoordinate (.inl i)) F
  | inr i => simpa [upperCellResetMeanValue,upperCellResetCoordinate,toFullBlockVec] using
      upper_cell_reset_average_compLpL Q (upperCellResetCoordinate (.inr i)) F

/-- The mean field is almost everywhere the constant physical block vector. -/
theorem upper_cell_reset_mean_field_ae
    (Q : TriadicCube 2) (F : HilbertBlockL2 (openCubeSet Q)) :
    upperCellResetMeanField Q F =ᵐ[volumeMeasureOn (openCubeSet Q)]
      fun _ => HilbertBlockVec.ofBlockVec (upperCellResetMeanValue Q F) :=
  coeFn_blockVecToHilbertBlockL2Const _

/-- A measurable physical band-load lift has a measurable canonical mean. -/
theorem upper_cell_reset_mean_field_measurable
    {Ω : Type*} [MeasurableSpace Ω] (Q : TriadicCube 2)
    (F : Ω → HilbertBlockL2 (openCubeSet Q)) (hF : Measurable F) :
    Measurable (fun ω => upperCellResetMeanField Q (F ω)) :=
  (upperCellResetMeanField Q).continuous.measurable.comp hF

/-- Physical representatives give the same literal cell average; no extra
integrability or moment assumption is needed for the L2 field. -/
theorem upper_cell_reset_mean_of_ae_field
    (Q : TriadicCube 2) (F : HilbertBlockL2 (openCubeSet Q))
    (f : Vec 2 → BlockVec 2)
    (hf : F =ᵐ[volumeMeasureOn (openCubeSet Q)] fun x => HilbertBlockVec.ofBlockVec (f x))
    (c : BlockCoord 2) :
    toFullBlockVec (upperCellResetMeanValue Q F) c=cubeAverage Q (fun x => toFullBlockVec (f x) c) := by
  rw [upper_cell_reset_mean_value_coordinate]
  simp only [cubeAverage_eq_integralAverage_openCubeSet]
  unfold integralAverage
  congr 1
  apply integral_congr_ae
  filter_upwards [hf] with x hx
  rw [hx]
  simp

end
end ASDExplicitGamma.Scalar
