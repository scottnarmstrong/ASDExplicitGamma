module

public import ASDExplicitGamma.Variational.AffineGradientClosed
public import ASDExplicitGamma.Response.ResponseRealization

/-! The exact closed source block carrier and pure-second injection. -/

@[expose] public section
namespace ASDExplicitGamma.Variational
open Homogenization MeasureTheory ASDExplicitGamma.Response
noncomputable section

 def hilbertFirstProjection (U : Set (Vec 2)) : HilbertBlockL2 U →L[ℝ] HilbertVectorL2 U :=
  (PiLp.proj 2 (fun _ : Fin 2 => HilbertVec 2) 0 : HilbertBlockVec 2 →L[ℝ] HilbertVec 2).compLpL 2 (volumeMeasureOn U)

 def hilbertPureSecond : HilbertVec 2 →ₗᵢ[ℝ] HilbertBlockVec 2 where
  toFun y := PiLp.single 2 1 y
  map_add' _ _ := PiLp.single_add 2 1
  map_smul' c y := by
    apply PiLp.ext
    intro i
    simp only [PiLp.single_apply, PiLp.smul_apply]
    fin_cases i <;> norm_num
  norm_map' y := PiLp.norm_single 2 (fun _ : Fin 2 => HilbertVec 2) 1 y

 def hilbertPureSecondL2 (U : Set (Vec 2)) : HilbertVectorL2 U →L[ℝ] HilbertBlockL2 U :=
  hilbertPureSecond.toContinuousLinearMap.compLpL 2 (volumeMeasureOn U)

 theorem hilbertFirstProjection_pureSecond (U : Set (Vec 2)) (Y : HilbertVectorL2 U) :
    hilbertFirstProjection U (hilbertPureSecondL2 U Y)=0 := by
  apply Lp.ext
  filter_upwards [(PiLp.proj 2 (fun _ : Fin 2 => HilbertVec 2) 0 : HilbertBlockVec 2 →L[ℝ] HilbertVec 2).coeFn_compLpL (hilbertPureSecondL2 U Y),
    hilbertPureSecond.toContinuousLinearMap.coeFn_compLpL Y, Lp.coeFn_zero (E := HilbertVec 2) 2 (volumeMeasureOn U)] with x hx hy hz
  simp only [hilbertFirstProjection, hilbertPureSecondL2] at hx hy ⊢
  rw [hx,hy,hz]
  change (PiLp.single (β := fun _ : Fin 2 => HilbertVec 2) 2 (1 : Fin 2) (Y x)) 0 = 0
  simp only [PiLp.single_apply]
  norm_num

/-- `(R²+grad H10) × L2`, as an exact closed subspace of the actual block L2 carrier. -/
def localizedBlockClosedSubmodule (Q : TriadicCube 2) : ClosedSubmodule ℝ (HilbertBlockL2 (openCubeSet Q)) :=
  (affineGradientClosedSubmodule Q).comap (hilbertFirstProjection (openCubeSet Q))

/-- The same actual closed block space in the fixed coefficient's energy norm. -/
def localizedEnergyClosedSubmodule (Q : TriadicCube 2)
    (D : EnergyHilbertData (H := HilbertBlockL2 (openCubeSet Q))) : ClosedSubmodule ℝ (EnergyCarrier D) :=
  (localizedBlockClosedSubmodule Q).comap (responseEnergyDownCLM D)

 def localizedEnergyFirst (Q : TriadicCube 2)
    (D : EnergyHilbertData (H := HilbertBlockL2 (openCubeSet Q))) :
    localizedEnergyClosedSubmodule Q D →L[ℝ] affineGradientClosedSubmodule Q :=
  (((hilbertFirstProjection (openCubeSet Q)).comp (responseEnergyDownCLM D)).comp
    (localizedEnergyClosedSubmodule Q D).toSubmodule.subtypeL).codRestrict
      (affineGradientClosedSubmodule Q).toSubmodule (fun x => x.property)

 def localizedEnergyPureSecond (Q : TriadicCube 2)
    (D : EnergyHilbertData (H := HilbertBlockL2 (openCubeSet Q))) :
    HilbertVectorL2 (openCubeSet Q) →L[ℝ] localizedEnergyClosedSubmodule Q D :=
  ((responseEnergyUpCLM D).comp (hilbertPureSecondL2 (openCubeSet Q))).codRestrict
    (localizedEnergyClosedSubmodule Q D).toSubmodule (by
      intro Y
      change hilbertFirstProjection _ (hilbertPureSecondL2 _ Y) ∈ affineGradientClosedSubmodule Q
      rw [hilbertFirstProjection_pureSecond]
      exact (affineGradientClosedSubmodule Q).toSubmodule.zero_mem)

 theorem localizedEnergyFirst_pureSecond (Q : TriadicCube 2)
    (D : EnergyHilbertData (H := HilbertBlockL2 (openCubeSet Q))) (Y : HilbertVectorL2 (openCubeSet Q)) :
    localizedEnergyFirst Q D (localizedEnergyPureSecond Q D Y)=0 := by
  apply Subtype.ext
  change hilbertFirstProjection _ (hilbertPureSecondL2 _ Y)=0
  exact hilbertFirstProjection_pureSecond _ Y

end
end ASDExplicitGamma.Variational
