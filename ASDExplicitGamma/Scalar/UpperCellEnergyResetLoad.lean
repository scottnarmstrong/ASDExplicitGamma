module

public import ASDExplicitGamma.Scalar.UpperCellEnergyResetMean
public import ASDExplicitGamma.Scalar.UpperCellEnergyBandLoad

/-! The canonical centered physical full band is an actual bottom load. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization Response MeasureTheory Algsuperdiff.Section3
noncomputable section

/-- A physical load with constant top component has exactly that top mean. -/
theorem upper_cell_reset_mean_top (Q : TriadicCube 2) (e : Vec 2)
    (f : Vec 2 → BlockVec 2) (hf : ∀ x, (f x).1=e)
    (F : HilbertBlockL2 (openCubeSet Q))
    (hF : F =ᵐ[volumeMeasureOn (openCubeSet Q)] fun x => HilbertBlockVec.ofBlockVec (f x)) :
    (upperCellResetMeanValue Q F).1=e := by
  funext i
  have hm := upper_cell_reset_mean_of_ae_field Q F f hF (.inl i)
  change (upperCellResetMeanValue Q F).1 i = cubeAverage Q (fun x => (f x).1 i) at hm
  simpa only [hf,cubeAverage_const] using hm

/-- The canonical fluctuation is literally the bottom field with its cell
mean removed, with equality of representatives on the physical cube. -/
theorem upper_cell_reset_centered_bottom (Q : TriadicCube 2) (e : Vec 2)
    (f : Vec 2 → BlockVec 2) (hf : ∀ x, (f x).1=e)
    (F : HilbertBlockL2 (openCubeSet Q))
    (hF : F =ᵐ[volumeMeasureOn (openCubeSet Q)] fun x => HilbertBlockVec.ofBlockVec (f x)) :
    F-upperCellResetMeanField Q F =ᵐ[volumeMeasureOn (openCubeSet Q)]
      fun x => HilbertBlockVec.ofBlockVec
        (0,(f x).2-(upperCellResetMeanValue Q F).2) := by
  have ht := upper_cell_reset_mean_top Q e f hf F hF
  filter_upwards [hF,upper_cell_reset_mean_field_ae Q F,
    Lp.coeFn_sub F (upperCellResetMeanField Q F)] with x hfx hmx hsub
  rw [hsub,Pi.sub_apply,hfx,hmx]
  apply (HilbertBlockVec.continuousLinearEquivBlockVec 2).injective
  simp only [map_sub]
  change f x-upperCellResetMeanValue Q F=(0,(f x).2-(upperCellResetMeanValue Q F).2)
  apply Prod.ext
  · change (f x).1-(upperCellResetMeanValue Q F).1=0
    rw [hf,ht,sub_self]
  · rfl

/-- Actual band-load lifts give the centered bottom source. The sole
representation premise is literal physical AE equality, not a moment bound. -/
theorem upper_cell_reset_actual_band_centered
    (M : ABKModel 2) (n terminal : ℤ) (sigma : ℝ) (e : Vec 2)
    (Q : TriadicCube 2) (F : Cutoff.CutoffSample 2 → HilbertBlockL2 (openCubeSet Q))
    (hF : ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      ∃ hω : MemBlockL2 (openCubeSet Q) (bandLoad M n terminal sigma e ω),
        F ω=toHilbertBlockL2OfBlockField hω) :
    ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      F ω-upperCellResetMeanField Q (F ω) =ᵐ[volumeMeasureOn (openCubeSet Q)]
        fun x => HilbertBlockVec.ofBlockVec
          (0,(bandLoad M n terminal sigma e ω x).2-
            (upperCellResetMeanValue Q (F ω)).2) := by
  filter_upwards [hF] with ω hω
  obtain ⟨hω,heq⟩ := hω
  apply upper_cell_reset_centered_bottom Q e (bandLoad M n terminal sigma e ω)
    (fun _ => rfl) (F ω)
  rw [heq]
  exact coeFn_toHilbertBlockL2OfBlockField hω

end
end ASDExplicitGamma.Scalar
