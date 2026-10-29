module

public import ASDExplicitGamma.Variational.ForcedSourceFeedback

/-! The generic forced-gradient estimate in the paired response formulation. -/

@[expose] public section
namespace ASDExplicitGamma.Variational

open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Scalar
open ASDExplicitGamma.Triadic
open scoped BigOperators

noncomputable section

/-- A forced weak equation on the parent restricts to every descendant by
zero extension of the variation. -/
theorem forcedSource_weakEquation_onDescendant (Q : TriadicCube 2) (j : ℕ)
    (R : TriadicCube 2) (hR : R ∈ descendantsAtDepth Q j)
    {a : CoeffField 2} (W : BlockState 2) (G : Vec 2 → Vec 2)
    (hforced : ∀ T : BlockState 2, ScalarVariation (openCubeSet Q) T.eval →
      volumeAverage (openCubeSet Q) (blockPairingIntegrand a T W) =
        volumeAverage (openCubeSet Q) (fun x => vecDot (T.potential x) (G x)))
    (T : BlockState 2) (hT : ScalarVariation (openCubeSet R) T.eval) :
    volumeAverage (openCubeSet R) (blockPairingIntegrand a T W) =
      volumeAverage (openCubeSet R) (fun x => vecDot (T.potential x) (G x)) := by
  let U := openCubeSet Q
  let V := openCubeSet R
  let Text : BlockState 2 :=
    { potential := fun x => V.indicator T.potential x
      flux := fun x => V.indicator T.flux x }
  have hEval : Text.eval = V.indicator T.eval := by
    funext x
    by_cases hx : x ∈ V
    · simp [Text, BlockState.eval, hx]
    · simp [Text, BlockState.eval, hx]
  have hText : ScalarVariation U Text.eval := by
    rw [hEval]
    exact scalar_variation_zero_extension (isOpen_openCubeSet R)
      (isOpen_openCubeSet Q)
      (openCubeSet_subset_of_mem_descendantsAtDepth hR) hT
  have hparent := hforced Text hText
  have hPair : blockPairingIntegrand a Text W =
      V.indicator (blockPairingIntegrand a T W) := by
    funext x
    by_cases hx : x ∈ V
    · simp [blockPairingIntegrand, Text, BlockState.eval, blockVecDot, vecDot, hx]
    · simp [blockPairingIntegrand, Text, BlockState.eval, blockVecDot, vecDot, hx]
  have hSource : (fun x => vecDot (Text.potential x) (G x)) =
      V.indicator (fun x => vecDot (T.potential x) (G x)) := by
    funext x
    by_cases hx : x ∈ V <;> simp [Text, vecDot, hx]
  have hvol : (MeasureTheory.volume U).toReal ≠ 0 := by
    rw [volume_openCubeSet_toReal]
    exact (cubeVolume_pos Q).ne'
  have hintegral :
      ∫ x in U, blockPairingIntegrand a Text W x ∂volume =
        ∫ x in U, vecDot (Text.potential x) (G x) ∂volume := by
    unfold volumeAverage at hparent
    exact (mul_left_cancel₀ (inv_ne_zero hvol) hparent)
  have hrestricted := hintegral
  rw [hPair, hSource, integral_indicator (measurableSet_openCubeSet R),
    integral_indicator (measurableSet_openCubeSet R)] at hrestricted
  rw [Measure.restrict_restrict (measurableSet_openCubeSet R)] at hrestricted
  rw [Set.inter_eq_left.mpr (openCubeSet_subset_of_mem_descendantsAtDepth hR)] at hrestricted
  unfold volumeAverage
  exact congrArg (fun z : ℝ => (MeasureTheory.volume V).toReal⁻¹ * z) hrestricted

end
end ASDExplicitGamma.Variational
