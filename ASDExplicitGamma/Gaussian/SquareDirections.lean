module

public import ASDExplicitGamma.Gaussian.Q3Directions
public import ASDExplicitGamma.Gaussian.SquareTrace

/-! One common physical q3 direction family restricted to arbitrary observation squares. -/

@[expose] public section
namespace ASDExplicitGamma.Gaussian
open Homogenization MeasureTheory ASDExplicitGamma.Inverse ASDExplicitGamma.Main
  ASDExplicitGamma.Response ASDExplicitGamma.Variational
noncomputable section

/-- The same global white-noise direction is restricted to the specified
square; the enumeration is shared by every square in a weighted family. -/
def squareQ3Directions (Q : TriadicCube 2) (b : ℝ) (L : {l : ℝ // 0 < l}) :
    ℕ → ResponseCoefficient (openCubeSet Q) :=
  fun n => mainShellResponseCoefficient Q b L (gaussEnumerated whiteBasis n)

/-- The actual frame-normalized multiplier in one white-noise basis coordinate. -/
def squareQ3BasisMultiplier (Q : TriadicCube 2) (b σ : ℝ)
    (L : {l : ℝ // 0 < l}) (l : whiteBasisIndex) : H1Function (openCubeSet Q) :=
  (σ⁻¹ : ℝ) • (mainQ3DirectionW2 Q b L (whiteBasis l)).value

theorem squareQ3Directions_value (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (n : ℕ) {x : Vec 2} (hx : x ∈ openCubeSet Q) :
    responseCoefficientExtension (squareQ3Directions Q b L n) x =
      q3Convolution b L h3Zero (gaussEnumerated whiteBasis n) x :=
  mainShellResponseCoefficient_extension Q b L _ hx

theorem squareQ3Directions_frameValue (Q : TriadicCube 2) (b σ : ℝ)
    (L : {l : ℝ // 0 < l}) (l : whiteBasisIndex) {x : Vec 2}
    (hx : x ∈ openCubeSet Q) :
    responseCoefficientExtension (squareQ3Directions Q b L
      (@Encodable.encode whiteBasisIndex (Encodable.ofCountable whiteBasisIndex) l)) x / σ =
      (squareQ3BasisMultiplier Q b σ L l).toFun x := by
  rw [squareQ3Directions_value Q b L _ hx]
  simp only [enumerated_encode, squareQ3BasisMultiplier, H1Function.smul_toFun,
    smul_eq_mul, mainQ3DirectionW2_value, div_eq_mul_inv, mul_comm]

/-- Local restriction does not lose square summability: the observation
closure is contained in a larger origin cube whose actual q3 directions
already have a square-summable continuous norm. -/
theorem squareQ3Directions_summable (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0 < l}) :
    Summable (fun n => ‖squareQ3Directions Q b L n‖ ^ 2) := by
  obtain ⟨m, hm⟩ := exists_originCube_containing_compact (closure (openCubeSet Q))
    (isBounded_openCubeSet Q).isCompact_closure
  have hnorm (n : ℕ) : ‖squareQ3Directions Q b L n‖ ≤
      ‖pureFluxMainCubeQ3ResponseCoefficient m b L n‖ := by
    apply (BoundedContinuousFunction.norm_le (norm_nonneg _)).2
    intro x
    change ‖q3Convolution b L h3Zero (gaussEnumerated whiteBasis n) x.1‖ ≤ _
    have hx := hm x.2
    have hval := pureFluxMainCubeQ3ResponseCoefficient_value m b L n hx
    rw [mainQ3DirectionW2_value] at hval
    rw [← hval]
    have h := (responseCoefficientExtension
      (pureFluxMainCubeQ3ResponseCoefficient m b L n)).norm_coe_le_norm x.1
    simpa only [responseCoefficientExtension_norm] using h
  exact Summable.of_nonneg_of_le (fun n => sq_nonneg _)
    (fun n => pow_le_pow_left₀ (norm_nonneg _) (hnorm n) 2)
    (main_q3_responseCoefficient_summable m b L)

/-- Removing the zero-padding does not change a scalar contraction of the
actual globally indexed square directions. -/
theorem squareQ3Directions_tsum_apply (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (f : ResponseCoefficient (openCubeSet Q) → ℝ)
    (hf : f 0 = 0) :
    (∑' n, f (squareQ3Directions Q b L n)) =
      ∑' l : whiteBasisIndex, f (squareQ3Directions Q b L
        (@Encodable.encode whiteBasisIndex (Encodable.ofCountable whiteBasisIndex) l)) := by
  let enc := @Encodable.encode whiteBasisIndex (Encodable.ofCountable whiteBasisIndex)
  let v := fun l => squareQ3Directions Q b L (enc l)
  have hzero : mainShellResponseCoefficient Q b L 0 = 0 := by
    ext x
    change q3Convolution b L h3Zero 0 x.1 = 0
    simp only [q3Convolution, inner_zero_left]
  have hz (n : ℕ) (hn : n ∉ Set.range enc) : squareQ3Directions Q b L n = 0 := by
    unfold squareQ3Directions gaussEnumerated
    rw [Function.extend_apply' _ _ _ hn]
    exact hzero
  have heq (n : ℕ) : squareQ3Directions Q b L n = gaussEnumerated v n := by
    by_cases hn : n ∈ Set.range enc
    · obtain ⟨l, rfl⟩ := hn
      rw [enumerated_encode]
    · rw [hz n hn, gaussEnumerated, Function.extend_apply' _ _ _ hn]
      rfl
  simp_rw [heq]
  simpa only [enumerated_encode] using enumerated_tsum_apply v f hf

end
end ASDExplicitGamma.Gaussian
