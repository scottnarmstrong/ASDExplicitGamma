module

public import ASDExplicitGamma.Inverse.PureFluxGeneratorSourceMap
public import ASDExplicitGamma.Main.CubeDirections

/-! The compact Gaussian q3 coefficient directions are the same physical
W² multipliers used by the DIAG source-row estimates. -/

@[expose] public section

open Homogenization MeasureTheory ASDExplicitGamma.Gaussian ASDExplicitGamma.Main
  ASDExplicitGamma.Response ASDExplicitGamma.Triadic ASDExplicitGamma.Variational

namespace ASDExplicitGamma.Inverse

/-- The response coefficient represented by one actual main-cube q3 H³
direction. -/
noncomputable def pureFluxMainCubeQ3ResponseCoefficient (n : ℤ) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (j : ℕ) :
    ResponseCoefficient (openCubeSet (originCube 2 n)) := by
  let Q := originCube 2 n
  letI pureFluxQ3MapCompact : CompactSpace (closure (openCubeSet Q)) := isCompact_iff_compactSpace.mp
    (isBounded_openCubeSet Q).isCompact_closure
  let incl : C(closure (openCubeSet Q), closure (cubeSet Q)) :=
    ⟨fun x => ⟨x.1, closure_mono (openCubeSet_subset_cubeSet Q) x.2⟩,
      continuous_subtype_val.subtype_mk _⟩
  exact BoundedContinuousFunction.mkOfCompact
    ((mainCubeH3Value n b L (mainCubeQ3Directions n b L j)).comp incl)

/-- On the observation cube, the actual coefficient extension agrees with
the exact q3 W² value field used in the row product theorem. -/
theorem pureFluxMainCubeQ3ResponseCoefficient_value (n : ℤ) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (j : ℕ) {x : Vec 2}
    (hx : x ∈ openCubeSet (originCube 2 n)) :
    responseCoefficientExtension
        (pureFluxMainCubeQ3ResponseCoefficient n b L j) x =
      (mainQ3DirectionW2 (originCube 2 n) b L
        (gaussEnumerated whiteBasis j)).value x := by
  rw [responseCoefficientExtension_eq _ hx]
  simp only [pureFluxMainCubeQ3ResponseCoefficient,
    BoundedContinuousFunction.mkOfCompact_apply, ContinuousMap.comp_apply]
  change mainCubeH3Value n b L (mainCubeQ3Directions n b L j)
      ⟨x, subset_closure (openCubeSet_subset_cubeSet (originCube 2 n) hx)⟩ = _
  rw [mainCubeH3Value_direction]
  exact (mainQ3DirectionW2_value (originCube 2 n) b L
    (gaussEnumerated whiteBasis j) x).symm

/-- The coefficient divided by the frame scale is exactly the multiplier
required by the physical response shear. -/
theorem pureFluxMainCubeQ3ResponseCoefficient_frameValue (n : ℤ) (b σ : ℝ)
    (L : {l : ℝ // 0 < l}) (j : ℕ) {x : Vec 2}
    (hx : x ∈ openCubeSet (originCube 2 n)) :
    responseCoefficientExtension
        (pureFluxMainCubeQ3ResponseCoefficient n b L j) x / σ =
      ((σ⁻¹ : ℝ) •
        (mainQ3DirectionW2 (originCube 2 n) b L
          (gaussEnumerated whiteBasis j)).value).toFun x := by
  rw [pureFluxMainCubeQ3ResponseCoefficient_value n b L j hx]
  simp [H1Function.smul_toFun, div_eq_mul_inv, mul_comm]

end ASDExplicitGamma.Inverse
