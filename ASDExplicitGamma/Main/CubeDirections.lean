module

public import ASDExplicitGamma.Main.CubeFactor
public import ASDExplicitGamma.Main.CMW2

/-! Smooth global representatives of the actual cube heat-factor directions. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Homogenization ASDExplicitGamma.Gaussian ASDExplicitGamma.Triadic

/-- The same zero-padded white basis used in the actual H3 heat realization. -/
noncomputable def mainQ3GlobalDirection (b : ℝ) (L : {l : ℝ // 0 < l}) (j : ℕ) : Vec 2 → ℝ :=
  q3Convolution b L h3Zero (gaussEnumerated whiteBasis j)

/-- Every actual heat direction is the restriction of this physical C3
convolution, with no regular-direction premise. -/
theorem mainCubeH3Value_direction (n : ℤ) (b : ℝ) (L : {l : ℝ // 0 < l})
    (j : ℕ) (x : closure (cubeSet (originCube 2 n))) :
    mainCubeH3Value n b L (mainCubeQ3Directions n b L j) x = mainQ3GlobalDirection b L j x.1 := by
  classical
  let enc := @Encodable.encode whiteBasisIndex (Encodable.ofCountable whiteBasisIndex)
  by_cases hj : j ∈ Set.range enc
  · obtain ⟨i, rfl⟩ := hj
    simp only [mainCubeQ3Directions, q3H3Directions, mainQ3GlobalDirection,
      enc, enumerated_encode]
    exact mainCubeH3Value_factor n b L _ x
  · rw [mainCubeQ3Directions, q3H3Directions, gaussEnumerated,
      Function.extend_apply' _ _ _ hj]
    rw [mainQ3GlobalDirection, gaussEnumerated, Function.extend_apply' _ _ _ hj]
    simp [q3Convolution]

end ASDExplicitGamma.Main
