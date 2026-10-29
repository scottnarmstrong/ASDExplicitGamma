module

public import ASDExplicitGamma.Inverse.PureFluxGeneratorHistory
public import Homogenization.CoarseGraining.Translation
public import Homogenization.Geometry.TriadicCubeTranslation

/-! Translation covariance of the complete inverse histories used in the
source VHEAT drift row. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open Homogenization ASDExplicitGamma.Inverse ASDExplicitGamma.Variational

noncomputable def nativeHeatCubeTranslationVector {d : ℕ}
    (z : Fin d → ℤ) (Q : TriadicCube d) : Vec d :=
  fun i => (z i : ℝ) * cubeScaleFactor Q

private theorem nativeHeat_openCubeSet_translateCube_eq {d : ℕ}
    (z : Fin d → ℤ) (Q : TriadicCube d) :
    openCubeSet (translateCube z Q) =
      translateSet (nativeHeatCubeTranslationVector z Q) (openCubeSet Q) := by
  ext x
  rw [mem_translateSet_iff_sub_mem]
  rw [mem_openCubeSet_translateCube_iff]
  rfl

private theorem nativeHeat_descendantTranslationVector_eq {d : ℕ}
    (z : Fin d → ℤ) (Q R : TriadicCube d) (k : ℕ)
    (hR : R ∈ descendantsAtDepth Q k) :
    nativeHeatCubeTranslationVector (descendantTranslationShift k z) R =
      nativeHeatCubeTranslationVector z Q := by
  have hscale : R.scale = Q.scale - (k : ℤ) :=
    scale_eq_sub_of_mem_descendantsAtDepth hR
  have hpow : (3 : ℝ) ^ (k : ℤ) * (3 : ℝ) ^ (Q.scale - (k : ℤ)) =
      (3 : ℝ) ^ Q.scale := by
    rw [← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    congr 1
    omega
  ext i
  simp only [nativeHeatCubeTranslationVector, descendantTranslationShift,
    Int.cast_mul, Int.cast_pow, Int.cast_ofNat, cubeScaleFactor]
  rw [hscale]
  have hnat : (3 : ℝ) ^ k = (3 : ℝ) ^ (k : ℤ) := by norm_cast
  rw [hnat]
  calc
    _ = (z i : ℝ) *
        ((3 : ℝ) ^ (k : ℤ) * (3 : ℝ) ^ (Q.scale - (k : ℤ))) := by ring
    _ = _ := by rw [hpow]

/-- The level-`k` inverse-operator envelope is unchanged by translating the
cell and translating the coefficient field with it. -/
theorem nativeHeat_lemmaVInverseDepthMax_translateCube {d : ℕ}
    (z : Fin d → ℤ) (Q : TriadicCube d) (a : CoeffField d) (k : ℕ) :
    lemmaVInverseDepthMax (translateCube z Q)
        (translateCoeffField
          (-nativeHeatCubeTranslationVector z Q) a) k =
      lemmaVInverseDepthMax Q a k := by
  classical
  unfold lemmaVInverseDepthMax
  rw [descendantsAtDepth_translateCube z Q k]
  apply Book.Ch02.finsetSupReal_image
  intro R hR
  have hz := nativeHeat_descendantTranslationVector_eq z Q R k hR
  rw [nativeHeat_openCubeSet_translateCube_eq]
  rw [hz, sigmaStarInvCoarse_translateSet_eq_translateCoeffField]
  have hcoeff : translateCoeffField (nativeHeatCubeTranslationVector z Q)
      (translateCoeffField (-nativeHeatCubeTranslationVector z Q) a) = a := by
    funext x
    simp [translateCoeffField]
  rw [hcoeff]

/-- The complete Lemma V history is invariant under the same exact spatial
translation, with no truncation of its infinite descendant series. -/
theorem nativeHeat_lemmaVInverseHistory_translateCube {d : ℕ}
    (z : Fin d → ℤ) (Q : TriadicCube d) (a : CoeffField d) (q : ℝ) :
    lemmaVInverseHistory (translateCube z Q)
        (translateCoeffField
          (-nativeHeatCubeTranslationVector z Q) a) q =
      lemmaVInverseHistory Q a q := by
  unfold lemmaVInverseHistory
  congr 1
  apply tsum_congr
  intro k
  exact congrArg (fun x : ℝ => (q⁻¹) ^ k * x)
    (nativeHeat_lemmaVInverseDepthMax_translateCube z Q a k)

end ASDExplicitGamma.Native

end
