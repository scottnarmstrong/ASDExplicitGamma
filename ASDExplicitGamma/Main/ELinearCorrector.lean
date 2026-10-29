module

public import ASDExplicitGamma.Main.ELinearHistoryBridge
public import ASDExplicitGamma.Main.DirectionalPhysicalFlux

/-! Translation of the OLD trace and corrector histories of a depth-five cell
to the origin cell at that scale, and the resulting actual-law payment of the
corrector history by the multiplier product `D M H`. -/

@[expose] public section

namespace ASDExplicitGamma.Main

attribute [local irreducible] Homogenization.descendantsAtDepth

open Homogenization MeasureTheory ASDExplicitGamma.Gaussian ASDExplicitGamma.Model
  ASDExplicitGamma.Native ASDExplicitGamma.Response ASDExplicitGamma.Scalar
  ASDExplicitGamma.Triadic ASDExplicitGamma.Variational
open Algsuperdiff.Section3 Algsuperdiff.Section3.Cutoff
open scoped ENNReal

noncomputable section

private theorem e_linear_vec_descendant
    (z : Fin 2 → ℤ) (Q R : TriadicCube 2) (j : ℕ)
    (hR : R ∈ descendantsAtDepth Q j) :
    nativeHeatCubeTranslationVector (descendantTranslationShift j z) R =
      nativeHeatCubeTranslationVector z Q := by
  have hscale : R.scale = Q.scale - (j : ℤ) :=
    scale_eq_sub_of_mem_descendantsAtDepth hR
  have hpow : (3 : ℝ) ^ (j : ℤ) * (3 : ℝ) ^ (Q.scale - (j : ℤ)) =
      (3 : ℝ) ^ Q.scale := by
    rw [← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    congr 1
    omega
  ext i
  simp only [nativeHeatCubeTranslationVector, descendantTranslationShift,
    Int.cast_mul, Int.cast_pow, Int.cast_ofNat, cubeScaleFactor]
  rw [hscale]
  have hnat : (3 : ℝ) ^ j = (3 : ℝ) ^ (j : ℤ) := by norm_cast
  rw [hnat]
  calc
    _ = (z i : ℝ) *
        ((3 : ℝ) ^ (j : ℤ) * (3 : ℝ) ^ (Q.scale - (j : ℤ))) := by ring
    _ = _ := by rw [hpow]

private theorem e_linear_openCube_translate
    (z : Fin 2 → ℤ) (Q : TriadicCube 2) :
    openCubeSet (translateCube z Q) =
      translateSet (nativeHeatCubeTranslationVector z Q) (openCubeSet Q) := by
  ext x
  rw [mem_translateSet_iff_sub_mem, mem_openCubeSet_translateCube_iff]
  rfl

/-- The depth-`j` average of trace defects is unchanged by translating the
cell together with the coefficient field. -/
theorem old_signed_trace_depth_average_translateCube
    (z : Fin 2 → ℤ) (Q : TriadicCube 2) (a : CoeffField 2) (j : ℕ) :
    descendantsAverage (translateCube z Q) j (fun R =>
        traceDefect (openCubeSet R)
          (translateCoeffField (-nativeHeatCubeTranslationVector z Q) a) 1) =
      descendantsAverage Q j (fun R => traceDefect (openCubeSet R) a 1) := by
  classical
  unfold descendantsAverage
  dsimp only
  rw [descendantsAtDepth_translateCube z Q j]
  have hinj : Set.InjOn (translateCube (descendantTranslationShift j z))
      (descendantsAtDepth Q j : Set (TriadicCube 2)) :=
    (Homogenization.Book.Ch02.translateCube_injective _).injOn
  rw [Finset.card_image_of_injOn hinj, Finset.sum_image hinj]
  congr 1
  apply Finset.sum_congr rfl
  intro R hR
  have hz := e_linear_vec_descendant z Q R j hR
  rw [e_linear_openCube_translate, hz, Model.traceDefect_translate]
  have hcoeff : translateCoeffField (nativeHeatCubeTranslationVector z Q)
      (translateCoeffField (-nativeHeatCubeTranslationVector z Q) a) = a := by
    funext x
    simp [translateCoeffField]
  rw [hcoeff]

theorem old_signed_traceHistory_translateCube
    (z : Fin 2 → ℤ) (Q : TriadicCube 2) (a : CoeffField 2) :
    oldSignedTraceHistory (translateCube z Q)
        (translateCoeffField (-nativeHeatCubeTranslationVector z Q) a) =
      oldSignedTraceHistory Q a := by
  unfold oldSignedTraceHistory
  apply congrArg (fun r : ℝ≥0∞ => ENNReal.ofReal (1 - inverseHistoryDiscount) * r)
  apply tsum_congr
  intro j
  rw [old_signed_trace_depth_average_translateCube]

theorem old_signed_correctorHistory_translateCube
    (z : Fin 2 → ℤ) (Q : TriadicCube 2) (a : CoeffField 2) :
    oldSignedCorrectorHistory (translateCube z Q)
        (translateCoeffField (-nativeHeatCubeTranslationVector z Q) a) =
      oldSignedCorrectorHistory Q a := by
  unfold oldSignedCorrectorHistory
  rw [main_eosc_responseHistory_translateCube,
    old_signed_traceHistory_translateCube]

end

end ASDExplicitGamma.Main
