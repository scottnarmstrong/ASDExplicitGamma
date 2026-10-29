module

public import ASDExplicitGamma.Cold.SquareMixedParseval
public import Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.FaceVanishCollar

/-! # Legitimate zero-boundary sine tests for distributional divergence -/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology Homogenization
open ASDExplicitGamma.Triadic ASDExplicitGamma.Triadic.Torus
open scoped BigOperators ENNReal

namespace ASDExplicitGamma.Cold

/-- Coordinate differentiation of an arbitrary mixed mode in a sine coordinate. -/
theorem fderiv_mixed_mode_apply {d : ℕ} (Q : TriadicCube d)
    (O : Finset (Fin d)) (p : Fin d → ℤ) (i : Fin d) (hi : i ∈ O) (x : Vec d) :
    fderiv ℝ (boxMode (cubeCorner Q) (cubeScaleFactor Q) O p) x (basisVec i) =
      cubeFreq Q p i * boxMode (cubeCorner Q) (cubeScaleFactor Q) (O.erase i) p x := by
  have hd : ∀ j, Differentiable ℝ (modeFactor (cubeCorner Q) (cubeScaleFactor Q) O p j) :=
    fun j => (contDiff_modeFactor _ _ _ _ j (m := 1)).differentiable (by simp)
  rw [show boxMode (cubeCorner Q) (cubeScaleFactor Q) O p =
    (fun y => ∏ j, modeFactor (cubeCorner Q) (cubeScaleFactor Q) O p j (y j)) from rfl,
    fderiv_prod_apply_basisVec _ hd x i,
    (hasDerivAt_modeFactor_sin_set (cubeCorner Q) (cubeScaleFactor Q) p i O hi (x i)).deriv,
    boxMode_eq_prod_modeFactor, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
  have hrest : ∏ j ∈ Finset.univ.erase i,
      modeFactor (cubeCorner Q) (cubeScaleFactor Q) O p j (x j) =
      ∏ j ∈ Finset.univ.erase i,
      modeFactor (cubeCorner Q) (cubeScaleFactor Q) (O.erase i) p j (x j) := by
    apply Finset.prod_congr rfl
    intro j hj
    have hji := Finset.ne_of_mem_erase hj
    unfold modeFactor
    simp [hji]
  rw [hrest]
  unfold cubeFreq
  ring

/-- The sine/sine mode vanishes on each lower face. -/
theorem square_sine_lower_face (Q : TriadicCube 2) (p : Fin 2 → ℤ) (i : Fin 2) (x : Vec 2) :
    boxMode (cubeCorner Q) (cubeScaleFactor Q) Finset.univ p (cubeLowerFaceProjection Q i x) = 0 := by
  rw [boxMode_eq_prod_modeFactor]
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simp [modeFactor, cubeLowerFaceProjection, cubeLowerFaceCoord, cubeCorner]

/-- The sine/sine mode vanishes on each upper face. -/
theorem square_sine_upper_face (Q : TriadicCube 2) (p : Fin 2 → ℤ) (i : Fin 2) (x : Vec 2) :
    boxMode (cubeCorner Q) (cubeScaleFactor Q) Finset.univ p (cubeUpperFaceProjection Q i x) = 0 := by
  rw [boxMode_eq_prod_modeFactor]
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simp only [modeFactor, Finset.mem_univ, ite_true, cubeUpperFaceProjection, Function.update_self]
  have he : cubeUpperFaceCoord Q i - cubeCorner Q i = cubeScaleFactor Q := by
    unfold cubeUpperFaceCoord cubeCorner; ring
  rw [he, mul_div_cancel_right₀ _ (cubeScaleFactor_pos' Q).ne']
  simpa only [mul_comm] using Real.sin_int_mul_pi (p i)

/-- A sine/sine mode is a genuine H¹₀ test, supplied by the zero-face closure theorem. -/
def squareSineH10 (Q : TriadicCube 2) (p : Fin 2 → ℤ) : H10Function (openCubeSet Q) :=
  H10Function.ofContDiffFaceZeroOnOpenCubeSetNoCompact Q
    (contDiff_cubeDirichletMode Q Finset.univ p)
    (square_sine_lower_face Q p) (square_sine_upper_face Q p)

/-- The H¹₀ test has the required classical derivative almost everywhere. -/
theorem squareSineH10_grad (Q : TriadicCube 2) (p : Fin 2 → ℤ) (i : Fin 2) :
    (fun x => (squareSineH10 Q p).toH1Function.grad x i) =ᵐ[volume.restrict (openCubeSet Q)]
      (fun x => cubeFreq Q p i * boxMode (cubeCorner Q) (cubeScaleFactor Q)
        (Finset.univ.erase i) p x) := by
  filter_upwards [ae_restrict_mem (measurableSet_openCubeSet Q)] with x hx
  have he : (fun y => faceCompactifyingCutoff Q y *
      boxMode (cubeCorner Q) (cubeScaleFactor Q) Finset.univ p y) =ᶠ[𝓝 x]
      boxMode (cubeCorner Q) (cubeScaleFactor Q) Finset.univ p := by
    filter_upwards [(isOpen_openCubeSet Q).mem_nhds hx] with y hy
    rw [faceCompactifyingCutoff_eq_one_on_openCubeSet Q hy, one_mul]
  unfold squareSineH10 H10Function.ofContDiffFaceZeroOnOpenCubeSetNoCompact
  rw [H10Function.ofContDiffFaceZeroOnOpenCubeSet_grad]
  dsimp only
  rw [he.fderiv_eq]
  exact fderiv_mixed_mode_apply Q Finset.univ p i (Finset.mem_univ i) x

end ASDExplicitGamma.Cold
