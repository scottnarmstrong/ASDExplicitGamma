/-
Copyright (c) 2026 Scott N. Armstrong. All rights reserved.
-/
module

public import ASDExplicitGamma.Scalar.SmoothFeedbackGammaRotation
public import Homogenization.Geometry.TriadicCubeTranslation
public import Homogenization.Geometry.TriadicPartition
public import Homogenization.Multiscale.CubeAverage
public import ASDExplicitGamma.Main.DirectionalSymmetry
public import ASDExplicitGamma.Scalar.SmoothFeedback
public import Algsuperdiff.Section3.Cutoff.Symmetry
import Homogenization.Sobolev.Fractional.EuclideanWspTranslation

/-! Translation covariance for the cell-local weak-Haar quantities used by
the smooth-feedback rotation transport. -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open Homogenization MeasureTheory ASDExplicitGamma.Triadic
open Algsuperdiff.Section3 Algsuperdiff.Frozen.Assumptions
open ASDExplicitGamma.Response

noncomputable section

/-- The physical displacement of an integer-grid translation of a triadic
cube. -/
def smoothFeedbackCubeTranslationVector (Q : TriadicCube 2)
    (shift : Fin 2 → ℤ) : Vec 2 :=
  fun i => (shift i : ℝ) * cubeScaleFactor Q

private theorem cubeSet_translateCube_as_translateSet
    (Q : TriadicCube 2) (shift : Fin 2 → ℤ) :
    cubeSet (translateCube shift Q) =
      translateSet (smoothFeedbackCubeTranslationVector Q shift) (cubeSet Q) := by
  ext x
  rw [mem_cubeSet_translateCube_iff, mem_translateSet_iff_sub_mem]
  rfl

private theorem translateCube_injective' (shift : Fin 2 → ℤ) :
    Function.Injective (translateCube shift : TriadicCube 2 → TriadicCube 2) := by
  intro Q R h
  cases Q with
  | mk qscale qindex =>
    cases R with
    | mk rscale rindex =>
      simp only [translateCube, TriadicCube.mk.injEq] at h
      rcases h with ⟨hscale, hindex⟩
      subst rscale
      have hindices : qindex = rindex := by
        funext i
        have hi := congrFun hindex i
        omega
      subst rindex
      rfl

/-- Cube averages commute with translations by an integer number of parent
side lengths. -/
theorem cubeAverage_translateCube
    (Q : TriadicCube 2) (shift : Fin 2 → ℤ) (f : Vec 2 → ℝ) :
    cubeAverage (translateCube shift Q)
        (fun x => f (x - smoothFeedbackCubeTranslationVector Q shift)) =
      cubeAverage Q f := by
  let z := smoothFeedbackCubeTranslationVector Q shift
  unfold cubeAverage
  rw [show cubeVolume (translateCube shift Q) = cubeVolume Q by
    simp [cubeVolume]]
  rw [cubeSet_translateCube_as_translateSet]
  congr 1
  calc
    (∫ x in translateSet z (cubeSet Q), f (x - z) ∂volume) =
        ∫ x in cubeSet Q, f ((x + z) - z) ∂volume :=
      (setIntegral_comp_addRight_translateSet z (cubeSet Q)
        (fun x => f (x - z))).symm
    _ = ∫ x in cubeSet Q, f x ∂volume := by
      congr 1
      funext x
      simp [sub_eq_add_neg, add_assoc]

/-- The normalized scalar energy is invariant under the same cell
translation. -/
theorem energy_translateCube
    (Q : TriadicCube 2) (shift : Fin 2 → ℤ) (f : Vec 2 → ℝ) :
    energy (translateCube shift Q)
        (fun x => f (x - smoothFeedbackCubeTranslationVector Q shift)) =
      energy Q f := by
  unfold energy pairing
  exact cubeAverage_translateCube Q shift (fun x => f x * f x)

private theorem descendant_translation_vector
    (Q R : TriadicCube 2) (j : ℕ) (shift : Fin 2 → ℤ)
    (hR : R ∈ descendantsAtDepth Q j) :
    smoothFeedbackCubeTranslationVector R
        (descendantTranslationShift j shift) =
      smoothFeedbackCubeTranslationVector Q shift := by
  ext i
  have hscale := scale_eq_sub_of_mem_descendantsAtDepth hR
  simp only [smoothFeedbackCubeTranslationVector,
    descendantTranslationShift, cubeScaleFactor]
  rw [hscale]
  push_cast
  calc
    (3 : ℝ) ^ (j : ℤ) * (shift i : ℝ) *
        (3 : ℝ) ^ (Q.scale - (j : ℤ)) =
      (shift i : ℝ) *
        ((3 : ℝ) ^ (j : ℤ) * (3 : ℝ) ^ (Q.scale - (j : ℤ))) := by ring
    _ = (shift i : ℝ) * (3 : ℝ) ^ Q.scale := by
      rw [← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
      congr 2
      omega

/-- A finite triadic projection commutes with translation by an integer
multiple of the parent side length. -/
theorem cubeProjection_translateCube
    (Q : TriadicCube 2) (shift : Fin 2 → ℤ) (j : ℕ) (f : Vec 2 → ℝ) :
    cubeProjection (translateCube shift Q) j
        (fun x => f (x - smoothFeedbackCubeTranslationVector Q shift)) =
      fun x => cubeProjection Q j f
        (x - smoothFeedbackCubeTranslationVector Q shift) := by
  classical
  let z := smoothFeedbackCubeTranslationVector Q shift
  funext x
  unfold cubeProjection
  rw [descendantsAtDepth_translateCube shift Q j]
  rw [Finset.sum_image (translateCube_injective'
    (descendantTranslationShift j shift)).injOn]
  apply Finset.sum_congr rfl
  intro R hR
  have hz := descendant_translation_vector Q R j shift hR
  have hset : cubeSet (translateCube (descendantTranslationShift j shift) R) =
      translateSet z (cubeSet R) := by
    rw [cubeSet_translateCube_as_translateSet]
    simp only [z]
    rw [hz]
  have havg : cubeAverage (translateCube (descendantTranslationShift j shift) R)
      (fun y => f (y - z)) = cubeAverage R f := by
    simpa only [z, hz] using
      cubeAverage_translateCube R (descendantTranslationShift j shift) f
  rw [hset, havg, mem_translateSet_iff_sub_mem]

private theorem cubeIncrement_translateCube
    (Q : TriadicCube 2) (shift : Fin 2 → ℤ) (j : ℕ) (f : Vec 2 → ℝ) :
    cubeIncrement (translateCube shift Q) j
        (fun x => f (x - smoothFeedbackCubeTranslationVector Q shift)) =
      fun x => cubeIncrement Q j f
        (x - smoothFeedbackCubeTranslationVector Q shift) := by
  funext x
  cases j with
  | zero =>
      simp only [cubeIncrement_zero]
      exact congrFun (cubeProjection_translateCube Q shift 0 f) x
  | succ j =>
      simp only [cubeIncrement_succ]
      rw [cubeProjection_translateCube Q shift (j + 1) f,
        cubeProjection_translateCube Q shift j f]

private theorem primalEnergy_translateCube
    (Q : TriadicCube 2) (shift : Fin 2 → ℤ) (q : ℝ) (f : Vec 2 → ℝ) :
    primalEnergy (translateCube shift Q) q
        (fun x => f (x - smoothFeedbackCubeTranslationVector Q shift)) =
      primalEnergy Q q f := by
  unfold primalEnergy
  rw [show energy (translateCube shift Q)
      (cubeIncrement (translateCube shift Q) 0
        (fun x => f (x - smoothFeedbackCubeTranslationVector Q shift))) =
      energy Q (cubeIncrement Q 0 f) by
        rw [cubeIncrement_translateCube, energy_translateCube]]
  congr 1
  apply tsum_congr
  intro k
  rw [show energy (translateCube shift Q)
      (cubeIncrement (translateCube shift Q) (k + 1)
        (fun x => f (x - smoothFeedbackCubeTranslationVector Q shift))) =
      energy Q (cubeIncrement Q (k + 1) f) by
        rw [cubeIncrement_translateCube, energy_translateCube]]

/-- The weak-Haar energy of a vector field is invariant under the same cell
translation, after translating each coordinate function. -/
theorem vectorWeakHaarEnergy_translateCube
    (Q : TriadicCube 2) (shift : Fin 2 → ℤ) (F : Vec 2 → Fin 2 → ℝ) :
    vectorWeakHaarEnergy (translateCube shift Q)
        (fun x i => F (x - smoothFeedbackCubeTranslationVector Q shift) i) =
      vectorWeakHaarEnergy Q F := by
  unfold vectorWeakHaarEnergy
  apply Finset.sum_congr rfl
  intro i hi
  unfold dualEnergy
  exact primalEnergy_translateCube Q shift (Real.sqrt 3)⁻¹
    (fun x => F x i)

private theorem dualEnergy_neg (Q : TriadicCube 2) (q : ℝ)
    (f : Vec 2 → ℝ) :
    dualEnergy Q q (fun x => -f x) = dualEnergy Q q f := by
  simp [dualEnergy, ASDExplicitGamma.Triadic.primalEnergy_neg]

private theorem vectorWeakHaarEnergy_quarterTurnPullback
    (m : ℤ) (F : Vec 2 → Fin 2 → ℝ)
    (hF : ∀ i, MemLp (fun x => F x i) 2
      (normalizedCubeMeasure (originCube 2 m))) :
    vectorWeakHaarEnergy (originCube 2 m)
        (fun x i => quarterTurnVector (F (spatialQuarterTurn x)) i) =
      vectorWeakHaarEnergy (originCube 2 m) F := by
  have hTurnLp : ∀ i, MemLp
      (fun x => quarterTurnVector (F x) i) 2
        (normalizedCubeMeasure (originCube 2 m)) := by
    intro i
    fin_cases i
    · have hfun : (fun x => quarterTurnVector (F x) (0 : Fin 2)) =
          fun x => F x 1 := by
        funext x
        simp [quarterTurnVector, matVecMul_swap_eq_comp,
          matVecMul_signFlipMatrix_apply]
      change MemLp (fun x => quarterTurnVector (F x) (0 : Fin 2)) 2
        (normalizedCubeMeasure (originCube 2 m))
      rw [hfun]
      exact hF 1
    · have hfun : (fun x => quarterTurnVector (F x) (1 : Fin 2)) =
          -(fun x => F x 0) := by
        funext x
        simp [quarterTurnVector, matVecMul_swap_eq_comp,
          matVecMul_signFlipMatrix_apply]
      change MemLp (fun x => quarterTurnVector (F x) (1 : Fin 2)) 2
        (normalizedCubeMeasure (originCube 2 m))
      rw [hfun]
      exact (hF 0).neg
  calc
    vectorWeakHaarEnergy (originCube 2 m)
        (fun x i => quarterTurnVector (F (spatialQuarterTurn x)) i) =
      vectorWeakHaarEnergy (originCube 2 m)
        (fun x i => quarterTurnVector (F x) i) := by
          exact vectorWeakHaarEnergy_spatialQuarterTurn m
            (fun x i => quarterTurnVector (F x) i) hTurnLp
    _ = vectorWeakHaarEnergy (originCube 2 m) F := by
      unfold vectorWeakHaarEnergy
      simp only [Fin.sum_univ_two, quarterTurnVector_zero,
        quarterTurnVector_one, dualEnergy_neg]
      ring

/-- The weak-Haar energy is invariant under a quarter-turn about the center
of any triadic cell, when vector components are quarter-turned with the
spatial variable. -/
theorem vectorWeakHaarEnergy_centeredQuarterTurn
    (Q : TriadicCube 2) (F : Vec 2 → Fin 2 → ℝ)
    (hF : ∀ i, MemLp (fun x => F x i) 2 (normalizedCubeMeasure Q)) :
    vectorWeakHaarEnergy Q
        (fun x i => quarterTurnVector
          (F (spatialQuarterTurn (x - triadicCubeShift Q) +
            triadicCubeShift Q)) i) =
      vectorWeakHaarEnergy Q F := by
  let O := originCube 2 Q.scale
  let shift := Q.index
  let z := triadicCubeShift Q
  have hQ : translateCube shift O = Q := by
    simp [O, shift, originCube, translateCube]
  have hz : smoothFeedbackCubeTranslationVector O shift = z := by
    ext i
    dsimp [smoothFeedbackCubeTranslationVector, shift, O, z,
      triadicCubeShift]
    simp [cubeScaleFactor]
  let T := euclideanWspTranslationEquiv shift O
  have hT : MeasurePreserving T (normalizedCubeMeasure O)
      (normalizedCubeMeasure Q) := by
    simpa [hQ, T] using euclideanWspTranslation_measurePreserving shift O
  have hTfun : (T : Vec 2 → Vec 2) = fun x => x + z := by
    funext x
    change x + Gagliardo.cubeShiftVector shift O = x + z
    congr 1
  have hMP : MeasurePreserving (fun x : Vec 2 => x + z)
      (normalizedCubeMeasure O) (normalizedCubeMeasure Q) := by
    simpa only [hTfun] using hT
  let F0 : Vec 2 → Fin 2 → ℝ := fun x i => F (x + z) i
  have hF0 : ∀ i, MemLp (fun x => F0 x i) 2 (normalizedCubeMeasure O) := by
    intro i
    exact (hF i).comp_measurePreserving hMP
  have hrot := vectorWeakHaarEnergy_quarterTurnPullback Q.scale F0 hF0
  have hleft : vectorWeakHaarEnergy Q
      (fun x i => quarterTurnVector
        (F (spatialQuarterTurn (x - z) + z)) i) =
      vectorWeakHaarEnergy O
        (fun x i => quarterTurnVector (F0 (spatialQuarterTurn x)) i) := by
    rw [← hQ]
    simpa only [hz, F0, sub_add_cancel, Function.comp_apply] using
      vectorWeakHaarEnergy_translateCube O shift
        (fun x i => quarterTurnVector (F0 (spatialQuarterTurn x)) i)
  have hright : vectorWeakHaarEnergy Q F = vectorWeakHaarEnergy O F0 := by
    rw [← hQ]
    simpa only [hz, F0, sub_add_cancel, Function.comp_apply] using
      vectorWeakHaarEnergy_translateCube O shift F0
  calc
    _ = vectorWeakHaarEnergy O
        (fun x i => quarterTurnVector (F0 (spatialQuarterTurn x)) i) := hleft
    _ = vectorWeakHaarEnergy O F0 := hrot
    _ = vectorWeakHaarEnergy Q F := hright.symm

/-- The sample-space action that rotates the cutoff about the center of `Q`.
It is built from the model's actual translation and signed-permutation
actions, so it retains the genuine lower-tail cutoff carrier. -/
noncomputable def centeredQuarterTurnCutoffSample (Q : TriadicCube 2)
    (ω : Cutoff.CutoffSample 2) : Cutoff.CutoffSample 2 :=
  Cutoff.translateCutoffSample (-triadicCubeShift Q)
    (Cutoff.rotateCutoffSample quarterTurn
      Main.main_quarterTurn_isSignedPermutation
      (Cutoff.translateCutoffSample (triadicCubeShift Q) ω))

/-- The actual OLD cutoff law is invariant under quarter-turn about the
center of any triadic cell. -/
theorem map_centeredQuarterTurnCutoffSample_cutoffSampleLaw
    (M : ABKModel 2) (Q : TriadicCube 2) :
    Measure.map (centeredQuarterTurnCutoffSample Q)
        (Cutoff.cutoffSampleLaw M).toMeasure =
      (Cutoff.cutoffSampleLaw M).toMeasure := by
  let z := triadicCubeShift Q
  let tauPlus := Cutoff.translateCutoffSample z
  let tauMinus := Cutoff.translateCutoffSample (-z)
  let ρ := Cutoff.rotateCutoffSample quarterTurn
    Main.main_quarterTurn_isSignedPermutation
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  have hTranslatePlus : Measure.map tauPlus μ = μ := by
    simpa [tauPlus, μ] using Cutoff.map_translateCutoffSample_cutoffSampleLaw M z
  have hTranslateMinus : Measure.map tauMinus μ = μ := by
    simpa [tauMinus, μ] using Cutoff.map_translateCutoffSample_cutoffSampleLaw M (-z)
  have hRotate : Measure.map ρ μ = μ := by
    simpa [ρ, μ] using Cutoff.map_rotateCutoffSample_cutoffSampleLaw M
      quarterTurn Main.main_quarterTurn_isSignedPermutation
  have hInnerMap : Measure.map (ρ ∘ tauPlus) μ =
      Measure.map ρ (Measure.map tauPlus μ) :=
    (Measure.map_map
      (Cutoff.measurable_rotateCutoffSample quarterTurn
        Main.main_quarterTurn_isSignedPermutation)
      (Cutoff.measurable_translateCutoffSample z)).symm
  have hInnerMeas : Measurable (ρ ∘ tauPlus) :=
    (Cutoff.measurable_rotateCutoffSample quarterTurn
      Main.main_quarterTurn_isSignedPermutation).comp
        (Cutoff.measurable_translateCutoffSample z)
  have hAction : centeredQuarterTurnCutoffSample Q =
      tauMinus ∘ (ρ ∘ tauPlus) := by
    funext ω
    rfl
  calc
    Measure.map (centeredQuarterTurnCutoffSample Q) μ =
        Measure.map tauMinus (Measure.map ρ (Measure.map tauPlus μ)) := by
          rw [hAction]
          rw [← Measure.map_map (Cutoff.measurable_translateCutoffSample (-z))
            hInnerMeas]
          rw [hInnerMap]
    _ = μ := by rw [hTranslatePlus, hRotate, hTranslateMinus]

/-- Pointwise covariance of the genuine cutoff under the centered-cell
quarter-turn action. -/
theorem cutoff_centeredQuarterTurn
    (m : ℤ) (Q : TriadicCube 2) (ω : Cutoff.CutoffSample 2) (x : Vec 2) :
    Cutoff.cutoff m (centeredQuarterTurnCutoffSample Q ω) x =
      matTranspose quarterTurn *
        Cutoff.cutoff m ω
          (matVecMul quarterTurn
            (x - triadicCubeShift Q) + triadicCubeShift Q) *
        quarterTurn := by
  let z := triadicCubeShift Q
  change Cutoff.cutoff m
      (Cutoff.translateCutoffSample (-z)
        (Cutoff.rotateCutoffSample quarterTurn
          Main.main_quarterTurn_isSignedPermutation
          (Cutoff.translateCutoffSample z ω))) x = _
  rw [Cutoff.cutoff_translateCutoffSample, Cutoff.cutoff_rotateCutoffSample,
    Cutoff.cutoff_translateCutoffSample]
  simp [z, translateReg_apply, rotateReg_apply, sub_eq_add_neg]

private theorem centeredQuarterTurn_mem_openCubeSet
    (Q : TriadicCube 2) {x : Vec 2} (hx : x ∈ openCubeSet Q) :
    spatialQuarterTurn (x - triadicCubeShift Q) + triadicCubeShift Q ∈
      openCubeSet Q := by
  let O := originCube 2 Q.scale
  let z := triadicCubeShift Q
  have hx0 : x - z ∈ openCubeSet O := by
    rw [openCubeSet_eq_translateSet_originCube_of_triadicCube Q] at hx
    simpa [z, O, mem_translateSet_iff_sub_mem] using hx
  have hO : quarterTurnCube O = O := by
    rw [show O = originCube 2 Q.scale by rfl]
    simp only [quarterTurnCube, originCube, TriadicCube.mk.injEq]
    constructor
    · trivial
    · funext i
      by_cases hi : i = 0 <;> simp [hi]
  have hpre := spatialQuarterTurn_openCubeSet O
  rw [hO] at hpre
  have hrot : spatialQuarterTurn (x - z) ∈ openCubeSet O := by
    have hmem := congrArg (fun S : Set (Vec 2) => (x - z) ∈ S) hpre
    simpa using hmem.mpr hx0
  rw [openCubeSet_eq_translateSet_originCube_of_triadicCube Q,
    mem_translateSet_iff_sub_mem]
  change (spatialQuarterTurn (x - z) + z) - z ∈ openCubeSet O
  simpa [sub_eq_add_neg, add_assoc] using hrot

/-- Evaluation of the coefficient pullback for a quarter-turn about the cell
center. -/
theorem quarterTurnCellCoeff_apply
    (Q : TriadicCube 2) (a : CoeffField 2) (x : Vec 2) :
    quarterTurnCellCoeff Q a x =
      matTranspose (Matrix.swap ℝ 0 1) *
        (matTranspose (signFlipMatrix 0) *
          a (matVecMul (signFlipMatrix 0)
            (matVecMul (Matrix.swap ℝ 0 1)
              (x - triadicCubeShift Q)) + triadicCubeShift Q) *
          signFlipMatrix 0) * Matrix.swap ℝ 0 1 := by
  unfold quarterTurnCellCoeff
  rfl

/-- The actual OLD-frame coefficient on `Q` transforms by the centered-cell
cutoff action and the coefficient pullback used in the response covariance. -/
theorem responseFramePlanarCoefficientField_centeredQuarterTurn
    (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2)
    (ω : Cutoff.CutoffSample 2) {x : Vec 2} (hx : x ∈ openCubeSet Q) :
    responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m : ℝ)
        (oldCutoffSkewCoefficient m Q (centeredQuarterTurnCutoffSample Q ω)) x =
      quarterTurnCellCoeff Q
        (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m : ℝ)
          (oldCutoffSkewCoefficient m Q ω)) x := by
  let z := triadicCubeShift Q
  let Fmat : Mat 2 := signFlipMatrix (0 : Fin 2)
  let Smat : Mat 2 := Matrix.swap ℝ (0 : Fin 2) (1 : Fin 2)
  let y := matVecMul Fmat (matVecMul Smat (x - z)) + z
  let σ := (Annealed.sigmaBar M m : ℝ)
  let R := quarterTurn
  have hy : y ∈ openCubeSet Q := by
    have hspatial : matVecMul Fmat (matVecMul Smat (x - z)) =
        spatialQuarterTurn (x - z) := by
      ext i
      fin_cases i <;> simp [Fmat, Smat, matVecMul,
        spatialQuarterTurn, signFlipMatrix, Matrix.swap,
        Equiv.swap_apply_def, Fin.sum_univ_two]
    have hyEq : y = spatialQuarterTurn (x - z) + z := by
      dsimp [y, z]
      rw [hspatial]
    rw [hyEq]
    exact centeredQuarterTurn_mem_openCubeSet Q hx
  have hcut := cutoff_centeredQuarterTurn m Q ω x
  have hturn : matVecMul quarterTurn (x - z) =
      matVecMul Fmat (matVecMul Smat (x - z)) := by
    ext i
    fin_cases i <;> simp [Fmat, Smat, matVecMul, quarterTurn,
      signFlipMatrix, Matrix.swap, Equiv.swap_apply_def, Fin.sum_univ_two]
  have hcut' : Cutoff.cutoff m (centeredQuarterTurnCutoffSample Q ω) x =
      matTranspose R * Cutoff.cutoff m ω y * R := by
    calc
      Cutoff.cutoff m (centeredQuarterTurnCutoffSample Q ω) x =
          matTranspose R * Cutoff.cutoff m ω
            (matVecMul quarterTurn (x - z) + z) * R := by
        simpa [R, z] using hcut
      _ = matTranspose R * Cutoff.cutoff m ω y * R := by rw [hturn]
  have hentry : (matTranspose R * Cutoff.cutoff m ω y * R) 1 0 =
      Cutoff.cutoff m ω y 1 0 := by
    have hskew := Cutoff.cutoff_skew m ω y
    rw [planar_skew_eq_scalar_quarter_turn _ hskew]
    have hJ : matTranspose R * responsePlanarJ * R = responsePlanarJ := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [R, quarterTurn, responsePlanarJ, matTranspose,
          Matrix.mul_apply, Fin.sum_univ_two]
    simp [smul_eq_mul, hJ]
  rw [responseFramePlanarCoefficientField_apply,
    old_cutoff_skew_coefficient_value m Q
      (centeredQuarterTurnCutoffSample Q ω) hx, hcut', hentry]
  have hRight : quarterTurnCellCoeff Q
      (responseFramePlanarCoefficientField M.nu σ
        (oldCutoffSkewCoefficient m Q ω)) x =
      responsePlanarCoefficient (M.nu / σ)
        (Cutoff.cutoff m ω y 1 0 / σ) := by
    rw [quarterTurnCellCoeff_apply]
    rw [responseFramePlanarCoefficientField_apply,
      old_cutoff_skew_coefficient_value m Q ω hy]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [responsePlanarCoefficient, responsePlanarJ,
        matTranspose, signFlipMatrix, div_eq_mul_inv]
  exact hRight.symm

private theorem cellTransport_blockCoeffField_centeredQuarterTurn
    (Q : TriadicCube 2) (a : CoeffField 2) (x : Vec 2) :
    blockCoeffField (quarterTurnCellCoeff Q a) x =
      blockMatConj (Matrix.swap ℝ (0 : Fin 2) (1 : Fin 2))
        (blockMatConj (signFlipMatrix (0 : Fin 2))
          (blockCoeffField a
            (spatialQuarterTurn (x - triadicCubeShift Q) +
              triadicCubeShift Q))) := by
  let F : Mat 2 := signFlipMatrix (0 : Fin 2)
  let S : Mat 2 := Matrix.swap ℝ (0 : Fin 2) (1 : Fin 2)
  change blockMatrixOfCoeff (quarterTurnCellCoeff Q a x) = _
  rw [quarterTurnCellCoeff_apply]
  have hS : matTranspose S = S := by simp [S, matTranspose]
  have hF : matTranspose F = F := by simp [F, matTranspose, signFlipMatrix]
  rw [hS]
  rw [blockMatrixOfCoeff_swap_conj (0 : Fin 2) (1 : Fin 2)
    (matTranspose F * a
      (matVecMul F (matVecMul S (x - triadicCubeShift Q)) +
        triadicCubeShift Q) * F)]
  rw [hF, blockMatrixOfCoeff_signFlipMatrix_conj (0 : Fin 2)]
  have hspatial : matVecMul F (matVecMul S (x - triadicCubeShift Q)) =
      spatialQuarterTurn (x - triadicCubeShift Q) := by
    ext i
    fin_cases i <;>
      simp [F, S, matVecMul_swap_eq_comp,
        matVecMul_signFlipMatrix_apply, spatialQuarterTurn]
  rw [hspatial]
  rfl

private theorem cellTransport_state_centeredQuarterTurn_eval
    (Q : TriadicCube 2) (X : BlockState 2) (x : Vec 2) :
    (quarterTurnCellState Q X).eval x =
      blockVecConj (Matrix.swap ℝ (0 : Fin 2) (1 : Fin 2))
        (blockVecConj (signFlipMatrix (0 : Fin 2))
          (X.eval (spatialQuarterTurn (x - triadicCubeShift Q) +
            triadicCubeShift Q))) := by
  let z := triadicCubeShift Q
  have hSwap : matVecMul (Matrix.swap ℝ (0 : Fin 2) (1 : Fin 2)) (x - z) =
      (x - z) ∘ ⇑(Equiv.swap (0 : Fin 2) (1 : Fin 2)) := by
    simpa using matVecMul_swap_eq_comp (0 : Fin 2) (1 : Fin 2) (x - z)
  have hspatial : matVecMul (signFlipMatrix (0 : Fin 2))
      (matVecMul (Matrix.swap ℝ (0 : Fin 2) (1 : Fin 2)) (x - z)) =
      spatialQuarterTurn (x - z) := by
    rw [hSwap]
    ext i
    fin_cases i <;>
      simp [matVecMul_signFlipMatrix_apply, spatialQuarterTurn]
  change ((((X.translate (-z)).signFlip (0 : Fin 2)).swap
    (0 : Fin 2) (1 : Fin 2)).translate z).eval x = _
  simp only [BlockState.eval, BlockState.translate, BlockState.signFlip,
    BlockState.swap, blockVecConj, signFlipVecContinuousLinearEquiv_apply,
    swapVecContinuousLinearEquiv_apply, sub_neg_eq_add]
  rw [hspatial]

theorem smooth_feedback_cell_directional_gamma_centeredQuarterTurn
    (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2)
    (ω : Cutoff.CutoffSample 2) (e : Vec 2) :
    smoothFeedbackCellDirectionalGamma M m Q e
        (centeredQuarterTurnCutoffSample Q ω) =
      smoothFeedbackCellDirectionalGamma M m Q
        (matVecMul quarterTurn e) ω := by
  let μ := (Annealed.sigmaBar M m : ℝ)
  let z := triadicCubeShift Q
  let q : Vec 2 → Vec 2 := fun x => spatialQuarterTurn (x - z) + z
  let a : CoeffField 2 := responseFramePlanarCoefficientField M.nu μ
    (oldCutoffSkewCoefficient m Q ω)
  let aTurn : CoeffField 2 := responseFramePlanarCoefficientField M.nu μ
    (oldCutoffSkewCoefficient m Q
      (centeredQuarterTurnCutoffSample Q ω))
  let b : CoeffField 2 := quarterTurnCellCoeff Q a
  let hEll := responseFramePlanarCoefficientField_isElliptic
    (measurableSet_openCubeSet Q) M.nu μ M.nu_pos
    (Annealed.sigmaBar M m).property (oldCutoffSkewCoefficient m Q ω)
  let hEllTurn := responseFramePlanarCoefficientField_isElliptic
    (measurableSet_openCubeSet Q) M.nu μ M.nu_pos
    (Annealed.sigmaBar M m).property
    (oldCutoffSkewCoefficient m Q
      (centeredQuarterTurnCutoffSample Q ω))
  let hEllB := quarterTurnCellCoeff_isElliptic Q a hEll
  let X := scalarCellResponseTest Q a hEll (matVecMul quarterTurn e, 0)
  let XTurn := scalarCellResponseTest Q aTurn hEllTurn (e, 0)
  have hCoeff : aTurn =ᵐ[volumeMeasureOn (openCubeSet Q)] b := by
    filter_upwards [ae_restrict_mem (measurableSet_openCubeSet Q)] with x hx
    simpa [aTurn, b, a, μ] using
      responseFramePlanarCoefficientField_centeredQuarterTurn M m Q ω hx
  have hVector : quarterTurnVector (matVecMul quarterTurn e) = e := by
    change matVecMul (Matrix.swap ℝ 0 1)
      (matVecMul (signFlipMatrix 0) (matVecMul quarterTurn e)) = e
    ext i
    fin_cases i <;>
      simp [quarterTurn, matVecMul, signFlipMatrix,
        Matrix.swap, Fin.sum_univ_two]
  have hLoad : quarterTurnLoad (matVecMul quarterTurn e, 0) = (e, 0) := by
    rw [quarterTurnLoad_affine]
    exact Prod.ext hVector (by simp)
  have hCong := Main.main_scalarCellResponseTest_congr_coeff_ae
    Q aTurn b hEllTurn hEllB hCoeff (e, 0)
  have hRot := scalar_cell_response_test_centered_quarterTurn_ae
    Q a hEll (matVecMul quarterTurn e, 0)
  have hRot' : (scalarCellResponseTest Q b hEllB (e, 0)).eval =ᵐ[
      volumeMeasureOn (openCubeSet Q)] (quarterTurnCellState Q X).eval := by
    simpa [b, X, hLoad] using hRot
  have hTest : XTurn.eval =ᵐ[volumeMeasureOn (openCubeSet Q)]
      (quarterTurnCellState Q X).eval := by
    exact hCong.trans hRot'
  have hLin (v : Vec 2) :
      quarterTurnVector v - e =
        quarterTurnVector (v - matVecMul quarterTurn e) := by
    rw [← hVector]
    ext i
    fin_cases i <;>
      simp [quarterTurnVector, quarterTurn, matVecMul,
        signFlipMatrix, Matrix.swap, Fin.sum_univ_two]
    all_goals ring
  have hTop :
      smoothFeedbackCellAffineTopDefect M m Q e
        (centeredQuarterTurnCutoffSample Q ω) =ᵐ[
          volumeMeasureOn (openCubeSet Q)]
      (fun x => quarterTurnVector
        (smoothFeedbackCellAffineTopDefect M m Q
          (matVecMul quarterTurn e) ω (q x))) := by
    filter_upwards [hTest] with x hx
    have hxFst := congrArg Prod.fst hx
    change (XTurn.eval x).1 - e = _
    rw [hxFst, cellTransport_state_centeredQuarterTurn_eval]
    change quarterTurnVector (X.eval (q x)).1 - e = _
    exact hLin (X.eval (q x)).1
  have hBlock : ∀ᵐ x ∂volumeMeasureOn (openCubeSet Q),
      blockCoeffField aTurn x =
        blockMatConj (Matrix.swap ℝ (0 : Fin 2) (1 : Fin 2))
          (blockMatConj (signFlipMatrix (0 : Fin 2))
            (blockCoeffField a (q x))) := by
    filter_upwards [hCoeff] with x hx
    calc
      blockCoeffField aTurn x = blockCoeffField b x := by
        change blockMatrixOfCoeff (aTurn x) = blockMatrixOfCoeff (b x)
        rw [hx]
      _ = _ := cellTransport_blockCoeffField_centeredQuarterTurn Q a x
  have hFlux :
      smoothFeedbackCellAffineReciprocalGradient M m Q e
        (centeredQuarterTurnCutoffSample Q ω) =ᵐ[
          volumeMeasureOn (openCubeSet Q)]
      (fun x => quarterTurnVector
        (smoothFeedbackCellAffineReciprocalGradient M m Q
          (matVecMul quarterTurn e) ω (q x))) := by
    filter_upwards [hTest, hBlock] with x hxTest hxBlock
    change (scalarCoefficientFlux aTurn XTurn.eval x).2 = _
    rw [scalarCoefficientFlux, hxBlock, hxTest,
      cellTransport_state_centeredQuarterTurn_eval]
    rw [blockMatVecMul_blockMatConj_of_mul_self_eq_one
      (Matrix.swap_mul_self (R := ℝ) (0 : Fin 2) (1 : Fin 2))]
    rw [blockMatVecMul_blockMatConj_of_mul_self_eq_one
      (signFlipMatrix_mul_self (0 : Fin 2))]
    rfl
  have hAffine : MemBlockL2 (openCubeSet Q)
      (smoothFeedbackCellAffineResidual M m Q
        (matVecMul quarterTurn e) ω) := by
    simpa [smoothFeedbackCellAffineResidual, X, a, hEll, μ] using
      scalar_cell_response_test_memL2 Q a hEll
        (matVecMul quarterTurn e, 0)
  have hTopVec : MemVectorL2 (openCubeSet Q)
      (smoothFeedbackCellAffineTopDefect M m Q
        (matVecMul quarterTurn e) ω) := by
    exact (memVectorL2_fst_of_memBlockL2 hAffine).sub
      (memLp_const (matVecMul quarterTurn e))
  have hFluxBlock : MemBlockL2 (openCubeSet Q)
      (scalarCoefficientFlux a
        (smoothFeedbackCellAffineResidual M m Q
          (matVecMul quarterTurn e) ω)) := by
    exact scalar_coefficient_flux_memL2 Q a hEll hAffine
  have hFluxVec : MemVectorL2 (openCubeSet Q)
      (smoothFeedbackCellAffineReciprocalGradient M m Q
        (matVecMul quarterTurn e) ω) := by
    exact memVectorL2_snd_of_memBlockL2 hFluxBlock
  have hTopCoord (i : Fin 2) : MemLp
      (fun x => smoothFeedbackCellAffineTopDefect M m Q
        (matVecMul quarterTurn e) ω x i) 2
      (normalizedCubeMeasure Q) :=
    memLp_normalized_of_memL2On (memScalarL2_coord_of_memVectorL2 hTopVec i)
  have hFluxCoord (i : Fin 2) : MemLp
      (fun x => smoothFeedbackCellAffineReciprocalGradient M m Q
        (matVecMul quarterTurn e) ω x i) 2
      (normalizedCubeMeasure Q) :=
    memLp_normalized_of_memL2On (memScalarL2_coord_of_memVectorL2 hFluxVec i)
  calc
    smoothFeedbackCellDirectionalGamma M m Q e
        (centeredQuarterTurnCutoffSample Q ω) =
      vectorWeakHaarEnergy Q (fun x => quarterTurnVector
          (smoothFeedbackCellAffineTopDefect M m Q
            (matVecMul quarterTurn e) ω (q x))) +
        vectorWeakHaarEnergy Q (fun x => quarterTurnVector
          (smoothFeedbackCellAffineReciprocalGradient M m Q
            (matVecMul quarterTurn e) ω (q x))) := by
          simp only [smoothFeedbackCellDirectionalGamma]
          rw [smooth_feedback_vector_weak_energy_congr_ae Q hTop,
            smooth_feedback_vector_weak_energy_congr_ae Q hFlux]
    _ = vectorWeakHaarEnergy Q
          (smoothFeedbackCellAffineTopDefect M m Q
            (matVecMul quarterTurn e) ω) +
        vectorWeakHaarEnergy Q
          (smoothFeedbackCellAffineReciprocalGradient M m Q
            (matVecMul quarterTurn e) ω) := by
          rw [vectorWeakHaarEnergy_centeredQuarterTurn Q _ hTopCoord,
            vectorWeakHaarEnergy_centeredQuarterTurn Q _ hFluxCoord]
    _ = smoothFeedbackCellDirectionalGamma M m Q
        (matVecMul quarterTurn e) ω := rfl

end
end ASDExplicitGamma.Scalar
