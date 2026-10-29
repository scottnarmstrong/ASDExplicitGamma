module

public import ASDExplicitGamma.Statements.TraceDefect
public import Algsuperdiff.Section3.Provider.Annealed.Monotonicity
public import Homogenization.CoarseGraining.Translation

/-! # Real translation of cutoff observables

The distributional adapter applies to any measurable covariant observable,
including joint vectors of descendant observables. Scales may be negative.
-/

@[expose] public section

namespace ASDExplicitGamma.Model

open Homogenization Homogenization.Book
open Algsuperdiff.Section3 MeasureTheory

/-- The completed cutoff coefficient law is invariant under every real shift. -/
theorem map_translate_cutoffLaw (M : ABKModel 2) (m : ℤ) (z : Vec 2) :
    Measure.map (translateReg z) (Cutoff.coefficientCutoffLaw M m) =
      Cutoff.coefficientCutoffLaw M m :=
  Cutoff.coefficientCutoffLaw_stationary_real M m z

/-- MO-TRANSLATION: every measurable translation-covariant observable has the
same law on a translated domain. The output can be a joint descendant vector. -/
theorem map_cutoffObservable_translate {E : Type*} [MeasurableSpace E]
    (M : ABKModel 2) (m : ℤ) (U : Set (Vec 2)) (z : Vec 2)
    (X : Set (Vec 2) → CoeffField 2 → E)
    (hX : AEMeasurable (fun a : RegCoeffField 2 => X U a.toFun)
      (Cutoff.coefficientCutoffLaw M m))
    (hcov : ∀ V z a, X (translateSet z V) a = X V (translateCoeffField z a)) :
    Measure.map (fun a : RegCoeffField 2 => X (translateSet z U) a.toFun)
        (Cutoff.coefficientCutoffLaw M m) =
      Measure.map (fun a : RegCoeffField 2 => X U a.toFun)
        (Cutoff.coefficientCutoffLaw M m) := by
  have hfun : (fun a : RegCoeffField 2 => X (translateSet z U) a.toFun) =
      (fun a : RegCoeffField 2 => X U a.toFun) ∘ translateReg z := by
    funext a
    exact hcov U z a.toFun
  rw [hfun, ← AEMeasurable.map_map_of_aemeasurable
    (by simpa only [map_translate_cutoffLaw M m z] using hX)
    (measurable_translateReg z).aemeasurable, map_translate_cutoffLaw]

/-- The generic translated-cell distribution adapter, expressed relative to
the origin cube at exactly the cell's scale. -/
theorem map_cutoffObservable_cube_eq_origin {E : Type*} [MeasurableSpace E]
    (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2)
    (X : Set (Vec 2) → CoeffField 2 → E)
    (hX : AEMeasurable (fun a : RegCoeffField 2 =>
      X (cubeSet (originCube 2 Q.scale)) a.toFun) (Cutoff.coefficientCutoffLaw M m))
    (hcov : ∀ V z a, X (translateSet z V) a = X V (translateCoeffField z a)) :
    Measure.map (fun a : RegCoeffField 2 => X (cubeSet Q) a.toFun)
        (Cutoff.coefficientCutoffLaw M m) =
      Measure.map (fun a : RegCoeffField 2 =>
        X (cubeSet (originCube 2 Q.scale)) a.toFun) (Cutoff.coefficientCutoffLaw M m) := by
  rw [cubeSet_eq_translateSet_originCube_of_triadicCube Q]
  exact map_cutoffObservable_translate M m _ _ X hX hcov

/-- The entire coarse response matrix has the origin-cell distribution. -/
theorem map_cutoffCoarseMatrix_cube_eq_origin (M : ABKModel 2) (m : ℤ)
    (Q : TriadicCube 2) :
    Measure.map (fun a : RegCoeffField 2 =>
        toFullBlockMat (coarseBlockMatrix (cubeSet Q) a.toFun))
        (Cutoff.coefficientCutoffLaw M m) =
      Measure.map (fun a : RegCoeffField 2 =>
        toFullBlockMat (coarseBlockMatrix (cubeSet (originCube 2 Q.scale)) a.toFun))
        (Cutoff.coefficientCutoffLaw M m) := by
  apply map_cutoffObservable_cube_eq_origin M m Q
    (fun U a => toFullBlockMat (coarseBlockMatrix U a))
  · exact (Cutoff.coefficientCutoffLaw_lawCarrier M m).aemeasurable_coarseFullBlockMatrix_cubeSet _
  · intro V z a
    rw [coarseBlockMatrix_translateSet_eq_translateCoeffField]

/-- Joint laws of all coarse matrices in a deterministic family of cells are
unchanged by a common real shift. In particular this applies to the entire
finite descendant family, preserving correlations as well as marginal laws. -/
theorem map_cutoffCoarseMatrix_family_translate {ι : Type*} [Countable ι]
    (M : ABKModel 2) (m : ℤ) (Q : ι → TriadicCube 2) (z : Vec 2) :
    Measure.map (fun a : RegCoeffField 2 => fun i =>
        toFullBlockMat (coarseBlockMatrix (translateSet z (cubeSet (Q i))) a.toFun))
        (Cutoff.coefficientCutoffLaw M m) =
      Measure.map (fun a : RegCoeffField 2 => fun i =>
        toFullBlockMat (coarseBlockMatrix (cubeSet (Q i)) a.toFun))
        (Cutoff.coefficientCutoffLaw M m) := by
  have hX : AEMeasurable (fun a : RegCoeffField 2 => fun i =>
      toFullBlockMat (coarseBlockMatrix (cubeSet (Q i)) a.toFun))
      (Cutoff.coefficientCutoffLaw M m) :=
    aemeasurable_pi_iff.mpr fun i =>
      (Cutoff.coefficientCutoffLaw_lawCarrier M m).aemeasurable_coarseFullBlockMatrix_cubeSet (Q i)
  have hfun : (fun a : RegCoeffField 2 => fun i =>
      toFullBlockMat (coarseBlockMatrix (translateSet z (cubeSet (Q i))) a.toFun)) =
      (fun a : RegCoeffField 2 => fun i =>
        toFullBlockMat (coarseBlockMatrix (cubeSet (Q i)) a.toFun)) ∘ translateReg z := by
    funext a i
    exact congrArg toFullBlockMat
      (coarseBlockMatrix_translateSet_eq_translateCoeffField z (cubeSet (Q i)) a.toFun)
  rw [hfun, ← AEMeasurable.map_map_of_aemeasurable
    (by simpa only [map_translate_cutoffLaw M m z] using hX)
    (measurable_translateReg z).aemeasurable, map_translate_cutoffLaw]

/-- The frozen trace defect commutes with translation, at any fixed frame. -/
theorem traceDefect_translate (U : Set (Vec 2)) (z : Vec 2)
    (a : CoeffField 2) (sigma : ℝ) :
    traceDefect (translateSet z U) a sigma =
      traceDefect U (translateCoeffField z a) sigma := by
  unfold traceDefect
  rw [coarseBlockMatrix_translateSet_eq_translateCoeffField]

/-- The frozen trace defect is a.e. measurable under the completed cutoff law. -/
theorem aemeasurable_traceDefect_cutoffLaw (M : ABKModel 2) (m : ℤ)
    (Q : TriadicCube 2) (sigma : ℝ) :
    AEMeasurable (fun a : RegCoeffField 2 => traceDefect (cubeSet Q) a.toFun sigma)
      (Cutoff.coefficientCutoffLaw M m) := by
  have hP := Cutoff.coefficientCutoffLaw_lawCarrier M m
  have hUL : AEMeasurable (fun a : RegCoeffField 2 =>
      Matrix.trace (coarseBlockMatrix (cubeSet Q) a.toFun).upperLeft)
      (Cutoff.coefficientCutoffLaw M m) := by
    unfold Matrix.trace
    apply Finset.aemeasurable_fun_sum
    intro i _
    exact hP.aemeasurable_coarseBlockMatrix_upperLeft_apply_cubeSet Q i i
  have hLR : AEMeasurable (fun a : RegCoeffField 2 =>
      Matrix.trace (coarseBlockMatrix (cubeSet Q) a.toFun).lowerRight)
      (Cutoff.coefficientCutoffLaw M m) := by
    unfold Matrix.trace
    apply Finset.aemeasurable_fun_sum
    intro i _
    exact hP.aemeasurable_coarseBlockMatrix_lowerRight_apply_cubeSet Q i i
  exact ((hUL.const_mul sigma⁻¹).add (hLR.const_mul sigma)).sub_const 4

/-- Trace-defect laws agree on a cell and its origin-cell translate. -/
theorem map_traceDefect_cube_eq_origin (M : ABKModel 2) (m : ℤ)
    (Q : TriadicCube 2) (sigma : ℝ) :
    Measure.map (fun a : RegCoeffField 2 => traceDefect (cubeSet Q) a.toFun sigma)
        (Cutoff.coefficientCutoffLaw M m) =
      Measure.map (fun a : RegCoeffField 2 =>
        traceDefect (cubeSet (originCube 2 Q.scale)) a.toFun sigma)
        (Cutoff.coefficientCutoffLaw M m) := by
  exact map_cutoffObservable_cube_eq_origin M m Q (fun U a => traceDefect U a sigma)
    (aemeasurable_traceDefect_cutoffLaw M m _ sigma)
    (fun U z a => traceDefect_translate U z a sigma)

/-- The annealed full coarse matrix on every real translate of an origin cube
is exactly the origin-scale annealed matrix. -/
theorem annealedBlockMatrix_translate_originCube (M : ABKModel 2) (m n : ℤ)
    (z : Vec 2) :
    Ch04.annealedBlockMatrix (Cutoff.coefficientCutoffLaw M m)
        (translateSet z (cubeSet (originCube 2 n))) =
      Ch04.annealedBlockMatrixAtScale (Cutoff.coefficientCutoffLaw M m) n := by
  have hentry := fun alpha beta =>
    Provider.Annealed.integral_comp_toFun_translation_transfer_real
      (P := Cutoff.coefficientCutoffLaw M m)
      (X := fun U a => blockMatEntry (coarseBlockMatrix U a) alpha beta)
      (Cutoff.coefficientCutoffLaw_stationary_real M m)
      (Provider.Annealed.aestronglyMeasurable_blockMatEntry_coarseBlockMatrix_cubeSet
        (Cutoff.coefficientCutoffLaw_lawCarrier M m) (originCube 2 n) alpha beta)
      (fun V z a => congrArg (fun A => blockMatEntry A alpha beta)
        (coarseBlockMatrix_translateSet_eq_translateCoeffField z V a)) z
  apply blockMat_ext <;> ext i j
  · exact hentry (Sum.inl i) (Sum.inl j)
  · exact hentry (Sum.inl i) (Sum.inr j)
  · exact hentry (Sum.inr i) (Sum.inl j)
  · exact hentry (Sum.inr i) (Sum.inr j)

/-- Translation-independent annealed response at an arbitrary triadic cell. -/
theorem annealedBlockMatrix_cube_eq_origin (M : ABKModel 2) (m : ℤ)
    (Q : TriadicCube 2) :
    Ch04.annealedBlockMatrix (Cutoff.coefficientCutoffLaw M m) (cubeSet Q) =
      Ch04.annealedBlockMatrixAtScale (Cutoff.coefficientCutoffLaw M m) Q.scale := by
  rw [cubeSet_eq_translateSet_originCube_of_triadicCube Q]
  exact annealedBlockMatrix_translate_originCube M m Q.scale _

end ASDExplicitGamma.Model
