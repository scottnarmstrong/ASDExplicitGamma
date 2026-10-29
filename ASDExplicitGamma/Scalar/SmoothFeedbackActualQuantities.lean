/-
Copyright (c) 2026 Scott N. Armstrong. All rights reserved.
-/
module

public import ASDExplicitGamma.Scalar.SmoothFeedbackGapPair
public import ASDExplicitGamma.Scalar.SmoothFeedbackJointCell
public import ASDExplicitGamma.Scalar.SmoothFeedbackJointFeedback
public import ASDExplicitGamma.Scalar.SmoothFeedbackSourceCharge
public import ASDExplicitGamma.Scalar.SmoothFeedbackAnnealed

/-! Named versions of the actual pathwise quantities of the smooth-feedback
estimate, as functions of the OLD sample, and the two pathwise estimates
stated for them. -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open MeasureTheory Homogenization Response Triadic Variational
open ASDExplicitGamma.Native
open Algsuperdiff.Section3
open scoped BigOperators

noncomputable section

section Defs

variable {ι : Type*} (S : Finset ι) (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2)
  (depth : ℕ) (u : ι → H10Function (openCubeSet Q))

/-- The cell mean of the `i`th load. -/
def cellMean (i : ι) (U : TriadicCube 2) : Vec 2 :=
  fun j => cubeAverage U (fun x => (u i).toH1Function.grad x j)

/-- The OLD coarse response matrix of a child cell. -/
def cellMat (U : OldSignedCellIndex Q depth) (ω : Cutoff.CutoffSample 2) : BlockMat 2 :=
  coarseBlockMatrix (openCubeSet U.val)
    (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m : ℝ)
      (oldSignedCellCoefficient Q U.val
        (openCubeSet_subset_of_mem_descendantsAtDepth U.property)
        (oldCutoffSkewCoefficient m Q ω)))

def pK' (ω : Cutoff.CutoffSample 2) : ℝ := ∑ i ∈ S,
  oldSignedCellAverage Q depth (fun U =>
    blockVecDot ((cellMean Q u i U.val, 0) : BlockVec 2)
      (blockMatVecMul (cellMat M m Q depth U ω) (cellMean Q u i U.val, 0)))

def pD (ω : Cutoff.CutoffSample 2) : ℝ := ∑ i ∈ S,
  oldSignedCellAverage Q depth (fun U =>
    blockVecDot ((0, cellMean Q u i U.val) : BlockVec 2)
      (blockMatVecMul (cellMat M m Q depth U ω) (0, cellMean Q u i U.val)))

def apair (ω : Cutoff.CutoffSample 2) : ℝ := ∑ i ∈ S,
  oldSignedCellAverage Q depth (fun U =>
    blockVecDot ((cellMean Q u i U.val, 0) : BlockVec 2)
        (blockMatVecMul (cellMat M m Q depth U ω) (cellMean Q u i U.val, 0)) +
      blockVecDot ((0, cellMean Q u i U.val) : BlockVec 2)
        (blockMatVecMul (cellMat M m Q depth U ω) (0, cellMean Q u i U.val)) -
      2 * vecNormSq (cellMean Q u i U.val))

def theta'' (ω : Cutoff.CutoffSample 2) : ℝ := ∑ i ∈ S,
  oldSignedCellAverage Q depth (fun U =>
    smoothFeedbackCellDirectionalGamma M m U.val (cellMean Q u i U.val) ω)

def bhist (ω : Cutoff.CutoffSample 2) : ℝ :=
  smoothFeedbackSourceHistoryMaximum Q depth M.nu (Annealed.sigmaBar M m : ℝ)
    (oldCutoffSkewCoefficient m Q ω)

/-- `Σ_l ‖w_l‖²` in the normalized `L²(Q)` norm. -/
def omega2 : ℝ := ∑ i ∈ S,
  volumeAverage (openCubeSet Q) (fun x => vecNormSq ((u i).toH1Function.grad x))

/-- `δ²`: the positive quarter-order oscillation of the loads. -/
def deltaSq' : ℝ := ∑ i ∈ S, oldSignedCellAverage Q depth (fun U =>
  vectorPositiveHaarEnergy U.val
    (fun x j => (u i).toH1Function.grad x j -
      cubeAverage U.val (fun y => (u i).toH1Function.grad y j)))

end Defs

section Defs2

variable {ι : Type*} (S : Finset ι) (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2)
  (depth : ℕ) (u : ι → H10Function (openCubeSet Q))

/-- The actual load `(w_i, 0)`. -/
def topLoad (i : ι) : Vec 2 → BlockVec 2 := fun x => ((u i).toH1Function.grad x, 0)

theorem topLoad_memL2 (i : ι) : MemBlockL2 (openCubeSet Q) (topLoad Q u i) :=
  memBlockL2_blockField (u i).toH1Function.grad_memVectorL2 MemLp.zero

/-- The centered top load `(w_i - w_{i,U}, 0)`. -/
def centeredLoad (i : ι) (U : TriadicCube 2) : Vec 2 → BlockVec 2 := fun x =>
  (fun j => (u i).toH1Function.grad x j - cellMean Q u i U j, 0)

theorem centeredLoad_memL2 (i : ι) (U : TriadicCube 2) :
    MemBlockL2 (openCubeSet Q) (centeredLoad Q u i U) := by
  have hsub : MemLp (fun x => topLoad Q u i x - (cellMean Q u i U, 0)) 2
      (volumeMeasureOn (openCubeSet Q)) :=
    (topLoad_memL2 Q u i).sub (memLp_const (cellMean Q u i U, 0))
  convert hsub using 1
  ext x j
  · simp [centeredLoad, topLoad]
  · change (0 : Vec 2) j = (0 - 0 : Vec 2) j
    simp

def rK' (ω : Cutoff.CutoffSample 2) : ℝ := ∑ i ∈ S,
  oldSignedCellAverage Q depth (fun U =>
    oldSignedEnergyPairing U.val M.nu (Annealed.sigmaBar M m : ℝ)
      (oldSignedCellCoefficient Q U.val
        (openCubeSet_subset_of_mem_descendantsAtDepth U.property)
        (oldCutoffSkewCoefficient m Q ω))
      (oldSignedCellResidual Q U.val
        (openCubeSet_subset_of_mem_descendantsAtDepth U.property)
        M.nu (Annealed.sigmaBar M m : ℝ) M.nu_pos (Annealed.sigmaBar M m).property
        (oldCutoffSkewCoefficient m Q ω) (centeredLoad Q u i U.val)
        (centeredLoad_memL2 Q u i U.val))
      (oldSignedCellResidual Q U.val
        (openCubeSet_subset_of_mem_descendantsAtDepth U.property)
        M.nu (Annealed.sigmaBar M m : ℝ) M.nu_pos (Annealed.sigmaBar M m).property
        (oldCutoffSkewCoefficient m Q ω) (centeredLoad Q u i U.val)
        (centeredLoad_memL2 Q u i U.val)))

variable
    (hcenter : ∀ i, ∀ U : TriadicCube 2, U ∈ descendantsAtDepth Q depth →
      ScalarPositiveHaarAdmissible U (fun x j =>
        (u i).toH1Function.grad x j -
          cubeAverage U (fun y => (u i).toH1Function.grad y j)))

include hcenter in
def rD (ω : Cutoff.CutoffSample 2) : ℝ := ∑ i ∈ S,
  oldSignedCellAverage Q depth (fun U =>
    oldSignedEnergyPairing U.val M.nu (Annealed.sigmaBar M m : ℝ)
      (oldSignedCellCoefficient Q U.val
        (openCubeSet_subset_of_mem_descendantsAtDepth U.property)
        (oldCutoffSkewCoefficient m Q ω))
      (scalarResidualField U.val M.nu (Annealed.sigmaBar M m : ℝ) M.nu_pos
        (Annealed.sigmaBar M m).property
        (oldSignedCellCoefficient Q U.val
          (openCubeSet_subset_of_mem_descendantsAtDepth U.property)
          (oldCutoffSkewCoefficient m Q ω))
        (toHilbertBlockL2OfBlockField
          (upper_cell_reset_bottom_load_memL2 U.val
            (hcenter i U.val U.property).memLp)))
      (scalarResidualField U.val M.nu (Annealed.sigmaBar M m : ℝ) M.nu_pos
        (Annealed.sigmaBar M m).property
        (oldSignedCellCoefficient Q U.val
          (openCubeSet_subset_of_mem_descendantsAtDepth U.property)
          (oldCutoffSkewCoefficient m Q ω))
        (toHilbertBlockL2OfBlockField
          (upper_cell_reset_bottom_load_memL2 U.val
            (hcenter i U.val U.property).memLp))))

def gap' (Z : Cutoff.CutoffSample 2 → ι → Vec 2 → BlockVec 2)
    (ω : Cutoff.CutoffSample 2) : ℝ := ∑ i ∈ S,
  scalarFieldEnergy M.nu (Annealed.sigmaBar M m : ℝ) (oldCutoffSkewCoefficient m Q ω)
    (Z ω i - oldSignedLocalResidual Q depth M.nu (Annealed.sigmaBar M m : ℝ)
      M.nu_pos (Annealed.sigmaBar M m).property (oldCutoffSkewCoefficient m Q ω)
      (topLoad Q u i) (topLoad_memL2 Q u i))

end Defs2

section Pathwise

variable {ι : Type*} (S : Finset ι) (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2)
  (depth : ℕ) (u : ι → H10Function (openCubeSet Q))

/-- `Gap ≤ G_pair` for the named actual quantities. -/
theorem actual_gap_le_gpair
    (H : ∀ i, HasWeakHessianOn (openCubeSet Q) (u i).toH1Function)
    (hpos : ∀ i, ∀ U : TriadicCube 2, U ∈ descendantsAtDepth Q depth →
      ScalarPositiveHaarAdmissible U (fun x j => (u i).toH1Function.grad x j))
    (hcenter : ∀ i, ∀ U : TriadicCube 2, U ∈ descendantsAtDepth Q depth →
      ScalarPositiveHaarAdmissible U (fun x j =>
        (u i).toH1Function.grad x j -
          cubeAverage U (fun y => (u i).toH1Function.grad y j)))
    (Z : Cutoff.CutoffSample 2 → ι → Vec 2 → BlockVec 2)
    (hZ : ∀ ω i, IsScalarOldMaximizer Q M.nu (Annealed.sigmaBar M m : ℝ)
      (oldCutoffSkewCoefficient m Q ω) (fun x => (u i).toH1Function.grad x) (Z ω i))
    (ω : Cutoff.CutoffSample 2) :
    gap' S M m Q depth u Z ω ≤ apair S M m Q depth u ω +
      2 * Real.sqrt (pK' S M m Q depth u ω * rK' S M m Q depth u ω) +
      rK' S M m Q depth u ω +
      2 * Real.sqrt (pD S M m Q depth u ω * rD S M m Q depth u hcenter ω) +
      rD S M m Q depth u hcenter ω +
      2 * Real.sqrt (deltaSq' S Q depth u) *
        (Real.sqrt (bhist M m Q depth ω *
          (Real.sqrt (pK' S M m Q depth u ω) + Real.sqrt (rK' S M m Q depth u ω)) ^ 2) +
          Real.sqrt (omega2 S Q u)) := by
  have := smooth_feedback_h2_gap_le_gpair S M m Q depth ω u H hpos hcenter
    (Z ω) (hZ ω)
  exact this

end Pathwise

end

end ASDExplicitGamma.Scalar
