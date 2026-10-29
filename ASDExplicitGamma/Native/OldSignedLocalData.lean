module

public import ASDExplicitGamma.Scalar.ProjectionFields
public import ASDExplicitGamma.Scalar.ProjectionCharacterization
public import ASDExplicitGamma.Scalar.LocalProjectionOrthogonality
public import ASDExplicitGamma.Triadic.PlanarNeumannBridge

/-! Concrete OLD signed-generator cell restrictions and weighted projections. -/
@[expose] public section

namespace ASDExplicitGamma.Native

open Homogenization MeasureTheory Response Scalar Triadic Variational

noncomputable section

/-- Restrict the parent response coefficient to the closed descendant square. -/
def oldSignedCellCoefficient (Q R : TriadicCube 2)
    (hRQ : openCubeSet R ⊆ openCubeSet Q)
    (k : ResponseCoefficient (openCubeSet Q)) :
    ResponseCoefficient (openCubeSet R) := by
  let incl : C(closure (openCubeSet R), closure (openCubeSet Q)) :=
    ⟨fun x => ⟨x.1, (closure_mono hRQ) x.2⟩,
      continuous_subtype_val.subtype_mk fun x => (closure_mono hRQ) x.2⟩
  exact k.compContinuous incl

/-- The actual weighted residual minimizer on one cell, for the restricted source. -/
def oldSignedCellResidual (Q R : TriadicCube 2)
    (hRQ : openCubeSet R ⊆ openCubeSet Q)
    (nu sigma : ℝ) (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (F : Vec 2 → BlockVec 2)
    (hF : MemBlockL2 (openCubeSet Q) F) : BlockL2 (openCubeSet R) := by
  let hFR : MemBlockL2 (openCubeSet R) F :=
    hF.mono_measure (Measure.restrict_mono_set volume hRQ)
  exact scalarResidualField R nu sigma hnu hsigma
    (oldSignedCellCoefficient Q R hRQ k)
    (toHilbertBlockL2OfBlockField hFR)

/-- Sum the zero extensions of the actual cell residual minimizers on a finite
triadic descendant partition. -/
def oldSignedLocalResidual (Q : TriadicCube 2) (depth : ℕ)
    (nu sigma : ℝ) (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (F : Vec 2 → BlockVec 2)
    (hF : MemBlockL2 (openCubeSet Q) F) : Vec 2 → BlockVec 2 := by
  classical
  exact fun x => ∑ R : {R : TriadicCube 2 // R ∈ descendantsAtDepth Q depth},
    (openCubeSet R.1).indicator
      (oldSignedCellResidual Q R.1
        (openCubeSet_subset_of_mem_descendantsAtDepth R.2)
        nu sigma hnu hsigma k F hF) x

/-- Normalized pairing in the actual fixed-frame response coefficient. -/
def oldSignedEnergyPairing (Q : TriadicCube 2) (nu sigma : ℝ)
    (k : ResponseCoefficient (openCubeSet Q)) (F G : Vec 2 → BlockVec 2) : ℝ :=
  volumeAverage (openCubeSet Q) (fun x => blockVecDot (F x)
    (blockMatVecMul (blockCoeffField (responseFramePlanarCoefficientField nu sigma k) x)
      (G x)))

/-- On each open descendant, the finite zero-extension sum is exactly that
cell's actual weighted residual minimizer. -/
theorem old_signed_local_residual_restrict (Q : TriadicCube 2) (depth : ℕ)
    (nu sigma : ℝ) (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (F : Vec 2 → BlockVec 2)
    (hF : MemBlockL2 (openCubeSet Q) F) (R : TriadicCube 2)
    (hR : R ∈ descendantsAtDepth Q depth) :
    oldSignedLocalResidual Q depth nu sigma hnu hsigma k F hF =ᵐ[
      volumeMeasureOn (openCubeSet R)]
      oldSignedCellResidual Q R (openCubeSet_subset_of_mem_descendantsAtDepth hR)
        nu sigma hnu hsigma k F hF := by
  classical
  apply (ae_restrict_iff' (measurableSet_openCubeSet R)).2
  filter_upwards with x hx
  change (∑ S : {S : TriadicCube 2 // S ∈ descendantsAtDepth Q depth},
    (openCubeSet S.1).indicator
      (oldSignedCellResidual Q S.1
        (openCubeSet_subset_of_mem_descendantsAtDepth S.2)
        nu sigma hnu hsigma k F hF) x) = _
  rw [Fintype.sum_eq_single ⟨R, hR⟩]
  · simp [hx]
  · intro S hne
    have hSR : S.1 ≠ R := by
      intro heq
      apply hne
      exact Subtype.ext heq
    have hdisj := pairwiseDisjoint_openCubeSet_descendantsAtDepth Q depth
      S.2 hR hSR
    have hxS : x ∉ openCubeSet S.1 := fun hxS =>
      (Set.disjoint_left.mp hdisj) hxS hx
    simp [hxS]

/-- The finite zero-extension sum is square-integrable on the parent. -/
theorem old_signed_local_residual_memLp (Q : TriadicCube 2) (depth : ℕ)
    (nu sigma : ℝ) (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (F : Vec 2 → BlockVec 2)
    (hF : MemBlockL2 (openCubeSet Q) F) :
    MemBlockL2 (openCubeSet Q)
      (oldSignedLocalResidual Q depth nu sigma hnu hsigma k F hF) := by
  classical
  let D := {R : TriadicCube 2 // R ∈ descendantsAtDepth Q depth}
  have hterm (R : D) :
      MemBlockL2 (openCubeSet Q) ((openCubeSet R.1).indicator
        (oldSignedCellResidual Q R.1
          (openCubeSet_subset_of_mem_descendantsAtDepth R.2)
          nu sigma hnu hsigma k F hF)) := by
    have hcell : MemBlockL2 (openCubeSet R.1)
        (oldSignedCellResidual Q R.1
          (openCubeSet_subset_of_mem_descendantsAtDepth R.2)
          nu sigma hnu hsigma k F hF) :=
      (oldSignedCellResidual Q R.1
        (openCubeSet_subset_of_mem_descendantsAtDepth R.2)
        nu sigma hnu hsigma k F hF).property
    have hglobal : MemLp ((openCubeSet R.1).indicator
        (oldSignedCellResidual Q R.1
          (openCubeSet_subset_of_mem_descendantsAtDepth R.2)
          nu sigma hnu hsigma k F hF)) 2 volume :=
      (memLp_indicator_iff_restrict (measurableSet_openCubeSet R.1)).2 hcell
    exact hglobal.mono_measure Measure.restrict_le_self
  have hsum : MemBlockL2 (openCubeSet Q) (fun x => ∑ R : D,
      (openCubeSet R.1).indicator
        (oldSignedCellResidual Q R.1
          (openCubeSet_subset_of_mem_descendantsAtDepth R.2)
          nu sigma hnu hsigma k F hF) x) := by
    simpa only [Finset.sum_apply] using
      (memLp_finsetSum Finset.univ (fun R _ => hterm R))
  exact hsum

end

end ASDExplicitGamma.Native
