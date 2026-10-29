module

public import ASDExplicitGamma.Scalar.SmoothFeedbackVaryingSource

/-! Finite-family Minkowski aggregation for the actual OLD cell residuals. -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open MeasureTheory Homogenization Response Triadic Variational
open ASDExplicitGamma.Native

noncomputable section

private theorem smooth_feedback_finite_energy_minkowski
    {α : Type*} (s : Finset α) (p r : α → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hr : ∀ i, 0 ≤ r i) :
    (∑ i ∈ s, (Real.sqrt (p i) + Real.sqrt (r i)) ^ 2) ≤
      (Real.sqrt (∑ i ∈ s, p i) + Real.sqrt (∑ i ∈ s, r i)) ^ 2 := by
  classical
  have hpSum : 0 ≤ ∑ i ∈ s, p i := Finset.sum_nonneg fun i hi => hp i
  have hrSum : 0 ≤ ∑ i ∈ s, r i := Finset.sum_nonneg fun i hi => hr i
  have hcross := Real.sum_sqrt_mul_sqrt_le (s := s) (f := p) (g := r)
    hp hr
  have hExpand :
      (∑ i ∈ s, (Real.sqrt (p i) + Real.sqrt (r i)) ^ 2) =
        (∑ i ∈ s, p i) + 2 * (∑ i ∈ s, Real.sqrt (p i) * Real.sqrt (r i)) +
          (∑ i ∈ s, r i) := by
    calc
      _ = ∑ i ∈ s, (p i + 2 * (Real.sqrt (p i) * Real.sqrt (r i)) + r i) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [add_sq, Real.sq_sqrt (hp i), Real.sq_sqrt (hr i)]
        ring
      _ = _ := by simp only [Finset.sum_add_distrib, Finset.mul_sum]
  have hpRoot := Real.sq_sqrt hpSum
  have hrRoot := Real.sq_sqrt hrSum
  rw [hExpand]
  nlinarith

private theorem smooth_feedback_cell_average_energy_minkowski
    (Q : TriadicCube 2) (depth : ℕ)
    (p r : OldSignedCellIndex Q depth → ℝ)
    (hp : ∀ U, 0 ≤ p U) (hr : ∀ U, 0 ≤ r U) :
    oldSignedCellAverage Q depth
        (fun U => (Real.sqrt (p U) + Real.sqrt (r U)) ^ 2) ≤
      (Real.sqrt (oldSignedCellAverage Q depth p) +
        Real.sqrt (oldSignedCellAverage Q depth r)) ^ 2 := by
  classical
  let c : ℝ := ((descendantsAtDepth Q depth).card : ℝ)⁻¹
  have hc : 0 ≤ c := by positivity
  have hcp : ∀ U, 0 ≤ c * p U := fun U => mul_nonneg hc (hp U)
  have hcr : ∀ U, 0 ≤ c * r U := fun U => mul_nonneg hc (hr U)
  have hleft :
      oldSignedCellAverage Q depth
          (fun U => (Real.sqrt (p U) + Real.sqrt (r U)) ^ 2) =
        ∑ U : OldSignedCellIndex Q depth,
          (Real.sqrt (c * p U) + Real.sqrt (c * r U)) ^ 2 := by
    rw [oldSignedCellAverage, show ((descendantsAtDepth Q depth).card : ℝ)⁻¹ = c by rfl,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro U hU
    rw [Real.sqrt_mul hc (p U), Real.sqrt_mul hc (r U)]
    conv_lhs => rw [← Real.sq_sqrt hc]
    ring
  have hfinite := smooth_feedback_finite_energy_minkowski
    (Finset.univ : Finset (OldSignedCellIndex Q depth))
    (fun U => c * p U) (fun U => c * r U)
    hcp hcr
  have hright :
      (Real.sqrt (∑ U : OldSignedCellIndex Q depth, c * p U) +
        Real.sqrt (∑ U : OldSignedCellIndex Q depth, c * r U)) ^ 2 =
      (Real.sqrt (oldSignedCellAverage Q depth p) +
        Real.sqrt (oldSignedCellAverage Q depth r)) ^ 2 := by
    simp [oldSignedCellAverage, c, Finset.mul_sum]
  calc
    oldSignedCellAverage Q depth (fun U => (Real.sqrt (p U) + Real.sqrt (r U)) ^ 2) =
        ∑ U : OldSignedCellIndex Q depth,
          (Real.sqrt (c * p U) + Real.sqrt (c * r U)) ^ 2 := hleft
    _ ≤ (Real.sqrt (∑ U : OldSignedCellIndex Q depth, c * p U) +
        Real.sqrt (∑ U : OldSignedCellIndex Q depth, c * r U)) ^ 2 := hfinite
    _ = (Real.sqrt (oldSignedCellAverage Q depth p) +
        Real.sqrt (oldSignedCellAverage Q depth r)) ^ 2 := hright

theorem smooth_feedback_h2_source_patch_energy_triangle
    {ι : Type*} (S : Finset ι)
    (Q : TriadicCube 2) (depth : ℕ) (nu sigma : ℝ)
    (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q))
    (u : ι → H10Function (openCubeSet Q))
    (hpos : ∀ i, ∀ U : TriadicCube 2,
      U ∈ descendantsAtDepth Q depth →
        ScalarPositiveHaarAdmissible U (fun x j => (u i).toH1Function.grad x j))
    (hcenter : ∀ i, ∀ U : TriadicCube 2,
      U ∈ descendantsAtDepth Q depth →
        ScalarPositiveHaarAdmissible U (fun x j =>
          (u i).toH1Function.grad x j -
            cubeAverage U (fun y => (u i).toH1Function.grad y j))) :
    let f : ι → Vec 2 → Vec 2 := fun i x => (u i).toH1Function.grad x
    let F : ι → Vec 2 → BlockVec 2 := fun i x => (f i x, 0)
    let hF : ∀ i, MemBlockL2 (openCubeSet Q) (F i) := fun i =>
      memBlockL2_blockField (u i).toH1Function.grad_memVectorL2 MemLp.zero
    let E : ι → ℝ := fun i => oldSignedCellAverage Q depth (fun U =>
      oldSignedEnergyPairing U.val nu sigma
        (oldSignedCellCoefficient Q U.val
          (openCubeSet_subset_of_mem_descendantsAtDepth U.property) k)
        (oldSignedCellResidual Q U.val
          (openCubeSet_subset_of_mem_descendantsAtDepth U.property)
          nu sigma hnu hsigma k (F i) (hF i))
        (oldSignedCellResidual Q U.val
          (openCubeSet_subset_of_mem_descendantsAtDepth U.property)
          nu sigma hnu hsigma k (F i) (hF i)))
    let P_K : ℝ := ∑ i ∈ S, oldSignedCellAverage Q depth (fun U =>
      let mean : Vec 2 := fun j => cubeAverage U.val (fun x => f i x j)
      let P : BlockVec 2 := (mean, 0)
      blockVecDot P (blockMatVecMul
        (coarseBlockMatrix (openCubeSet U.val)
          (responseFramePlanarCoefficientField nu sigma
            (oldSignedCellCoefficient Q U.val
              (openCubeSet_subset_of_mem_descendantsAtDepth U.property) k))) P))
    let R_K : ℝ := ∑ i ∈ S, oldSignedCellAverage Q depth (fun U =>
      let hU := openCubeSet_subset_of_mem_descendantsAtDepth U.property
      let mean : Vec 2 := fun j => cubeAverage U.val (fun x => f i x j)
      let c : Vec 2 → Vec 2 := fun x j => f i x j - mean j
      let C : Vec 2 → BlockVec 2 := fun x => (c x, 0)
      let hC : MemBlockL2 (openCubeSet Q) C :=
        by
          have hsub : MemLp (fun x => F i x - (mean, 0)) 2
              (volumeMeasureOn (openCubeSet Q)) :=
            (hF i).sub (memLp_const (mean, 0))
          convert hsub using 1
          ext x j
          · simp [C, c, F, f]
          · change (0 : Vec 2) j = (0 - 0 : Vec 2) j
            simp
      oldSignedEnergyPairing U.val nu sigma
        (oldSignedCellCoefficient Q U.val hU k)
        (oldSignedCellResidual Q U.val hU nu sigma hnu hsigma k C hC)
        (oldSignedCellResidual Q U.val hU nu sigma hnu hsigma k C hC))
    (∑ i ∈ S, E i) ≤ (Real.sqrt P_K + Real.sqrt R_K) ^ 2 := by
  classical
  dsimp only
  let f : ι → Vec 2 → Vec 2 := fun i x => (u i).toH1Function.grad x
  let F : ι → Vec 2 → BlockVec 2 := fun i x => (f i x, 0)
  let hF : ∀ i, MemBlockL2 (openCubeSet Q) (F i) := fun i =>
    memBlockL2_blockField (u i).toH1Function.grad_memVectorL2 MemLp.zero
  let p : ι → OldSignedCellIndex Q depth → ℝ := fun i U =>
    let mean : Vec 2 := fun j => cubeAverage U.val (fun x => f i x j)
    let P : BlockVec 2 := (mean, 0)
    blockVecDot P (blockMatVecMul
      (coarseBlockMatrix (openCubeSet U.val)
        (responseFramePlanarCoefficientField nu sigma
          (oldSignedCellCoefficient Q U.val
            (openCubeSet_subset_of_mem_descendantsAtDepth U.property) k))) P)
  let r : ι → OldSignedCellIndex Q depth → ℝ := fun i U =>
    let hU := openCubeSet_subset_of_mem_descendantsAtDepth U.property
    let mean : Vec 2 := fun j => cubeAverage U.val (fun x => f i x j)
    let c : Vec 2 → Vec 2 := fun x j => f i x j - mean j
    let C : Vec 2 → BlockVec 2 := fun x => (c x, 0)
      let hC : MemBlockL2 (openCubeSet Q) C :=
        by
          have hsub : MemLp (fun x => F i x - (mean, 0)) 2
              (volumeMeasureOn (openCubeSet Q)) :=
            (hF i).sub (memLp_const (mean, 0))
          convert hsub using 1
          ext x j
          · simp [C, c, F, f]
          · change (0 : Vec 2) j = (0 - 0 : Vec 2) j
            simp
    oldSignedEnergyPairing U.val nu sigma
      (oldSignedCellCoefficient Q U.val hU k)
      (oldSignedCellResidual Q U.val hU nu sigma hnu hsigma k C hC)
      (oldSignedCellResidual Q U.val hU nu sigma hnu hsigma k C hC)
  let e : ι → OldSignedCellIndex Q depth → ℝ := fun i U =>
    oldSignedEnergyPairing U.val nu sigma
      (oldSignedCellCoefficient Q U.val
        (openCubeSet_subset_of_mem_descendantsAtDepth U.property) k)
      (oldSignedCellResidual Q U.val
        (openCubeSet_subset_of_mem_descendantsAtDepth U.property)
        nu sigma hnu hsigma k (F i) (hF i))
      (oldSignedCellResidual Q U.val
        (openCubeSet_subset_of_mem_descendantsAtDepth U.property)
        nu sigma hnu hsigma k (F i) (hF i))
  have hp : ∀ i U, 0 ≤ p i U := by
    intro i U
    dsimp [p]
    rw [← old_signed_affine_energy U.val nu sigma hnu hsigma
      (oldSignedCellCoefficient Q U.val
        (openCubeSet_subset_of_mem_descendantsAtDepth U.property) k)]
    exact old_signed_energy_pairing_nonneg U.val nu sigma hnu hsigma _ _
  have hr : ∀ i U, 0 ≤ r i U := by
    intro i U
    exact old_signed_energy_pairing_nonneg U.val nu sigma hnu hsigma _ _
  have hcell : ∀ i U, e i U ≤ (Real.sqrt (p i U) + Real.sqrt (r i U)) ^ 2 := by
    intro i U
    let hU := openCubeSet_subset_of_mem_descendantsAtDepth U.property
    let hFR : MemBlockL2 (openCubeSet U.val) (F i) :=
      (hF i).mono_measure (Measure.restrict_mono_set volume hU)
    let hCell : MemBlockL2 (openCubeSet U.val) (F i) :=
      scalar_source_block_memL2 U.val (hpos i U.val U.property).memLp
    have hInput :
        toHilbertBlockL2OfBlockField hFR = toHilbertBlockL2OfBlockField hCell := by
      apply Lp.ext
      filter_upwards [coeFn_toHilbertBlockL2OfBlockField hFR,
        coeFn_toHilbertBlockL2OfBlockField hCell] with x hxFR hxCell
      calc
        (toHilbertBlockL2OfBlockField hFR) x = HilbertBlockVec.ofBlockVec (F i x) := by
          simpa [hilbertifyBlockField] using hxFR
        _ = (toHilbertBlockL2OfBlockField hCell) x := by
          simpa [hilbertifyBlockField, scalar_source_block_memL2] using hxCell.symm
    have hResidual :
        oldSignedCellResidual Q U.val hU nu sigma hnu hsigma k (F i) (hF i) =
          scalarResidualField U.val nu sigma hnu hsigma
            (oldSignedCellCoefficient Q U.val hU k)
            (toHilbertBlockL2OfBlockField hCell) := by
      unfold oldSignedCellResidual
      exact congrArg (scalarResidualField U.val nu sigma hnu hsigma
        (oldSignedCellCoefficient Q U.val hU k)) hInput
    have htriangle := smooth_feedback_scalar_top_source_cell_energy_triangle
      U.val nu sigma hnu hsigma
      (oldSignedCellCoefficient Q U.val hU k)
      (f i) (hpos i U.val U.property) (hcenter i U.val U.property)
    dsimp only at htriangle
    dsimp [e, p, r]
    rw [hResidual]
    exact htriangle
  let pbar : ι → ℝ := fun i => oldSignedCellAverage Q depth (p i)
  let rbar : ι → ℝ := fun i => oldSignedCellAverage Q depth (r i)
  have hpbar : ∀ i, 0 ≤ pbar i := by
    intro i
    unfold pbar oldSignedCellAverage
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun U hU => hp i U)
  have hrbar : ∀ i, 0 ≤ rbar i := by
    intro i
    unfold rbar oldSignedCellAverage
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun U hU => hr i U)
  have hcellAvg : ∀ i,
      oldSignedCellAverage Q depth (e i) ≤
        (Real.sqrt (pbar i) + Real.sqrt (rbar i)) ^ 2 := by
    intro i
    calc
      oldSignedCellAverage Q depth (e i) ≤
          oldSignedCellAverage Q depth (fun U =>
            (Real.sqrt (p i U) + Real.sqrt (r i U)) ^ 2) :=
        old_signed_cell_average_mono Q depth (fun U => hcell i U)
      _ ≤ _ := smooth_feedback_cell_average_energy_minkowski Q depth (p i) (r i)
        (hp i) (hr i)
  have hFamily := smooth_feedback_finite_energy_minkowski S pbar rbar
    hpbar hrbar
  have hsum :
      (∑ i ∈ S, oldSignedCellAverage Q depth (e i)) ≤
        ∑ i ∈ S, (Real.sqrt (pbar i) + Real.sqrt (rbar i)) ^ 2 :=
    Finset.sum_le_sum fun i hi => hcellAvg i
  have hP :
      (∑ i ∈ S, pbar i) =
        ∑ i ∈ S, oldSignedCellAverage Q depth (p i) := rfl
  have hR :
      (∑ i ∈ S, rbar i) =
        ∑ i ∈ S, oldSignedCellAverage Q depth (r i) := rfl
  simpa [e, pbar, rbar, p, r, f, F, hF, hP, hR] using hsum.trans hFamily

end
end ASDExplicitGamma.Scalar
