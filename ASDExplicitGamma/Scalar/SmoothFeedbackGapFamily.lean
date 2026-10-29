/-
Copyright (c) 2026 Scott N. Armstrong. All rights reserved.
-/
module

public import ASDExplicitGamma.Scalar.SmoothFeedbackGapIdentity
public import ASDExplicitGamma.Scalar.SmoothFeedbackBottomSourceTriangle
public import ASDExplicitGamma.Scalar.SmoothFeedbackSourceCharge

/-! Finite-family pathwise assembly of the actual OLD two-patch gap identity
with the proved H² source-pairing lower bound. -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open MeasureTheory Homogenization Response Triadic Variational
open ASDExplicitGamma.Native

noncomputable section

private theorem gap_family_scalar_energy_eq_pairing
    (Q : TriadicCube 2) (nu sigma : ℝ) (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (F : Vec 2 → BlockVec 2) :
    scalarFieldEnergy nu sigma k F = oldSignedEnergyPairing Q nu sigma k F F := by
  unfold scalarFieldEnergy oldSignedEnergyPairing
  apply congrArg (volumeAverage (openCubeSet Q))
  funext x
  rw [responseFrameEnergyDensity_eq_scaledCoefficientBlock nu sigma
    (responseCoefficientExtension k x) hnu hsigma]
  rfl

/-- For a finite family of genuine H² parent sources and their actual OLD
maximizers, the sum of pathwise gaps is bounded by the literal top and bottom
cell-patch energies and the actual source-pairing charge. This is the family
assembly before the separate source-patch energy triangles are applied. -/
theorem smooth_feedback_h2_family_gap_precomparison
    {ι : Type*} (S : Finset ι)
    (Q : TriadicCube 2) (depth : ℕ) (nu sigma : ℝ)
    (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q))
    (u : ι → H10Function (openCubeSet Q))
    (H : ∀ i, HasWeakHessianOn (openCubeSet Q) (u i).toH1Function)
    (Z : ι → Vec 2 → BlockVec 2)
    (hZ : ∀ i, IsScalarOldMaximizer Q nu sigma k
      (fun x => (u i).toH1Function.grad x) (Z i)) :
    let f : ι → Vec 2 → Vec 2 := fun i x => (u i).toH1Function.grad x
    let F : ι → Vec 2 → BlockVec 2 := fun i x => (f i x, 0)
    let hF := fun i =>
      memBlockL2_blockField (u i).toH1Function.grad_memVectorL2 MemLp.zero
    let Ytop : ι → Vec 2 → BlockVec 2 := fun i =>
      oldSignedLocalResidual Q depth nu sigma hnu hsigma k (F i) (hF i)
    let Ybottom : ι → Vec 2 → BlockVec 2 := fun i =>
      oldSignedLocalResidual Q depth nu sigma hnu hsigma k
        (scalarBottomLoad (f i))
        (scalar_bottom_load_memL2 (memVectorL2_fst_of_memBlockL2 (hF i)))
    let Etop : ι → ℝ := fun i =>
      oldSignedEnergyPairing Q nu sigma k (Ytop i) (Ytop i)
    let Ebottom : ι → ℝ := fun i =>
      oldSignedEnergyPairing Q nu sigma k (Ybottom i) (Ybottom i)
    let Cavg : ι → ℝ := fun i => oldSignedCellAverage Q depth (fun U =>
      vecNormSq (fun j => cubeAverage U.val (fun x => f i x j)))
    let Eavg : ι → ℝ := fun i => oldSignedCellAverage Q depth (fun U =>
      oldSignedEnergyPairing U.val nu sigma
        (oldSignedCellCoefficient Q U.val
          (openCubeSet_subset_of_mem_descendantsAtDepth U.property) k)
        (oldSignedCellResidual Q U.val
          (openCubeSet_subset_of_mem_descendantsAtDepth U.property)
          nu sigma hnu hsigma k (F i) (hF i))
        (oldSignedCellResidual Q U.val
          (openCubeSet_subset_of_mem_descendantsAtDepth U.property)
          nu sigma hnu hsigma k (F i) (hF i)))
    let Pavg : ι → ℝ := fun i => oldSignedCellAverage Q depth (fun U =>
      vectorPositiveHaarEnergy U.val
        (fun x => f i x - fun j => cubeAverage U.val (fun y => f i y j)))
    let Bmax := smoothFeedbackSourceHistoryMaximum Q depth nu sigma k
    (∑ i ∈ S, scalarFieldEnergy nu sigma k (Z i - Ytop i)) ≤
      (∑ i ∈ S, Etop i) - 2 * (∑ i ∈ S, Cavg i) +
        (∑ i ∈ S, Ebottom i) +
        2 * Real.sqrt (Bmax * (∑ i ∈ S, Eavg i)) *
          Real.sqrt (∑ i ∈ S, Pavg i) := by
  classical
  dsimp only
  let f : ι → Vec 2 → Vec 2 := fun i x => (u i).toH1Function.grad x
  let F : ι → Vec 2 → BlockVec 2 := fun i x => (f i x, 0)
  let hF := fun i =>
    memBlockL2_blockField (u i).toH1Function.grad_memVectorL2 MemLp.zero
  let Ytop : ι → Vec 2 → BlockVec 2 := fun i =>
    oldSignedLocalResidual Q depth nu sigma hnu hsigma k (F i) (hF i)
  let Ybottom : ι → Vec 2 → BlockVec 2 := fun i =>
    oldSignedLocalResidual Q depth nu sigma hnu hsigma k
      (scalarBottomLoad (f i))
      (scalar_bottom_load_memL2 (memVectorL2_fst_of_memBlockL2 (hF i)))
  let Etop : ι → ℝ := fun i =>
    oldSignedEnergyPairing Q nu sigma k (Ytop i) (Ytop i)
  let Ebottom : ι → ℝ := fun i =>
    oldSignedEnergyPairing Q nu sigma k (Ybottom i) (Ybottom i)
  let Cavg : ι → ℝ := fun i => oldSignedCellAverage Q depth (fun U =>
    vecNormSq (fun j => cubeAverage U.val (fun x => f i x j)))
  let Eavg : ι → ℝ := fun i => oldSignedCellAverage Q depth (fun U =>
    oldSignedEnergyPairing U.val nu sigma
      (oldSignedCellCoefficient Q U.val
        (openCubeSet_subset_of_mem_descendantsAtDepth U.property) k)
      (oldSignedCellResidual Q U.val
        (openCubeSet_subset_of_mem_descendantsAtDepth U.property)
        nu sigma hnu hsigma k (F i) (hF i))
      (oldSignedCellResidual Q U.val
        (openCubeSet_subset_of_mem_descendantsAtDepth U.property)
        nu sigma hnu hsigma k (F i) (hF i)))
  let Pavg : ι → ℝ := fun i => oldSignedCellAverage Q depth (fun U =>
    vectorPositiveHaarEnergy U.val
      (fun x => f i x - fun j => cubeAverage U.val (fun y => f i y j)))
  let Bmax := smoothFeedbackSourceHistoryMaximum Q depth nu sigma k
  have hW (i : ι) : ScalarVariation (openCubeSet Q) (fun x => (f i x, 0)) := by
    refine ⟨hF i, ?_, ?_⟩
    · simpa [f] using (u i).isPotentialZeroTraceOn
    · exact isSolenoidalZeroNormalTraceOn_zero
  have hTwo (i : ι) :
      scalarFieldEnergy nu sigma k (Z i - Ytop i) ≤
        scalarFieldEnergy nu sigma k (Ytop i) -
          2 * scalarSourcePairing (openCubeSet Q) (f i) (Ytop i) +
          scalarFieldEnergy nu sigma k (Ybottom i) := by
    simpa [Ytop, Ybottom, F, hF, f] using
      smooth_feedback_actual_two_patch_gap_bound Q depth nu sigma hnu hsigma k
        (f i) (hW i) (Z i) (hZ i)
  have hTopCell (i : ι) : Etop i = Eavg i := by
    change oldSignedEnergyPairing Q nu sigma k (Ytop i) (Ytop i) = _
    have hpart := old_signed_local_residual_cell_pairing Q depth nu sigma hnu hsigma k
      (F i) (F i) (hF i) (hF i)
    simpa [Ytop, Etop, Eavg, F, hF] using hpart
  have hBottomCell (i : ι) : Ebottom i =
      oldSignedCellAverage Q depth (fun U =>
        oldSignedEnergyPairing U.val nu sigma
          (oldSignedCellCoefficient Q U.val
            (openCubeSet_subset_of_mem_descendantsAtDepth U.property) k)
          (oldSignedCellResidual Q U.val
            (openCubeSet_subset_of_mem_descendantsAtDepth U.property)
            nu sigma hnu hsigma k (scalarBottomLoad (f i))
              (scalar_bottom_load_memL2
                (memVectorL2_fst_of_memBlockL2 (hF i))))
          (oldSignedCellResidual Q U.val
            (openCubeSet_subset_of_mem_descendantsAtDepth U.property)
            nu sigma hnu hsigma k (scalarBottomLoad (f i))
              (scalar_bottom_load_memL2
                (memVectorL2_fst_of_memBlockL2 (hF i))))) := by
    have hpart := old_signed_local_residual_cell_pairing Q depth nu sigma hnu hsigma k
      (scalarBottomLoad (f i)) (scalarBottomLoad (f i))
      (scalar_bottom_load_memL2 (memVectorL2_fst_of_memBlockL2 (hF i)))
      (scalar_bottom_load_memL2 (memVectorL2_fst_of_memBlockL2 (hF i)))
    simpa [Ybottom, Ebottom] using hpart
  have hEnergyEqTop (i : ι) : scalarFieldEnergy nu sigma k (Ytop i) = Etop i := by
    rw [gap_family_scalar_energy_eq_pairing Q nu sigma hnu hsigma k]
  have hEnergyEqBottom (i : ι) : scalarFieldEnergy nu sigma k (Ybottom i) = Ebottom i := by
    rw [gap_family_scalar_energy_eq_pairing Q nu sigma hnu hsigma k]
  have hsumTwo :
      (∑ i ∈ S, scalarFieldEnergy nu sigma k (Z i - Ytop i)) ≤
        (∑ i ∈ S, Etop i) -
          2 * (∑ i ∈ S, scalarSourcePairing (openCubeSet Q) (f i) (Ytop i)) +
          (∑ i ∈ S, Ebottom i) := by
    have hs := Finset.sum_le_sum (s := S) (fun i _ => hTwo i)
    calc
      _ ≤ ∑ i ∈ S,
          (scalarFieldEnergy nu sigma k (Ytop i) -
            2 * scalarSourcePairing (openCubeSet Q) (f i) (Ytop i) +
            scalarFieldEnergy nu sigma k (Ybottom i)) := hs
      _ = _ := by
        simp_rw [hEnergyEqTop, hEnergyEqBottom]
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  have hpair :
      (∑ i ∈ S, scalarSourcePairing (openCubeSet Q) (f i) (Ytop i)) ≥
        (∑ i ∈ S, Cavg i) -
          Real.sqrt (Bmax * (∑ i ∈ S, Eavg i)) *
            Real.sqrt (∑ i ∈ S, Pavg i) := by
    simpa [f, F, hF, Ytop, Cavg, Eavg, Pavg, Bmax] using
      smooth_feedback_h2_source_patch_family_pairing_lower
        S Q depth nu sigma hnu hsigma k u H
  have hfinal := calc
      (∑ i ∈ S, scalarFieldEnergy nu sigma k (Z i - Ytop i)) ≤
          (∑ i ∈ S, Etop i) -
            2 * (∑ i ∈ S, scalarSourcePairing (openCubeSet Q) (f i) (Ytop i)) +
            (∑ i ∈ S, Ebottom i) := hsumTwo
      _ ≤ (∑ i ∈ S, Etop i) - 2 * (∑ i ∈ S, Cavg i) +
            (∑ i ∈ S, Ebottom i) +
              2 * Real.sqrt (Bmax * (∑ i ∈ S, Eavg i)) *
                Real.sqrt (∑ i ∈ S, Pavg i) := by
          nlinarith [hpair]
  exact hfinal

/-- Aggregate the literal RESET-bottom cell triangles over a finite family
and the physical equal-volume source-cell partition. The result is the
bottom-patch energy split used after global OLD-maximizer duality. -/
theorem smooth_feedback_h2_family_bottom_patch_energy_triangle
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
    let P_D : ℝ := ∑ i ∈ S, oldSignedCellAverage Q depth (fun U =>
      let mean : Vec 2 := fun j => cubeAverage U.val (fun x => f i x j)
      let P : BlockVec 2 := (0, mean)
      blockVecDot P (blockMatVecMul
        (coarseBlockMatrix (openCubeSet U.val)
          (responseFramePlanarCoefficientField nu sigma
            (oldSignedCellCoefficient Q U.val
              (openCubeSet_subset_of_mem_descendantsAtDepth U.property) k))) P))
    let R_D : ℝ := ∑ i ∈ S, oldSignedCellAverage Q depth (fun U =>
      let hU := openCubeSet_subset_of_mem_descendantsAtDepth U.property
      let hC := upper_cell_reset_bottom_load_memL2 U.val
        (hcenter i U.val U.property).memLp
      let YC := scalarResidualField U.val nu sigma hnu hsigma
        (oldSignedCellCoefficient Q U.val hU k)
        (toHilbertBlockL2OfBlockField hC)
      oldSignedEnergyPairing U.val nu sigma
        (oldSignedCellCoefficient Q U.val hU k) YC YC)
    let E_D : ℝ := ∑ i ∈ S, oldSignedCellAverage Q depth (fun U =>
      let hU := openCubeSet_subset_of_mem_descendantsAtDepth U.property
      let hB := upper_cell_reset_bottom_load_memL2 U.val
        (hpos i U.val U.property).memLp
      let YB := scalarResidualField U.val nu sigma hnu hsigma
        (oldSignedCellCoefficient Q U.val hU k)
        (toHilbertBlockL2OfBlockField hB)
      oldSignedEnergyPairing U.val nu sigma
        (oldSignedCellCoefficient Q U.val hU k) YB YB)
    E_D ≤ (Real.sqrt P_D + Real.sqrt R_D) ^ 2 := by
  classical
  dsimp only
  let f : ι → Vec 2 → Vec 2 := fun i x => (u i).toH1Function.grad x
  let Pcell : ι → OldSignedCellIndex Q depth → ℝ := fun i U =>
    let mean : Vec 2 := fun j => cubeAverage U.val (fun x => f i x j)
    let P : BlockVec 2 := (0, mean)
    blockVecDot P (blockMatVecMul
      (coarseBlockMatrix (openCubeSet U.val)
        (responseFramePlanarCoefficientField nu sigma
          (oldSignedCellCoefficient Q U.val
            (openCubeSet_subset_of_mem_descendantsAtDepth U.property) k))) P)
  let Rcell : ι → OldSignedCellIndex Q depth → ℝ := fun i U =>
    let hU := openCubeSet_subset_of_mem_descendantsAtDepth U.property
    let hC := upper_cell_reset_bottom_load_memL2 U.val
      (hcenter i U.val U.property).memLp
    let YC := scalarResidualField U.val nu sigma hnu hsigma
      (oldSignedCellCoefficient Q U.val hU k)
      (toHilbertBlockL2OfBlockField hC)
    oldSignedEnergyPairing U.val nu sigma
      (oldSignedCellCoefficient Q U.val hU k) YC YC
  let Bcell : ι → OldSignedCellIndex Q depth → ℝ := fun i U =>
    let hU := openCubeSet_subset_of_mem_descendantsAtDepth U.property
    let hB := upper_cell_reset_bottom_load_memL2 U.val
      (hpos i U.val U.property).memLp
    let YB := scalarResidualField U.val nu sigma hnu hsigma
      (oldSignedCellCoefficient Q U.val hU k)
      (toHilbertBlockL2OfBlockField hB)
    oldSignedEnergyPairing U.val nu sigma
      (oldSignedCellCoefficient Q U.val hU k) YB YB
  let Pavg : ι → ℝ := fun i => oldSignedCellAverage Q depth (Pcell i)
  let Ravg : ι → ℝ := fun i => oldSignedCellAverage Q depth (Rcell i)
  let Bavg : ι → ℝ := fun i => oldSignedCellAverage Q depth (Bcell i)
  have hPcell (i : ι) (U : OldSignedCellIndex Q depth) : 0 ≤ Pcell i U := by
    let hU := openCubeSet_subset_of_mem_descendantsAtDepth U.property
    let kU := oldSignedCellCoefficient Q U.val hU k
    let mean : Vec 2 := fun j => cubeAverage U.val (fun x => f i x j)
    let P : BlockVec 2 := (0, mean)
    change 0 ≤ blockVecDot P (blockMatVecMul
      (coarseBlockMatrix (openCubeSet U.val)
        (responseFramePlanarCoefficientField nu sigma kU)) P)
    rw [← old_signed_affine_energy U.val nu sigma hnu hsigma kU P]
    exact old_signed_energy_pairing_nonneg U.val nu sigma hnu hsigma kU
      (scalarResidualField U.val nu sigma hnu hsigma kU
        ((scalarFrameRealization U.val nu sigma hnu hsigma kU).constantField P))
  have hRcell (i : ι) (U : OldSignedCellIndex Q depth) : 0 ≤ Rcell i U := by
    exact old_signed_energy_pairing_nonneg U.val nu sigma hnu hsigma
      (oldSignedCellCoefficient Q U.val
        (openCubeSet_subset_of_mem_descendantsAtDepth U.property) k) _
  have hBtri (i : ι) (U : OldSignedCellIndex Q depth) :
      Bcell i U ≤ (Real.sqrt (Pcell i U) + Real.sqrt (Rcell i U)) ^ 2 := by
    let hU := openCubeSet_subset_of_mem_descendantsAtDepth U.property
    let kU := oldSignedCellCoefficient Q U.val hU k
    let mean : Vec 2 := fun j => cubeAverage U.val (fun x => f i x j)
    let c : Vec 2 → Vec 2 := fun x j => f i x j - mean j
    simpa [Bcell, Pcell, Rcell, f, hU, kU, mean, c] using
      smooth_feedback_scalar_bottom_source_cell_energy_triangle U.val nu sigma
        hnu hsigma kU (f i) (hpos i U.val U.property)
        (hcenter i U.val U.property)
  have hCrossAvg (i : ι) :
      oldSignedCellAverage Q depth (fun U =>
        Real.sqrt (Pcell i U) * Real.sqrt (Rcell i U)) ≤
        Real.sqrt (Pavg i) * Real.sqrt (Ravg i) :=
    old_signed_cell_average_root_cauchy Q depth (Pcell i) (Rcell i)
      (hPcell i) (hRcell i)
  have hBavg (i : ι) :
      Bavg i ≤ Pavg i + Ravg i +
        2 * (Real.sqrt (Pavg i) * Real.sqrt (Ravg i)) := by
    have hmono := old_signed_cell_average_mono Q depth (hBtri i)
    have hsquare : oldSignedCellAverage Q depth (fun U =>
        (Real.sqrt (Pcell i U) + Real.sqrt (Rcell i U)) ^ 2) =
        Pavg i + Ravg i +
          2 * oldSignedCellAverage Q depth (fun U =>
            Real.sqrt (Pcell i U) * Real.sqrt (Rcell i U)) := by
      calc
        _ = oldSignedCellAverage Q depth (fun U =>
            Pcell i U + Rcell i U +
              2 * (Real.sqrt (Pcell i U) * Real.sqrt (Rcell i U))) := by
          apply congrArg (oldSignedCellAverage Q depth)
          funext U
          rw [add_sq, Real.sq_sqrt (hPcell i U), Real.sq_sqrt (hRcell i U)]
          ring
        _ = _ := by
          rw [old_signed_cell_average_add, old_signed_cell_average_add,
            old_signed_cell_average_mul]
    calc
      Bavg i ≤ oldSignedCellAverage Q depth (fun U =>
          (Real.sqrt (Pcell i U) + Real.sqrt (Rcell i U)) ^ 2) := hmono
      _ = Pavg i + Ravg i +
          2 * oldSignedCellAverage Q depth (fun U =>
            Real.sqrt (Pcell i U) * Real.sqrt (Rcell i U)) := hsquare
      _ ≤ _ := by nlinarith [hCrossAvg i]
  have hPavg (i : ι) : 0 ≤ Pavg i :=
    old_signed_cell_average_nonneg Q depth (Pcell i) (hPcell i)
  have hRavg (i : ι) : 0 ≤ Ravg i :=
    old_signed_cell_average_nonneg Q depth (Rcell i) (hRcell i)
  have hsumCell :
      (∑ i ∈ S, Bavg i) ≤
        (∑ i ∈ S, Pavg i) + (∑ i ∈ S, Ravg i) +
          2 * (∑ i ∈ S, Real.sqrt (Pavg i) * Real.sqrt (Ravg i)) := by
    have hs := Finset.sum_le_sum (s := S) (fun i _ => hBavg i)
    simpa only [Finset.sum_add_distrib, ← Finset.mul_sum] using hs
  have hsumRoot := Real.sum_sqrt_mul_sqrt_le (s := S)
    (f := Pavg) (g := Ravg) hPavg hRavg
  have hPnonneg : 0 ≤ ∑ i ∈ S, Pavg i := Finset.sum_nonneg (fun i _ => hPavg i)
  have hRnonneg : 0 ≤ ∑ i ∈ S, Ravg i := Finset.sum_nonneg (fun i _ => hRavg i)
  have hProot : Real.sqrt (∑ i ∈ S, Pavg i) ^ 2 = ∑ i ∈ S, Pavg i :=
    Real.sq_sqrt hPnonneg
  have hRroot : Real.sqrt (∑ i ∈ S, Ravg i) ^ 2 = ∑ i ∈ S, Ravg i :=
    Real.sq_sqrt hRnonneg
  have hsumCell' :
      (∑ i ∈ S, Bavg i) ≤
        (∑ i ∈ S, Pavg i) + (∑ i ∈ S, Ravg i) +
          2 * (Real.sqrt (∑ i ∈ S, Pavg i) * Real.sqrt (∑ i ∈ S, Ravg i)) := by
    calc
      _ ≤ _ := hsumCell
      _ ≤ _ := by nlinarith [hsumRoot]
  change (∑ i ∈ S, Bavg i) ≤ _
  nlinarith [hsumCell', hProot, hRroot]

end

end ASDExplicitGamma.Scalar
