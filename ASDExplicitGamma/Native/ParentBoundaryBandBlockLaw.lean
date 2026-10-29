module

public import ASDExplicitGamma.Native.ParentBoundaryBandHalfTrace
public import ASDExplicitGamma.Variational.AdapterDuality

/-! Individual positive diagonal-block laws for the signed affine payment.
Only the positive matrices are averaged; their deviations may have either sign. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Inverse Algsuperdiff.Section3
noncomputable section

/-- A literal normalized diagonal block of the actual band response. -/
def parentBoundaryBandNormalizedBlock (M : ABKModel 2) (n : ℤ) (height : ℕ)
    (t : ℝ) (U : TriadicCube 2) (plus : Bool) (omega : Cutoff.CutoffSample 2) : Mat 2 :=
  let A := frameMatrix (Annealed.sigmaBar M n) (coarseBlockMatrix (cubeSet U)
    (attenuatedCoefficient M n (n+(height:ℤ)) (fun _ => Real.sqrt t) omega))
  if plus then A.upperLeft else A.lowerRight

/-- Both actual diagonal blocks are positive in every load direction. -/
theorem parent_boundary_band_block_nonneg (M : ABKModel 2) (n : ℤ) (height : ℕ)
    (t : ℝ) (U : TriadicCube 2) (plus : Bool) (omega : Cutoff.CutoffSample 2) (e : Vec 2) :
    0≤vecDot e (matVecMul (parentBoundaryBandNormalizedBlock M n height t U plus omega) e) := by
  obtain ⟨Lam,_,hEll⟩ := parent_boundary_band_elliptic_cube M n (n+(height:ℤ))
    (fun _ => Real.sqrt t) omega U
  have hp := coarse_energy_ge_abs_pairing M.nu_pos hEll (e,0)
  have hm := coarse_energy_ge_abs_pairing M.nu_pos hEll (0,e)
  have hs := (Annealed.sigmaBar_characterization M n).1.le
  cases plus
  · have hnonneg : 0≤vecDot e (matVecMul (coarseBlockMatrix (cubeSet U)
        (attenuatedCoefficient M n (n+(height:ℤ)) (fun _ => Real.sqrt t) omega)).lowerRight e) := by
      simpa [blockVecDot,blockMatVecMul,vecDot,matVecMul,Fin.sum_univ_two] using hm
    convert mul_nonneg hs hnonneg using 1
    simp [parentBoundaryBandNormalizedBlock,frameMatrix,vecDot,matVecMul,Fin.sum_univ_two]
    ring
  · have hnonneg : 0≤vecDot e (matVecMul (coarseBlockMatrix (cubeSet U)
        (attenuatedCoefficient M n (n+(height:ℤ)) (fun _ => Real.sqrt t) omega)).upperLeft e) := by
      simpa [blockVecDot,blockMatVecMul,vecDot,matVecMul,Fin.sum_univ_two] using hp
    convert mul_nonneg (inv_nonneg.mpr hs) hnonneg using 1
    simp [parentBoundaryBandNormalizedBlock,frameMatrix,vecDot,matVecMul,Fin.sum_univ_two]
    ring

/-- The expected individual block is a nonnegative scalar matrix, with
all entry integrability proved for the actual source-cell law. -/
theorem parent_boundary_band_block_scalar_law
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (n : ℤ)
    (height : ℕ) (hheight : 1≤height) (r : ℕ) (U : TriadicCube 2)
    (hU : U∈descendantsAtDepth (originCube 2 n) r) (t : ℝ) (plus : Bool) :
    let A := parentBoundaryBandNormalizedBlock M n height t U plus
    (∀ i j,Integrable (fun omega => A omega i j) (Cutoff.cutoffSampleLaw M).toMeasure) ∧
    ∃ c : ℝ,0≤c ∧ ∀ i j,(∫ omega,A omega i j ∂(Cutoff.cutoffSampleLaw M).toMeasure)=
      if i=j then c else 0 := by
  intro A
  have hint (i j) : Integrable (fun omega => A omega i j) (Cutoff.cutoffSampleLaw M).toMeasure := by
    cases plus
    · exact (parent_boundary_band_cell_entry_memLp M h hM n height hheight r U hU
        (.inr i) (.inr j) t 2 (by norm_num)).integrable (by norm_num)
    · exact (parent_boundary_band_cell_entry_memLp M h hM n height hheight r U hU
        (.inl i) (.inl j) t 2 (by norm_num)).integrable (by norm_num)
  obtain ⟨c,hc⟩ := parent_boundary_band_expected_cell_block M n (n+(height:ℤ))
    (fun _ => Real.sqrt t) U plus
  let d : ℝ := if plus then (Annealed.sigmaBar M n:ℝ)⁻¹ else (Annealed.sigmaBar M n:ℝ)
  have hm (i j) : (∫ omega,A omega i j ∂(Cutoff.cutoffSampleLaw M).toMeasure)=if i=j then d*c else 0 := by
    have he (omega) : A omega i j=d*parentBoundaryBandDiagonalBlock M n (n+(height:ℤ))
        (fun _ => Real.sqrt t) U plus omega i j := by
      cases plus <;> rfl
    simp_rw [he]
    rw [integral_const_mul,hc]
    split_ifs <;> simp
  refine ⟨hint,d*c,?_,hm⟩
  have hn : 0≤∫ omega,A omega 0 0 ∂(Cutoff.cutoffSampleLaw M).toMeasure := by
    apply integral_nonneg
    intro omega
    have hh := parent_boundary_band_block_nonneg M n height t U plus omega (basisVec 0)
    simpa [vecDot,matVecMul,basisVec,Fin.sum_univ_two] using hh
  simpa only [hm,ite_true] using hn

/-- The literal expected diagonal coefficient in the unchanged starting frame. -/
def parentBoundaryBandBlockMean (M : ABKModel 2) (n : ℤ) (height : ℕ)
    (t : ℝ) (U : TriadicCube 2) (plus : Bool) : ℝ :=
  ∫ omega,parentBoundaryBandNormalizedBlock M n height t U plus omega 0 0
    ∂(Cutoff.cutoffSampleLaw M).toMeasure

/-- The scalar coefficient is the actual expected diagonal entry. -/
theorem parent_boundary_band_block_mean
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (n : ℤ)
    (height : ℕ) (hheight : 1≤height) (r : ℕ) (U : TriadicCube 2)
    (hU : U∈descendantsAtDepth (originCube 2 n) r) (t : ℝ) (plus : Bool) :
    0≤parentBoundaryBandBlockMean M n height t U plus ∧
    ∀ i j,(∫ omega,parentBoundaryBandNormalizedBlock M n height t U plus omega i j
      ∂(Cutoff.cutoffSampleLaw M).toMeasure)=
      if i=j then parentBoundaryBandBlockMean M n height t U plus else 0 := by
  obtain ⟨_,c,hc,hm⟩ := parent_boundary_band_block_scalar_law M h hM n height hheight r U hU t plus
  have he : parentBoundaryBandBlockMean M n height t U plus=c := by
    simpa only [parentBoundaryBandBlockMean,ite_true] using hm 0 0
  rw [he]
  exact ⟨hc,hm⟩

end
end ASDExplicitGamma.Native
