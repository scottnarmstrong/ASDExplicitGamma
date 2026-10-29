module

public import ASDExplicitGamma.Native.ParentRowErrorExpectation
public import ASDExplicitGamma.Native.ParentBoundaryDirectionalModel
public import ASDExplicitGamma.Native.OldSignedQ1OneShellExpectation
public import ASDExplicitGamma.Native.ParentBoundaryBandAffineBill

/-! The actual simultaneous parent generator with its signed inverse term. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Gaussian Inverse Main Triadic Variational Algsuperdiff.Section3
noncomputable section

/-- The open-cube inverse trace equals the actual fixed-frame observable
at every height, before averaging the sample law. -/
theorem parent_row_inverse_observable (M : ABKModel 2) (n : ℤ)
    (height : ℕ) (t : ℝ) (ω : Cutoff.CutoffSample 2) :
    Matrix.trace (coarseBlockMatrix (openCubeSet (originCube 2 n))
      (parentBoundaryBandFrameField M n height t ω)).lowerRight=
      mainInverseObservable n M.nu (Annealed.sigmaBar M n) (nativeSourceBandScalar n height t ω) := by
  unfold parentBoundaryBandFrameField
  rw [old_signed_open_coarse_frame' n M.nu (Annealed.sigmaBar M n) M.nu_pos
    (Annealed.sigmaBar_characterization M n).1]
  simp only [frameMatrix,mainInverseObservable,Matrix.trace_smul,smul_eq_mul]

/-- Finite-shell actual-law error envelope in the starting true frame. -/
def parentRowBandErrorEnvelope (M : ABKModel 2) (h : ℝ) (n : ℤ) (height r : ℕ)
    (t : ℝ) (ω : Cutoff.CutoffSample 2) : ℝ :=
  ∑ i : Fin height,parentRowErrorEnvelope M n height r t
    (q3ModelAmplitude M h (n+((i.val+1:ℕ):ℤ))/(Annealed.sigmaBar M n:ℝ))
    (q3ModelLength (n+((i.val+1:ℕ):ℤ))) ω

/-- The literal parent generator is paid by its affine bill and error
majorant. The signed inverse deficit retains the exact complete Y coefficient. -/
theorem parent_row_generator_spatial
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (n : ℤ) (height r : ℕ) (hr : r≤5)
    (hpast : ∀ l<n,nativeInductionState M h l) (t : ℝ) (ht : 0≤t ∧ t≤1) :
    ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      nativeSourceBandMeanGenerator M h n height t ω≤
        (∑ i : Fin height,oldSignedFlatBoundaryEnergy (originCube 2 n)
          (q3ModelAmplitude M h (n+((i.val+1:ℕ):ℤ))/(Annealed.sigmaBar M n:ℝ))
          (q3ModelLength (n+((i.val+1:ℕ):ℤ))))+
        parentBoundaryBandAffineBill M h n height r t ω-
        parentBoundaryBandDirichletEnergy M h n height*
          (mainInverseObservable n M.nu (Annealed.sigmaBar M n) (nativeSourceBandScalar n height t ω)-2)+
        parentRowBandErrorEnvelope M h n height r t ω := by
  let Q := originCube 2 n
  let b := fun i : Fin height => q3ModelAmplitude M h (n+((i.val+1:ℕ):ℤ))/(Annealed.sigmaBar M n:ℝ)
  let L := fun i : Fin height => q3ModelLength (n+((i.val+1:ℕ):ℤ))
  have he (i : Fin height) := parent_row_actual_error_spatial_majorant M h hM hg n height hpast r hr t ht (b i) (L i)
  filter_upwards [ae_all_iff.mpr he] with ω hω
  have hh (i : Fin height) := parent_boundary_directional_model_generator n r M.nu
    (Annealed.sigmaBar M n) M.nu_pos (Annealed.sigmaBar_characterization M n).1
    (nativeSourceBandScalar n height t ω) (b i) (L i)
  have hs (i : Fin height) : (Annealed.sigmaBar M n:ℝ)*b i=
      q3ModelAmplitude M h (n+((i.val+1:ℕ):ℤ)) := by
    dsimp only [b]
    field_simp [(Annealed.sigmaBar_characterization M n).1.ne']
  have hi (i : Fin height) := (hh i).trans (add_le_add le_rfl (hω i))
  simp only [hs] at hi
  change ∀ i : Fin height, _≤oldSignedFlatBoundaryEnergy Q (b i) (L i)+
    oldSignedFlatAffineContribution Q r (parentBoundaryBandFrameField M n height t ω) (b i) (L i)-
    parentBoundaryDirichletEnergy Q (b i) (L i)*
      (Matrix.trace (coarseBlockMatrix (openCubeSet Q) (parentBoundaryBandFrameField M n height t ω)).lowerRight-2)+
    parentRowErrorEnvelope M n height r t (b i) (L i) ω at hi
  rw [parent_row_inverse_observable] at hi
  have hsum := Finset.sum_le_sum (fun i (_ : i∈(Finset.univ : Finset (Fin height))) => hi i)
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,←Finset.sum_mul] at hsum
  exact hsum

end
end ASDExplicitGamma.Native
