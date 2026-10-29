module

public import ASDExplicitGamma.Native.ParentBoundaryModelScales
public import ASDExplicitGamma.Native.ParentBoundaryPlusMean
public import ASDExplicitGamma.Native.GenericSourceShellBudget

/-! Actual finite-band flat energy and summable own-native inverse clock. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Algsuperdiff.Section3 Response Scalar Gaussian Main Triadic
noncomputable section

/-- Full fresh point variance in the fixed starting true frame. -/
def parentBoundaryBandVariance (M : ABKModel 2) (h : ℝ) (n : ℤ) (height : ℕ) : ℝ :=
  ∑ i : Fin height,(q3ModelAmplitude M h (n+((i.val+1:ℕ):ℤ))/(Annealed.sigmaBar M n:ℝ))^2

/-- Literal complete Dirichlet energy of every fresh shell in the band. -/
def parentBoundaryBandDirichletEnergy (M : ABKModel 2) (h : ℝ) (n : ℤ) (height : ℕ) : ℝ :=
  ∑ i : Fin height,parentBoundaryDirichletEnergy (originCube 2 n)
    (q3ModelAmplitude M h (n+((i.val+1:ℕ):ℤ))/(Annealed.sigmaBar M n:ℝ))
    (q3ModelLength (n+((i.val+1:ℕ):ℤ)))

/-- The full physical variance and the smaller Dirichlet energy are
nonnegative; the latter never exceeds the former. -/
theorem parent_boundary_band_energy_bounds (M : ABKModel 2) (h : ℝ) (n : ℤ) (height : ℕ) :
    0≤parentBoundaryBandDirichletEnergy M h n height ∧
    parentBoundaryBandDirichletEnergy M h n height≤parentBoundaryBandVariance M h n height := by
  constructor
  · exact Finset.sum_nonneg (fun i _ => (parent_boundary_dirichlet_energy_bounds _ _ _).1)
  · exact Finset.sum_le_sum (fun i _ => (parent_boundary_dirichlet_energy_bounds _ _ _).2)

/-- The actual full variance obeys the finite source-program shell sum;
each shell keeps its own exact exponential height. -/
theorem parent_boundary_band_variance_clock (M : ABKModel 2) (h : ℝ) (n : ℤ)
    (height : ℕ) (hstate : nativeInductionState M h n) :
    parentBoundaryBandVariance M h n height≤
      ∑ i : Fin height,nativeSourceShellClock M.gamma (i.val+1) := by
  apply Finset.sum_le_sum
  intro i _
  simpa only [div_pow] using native_source_shell_variance_le_clock M h n (i.val+1) (i.val+1) hstate le_rfl

/-- The literal flat baseline of the band remains 2v-2Y. -/
theorem parent_boundary_band_flat_baseline (M : ABKModel 2) (h : ℝ) (n : ℤ) (height : ℕ) :
    (∑ i : Fin height,oldSignedFlatBoundaryEnergy (originCube 2 n)
      (q3ModelAmplitude M h (n+((i.val+1:ℕ):ℤ))/(Annealed.sigmaBar M n:ℝ))
      (q3ModelLength (n+((i.val+1:ℕ):ℤ)))) =
      2*parentBoundaryBandVariance M h n height-2*parentBoundaryBandDirichletEnergy M h n height := by
  have he (i : Fin height) := (parent_boundary_flat_baseline (originCube 2 n)
    (q3ModelAmplitude M h (n+((i.val+1:ℕ):ℤ))/(Annealed.sigmaBar M n:ℝ))
    (q3ModelLength (n+((i.val+1:ℕ):ℤ)))).1
  simp_rw [he]
  simp only [Finset.sum_sub_distrib,←Finset.mul_sum,parentBoundaryBandVariance,parentBoundaryBandDirichletEnergy]

end
end ASDExplicitGamma.Native
