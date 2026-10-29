module

public import ASDExplicitGamma.Inverse.BankHistoryPhysical
public import ASDExplicitGamma.Inverse.BankLocal
public import ASDExplicitGamma.Inverse.ClippedMatrixLocal
public import ASDExplicitGamma.Model.CutoffGaussian
public import ASDExplicitGamma.Gaussian.ModelHeatTrace
public import ASDExplicitGamma.Variational.TraceDefect
public import ASDExplicitGamma.Native.HeatVHEATRefinedVectorD4

/-! The OLD local inverse profile at the refined cutoff `m + 1` for children of
scale `m`, using the depth-four local roots (scale spread five). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Inverse ASDExplicitGamma.Model
open ASDExplicitGamma.Variational
open scoped ENNReal

set_option linter.constructorNameAsVariable false

theorem nativeHeatRootsR_scale (Q U : TriadicCube 2) (R : ℕ)
    (hU : U ∈ bankLocalRoots Q R) : U.scale ≤ Q.scale ∧ Q.scale - U.scale ≤ R := by
  rw [bankLocalRoots] at hU
  rcases Finset.mem_insert.mp hU with rfl | hU
  · exact ⟨le_rfl, by omega⟩
  obtain ⟨r, hr', hU⟩ := Finset.mem_biUnion.mp hU
  have hs := scale_eq_sub_of_mem_descendantsAtDepth hU
  have hrr := Finset.mem_range.mp hr'
  omega

/-- Native states strictly below the cutoff `m` give the actual OLD local bank
for a child of scale `m - 1`: its trace defect in the frame `sigmaBar m` has the
baseline-plus-rare profile, with measurable nonnegative depth-four remainder. -/
theorem nativeHeatOldInverseTraceProfileD4_of_states
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (Q : TriadicCube 2) (m : ℤ)
    (hscale : Q.scale + 1 = m)
    (hpast : ∀ n < m, nativeInductionState M h n) :
    Measurable (nativeHeatOldInverseRemainderD4 M Q m) ∧
      (∀ ω, 0 ≤ nativeHeatOldInverseRemainderD4 M Q m ω) ∧
      (∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
        Matrix.trace (frameMatrix (Annealed.sigmaBar M m : ℝ)
          (coarseBlockMatrix (cubeSet Q)
            (Cutoff.coefficientCutoff M.nu m ω).toFun)).lowerRight ≤
          2 * ((inverseBankCap .localInverse : ℝ) +
            nativeHeatOldInverseRemainderD4 M Q m ω)) ∧
      True := by
  let s := bankLocalRoots Q 4
  let w : ℤ → ℝ := fun _ => 0
  have hgeom := bank_local_roots_geometry Q 4 (by norm_num)
  have hscaleRoots : ∀ U ∈ s, U.scale ≤ m ∧ m - U.scale ≤ 5 := by
    intro U hU
    have hU' := nativeHeatRootsR_scale Q U 4 hU
    omega
  have hweights : ∀ k ∈ Finset.Ioc m (m + 1), 0 ≤ w k ∧ w k ≤ 1 := by
    intro k hk
    simp [w]
  have hmeans := bank_inverse_mean_inputs_of_states M h hM hg m hpast
  have hbank : InverseBankConclusion M .localInverse s m (m + 1) w :=
    local_inverse_bank M h hM hg s m (m + 1) (by omega) w hweights
      hscaleRoots hgeom.2 hpast hmeans.2
  have hQ : Q ∈ s := by
    exact bank_local_roots_self Q 4
  have hcap : 0 ≤ (inverseBankCap .localInverse : ℝ) := by
    norm_num [inverseBankCap]
  have hCoeff (ω : Cutoff.CutoffSample 2) :
      attenuatedCoefficient M m (m + 1) w ω =
        (partialInsertedCoefficient M m 0 ω).toFun := by
    funext x
    simp [attenuatedCoefficient, w, partialInsertedCoefficient]
  have hresponse : ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      rootInverseResponse M Q m (m + 1) w ω ≤
        (inverseBankCap .localInverse : ℝ) + nativeHeatOldInverseRemainderD4 M Q m ω := by
    filter_upwards [hbank.history_le] with ω hsplit
    obtain ⟨ell, hK⟩ := Gaussian.exists_originCube_containing_compact _
      (isBounded_cubeSet Q).isCompact_closure
    have hEllPartial : IsEllipticFieldOn M.nu
        (((2 : ℝ) * 2 * (partialInsertedEntryBound M ell m ω) ^ 2 + M.nu ^ 2) / M.nu)
        (openCubeSet Q) (partialInsertedCoefficient M m 0 ω) :=
      partialInsertedCoefficient_isEllipticFieldOn M ell m ω
        (by norm_num) (measurableSet_openCubeSet Q)
        (fun x hx => hK (subset_closure (openCubeSet_subset_cubeSet Q hx)))
    have hEll : IsEllipticFieldOn M.nu
        (((2 : ℝ) * 2 * (partialInsertedEntryBound M ell m ω) ^ 2 + M.nu ^ 2) / M.nu)
        (openCubeSet Q) (attenuatedCoefficient M m (m + 1) w ω) := by
      simpa only [hCoeff ω] using hEllPartial
    have hroot := bank_root_response_le_history Q M m (m + 1) w ω hEll
    have hmember := bank_member_history_le M s Q hQ m (m + 1) w ω
    have hENN : ENNReal.ofReal
        (rootInverseResponse M Q m (m + 1) w ω) ≤
          ENNReal.ofReal (inverseBankCap .localInverse : ℝ) +
            ENNReal.ofReal (nativeHeatOldInverseRemainderD4 M Q m ω) :=
      hroot.trans (hmember.trans (by simpa [s, w, nativeHeatOldInverseRemainderD4] using hsplit))
    have hrem0 : 0 ≤ nativeHeatOldInverseRemainderD4 M Q m ω :=
      hbank.remainder_nonneg ω
    have hupper : ENNReal.ofReal (inverseBankCap .localInverse : ℝ) +
        ENNReal.ofReal (nativeHeatOldInverseRemainderD4 M Q m ω) =
          ENNReal.ofReal ((inverseBankCap .localInverse : ℝ) +
            nativeHeatOldInverseRemainderD4 M Q m ω) :=
      (ENNReal.ofReal_add hcap hrem0).symm
    have hENN' : ENNReal.ofReal
        (rootInverseResponse M Q m (m + 1) w ω) ≤
          ENNReal.ofReal ((inverseBankCap .localInverse : ℝ) +
            nativeHeatOldInverseRemainderD4 M Q m ω) := hENN.trans_eq hupper
    have hreal := ENNReal.toReal_mono
      (ENNReal.ofReal_ne_top : ENNReal.ofReal
        ((inverseBankCap .localInverse : ℝ) + nativeHeatOldInverseRemainderD4 M Q m ω) ≠ ∞)
      hENN'
    have hresponse0 : 0 ≤ rootInverseResponse M Q m (m + 1) w ω :=
      mul_nonneg (Annealed.sigmaBar_characterization M m).1.le (norm_nonneg _)
    rw [ENNReal.toReal_ofReal hresponse0,
      ENNReal.toReal_ofReal (add_nonneg hcap hrem0)] at hreal
    exact hreal
  have htrace : ∀ ω,
      Matrix.trace (frameMatrix (Annealed.sigmaBar M m : ℝ)
        (coarseBlockMatrix (cubeSet Q)
          (Cutoff.coefficientCutoff M.nu m ω).toFun)).lowerRight ≤
        2 * rootInverseResponse M Q m (m + 1) w ω := by
    intro ω
    let A := (coarseBlockMatrix (cubeSet Q)
      (attenuatedCoefficient M m (m + 1) w ω)).lowerRight
    have h0 := (le_abs_self (A 0 0)).trans (clipped_matrix_entry_abs_le_norm A 0 0)
    have h1 := (le_abs_self (A 1 1)).trans (clipped_matrix_entry_abs_le_norm A 1 1)
    have hσ := (Annealed.sigmaBar_characterization M m).1.le
    have hh := add_le_add
      (mul_le_mul_of_nonneg_left h0 hσ)
      (mul_le_mul_of_nonneg_left h1 hσ)
    have hpart : (partialInsertedCoefficient M m 0 ω).toFun =
        (Cutoff.coefficientCutoff M.nu m ω).toFun := by
      funext x
      simp [partialInsertedCoefficient]
    have hA : A = (coarseBlockMatrix (cubeSet Q)
        (Cutoff.coefficientCutoff M.nu m ω).toFun).lowerRight := by
      change (coarseBlockMatrix (cubeSet Q)
        (attenuatedCoefficient M m (m + 1) w ω)).lowerRight = _
      rw [hCoeff ω, hpart]
    calc
      Matrix.trace (frameMatrix (Annealed.sigmaBar M m : ℝ)
          (coarseBlockMatrix (cubeSet Q)
            (Cutoff.coefficientCutoff M.nu m ω).toFun)).lowerRight
          = (Annealed.sigmaBar M m : ℝ) * A 0 0 +
              (Annealed.sigmaBar M m : ℝ) * A 1 1 := by
                simp [frameMatrix, Matrix.trace, Fin.sum_univ_two, A, hA]
      _ ≤ 2 * ((Annealed.sigmaBar M m : ℝ) *
          ‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) A‖) := by
            nlinarith only [hh]
      _ = 2 * rootInverseResponse M Q m (m + 1) w ω := by
            simp [rootInverseResponse, A]
  refine ⟨?_, ?_, ?_, ?_⟩
  · change Measurable
      (inverseBankPopulationRemainder .localInverse (bankLocalRoots Q 4) M m (m + 1)
        (fun _ => 0))
    exact hbank.remainder_measurable
  · intro ω
    simpa [nativeHeatOldInverseRemainderD4, s, w] using hbank.remainder_nonneg ω
  · filter_upwards [hresponse] with ω hω
    have hr0 : 0 ≤ nativeHeatOldInverseRemainderD4 M Q m ω :=
      hbank.remainder_nonneg ω
    calc
      _ ≤ 2 * rootInverseResponse M Q m (m + 1) w ω := htrace ω
      _ ≤ 2 * ((inverseBankCap .localInverse : ℝ) +
          nativeHeatOldInverseRemainderD4 M Q m ω) := by
            exact mul_le_mul_of_nonneg_left hω (by norm_num)
  · trivial

end ASDExplicitGamma.Native
