module

public import ASDExplicitGamma.Main.ObsLowerTwoLoad
public import ASDExplicitGamma.Main.ObsLowerTraceBridge
public import ASDExplicitGamma.Main.HotPatchBank
public import ASDExplicitGamma.Scalar.FlatSourceQ3ActualBank
public import ASDExplicitGamma.Inverse.PureFluxGeneratorBankLoads

/-! (A): the pathwise inverse-trace lower generator at every main-range observer
`Q = originCube 2 (m + hobs)`, `hobs ≤ 40`: with frame `σ̄_m`, shell `m+1`, `v = (b/σ̄_m)^2`,
`B* = mixedBridgeBstar`. The coercivity is the source (1.2) through the cell history `B*`
and no ellipticity constant. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Homogenization MeasureTheory ASDExplicitGamma.Gaussian ASDExplicitGamma.Inverse
  ASDExplicitGamma.Response ASDExplicitGamma.Triadic ASDExplicitGamma.Variational
  ASDExplicitGamma.Model ASDExplicitGamma.Native ASDExplicitGamma.Scalar
open Algsuperdiff.Section3
open scoped BigOperators

/-- Pathwise lower generator row at the observer `originCube 2 (m + hobs)`. -/
theorem main_observer_q3_inverse_trace_lower_pathwise
    (M : ABKModel 2) (h : ℝ) (m : ℤ) (hobs : ℕ) (h40 : hobs ≤ 40)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) (ω : Cutoff.CutoffSample 2) :
    let Q := originCube 2 (m + hobs)
    let σ := (Annealed.sigmaBar M m : ℝ)
    let x := modelInsertedScalar (closure (cubeSet Q)) m t ω
    let amp := q3ModelAmplitude M h (m + 1)
    let L := q3ModelLength (m + 1)
    (1 / 2 : ℝ) * modelCovarianceTrace (mainInverseObservable (m + hobs) M.nu σ)
        (pureFluxMainCubeQ3Directions (m + hobs) amp L) x ≥
      -(mainInverseMuMinusSource ((amp / σ) ^ 2) * (max 1 (mixedBridgeBstar M m t ω)) ^ 2 *
        mainInverseObservable (m + hobs) M.nu σ x) := by
  classical
  intro Q σ x amp L
  have hσ : 0 < σ := (Annealed.sigmaBar_characterization M m).1
  let hU := measurableSet_openCubeSet Q
  let hvol := volume_openCubeSet_originCube_toReal_pos (d := 2) (m + hobs)
  let k := pureFluxOpenResponseRestriction (m + hobs) x
  let B := mixedBridgeBstar M m t ω
  have hB : 0 ≤ B := mixed_bridge_bstar_nonneg M m t ω
  have hhist : ∀ U ∈ descendantsAtDepth Q (hobs + 5),
      lemmaVInverseHistory U (responseFramePlanarCoefficientField M.nu σ k)
        ((3 : ℝ) ^ (1 / 4 : ℝ)) ≤ B := by
    intro U hU'
    exact hot_cell_history_le_bstar M m hobs h40 t ht ω U hU'
  have hEll := responseFramePlanarCoefficientField_isElliptic
    (measurableSet_openCubeSet Q) M.nu σ M.nu_pos hσ k
  let P : Fin 2 → BlockVec 2 := fun i => (0, Pi.single i 1)
  have hmins (i : Fin 2) := lemmaV_minimizer_pair (m + hobs) hEll (P i)
  choose r' u' w' hrep hgrad hEv hEu using hmins
  rw [lemmaV_responseSystem_eq_canonical hU hvol
    M.nu σ M.nu_pos hσ k] at hrep hEv hEu
  have hrow := obs_twoLoad_trace_lower_source_root m hobs M.nu σ amp B M.nu_pos hσ k P
    r' u' w' hrep hgrad hB hhist
  dsimp only at hrow
  let E (i : Fin 2) := responseFrameEnergyObservable hU hvol M.nu σ M.nu_pos hσ (P i)
  have hbridge := obs_response_trace_eq_inverse_trace (m + hobs) M.nu σ amp M.nu_pos hσ L x
  dsimp only at hbridge
  have hE (i : Fin 2) : E i k = σ * (coarseBlockMatrix (cubeSet Q)
      (responsePlanarCoefficientField M.nu
        (ContinuousMap.linearIsometryBoundedOfCompact (closure (cubeSet Q)) ℝ ℝ x))).lowerRight i i := by
    simpa only [E, hU, hvol, P, Q, k, pureFluxBankLoadEnergy] using
      pureFlux_bank_load_energy_eq (m + hobs) M.nu σ M.nu_pos hσ x i
  have hsum : (∑ i : Fin 2, E i k) = mainInverseObservable (m + hobs) M.nu σ x := by
    calc
      (∑ i : Fin 2, E i k) =
          ∑ i : Fin 2, σ * (coarseBlockMatrix (cubeSet Q)
            (responsePlanarCoefficientField M.nu
              (ContinuousMap.linearIsometryBoundedOfCompact
                (closure (cubeSet Q)) ℝ ℝ x))).lowerRight i i :=
        Finset.sum_congr rfl fun i _ => hE i
      _ = σ * Matrix.trace (coarseBlockMatrix (cubeSet Q)
          (responsePlanarCoefficientField M.nu
            (ContinuousMap.linearIsometryBoundedOfCompact
              (closure (cubeSet Q)) ℝ ℝ x))).lowerRight := by
        rw [← Finset.mul_sum]
        rfl
      _ = mainInverseObservable (m + hobs) M.nu σ x := by rfl
  have hv : (|σ⁻¹| * |amp|) ^ 2 = (amp / σ) ^ 2 := by
    rw [← abs_mul, sq_abs, div_eq_inv_mul]
  rw [hv] at hrow
  rw [← hsum, ← hbridge]
  exact hrow

/-- (A) in the interface shape consumed by `main_inverse_heat_absolute_branch_of_generator_bound`:
for every `t` the pathwise row holds almost surely (in fact for every sample). -/
theorem main_observer_q3_inverse_trace_lower_ae
    (M : ABKModel 2) (h : ℝ) (m : ℤ) (hobs : ℕ) (h40 : hobs ≤ 40)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    let Q := originCube 2 (m + hobs)
    let σ := (Annealed.sigmaBar M m : ℝ)
    let x := modelInsertedScalar (closure (cubeSet Q)) m t
    let amp := q3ModelAmplitude M h (m + 1)
    let L := q3ModelLength (m + 1)
    ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      (1 / 2 : ℝ) * modelCovarianceTrace (mainInverseObservable (m + hobs) M.nu σ)
          (pureFluxMainCubeQ3Directions (m + hobs) amp L) (x ω) ≥
        -(mainInverseMuMinusSource ((amp / σ) ^ 2) * (max 1 (mixedBridgeBstar M m t ω)) ^ 2 *
          mainInverseObservable (m + hobs) M.nu σ (x ω)) :=
  Filter.Eventually.of_forall fun ω =>
    main_observer_q3_inverse_trace_lower_pathwise M h m hobs h40 t ht ω

end ASDExplicitGamma.Main
