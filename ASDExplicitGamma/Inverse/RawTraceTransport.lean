module

public import ASDExplicitGamma.Inverse.RawTraceBandTransport
public import ASDExplicitGamma.Inverse.RawShellBandTransport
public import ASDExplicitGamma.Numerics.Inverse.Scalars

/-! The depth profile and complete rare-reserve arithmetic following the raw
finite-band shell-transport conclusion. -/
@[expose] public section

namespace ASDExplicitGamma.Inverse

open Homogenization Algsuperdiff.Section3 MeasureTheory
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Response ASDExplicitGamma.Variational
open ASDExplicitGamma.Numerics.Inverse
open scoped ENNReal

noncomputable section

/-- The padded band uses all shells through `m`, the attenuated shell
at `m+1`, and zero weights after that terminal insertion. -/
noncomputable def rawTraceTransportWeights (m : ℤ) (t : ℝ) : ℤ → ℝ :=
  fun k => if k ≤ m then 1 else if k = m + 1 then Real.sqrt t else 0

/-- Reconstruct the exact p=20 shell premise from the actual depth-indexed
native states and the padded weights. This is the common source
adapter used by the four node instantiations. -/
theorem raw_trace_transport_shell_p20_from_depth_states
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (m : ℤ) (r : ℕ) (j : ℕ) (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hstate : ∀ q : ℕ,
      nativeInductionState M h (m - (r : ℤ) - (q : ℤ))) :
    eLpNorm
        (fun ω => modelTraceObservable (m - (r : ℤ) - (j : ℤ)) M.nu
          (Annealed.sigmaBar M (m - (r : ℤ) - (j : ℤ)) : ℝ)
          (rawShellBandScalarFromWeights M
            (m - (r : ℤ) - (j : ℤ)) (134 + j)
            (rawTraceTransportWeights m t) ω))
        (ENNReal.ofReal 20) (Cutoff.cutoffSampleLaw M).toMeasure ≤
      eLpNorm
        (fun ω => modelTraceObservable (m - (r : ℤ) - (j : ℤ)) M.nu
          (Annealed.sigmaBar M (m - (r : ℤ) - (j : ℤ)) : ℝ)
          (olderField
            (closure (cubeSet (originCube 2 (m - (r : ℤ) - (j : ℤ)))))
            (m - (r : ℤ) - (j : ℤ)) ω))
        (ENNReal.ofReal 20) (Cutoff.cutoffSampleLaw M).toMeasure +
      ENNReal.ofReal (rawTraceBandShellIncrement M.gamma (134 + j)) := by
  let n : ℤ := m - (r : ℤ) - (j : ℤ)
  let N : ℕ := 134 + j
  let weights : ℤ → ℝ := rawTraceTransportWeights m t
  have hN : 1 ≤ N := by dsimp [N]; omega
  have hAnchor : nativeInductionState M h n := by
    simpa [n] using hstate j
  have hPastLocal : ∀ k < n, nativeInductionState M h k := by
    intro k hk
    let q : ℕ := (m - (r : ℤ) - k).toNat
    have hqNonneg : 0 ≤ m - (r : ℤ) - k := by
      dsimp [n] at hk
      omega
    have hqCast : (q : ℤ) = m - (r : ℤ) - k := by
      dsimp [q]
      exact Int.toNat_of_nonneg hqNonneg
    have hindex : m - (r : ℤ) - (q : ℤ) = k := by omega
    simpa [hindex] using hstate q
  have hPastFull : ∀ k ≤ n + (N : ℤ) - 303,
      nativeInductionState M h k := by
    have hend : n + (N : ℤ) - 303 = m - (r : ℤ) - 169 := by
      dsimp [n, N]
      omega
    intro k hk
    rw [hend] at hk
    let q : ℕ := (m - (r : ℤ) - k).toNat
    have hqNonneg : 0 ≤ m - (r : ℤ) - k := by omega
    have hqCast : (q : ℤ) = m - (r : ℤ) - k := by
      dsimp [q]
      exact Int.toNat_of_nonneg hqNonneg
    have hindex : m - (r : ℤ) - (q : ℤ) = k := by omega
    simpa [hindex] using hstate q
  have hweights : ∀ k ∈ Finset.Ioc n (n + (N : ℤ)),
      0 ≤ weights k ∧ weights k ≤ 1 := by
    intro k hk
    by_cases hkm : k ≤ m
    · simp [weights, rawTraceTransportWeights, hkm]
    · by_cases hkm1 : k = m + 1
      · subst k
        constructor
        · simpa [weights, rawTraceTransportWeights, hkm] using
            (Real.sqrt_nonneg t)
        · simpa [weights, rawTraceTransportWeights, hkm] using
            (Real.sqrt_le_one.mpr ht.2)
      · simp [weights, rawTraceTransportWeights, hkm, hkm1]
  have hraw := raw_shell_band_transport_p20 M h hM hγ n N hN
    hAnchor hPastLocal hPastFull weights hweights
  simpa [n, N, weights, rawTraceTransportWeights,
    rawTraceBandShellIncrement] using hraw.1

/-- The origin-cell band observable at depth `j`, before the translation
average. -/
noncomputable def rawTraceTransportBandObservable (M : ABKModel 2)
    (m : ℤ) (r : ℕ) (t : ℝ) (j : ℕ) (ω : Cutoff.CutoffSample 2) : ℝ :=
  modelTraceObservable (m - (r : ℤ) - (j : ℤ)) M.nu
    (Annealed.sigmaBar M m : ℝ)
    (rawShellBandScalarFromWeights M (m - (r : ℤ) - (j : ℤ)) (134 + j)
      (rawTraceTransportWeights m t) ω)

/-- Apply the exact shell conclusion independently at each source depth.
The weights pad the source band to `134+j`; they keep the completed law through
`m`, its attenuated `m+1` shell, and zero thereafter. -/
theorem raw_trace_transport_origin_depth_family_helper
    (M : ABKModel 2) (h : ℝ) (hγ : M.gamma ≤ gammaZero)
    (m : ℤ) (r : ℕ) (hr : r ≤ 5) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hstate : ∀ j : ℕ,
      nativeInductionState M h (m - (r : ℤ) - (j : ℤ)))
    (hShell : ∀ j : ℕ,
      eLpNorm
          (fun ω => modelTraceObservable (m - (r : ℤ) - (j : ℤ)) M.nu
            (Annealed.sigmaBar M (m - (r : ℤ) - (j : ℤ)) : ℝ)
            (rawShellBandScalarFromWeights M
              (m - (r : ℤ) - (j : ℤ)) (134 + j)
              (rawTraceTransportWeights m t) ω))
          (ENNReal.ofReal 20) (Cutoff.cutoffSampleLaw M).toMeasure ≤
        eLpNorm
          (fun ω => modelTraceObservable (m - (r : ℤ) - (j : ℤ)) M.nu
            (Annealed.sigmaBar M (m - (r : ℤ) - (j : ℤ)) : ℝ)
            (olderField
              (closure (cubeSet (originCube 2 (m - (r : ℤ) - (j : ℤ)))))
              (m - (r : ℤ) - (j : ℤ)) ω))
          (ENNReal.ofReal 20) (Cutoff.cutoffSampleLaw M).toMeasure +
        ENNReal.ofReal
          (rawTraceBandShellIncrement M.gamma (134 + j))) :
    ∀ j : ℕ,
      eLpNorm (rawTraceTransportBandObservable M m r t j)
        (ENNReal.ofReal 2) (Cutoff.cutoffSampleLaw M).toMeasure ≤
        ENNReal.ofReal
          (theta M * (invTraceM : ℚ) * (1 + (j : ℝ)) ^ 2 *
            (3 : ℝ) ^ (6 * gammaZero * j)) := by
  intro j
  let n : ℤ := m - (r : ℤ) - (j : ℤ)
  let weights : ℤ → ℝ := rawTraceTransportWeights m t
  have hnm : n ≤ m := by
    dsimp [n]
    omega
  have hgap : m - n = (r : ℤ) + (j : ℤ) := by
    dsimp [n]
    omega
  have hgapR : ((m - n : ℤ) : ℝ) = (r : ℝ) + (j : ℝ) := by
    exact_mod_cast hgap
  have hrR : (r : ℝ) ≤ 5 := by exact_mod_cast hr
  have hdepth : ((m - n : ℤ) : ℝ) + 1 ≤ 134 + (j : ℝ) := by
    rw [hgapR]
    have hj : 0 ≤ (j : ℝ) := by positivity
    nlinarith
  have hweights : ∀ k ∈ Finset.Ioc n (n + ((134 + j : ℕ) : ℤ)),
      0 ≤ weights k ∧ weights k ≤ 1 := by
    intro k hk
    dsimp [weights, rawTraceTransportWeights]
    by_cases hkm : k ≤ m
    · simp [hkm]
    · by_cases hk1 : k = m + 1
      · have hsqrt_le : Real.sqrt t ≤ 1 := by
          exact Real.sqrt_le_one.mpr ht.2
        simpa [hkm, hk1] using
          (And.intro (Real.sqrt_nonneg t) hsqrt_le)
      · simp [hkm, hk1]
  have hShell' := hShell j
  change eLpNorm
      (fun ω => modelTraceObservable n M.nu (Annealed.sigmaBar M m : ℝ)
        (rawShellBandScalarFromWeights M n (134 + j) weights ω))
      (ENNReal.ofReal 2) (Cutoff.cutoffSampleLaw M).toMeasure ≤ _
  exact raw_trace_band_depth_profile_of_shell_transport_helper M h hγ n m j hnm
    hdepth (hstate j) weights hweights hShell'

/-- The two complete rare corrections are strictly below the
theta-proportional reserve. This is the certified polynomial-geometric sum
bound, using `MM < 10^6`; no reserve estimate is assumed. -/
theorem raw_trace_transport_rare_reserves_helper (theta : ℝ) (hθ : 0 ≤ theta) :
    (5400 : ℝ) * (1 / 10^24 : ℝ) * (invTraceM : ℚ) * theta ≤
        (1 / 10^12 : ℝ) * theta ∧
    (27000 : ℝ) * (1 / 10^24 : ℝ) * (invTraceM : ℚ) * theta ≤
        (1 / 10^12 : ℝ) * theta := by
  have hordinary : (5400 : ℝ) * (1 / 10^24 : ℝ) * (invTraceM : ℚ) ≤
      (1 / 10^12 : ℝ) := by
    have hM : (invTraceM : ℝ) < 10^6 := by
      exact_mod_cast invTrace_coefficient.2.1
    nlinarith [hM]
  have hgrouped : (27000 : ℝ) * (1 / 10^24 : ℝ) * (invTraceM : ℚ) ≤
      (1 / 10^12 : ℝ) := by
    have hM : (invTraceM : ℝ) < 10^6 := by
      exact_mod_cast invTrace_coefficient.2.1
    nlinarith [hM]
  exact ⟨mul_le_mul_of_nonneg_right hordinary hθ,
    mul_le_mul_of_nonneg_right hgrouped hθ⟩

/-- The exact p=20 conclusion, supplied at every depth by the
native-state family. This is the shared discharge of the former
conditional shell premise. -/
theorem raw_trace_transport_shell_family_source
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (m : ℤ) (r : ℕ) (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hstate : ∀ q : ℕ,
      nativeInductionState M h (m - (r : ℤ) - (q : ℤ))) :
    ∀ j : ℕ,
      eLpNorm
          (fun ω => modelTraceObservable (m - (r : ℤ) - (j : ℤ)) M.nu
            (Annealed.sigmaBar M (m - (r : ℤ) - (j : ℤ)) : ℝ)
            (rawShellBandScalarFromWeights M
              (m - (r : ℤ) - (j : ℤ)) (134 + j)
              (rawTraceTransportWeights m t) ω))
          (ENNReal.ofReal 20) (Cutoff.cutoffSampleLaw M).toMeasure ≤
        eLpNorm
          (fun ω => modelTraceObservable (m - (r : ℤ) - (j : ℤ)) M.nu
            (Annealed.sigmaBar M (m - (r : ℤ) - (j : ℤ)) : ℝ)
            (olderField
              (closure (cubeSet (originCube 2
                (m - (r : ℤ) - (j : ℤ)))))
              (m - (r : ℤ) - (j : ℤ)) ω))
          (ENNReal.ofReal 20) (Cutoff.cutoffSampleLaw M).toMeasure +
        ENNReal.ofReal
          (rawTraceBandShellIncrement M.gamma (134 + j)) := by
  intro j
  exact raw_trace_transport_shell_p20_from_depth_states
    M h hM hγ m r j t ht hstate

/-- IN-RAW-TRACE-BAND profile for the actual padded
transport band. Its shell estimate is instantiated from the theorem at each
depth, so the statement has no shell-transport premise. -/
theorem raw_trace_band_profile_source
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (m : ℤ) (r : ℕ) (hr : r ≤ 5)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hstate : ∀ q : ℕ,
      nativeInductionState M h (m - (r : ℤ) - (q : ℤ))) :
    ∀ j : ℕ,
      eLpNorm (rawTraceTransportBandObservable M m r t j)
        (ENNReal.ofReal 2) (Cutoff.cutoffSampleLaw M).toMeasure ≤
        ENNReal.ofReal
          (theta M * (invTraceM : ℚ) * (1 + (j : ℝ)) ^ 2 *
            (3 : ℝ) ^ (6 * gammaZero * j)) := by
  exact raw_trace_transport_origin_depth_family_helper M h hγ m r hr t ht
    hstate (raw_trace_transport_shell_family_source
      M h hM hγ m r t ht hstate)

end
end ASDExplicitGamma.Inverse
