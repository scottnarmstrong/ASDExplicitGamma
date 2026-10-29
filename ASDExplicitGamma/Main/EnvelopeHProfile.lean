module

public import ASDExplicitGamma.Main.EnvelopeHTransport
public import ASDExplicitGamma.Cold.NativeParentMoment

/-! Assemble the exact p=20 depth rows into the OLD weak-trace history. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open MeasureTheory Set Homogenization Algsuperdiff.Section3
open ASDExplicitGamma.Inverse ASDExplicitGamma.Cold ASDExplicitGamma.Gaussian
open scoped ENNReal

noncomputable section

/-- A family of exact p=20 generator rows transports an OLD L20 profile to
the actual weak-trace history. The generator inequality, old profile, and
endpoint L20 facts remain explicit so this helper can be instantiated from
the raw-shell transport and the OLD bank. -/
theorem main_rawWeakTraceHistory_lpNorm_le_of_depth_generators
    (M : ABKModel 2) (m : ℤ) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (τ : ℝ) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (B : ℕ → ℝ) (U : ℕ → ℝ → ℝ)
    (hU0 : ∀ j t, t ∈ Icc (0 : ℝ) 1 → 0 ≤ U j t)
    (hUInt : ∀ j, IntegrableOn (U j) (Icc (0 : ℝ) 1))
    (hT0 : ∀ j, MemLp
      (rawDepthFourLoadTrace M m (m - ((5 + j : ℕ) : ℤ)) 0) 20
      (Cutoff.cutoffSampleLaw M).toMeasure)
    (hTτ : ∀ j, MemLp
      (rawDepthFourLoadTrace M m (m - ((5 + j : ℕ) : ℤ)) τ) 20
      (Cutoff.cutoffSampleLaw M).toMeasure)
    (hB : ∀ j, lpNorm
      (rawDepthFourLoadTrace M m (m - ((5 + j : ℕ) : ℤ)) 0) 20
      (Cutoff.cutoffSampleLaw M).toMeasure ≤ B j)
    (hGenerator : ∀ j t, t ∈ Ioo (0 : ℝ) 1 →
      deriv (modelTracePowerHeatAverage (m - ((5 + j : ℕ) : ℤ)) M m 20) t ≤
        20 * modelTracePowerHeatAverage (m - ((5 + j : ℕ) : ℤ)) M m 20 t ^
          ((19 : ℝ) / 20) * U j t)
    (hprofile : Summable (fun j : ℕ => Scalar.inverseHistoryDiscount ^ j *
      (B j + ∫ t in (0 : ℝ)..τ, U j t))) :
    ∃ hT : ∀ j : ℕ,
      MemLp (rawWeakTraceSequence M m (originCube 2 (m - 5)) τ · j) 2
        (Cutoff.cutoffSampleLaw M).toMeasure,
      ‖rawWeakTraceHistoryLp M m (originCube 2 (m - 5)) τ hT‖ ≤
        (1 - Scalar.inverseHistoryDiscount) *
          ∑' j : ℕ, Scalar.inverseHistoryDiscount ^ j *
            (B j + ∫ t in (0 : ℝ)..τ, U j t) := by
  let Q : TriadicCube 2 := originCube 2 (m - 5)
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let E : ℕ → ℝ := fun j => ∫ t in (0 : ℝ)..τ, U j t
  let X : ∀ j, SquareCells Q j → Cutoff.CutoffSample 2 → ℝ := fun j C =>
    rawCubeFourLoadTrace M m C.val τ
  have hscale (j : ℕ) (C : SquareCells Q j) :
      C.val.scale = m - ((5 + j : ℕ) : ℤ) := by
    rw [scale_eq_sub_of_mem_descendantsAtDepth C.property]
    change (m - 5) - (j : ℤ) = m - ((5 + j : ℕ) : ℤ)
    omega
  have hX20 (j : ℕ) (C : SquareCells Q j) : MemLp (X j C) 20 μ := by
    have hTcell : MemLp (rawDepthFourLoadTrace M m C.val.scale τ) 20 μ := by
      simpa only [hscale j C] using hTτ j
    simpa only [X] using
      main_rawCubeFourLoadTrace_memLp_of_origin M m C.val τ 20 hTcell
  have hX2 (j : ℕ) (C : SquareCells Q j) : MemLp (X j C) 2 μ :=
    (hX20 j C).mono_exponent (by norm_num : (2 : ℝ≥0∞) ≤ 20)
  have hXcap20 (j : ℕ) (C : SquareCells Q j) :
      lpNorm (X j C) 20 μ ≤ B j + E j := by
    have hGenCell : ∀ t ∈ Ioo (0 : ℝ) 1,
        deriv (modelTracePowerHeatAverage C.val.scale M m 20) t ≤
          20 * modelTracePowerHeatAverage C.val.scale M m 20 t ^ ((19 : ℝ) / 20) * U j t := by
      intro t ht
      simpa only [hscale j C] using hGenerator j t ht
    have hT0cell : MemLp (rawDepthFourLoadTrace M m C.val.scale 0) 20 μ := by
      simpa only [hscale j C] using hT0 j
    have hTτcell : MemLp (rawDepthFourLoadTrace M m C.val.scale τ) 20 μ := by
      simpa only [hscale j C] using hTτ j
    have hBcell : lpNorm (rawDepthFourLoadTrace M m C.val.scale 0) 20 μ ≤ B j := by
      simpa only [hscale j C] using hB j
    have h := main_rawCube_lpNorm_twenty_bound_of_generator
      C.val M h hM m (U j) (hU0 j) (hUInt j) τ hτ0 hτ1 hGenCell
      hT0cell hTτcell (B j) hBcell
    simpa only [X, E] using h
  have hXcap2 (j : ℕ) (C : SquareCells Q j) :
      lpNorm (X j C) 2 μ ≤ B j + E j := by
    have hmono := eLpNorm_le_eLpNorm_of_exponent_le
      (f := X j C) (μ := μ) (by norm_num : (2 : ℝ≥0∞) ≤ 20)
    calc
      lpNorm (X j C) 2 μ ≤ lpNorm (X j C) 20 μ := by
        change (eLpNorm (X j C) 2 μ).toReal ≤
          (eLpNorm (X j C) 20 μ).toReal
        exact ENNReal.toReal_mono (hX20 j C).eLpNorm_ne_top hmono
      _ ≤ B j + E j := hXcap20 j C
  have hmean (j : ℕ) (ω : Cutoff.CutoffSample 2) :
      rawWeakTraceSequence M m Q τ ω j =
        (∑ C : SquareCells Q j, X j C ω) /
          (Fintype.card (SquareCells Q j) : ℝ) := by
    simp only [rawWeakTraceSequence, X, squareCellMean]
    have hcard : (descendantsAtDepth Q j).card = Fintype.card (SquareCells Q j) := by
      simp [SquareCells]
    rw [hcard]
    ring
  have hseq (j : ℕ) :
      (fun ω => rawWeakTraceSequence M m Q τ ω j) =
        fun ω => (∑ C : SquareCells Q j, X j C ω) /
          (Fintype.card (SquareCells Q j) : ℝ) := by
    funext ω
    exact hmean j ω
  have hT : ∀ j : ℕ,
      MemLp (rawWeakTraceSequence M m Q τ · j) 2 μ := by
    intro j
    rw [hseq j]
    convert (memLp_finsetSum Finset.univ (fun C _ => hX2 j C)).const_mul
      ((Fintype.card (SquareCells Q j) : ℝ)⁻¹) using 1
    funext ω
    simp [div_eq_mul_inv, mul_comm]
  have hcap (j : ℕ) :
      lpNorm (rawWeakTraceSequence M m Q τ · j) 2 μ ≤ B j + E j := by
    rw [hseq j]
    exact cold_trace_average_two_lpNorm_le (fun C => hX2 j C) (fun C => hXcap2 j C)
  have hbound (j : ℕ) :
      ‖(hT j).toLp (rawWeakTraceSequence M m Q τ · j)‖ ≤ B j + E j := by
    simpa only [Lp.norm_toLp, lpNorm] using hcap j
  refine ⟨hT, ?_⟩
  exact raw_weak_trace_history_lpNorm_le_of_envelope M m Q τ hT
    (fun j => B j + E j) (by simpa only [E] using hprofile) hbound

end

end ASDExplicitGamma.Main

