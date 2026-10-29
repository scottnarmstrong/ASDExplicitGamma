module

public import ASDExplicitGamma.Inverse.PositiveRootBound
public import ASDExplicitGamma.Inverse.FixedSelectedHeight
public import ASDExplicitGamma.Inverse.StoppedPastDiameterFinite

/-! Actual-law positive root assembly at the fixed source row's selected height. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian
open scoped ENNReal
noncomputable section

/-- IN-POSITIVE-ROOT-ASSEMBLY: the actual root response is bounded almost
surely by the exact Li selected-height clock and the previously constructed
complete positive E_l. All separation, diameter-finiteness, local response,
frame, hybrid gluing and deterministic layer inputs are supplied internally. -/
theorem q3_positive_root_assembly (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (Q : TriadicCube 2) (m J : ℤ)
    (hQ : Q.scale ≤ m) (hm : m ≤ J) (weights : ℤ → ℝ)
    (hw : ∀ k ∈ Finset.Ioc m J, 0 ≤ weights k ∧ weights k ≤ 1)
    (r : RootRow) (hpast : ∀ n < m, nativeInductionState M h n)
    (hmean : ClippedInverseMeanInput M m r) :
    ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      ENNReal.ofReal (rootInverseResponse M Q m J weights ω) ≤
        ENNReal.ofReal ((3:ℝ)^(2*M.gamma*|((m-Q.scale+1:ℤ):ℝ)|))*
          (ENNReal.ofReal (rootLi M.gamma r)*
            selectedHeightClock M.gamma (q3StoppedHeight M Q (rootH0 r) (rootTau r)
              (waveGateEta (rootWaveTuple r))) ω+positiveRootError M Q r ω) := by
  have hH0 : 333 ≤ rootH0 r := by cases r <;> norm_num [rootH0]
  have hτ : 0 < rootTau r := by cases r <;> norm_num [rootTau]
  obtain ⟨hq0,hq,hraw⟩ := root_row_density_inputs r
  have hprotected : ∀ k ≤ Q.scale-(rootH0 r:ℤ)+40, nativeInductionState M h k := by
    intro k hk
    exact hpast k (by omega)
  have hgood := q3_stopped_height_ae_good M h hM hg Q (rootH0 r) hH0
    (rootTau r) hτ (rootWaveTuple r) (rootQ r) hq0 hq hraw hprotected
  have hfin := q3_past_diameter_ae_ne_top M h hM hg (Q.scale-(rootH0 r:ℤ))
    (rootTau r) hτ (rootWaveTuple r) (rootQ r) hq0 hq hraw
      (fun k hk => hprotected k (by omega))
  filter_upwards [hgood,hfin] with ω hωg hωf
  let H := q3StoppedHeight M Q (rootH0 r) (rootTau r) (waveGateEta (rootWaveTuple r)) ω
  have hHH0 : rootH0 r ≤ H := q3_stopped_height_ge M Q (rootH0 r) (rootTau r) _ ω
  have hf : ∀ j ≤ Q.scale-(H:ℤ), ∀ z, diameterField
      (q3PlanarMarks M j (rootTau r) (waveGateEta (rootWaveTuple r))) ω z ≠ ∞ := by
    intro j hj z
    exact hωf j (by omega) z
  have hh := positive_root_bound_of_successful_height M hg Q H r hHH0 ω hωg hf
    m J hQ hm weights hw hmean
  simpa only [Int.cast_abs,selectedHeightClock,H] using hh

end
end ASDExplicitGamma.Inverse
