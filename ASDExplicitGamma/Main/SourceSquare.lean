module

public import ASDExplicitGamma.Main.SourceSquareAssembly
public import ASDExplicitGamma.Model.Cutoff
public import ASDExplicitGamma.Gaussian.RioTwoSum

/-! Actual-law assembly of the positive source-square row. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open MeasureTheory Homogenization Algsuperdiff.Section3
open Algsuperdiff.Section3.Cutoff

/-- The source-square L² contribution on the actual cutoff law. `hGlobal`
is the positive-split source-row conclusion from the global inverse bank;
`hMixedBridge` is the correlated four-load source-row conclusion. Their
random variables are the actual OLD-frame source observables. The proof is
the source Minkowski step and the literal coefficient identification. -/
theorem main_e_source_square_actual_law
    (M : ABKModel 2) (v a f H xi : ℝ)
    (X Y : Cutoff.CutoffSample 2 → ℝ)
    (hGlobal :
      MemLp (fun ω => mainKa v * X ω) 2
        (Cutoff.cutoffSampleLaw M).toMeasure ∧
      lpNorm (fun ω => mainKa v * X ω) 2
        (Cutoff.cutoffSampleLaw M).toMeasure ≤ mainKa v * mainR2 a f H)
    (hMixedBridge :
      MemLp (fun ω => mainKd v * Y ω) 2
        (Cutoff.cutoffSampleLaw M).toMeasure ∧
      lpNorm (fun ω => mainKd v * Y ω) 2
        (Cutoff.cutoffSampleLaw M).toMeasure ≤
          mainKd v * Real.sqrt
            (mainBeta * xi + mainEpsNew * mainD * mainBeta * H)) :
    0 ≤ mainLoadZ v a f H xi (mainKd v) ∧
      MemLp (fun ω => mainKa v * X ω + mainKd v * Y ω) 2
        (Cutoff.cutoffSampleLaw M).toMeasure ∧
      (∫ ω, (mainKa v * X ω + mainKd v * Y ω) ^ 2
        ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
          mainLoadZ v a f H xi (mainKd v) ^ 2 := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let Z : Cutoff.CutoffSample 2 → ℝ := fun ω => mainKa v * X ω + mainKd v * Y ω
  have hAssembly := main_source_square_l2_contribution_of_bank_rows
    (μ := (Cutoff.cutoffSampleLaw M).toMeasure) v a f H xi
    hGlobal.1 hGlobal.2 hMixedBridge.2
  have hZ : MemLp Z 2 μ := by
    dsimp [Z]
    exact hGlobal.1.add hMixedBridge.1
  refine ⟨hAssembly.1, hZ, ?_⟩
  have hnorm := hAssembly.2
  rw [← ASDExplicitGamma.Gaussian.rio_lpNorm_two_sq hZ]
  simpa only [Z, μ] using hnorm

end ASDExplicitGamma.Main
