module

public import ASDExplicitGamma.Main.ErrorCoefficients
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-! L² assembly of the two positive-split source-square rows. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open MeasureTheory
open scoped ENNReal

/-- The two source-row L² caps combine to the exact square load `z²`.
The first cap is the global positive-split row and the second is the
correlated mixed-bridge row; this lemma only performs their Minkowski sum. -/
theorem main_source_square_l2_contribution_of_bank_rows
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X Y : Ω → ℝ}
    (v a f H xi : ℝ)
    (hA : MemLp (fun ω => mainKa v * X ω) 2 μ)
    (hArow : lpNorm (fun ω => mainKa v * X ω) 2 μ ≤
      mainKa v * mainR2 a f H)
    (hBrow : lpNorm (fun ω => mainKd v * Y ω) 2 μ ≤
      mainKd v * Real.sqrt (mainBeta * xi + mainEpsNew * mainD * mainBeta * H)) :
    0 ≤ mainLoadZ v a f H xi (mainKd v) ∧
      lpNorm (fun ω => mainKa v * X ω + mainKd v * Y ω) 2 μ ^ 2 ≤
        mainLoadZ v a f H xi (mainKd v) ^ 2 := by
  have hka : 0 ≤ mainKa v := by unfold mainKa; positivity
  have hkd : 0 ≤ mainKd v := mainKd_nonneg v
  have hz : 0 ≤ mainLoadZ v a f H xi (mainKd v) := by
    unfold mainLoadZ mainKa mainR2 mainBeta mainEpsNew mainD mainA2 mainAlpha
    positivity
  have htriangle :
      lpNorm (fun ω => mainKa v * X ω + mainKd v * Y ω) 2 μ ≤
        lpNorm (fun ω => mainKa v * X ω) 2 μ +
          lpNorm (fun ω => mainKd v * Y ω) 2 μ := by
    exact lpNorm_add_le hA (g := fun ω => mainKd v * Y ω)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hnorm :
      lpNorm (fun ω => mainKa v * X ω + mainKd v * Y ω) 2 μ ≤
        mainLoadZ v a f H xi (mainKd v) := by
    calc
      _ ≤ lpNorm (fun ω => mainKa v * X ω) 2 μ +
          lpNorm (fun ω => mainKd v * Y ω) 2 μ := htriangle
      _ ≤ mainKa v * mainR2 a f H +
          mainKd v * Real.sqrt (mainBeta * xi + mainEpsNew * mainD * mainBeta * H) :=
        add_le_add hArow hBrow
      _ = mainLoadZ v a f H xi (mainKd v) := rfl
  refine ⟨hz, ?_⟩
  exact (pow_le_pow_left₀ lpNorm_nonneg hnorm 2)

end ASDExplicitGamma.Main
