module

public import ASDExplicitGamma.Native.HeatPassUniformCap

/-! Finite iteration of proved uniform heat caps, never a fixed-point premise. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Numerics.Native MeasureTheory Set
noncomputable section

/-- The tail-recursive producer is also forward iteration of one heat pass. -/
theorem heat_passes_succ_end (old : NativeOldRow) (frames : NativeHeatFrameInputs)
    (coef fixed : List ℚ) (base : ℚ) (n : ℕ) (y : ℚ) :
    nativeHeatPasses old frames coef fixed base (n+1) y =
      nativeHeatPass old frames coef fixed base (nativeHeatPasses old frames coef fixed base n y) := by
  induction n generalizing y with
  | zero => rfl
  | succ n ih => exact ih (nativeHeatPass old frames coef fixed base y)

/-- Every finite redistribution, including the source's48 passes, is a
consequence of the differential rows at previously PROVED uniform caps. The
root inputs are numerical certificates, not assumed analytic cap estimates. -/
theorem heat_finite_passes_uniform_cap (old : NativeOldRow) (frames : NativeHeatFrameInputs)
    (fixed init : List ℚ) (y0 c ee : ℚ) (steps : ℕ) (hc : 0 ≤ c)
    (hcheck : nativeHeatExpCheck c ee = true)
    (he : 0 ≤ old.e) (hx : 0 ≤ frames.x)
    (hfixed : ∀ j < 20,0 ≤ fixed.getD j 0)
    (hinitlen : init.length = 21) (hinit0 : ∀ j ≤ 20,0 ≤ init.getD j 0)
    (m mp : ℕ → ℝ → ℝ) (hy0 : HeatUniformMomentCap m y0)
    (hmcont : ∀ j ≤ 20,ContinuousOn (m j) (Icc 0 1))
    (hmderiv : ∀ s ∈ Ioo 0 1,∀ j ≤ 20,HasDerivAt (m j) (mp j s) s)
    (hint : ∀ T ∈ Icc (0:ℝ) 1,IntervalIntegrable (heatMomentBackwardDerivative c 20 T m mp) volume 0 T)
    (hstart : ∀ j ≤ 20,m j 0 ≤ (init.getD j 0:ℝ))
    (hrow : ∀ y : ℚ,HeatUniformMomentCap m y → y ≤ y0 →
      ∀ s ∈ Icc 0 1,∀ j ≤ 20,mp j s ≤ (c:ℝ)*(j:ℝ)*m j s+4*(c:ℝ)*(j:ℝ)*m (j-1) s+
        (if j=0 then 0 else (nativeHeatForcingAt old frames fixed y j:ℝ)))
    (hroot : ∀ n < steps,nativeRootValid
      (heatPassMomentBudget old frames (nativeHeatCoefficients ee) fixed
        (nativeHeatBase (nativeHeatCoefficients ee) init)
        (nativeHeatPasses old frames (nativeHeatCoefficients ee) fixed
          (nativeHeatBase (nativeHeatCoefficients ee) init) n y0)) 20 = true) :
    HeatUniformMomentCap m (nativeHeatPasses old frames (nativeHeatCoefficients ee) fixed
      (nativeHeatBase (nativeHeatCoefficients ee) init) steps y0) := by
  have hcap : ∀ n, n ≤ steps → HeatUniformMomentCap m
      (nativeHeatPasses old frames (nativeHeatCoefficients ee) fixed
        (nativeHeatBase (nativeHeatCoefficients ee) init) n y0) := by
    intro n
    induction n with
    | zero => intro _; exact hy0
    | succ n ih =>
      intro hn
      have hprev := ih (by omega)
      rw [heat_passes_succ_end]
      apply heat_pass_uniform_cap old frames fixed init _ c ee hc hcheck he hx hfixed hinitlen hinit0
        m mp hprev hmcont hmderiv hint hstart
      · exact hrow _ hprev (native_heat_passes_le old frames _ fixed _ n y0)
      · exact hroot n (by omega)
  exact hcap steps le_rfl

end
end ASDExplicitGamma.Native
