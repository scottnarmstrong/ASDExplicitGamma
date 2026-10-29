module

public import ASDExplicitGamma.Inverse.AssemblyTraceProfileCap
public import ASDExplicitGamma.Inverse.AssemblyTraceSeries
public import ASDExplicitGamma.Inverse.OrderResetInterface
public import ASDExplicitGamma.Inverse.FullResponseFrameTransport

/-! The actual trace satisfies its all-order profile in every reference
frame, with exactly the source frame-gap exponent. -/

@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open scoped ENNReal
noncomputable section

/-- The complete actual trace has the source all-real-order profile at an
arbitrary reference label. The frame gap contributes only `2γf`. -/
theorem assembly_root_trace_profile_Lp
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (Q : TriadicCube 2) (p : ℝ) (hp : 2 ≤ p)
    (hpast : ∀ n : ℤ,
      n ≤ Q.scale-342-12*orderBand p → nativeInductionState M h n)
    (N K₀ : ℤ) (hN : Q.scale-1 ≤ N) (weights : ℤ → ℝ)
    (hw : ∀ n ∈ Finset.Ioc
      (protectedOldLabel Q.scale (orderBand p)) N,
      0 ≤ weights n ∧ weights n ≤ 1) :
    let D := ((N-Q.scale+1:ℤ):ℝ)
    let f := |((K₀-Q.scale+1:ℤ):ℝ)|
    eLpNorm (rootTraceObservable M Q
      (protectedOldLabel Q.scale (orderBand p)) N K₀ weights)
      (ENNReal.ofReal p) (Cutoff.cutoffSampleLaw M).toMeasure ≤
        ENNReal.ofReal (orderTraceProfile M.gamma p D f) := by
  let D : ℝ := ((N-Q.scale+1:ℤ):ℝ)
  let f : ℝ := |((K₀-Q.scale+1:ℤ):ℝ)|
  let k := orderBand p
  let E := heightEntrance k
  let m := protectedOldLabel Q.scale k
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  have hD : 0 ≤ D := by
    dsimp only [D]
    exact_mod_cast (show 0 ≤ N-Q.scale+1 by omega)
  have hγ0 : 0 ≤ M.gamma := M.shellPrefix.gamma_pos.le
  have hmN : m ≤ N := by
    dsimp only [m,protectedOldLabel]
    omega
  have hbudget := assembly_trace_profile_budget_cap M.gamma p D hγ hγ0 hp hD
  have hsource :
      eLpNorm (rootTraceObservable M Q m N (Q.scale-1) weights)
        (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal (orderTraceProfile M.gamma p D 0) := by
    have htrace := assembly_root_trace_Lp M h hM hγ Q p hp hpast N hN weights hw
    have hreal :
        4*assemblyTraceSeriesSelectedBudget M.gamma p D k ≤
          orderTraceProfile M.gamma p D 0 := by
      have hbudget' :
          assemblyTraceSeriesSelectedBudget M.gamma p D k ≤
            (2+2810*M.gamma*((E:ℝ)+20+p*(D+1)))*
              (3:ℝ)^(4*M.gamma*((E:ℝ)+20)+2*M.gamma*D) := by
        simpa only [k,E] using hbudget
      calc
        _ ≤ 4*((2+2810*M.gamma*((E:ℝ)+20+p*(D+1)))*
            (3:ℝ)^(4*M.gamma*((E:ℝ)+20)+2*M.gamma*D)) :=
          mul_le_mul_of_nonneg_left hbudget' (by norm_num)
        _ = orderTraceProfile M.gamma p D 0 := by
          unfold orderTraceProfile
          simp only [mul_zero, add_zero]
          ring
    exact htrace.trans (ENNReal.ofReal_le_ofReal hreal)
  let G := (3:ℝ)^(2*M.gamma*f)
  have hG0 : 0 ≤ G := by dsimp only [G]; positivity
  have hprofile : G*orderTraceProfile M.gamma p D 0 =
      orderTraceProfile M.gamma p D f := by
    unfold orderTraceProfile
    dsimp only [G]
    simp only [mul_zero, add_zero]
    calc
      _ = 4*(2+2810*M.gamma*((heightEntrance (orderBand p):ℝ)+20+
          p*(D+1)))*
          ((3:ℝ)^(4*M.gamma*((heightEntrance (orderBand p):ℝ)+20)+
            2*M.gamma*D)*(3:ℝ)^(2*M.gamma*f)) := by ring
      _ = _ := by
        rw [← Real.rpow_add (by norm_num : (0:ℝ)<3)]
  have hframe := full_response_trace_frame_Lp_le M Q m N K₀ hmN weights
    (ENNReal.ofReal p)
  have hfull (K : ℤ) :
      eLpNorm (rootTraceObservable M Q m N K weights)
          (ENNReal.ofReal p) μ =
        ENNReal.ofReal (4:ℝ)*
          eLpNorm (fun ω => rootTraceObservable M Q m N K weights ω/4)
            (ENNReal.ofReal p) μ := by
    change eLpNorm (fun ω => rootTraceObservable M Q m N K weights ω)
      (ENNReal.ofReal p) μ = _
    have hfun : (fun ω => rootTraceObservable M Q m N K weights ω) =
        (4:ℝ) • (fun ω => rootTraceObservable M Q m N K weights ω/4) := by
      funext ω
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    rw [hfun,eLpNorm_const_smul,Real.enorm_eq_ofReal (by norm_num : (0:ℝ)≤4)]
  calc
    _ = ENNReal.ofReal (4:ℝ)*
        eLpNorm (fun ω => rootTraceObservable M Q m N K₀ weights ω/4)
          (ENNReal.ofReal p) μ := hfull K₀
    _ ≤ ENNReal.ofReal (4:ℝ)*
        (ENNReal.ofReal G*
          eLpNorm (fun ω => rootTraceObservable M Q m N (Q.scale-1) weights ω/4)
            (ENNReal.ofReal p) μ) :=
      mul_le_mul_of_nonneg_left hframe (by positivity)
    _ = ENNReal.ofReal G*
        (ENNReal.ofReal (4:ℝ)*
          eLpNorm (fun ω => rootTraceObservable M Q m N (Q.scale-1) weights ω/4)
            (ENNReal.ofReal p) μ) := by ac_rfl
    _ = ENNReal.ofReal G*
        eLpNorm (rootTraceObservable M Q m N (Q.scale-1) weights)
          (ENNReal.ofReal p) μ := by rw [← hfull (Q.scale-1)]
    _ ≤ ENNReal.ofReal G*ENNReal.ofReal (orderTraceProfile M.gamma p D 0) :=
      mul_le_mul_of_nonneg_left hsource (by positivity)
    _ = ENNReal.ofReal (orderTraceProfile M.gamma p D f) := by
      rw [← ENNReal.ofReal_mul hG0,hprofile]

end
end ASDExplicitGamma.Inverse
