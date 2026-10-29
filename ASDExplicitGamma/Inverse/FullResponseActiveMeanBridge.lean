module

public import ASDExplicitGamma.Inverse.FullResponseActiveMeanOscillation
public import ASDExplicitGamma.Inverse.FullResponseActiveTriangle
public import ASDExplicitGamma.Inverse.HybridFullTraceCongruence

/-! Convert the good-cell descendant mean oscillation into the exact two
active shear coefficients of the source. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse

open Homogenization MeasureTheory Algsuperdiff.Section3
open Algsuperdiff.Section3.Provider Algsuperdiff.Section3.Provider.Multiscale
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Model ASDExplicitGamma.Triadic
open ASDExplicitGamma.Response ASDExplicitGamma.Variational
open scoped ENNReal

noncomputable section

private theorem full_active_mean_coefficients (z : ℝ) :
    2 * (1 + 2 * Real.sqrt 3 * rootTau .full) *
        (1 + (|z| + 10 * waveGateEta .full)^2) ≤
      2 * (1 + Real.sqrt 2 * (10 * waveGateEta .full))^2 *
          (1 + 6 * rootTau .full) +
        2 * (1 + 6 * rootTau .full) * z^2 := by
  let τ := rootTau .full
  let δ := 10 * waveGateEta .full
  let A := 1 + 2 * Real.sqrt 3 * τ
  let B := 1 + 6 * τ
  have hτ : 1 ≤ τ := by norm_num [τ, rootTau]
  have hδ : 0 ≤ δ := by
    dsimp only [δ]
    exact mul_nonneg (by norm_num) (wave_gate_eta_pos .full).le
  have hδ16 : δ ≤ 1/16 := by
    norm_num [δ, waveGateEta, ASDExplicitGamma.Numerics.Wave.fullEta,
      ASDExplicitGamma.Numerics.Wave.fullTau]
  have hsqrt3 : Real.sqrt (3:ℝ) ≤ 2 := by
    have hs : (Real.sqrt (3:ℝ))^2 = 3 := Real.sq_sqrt (by norm_num)
    have hn := Real.sqrt_nonneg (3:ℝ)
    nlinarith only [hs, hn]
  have hA : 0 ≤ A := by positivity
  have hAupper : A ≤ 1 + 4 * τ := by
    have hmul := mul_le_mul_of_nonneg_right hsqrt3 (by positivity : 0 ≤ τ)
    dsimp only [A]
    nlinarith only [hmul]
  have hsmall : 1 + 5 * δ^2 ≤ 1 + 5 * (1/16:ℝ)^2 := by
    nlinarith only [hδ, hδ16]
  have hbase : A * (1 + 5 * δ^2) ≤ B := by
    have hprod := mul_le_mul hAupper hsmall (by positivity) (by positivity)
    dsimp only [B]
    nlinarith only [hprod, hτ]
  have hwave : (5/4:ℝ) * A ≤ B := by
    have hmul := mul_le_mul_of_nonneg_left hAupper (by norm_num : (0:ℝ) ≤ 5/4)
    dsimp only [B]
    nlinarith only [hmul, hτ]
  have hcross : 1 + (|z| + δ)^2 ≤
      (1 + 5 * δ^2) + (5/4:ℝ) * (|z|)^2 := by
    have hsquare : 0 ≤ (|z|/2 - 2*δ)^2 := sq_nonneg _
    nlinarith only [hsquare]
  have hmain : A * (1 + (|z| + δ)^2) ≤ B + B*z^2 := by
    calc
      _ ≤ A * ((1 + 5*δ^2) + (5/4:ℝ) * (|z|)^2) :=
        mul_le_mul_of_nonneg_left hcross hA
      _ = A*(1+5*δ^2) + ((5/4:ℝ)*A)*(|z|)^2 := by ring
      _ ≤ B + B*z^2 := by
        have hwave' := mul_le_mul_of_nonneg_right hwave (sq_nonneg (|z|))
        simpa only [sq_abs] using add_le_add hbase hwave'
  have hx : 0 ≤ Real.sqrt 2 * δ :=
    mul_nonneg (Real.sqrt_nonneg _) hδ
  have hfactor : 1 ≤ (1 + Real.sqrt 2 * δ)^2 := by nlinarith only [hx]
  have hB : 0 ≤ B := by positivity
  have hfactorB := mul_le_mul_of_nonneg_right hfactor hB
  calc
    _ = 2 * ((1 + 2 * Real.sqrt 3 * rootTau .full) *
        (1 + (|z| + 10 * waveGateEta .full)^2)) := by ring
    _ ≤ 2 * ((1 + 6 * rootTau .full) +
        (1 + 6 * rootTau .full) * z^2) := by
      exact mul_le_mul_of_nonneg_left hmain (by norm_num)
    _ ≤ 2 * (1 + Real.sqrt 2 * (10 * waveGateEta .full))^2 *
          (1 + 6 * rootTau .full) +
        2 * (1 + 6 * rootTau .full) * z^2 := by
      nlinarith only [hfactorB]

/-- On an actual good active parent triangle, the descendant mean-oscillation
gate yields the source (c_{0t}+c_{1t}m^2) trace cap. Here (m) is the
later-band average on the original source square in its fixed sigmaBar frame. -/
theorem good_parent_active_triangle_actual_full_trace_root_mean
    (M : ABKModel 2) {Q U : TriadicCube 2} {a : ℕ}
    (hU : U ∈ descendantsAtDepth Q a) (ha : a ≤ 2)
    (pi : Equiv.Perm (Fin 2)) (m J : ℤ) (hn : Q.scale + 40 ≤ m)
    (hm : m ≤ J) (weights : ℤ → ℝ)
    (hw : ∀ k ∈ Finset.Ioc m J, 0 ≤ weights k ∧ weights k ≤ 1)
    (ω : Cutoff.CutoffSample 2)
    (hgood : ω ∉ cellFailure M (rootTau .full)
      (waveGateEta .full) Q) :
    let n := Q.scale + 40
    let σ := (Annealed.sigmaBar M n : ℝ)
    let y := cubeAverage Q
      (laterBandW2 Q n J (sourceBandWeights m weights) ω).value.toFun / σ
    let c0t := 2 * (1 + Real.sqrt 2 * (10 * waveGateEta .full))^2 *
      (1 + 6 * rootTau .full)
    let c1t := 2 * (1 + 6 * rootTau .full)
    ENNReal.ofReal (Matrix.trace (toFullBlockMat (frameMatrix
      (Annealed.sigmaBar M (Q.scale + 40) : ℝ)
      (coarseBlockMatrix (Whitney.KuhnCell.mk U pi).openCarrier
        (attenuatedCoefficient M m J weights ω)))) / 4) ≤
      ENNReal.ofReal (rootEdelta .full * (c0t + c1t*y^2)) := by
  classical
  dsimp only
  let n := Q.scale + 40
  let σ := (Annealed.sigmaBar M n : ℝ)
  let source := sourceBandWeights m weights
  let f := laterBandW2 Q n J source ω
  let y := cubeAverage Q f.value.toFun / σ
  let δ := 10 * waveGateEta .full
  let W := |y| + δ
  let c0t := 2 * (1 + Real.sqrt 2 * δ)^2 * (1 + 6 * rootTau .full)
  let c1t := 2 * (1 + 6 * rootTau .full)
  have hη : 0 ≤ waveGateEta .full := (wave_gate_eta_pos .full).le
  have hδ : 0 ≤ δ := by dsimp only [δ]; positivity
  have hsource := source_band_weights_bounds n m J weights hw
  have hmean : ∀ P : ↥(triangleCubePartition U.scale pi),
      |cubeAverage (triangleRootCube U pi P)
        ((laterBandW2 Q n J source ω).restrict
          (triangle_root_cube_descendant_of_parent hU pi P)).value.toFun / σ| ≤ W := by
    intro P
    let R := triangleRootCube U pi P
    let hR := triangle_root_cube_descendant_of_parent hU pi P
    let x := cubeAverage R ((laterBandW2 Q n J source ω).restrict hR).value.toFun / σ
    have hosc := good_cell_later_band_cube_average_oscillation M Q R
      (a + (triangleRootPartitionDepth U pi P + 1)) hR
      (rootTau .full) (waveGateEta .full) hη ω hgood J source hsource
    have hosc' : |x-y| ≤ δ := by
      simpa only [x, y, δ, R, hR, f, n, σ, source] using hosc
    have hbound : |x| ≤ |y| + δ := by
      calc
        _ = |(x-y)+y| := by congr 1; ring
        _ ≤ |x-y|+|y| := abs_add_le _ _
        _ ≤ δ+|y| := add_le_add hosc' le_rfl
        _ = |y|+δ := by ring
    simpa only [x, W] using hbound
  have hW : 0 ≤ W := by dsimp only [W]; positivity
  have htriangle := good_parent_active_triangle_actual_full_trace_of_uniform_mean
    M hU ha pi .full m J hn hm weights hw ω hgood W hW hmean
  have hcoef := full_active_mean_coefficients y
  have hE : 0 ≤ rootEdelta .full := (Real.exp_pos _).le
  have hscalar :
      2 * rootEdelta .full * (1 + W^2) *
          (1 + 2 * Real.sqrt 3 * rootTau .full) ≤
        rootEdelta .full * (c0t + c1t*y^2) := by
    calc
      _ = rootEdelta .full *
          (2 * (1 + 2 * Real.sqrt 3 * rootTau .full) *
          (1 + (|y| + δ)^2)) := by ring
      _ ≤ rootEdelta .full * (c0t + c1t*y^2) := by
        apply mul_le_mul_of_nonneg_left _ hE
        simpa only [c0t, c1t, δ, sq_abs] using hcoef
  calc
    _ ≤ ENNReal.ofReal (2 * rootEdelta .full * (1 + W^2) *
        (1 + 2 * Real.sqrt 3 * rootTau .full)) := by
      simpa only [n, σ] using htriangle
    _ ≤ _ := ENNReal.ofReal_le_ofReal hscalar

end
end ASDExplicitGamma.Inverse
