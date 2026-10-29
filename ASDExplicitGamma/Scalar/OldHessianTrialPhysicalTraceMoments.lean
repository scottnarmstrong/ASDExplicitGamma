module

public import ASDExplicitGamma.Scalar.OldHessianTrialPhysicalSourceMeans
public import ASDExplicitGamma.Native.OldSignedSourceCellTraceLaw

/-! Raw trace moment control on the actual large scalar parent, at the
original source offsets and all additional weak depths. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational Gaussian Inverse Main Cold Algsuperdiff.Section3
open scoped ENNReal
noncomputable section
attribute [local irreducible] Homogenization.descendantsAtDepth

/-- The huge parent average costs no population factor in its L2 trace
profile. Each physical child retains scale m-r-j and the true frame m. -/
theorem old_hessian_large_parent_trace_profile
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (N : ℤ)
    (hpast : ∀ k<N,nativeInductionState M h k) (m : ℤ) (hm : m<N)
    (r : ℕ) (hr : r≤5) (j : ℕ) :
    eLpNorm (fun ω => rawWeakTraceSequence M m (originCube 2 (m+129)) 0 ω (129+r+j)) 2
      (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal (theta M*(Numerics.Inverse.invTraceM:ℝ)*(1+(j:ℝ))^2*(3:ℝ)^(6*gammaZero*j)) := by
  let Q := originCube 2 (m+129)
  let depth := 129+r+j
  let I := SquareCells Q depth
  let C := theta M*(Numerics.Inverse.invTraceM:ℝ)*(1+(j:ℝ))^2*(3:ℝ)^(6*gammaZero*j)
  let d : ℝ := (descendantsAtDepth Q depth).card
  have hd : 0<d := by
    dsimp [d]
    exact_mod_cast Finset.card_pos.mpr (descendantsAtDepth_nonempty Q depth)
  have htheta : 0≤theta M := div_nonneg M.shellPrefix.gamma_pos.le (by norm_num [gammaZero])
  have hMrat : 0≤Numerics.Inverse.invTraceM := by
    rw [Numerics.Inverse.invTrace_coefficient.1]
    positivity
  have hM0 : 0≤(Numerics.Inverse.invTraceM:ℝ) := by exact_mod_cast hMrat
  have hC : 0≤C := by dsimp [C]; positivity
  have hstates : ∀ k ≤ m,nativeInductionState M h k := fun k hk => hpast k (hk.trans_lt hm)
  have hcell (U : I) : eLpNorm (rawCubeFourLoadTrace M m U.val 0) 2
      (Cutoff.cutoffSampleLaw M).toMeasure ≤ ENNReal.ofReal C := by
    apply old_signed_source_cell_trace_L2 M h hM hg m r j hr 0 (by norm_num) hstates U.val
    have hs := scale_eq_sub_of_mem_descendantsAtDepth U.property
    change U.val.scale=m+129-(depth:ℤ) at hs
    dsimp only [depth] at hs
    omega
  have hh := finite_density_sum_Lp (Cutoff.cutoffSampleLaw M).toMeasure 2
    (by norm_num) (fun U : I => rawCubeFourLoadTrace M m U.val 0)
    (fun _ => d⁻¹) (fun _ => C) (fun _ => inv_nonneg.mpr hd.le) (fun _ => hC) hcell
  have hcard : Fintype.card I=(descendantsAtDepth Q depth).card := by simp [I,SquareCells]
  have hsum : (∑ _U : I,d⁻¹*C)=C := by
    simp only [Finset.sum_const,Finset.card_univ,hcard,nsmul_eq_mul]
    change d*(d⁻¹*C)=C
    rw [←mul_assoc,mul_inv_cancel₀ hd.ne',one_mul]
  have he : (fun ω => rawWeakTraceSequence M m Q 0 ω depth)=
      (fun ω => ∑ U : I,d⁻¹*rawCubeFourLoadTrace M m U.val 0 ω) := by
    funext ω
    exact Finset.mul_sum _ _ _
  rw [he]
  rwa [hsum] at hh

end
end ASDExplicitGamma.Scalar
