module

public import ASDExplicitGamma.Scalar.OldHessianTrialStrongTraceCap

/-! Sharp finite-moment bounds on the actual scalar source trace average. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational Gaussian Inverse Main Cold Algsuperdiff.Section3
open scoped ENNReal
noncomputable section
attribute [local irreducible] Homogenization.descendantsAtDepth

/-- The literal fixed-frame source trace on the large scalar parent. -/
def oldHessianSourceTrace (M : ABKModel 2) (m : ℤ) (r : ℕ)
    (ω : Cutoff.CutoffSample 2) : ℝ :=
  descendantsAverage (originCube 2 (m+129)) (129+r) (fun U =>
    traceDefect (openCubeSet U)
      (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m)
        (oldHessianOldOpenCoefficient (m+129) m ω)) 1)

theorem old_hessian_source_trace_nonneg (M : ABKModel 2) (m : ℤ) (r : ℕ)
    (ω : Cutoff.CutoffSample 2) : 0≤oldHessianSourceTrace M m r ω := by
  unfold oldHessianSourceTrace
  rw [old_hessian_old_open_trace_sequence]
  exact raw_weak_trace_sequence_nonneg M m (originCube 2 (m+129)) 0 (by norm_num) ω (129+r)

/-- The actual large-parent spatial average inherits the sharp completed
strong20 moment cap with no spatial population loss. -/
theorem old_hessian_source_trace_L20
    (M : ABKModel 2) (h : ℝ) (m : ℤ) (hstate : nativeInductionState M h m)
    (r : ℕ) (hr : r≤5) :
    eLpNorm (oldHessianSourceTrace M m r) 20 (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal (theta M*((5423/2500:ℝ)/(1-19/25))) := by
  let Q := originCube 2 (m+129)
  let depth := 129+r
  let I := SquareCells Q depth
  let C := theta M*((5423/2500:ℝ)/(1-19/25))
  let d : ℝ := (descendantsAtDepth Q depth).card
  have hd : 0<d := by
    dsimp [d]
    exact_mod_cast Finset.card_pos.mpr (descendantsAtDepth_nonempty Q depth)
  have hC : 0≤C := mul_nonneg (cold_theta_pos M).le (by norm_num)
  have horigin := old_hessian_origin_strong_trace_cap M h m hstate r hr
  have hcell (U : I) : eLpNorm (rawCubeFourLoadTrace M m U.val 0) 20
      (Cutoff.cutoffSampleLaw M).toMeasure ≤ ENNReal.ofReal C := by
    have hz : rawCubeFourLoadTrace M m U.val 0=coldNativeCellTrace M m U.val := by
      funext ω
      change traceDefect (cubeSet U.val) (Model.partialInsertedCoefficient M m 0 ω).toFun
        (Annealed.sigmaBar M m)=_
      have he : (Model.partialInsertedCoefficient M m 0 ω).toFun=
          (Cutoff.coefficientCutoff M.nu m ω).toFun :=
        funext (fun x => old_hessian_partial_zero M m ω x)
      rw [he]
      rfl
    rw [hz,(coldNativeCellTrace_identDistrib M m U.val).eLpNorm_eq]
    have hs := scale_eq_sub_of_mem_descendantsAtDepth U.property
    have hscale : U.val.scale=m-(r:ℤ) := by
      change U.val.scale=m+129-(depth:ℤ) at hs
      dsimp only [depth] at hs
      omega
    rw [hscale]
    exact horigin
  have hh := finite_density_sum_Lp (Cutoff.cutoffSampleLaw M).toMeasure 20
    (by norm_num) (fun U : I => rawCubeFourLoadTrace M m U.val 0)
    (fun _ => d⁻¹) (fun _ => C) (fun _ => inv_nonneg.mpr hd.le) (fun _ => hC) hcell
  have hcard : Fintype.card I=(descendantsAtDepth Q depth).card := by simp [I,SquareCells]
  have hsum : (∑ _U : I,d⁻¹*C)=C := by
    simp only [Finset.sum_const,Finset.card_univ,hcard,nsmul_eq_mul]
    change d*(d⁻¹*C)=C
    rw [←mul_assoc,mul_inv_cancel₀ hd.ne',one_mul]
  have he : oldHessianSourceTrace M m r=
      (fun ω => ∑ U : I,d⁻¹*rawCubeFourLoadTrace M m U.val 0 ω) := by
    funext ω
    unfold oldHessianSourceTrace
    rw [old_hessian_old_open_trace_sequence]
    exact Finset.mul_sum _ _ _
  rw [he]
  rwa [hsum] at hh

end
end ASDExplicitGamma.Scalar
