module

public import ASDExplicitGamma.Native.ParentBoundaryCommonProtectedExpectation
public import ASDExplicitGamma.Native.ParentBoundaryCommonMomentDerivative
public import ASDExplicitGamma.Inverse.RawMomentRoot

/-! Actual common-center descendant root transport with the sharp source profile. -/

@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Gaussian Inverse Main Model Triadic Algsuperdiff.Section3
noncomputable section

/-- Actual physical finite-shell root drift, with the original full response
profile and the source48v center-error payment. -/
def parentBoundaryCommonProtectedRootDrift (M : ABKModel 2) (h : ℝ)
    (P Q : TriadicCube 2) (m n : ℤ) (height depth : ℕ) : ℝ :=
  (∑ i : Fin height,parentBoundaryCommonProtectedShellCoefficient M h P Q m n height i)*
    ((26/25:ℝ)*(3683/2500:ℝ)^2*parentBoundaryBandTraceCap M height depth+
      (26*48:ℝ)*((Annealed.sigmaBar M n:ℝ)/(Annealed.sigmaBar M m:ℝ))*
        parentBoundaryBandVariance M h n height*(3683/2500:ℝ)^3)

/-- Every term in the actual sharp root drift is nonnegative. -/
theorem parent_boundary_common_protected_root_drift_nonneg
    (M : ABKModel 2) (h : ℝ) (P Q : TriadicCube 2) (m n : ℤ) (height depth : ℕ) :
    0 ≤ parentBoundaryCommonProtectedRootDrift M h P Q m n height depth := by
  have hsum := Finset.sum_nonneg (s := Finset.univ) (fun (i : Fin height) _ =>
    parent_boundary_common_protected_coefficient_nonneg M h P Q m n height i)
  have hF := parent_boundary_band_trace_cap_nonneg M height depth
  have hV : 0 ≤ parentBoundaryBandVariance M h n height := by
    unfold parentBoundaryBandVariance
    exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hR := div_nonneg (Annealed.sigmaBar_characterization M n).1.le
    (Annealed.sigmaBar_characterization M m).1.le
  unfold parentBoundaryCommonProtectedRootDrift
  exact mul_nonneg hsum (add_nonneg (mul_nonneg (by norm_num) hF)
    (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hR) hV) (by norm_num)))

/-- Exact actual moment derivative with the sharp source profile. -/
theorem parent_boundary_common_protected_moment_derivative
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (hg : M.gamma ≤ gammaZero)
    {P Q : TriadicCube 2} {d : ℕ} (hQ : Q ∈ descendantsAtDepth P d)
    (m n : ℤ) (hQm : Q.scale ≤ m) (hgap : m-Q.scale ≤ 5) (hmn : m ≤ n) (depth : ℕ) (hscale : Q.scale=n-(depth:ℤ))
    (height : ℕ) (hheight : 1 ≤ height) (hpast : ∀ k<n,nativeInductionState M h k)
    (t : ℝ) (ht : t ∈ Set.Ioo (0:ℝ) 1) :
    deriv (parentBoundaryCommonTraceMoment M hQ n height) t ≤
      20*(parentBoundaryCommonTraceMoment M hQ n height t)^((19:ℝ)/20)*
        parentBoundaryCommonProtectedRootDrift M h P Q m n height depth := by
  let Φ := squareTrace Q M.nu (Annealed.sigmaBar M n)
  let X := parentBoundaryCommonCubeObserved hQ n height t
  let T := fun ω => Φ (X ω)
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let f := parentBoundaryCommonTraceMoment M hQ n height
  let H := fun i : Fin height => parentBoundaryCommonResponseDirections P Q
    (q3ModelAmplitude M h (n+((i.val+1:ℕ):ℤ))) (q3ModelLength (n+((i.val+1:ℕ):ℤ)))
  have hh := (parent_boundary_common_cube_p20_shell_heat M h hM hQ n height hheight).2 t ht.1
  have hfun : parentBoundaryCommonTraceMoment M hQ n height =
      parentBoundaryCommonCubeAverage M hQ n height (fun x => Φ x^(20:ℝ)) := rfl
  rw [hfun,hh.deriv]
  have hi (i : Fin height) : Integrable (fun ω => modelPowerHeatGenerator Φ (H i) 20 (X ω)) μ :=
    parent_boundary_common_cube_power_integrable M h hM hQ n height hheight t _ _
  rw [integral_finsetSum _ (fun i _ => hi i)]
  have hnorm : lpNorm T 20 μ=(f t)^((20:ℝ)⁻¹) :=
    parent_boundary_common_cube_trace_norm_eq_root M h hM hQ n height hheight t
  have hnorm19 : (lpNorm T 20 μ)^19=(f t)^((19:ℝ)/20) := by
    rw [hnorm,←Real.rpow_mul_natCast (parent_boundary_common_trace_moment_nonneg M hQ n height t)]
    norm_num
    rfl
  let A := (26/25:ℝ)*(3683/2500:ℝ)^2*parentBoundaryBandTraceCap M height depth+
    (26*48:ℝ)*((Annealed.sigmaBar M n:ℝ)/(Annealed.sigmaBar M m:ℝ))*
      parentBoundaryBandVariance M h n height*(3683/2500:ℝ)^3
  calc
    _ ≤ ∑ i : Fin height,20*parentBoundaryCommonProtectedShellCoefficient M h P Q m n height i*
        (f t)^((19:ℝ)/20)*A := by
      apply Finset.sum_le_sum
      intro i _
      have hb := parent_boundary_common_protected_sharp_power_expectation M h hM hg hQ m n hQm hgap hmn depth hscale height hheight hpast t ht.1.le ht.2.le i
      dsimp only at hb
      rw [hnorm19] at hb
      exact hb
    _ = _ := by
      dsimp only [parentBoundaryCommonProtectedRootDrift]
      rw [Finset.sum_mul,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      dsimp only [A,f,parentBoundaryCommonTraceMoment,Φ]
      ring

/-- Each actual common-centered descendant norm grows from its exact native
initial norm at the sharp source drift. No trace cap or differential premise
is assumed; all inputs were proved for this same cutoff law and true frame. -/
theorem parent_boundary_common_protected_root_transport
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (hg : M.gamma ≤ gammaZero)
    {P Q : TriadicCube 2} {d : ℕ} (hQ : Q ∈ descendantsAtDepth P d)
    (m n : ℤ) (hQm : Q.scale ≤ m) (hgap : m-Q.scale ≤ 5) (hmn : m ≤ n) (depth : ℕ) (hscale : Q.scale=n-(depth:ℤ))
    (height : ℕ) (hheight : 1 ≤ height) (hpast : ∀ k<n,nativeInductionState M h k)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    lpNorm (fun ω => squareTrace Q M.nu (Annealed.sigmaBar M n)
      (parentBoundaryCommonCubeObserved hQ n height t ω)) 20 (Cutoff.cutoffSampleLaw M).toMeasure ≤
      lpNorm (cutoffTraceDefect M n Q.scale) 20 (Cutoff.cutoffSampleLaw M).toMeasure+
        t*parentBoundaryCommonProtectedRootDrift M h P Q m n height depth := by
  let Φ := squareTrace Q M.nu (Annealed.sigmaBar M n)
  let f := parentBoundaryCommonTraceMoment M hQ n height
  let C := parentBoundaryCommonProtectedRootDrift M h P Q m n height depth
  have hheat := parent_boundary_common_cube_p20_shell_heat M h hM hQ n height hheight
  have hf : ContinuousOn f (Set.Icc (0:ℝ) 1) := hheat.1.mono (fun _ hx => hx.1)
  have hf0 : ∀ s ∈ Set.Icc (0:ℝ) 1,0 ≤ f s :=
    fun s _ => parent_boundary_common_trace_moment_nonneg M hQ n height s
  have hdf : ∀ s ∈ Set.Ioo (0:ℝ) 1,HasDerivAt f (deriv f s) s := by
    intro s hs
    have hd := hheat.2 s hs.1
    change HasDerivAt (parentBoundaryCommonCubeAverage M hQ n height (fun x => Φ x^(20:ℝ)))
      (deriv (parentBoundaryCommonCubeAverage M hQ n height (fun x => Φ x^(20:ℝ))) s) s
    rw [hd.deriv]
    exact hd
  have hC := parent_boundary_common_protected_root_drift_nonneg M h P Q m n height depth
  have hgen : ∀ s ∈ Set.Ioo (0:ℝ) 1,deriv f s ≤ 20*f s^((19:ℝ)/20)*C :=
    fun s hs => parent_boundary_common_protected_moment_derivative M h hM hg hQ m n hQm hgap hmn depth hscale height hheight hpast s hs
  have hr := raw_p20_moment_root_sub_le_integral hf hf0 hdf (fun _ _ => hC)
    (integrableOn_const (C := C) (by rw [Real.volume_Icc]; norm_num)) hgen
    (s := 0) (t := t) (by norm_num) ht0 ht1
  have hnormt : f t^((20:ℝ)⁻¹)=lpNorm (fun ω => Φ (parentBoundaryCommonCubeObserved hQ n height t ω))
      20 (Cutoff.cutoffSampleLaw M).toMeasure :=
    (parent_boundary_common_cube_trace_norm_eq_root M h hM hQ n height hheight t).symm
  have hnorm0 : f 0^((20:ℝ)⁻¹)=lpNorm (cutoffTraceDefect M n Q.scale) 20
      (Cutoff.cutoffSampleLaw M).toMeasure :=
    (parent_boundary_common_cube_trace_norm_eq_root M h hM hQ n height hheight 0).symm.trans
      (parent_boundary_common_cube_initial_norm M hQ n height)
  rw [hnormt,hnorm0,intervalIntegral.integral_const,sub_zero,smul_eq_mul] at hr
  exact (sub_le_iff_le_add.mp hr).trans_eq (add_comm _ _)

end
end ASDExplicitGamma.Native
