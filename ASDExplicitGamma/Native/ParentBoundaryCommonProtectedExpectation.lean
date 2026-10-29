module

public import ASDExplicitGamma.Native.ParentBoundaryCommonFullBank
public import ASDExplicitGamma.Native.ParentBoundaryCommonPowerExpectation
public import ASDExplicitGamma.Native.ParentBoundaryCommonCenterMoment64
public import ASDExplicitGamma.Native.ParentBoundaryCommonCenterHolder
public import ASDExplicitGamma.Native.ParentBoundaryCommonProtectedGenerator
public import ASDExplicitGamma.Native.ParentBoundaryCommonProtectedCoefficient
public import ASDExplicitGamma.Native.ParentBoundaryCommonProtectedFullBank
public import ASDExplicitGamma.Native.ParentBoundaryBandEnergy

/-! Sharp actual common-center shell expectation with the source center-error payment. -/

@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Gaussian Inverse Main Model Triadic Algsuperdiff.Section3
open scoped ENNReal
noncomputable section

/-- Every actual shell expectation has the sharp source Young/full-response
payment and the48v center term. Every bank, trace and Gaussian moment input
is discharged on the original correlated cutoff law. -/
theorem parent_boundary_common_protected_sharp_power_expectation
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (hg : M.gamma ≤ gammaZero)
    {P Q : TriadicCube 2} {d : ℕ} (hQ : Q ∈ descendantsAtDepth P d)
    (m n : ℤ) (hQm : Q.scale ≤ m) (hgap : m-Q.scale ≤ 5) (hmn : m ≤ n) (depth : ℕ) (hscale : Q.scale=n-(depth:ℤ))
    (height : ℕ) (hheight : 1 ≤ height) (hpast : ∀ k<n,nativeInductionState M h k)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (i : Fin height) :
    let Φ := squareTrace Q M.nu (Annealed.sigmaBar M n)
    let H := parentBoundaryCommonResponseDirections P Q
      (q3ModelAmplitude M h (n+((i.val+1:ℕ):ℤ))) (q3ModelLength (n+((i.val+1:ℕ):ℤ)))
    let X := parentBoundaryCommonCubeObserved hQ n height t
    (∫ ω,modelPowerHeatGenerator Φ H 20 (X ω) ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
      20*parentBoundaryCommonProtectedShellCoefficient M h P Q m n height i*
        (lpNorm (fun ω => Φ (X ω)) 20 (Cutoff.cutoffSampleLaw M).toMeasure)^19*
          ((26/25:ℝ)*(3683/2500:ℝ)^2*parentBoundaryBandTraceCap M height depth+
            (26*48:ℝ)*((Annealed.sigmaBar M n:ℝ)/(Annealed.sigmaBar M m:ℝ))*
              parentBoundaryBandVariance M h n height*(3683/2500:ℝ)^3) := by
  intro Φ H X
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let T := fun ω => Φ (X ω)
  let U := nativeSourceFullResponseTrace M Q n (n+(height:ℤ)) (fun _ => Real.sqrt t)
  let Z := parentBoundaryCommonSingletonHistory M Q m n height t
  let G0 := fun ω => parentBoundaryCommonCubeCenterValue P n height t ω/(Annealed.sigmaBar M n:ℝ)
  let G := fun ω => |G0 ω|
  let R := (Annealed.sigmaBar M n:ℝ)/(Annealed.sigmaBar M m:ℝ)
  let C := parentBoundaryCommonProtectedShellCoefficient M h P Q m n height i
  let V := parentBoundaryBandVariance M h n height
  let F := parentBoundaryBandTraceCap M height depth
  let b : ℝ := 3683/2500
  have hR : 0 ≤ R := div_nonneg (Annealed.sigmaBar_characterization M n).1.le
    (Annealed.sigmaBar_characterization M m).1.le
  have hC : 0 ≤ C := parent_boundary_common_protected_coefficient_nonneg M h P Q m n height i
  have hV : 0 ≤ V := by
    unfold V parentBoundaryBandVariance
    exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hF : 0 ≤ F := parent_boundary_band_trace_cap_nonneg M height depth
  have hT0 (ω) : 0 ≤ T ω := parent_boundary_common_square_trace_nonneg Q M.nu (Annealed.sigmaBar M n)
    M.nu_pos (Annealed.sigmaBar_characterization M n).1 (X ω)
  have hU0 (ω) : 0 ≤ U ω := by
    dsimp only [U]
    rw [parent_boundary_common_physical_full_eq]
    exact add_nonneg (parent_boundary_band_trace_nonneg M n height t Q ω) (by norm_num)
  have hZ0 (ω) : 0 ≤ Z ω := ENNReal.toReal_nonneg
  have hT20 : MemLp T 20 μ := by
    simpa only [show ENNReal.ofReal (20:ℝ)=(20:ℝ≥0∞) by norm_num] using
      (parent_boundary_common_cube_trace_memLp M h hM hQ n height hheight t 20 (by norm_num)).1
  have hU128 := parent_boundary_common_physical_full_L128 M h hM hg Q n height depth hscale hpast t ht1
  have hZ128cap := parent_boundary_common_singleton_history_L128 M h hM hg Q m n hQm hgap hmn height hpast t ht1
  have hZ128 : MemLp Z 128 μ := hZ128cap.trans_lt ENNReal.ofReal_lt_top
  have hZ256cap : eLpNorm Z 256 μ ≤ ENNReal.ofReal b :=
    parent_boundary_common_singleton_history_L256 M h hM hg Q m n hQm hgap hmn height hpast t ht1
  have hZ256 : MemLp Z 256 μ := hZ256cap.trans_lt ENNReal.ofReal_lt_top
  have hG064 : MemLp G0 64 μ := parent_boundary_common_cube_center_memLp M h hM P n height t 64 (by finiteness)
  have hG64 : MemLp G 64 μ := by simpa only [Real.norm_eq_abs] using hG064.norm
  have hGeq : eLpNorm G 64 μ=eLpNorm G0 64 μ := by
    simpa only [Real.norm_eq_abs] using eLpNorm_norm G0 hG064.aestronglyMeasurable
  have hGcap : eLpNorm G 64 μ ≤ ENNReal.ofReal (lpNorm G 64 μ) :=
    (ENNReal.ofReal_toReal hG64.eLpNorm_ne_top).symm.le
  have hGsq : (lpNorm G 64 μ)^2 ≤ 24*V := by
    have hb := parent_boundary_common_cube_center_L64_sq M h hM P n height t ht0
    have hi (i : Fin height) : nativeSourceBandIndex n height i=n+((i.val+1:ℕ):ℤ) := by
      dsimp only [nativeSourceBandIndex]
      push_cast
      ring
    have hv : ((∑ i : Fin height,(q3ModelAmplitude M h (nativeSourceBandIndex n height i))^2)/
        (Annealed.sigmaBar M n:ℝ)^2)=V := by
      dsimp only [V,parentBoundaryBandVariance]
      rw [Finset.sum_div]
      simp only [hi,div_pow]
    rw [hv] at hb
    change (eLpNorm G0 64 μ).toReal^2 ≤ 24*t*V at hb
    change (eLpNorm G 64 μ).toReal^2 ≤ _
    rw [hGeq]
    exact hb.trans (by nlinarith only [ht1,hV])
  have hmix := parent_boundary_rare_mixed_product_holder μ T U Z hT0 hU0 hZ0 hT20
    hU128.1 hZ128 b F (by norm_num [b]) hF hZ128cap hU128.2 ⟨1,by decide⟩
  have hcenter := parent_boundary_common_center_product_holder μ T G Z hT0 (fun _ => abs_nonneg _) hZ0
    hT20 hG64 hZ256 b (lpNorm G 64 μ) (by norm_num [b]) lpNorm_nonneg hZ256cap hGcap
  have hcenterCap : (∫ ω,T ω^19*Z ω^3*G ω^2 ∂μ) ≤ (lpNorm T 20 μ)^19*b^3*(24*V) :=
    hcenter.2.trans (mul_le_mul_of_nonneg_left hGsq (mul_nonneg (pow_nonneg lpNorm_nonneg _) (by norm_num [b])))
  have hGi := parent_boundary_common_cube_power_integrable M h hM hQ n height hheight t
    (q3ModelAmplitude M h (n+((i.val+1:ℕ):ℤ))) (q3ModelLength (n+((i.val+1:ℕ):ℤ)))
  have hpoint : ∀ᵐ ω ∂μ,modelPowerHeatGenerator Φ H 20 (X ω) ≤
      (20*C)*((26/25:ℝ)*(T ω^19*Z ω^2*U ω)+(52*R)*(T ω^19*Z ω^3*G ω^2)) := by
    filter_upwards [parent_boundary_common_protected_power_generator M h hM hg hQ m n hQm hgap hmn height hpast t ht1 i,
      parent_boundary_common_protected_full_bank_young M h hM hg hQ m n hQm hgap hmn height hpast t ht1 (1/25) (by norm_num)]
      with ω hgen hy
    dsimp only at hgen hy
    have hy' : T ω+4 ≤ (26/25:ℝ)*U ω+52*R*G ω^2*Z ω := by
      dsimp only [T,U,G,G0,R,X,Φ,Z]
      rw [sq_abs]
      convert hy using 1
      norm_num
    have hfac : 0 ≤ 20*T ω^19*C*Z ω^2 :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg (hT0 ω) 19)) hC) (sq_nonneg _)
    have hz := mul_le_mul_of_nonneg_left hy' hfac
    have hgen' : modelPowerHeatGenerator Φ H 20 (X ω) ≤ 20*T ω^19*C*Z ω^2*(T ω+4) :=
      hgen.trans_eq (by dsimp only [C,parentBoundaryCommonProtectedShellCoefficient,T,Z,Φ,X]; ring)
    exact hgen'.trans (hz.trans_eq (by ring))
  have hi := integral_mono_ae hGi
    (((hmix.1.const_mul (26/25)).add (hcenter.1.const_mul (52*R))).const_mul (20*C)) hpoint
  simp only [Pi.add_apply] at hi
  rw [integral_const_mul,integral_add (hmix.1.const_mul _) (hcenter.1.const_mul _),integral_const_mul,integral_const_mul] at hi
  calc
    _ ≤ (20*C)*((26/25:ℝ)*(∫ ω,T ω^19*Z ω^2*U ω ∂μ)+(52*R)*(∫ ω,T ω^19*Z ω^3*G ω^2 ∂μ)) := hi
    _ ≤ (20*C)*((26/25:ℝ)*((lpNorm T 20 μ)^19*b^2*F)+(52*R)*((lpNorm T 20 μ)^19*b^3*(24*V))) :=
      mul_le_mul_of_nonneg_left (add_le_add
        (mul_le_mul_of_nonneg_left hmix.2 (by norm_num))
        (mul_le_mul_of_nonneg_left hcenterCap (mul_nonneg (by norm_num) hR))) (mul_nonneg (by norm_num) hC)
    _ = _ := by dsimp only [C,T,F,R,V,b]; ring

end
end ASDExplicitGamma.Native
