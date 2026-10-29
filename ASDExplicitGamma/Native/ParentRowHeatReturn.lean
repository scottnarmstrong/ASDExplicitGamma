module

public import ASDExplicitGamma.Native.ParentRowCertificates
public import ASDExplicitGamma.Native.GenericSourceBandMeanHeat
public import ASDExplicitGamma.Native.GenericSourceBandInitial

/-! Integrating the parent row while keeping the signed inverse contribution.
The physical generator-to-panel inequality is an explicit in-node input here;
the theorem must discharge it. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Gaussian Main Triadic Scalar Response Variational Algsuperdiff.Section3 Numerics.Native Set
noncomputable section

/-- The actual heat return once its complete parent generator has been paid.
Only the displayed generator inequality remains an assembly premise. -/
theorem parent_row_band_return_of_generator
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (m : ℤ)
    (hpast : ∀ k<m,nativeInductionState M h k) (j : Fin 16)
    (hrow : ∀ t ∈ Ioo (0:ℝ) 1,
      let n := m-((j.val+1:ℕ):ℤ)
      (∫ ω,nativeSourceBandMeanGenerator M h n (j.val+1) t ω
        ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
      theta M*(parentRowB0 j+nativePanelValue (parentRowFields j) t)-
        parentBoundaryBandDirichletEnergy M h n (j.val+1)*
          (parentBoundaryBandInverseMean M n (j.val+1) t-2)) :
    nativeSourceBandMean M (m-((j.val+1:ℕ):ℤ)) (j.val+1) 1 ≤
      theta M*((3/50:ℝ)+parentRowB0 j+
        (∫ t in (0:ℝ)..1,nativePanelValue (parentRowFields j) t)+
        parentBoundarySetupInverseCost j) := by
  let height := j.val+1
  let n := m-(height:ℤ)
  have hh0 : 1≤height := by dsimp [height]; omega
  have hn : n<m := by dsimp [n]; omega
  let B := theta M*parentRowB0 j
  let P := fun t => theta M*nativePanelValue (parentRowFields j) t
  let I := fun t => -parentBoundaryBandDirichletEnergy M h n height*
    (parentBoundaryBandInverseMean M n height t-2)
  let F := nativeSourceBandMean M n height
  let dF := fun t => ∫ ω,nativeSourceBandMeanGenerator M h n height t ω
    ∂(Cutoff.cutoffSampleLaw M).toMeasure
  have hheat := native_source_band_mean_heat_generator M h hM n height hh0
  have hinv := parent_boundary_inverse_band_generator_heat M h hM n height hh0
  have hI : IntervalIntegrable I volume 0 1 := by
    apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
    intro t ht
    exact continuousWithinAt_const.mul (((hinv.1 t ht.1).mono (fun _ hx => hx.1)).sub continuousWithinAt_const)
  have hP : IntervalIntegrable P volume 0 1 :=
    (parent_row_panel_integrable j).const_mul _
  have hB : IntervalIntegrable (fun _ : ℝ => B) volume 0 1 := intervalIntegrable_const
  have hbill : IntervalIntegrable (fun t => B+P t+I t) volume 0 1 := (hB.add hP).add hI
  have hd : ∀ t ∈ Ioo (0:ℝ) 1,dF t ≤ B+P t+I t := by
    intro t ht
    have hh := hrow t ht
    dsimp only at hh
    dsimp only [B,P,I,dF,n,height]
    convert hh using 1
    ring
  have hh := intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le (by norm_num : (0:ℝ) ≤ 1)
    (show ContinuousOn F (Icc 0 1) from hheat.1.mono (fun _ ht => ht.1))
    (fun t ht => (hheat.2 t ht.1).hasDerivWithinAt)
    ((intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)).mp hbill) hd
  have he : (∫ t in (0:ℝ)..1,B+P t+I t)=B+
      theta M*(∫ t in (0:ℝ)..1,nativePanelValue (parentRowFields j) t)+
      (∫ t in (0:ℝ)..1,I t) := by
    rw [intervalIntegral.integral_add (hB.add hP) hI,intervalIntegral.integral_add hB hP]
    simp only [P,intervalIntegral.integral_const,sub_zero,one_smul,intervalIntegral.integral_const_mul]
  rw [he] at hh
  have h0 := native_source_band_mean_zero_le M h n height (hpast n hn)
  have hi := parent_boundary_actual_inverse_setup_return M h hM hg m hpast j
  change (∫ t in (0:ℝ)..1,I t) ≤ _ at hi
  dsimp only [F,B,n,height] at hh h0 hi
  linarith only [hh,h0,hi]

end
end ASDExplicitGamma.Native
