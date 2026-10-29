module

public import ASDExplicitGamma.Inverse.AssemblyReferenceInverse
public import ASDExplicitGamma.Inverse.AssemblyErrorMoments
public import ASDExplicitGamma.Inverse.AssemblySelectedClock
public import ASDExplicitGamma.Inverse.BankLpArithmetic
public import ASDExplicitGamma.Inverse.BankResponseMeasurable

/-! Complete inverse moments in the source root frame, before numerical extraction. -/

@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian
open scoped ENNReal
noncomputable section

/-- The positive error is measurable independently of its moment bounds. -/
theorem assembly_inverse_error_measurable (M : ABKModel 2) (Q : TriadicCube 2) (H0 : ℕ) :
    Measurable (assemblyInverseError M Q H0) := by
  apply Measurable.const_mul
  apply Measurable.tsum
  intro hk
  apply Measurable.const_mul
  have hD : Measurable (fun ω => ∑ e : Fin 3, ENNReal.ofReal
      (resetDensityExcess M Q H0 resetAllOrderTau (waveGateEta .allOrder)
        (allOrderDensity:ℝ) 1324 2 hk e ω)) := by
    apply Finset.measurable_sum
    intro e _
    exact (reset_density_excess_measurable M Q H0 _ _ _ _ _ hk e).ennreal_ofReal
  exact (reset_root_matrix_positive_error_measurable M Q (H0+hk.1) (hk.2+1)
    resetAllOrderTau).ennreal_ofReal.add (hD.const_mul _)

/-- The reference inverse is a deterministic multiple of the actual old-frame response. -/
theorem assembly_inverse_eq_ratio (M : ABKModel 2) (Q : TriadicCube 2)
    (m N ref : ℤ) (weights : ℤ → ℝ) (ω : Cutoff.CutoffSample 2) :
    rootInverseObservable M Q m N ref weights ω =
      ((Annealed.sigmaBar M ref:ℝ)/(Annealed.sigmaBar M m:ℝ))*
        rootInverseResponse M Q m N weights ω := by
  have hs := (Annealed.sigmaBar_characterization M m).1.ne'
  unfold rootInverseObservable rootInverseResponse
  field_simp

theorem assembly_inverse_measurable (M : ABKModel 2) (Q : TriadicCube 2)
    (m N ref : ℤ) (weights : ℤ → ℝ) :
    Measurable (rootInverseObservable M Q m N ref weights) := by
  have he : rootInverseObservable M Q m N ref weights =
      fun ω => ((Annealed.sigmaBar M ref:ℝ)/(Annealed.sigmaBar M m:ℝ))*
        rootInverseResponse M Q m N weights ω := by
    funext ω
    exact assembly_inverse_eq_ratio M Q m N ref weights ω
  rw [he]
  exact (root_inverse_response_measurable M m N weights Q).const_mul _

/-- All-order inverse norm bound with the complete exact selected clock and
positive-error budgets; no response-moment assumption remains. -/
theorem assembly_root_inverse_Lp (M : ABKModel 2) (h : ℝ)
    (hM : PlanarQ3Gaussian M h) (hγ : M.gamma ≤ gammaZero)
    (Q : TriadicCube 2) (p : ℝ) (hp : 2 ≤ p)
    (hpast : ∀ n : ℤ, n ≤ Q.scale-342-12*orderBand p → nativeInductionState M h n)
    (N : ℤ) (hN : Q.scale-1 ≤ N) (weights : ℤ → ℝ)
    (hw : ∀ n ∈ Finset.Ioc (protectedOldLabel Q.scale (orderBand p)) N,
      0 ≤ weights n ∧ weights n ≤ 1) :
    eLpNorm (rootInverseObservable M Q (protectedOldLabel Q.scale (orderBand p))
      N (Q.scale-1) weights) (ENNReal.ofReal p) (Cutoff.cutoffSampleLaw M).toMeasure ≤
        ENNReal.ofReal (assemblyInverseLi M.gamma)*
          ENNReal.ofReal (assemblySelectedClockBudget M.gamma p (heightEntrance (orderBand p)))+
            ENNReal.ofReal (assemblyMatrixBudget M.gamma p (heightEntrance (orderBand p)+5)+
              assemblyDensityBudget M.gamma (orderBand p) (heightEntrance (orderBand p)+5)) := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let H := fun ω => ENNReal.ofReal ((3:ℝ)^(2*M.gamma*
    ((resetQ3StoppedHeight M Q (orderBand p) ω:ℝ)-38)))
  let E := assemblyInverseError M Q (heightEntrance (orderBand p)+5)
  let A := ENNReal.ofReal (assemblyInverseLi M.gamma)
  let I := rootInverseObservable M Q (protectedOldLabel Q.scale (orderBand p)) N (Q.scale-1) weights
  have hI := assembly_inverse_measurable M Q (protectedOldLabel Q.scale (orderBand p)) N (Q.scale-1) weights
  have hIn (ω : Cutoff.CutoffSample 2) : 0 ≤ I ω :=
    mul_nonneg (Annealed.sigmaBar_characterization M _).1.le (norm_nonneg _)
  have hHm : Measurable H := by
    have hnat : Measurable (fun n : ℕ => ENNReal.ofReal ((3:ℝ)^(2*M.gamma*((n:ℝ)-38)))) :=
      measurable_of_countable _
    exact hnat.comp (q3_stopped_height_measurable M Q
      (heightEntrance (orderBand p)+5) resetAllOrderTau (waveGateEta .allOrder))
  have hEm := assembly_inverse_error_measurable M Q (heightEntrance (orderBand p)+5)
  have hdom := assembly_q3_root_framed_inverse_bound M h hM hγ Q p hp hpast N hN weights hw
  have hnorm : eLpNorm (fun ω => ENNReal.ofReal (I ω)) (ENNReal.ofReal p) μ ≤
      eLpNorm (fun ω => H ω*A+E ω) (ENNReal.ofReal p) μ := by
    apply eLpNorm_mono_enorm_ae hI.ennreal_ofReal.aestronglyMeasurable
    filter_upwards [hdom] with ω hω
    simpa only [enorm_eq_self,H,A,E,mul_comm] using hω
  change eLpNorm (ENNReal.ofReal ∘ I) (ENNReal.ofReal p) μ ≤ _ at hnorm
  rw [eLpNorm_ofReal _ (Filter.Eventually.of_forall hIn)] at hnorm
  have ha := bank_ennreal_affine_Lp_bound μ (ENNReal.ofReal p) 1 A H E ENNReal.one_ne_top
    ENNReal.ofReal_ne_top hHm hEm (ENNReal.one_le_ofReal.mpr (by linarith only [hp]))
  simp only [mul_one,one_mul] at ha
  have hclock := assembly_q3_selected_clock_Lp M h hM hγ Q p hp hpast
  have hclock' : eLpNorm H (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal (assemblySelectedClockBudget M.gamma p (heightEntrance (orderBand p))) := by
    change eLpNorm (ENNReal.ofReal ∘ (fun ω => (3:ℝ)^(2*M.gamma*
      ((resetQ3StoppedHeight M Q (orderBand p) ω:ℝ)-38)))) (ENNReal.ofReal p) μ ≤ _
    rw [eLpNorm_ofReal _ (Filter.Eventually.of_forall fun _ => by positivity)]
    exact hclock
  have herr := assembly_inverse_error_Lp M h hM hγ Q p hp
    (heightEntrance (orderBand p)+5) le_rfl hpast
  exact hnorm.trans (ha.trans (add_le_add (mul_le_mul_right hclock' A) herr))

/-- Changing to any full-law reference frame pays precisely the absolute
root-reference gap, independently of the protected entrance. -/
theorem assembly_reference_inverse_Lp (M : ABKModel 2) (h : ℝ)
    (hM : PlanarQ3Gaussian M h) (hγ : M.gamma ≤ gammaZero)
    (Q : TriadicCube 2) (p : ℝ) (hp : 2 ≤ p)
    (hpast : ∀ n : ℤ, n ≤ Q.scale-342-12*orderBand p → nativeInductionState M h n)
    (N ref : ℤ) (hN : Q.scale-1 ≤ N) (weights : ℤ → ℝ)
    (hw : ∀ n ∈ Finset.Ioc (protectedOldLabel Q.scale (orderBand p)) N,
      0 ≤ weights n ∧ weights n ≤ 1) :
    eLpNorm (rootInverseObservable M Q (protectedOldLabel Q.scale (orderBand p))
      N ref weights) (ENNReal.ofReal p) (Cutoff.cutoffSampleLaw M).toMeasure ≤
        ENNReal.ofReal ((3:ℝ)^(2*M.gamma*|((ref-Q.scale+1:ℤ):ℝ)|))*
          (ENNReal.ofReal (assemblyInverseLi M.gamma)*
            ENNReal.ofReal (assemblySelectedClockBudget M.gamma p (heightEntrance (orderBand p)))+
              ENNReal.ofReal (assemblyMatrixBudget M.gamma p (heightEntrance (orderBand p)+5)+
                assemblyDensityBudget M.gamma (orderBand p) (heightEntrance (orderBand p)+5))) := by
  let c := (Annealed.sigmaBar M ref:ℝ)/(Annealed.sigmaBar M (Q.scale-1):ℝ)
  have hc : 0 ≤ c := div_nonneg (Annealed.sigmaBar_characterization M ref).1.le
    (Annealed.sigmaBar_characterization M (Q.scale-1)).1.le
  have he : rootInverseObservable M Q (protectedOldLabel Q.scale (orderBand p)) N ref weights =
      c • rootInverseObservable M Q (protectedOldLabel Q.scale (orderBand p)) N (Q.scale-1) weights := by
    funext ω
    dsimp only [rootInverseObservable,Pi.smul_apply,smul_eq_mul,c]
    have hs := (Annealed.sigmaBar_characterization M (Q.scale-1)).1.ne'
    field_simp
  rw [he,eLpNorm_const_smul,Real.enorm_eq_ofReal hc]
  have hc' : c ≤ (3:ℝ)^(2*M.gamma*|((ref-Q.scale+1:ℤ):ℝ)|) := by
    have hh := true_frame_ratio_le M ref (Q.scale-1)
    rw [show ref-(Q.scale-1)=ref-Q.scale+1 by omega] at hh
    exact hh
  exact mul_le_mul (ENNReal.ofReal_le_ofReal hc')
    (assembly_root_inverse_Lp M h hM hγ Q p hp hpast N hN weights hw) bot_le bot_le

end
end ASDExplicitGamma.Inverse
