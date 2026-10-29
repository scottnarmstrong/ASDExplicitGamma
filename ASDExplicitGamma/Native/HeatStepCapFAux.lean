module

public import ASDExplicitGamma.Native.HeatStepPasses
public import ASDExplicitGamma.Native.HeatVHEATBracketRefinedObservationGen
public import ASDExplicitGamma.Native.HeatVHEATBracketRefinedGeometryGen
public import ASDExplicitGamma.Native.HeatVHEATSourceAuxiliary
public import ASDExplicitGamma.Native.HeatVHEATRefinedAuxiliary
public import ASDExplicitGamma.Native.HeatVHEATCarrierRow
public import ASDExplicitGamma.Native.HeatVHEATBracketRefinedObservation
public import ASDExplicitGamma.Native.HeatVHEATDriftSourceClocks
public import ASDExplicitGamma.Native.HeatVHEATDriftSourceNorms
public import ASDExplicitGamma.Native.HeatVHEATDriftRefinedActual
public import ASDExplicitGamma.Native.HeatRefinedFamilyProfiles
public import ASDExplicitGamma.Native.HeatStepFrameNum
public import ASDExplicitGamma.Native.HeatStepIndivNum
public import ASDExplicitGamma.Native.HeatOldEndpoint
public import ASDExplicitGamma.Native.HeatRefinedRawProfile

/-! The auxiliary-center variance bound and the raw-envelope cap `F` for `ns` shells. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open MeasureTheory Homogenization ASDExplicitGamma.Gaussian ASDExplicitGamma.Model
open ASDExplicitGamma.Numerics.Native
open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open ProbabilityTheory
open scoped RealInnerProductSpace

section Aux

variable (ns : ℕ) [NeZero ns]

/-- The value variance of one selected shell at a depth-ten child center. -/
theorem nativeHeatStep_shellCenterVariance
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (m : ℤ) (i : nativeHeatQ3RefinedCarrierIndex) (d : Fin ns) :
    ∑' j,
      ((nativeHeatQ3RefinedCarrierFreshShellFamilyChosenGen M h hM m ns).factor d
        ((nativeHeatQ3RefinedCarrierFreshShellFamilyChosenGen M h hM m ns).direction d j)
        (nativeHeatQ3RefinedCarrierCenter m i)) ^ 2 =
      (q3ModelAmplitude M h
        (nativeHeatQ3RefinedCarrierPhysicalShellsGen m ns d)) ^ 2 := by
  classical
  let F := nativeHeatQ3RefinedCarrierFreshShellFamilyChosenGen M h hM m ns
  let p := finProdFinEquiv.symm i
  let Q := nativeHeatQ3RefinedCarrierChild m i
  let amp := q3ModelAmplitude M h
    (nativeHeatQ3RefinedCarrierPhysicalShellsGen m ns d)
  let qSection := q3Section amp (q3GridKernelScale 10 (d.val + 2)) h3Zero
    (q3GridRectangleCenter 10 p)
  let pts : Unit → nativeHeatQ3RefinedCarrierDomain m := fun _ =>
    nativeHeatQ3RefinedCarrierCenter m i
  let ptsVec : Unit → Vec 2 := fun _ => cubeCenter Q
  let weights : Unit → ℝ := fun _ => 1
  let sections : Unit → Gaussian.WhiteNoise := fun _ => qSection
  have hpts (u : Unit) : (pts u : Vec 2) = ptsVec u := by rfl
  have hcenter : cubeCenter Q =
      cubeCenter (nativeHeatQ3RefinedCarrierChild m (finProdFinEquiv p)) := by
    have hp : finProdFinEquiv p = i := Equiv.apply_symm_apply finProdFinEquiv i
    simp only [Q, nativeHeatQ3RefinedCarrierChild]
    rw [hp]
  have hpcenter : (q3GridRectangleCenter 10 p : Vec 2) =
      q3GridCenterVector 10 p := rfl
  have hkernelInner : q3ShellCovariance M h
      (nativeHeatQ3RefinedCarrierPhysicalShellsGen m ns d) (cubeCenter Q) (cubeCenter Q) =
      ⟪qSection, qSection⟫ := by
    have hk := (nativeHeatQ3RefinedCarrierShellKernel_eq_Gen ns) M h m d p p
    rw [← hcenter, ← hpcenter] at hk
    simpa [qSection, amp, Q] using hk
  have hkernel : q3ShellCovariance M h
      (nativeHeatQ3RefinedCarrierPhysicalShellsGen m ns d) (cubeCenter Q) (cubeCenter Q) =
      ‖qSection‖ ^ 2 := hkernelInner.trans (real_inner_self_eq_norm_sq qSection)
  have hvariance := (nativeHeatQ3RefinedCarrierShellObservationVariance_of_kernel_Gen ns)
    M h hM m d F pts ptsVec hpts weights sections
    (by intro u v; simpa only [ptsVec, sections] using hkernelInner)
  have hobs : ∑' j,
      (F.factor d (F.direction d j) (nativeHeatQ3RefinedCarrierCenter m i)) ^ 2 =
      ‖qSection‖ ^ 2 := by
    simpa [F, pts, weights, sections,
      nativeHeatQ3FiniteCenterObservation_apply,
      nativeHeatQ3FiniteSectionSum] using hvariance
  calc
    _ = ‖qSection‖ ^ 2 := hobs
    _ = amp ^ 2 := by
      rw [← hkernel, q3ShellCovariance_diagonal, q3ModelAmplitude_sq]

theorem nativeHeatStep_auxVariance_le
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (m : ℤ)
    (hstate : nativeInductionState M h (m + 1)) (t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1)
    (i : nativeHeatQ3RefinedCarrierIndex) :
    ((nativeHeatQ3RefinedCarrierSourceAuxCenterVarianceGen M m ns
        (nativeHeatQ3RefinedCarrierFreshShellFamilyChosenGen M h hM m ns)
        (nativeHeatTheta : ℝ) t i : NNReal) : ℝ) ≤
      (1 + (nativeHeatTheta : ℝ)) * ((ns : ℝ) * (heatVHEATDriftEGen ns) M) := by
  classical
  let F := nativeHeatQ3RefinedCarrierFreshShellFamilyChosenGen M h hM m ns
  let K := nativeHeatQ3RefinedCarrierDomain m
  let σ : ℝ := Annealed.sigmaBar M (m + 1)
  let E := nativeHeatQ3RefinedCarrierFreshShellSeriesFactorGen F
  let v := nativeHeatQ3RefinedCarrierFreshShellSeriesDirectionsGen F
  let θ : ℝ := nativeHeatTheta
  have hθ : 0 ≤ 1 + θ := by norm_num [θ, nativeHeatTheta]
  let A₀ : C(K, ℝ) →L[ℝ] ℝ :=
    (σ⁻¹) • ContinuousMap.evalCLM ℝ (nativeHeatQ3RefinedCarrierCenter m i)
  let Aₜ := nativeHeatQ3RefinedCarrierSourceAuxCenterObservationGen M m θ t i
  let q := ∑' j, (A₀ (E (v j))) ^ 2
  have hσ : 0 < σ := (Annealed.sigmaBar_characterization M (m + 1)).1
  have htime : 0 ≤ (1 + θ) * (1 - t) := mul_nonneg hθ (sub_nonneg.mpr ht.2)
  have hAₜ (f : C(K, ℝ)) : Aₜ f = Real.sqrt ((1 + θ) * (1 - t)) * A₀ f := by
    simp [Aₜ, A₀, nativeHeatQ3RefinedCarrierSourceAuxCenterObservationGen,
      nativeHeatQ3RefinedCarrierSourceAuxCenterObservation, σ, smul_eq_mul]
    field_simp
  have hscaled : ∑' j, (Aₜ (E (v j))) ^ 2 = ((1 + θ) * (1 - t)) * q := by
    calc
      _ = ∑' j, ((1 + θ) * (1 - t)) * (A₀ (E (v j))) ^ 2 := by
        apply tsum_congr
        intro j
        rw [hAₜ, mul_pow, Real.sq_sqrt htime]
      _ = _ := tsum_mul_left
  let B : ℝ →L[ℝ] ℝ →L[ℝ] ℝ :=
    (ContinuousLinearMap.id ℝ ℝ).smulRight (ContinuousLinearMap.id ℝ ℝ)
  have hsplit : q = ∑ d : Fin ns, ∑' j,
      (A₀ (F.factor d (F.direction d j))) ^ 2 := by
    let V : Fin ns → Type := fun _ => GaussianFactorL2 ℕ
    have hcomp : A₀.comp (finiteFactor V F.factor) =
        finiteFactor V (fun d => A₀.comp (F.factor d)) := by
      ext z
      simp [finiteFactor]
    have hmap :
        (fun j => A₀ (finiteFactor V F.factor (finiteDirections V F.direction j))) =
        (fun j => finiteFactor V (fun d => A₀.comp (F.factor d))
          (finiteDirections V F.direction j)) := by
      funext j
      have hh := congrArg (fun L => L (finiteDirections V F.direction j)) hcomp
      simpa only [ContinuousLinearMap.comp_apply] using hh
    have hmap_point j := congrFun hmap j
    have hbil := finiteFactor_bilinearTrace_eq_sum
      F.direction F.squareSummable (fun d => A₀.comp (F.factor d)) B
    change ∑' j, (A₀ (finiteFactor V F.factor
        (finiteDirections V F.direction j))) ^ 2 = _
    simp_rw [hmap_point]
    simpa [B, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
      smul_eq_mul, pow_two] using hbil
  have hshell (d : Fin ns) :
      ∑' j, (A₀ (F.factor d (F.direction d j))) ^ 2 =
        (heatVHEATDriftVarianceGen ns) M h (m + 1) d := by
    have hcenter := nativeHeatStep_shellCenterVariance ns M h hM m i d
    have hscale :
        ∑' j, (A₀ (F.factor d (F.direction d j))) ^ 2 =
          (q3ModelAmplitude M h
            (nativeHeatQ3RefinedCarrierPhysicalShellsGen m ns d)) ^ 2 / σ ^ 2 := by
      dsimp [A₀]
      simp only [ContinuousLinearMap.smul_apply, smul_eq_mul,
        ContinuousMap.evalCLM_apply]
      calc
        _ = (σ⁻¹) ^ 2 * ∑' j,
            ((F.factor d (F.direction d j))
              (nativeHeatQ3RefinedCarrierCenter m i)) ^ 2 := by
              calc
                _ = ∑' j, (σ⁻¹) ^ 2 *
                    ((F.factor d (F.direction d j))
                      (nativeHeatQ3RefinedCarrierCenter m i)) ^ 2 := by
                      apply tsum_congr
                      intro j
                      ring
                _ = _ := tsum_mul_left
        _ = _ := by
              rw [hcenter]
              field_simp [ne_of_gt hσ]
    rw [hscale]
    have hlabel : nativeHeatQ3RefinedCarrierPhysicalShellsGen m ns d =
        (m + 1) + ((d.val + 1 : ℕ) : ℤ) := by
      simp [nativeHeatQ3RefinedCarrierPhysicalShellsGen]
      omega
    simp [heatVHEATDriftVarianceGen, σ, hlabel]
  have hq : q = ∑ d : Fin ns, (heatVHEATDriftVarianceGen ns) M h (m + 1) d := by
    rw [hsplit]
    exact Finset.sum_congr rfl fun d _ => hshell d
  have hvarianceNonneg (d : Fin ns) :
      0 ≤ (heatVHEATDriftVarianceGen ns) M h (m + 1) d :=
    ((heatVHEATDrift_source_variance_le_Gen ns) M h (m + 1) hstate d).1
  have hvarianceCap (d : Fin ns) :
      (heatVHEATDriftVarianceGen ns) M h (m + 1) d ≤ (heatVHEATDriftEGen ns) M :=
    ((heatVHEATDrift_source_variance_le_Gen ns) M h (m + 1) hstate d).2
  have hqnonneg : 0 ≤ q := by rw [hq]; exact Finset.sum_nonneg fun d _ => hvarianceNonneg d
  have hqcap : q ≤ (ns : ℝ) * (heatVHEATDriftEGen ns) M := by
    rw [hq]
    calc
      _ ≤ ∑ d : Fin ns, (heatVHEATDriftEGen ns) M :=
        Finset.sum_le_sum (fun d _ => hvarianceCap d)
      _ = (ns : ℝ) * (heatVHEATDriftEGen ns) M := by simp
  have hqtime : ((1 + θ) * (1 - t)) * q ≤ (1 + θ) * q := by
    have h1 : (1 - t) ≤ 1 := by linarith [ht.1]
    have := mul_le_mul_of_nonneg_right h1 hθ
    nlinarith [mul_le_mul_of_nonneg_right this hqnonneg]
  have hcast :
      ((nativeHeatQ3RefinedCarrierSourceAuxCenterVarianceGen M m ns F θ t i : NNReal) : ℝ) =
        ∑' j, (Aₜ (E (v j))) ^ 2 := by
    rw [nativeHeatQ3RefinedCarrierSourceAuxCenterVarianceGen]
    rw [Real.coe_toNNReal _ (tsum_nonneg fun j => sq_nonneg _)]
  change ((nativeHeatQ3RefinedCarrierSourceAuxCenterVarianceGen M m ns F θ t i : NNReal) : ℝ) ≤ _
  rw [hcast, hscaled]
  exact hqtime.trans (mul_le_mul_of_nonneg_left hqcap hθ)

theorem nativeHeatStep_auxVarianceSup_le
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (m : ℤ)
    (hstate : nativeInductionState M h (m + 1)) (t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1) :
    heatVHEATDriftAuxVariance Finset.univ
      (nativeHeatQ3RefinedCarrierSourceAuxCenterVarianceGen M m ns
        (nativeHeatQ3RefinedCarrierFreshShellFamilyChosenGen M h hM m ns)
        (nativeHeatTheta : ℝ) t) ≤
      (1 + (nativeHeatTheta : ℝ)) * ((ns : ℝ) * (heatVHEATDriftEGen ns) M) := by
  classical
  have hE : 0 ≤ (1 + (nativeHeatTheta : ℝ)) * ((ns : ℝ) * (heatVHEATDriftEGen ns) M) := by
    have : 0 ≤ (heatVHEATDriftEGen ns) M := by
      unfold heatVHEATDriftEGen
      exact mul_nonneg (mul_nonneg (by norm_num) M.shellPrefix.gamma_pos.le)
        (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) _).le
    have h0 : (0 : ℝ) ≤ 1 + (nativeHeatTheta : ℝ) := by norm_num [nativeHeatTheta]
    positivity
  rw [heatVHEATDriftAuxVariance]
  have hsup : Finset.univ.sup (nativeHeatQ3RefinedCarrierSourceAuxCenterVarianceGen M m ns
      (nativeHeatQ3RefinedCarrierFreshShellFamilyChosenGen M h hM m ns)
      (nativeHeatTheta : ℝ) t) ≤
      Real.toNNReal ((1 + (nativeHeatTheta : ℝ)) * ((ns : ℝ) * (heatVHEATDriftEGen ns) M)) := by
    apply Finset.sup_le
    intro i _
    have := nativeHeatStep_auxVariance_le ns M h hM m hstate t ht i
    have h' : ((nativeHeatQ3RefinedCarrierSourceAuxCenterVarianceGen M m ns
        (nativeHeatQ3RefinedCarrierFreshShellFamilyChosenGen M h hM m ns)
        (nativeHeatTheta : ℝ) t i : NNReal) : ℝ) ≤
        (Real.toNNReal ((1 + (nativeHeatTheta : ℝ)) * ((ns : ℝ) * (heatVHEATDriftEGen ns) M)) : ℝ) := by
      rw [Real.coe_toNNReal _ hE]; exact this
    exact_mod_cast h'
  calc _ ≤ (Real.toNNReal ((1 + (nativeHeatTheta : ℝ)) * ((ns : ℝ) * (heatVHEATDriftEGen ns) M)) : ℝ) := by
        exact_mod_cast hsup
    _ = _ := Real.coe_toNNReal _ hE

end Aux

/-- A checked outward root dominates the real square root. -/
theorem nativeHeatStep_sqrt_le_rootUp (q : ℚ) (hq : nativeRootValid q 2 = true) :
    Real.sqrt (q : ℝ) ≤ (nativeRootUp q : ℝ) := by
  have := nativeRoot_sound hq
  rw [Real.sqrt_eq_rpow]
  simpa using this

theorem nativeHeatStep_rawCap (ns : ℕ) [NeZero ns] (hns9 : 9 ≤ ns) (hns160 : ns ≤ 160)
    (hnum : NativeHeatStepPassNum ns) (hfr : NativeHeatStepFrameNum ns)
    (hind : NativeHeatStepIndivNum ns hns160) (hgen : NativeHeatGenNum ns)
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (hg : M.gamma ≤ gammaZero) (m : ℤ)
    (hstate : nativeInductionState M h (m + 1)) :
    ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      heatRefinedRawEnvelope ns
        (heatVHEATDriftAuxVariance Finset.univ
          (nativeHeatQ3RefinedCarrierSourceAuxCenterVarianceGen M m ns
            (nativeHeatQ3RefinedCarrierFreshShellFamilyChosenGen M h hM m ns)
            (nativeHeatTheta : ℝ) t)) ≤ ((nativeHeatFramesGen ns).raw : ℝ) := by
  intro t ht
  have hg0 := M.shellPrefix.gamma_pos.le
  have hsup := nativeHeatStep_auxVarianceSup_le ns M h hM m hstate t ⟨ht.1.le, ht.2.le⟩
  have heold : (heatVHEATDriftEGen ns) M ≤ ((nativeHeatOldRowGen ns).e : ℝ) := by
    unfold heatVHEATDriftEGen
    exact hgen.efactor M.gamma hg0 hg
  have hθ : (0 : ℝ) ≤ 1 + (nativeHeatTheta : ℝ) := by norm_num [nativeHeatTheta]
  have hVar : (1 + (nativeHeatTheta : ℝ)) * ((ns : ℝ) * (heatVHEATDriftEGen ns) M) ≤
      (nativeHeatGenVariance ns : ℝ) := by
    rw [nativeHeatGenVariance_eq]
    have h1 := (Rat.cast_le (K := ℝ)).2
      (nativeUp_ge ((1 + nativeHeatTheta) * (nativeHeatOldRowGen ns).e * (ns : ℚ)))
    push_cast at h1
    refine le_trans ?_ h1
    have : (ns : ℝ) * (heatVHEATDriftEGen ns) M ≤ (ns : ℝ) * ((nativeHeatOldRowGen ns).e : ℝ) :=
      mul_le_mul_of_nonneg_left heold (by positivity)
    nlinarith [mul_le_mul_of_nonneg_left this hθ]
  have hV := hsup.trans hVar
  have hBn : (0 : ℝ) ≤ (nativeHeatB : ℝ) := by
    have : (0 : ℚ) ≤ nativeHeatB := by
      norm_num [nativeHeatB, nativeHeatRQ, nativeE, nativeGamma, nativeB]
    exact_mod_cast this
  have hV0 : 0 ≤ heatVHEATDriftAuxVariance Finset.univ
      (nativeHeatQ3RefinedCarrierSourceAuxCenterVarianceGen M m ns
        (nativeHeatQ3RefinedCarrierFreshShellFamilyChosenGen M h hM m ns)
        (nativeHeatTheta : ℝ) t) := by
    unfold heatVHEATDriftAuxVariance; exact NNReal.coe_nonneg _
  -- unfold the frame
  have hraw : ((nativeHeatFramesGen ns).raw : ℚ) =
      nativeUp ((nativeRootUp (nativeHeatRQ * (nativeHeatOldRowGen ns).f) +
        nativeRootUp (2 * nativeHeatB * 255 * nativeHeatGenVariance ns)) ^ 2) := by
    simp [nativeHeatFramesGen, nativeHeatFrames]
  have hcap : nativeSourceGenericFullResponseCap (17 / 50000) (ns + 1) ≤
      ((nativeHeatOldRowGen ns).f : ℝ) := by
    have := heat_old_full_endpoint (ns + 1)
    rwa [hind.old_source] at this
  have hRQ : (0 : ℝ) ≤ nativeHeatRQ := by norm_num [nativeHeatRQ, nativeE, nativeGamma]
  have t1 : Real.sqrt ((nativeHeatRQ : ℝ) * nativeSourceGenericFullResponseCap (17 / 50000) (ns + 1)) ≤
      (nativeRootUp (nativeHeatRQ * (nativeHeatOldRowGen ns).f) : ℝ) := by
    refine le_trans (Real.sqrt_le_sqrt ?_) (nativeHeatStep_sqrt_le_rootUp _ hfr.f_root)
    push_cast
    exact mul_le_mul_of_nonneg_left hcap hRQ
  have hB : (2 * ((3683 / 2500 : ℝ) + 3 / 10 ^ 46)) ≤ 2 * (nativeHeatB : ℝ) := by
    have : (3683 / 2500 + 3 / 10 ^ 46 : ℚ) ≤ nativeHeatB := by
      norm_num [nativeHeatB, nativeHeatRQ, nativeE, nativeGamma, nativeB]
    have h2 := (Rat.cast_le (K := ℝ)).2 this
    push_cast at h2
    linarith
  have t2 : Real.sqrt (2 * ((3683 / 2500 : ℝ) + 3 / 10 ^ 46) * 255 * heatVHEATDriftAuxVariance Finset.univ
      (nativeHeatQ3RefinedCarrierSourceAuxCenterVarianceGen M m ns
        (nativeHeatQ3RefinedCarrierFreshShellFamilyChosenGen M h hM m ns)
        (nativeHeatTheta : ℝ) t)) ≤
      (nativeRootUp (2 * nativeHeatB * 255 * nativeHeatGenVariance ns) : ℝ) := by
    refine le_trans (Real.sqrt_le_sqrt ?_) (nativeHeatStep_sqrt_le_rootUp _ hfr.fr_root)
    push_cast
    have hvar0 : (0 : ℝ) ≤ (nativeHeatGenVariance ns : ℝ) := hV0.trans hV
    have e1 := mul_le_mul_of_nonneg_right hB (mul_nonneg (by norm_num : (0:ℝ) ≤ 255) hV0)
    have e2 := mul_le_mul_of_nonneg_left hV (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hBn) (by norm_num : (0:ℝ) ≤ 255))
    nlinarith [e1, e2]
  unfold heatRefinedRawEnvelope
  have hs0 : 0 ≤ Real.sqrt ((nativeHeatRQ : ℝ) * nativeSourceGenericFullResponseCap (17 / 50000) (ns + 1)) +
      Real.sqrt (2 * ((3683 / 2500 : ℝ) + 3 / 10 ^ 46) * 255 * heatVHEATDriftAuxVariance Finset.univ
      (nativeHeatQ3RefinedCarrierSourceAuxCenterVarianceGen M m ns
        (nativeHeatQ3RefinedCarrierFreshShellFamilyChosenGen M h hM m ns)
        (nativeHeatTheta : ℝ) t)) := by
    refine add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hsq := pow_le_pow_left₀ hs0 (add_le_add t1 t2) 2
  have hnu := (Rat.cast_le (K := ℝ)).2
    (nativeUp_ge ((nativeRootUp (nativeHeatRQ * (nativeHeatOldRowGen ns).f) +
        nativeRootUp (2 * nativeHeatB * 255 * nativeHeatGenVariance ns)) ^ 2))
  rw [← hraw] at hnu
  push_cast at hnu hsq ⊢
  exact hsq.trans hnu

end ASDExplicitGamma.Native

end
