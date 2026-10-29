module

public import ASDExplicitGamma.Cold.NativeLocalPointSigma
public import Mathlib.MeasureTheory.Integral.Prod

/-! # Sharp stream-point restrictions contain the genuine local integral sigma algebra -/

@[expose] public section
noncomputable section
open MeasureTheory Homogenization Algsuperdiff.Section3
open Algsuperdiff.Frozen.Assumptions
namespace ASDExplicitGamma.Cold

/-- Every supported actual local entry test is measurable from the sharp stream-point restriction.
The finite-volume probe region makes the parameter integral legitimate even for unbounded U. -/
theorem cold_entryTest_point_measurable {U : Set (Vec 2)} (hU : MeasurableSet U)
    (i k : Fin 2) {φ : Vec 2 → ℝ} (hφ : IsProbeR φ) (hsupp : Function.support φ ⊆ U) :
    @Measurable (ShellField 2) ℝ (coldStreamPointSigma U) (borel ℝ)
      (fun j => entryTestR i k φ (ShellField.forgetShell j)) := by
  let S := U ∩ tsupport φ
  have hS : MeasurableSet S := hU.inter (isClosed_tsupport φ).measurableSet
  let instColdPointDomain : MeasurableSpace (ShellField 2) := coldStreamPointSigma U
  let instColdProbeMeasure : MeasureSpace S := Measure.Subtype.measureSpace
  let instColdProbeFinite : IsFiniteMeasure (volume : Measure S) := ⟨by
    rw [Measure.Subtype.volume_univ hS.nullMeasurableSet]
    exact (measure_mono (Set.inter_subset_right : S ⊆ tsupport φ)).trans_lt hφ.hasCompactSupport.measure_lt_top⟩
  have hcont (j : ShellField 2) : Continuous (fun x : S => j x.val i k) :=
    ((continuous_apply k).comp ((continuous_apply i).comp j.1.1.continuous)).comp continuous_subtype_val
  have hpoint (x : S) : Measurable (fun j : ShellField 2 => j x.val i k) :=
    cold_matrixPoint_measurable U ⟨x.val,x.property.1⟩ i k
  have hjoint : Measurable (fun p : S × ShellField 2 => p.2 p.1.val i k) :=
    measurable_uncurry_of_continuous_of_measurable hcont hpoint
  have hF : Measurable (fun p : ShellField 2 × S => p.1 p.2.val i k*φ p.2.val) :=
    (hjoint.comp measurable_swap).mul ((hφ.measurable.comp measurable_subtype_coe).comp measurable_snd)
  have hInt : Measurable (fun j : ShellField 2 => ∫ x : S, j x.val i k*φ x.val) :=
    hF.stronglyMeasurable.integral_prod_right'.measurable
  have he : (fun j : ShellField 2 => ∫ x : S, j x.val i k*φ x.val) =
      (fun j => entryTestR i k φ (ShellField.forgetShell j)) := by
    funext j
    rw [integral_subtype hS (fun x : Vec 2 => j x i k*φ x)]
    unfold entryTestR
    simp only [ShellField.forgetShell_apply]
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hzero : φ x = 0 := by
      by_contra hn
      exact hx ⟨hsupp hn,subset_tsupport _ hn⟩
    rw [hzero,mul_zero]
  rw [← he]
  exact hInt

/-- The exact local integral sigma algebra is below the sharp Gaussian point sigma algebra. -/
theorem cold_lihLocalSigma_le_point {U : Set (Vec 2)} (hU : MeasurableSet U) :
    ShellField.lihLocalSigma U ≤ coldStreamPointSigma U := by
  unfold ShellField.lihLocalSigma
  apply MeasurableSpace.comap_le_iff_le_map.mpr
  apply MeasurableSpace.generateFrom_le
  rintro _ ⟨i,k,φ,hφ,hsupp,t,ht,rfl⟩
  exact cold_entryTest_point_measurable hU i k hφ hsupp ht

/-- Two-region form of the sharp integral-local zero-shell independence. -/
theorem cold_zeroShell_localSigma_pair (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    {U V : Set (Vec 2)} (hU : MeasurableSet U) (hV : MeasurableSet V)
    (hsep : ∀ x ∈ U, ∀ y ∈ V, ∃ k : Fin 2, 1 ≤ |(x-y) k|) :
    ProbabilityTheory.Indep (ShellField.lihLocalSigma U) (ShellField.lihLocalSigma V)
      (ShellField.zeroShellLaw M.P).toMeasure := by
  have hproc := (cold_zeroShell_isGaussianProcess M h hM).comp_right
    (Sum.elim (fun x : U => x.val) (fun y : V => y.val))
  have hproc' : ProbabilityTheory.IsGaussianProcess
      (Sum.elim (fun (x : U) (j : ShellField 2) => j x.val 1 0)
        (fun (y : V) (j : ShellField 2) => j y.val 1 0)) (ShellField.zeroShellLaw M.P).toMeasure :=
    hproc.congr (fun p => by cases p <;> exact Filter.Eventually.of_forall (fun _ => rfl))
  have hpoint := ProbabilityTheory.IsGaussianProcess.indepFun_of_covariance_eq_zero hproc' 
    (fun x => (ShellField.measurable_eval_entry x.val 1 0).aemeasurable)
    (fun y => (ShellField.measurable_eval_entry y.val 1 0).aemeasurable)
    (fun x y => cold_zeroShell_covariance_zero M h hM (hsep x.val x.property y.val y.property))
  exact ProbabilityTheory.indep_of_indep_of_le_right
    (ProbabilityTheory.indep_of_indep_of_le_left hpoint (cold_lihLocalSigma_le_point hU))
    (cold_lihLocalSigma_le_point hV)

end ASDExplicitGamma.Cold
