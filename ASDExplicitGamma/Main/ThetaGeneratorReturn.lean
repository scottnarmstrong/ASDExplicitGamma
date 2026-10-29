module

public import ASDExplicitGamma.Main.ThetaGeneratorComposition
public import ASDExplicitGamma.Main.ChronologyGeneric
public import ASDExplicitGamma.Main.OrdinaryReturn
public import ASDExplicitGamma.Main.PanelCertifiedFinal
public import ASDExplicitGamma.Main.PanelEnclosureClosed
public import ASDExplicitGamma.Cold.NativeThetaScaling
public import ASDExplicitGamma.Statements.NativeInductionState
public import ASDExplicitGamma.Numerics.Cold.Certificate
public import ASDExplicitGamma.Numerics.MainReturnCertificate.Composition

/-! MA-THETA-CONTINUATION: the closed `θ`-scaled insertion step at observer `k` (leaves and panel
data discharged from the certificate), and the cold lag-40 start `≤ θ · cold40/G`. -/

@[expose] public section
noncomputable section

open MeasureTheory
open ASDExplicitGamma.Numerics
open ASDExplicitGamma.Numerics.Cold
open ASDExplicitGamma.Numerics.MainReturnCertificate
open ASDExplicitGamma.Numerics.Spike
open Algsuperdiff.Section3 Set

namespace ASDExplicitGamma.Main

/-- The rational cold table's lag-40 endpoint is the exact MainReturn grid value. -/
private theorem main_cold_mean_at40_grid_bound_Th :
    (coldMeanAt 40 : ℝ) ≤
      (mainReturnCold40Upper : ℝ) / (gridScale : ℝ) := by
  have hsourceQ : coldMeanAt 40 ≤
      (mainReturnCold40Upper : ℚ) / (gridScale : ℚ) := by
    calc
      coldMeanAt 40 ≤ (Spike.cold40Upper : ℚ) / (10 : ℚ) ^ 32 :=
        coldD40_le_mainReturnInput_of_replay
      _ = (mainReturnCold40Upper : ℚ) / (gridScale : ℚ) := by
        norm_num [mainReturnCold40Upper, Spike.gridScale]
  have hcast : (coldMeanAt 40 : ℝ) ≤
      (((mainReturnCold40Upper : ℚ) / (gridScale : ℚ) : ℚ) : ℝ) :=
    Rat.cast_le.mpr hsourceQ
  simpa only [Rat.cast_div, Rat.cast_natCast] using hcast

/-- The actual fixed-coefficient, fixed-frame cold mean has the proportional
lag-40 grid bound consumed by theta continuation. -/
theorem main_cold_start_theta_grid_bound_of_native_state_Th
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hgamma : M.gamma ≤ gammaZero) (m : ℤ)
    (hpast : ∀ n ≤ m, nativeInductionState M h n) :
    (∫ ω, cutoffTraceDefect M m (m + 40) ω
      ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
      theta M * ((mainReturnCold40Upper : ℝ) / (gridScale : ℝ)) := by
  rcases hpast m le_rfl with ⟨hordinary, hstrong, hroot, _, _, _, _, _⟩
  have htri := ASDExplicitGamma.Cold.cold_theta_scaling M h hM m hgamma
    hordinary hstrong hroot
  have h40 := htri 40 (by norm_num)
  have htheta : 0 ≤ theta M := (ASDExplicitGamma.Cold.cold_theta_pos M).le
  calc
    _ ≤ theta M * (coldMeanAt 40 : ℝ) := h40
    _ ≤ theta M * ((mainReturnCold40Upper : ℝ) / (gridScale : ℝ)) :=
      mul_le_mul_of_nonneg_left main_cold_mean_at40_grid_bound_Th htheta


/-- Insertion record of observer `k` (1-indexed). -/
def thetaIns (k : ℕ) : MainInsertionEndpoints :=
  mainInsertionList.getD (k - 1) observer1InsertionEndpoints

theorem thetaIns_panels_length (k : ℕ) (h1 : 1 ≤ k) (h40 : k ≤ 40) :
    (thetaIns k).panels.length = 8 := by
  interval_cases k <;> rfl

theorem thetaIns_frame (k : ℕ) (h1 : 1 ≤ k) (h40 : k ≤ 40) :
    insertionFrameRecurrenceFields (thetaIns k).frameLower (thetaIns k).frameUpper := by
  interval_cases k
  · exact observer1_frame_recurrence_fields_sound
  · exact observer2_frame_recurrence_fields_sound
  · exact observer3_frame_recurrence_fields_sound
  · exact observer4_frame_recurrence_fields_sound
  · exact observer5_frame_recurrence_fields_sound
  · exact observer6_frame_recurrence_fields_sound
  · exact observer7_frame_recurrence_fields_sound
  · exact observer8_frame_recurrence_fields_sound
  · exact observer9_frame_recurrence_fields_sound
  · exact observer10_frame_recurrence_fields_sound
  · exact observer11_frame_recurrence_fields_sound
  · exact observer12_frame_recurrence_fields_sound
  · exact observer13_frame_recurrence_fields_sound
  · exact observer14_frame_recurrence_fields_sound
  · exact observer15_frame_recurrence_fields_sound
  · exact observer16_frame_recurrence_fields_sound
  · exact observer17_frame_recurrence_fields_sound
  · exact observer18_frame_recurrence_fields_sound
  · exact observer19_frame_recurrence_fields_sound
  · exact observer20_frame_recurrence_fields_sound
  · exact observer21_frame_recurrence_fields_sound
  · exact observer22_frame_recurrence_fields_sound
  · exact observer23_frame_recurrence_fields_sound
  · exact observer24_frame_recurrence_fields_sound
  · exact observer25_frame_recurrence_fields_sound
  · exact observer26_frame_recurrence_fields_sound
  · exact observer27_frame_recurrence_fields_sound
  · exact observer28_frame_recurrence_fields_sound
  · exact observer29_frame_recurrence_fields_sound
  · exact observer30_frame_recurrence_fields_sound
  · exact observer31_frame_recurrence_fields_sound
  · exact observer32_frame_recurrence_fields_sound
  · exact observer33_frame_recurrence_fields_sound
  · exact observer34_frame_recurrence_fields_sound
  · exact observer35_frame_recurrence_fields_sound
  · exact observer36_frame_recurrence_fields_sound
  · exact observer37_frame_recurrence_fields_sound
  · exact observer38_frame_recurrence_fields_sound
  · exact observer39_frame_recurrence_fields_sound
  · exact observer40_frame_recurrence_fields_sound

theorem thetaMainCert_getElem (i : ℕ) (hi : i < 40) :
    mainCert[i]? = some (thetaIns (40 - i)).toInsertionCert := by
  interval_cases i <;> rfl

/-- One insertion at observer `k`, label `m`, scaled by `θ`. -/
theorem theta_step_observer
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (hγ : M.gamma ≤ gammaZero) (N : ℤ)
    (hpast : ∀ l < N, nativeInductionState M h l) (m : ℤ) (hm : m < N) (k : ℕ)
    (h1 : 1 ≤ k) (h40 : k ≤ 40) (x : ℕ)
    (hOld : (∫ ω, cutoffTraceDefect M m (m + (k : ℤ)) ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
      theta M * ((x : ℝ) / (Spike.gridScale : ℝ))) :
    (∫ ω, cutoffTraceDefect M (m + 1) (m + (k : ℤ)) ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
      theta M * ((advanceInsertion x (thetaIns k).toInsertionCert : ℝ) /
        (Spike.gridScale : ℝ)) := by
  set ins := thetaIns k with hins
  have hlen := thetaIns_panels_length k h1 h40
  let E : ℕ → PanelEndpoints := fun j => ins.panels.getD j observer1Panel0Endpoints
  have hpanelsE : ins.panels = (List.range 8).map E := by
    apply List.ext_getElem (by simpa using hlen)
    intro j hj1 hj2
    simp [E, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj1]
  have hcert : ins.toInsertionCert.panels = (List.range 8).map (fun j => thetaPanelCert (E j)) := by
    show ins.panels.map PanelEndpoints.toPanelCert = _
    rw [hpanelsE, List.map_map]
    rfl
  refine ma_theta_insertion_step panelLeafL1L2 M h hM hγ N hpast m hm k h1 h40
    ins.toInsertionCert (thetaIns_frame k h1 h40) E hcert x hOld ?_
  intro j hj
  obtain ⟨d, e', hc, ins', hins', hpan⟩ := panel_certified k j h1 h40 hj
  have hii : ins' = ins := by
    have : mainInsertionList[k - 1]? = some ins' := hins'
    simp [hins, thetaIns, List.getD_eq_getElem?_getD, this]
  subst hii
  have hE : E j = e' := by
    simp [E, List.getD_eq_getElem?_getD, hpan]
  obtain ⟨hb, hfields, hanchor, hmeanQ, hxiQ, hq, hlo, hhi⟩ := hc
  refine ⟨d, ?_, ?_, hanchor, ?_, ?_, hq, ?_⟩
  · rw [hE]; exact hb
  · rw [hE]; exact hfields
  · rw [hmeanQ]; rfl
  · have hQ : observer1Panel0Data.initialInverseMean =
        ASDExplicitGamma.Numerics.MainReturn.observer1Panel0Data.initialInverseMean := by
      decide +kernel
    rw [hxiQ, hQ]; unfold mainSourceInversePrefix; ring
  · intro s hs
    refine ⟨?_, ?_⟩
    · rw [hlo]; push_cast; exact hs.1
    · rw [hhi]; push_cast; have := hs.2; push_cast at this; exact this

/-- MA-THETA-CONTINUATION: the real return at the target label, from the closed `θ` step and the
cold lag-40 start composed by `main_composed_generic` with `c = θ`. -/
theorem ma_theta_return
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (hγ : M.gamma ≤ gammaZero) (N : ℤ)
    (hpast : ∀ n < N, nativeInductionState M h n) :
    (∫ ω, cutoffTraceDefect M N N ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
      3 / 50 * theta M := by
  have hθ0 : 0 ≤ theta M := (ASDExplicitGamma.Cold.cold_theta_pos M).le
  have hcold := main_cold_start_theta_grid_bound_of_native_state_Th M h hM hγ (N - 40)
    (fun n hn => hpast n (by omega))
  have hcomp := main_composed_generic M (N - 40) (theta M) hcold (by
    intro i hi cert x0 hcert hold
    have hc := thetaMainCert_getElem i hi
    rw [hcert] at hc
    have hce : cert = (thetaIns (40 - i)).toInsertionCert := Option.some.inj hc
    subst hce
    have hcube : (N - 40 + (i : ℤ)) + ((40 - i : ℕ) : ℤ) = N - 40 + 40 := by omega
    have hstep := theta_step_observer M h hM hγ N hpast (N - 40 + (i : ℤ)) (by omega)
      (40 - i) (by omega) (by omega) x0 (by rw [hcube]; exact hold)
    rw [hcube] at hstep
    exact hstep)
  have hN : N - 40 + 40 = N := by omega
  rw [hN] at hcomp
  have hlt := mainReturn_composed_lt_three_fiftieth
  calc _ ≤ _ := hcomp
    _ ≤ theta M * (3 / 50) := mul_le_mul_of_nonneg_left hlt.le hθ0
    _ = _ := by ring

/-- The exact `MaThetaReturnReal` of w02's ordinary-return tail. -/
theorem ma_theta_return_real
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (hγ : M.gamma ≤ gammaZero) (N : ℤ) :
    MaThetaReturnReal M h N :=
  fun hpast => ma_theta_return M h hM hγ N hpast

end ASDExplicitGamma.Main

end
