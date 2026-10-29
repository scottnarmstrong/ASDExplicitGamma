module

public import ASDExplicitGamma.Main.PartialInsertion
public import Algsuperdiff.Section3.Cutoff.HighMoments
public import Algsuperdiff.Section3.Cutoff.LocalControlMoment
public import Algsuperdiff.Section3.Cutoff.P4UpperMoments

/-! Second moments of the actual partial-insertion coefficient envelope. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open MeasureTheory Algsuperdiff.Section3 Algsuperdiff.Section3.Cutoff
  Algsuperdiff.Frozen.Assumptions

theorem mainInsertion_freshLocalControl_fourth_integrable
    (M : ABKModel 2) (ell m : ℤ) :
    Integrable
      (fun ω : Cutoff.CutoffSample 2 =>
        localCubeControl ell (ω.1 (m + 1)) ^ 4)
      (Cutoff.cutoffSampleLaw M).toMeasure := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let ν := (ShellField.zeroShellLaw M.P).toMeasure
  let q : ℤ := ell - (m + 1)
  let c : ℝ := Real.rpow 3 (M.gamma * ((m + 1 : ℤ) : ℝ))
  let f : ShellField 2 → ℝ :=
    fun j => localCubeControl ell (ShellField.triadicScale M.gamma (m + 1) j) ^ 4
  let g : ShellField 2 → ℝ := fun j => localCubeControl q j ^ 4
  have hlocal : Integrable g ν := by
    have hpow := hasGammaMomentGrowthWith_localCubeControl_zero M q
      (by norm_num : (1 : ℝ) ≤ 4)
    have hlocalReal : Integrable
        (fun j : ShellField 2 => localCubeControl q j ^ (4 : ℝ)) ν := by
      simpa only [abs_of_nonneg (localCubeControl_nonneg q _)] using hpow.1
    convert hlocalReal using 1
    funext j
    exact (Real.rpow_natCast (localCubeControl q j) 4).symm
  have hscale : ∀ j, f j = c ^ 4 * g j := by
    intro j
    change localCubeControl ell (ShellField.triadicScale M.gamma (m + 1) j) ^ 4 = _
    rw [localCubeControl_triadicScale]
    simp only [g, q, c, pow_succ]
    ring
  have hfbase : Measurable (fun j : ShellField 2 =>
      localCubeControl ell (ShellField.triadicScale M.gamma (m + 1) j)) :=
    (measurable_localCubeControl ell).comp
      (ShellField.measurable_triadicScale M.gamma (m + 1))
  have hf : Measurable f := by
    simpa only [f] using hfbase.pow_const 4
  have hfg : Integrable f ν := by
    have hc : Integrable (fun j => c ^ 4 * g j) ν := hlocal.const_mul (c ^ 4)
    convert hc using 1
    funext j
    exact hscale j
  have hmap :
      Measure.map (fun ω : Cutoff.CutoffSample 2 =>
        localCubeControl ell (ω.1 (m + 1)) ^ 4) μ = Measure.map f ν := by
    let coordinate : Cutoff.CutoffSample 2 → ShellField 2 := fun ω => ω.1 (m + 1)
    let fourthControl : ShellField 2 → ℝ := fun j => localCubeControl ell j ^ 4
    calc
      Measure.map (fun ω : Cutoff.CutoffSample 2 =>
          localCubeControl ell (ω.1 (m + 1)) ^ 4) μ =
          Measure.map fourthControl (Measure.map coordinate μ) := by
            change Measure.map (fourthControl ∘ coordinate) μ = _
            exact (Measure.map_map ((measurable_localCubeControl ell).pow_const 4)
              ((measurable_pi_apply (m + 1)).comp measurable_subtype_coe)).symm
      _ = Measure.map fourthControl
            (Measure.map (ShellField.triadicScale M.gamma (m + 1)) ν) := by
              rw [Model.map_freshShell_eq_scaledZeroShellLaw]
      _ = Measure.map (fourthControl ∘ ShellField.triadicScale M.gamma (m + 1)) ν :=
            Measure.map_map ((measurable_localCubeControl ell).pow_const 4)
              (ShellField.measurable_triadicScale M.gamma (m + 1))
      _ = Measure.map f ν := by rfl
  have hmapInt : Integrable id (Measure.map f ν) := by
    apply (integrable_map_measure measurable_id.aestronglyMeasurable hf.aemeasurable).mpr
    simpa [id] using hfg
  have hsourceMap : Integrable id
      (Measure.map (fun ω : Cutoff.CutoffSample 2 =>
        localCubeControl ell (ω.1 (m + 1)) ^ 4) μ) := by
    rw [hmap]
    exact hmapInt
  have hsourceMeas : Measurable
      (fun ω : Cutoff.CutoffSample 2 =>
        localCubeControl ell (ω.1 (m + 1)) ^ 4) := by
    have hbase : Measurable (fun ω : Cutoff.CutoffSample 2 =>
        localCubeControl ell (ω.1 (m + 1))) :=
      (measurable_localCubeControl ell).comp
        ((measurable_pi_apply (m + 1)).comp measurable_subtype_coe)
    exact hbase.pow_const 4
  simpa [id] using!
    (integrable_map_measure measurable_id.aestronglyMeasurable hsourceMeas.aemeasurable).mp
      hsourceMap

theorem mainInsertion_partialEntryBound_fourth_integrable
    (M : ABKModel 2) (ell m : ℤ) :
    Integrable
      (fun ω : Cutoff.CutoffSample 2 =>
        Model.partialInsertedEntryBound M ell m ω ^ 4)
      (Cutoff.cutoffSampleLaw M).toMeasure := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let old : Cutoff.CutoffSample 2 → ℝ := fun ω =>
    Cutoff.cutoffLocalControl ell m ω
  let fresh : Cutoff.CutoffSample 2 → ℝ := fun ω =>
    localCubeControl ell (ω.1 (m + 1))
  have hOldFourth : Integrable (fun ω => old ω ^ 4) μ := by
    simpa only [old, abs_of_nonneg (Cutoff.cutoffLocalControl_nonneg ell m _),
      Real.rpow_natCast] using Cutoff.integrable_cutoffLocalControl_pow M ell m 4
  have hFreshFourth : Integrable (fun ω => fresh ω ^ 4) μ := by
    simpa only [fresh] using mainInsertion_freshLocalControl_fourth_integrable M ell m
  have hOld : Measurable old := Cutoff.measurable_cutoffLocalControl ell m
  have hFresh : Measurable fresh := (measurable_localCubeControl ell).comp
    ((measurable_pi_apply (m + 1)).comp measurable_subtype_coe)
  have hbound : ∀ ω, Model.partialInsertedEntryBound M ell m ω ^ 4 ≤
      27 * (M.nu ^ 4 + old ω ^ 4 + fresh ω ^ 4) := by
    intro ω
    rw [Model.partialInsertedEntryBound]
    have hn : 0 ≤ M.nu := M.nu_pos.le
    have ho : 0 ≤ old ω := Cutoff.cutoffLocalControl_nonneg ell m ω
    have hf : 0 ≤ fresh ω := localCubeControl_nonneg ell (ω.1 (m + 1))
    have hsum : (M.nu + old ω + fresh ω) ^ 2 ≤
        3 * (M.nu ^ 2 + old ω ^ 2 + fresh ω ^ 2) := by
      nlinarith [sq_nonneg (M.nu - old ω), sq_nonneg (M.nu - fresh ω),
        sq_nonneg (old ω - fresh ω)]
    have hsum2 : (M.nu ^ 2 + old ω ^ 2 + fresh ω ^ 2) ^ 2 ≤
        3 * (M.nu ^ 4 + old ω ^ 4 + fresh ω ^ 4) := by
      nlinarith [sq_nonneg (M.nu ^ 2 - old ω ^ 2),
        sq_nonneg (M.nu ^ 2 - fresh ω ^ 2),
        sq_nonneg (old ω ^ 2 - fresh ω ^ 2)]
    have hsum_nonneg : 0 ≤ M.nu ^ 2 + old ω ^ 2 + fresh ω ^ 2 := by positivity
    have hpow : (M.nu + old ω + fresh ω) ^ 4 ≤
        (3 * (M.nu ^ 2 + old ω ^ 2 + fresh ω ^ 2)) ^ 2 := by
      have := mul_le_mul hsum hsum (sq_nonneg _) (by positivity)
      nlinarith
    calc
      (M.nu + old ω + fresh ω) ^ 4 ≤
          (3 * (M.nu ^ 2 + old ω ^ 2 + fresh ω ^ 2)) ^ 2 := hpow
      _ = 9 * (M.nu ^ 2 + old ω ^ 2 + fresh ω ^ 2) ^ 2 := by ring
      _ ≤ 27 * (M.nu ^ 4 + old ω ^ 4 + fresh ω ^ 4) := by
        nlinarith [hsum2]
  have hsum : Integrable
      (fun ω => 27 * (M.nu ^ 4 + old ω ^ 4 + fresh ω ^ 4)) μ := by
    have hconst : Integrable (fun _ : Cutoff.CutoffSample 2 => 27 * M.nu ^ 4) μ :=
      integrable_const _
    have hcontrols := hOldFourth.add hFreshFourth
    have hcontrols' : Integrable (fun ω => 27 * (old ω ^ 4 + fresh ω ^ 4)) μ := by
      convert hcontrols.const_mul 27 using 1
    convert hconst.add hcontrols' using 1
    ext ω
    simp only [Pi.add_apply]
    ring
  have hEntryMeas : Measurable
      (fun ω : Cutoff.CutoffSample 2 =>
        Model.partialInsertedEntryBound M ell m ω ^ 4) := by
    have hbase : Measurable (fun ω : Cutoff.CutoffSample 2 =>
        Model.partialInsertedEntryBound M ell m ω) := by
      change Measurable (fun ω => M.nu +
        Cutoff.cutoffLocalControl ell m ω + localCubeControl ell (ω.1 (m + 1)))
      exact ((measurable_const.add hOld).add hFresh)
    exact hbase.pow_const 4
  apply hsum.mono'
  · exact hEntryMeas.aestronglyMeasurable
  · filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hbound ω

end ASDExplicitGamma.Main
