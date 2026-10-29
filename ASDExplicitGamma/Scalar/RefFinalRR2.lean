module

public import ASDExplicitGamma.Scalar.RefFinalAux
public import ASDExplicitGamma.Scalar.RefFinalRR

/-! Successor of the physical defect fourth-moment theorem for the corrected reference. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar

open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Triadic
  ASDExplicitGamma.Variational ASDExplicitGamma.Gaussian ASDExplicitGamma.Main
open Algsuperdiff.Section3 ASDExplicitGamma.Native ASDExplicitGamma.Inverse Filter
open scoped InnerProductSpace BigOperators ENNReal Topology

noncomputable section

section Final

variable (M : ABKModel 2) (h : ℝ) (m : ℤ) {a b c d : ℝ} (hab : a < b) (hcd : c < d)
  (hQ : openCubeSet (originCube 2 (m + 129)) ⊆ openRectangle a b c d) (e : Vec 2)

local notation "CC" => finalCfg M h m hab hcd hQ e

theorem actual_defect_finalRR (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero)
    (hpast : ∀ n < m, nativeInductionState M h n)
    (a5 ξ mStar εOld Rr : ℝ) (hRr : 0 ≤ Rr)
    (hΛ1 : ∀ n, ∫ ω, ((CC).LamFR n (olderField (closedRectangle a b c d) m ω) +
      (CC).LamGR n (olderField (closedRectangle a b c d) m ω))
        ∂(Cutoff.cutoffSampleLaw M).toMeasure ≤
      (CC).amp ^ 2 * defectLambda a5 ξ mStar (14103 / 10000) εOld)
    (hΛq : ∀ n, eLpNorm (fun ω => (CC).LamFR n (olderField (closedRectangle a b c d) m ω) +
      (CC).LamGR n (olderField (closedRectangle a b c d) m ω))
        (ENNReal.ofReal (128 / 127)) (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal ((CC).amp ^ 2 *
        Rr))
    (hLam0 : 0 ≤ defectLambda a5 ξ mStar (14103 / 10000) εOld) :
    Integrable (fun ω => max ((CC).DactR m ω) 0) (Cutoff.cutoffSampleLaw M).toMeasure ∧
      ∫ ω, max ((CC).DactR m ω) 0 ∂(Cutoff.cutoffSampleLaw M).toMeasure ≤
        (volume (openCubeSet (originCube 2 (m + 129)))).toReal *
          ((44 / 25 : ℝ) * ((CC).amp ^ 2) ^ 2 *
            defectFdefR a5 ξ mStar (14103 / 10000) εOld (14103 / 10000) (5 / 10 ^ 24) Rr) := by
  obtain ⟨ell, hK⟩ := exists_originCube_containing_compact (closedRectangle a b c d)
    (closedRectangle_isCompact a b c d)
  obtain ⟨μ', hprob, hfst, hshell, hold⟩ := shell_coupling a b c d hab hcd M h hM ell m hK
  haveI := hprob
  have hmeasOld : Measurable (fun ω : Cutoff.CutoffSample 2 =>
      olderField (closedRectangle a b c d) m ω) := measurable_olderField _ ell m hK
  obtain ⟨ν, hνdef⟩ : ∃ ν : Measure C(closedRectangle a b c d, ℝ), ν =
      (Cutoff.cutoffSampleLaw M).toMeasure.map (olderField (closedRectangle a b c d) m) :=
    ⟨_, rfl⟩
  have hνprob : IsProbabilityMeasure ν := by
    rw [hνdef]; infer_instance
  haveI := hνprob
  haveI hfinν : IsFiniteMeasure ν := inferInstance
  have hLamm : ∀ n, Measurable (fun o => (CC).LamFR n o + (CC).LamGR n o) := fun n =>
    ((CC).LamFR_measurable n).add ((CC).LamGR_measurable n)
  have hΛ1' : ∀ n, ∫ o, ((CC).LamFR n o + (CC).LamGR n o) ∂ν ≤
      (CC).amp ^ 2 * defectLambda a5 ξ mStar (14103 / 10000) εOld := by
    intro n
    rw [hνdef, integral_map hmeasOld.aemeasurable (hLamm n).aestronglyMeasurable]
    exact hΛ1 n
  have hΛq' : ∀ n, eLpNorm (fun o => (CC).LamFR n o + (CC).LamGR n o) (ENNReal.ofReal (128 / 127)) ν ≤
      ENNReal.ofReal ((CC).amp ^ 2 *
        Rr) := by
    intro n
    have hmap := eLpNorm_map_measure (μ := (Cutoff.cutoffSampleLaw M).toMeasure)
      (p := ENNReal.ofReal (128 / 127)) (f := olderField (closedRectangle a b c d) m)
      (g := fun o => (CC).LamFR n o + (CC).LamGR n o) (hLamm n).aestronglyMeasurable
      hmeasOld.aemeasurable
    have e : eLpNorm (fun o => (CC).LamFR n o + (CC).LamGR n o) (ENNReal.ofReal (128 / 127)) ν =
        eLpNorm ((fun o => (CC).LamFR n o + (CC).LamGR n o) ∘
          (olderField (closedRectangle a b c d) m)) (ENNReal.ofReal (128 / 127))
          (Cutoff.cutoffSampleLaw M).toMeasure := by
      rw [hνdef]; exact hmap
    exact e.trans_le (hΛq n)
  have hLamInt : ∀ n, Integrable (fun o => (CC).LamFR n o + (CC).LamGR n o) ν := by
    intro n
    have hmem : MemLp (fun o => (CC).LamFR n o + (CC).LamGR n o) (ENNReal.ofReal (128 / 127)) ν :=
      lt_of_le_of_lt (hΛq' n) ENNReal.ofReal_lt_top
    have hq : (1 : ENNReal) ≤ ENNReal.ofReal (128 / 127) := by
      rw [show (1 : ENNReal) = ENNReal.ofReal 1 by simp]
      exact ENNReal.ofReal_le_ofReal (by norm_num)
    exact MeasureTheory.MemLp.integrable (μ := ν) hq hmem
  have hFint : ∀ n, Integrable ((CC).LamFR n) ν := fun n =>
    (hLamInt n).mono' ((CC).LamFR_measurable n).aestronglyMeasurable
      (Filter.Eventually.of_forall fun o => by
        rw [Real.norm_eq_abs, abs_of_nonneg ((CC).LamFR_nonneg n o)]
        linarith [(CC).LamGR_nonneg n o])
  have hGint : ∀ n, Integrable ((CC).LamGR n) ν := fun n =>
    (hLamInt n).mono' ((CC).LamGR_measurable n).aestronglyMeasurable
      (Filter.Eventually.of_forall fun o => by
        rw [Real.norm_eq_abs, abs_of_nonneg ((CC).LamGR_nonneg n o)]
        linarith [(CC).LamFR_nonneg n o])
  have hQcl := hQcl' hab hcd (originCube 2 (m + 129)) hQ
  have hQK : openCubeSet (originCube 2 (m + 129)) ⊆ closedRectangle a b c d :=
    fun x hx => hQcl (subset_closure hx)
  have hQell : openCubeSet (originCube 2 (m + 129)) ⊆ openCubeSet (originCube 2 ell) :=
    hQK.trans hK
  have hQscale : (originCube 2 (m + 129)).scale = m + 129 := by simp [originCube]
  obtain ⟨hB128, hR128⟩ := bank_Bnew M h hM hγ m hpast (originCube 2 (m + 129)) hQscale ell
    hQell
  have hBm : Measurable (fun ω => bnew M m (originCube 2 (m + 129)) ω) :=
    bnew_measurable M ell m _ hQell
  have hRm' : Measurable (fun ω => max (bnew M m (originCube 2 (m + 129)) ω -
      14103 / 10000) 0) := (hBm.sub_const _).max measurable_const
  have hfstmeas : Measurable (Prod.fst : Cutoff.CutoffSample 2 × (ℕ → ℝ) → _) := measurable_fst
  have hB128' : eLpNorm (fun p : Cutoff.CutoffSample 2 × (ℕ → ℝ) =>
      bnew M m (originCube 2 (m + 129)) p.1) 128 μ' ≤ ENNReal.ofReal (14103 / 10000) := by
    have e := eLpNorm_map_measure (μ := μ') (p := 128) (f := Prod.fst)
      (g := fun ω => bnew M m (originCube 2 (m + 129)) ω) hBm.aestronglyMeasurable
      hfstmeas.aemeasurable
    rw [hfst] at e
    exact e.symm.le.trans hB128
  have hR128' : eLpNorm (fun p : Cutoff.CutoffSample 2 × (ℕ → ℝ) =>
      max (bnew M m (originCube 2 (m + 129)) p.1 - 14103 / 10000) 0) 128 μ' ≤
        ENNReal.ofReal (5 / 10 ^ 24) := by
    have e := eLpNorm_map_measure (μ := μ') (p := 128) (f := Prod.fst)
      (g := fun ω => max (bnew M m (originCube 2 (m + 129)) ω - 14103 / 10000) 0)
      hRm'.aestronglyMeasurable hfstmeas.aemeasurable
    rw [hfst] at e
    exact e.symm.le.trans hR128
  have hpairmeas : Measurable (fun p : Cutoff.CutoffSample 2 × (ℕ → ℝ) =>
      (olderField (closedRectangle a b c d) m p.1, p.2)) :=
    (hmeasOld.comp measurable_fst).prodMk measurable_snd
  have hold' : μ'.map (fun p : Cutoff.CutoffSample 2 × (ℕ → ℝ) =>
      (olderField (closedRectangle a b c d) m p.1, p.2)) =
        ν.prod standardGaussianInfinitePi := by rw [hνdef]; exact hold
  have hsnd : μ'.map Prod.snd = standardGaussianInfinitePi := by
    have h1 := congrArg (Measure.map (Prod.snd : C(closedRectangle a b c d, ℝ) × (ℕ → ℝ) →
      (ℕ → ℝ))) hold'
    rw [Measure.map_map measurable_snd hpairmeas] at h1
    have h2 : (Prod.snd ∘ fun p : Cutoff.CutoffSample 2 × (ℕ → ℝ) =>
        (olderField (closedRectangle a b c d) m p.1, p.2)) = Prod.snd := rfl
    rw [h2] at h1
    rw [h1, Measure.map_snd_prod]
    simp
  have hgauss := ae_partial_tendsto a b c d (q3ModelAmplitude M h (m + 1))
    (q3ModelLength (m + 1))
  have hae2 : ∀ᵐ p ∂μ', Tendsto (fun n => ∑ i ∈ Finset.range n, p.2 i •
      (CC).Hs i) atTop (𝓝 ((q3C1Series a b c d (q3ModelAmplitude M h (m + 1))
        (q3ModelLength (m + 1)) whiteBasis p.2) 0)) :=
    ae_of_ae_map measurable_snd.aemeasurable (by rw [hsnd]; exact hgauss)
  have hlimA : ∀ᵐ p ∂μ', Tendsto (fun n => (CC).DtruncR m p.1 n (fun i : Fin n => p.2 i)) atTop
      (𝓝 ((CC).DactR m p.1)) := by
    filter_upwards [hshell, hae2] with p h1 h2
    refine (CC).DtruncR_tendsto m p.1 p.2 ?_
    have : (CC).z0 m p.1 = (q3C1Series a b c d (q3ModelAmplitude M h (m + 1))
        (q3ModelLength (m + 1)) whiteBasis p.2) 0 := h1.symm
    rw [this]
    exact h2
  have hmesh : diagMeshRadius (CC).Q 134 ≤ (CC).L.1 / 729 := mesh' m
  have hvol : 0 ≤ (volume (openCubeSet (originCube 2 (m + 129)))).toReal := ENNReal.toReal_nonneg
  have hv : 0 ≤ (CC).amp ^ 2 := sq_nonneg _
  have hBmem : MemLp (fun p : Cutoff.CutoffSample 2 × (ℕ → ℝ) =>
      bnew M m (originCube 2 (m + 129)) p.1) 128 μ' :=
    lt_of_le_of_lt hB128' ENNReal.ofReal_lt_top
  have hκ2 : 0 ≤ 3 * defectA ^ 2 * (CC).amp ^ 2 := by positivity
  have hLq : 0 ≤ (CC).amp ^ 2 * Rr := by
    positivity
  have hDnm : ∀ n, Measurable (fun p : Cutoff.CutoffSample 2 × (ℕ → ℝ) =>
      (CC).DtruncR m p.1 n (fun i : Fin n => p.2 i)) := fun n => (CC).DtruncR_measurable m ell hK n
  have hDinfm : Measurable (fun p : Cutoff.CutoffSample 2 × (ℕ → ℝ) => (CC).DactR m p.1) :=
    ((CC).DactR_measurable m ell hK).comp measurable_fst
  have hBH : ∀ n, Integrable (fun p : Cutoff.CutoffSample 2 × (ℕ → ℝ) =>
      bnew M m (originCube 2 (m + 129)) p.1 *
        (tiledPositiveEnergy (CC).Q 134 (psdDefectSource ((CC).BFoR
          (olderField (closedRectangle a b c d) m p.1) n) (fun i : Fin n => p.2 i)) +
         tiledPositiveEnergy (CC).Q 134 (psdDefectSource ((CC).BGoR
          (olderField (closedRectangle a b c d) m p.1) n) (fun i : Fin n => p.2 i)))) μ' := by
    intro n
    exact two_slot_hBH μ' ν (fun p => olderField (closedRectangle a b c d) m p.1)
      (fun p => p.2) (hmeasOld.comp measurable_fst) measurable_snd hold' (CC).Q 134
      (fun o => (CC).BFoR o n) (fun o => (CC).BGoR o n)
      (fun o i j => (CC).BFoR_symm o n i j) (fun o i j => (CC).BGoR_symm o n i j)
      ((CC).BFoR_meas n) ((CC).BGoR_meas n) ((CC).LamFR n) ((CC).LamGR n)
      ((CC).LamFR_measurable n) ((CC).LamGR_measurable n) (hFint n) (hGint n)
      (fun o => (CC).LamFR_nonneg n o) (fun o => (CC).LamGR_nonneg n o)
      (3 * defectA ^ 2 * (CC).amp ^ 2) hκ2
      (fun o => (CC).BFoR_wick hmesh o n) (fun o => (CC).BGoR_wick hmesh o n)
      (fun p => bnew M m (originCube 2 (m + 129)) p.1)
      ((CC).amp ^ 2 * defectLambda a5 ξ mStar (14103 / 10000) εOld)
      ((CC).amp ^ 2 * Rr) hLq
      (hΛ1' n) (hΛq' n) hBmem
  have hpath : ∀ n (p : Cutoff.CutoffSample 2 × (ℕ → ℝ)),
      (CC).DtruncR m p.1 n (fun i : Fin n => p.2 i) ≤ (44 / 25 : ℝ) *
        ((volume (openCubeSet (originCube 2 (m + 129)))).toReal *
          (bnew M m (originCube 2 (m + 129)) p.1 *
            (tiledPositiveEnergy (CC).Q 134 (psdDefectSource ((CC).BFoR
              (olderField (closedRectangle a b c d) m p.1) n) (fun i : Fin n => p.2 i)) +
             tiledPositiveEnergy (CC).Q 134 (psdDefectSource ((CC).BGoR
              (olderField (closedRectangle a b c d) m p.1) n) (fun i : Fin n => p.2 i))))) :=
    fun n p => (CC).DtruncR_le m M rfl rfl ell hK p.1 n (fun i : Fin n => p.2 i)
  have key := two_slot_final_of_piecesRR Rr hRr μ' ν (fun p => olderField (closedRectangle a b c d) m p.1)
    (fun p => p.2) (hmeasOld.comp measurable_fst) measurable_snd hold'
    (CC).Q 134 (volume (openCubeSet (originCube 2 (m + 129)))).toReal hvol
    (fun n o => (CC).BFoR o n) (fun n o => (CC).BGoR o n)
    (fun n o i j => (CC).BFoR_symm o n i j) (fun n o i j => (CC).BGoR_symm o n i j)
    (fun n => (CC).BFoR_meas n) (fun n => (CC).BGoR_meas n)
    ((CC).amp ^ 2) a5 ξ mStar εOld hv (fun n => (CC).LamFR n) (fun n => (CC).LamGR n)
    (fun n => (CC).LamFR_measurable n) (fun n => (CC).LamGR_measurable n) hFint hGint
    (fun n o => (CC).LamFR_nonneg n o) (fun n o => (CC).LamGR_nonneg n o)
    (fun n o => (CC).BFoR_wick hmesh o n) (fun n o => (CC).BGoR_wick hmesh o n)
    (fun p => bnew M m (originCube 2 (m + 129)) p.1)
    (fun p => max (bnew M m (originCube 2 (m + 129)) p.1 - 14103 / 10000) 0)
    (hRm'.comp measurable_fst) (fun p => bnew_nonneg M m _ p.1)
    (fun p => by linarith [le_max_left (bnew M m (originCube 2 (m + 129)) p.1 - 14103 / 10000) 0])
    (fun p => le_max_right _ _) hΛ1' hΛq' hR128' hBH
    (fun n p => (CC).DtruncR m p.1 n (fun i : Fin n => p.2 i))
    (fun p => (CC).DactR m p.1) hDnm hDinfm hpath hlimA hLam0
  have hmaxm : Measurable (fun ω : Cutoff.CutoffSample 2 => max ((CC).DactR m ω) 0) :=
    ((CC).DactR_measurable m ell hK).max measurable_const
  refine ⟨?_, ?_⟩
  · rw [← hfst]
    exact (integrable_map_measure hmaxm.aestronglyMeasurable
      measurable_fst.aemeasurable).2 key.1
  · have e := integral_map measurable_fst.aemeasurable hmaxm.aestronglyMeasurable (μ := μ')
    rw [hfst] at e
    rw [e]
    exact key.2

end Final

end

end ASDExplicitGamma.Scalar
