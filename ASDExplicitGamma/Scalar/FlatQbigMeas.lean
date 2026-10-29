module

public import ASDExplicitGamma.Scalar.FlatQbigTile
public import ASDExplicitGamma.Scalar.FlatSourceQ3PositiveHaar
public import ASDExplicitGamma.Scalar.FlatSourceHaarLimit

/-! Q_big flat successor: the tiled positive Haar energy of a Hilbert vector field,
its measurability, and its lower semicontinuity under `L²` convergence of `H¹` approximants. -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open MeasureTheory Homogenization ASDExplicitGamma.Triadic ASDExplicitGamma.Variational
  Filter Topology
open scoped ENNReal

noncomputable section

/-- The tiled positive Haar energy of the normalized coordinates of a Hilbert vector field. -/
def phi' (Q : TriadicCube 2) (n : ℕ) (V : HilbertVectorL2 (openCubeSet Q)) : ℝ :=
  lemmaVTiledPositiveEnergy Q n (fun x i => (hilbertVectorL2_normalizedCoordCLM Q i V) x)

theorem vecEnergy_eq_norm_sq (R : TriadicCube 2) (F : Vec 2 → Fin 2 → ℝ) :
    vectorPositiveHaarEnergy R F = vectorPositiveHaarNorm R F ^ 2 := by
  unfold vectorPositiveHaarNorm
  rw [Real.sq_sqrt (vectorPositiveHaarEnergy_nonneg R F)]

theorem vecEnergy_congr_ae (R : TriadicCube 2) {F G : Vec 2 → Fin 2 → ℝ}
    (h : ∀ i, (fun x => F x i) =ᵐ[normalizedCubeMeasure R] (fun x => G x i)) :
    vectorPositiveHaarEnergy R F = vectorPositiveHaarEnergy R G := by
  rw [vecEnergy_eq_norm_sq, vecEnergy_eq_norm_sq]
  exact vectorPositiveHaarNorm_sq_congr_ae R h

theorem primalEnergy_congr_ae (R : TriadicCube 2) (q : ℝ) {f g : Vec 2 → ℝ}
    (h : f =ᵐ[normalizedCubeMeasure R] g) : primalEnergy R q f = primalEnergy R q g := by
  unfold primalEnergy
  simp only [cubeIncrement_congr_ae R _ h]

/-- Normalized measure of a descendant is dominated by a multiple of the parent's. -/
theorem normalized_descendant_le {Q R : TriadicCube 2} {n : ℕ}
    (hR : R ∈ descendantsAtDepth Q n) :
    ∃ c : ℝ≥0∞, c ≠ ∞ ∧ normalizedCubeMeasure R ≤ c • normalizedCubeMeasure Q := by
  have hQ := normalizedCubeMeasure_eq_smul_open Q
  have hRm := normalizedCubeMeasure_eq_smul_open R
  have hb0 : ENNReal.ofReal ((cubeVolume Q)⁻¹) ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact inv_pos.mpr (cubeVolume_pos Q)
  have hbt : ENNReal.ofReal ((cubeVolume Q)⁻¹) ≠ ∞ := ENNReal.ofReal_ne_top
  have hμ : volumeMeasureOn (openCubeSet Q) =
      (ENNReal.ofReal ((cubeVolume Q)⁻¹))⁻¹ • normalizedCubeMeasure Q := by
    rw [hQ, smul_smul, ENNReal.inv_mul_cancel hb0 hbt, one_smul]
  have hle : volumeMeasureOn (openCubeSet R) ≤ volumeMeasureOn (openCubeSet Q) :=
    Measure.restrict_mono (openCubeSet_subset_of_mem_descendantsAtDepth hR) le_rfl
  refine ⟨ENNReal.ofReal ((cubeVolume R)⁻¹) * (ENNReal.ofReal ((cubeVolume Q)⁻¹))⁻¹,
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.inv_ne_top.2 hb0), ?_⟩
  rw [hRm, mul_smul, ← hμ]
  refine Measure.le_iff'.2 fun s => ?_
  simp only [Measure.smul_apply, smul_eq_mul]
  exact mul_le_mul' le_rfl (hle s)

/-- Restriction of a parent `L²` class to a descendant tile. -/
noncomputable def restrictLp {Q R : TriadicCube 2} {n : ℕ} (hR : R ∈ descendantsAtDepth Q n) :
    Lp ℝ 2 (normalizedCubeMeasure Q) →L[ℝ] Lp ℝ 2 (normalizedCubeMeasure R) :=
  Lp.LpToLpOfMeasureLeSMul (p := (2 : ℝ≥0∞)) (μ := normalizedCubeMeasure R)
    (ν := normalizedCubeMeasure Q) (c := (normalized_descendant_le hR).choose)
    (normalized_descendant_le hR).choose_spec.1
    (normalized_descendant_le hR).choose_spec.2

theorem restrictLp_ae {Q R : TriadicCube 2} {n : ℕ} (hR : R ∈ descendantsAtDepth Q n)
    (f : Lp ℝ 2 (normalizedCubeMeasure Q)) :
    (fun x => restrictLp hR f x) =ᵐ[normalizedCubeMeasure R] fun x => f x :=
  Lp.coeFn_LpToLpOfMeasureLeSMul (normalized_descendant_le hR).choose_spec.1
    (normalized_descendant_le hR).choose_spec.2 f

theorem ae_descendant {Q R : TriadicCube 2} {n : ℕ} (hR : R ∈ descendantsAtDepth Q n)
    {f g : Vec 2 → ℝ} (h : f =ᵐ[normalizedCubeMeasure Q] g) :
    f =ᵐ[normalizedCubeMeasure R] g :=
  h.filter_mono (Measure.absolutelyContinuous_of_le_smul
    (normalized_descendant_le hR).choose_spec.2).ae_le

/-- Measurability of the tiled positive Haar energy along a measurable family of `L²` coordinates. -/
theorem tiledPE_measurable {Ω : Type*} [MeasurableSpace Ω] (Q : TriadicCube 2) (n : ℕ)
    [MeasurableSpace (Lp ℝ 2 (normalizedCubeMeasure Q))]
    [BorelSpace (Lp ℝ 2 (normalizedCubeMeasure Q))]
    (u : Fin 2 → Ω → Lp ℝ 2 (normalizedCubeMeasure Q)) (hu : ∀ i, Measurable (u i)) :
    Measurable (fun ω => lemmaVTiledPositiveEnergy Q n (fun x i => u i ω x)) := by
  classical
  unfold lemmaVTiledPositiveEnergy descendantsAverage
  refine Measurable.const_mul (Finset.measurable_sum _ fun R hR => ?_) _
  unfold vectorPositiveHaarEnergy
  refine Finset.measurable_sum _ fun i _ => ?_
  letI : MeasurableSpace (Lp ℝ 2 (normalizedCubeMeasure R)) := borel _
  haveI : BorelSpace (Lp ℝ 2 (normalizedCubeMeasure R)) := ⟨rfl⟩
  have hcomp : Measurable (fun ω => restrictLp hR (u i ω)) :=
    (restrictLp hR).continuous.measurable.comp (hu i)
  have := primalEnergy_measurable_of_l2_map R _ hcomp
  convert this using 2 with ω
  exact (primalEnergy_congr_ae R _ (restrictLp_ae hR _).symm)

theorem liminf_add_le' (u v : ℕ → ℝ≥0∞) :
    liminf u atTop + liminf v atTop ≤ liminf (fun N => u N + v N) atTop := by
  rw [Filter.liminf_eq_iSup_iInf_of_nat, Filter.liminf_eq_iSup_iInf_of_nat,
    Filter.liminf_eq_iSup_iInf_of_nat]
  have hmu : Monotone (fun n => ⨅ i ≥ n, u i) := fun a b hab =>
    iInf₂_mono' fun i hi => ⟨i, hab.trans hi, le_rfl⟩
  have hmv : Monotone (fun n => ⨅ i ≥ n, v i) := fun a b hab =>
    iInf₂_mono' fun i hi => ⟨i, hab.trans hi, le_rfl⟩
  rw [ENNReal.iSup_add_iSup_of_monotone hmu hmv]
  refine iSup_mono fun n => ?_
  refine le_iInf₂ fun i hi => ?_
  exact add_le_add (iInf₂_le i hi) (iInf₂_le i hi)

theorem sum_liminf_le {ι : Type*} (s : Finset ι) (a : ι → ℕ → ℝ≥0∞) :
    ∑ r ∈ s, liminf (a r) atTop ≤ liminf (fun N => ∑ r ∈ s, a r N) atTop := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert r s hr ih =>
      rw [Finset.sum_insert hr]
      calc
        liminf (a r) atTop + ∑ r ∈ s, liminf (a r) atTop ≤
            liminf (a r) atTop + liminf (fun N => ∑ r ∈ s, a r N) atTop :=
          add_le_add le_rfl ih
        _ ≤ liminf (fun N => a r N + ∑ r ∈ s, a r N) atTop :=
          liminf_add_le' (a r) (fun N => ∑ r ∈ s, a r N)
        _ = _ := by simp only [Finset.sum_insert hr]

theorem ofReal_tiled (Q : TriadicCube 2) (n : ℕ) (F : Vec 2 → Fin 2 → ℝ) :
    ENNReal.ofReal (lemmaVTiledPositiveEnergy Q n F) =
      ENNReal.ofReal (((descendantsAtDepth Q n).card : ℝ)⁻¹) *
        ∑ R ∈ descendantsAtDepth Q n, ENNReal.ofReal (vectorPositiveHaarEnergy R F) := by
  unfold lemmaVTiledPositiveEnergy descendantsAverage
  rw [ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_sum_of_nonneg fun R _ => vectorPositiveHaarEnergy_nonneg R F]

/-- Lower semicontinuity of the tiled positive Haar energy under `L²` convergence of `H¹`
approximants. -/
theorem tiled_lsc (Q : TriadicCube 2) (n : ℕ)
    (fseq : ℕ → Fin 2 → Lp ℝ 2 (normalizedCubeMeasure Q))
    (f : Fin 2 → Lp ℝ 2 (normalizedCubeMeasure Q))
    (rawseq : ℕ → Fin 2 → Vec 2 → ℝ) (Gseq : ℕ → Fin 2 → Vec 2 → Vec 2)
    (hseq : ∀ i, Tendsto (fun N => fseq N i) atTop (𝓝 (f i)))
    (hrep : ∀ N i, (fun x => fseq N i x) =ᵐ[normalizedCubeMeasure Q] rawseq N i)
    (hG : ∀ N i j, MemLp (fun x => Gseq N i x j) 2 (normalizedCubeMeasure Q))
    (hweak : ∀ N i, HasWeakGradientOn (openCubeSet Q) (rawseq N i) (Gseq N i)) :
    ENNReal.ofReal (lemmaVTiledPositiveEnergy Q n (fun x i => f i x)) ≤
      liminf (fun N => ENNReal.ofReal
        (lemmaVTiledPositiveEnergy Q n (fun x i => fseq N i x))) atTop := by
  classical
  have hmeas : MeasurableSet (openCubeSet Q) :=
    (isOpenBoundedConvexDomain_openCubeSet Q).1.measurableSet
  have hcell : ∀ R ∈ descendantsAtDepth Q n,
      ENNReal.ofReal (vectorPositiveHaarEnergy R (fun x i => f i x)) ≤
        liminf (fun N => ENNReal.ofReal
          (vectorPositiveHaarEnergy R (fun x i => fseq N i x))) atTop := by
    intro R hR
    have hsub := openCubeSet_subset_of_mem_descendantsAtDepth hR
    have h := vectorPositiveHaarNorm_sq_lsc_of_l2_tendsto_h1 R
      (fun N i => restrictLp hR (fseq N i)) (fun i => restrictLp hR (f i)) rawseq Gseq
      (fun i => ((restrictLp hR).continuous.tendsto _).comp (hseq i))
      (fun N i => (restrictLp_ae hR _).trans (ae_descendant hR (hrep N i)))
      (fun N i j => memLp_on_descendant_of_memLp hR (hG N i j))
      (fun N i => hasWeakGradientOn_mono hsub hmeas (hweak N i))
    have e1 (g : Fin 2 → Lp ℝ 2 (normalizedCubeMeasure Q)) :
        vectorPositiveHaarNorm R (fun x i => restrictLp hR (g i) x) ^ 2 =
          vectorPositiveHaarEnergy R (fun x i => g i x) := by
      rw [← vecEnergy_eq_norm_sq]
      exact vecEnergy_congr_ae R (fun i => restrictLp_ae hR (g i))
    simpa only [e1] using h
  rw [ofReal_tiled]
  have hc : ENNReal.ofReal (((descendantsAtDepth Q n).card : ℝ)⁻¹) ≠ ⊤ := ENNReal.ofReal_ne_top
  calc
    _ ≤ ENNReal.ofReal (((descendantsAtDepth Q n).card : ℝ)⁻¹) *
        ∑ R ∈ descendantsAtDepth Q n, liminf (fun N => ENNReal.ofReal
          (vectorPositiveHaarEnergy R (fun x i => fseq N i x))) atTop :=
      mul_le_mul' le_rfl (Finset.sum_le_sum hcell)
    _ ≤ ENNReal.ofReal (((descendantsAtDepth Q n).card : ℝ)⁻¹) *
        liminf (fun N => ∑ R ∈ descendantsAtDepth Q n, ENNReal.ofReal
          (vectorPositiveHaarEnergy R (fun x i => fseq N i x))) atTop :=
      mul_le_mul' le_rfl (sum_liminf_le _ _)
    _ = _ := by
      rw [← ENNReal.liminf_const_mul_of_ne_top hc]
      simp only [ofReal_tiled]

end

end ASDExplicitGamma.Scalar
