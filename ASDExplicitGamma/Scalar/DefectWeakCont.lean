module

public import ASDExplicitGamma.Scalar.FlatSourceQ3PositiveHaar
public import ASDExplicitGamma.Scalar.DefectCoeff
public import ASDExplicitGamma.Scalar.DefectEnergyCarrierOperators

/-! Measurability of the tiled weak energy of the gradient of the `H10` representative of a
closed-graph point: coordinates of the gradient class on each tile are continuous in the point. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar

open MeasureTheory Homogenization ASDExplicitGamma.Triadic ASDExplicitGamma.Variational Filter
open scoped ENNReal Topology

noncomputable section

/-- Coordinate `i` of a Hilbert-vector class of `Q`, restricted to a sub-tile `R`, as an element
of the normalized `L²` of `R`. -/
def tileCoordCLM (Q R : TriadicCube 2) (hsub : cubeSet R ⊆ cubeSet Q) (i : Fin 2) :
    HilbertVectorL2 (openCubeSet Q) →L[ℝ] Lp ℝ 2 (normalizedCubeMeasure R) := by
  let μ := volumeMeasureOn (openCubeSet Q)
  let c : ℝ≥0∞ := ENNReal.ofReal ((cubeVolume R)⁻¹)
  have hc : c ≠ ∞ := ENNReal.ofReal_ne_top
  have hdom : normalizedCubeMeasure R ≤ c • μ := by
    have hmeasure : cubeMeasure Q = volumeMeasureOn (openCubeSet Q) := by
      rw [cubeMeasure, volumeMeasureOn]
      exact volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q
    show ENNReal.ofReal ((cubeVolume R)⁻¹) • cubeMeasure R ≤ c • volumeMeasureOn (openCubeSet Q)
    rw [← hmeasure]
    intro s
    simp only [Measure.smul_apply, smul_eq_mul]
    exact mul_le_mul' le_rfl (Measure.restrict_mono hsub le_rfl s)
  let toScalar : Lp (Vec 2) 2 μ →L[ℝ] Lp ℝ 2 μ :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) i).compLpL 2 μ
  let toNormalized : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 (normalizedCubeMeasure R) :=
    Lp.LpToLpOfMeasureLeSMul (p := (2 : ℝ≥0∞))
      (μ := normalizedCubeMeasure R) (ν := μ) (c := c) hc hdom
  exact toNormalized.comp (toScalar.comp
    (hilbertVectorL2ToVectorL2 (U := openCubeSet Q)))

theorem tileCoordCLM_ae (Q R : TriadicCube 2) (hsub : cubeSet R ⊆ cubeSet Q) (i : Fin 2)
    (F : HilbertVectorL2 (openCubeSet Q)) :
    tileCoordCLM Q R hsub i F =ᵐ[normalizedCubeMeasure R]
      fun x => (hilbertVectorL2ToVectorL2 (U := openCubeSet Q) F x) i := by
  let μ := volumeMeasureOn (openCubeSet Q)
  let c : ℝ≥0∞ := ENNReal.ofReal ((cubeVolume R)⁻¹)
  have hc : c ≠ ∞ := ENNReal.ofReal_ne_top
  have hdom : normalizedCubeMeasure R ≤ c • μ := by
    have hmeasure : cubeMeasure Q = volumeMeasureOn (openCubeSet Q) := by
      rw [cubeMeasure, volumeMeasureOn]
      exact volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q
    show ENNReal.ofReal ((cubeVolume R)⁻¹) • cubeMeasure R ≤ c • volumeMeasureOn (openCubeSet Q)
    rw [← hmeasure]
    intro s
    simp only [Measure.smul_apply, smul_eq_mul]
    exact mul_le_mul' le_rfl (Measure.restrict_mono hsub le_rfl s)
  have hproj : ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) i).compLpL 2 μ)
      (hilbertVectorL2ToVectorL2 (U := openCubeSet Q) F) =ᵐ[μ]
        fun x => (hilbertVectorL2ToVectorL2 (U := openCubeSet Q) F x) i :=
    ContinuousLinearMap.coeFn_compLpL
      (p := 2) (μ := μ)
      (L := ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) i)
      (f := hilbertVectorL2ToVectorL2 (U := openCubeSet Q) F)
  have htransfer := Lp.coeFn_LpToLpOfMeasureLeSMul hc hdom
    (((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) i).compLpL 2 μ)
      (hilbertVectorL2ToVectorL2 (U := openCubeSet Q) F))
  filter_upwards [htransfer,
    hproj.filter_mono (Measure.absolutelyContinuous_of_le_smul hdom).ae_le] with x hx₁ hx₂
  change ((Lp.LpToLpOfMeasureLeSMul (p := (2 : ℝ≥0∞))
      (μ := normalizedCubeMeasure R) (ν := μ) (c := c) hc hdom)
      (((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) i).compLpL 2 μ)
        (hilbertVectorL2ToVectorL2 (U := openCubeSet Q) F))) x = _
  rw [hx₁, hx₂]

noncomputable local instance wLp2MeasurableSpace (Q : TriadicCube 2) :
    MeasurableSpace (Lp ℝ 2 (normalizedCubeMeasure Q)) := borel _
noncomputable local instance wLp2BorelSpace (Q : TriadicCube 2) :
    BorelSpace (Lp ℝ 2 (normalizedCubeMeasure Q)) := ⟨rfl⟩
noncomputable local instance wLp2Opens (Q : TriadicCube 2) :
    OpensMeasurableSpace (Lp ℝ 2 (normalizedCubeMeasure Q)) := ⟨le_of_eq rfl⟩

theorem primalEnergy_measurable_of_l2_map'
    {Ω : Type*} [MeasurableSpace Ω] (q : ℝ) (hq0 : 0 ≤ q)
    (Q : TriadicCube 2)
    [MeasurableSpace (Lp ℝ 2 (normalizedCubeMeasure Q))]
    [BorelSpace (Lp ℝ 2 (normalizedCubeMeasure Q))]
    [OpensMeasurableSpace (Lp ℝ 2 (normalizedCubeMeasure Q))]
    (u : Ω → Lp ℝ 2 (normalizedCubeMeasure Q))
    (hu : Measurable u) :
    Measurable (fun ω => primalEnergy Q q (fun x => u ω x)) := by
  classical
  let a : ℕ → Ω → ℝ := fun n ω =>
    q ^ (n + 1) * ‖cubeIncrementL2CLM Q (n + 1) (u ω)‖ ^ 2
  let S : Ω → ℝ≥0∞ := fun ω => ∑' n, ENNReal.ofReal (a n ω)
  have ha (n : ℕ) : Measurable (a n) := by
    dsimp [a]
    have hnorm : Measurable (fun ω =>
        ‖cubeIncrementL2CLM Q (n + 1) (u ω)‖ ^ 2) :=
      (((cubeIncrementL2CLM Q (n + 1)).continuous.measurable.comp hu).norm.pow_const 2)
    simpa only [mul_comm] using hnorm.const_mul (q ^ (n + 1))
  have ha_nonneg (n : ℕ) (ω : Ω) : 0 ≤ a n ω := by
    dsimp [a]
    positivity
  have hS : Measurable S := by
    dsimp [S]
    exact Measurable.ennreal_tsum fun n => (ha n).ennreal_ofReal
  have htsum (ω : Ω) :
      (∑' n, a n ω) = (S ω).toReal := by
    by_cases htop : S ω = ∞
    · have hnot : ¬ Summable (fun n => a n ω) := by
        intro hs
        have hfinite := hs.tsum_ofReal_ne_top
        have hSfinite : S ω ≠ ∞ := by
          intro hInf
          exact hfinite (by simpa [S] using hInf)
        exact hSfinite htop
      rw [tsum_eq_zero_of_not_summable hnot, htop]
      rfl
    · let b : ℕ → NNReal := fun n => Real.toNNReal (a n ω)
      have hb (n : ℕ) : (b n : ℝ≥0∞) = ENNReal.ofReal (a n ω) := by
        simp [b, ENNReal.ofReal, Real.toNNReal_of_nonneg (ha_nonneg n ω)]
      have hsumB : Summable b := by
        apply (ENNReal.tsum_coe_ne_top_iff_summable).mp
        rw [show (∑' n, (b n : ℝ≥0∞)) = S ω from by
          apply tsum_congr
          intro n
          exact hb n]
        exact htop
      have hsumA : Summable (fun n => a n ω) := by
        have hsumReal : Summable (fun n => (b n : ℝ)) :=
          NNReal.summable_coe.2 hsumB
        have hEq : (fun n => (b n : ℝ)) = fun n => a n ω := by
          funext n
          dsimp [b]
          exact Real.coe_toNNReal _ (ha_nonneg n ω)
        exact hEq ▸ hsumReal
      have hrepr : ENNReal.ofReal (∑' n, a n ω) = S ω := by
        dsimp [S]
        exact ENNReal.ofReal_tsum_of_nonneg (fun n => ha_nonneg n ω) hsumA
      have hsum_nonneg : 0 ≤ (∑' n, a n ω) :=
        tsum_nonneg fun n => ha_nonneg n ω
      calc
        (∑' n, a n ω) = (ENNReal.ofReal (∑' n, a n ω)).toReal := by
          rw [ENNReal.toReal_ofReal hsum_nonneg]
        _ = (S ω).toReal := by rw [hrepr]
  have hbaseEq :
      (fun ω => energy Q (cubeIncrement Q 0 (fun x => u ω x))) =
        fun ω => ‖cubeIncrementL2CLM Q 0 (u ω)‖ ^ 2 := by
    funext ω
    exact energy_cubeIncrement_eq_clm_norm_sq Q 0 (u ω)
  have hbase : Measurable
      (fun ω => energy Q (cubeIncrement Q 0 (fun x => u ω x))) := by
    rw [hbaseEq]
    exact (((cubeIncrementL2CLM Q 0).continuous.measurable.comp hu).norm.pow_const 2)
  have hEq (ω : Ω) :
      primalEnergy Q q (fun x => u ω x) =
        energy Q (cubeIncrement Q 0 (fun x => u ω x)) + (S ω).toReal := by
    rw [primalEnergy]
    have hterm (n : ℕ) :
        q ^ (n + 1) * energy Q
          (cubeIncrement Q (n + 1) (fun x => u ω x)) = a n ω := by
      rw [energy_cubeIncrement_eq_clm_norm_sq]
    rw [tsum_congr hterm, htsum ω]
  have hresult : Measurable
      (fun ω => energy Q (cubeIncrement Q 0 (fun x => u ω x)) + (S ω).toReal) :=
    hbase.add hS.ennreal_toReal
  rw [show (fun ω => primalEnergy Q q (fun x => u ω x)) =
      fun ω => energy Q (cubeIncrement Q 0 (fun x => u ω x)) + (S ω).toReal from by
        funext ω
        exact hEq ω]
  exact hresult

theorem ae_tile (Q R : TriadicCube 2) (hsub : cubeSet R ⊆ cubeSet Q) {f g : Vec 2 → Vec 2}
    (h : f =ᵐ[volumeMeasureOn (openCubeSet Q)] g) : f =ᵐ[normalizedCubeMeasure R] g := by
  have hmeasure : cubeMeasure Q = volumeMeasureOn (openCubeSet Q) := by
    rw [cubeMeasure, volumeMeasureOn]
    exact volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q
  have h1 : f =ᵐ[cubeMeasure Q] g := by rw [hmeasure]; exact h
  have h2 : f =ᵐ[cubeMeasure R] g :=
    (Measure.absolutelyContinuous_of_le (Measure.restrict_mono hsub le_rfl)).ae_le h1
  rw [normalizedCubeMeasure]
  exact Measure.ae_smul_measure h2 _

local instance wH10Measurable (nQ : ℤ) :
    MeasurableSpace (H10GraphClosedSpace (openCubeSet (originCube 2 nQ))) := borel _

local instance wH10Borel (nQ : ℤ) :
    BorelSpace (H10GraphClosedSpace (openCubeSet (originCube 2 nQ))) := ⟨rfl⟩

local instance wVecMeasurable (Q : TriadicCube 2) :
    MeasurableSpace (HilbertVectorL2 (openCubeSet Q)) := borel _

local instance wVecBorel (Q : TriadicCube 2) :
    BorelSpace (HilbertVectorL2 (openCubeSet Q)) := ⟨rfl⟩

/-- The tiled weak energy of the gradient of the representative is measurable in the point. -/
theorem weak_energy_measurable {𝒪 : Type*} [MeasurableSpace 𝒪] (nQ : ℤ) (m : ℕ)
    (zs : 𝒪 → H10GraphClosedSpace (openCubeSet (originCube 2 nQ))) (hz : Measurable zs) :
    Measurable (fun o => lemmaVTiledWeakEnergy (originCube 2 nQ) m
      (rep'' nQ (zs o)).toH1Function.grad) := by
  classical
  unfold lemmaVTiledWeakEnergy descendantsAverage
  refine Measurable.const_mul (Finset.measurable_sum _ fun R hR => ?_) _
  have hsub : cubeSet R ⊆ cubeSet (originCube 2 nQ) :=
    cubeSet_subset_of_mem_descendantsAtDepth hR
  have hG : Measurable (fun o => H10GraphClosed.gradientCLM (zs o)) :=
    (H10GraphClosed.gradientCLM (d := 2) (U := openCubeSet (originCube 2 nQ))).continuous.measurable.comp hz
  have hc : ∀ i : Fin 2, Measurable (fun o => tileCoordCLM (originCube 2 nQ) R hsub i
      (H10GraphClosed.gradientCLM (zs o))) := fun i =>
    (tileCoordCLM (originCube 2 nQ) R hsub i).continuous.measurable.comp hG
  have hmem : ∀ o (i : Fin 2), MemLp (fun x => (rep'' nQ (zs o)).toH1Function.grad x i) 2
      (normalizedCubeMeasure R) := fun o i =>
    (rep'' nQ (zs o)).toH1Function.grad_memL2_normalizedCubeMeasure_of_mem_descendantsAtDepth hR i
  have hform : ∀ o, vectorWeakHaarEnergy R (rep'' nQ (zs o)).toH1Function.grad =
      ∑ i : Fin 2, primalEnergy R (Real.sqrt 3)⁻¹
        (fun x => tileCoordCLM (originCube 2 nQ) R hsub i
          (H10GraphClosed.gradientCLM (zs o)) x) := by
    intro o
    let Gz := H10GraphClosed.gradientCLM (zs o)
    have hae : (rep'' nQ (zs o)).toH1Function.grad =ᵐ[volumeMeasureOn (openCubeSet (originCube 2 nQ))]
        hilbertVectorL2ToVectorL2 (U := openCubeSet (originCube 2 nQ)) Gz :=
      (graphPotentialField_ofRepresentative (originCube 2 nQ) (ULift.up.{0} (zs o))).symm
    have hae' := ae_tile (originCube 2 nQ) R hsub hae
    have hcoord : ∀ i : Fin 2, (fun x => tileCoordCLM (originCube 2 nQ) R hsub i Gz x) =ᵐ[normalizedCubeMeasure R]
        fun x => (hilbertVectorL2ToVectorL2 (U := openCubeSet (originCube 2 nQ)) Gz x) i :=
      fun i => tileCoordCLM_ae (originCube 2 nQ) R hsub i Gz
    have hGmem : ∀ i : Fin 2, MemLp (fun p => (fun x (i : Fin 2) =>
        tileCoordCLM (originCube 2 nQ) R hsub i Gz x) p i) 2 (normalizedCubeMeasure R) :=
      fun i => Lp.memLp _
    have hEq : (rep'' nQ (zs o)).toH1Function.grad =ᵐ[normalizedCubeMeasure R]
        (fun x (i : Fin 2) => tileCoordCLM (originCube 2 nQ) R hsub i Gz x) := by
      have hall : ∀ᵐ x ∂normalizedCubeMeasure R, ∀ i : Fin 2,
          tileCoordCLM (originCube 2 nQ) R hsub i Gz x =
            hilbertVectorL2ToVectorL2 (U := openCubeSet (originCube 2 nQ)) Gz x i :=
        ae_all_iff.2 hcoord
      filter_upwards [hae', hall] with x hx1 hx2
      funext i
      rw [hx1, hx2]
    rw [vectorWeakHaarEnergy_congr_ae R (fun i => hmem o i) hGmem hEq]
    unfold vectorWeakHaarEnergy dualEnergy
    rfl
  have : (fun o => vectorWeakHaarEnergy R (rep'' nQ (zs o)).toH1Function.grad) =
      fun o => ∑ i : Fin 2, primalEnergy R (Real.sqrt 3)⁻¹
        (fun x => tileCoordCLM (originCube 2 nQ) R hsub i
          (H10GraphClosed.gradientCLM (zs o)) x) := funext hform
  show Measurable (fun o => vectorWeakHaarEnergy R (rep'' nQ (zs o)).toH1Function.grad)
  rw [this]
  exact Finset.measurable_sum _ fun i _ =>
    primalEnergy_measurable_of_l2_map' (Real.sqrt 3)⁻¹ (inv_nonneg.2 (Real.sqrt_nonneg _)) R
      (fun o => tileCoordCLM (originCube 2 nQ) R hsub i (H10GraphClosed.gradientCLM (zs o)))
      (hc i)

end

end ASDExplicitGamma.Scalar
