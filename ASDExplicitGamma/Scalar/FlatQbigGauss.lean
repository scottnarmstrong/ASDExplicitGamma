module

public import ASDExplicitGamma.Scalar.FlatQbigMeas
public import ASDExplicitGamma.Scalar.FlatQbigFiniteChaos
public import ASDExplicitGamma.Scalar.FlatSourceQ3LpBridge
public import ASDExplicitGamma.Scalar.FlatSourceQ3PositiveHaar
public import ASDExplicitGamma.Scalar.FlatSourceFiniteChaos
public import ASDExplicitGamma.Scalar.ChaosHilbertSymmetrization
public import ASDExplicitGamma.Scalar.FlatSourceC1Multiplier
public import ASDExplicitGamma.Main.CMRegularity
public import ASDExplicitGamma.Gaussian.Q3SobolevOperator

/-! Q_big flat successor: the tiled positive Haar energy of the fixed physical q3 product,
by the finite-mode envelope, Fatou and tile lower semicontinuity. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Homogenization Filter
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Triadic ASDExplicitGamma.Variational
open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open scoped ENNReal Topology

namespace ASDExplicitGamma.Scalar

noncomputable section

/-- Fatou transfer of an expectation cap through a pathwise lower bound by a `liminf`. -/
theorem lintegral_of_liminf {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (T : Ω → ℝ) (Tn : ℕ → Ω → ℝ) (C : ℝ)
    (hTn : ∀ N, Measurable (Tn N))
    (hLSC : ∀ᵐ ω ∂μ, ENNReal.ofReal (T ω) ≤
      liminf (fun N => ENNReal.ofReal (Tn N ω)) atTop)
    (hcap : ∀ N, ∫⁻ ω, ENNReal.ofReal (Tn N ω) ∂μ ≤ ENNReal.ofReal C) :
    ∫⁻ ω, ENNReal.ofReal (T ω) ∂μ ≤ ENNReal.ofReal C := by
  have hfatou := lintegral_liminf_le' (μ := μ) (u := atTop)
    (f := fun N ω => ENNReal.ofReal (Tn N ω))
    (fun N => (ENNReal.measurable_ofReal.comp (hTn N)).aemeasurable)
  calc
    _ ≤ ∫⁻ ω, liminf (fun N => ENNReal.ofReal (Tn N ω)) atTop ∂μ := lintegral_mono_ae hLSC
    _ ≤ liminf (fun N => ∫⁻ ω, ENNReal.ofReal (Tn N ω) ∂μ) atTop := hfatou
    _ ≤ ENNReal.ofReal C :=
      liminf_le_of_frequently_le (Frequently.of_forall fun N => hcap N)

/-- Fatou transfer of an `L^(128/127)` cap through a pathwise lower bound by a `liminf`. -/
theorem L128_of_liminf {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (T : Ω → ℝ) (Tn : ℕ → Ω → ℝ) (C : ℝ)
    (hTmeas : Measurable T) (hTn : ∀ N, Measurable (Tn N))
    (hT0 : ∀ ω, 0 ≤ T ω) (hTn0 : ∀ N ω, 0 ≤ Tn N ω)
    (hLSC : ∀ᵐ ω ∂μ, ENNReal.ofReal (T ω) ≤
      liminf (fun N => ENNReal.ofReal (Tn N ω)) atTop)
    (hcap : ∀ N, eLpNorm (Tn N) (ENNReal.ofReal (128 / 127 : ℝ)) μ ≤ ENNReal.ofReal C) :
    eLpNorm T (ENNReal.ofReal (128 / 127 : ℝ)) μ ≤ ENNReal.ofReal C := by
  let q : ℝ := 128 / 127
  let p : ℝ≥0∞ := ENNReal.ofReal q
  let W : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal (T ω) ^ q
  let Wn : ℕ → Ω → ℝ≥0∞ := fun N ω => ENNReal.ofReal (Tn N ω) ^ q
  have hqpos : 0 < q := by norm_num [q]
  have hqne : q ≠ 0 := hqpos.ne'
  have hqnonneg : 0 ≤ q := hqpos.le
  have hTnENN (N : ℕ) : Measurable (fun ω => ENNReal.ofReal (Tn N ω)) :=
    ENNReal.measurable_ofReal.comp (hTn N)
  have hWnMeas (N : ℕ) : Measurable (Wn N) := by
    dsimp [Wn]
    exact ENNReal.continuous_rpow_const.measurable.comp (hTnENN N)
  have hpowerIntegralEq (N : ℕ) :
      (∫⁻ ω, Wn N ω ∂μ) = eLpNorm (Tn N) p μ ^ q := by
    have hcongr : Wn N =ᵐ[μ] fun ω => ‖Tn N ω‖ₑ ^ q := by
      filter_upwards [] with ω
      simp [Wn, Real.enorm_eq_ofReal (hTn0 N ω)]
    calc
      _ = eLpNorm (Wn N) 1 μ := by
        symm
        rw [eLpNorm_one_eq_lintegral_enorm (hWnMeas N).aestronglyMeasurable]
        simp [Wn]
      _ = eLpNorm (fun ω => ‖Tn N ω‖ₑ ^ q) 1 μ := eLpNorm_congr_ae hcongr
      _ = eLpNorm (Tn N) (1 * ENNReal.ofReal q) μ ^ q :=
        eLpNorm_enorm_rpow (p := 1) (f := Tn N) (hTn N).aestronglyMeasurable hqpos
      _ = eLpNorm (Tn N) p μ ^ q := by simp [p]
  have hpowerCap (N : ℕ) : (∫⁻ ω, Wn N ω ∂μ) ≤ ENNReal.ofReal C ^ q := by
    rw [hpowerIntegralEq N]
    exact ENNReal.rpow_le_rpow (hcap N) hqnonneg
  have hlimintUpper : liminf (fun N => ∫⁻ ω, Wn N ω ∂μ) atTop ≤ ENNReal.ofReal C ^ q :=
    liminf_le_of_frequently_le (Frequently.of_forall fun N => hpowerCap N)
  have hpowerLSC : ∀ᵐ ω ∂μ, W ω ≤ liminf (fun N => Wn N ω) atTop := by
    filter_upwards [hLSC] with ω hω
    have hlim : liminf (fun N => Wn N ω) atTop =
        (liminf (fun N => ENNReal.ofReal (Tn N ω)) atTop) ^ q := by
      change liminf (fun N =>
          ENNReal.orderIsoRpow q hqpos (ENNReal.ofReal (Tn N ω))) atTop =
        ENNReal.orderIsoRpow q hqpos
          (liminf (fun N => ENNReal.ofReal (Tn N ω)) atTop)
      refine (OrderIso.liminf_apply (ENNReal.orderIsoRpow q hqpos) ?_ ?_ ?_ ?_).symm <;>
        isBoundedDefault
    have hp := ENNReal.rpow_le_rpow hω hqnonneg
    simpa [W, hlim] using hp
  have hfatou := lintegral_liminf_le' (μ := μ) (u := atTop)
    (fun N => (hWnMeas N).aemeasurable)
  have hfixedIntegral : (∫⁻ ω, W ω ∂μ) ≤ ENNReal.ofReal C ^ q := by
    calc
      _ ≤ ∫⁻ ω, liminf (fun N => Wn N ω) atTop ∂μ := lintegral_mono_ae hpowerLSC
      _ ≤ liminf (fun N => ∫⁻ ω, Wn N ω ∂μ) atTop := hfatou
      _ ≤ ENNReal.ofReal C ^ q := hlimintUpper
  have hp0 : p ≠ 0 := by simp [p, q]
  have hptop : p ≠ ∞ := ENNReal.ofReal_ne_top
  have hLpFormula : eLpNorm T p μ = (∫⁻ ω, W ω ∂μ) ^ (1 / q) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hptop hTmeas.aestronglyMeasurable]
    rw [show p.toReal = q by
      change (ENNReal.ofReal q).toReal = q
      exact ENNReal.toReal_ofReal hqnonneg]
    congr 1
    apply lintegral_congr_ae
    filter_upwards [] with ω
    simp [W, Real.enorm_eq_ofReal (hT0 ω)]
  calc
    eLpNorm T p μ = (∫⁻ ω, W ω ∂μ) ^ (1 / q) := hLpFormula
    _ ≤ (ENNReal.ofReal C ^ q) ^ (1 / q) := ENNReal.rpow_le_rpow hfixedIntegral (by positivity)
    _ = ENNReal.ofReal C := by
      simpa [one_div] using ENNReal.rpow_rpow_inv hqne (ENNReal.ofReal C)

section Fixed

noncomputable local instance gaussLp2MeasurableSpace (Q : TriadicCube 2) :
    MeasurableSpace (Lp ℝ 2 (normalizedCubeMeasure Q)) := borel _
noncomputable local instance gaussLp2BorelSpace (Q : TriadicCube 2) :
    BorelSpace (Lp ℝ 2 (normalizedCubeMeasure Q)) := ⟨rfl⟩
noncomputable local instance gaussVectorOpens (Q : TriadicCube 2) :
    OpensMeasurableSpace (HilbertVectorL2 (openCubeSet Q)) := ⟨le_of_eq rfl⟩
noncomputable local instance gaussRangeOpens
    (a₀ b₀ c₀ d₀ β : ℝ) (L : {l : ℝ // 0 < l}) :
    OpensMeasurableSpace (Q3H3Range a₀ b₀ c₀ d₀ β L) := ⟨le_of_eq rfl⟩

variable {a₀ b₀ c₀ d₀ : ℝ}

/-- The finite-mode physical q3 product as a Hilbert field. -/
noncomputable def vfin (Q : TriadicCube 2) (hab : a₀ < b₀) (hcd : c₀ < d₀) (β : ℝ)
    (L : {l : ℝ // 0 < l}) (e : Vec 2) (N : ℕ) (ω : ℕ → ℝ) :
    HilbertVectorL2 (openCubeSet Q) :=
  flatSourceQ3ValueLInf Q hab hcd β L
      (gaussianPartialSum (q3H3Directions a₀ b₀ c₀ d₀ β L whiteBasis) N ω) •
    flatSourceQ3ProjectedL2 Q hab hcd e β L
      (gaussianPartialSum (q3H3Directions a₀ b₀ c₀ d₀ β L whiteBasis) N ω)

/-- The fixed physical q3 product as a Hilbert field. -/
noncomputable def vfix (Q : TriadicCube 2) (hab : a₀ < b₀) (hcd : c₀ < d₀) (β : ℝ)
    (L : {l : ℝ // 0 < l}) (e : Vec 2) (ω : ℕ → ℝ) :
    HilbertVectorL2 (openCubeSet Q) :=
  flatSourceQ3ValueLInf Q hab hcd β L
      (q3H3Series a₀ b₀ c₀ d₀ β L whiteBasis ω) •
    flatSourceQ3ProjectedL2 Q hab hcd e β L
      (q3H3Series a₀ b₀ c₀ d₀ β L whiteBasis ω)

theorem tiled_congr_ae (Q : TriadicCube 2) (n : ℕ) {F G : Vec 2 → Fin 2 → ℝ}
    (h : ∀ i, (fun x => F x i) =ᵐ[normalizedCubeMeasure Q] (fun x => G x i)) :
    lemmaVTiledPositiveEnergy Q n F = lemmaVTiledPositiveEnergy Q n G := by
  unfold lemmaVTiledPositiveEnergy descendantsAverage
  dsimp only
  congr 1
  exact Finset.sum_congr rfl fun R hR =>
    vecEnergy_congr_ae R fun i => ae_descendant hR (h i)

theorem vfin_coord (Q : TriadicCube 2) (hab : a₀ < b₀) (hcd : c₀ < d₀)
    (hQ : openCubeSet Q ⊆ openRectangle a₀ b₀ c₀ d₀) (β : ℝ) (L : {l : ℝ // 0 < l})
    (e : Vec 2) (N : ℕ) (ω : ℕ → ℝ) (i : Fin 2) :
    hilbertVectorL2_normalizedCoordCLM Q i (vfin Q hab hcd β L e N ω) =
      (flatSourceQ3FiniteProductComponent Q β L e N ω i).memL2_normalizedCubeMeasure.toLp
        (flatSourceQ3FiniteProductComponent Q β L e N ω i).toFun := by
  classical
  apply Lp.ext
  let μ := volumeMeasureOn (openCubeSet Q)
  let c : ℝ≥0∞ := ENNReal.ofReal ((cubeVolume Q)⁻¹)
  have hdom : normalizedCubeMeasure Q ≤ c • μ := by
    rw [show normalizedCubeMeasure Q = c • μ from normalizedCubeMeasure_eq_smul_open Q]
  let U := flatSourceQ3FiniteProductComponent Q β L e N ω i
  have hcoord := hilbertVectorL2_normalizedCoordCLM_ae Q i (vfin Q hab hcd β L e N ω)
  have hfinite : (fun x => ((vfin Q hab hcd β L e N ω) x).toVec i) =ᵐ[
      volumeMeasureOn (openCubeSet Q)] U.toFun :=
    flat_source_q3_finite_product_component_ae Q hab hcd hQ e N ω β L i
  have hfinite' := hfinite.filter_mono (Measure.absolutelyContinuous_of_le_smul hdom).ae_le
  have htoLp : U.memL2_normalizedCubeMeasure.toLp U.toFun =ᵐ[normalizedCubeMeasure Q] U.toFun :=
    MemLp.coeFn_toLp U.memL2_normalizedCubeMeasure
  have hback := coeFn_hilbertVectorL2ToVectorL2 (U := openCubeSet Q)
    (f := vfin Q hab hcd β L e N ω)
  have hback' := hback.filter_mono (Measure.absolutelyContinuous_of_le_smul hdom).ae_le
  have hfiniteVec : (fun x => (hilbertVectorL2ToVectorL2 (U := openCubeSet Q)
      (vfin Q hab hcd β L e N ω) x) i) =ᵐ[normalizedCubeMeasure Q] U.toFun := by
    filter_upwards [hback', hfinite'] with x hback hfinite
    calc
      (hilbertVectorL2ToVectorL2 (U := openCubeSet Q) (vfin Q hab hcd β L e N ω) x) i =
          (((vfin Q hab hcd β L e N ω) x).toVec) i := by rw [hback]
      _ = U.toFun x := hfinite
  filter_upwards [hcoord, hfiniteVec, htoLp] with x hcoord hfinite htoLp
  rw [hcoord, hfinite, htoLp]

theorem Phi_measurable_of_V {Ω : Type*} [MeasurableSpace Ω] (Q : TriadicCube 2) (n : ℕ)
    (V : Ω → HilbertVectorL2 (openCubeSet Q)) (hV : Measurable V) :
    Measurable (fun ω => phi' Q n (V ω)) :=
  tiledPE_measurable Q n (fun i ω => hilbertVectorL2_normalizedCoordCLM Q i (V ω))
    (fun i => (hilbertVectorL2_normalizedCoordCLM Q i).continuous.measurable.comp hV)

theorem vfin_measurable (Q : TriadicCube 2) (hab : a₀ < b₀) (hcd : c₀ < d₀) (β : ℝ)
    (L : {l : ℝ // 0 < l}) (e : Vec 2) (N : ℕ) :
    Measurable (vfin Q hab hcd β L e N) := by
  classical
  let dirs := q3H3Directions a₀ b₀ c₀ d₀ β L whiteBasis
  let μ := volumeMeasureOn (openCubeSet Q)
  have hprod : Continuous (fun z : Q3H3Range a₀ b₀ c₀ d₀ β L =>
      flatSourceQ3ValueLInf Q hab hcd β L z •
        flatSourceQ3ProjectedL2 Q hab hcd e β L z) := by
    rw [continuous_iff_seqContinuous]
    intro zseq z hz
    have hf := (flatSourceQ3ValueLInf Q hab hcd β L).continuous.tendsto z |>.comp hz
    have hg := (flatSourceQ3ProjectedL2 Q hab hcd e β L).continuous.tendsto z |>.comp hz
    exact lp_product_tendsto_of_tendsto μ _ _ _ _ hf hg
  have hpartialInput : Measurable (fun ω : ℕ → ℝ => gaussianPartialSum dirs N ω) := by
    have hc : Continuous (fun ω : ℕ → ℝ => ∑ j ∈ Finset.range N, ω j • dirs j) := by
      apply continuous_finsetSum
      intro j hj
      exact (continuous_apply j).smul continuous_const
    simpa [gaussianPartialSum] using hc.measurable
  exact hprod.measurable.comp hpartialInput

theorem vfix_measurable (Q : TriadicCube 2) (hab : a₀ < b₀) (hcd : c₀ < d₀) (β : ℝ)
    (L : {l : ℝ // 0 < l}) (e : Vec 2) :
    Measurable (vfix Q hab hcd β L e) := by
  classical
  let μ := volumeMeasureOn (openCubeSet Q)
  have hproduct : Continuous (fun z : Q3H3Range a₀ b₀ c₀ d₀ β L =>
      flatSourceQ3ValueLInf Q hab hcd β L z •
        flatSourceQ3ProjectedL2 Q hab hcd e β L z) := by
    rw [continuous_iff_seqContinuous]
    intro zseq z₀ hz₀
    have hf := (flatSourceQ3ValueLInf Q hab hcd β L).continuous.tendsto z₀ |>.comp hz₀
    have hg := (flatSourceQ3ProjectedL2 Q hab hcd e β L).continuous.tendsto z₀ |>.comp hz₀
    exact lp_product_tendsto_of_tendsto μ _ _ _ _ hf hg
  have hz : Measurable (q3H3Series a₀ b₀ c₀ d₀ β L whiteBasis) := by
    exact (@stronglyMeasurable_gaussianSeriesLimit
      (Q3H3Range a₀ b₀ c₀ d₀ β L) inferInstance
      (instQ3H3RangeInnerProductSpace a₀ b₀ c₀ d₀ β L)
      inferInstance inferInstance inferInstance inferInstance inferInstance
      (q3H3Directions a₀ b₀ c₀ d₀ β L whiteBasis)
      (q3H3Directions_summable a₀ b₀ c₀ d₀ β L whiteBasis)).measurable
  exact hproduct.measurable.comp hz

/-- Pathwise tile bound for a finite-mode product. -/
theorem phi_vfin_le (Q : TriadicCube 2) (hab : a₀ < b₀) (hcd : c₀ < d₀)
    (hQ : openCubeSet Q ⊆ openRectangle a₀ b₀ c₀ d₀) (β : ℝ) (L : {l : ℝ // 0 < l})
    (e : Vec 2) (N : ℕ) (ω : ℕ → ℝ) :
    phi' Q 134 (vfin Q hab hcd β L e N ω) ≤
      (∑ i : Fin 2, energy Q (fun x =>
        (flatSourceQ3FiniteProductComponent Q β L e N ω i).toFun x)) +
        (467 / 1000 : ℝ) ^ 2 * tileSide Q ^ 2 *
          ∑ i : Fin 2, ∑ j : Fin 2, energy Q (fun x =>
            (flatSourceQ3FiniteProductComponent Q β L e N ω i).grad x j) := by
  have h1 : phi' Q 134 (vfin Q hab hcd β L e N ω) =
      lemmaVTiledPositiveEnergy Q 134 (fun x i =>
        (flatSourceQ3FiniteProductComponent Q β L e N ω i).toFun x) := by
    unfold phi'
    apply tiled_congr_ae
    intro i
    rw [vfin_coord Q hab hcd hQ β L e N ω i]
    exact MemLp.coeFn_toLp _
  rw [h1]
  have := tiled_positiveHaar_le_l2_add_gradient Q 134
    (fun x i => (flatSourceQ3FiniteProductComponent Q β L e N ω i).toFun x)
    (fun x i j => (flatSourceQ3FiniteProductComponent Q β L e N ω i).grad x j)
    (fun i => (flatSourceQ3FiniteProductComponent Q β L e N ω i).memL2_normalizedCubeMeasure)
    (fun i j => (flatSourceQ3FiniteProductComponent Q β L e N ω i).grad_memL2_normalizedCubeMeasure j)
    (fun i => (flatSourceQ3FiniteProductComponent Q β L e N ω i).hasWeakGradient)
  simpa [tileSide] using this

theorem phi_nonneg' (Q : TriadicCube 2) (n : ℕ) (V : HilbertVectorL2 (openCubeSet Q)) :
    0 ≤ phi' Q n V := lemmaVTiledPositiveEnergy_nonneg Q n _

/-- Expected tiled energy of a finite-mode product. -/
theorem finite_tiled_lintegral_le (Q : TriadicCube 2) (hab : a₀ < b₀) (hcd : c₀ < d₀)
    (hQ : openCubeSet Q ⊆ openRectangle a₀ b₀ c₀ d₀)
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (e : Vec 2) (he : Book.Ch02.vecNorm e = 1) (k : ℤ) (N : ℕ) :
    ∫⁻ ω, ENNReal.ofReal (phi' Q 134 (vfin Q hab hcd (q3ModelAmplitude M h k)
        (q3ModelLength k) e N ω)) ∂standardGaussianInfinitePi ≤
      ENNReal.ofReal ((3 / 2 : ℝ) * (q3ModelAmplitude M h k) ^ 4 +
        (467 / 1000 : ℝ) ^ 2 * tileSide Q ^ 2 *
          ((936 / 5 : ℝ) * (q3ModelAmplitude M h k) ^ 4 / (q3ModelLength k).1 ^ 2)) := by
  obtain ⟨hInt, hle⟩ := flat_source_q3_finite_h1_product_vector_expected_norm_sq_le
    Q hab hcd hQ M h hM e he k N
  have hpt (ω : ℕ → ℝ) : phi' Q 134 (vfin Q hab hcd (q3ModelAmplitude M h k)
      (q3ModelLength k) e N ω) ≤
      ‖tFlatSourceQ3FiniteH1ProductVector Q (q3ModelAmplitude M h k)
        (q3ModelLength k) e N ω‖ ^ 2 := by
    rw [flat_source_q3_finite_h1_product_vector_norm_sq_eq_energy]
    exact phi_vfin_le Q hab hcd hQ _ _ e N ω
  calc
    _ ≤ ∫⁻ ω, ENNReal.ofReal (‖tFlatSourceQ3FiniteH1ProductVector Q
        (q3ModelAmplitude M h k) (q3ModelLength k) e N ω‖ ^ 2)
          ∂standardGaussianInfinitePi :=
      lintegral_mono fun ω => ENNReal.ofReal_le_ofReal (hpt ω)
    _ = ENNReal.ofReal (∫ ω, ‖tFlatSourceQ3FiniteH1ProductVector Q
        (q3ModelAmplitude M h k) (q3ModelLength k) e N ω‖ ^ 2
          ∂standardGaussianInfinitePi) :=
      (ofReal_integral_eq_lintegral_ofReal hInt (Filter.Eventually.of_forall fun ω => sq_nonneg _)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal hle

/-- The tile lower semicontinuity along the finite-mode approximation. -/
theorem fixed_tiled_lsc (Q : TriadicCube 2) (hab : a₀ < b₀) (hcd : c₀ < d₀)
    (hQ : openCubeSet Q ⊆ openRectangle a₀ b₀ c₀ d₀) (e : Vec 2) (β : ℝ)
    (L : {l : ℝ // 0 < l}) :
    ∀ᵐ ω ∂standardGaussianInfinitePi,
      ENNReal.ofReal (phi' Q 134 (vfix Q hab hcd β L e ω)) ≤
        liminf (fun N => ENNReal.ofReal (phi' Q 134 (vfin Q hab hcd β L e N ω))) atTop := by
  classical
  filter_upwards [flat_source_q3_fixed_product_tendsto Q hab hcd e β L] with ω hω
  have hω' : Tendsto (fun N => vfin Q hab hcd β L e N ω) atTop
      (𝓝 (vfix Q hab hcd β L e ω)) := hω
  let fseq : ℕ → Fin 2 → Lp ℝ 2 (normalizedCubeMeasure Q) := fun N i =>
    (flatSourceQ3FiniteProductComponent Q β L e N ω i).memL2_normalizedCubeMeasure.toLp
      (flatSourceQ3FiniteProductComponent Q β L e N ω i).toFun
  have hclass (N : ℕ) (i : Fin 2) :
      hilbertVectorL2_normalizedCoordCLM Q i (vfin Q hab hcd β L e N ω) = fseq N i :=
    vfin_coord Q hab hcd hQ β L e N ω i
  have hseq : ∀ i, Tendsto (fun N => fseq N i) atTop
      (𝓝 (hilbertVectorL2_normalizedCoordCLM Q i (vfix Q hab hcd β L e ω))) := by
    intro i
    have hmap := ((hilbertVectorL2_normalizedCoordCLM Q i).continuous.tendsto
      (vfix Q hab hcd β L e ω)).comp hω'
    simpa [Function.comp_def, hclass] using hmap
  have hlsc := tiled_lsc Q 134 fseq
    (fun i => hilbertVectorL2_normalizedCoordCLM Q i (vfix Q hab hcd β L e ω))
    (fun N i => (flatSourceQ3FiniteProductComponent Q β L e N ω i).toFun)
    (fun N i => (flatSourceQ3FiniteProductComponent Q β L e N ω i).grad)
    hseq
    (fun N i => MemLp.coeFn_toLp _)
    (fun N i j => (flatSourceQ3FiniteProductComponent Q β L e N ω i).grad_memL2_normalizedCubeMeasure j)
    (fun N i => (flatSourceQ3FiniteProductComponent Q β L e N ω i).hasWeakGradient)
  have hfin (N : ℕ) : phi' Q 134 (vfin Q hab hcd β L e N ω) =
      lemmaVTiledPositiveEnergy Q 134 (fun x i => fseq N i x) := by
    unfold phi'
    simp only [hclass]
  simp only [hfin]
  exact hlsc

/-- Expected tiled energy of the fixed physical q3 product. -/
theorem fixed_tiled_lintegral_le (Q : TriadicCube 2) (hab : a₀ < b₀) (hcd : c₀ < d₀)
    (hQ : openCubeSet Q ⊆ openRectangle a₀ b₀ c₀ d₀)
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (e : Vec 2) (he : Book.Ch02.vecNorm e = 1) (k : ℤ) :
    ∫⁻ ω, ENNReal.ofReal (phi' Q 134 (vfix Q hab hcd (q3ModelAmplitude M h k)
        (q3ModelLength k) e ω)) ∂standardGaussianInfinitePi ≤
      ENNReal.ofReal ((3 / 2 : ℝ) * (q3ModelAmplitude M h k) ^ 4 +
        (467 / 1000 : ℝ) ^ 2 * tileSide Q ^ 2 *
          ((936 / 5 : ℝ) * (q3ModelAmplitude M h k) ^ 4 / (q3ModelLength k).1 ^ 2)) :=
  lintegral_of_liminf standardGaussianInfinitePi _
    (fun N ω => phi' Q 134 (vfin Q hab hcd (q3ModelAmplitude M h k)
        (q3ModelLength k) e N ω)) _
    (fun N => Phi_measurable_of_V Q 134 _ (vfin_measurable Q hab hcd _ _ e N))
    (fixed_tiled_lsc Q hab hcd hQ e _ _)
    (fun N => finite_tiled_lintegral_le Q hab hcd hQ M h hM e he k N)

/-- `L^(128/127)` tiled energy of the fixed physical q3 product. -/
theorem fixed_tiled_L128 (Q : TriadicCube 2) (hab : a₀ < b₀) (hcd : c₀ < d₀)
    (hQ : openCubeSet Q ⊆ openRectangle a₀ b₀ c₀ d₀)
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (e : Vec 2) (he : Book.Ch02.vecNorm e = 1) (k : ℤ) :
    eLpNorm (fun ω => phi' Q 134 (vfix Q hab hcd (q3ModelAmplitude M h k)
        (q3ModelLength k) e ω)) (ENNReal.ofReal (128 / 127 : ℝ)) standardGaussianInfinitePi ≤
      ENNReal.ofReal ((513 / 500 : ℝ) * ((3 / 2 : ℝ) * (q3ModelAmplitude M h k) ^ 4 +
        (467 / 1000 : ℝ) ^ 2 * tileSide Q ^ 2 *
          ((936 / 5 : ℝ) * (q3ModelAmplitude M h k) ^ 4 / (q3ModelLength k).1 ^ 2))) :=
  L128_of_liminf standardGaussianInfinitePi _
    (fun N ω => phi' Q 134 (vfin Q hab hcd (q3ModelAmplitude M h k)
        (q3ModelLength k) e N ω)) _
    (Phi_measurable_of_V Q 134 _ (vfix_measurable Q hab hcd _ _ e))
    (fun N => Phi_measurable_of_V Q 134 _ (vfin_measurable Q hab hcd _ _ e N))
    (fun ω => phi_nonneg' Q 134 _) (fun N ω => phi_nonneg' Q 134 _)
    (fixed_tiled_lsc Q hab hcd hQ e _ _)
    (fun N => finite_tiled_energy_L128 Q hab hcd hQ M h hM e he k N _
      (Phi_measurable_of_V Q 134 _ (vfin_measurable Q hab hcd _ _ e N))
      (fun ω => phi_nonneg' Q 134 _)
      (fun ω => phi_vfin_le Q hab hcd hQ _ _ e N ω))

end Fixed

end

end ASDExplicitGamma.Scalar
