module

public import ASDExplicitGamma.Native.HeatInitialRefinedShear
public import ASDExplicitGamma.Native.HeatInitialRefinedGaussian
public import ASDExplicitGamma.Native.HeatInitialCrossRow
public import ASDExplicitGamma.Cold.NativeSharpLocalIndependence
public import ASDExplicitGamma.Cold.NativeLocalResponse
public import ASDExplicitGamma.Cold.NativeTraceMoments
public import ASDExplicitGamma.Gaussian.Rio

/-! The refined cross row: finite-colour type-two estimates with `chi = 81` colours. -/

@[expose] public section
noncomputable section

namespace ASDExplicitGamma.Native

open MeasureTheory ProbabilityTheory
open Homogenization Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Numerics.Native
open scoped BigOperators ENNReal

set_option linter.constructorNameAsVariable false

/-- Cauchy--Schwarz across the colour classes. -/
theorem nativeHeat_colour_sqrt_sum_le {κ : Type*} [Fintype κ] (V : κ → ℝ)
    (hV : ∀ c, 0 ≤ V c) :
    (∑ c, Real.sqrt (V c)) ≤ Real.sqrt (Fintype.card κ : ℝ) * Real.sqrt (∑ c, V c) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : κ => (1 : ℝ))
    (fun c => Real.sqrt (V c))
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at h
  simp_rw [Real.sq_sqrt (hV _)] at h
  have he : (Real.sqrt (Fintype.card κ : ℝ) * Real.sqrt (∑ c, V c)) ^ 2 =
      (Fintype.card κ : ℝ) * (∑ c, V c) := by
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _),
      Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => hV _))]
  apply (sq_le_sq₀ (Finset.sum_nonneg (fun _ _ => Real.sqrt_nonneg _))
    (by positivity)).mp
  rw [he]
  exact h

/-- Independent centered old coefficients, weighted by fixed-fresh coefficients, in
`κ` colours. -/
theorem nativeHeat_colour_independent_coefficients_average_typeTwo
    {Ω ι κ : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    [Fintype ι] [Nonempty ι] [Fintype κ] (color : ι → κ) (p : ℝ) (hp : 2 ≤ p)
    {Y : ι → Ω → ℝ} (a cap : ι → ℝ)
    (hYm : ∀ i, Measurable (Y i))
    (hY : ∀ i, MemLp (Y i) (ENNReal.ofReal p) μ)
    (hIndep : ∀ c, iIndepFun (fun i : {i // color i = c} => Y i.val) μ)
    (hCenter : ∀ i, (∫ ω, Y i ω ∂μ) = 0)
    (hcapNonneg : ∀ i, 0 ≤ cap i)
    (hcap : ∀ i, lpNorm (Y i) (ENNReal.ofReal p) μ ≤ cap i) :
    lpNorm (fun ω => (∑ i, a i * Y i ω) / (Fintype.card ι : ℝ))
        (ENNReal.ofReal p) μ ≤
      Real.sqrt (Fintype.card κ : ℝ) * Real.sqrt (p - 1) *
        Real.sqrt (∑ i, (|a i| * cap i) ^ 2) / (Fintype.card ι : ℝ) := by
  classical
  let X : ι → Ω → ℝ := fun i ω => a i * Y i ω
  let b : ι → ℝ := fun i => |a i| * cap i
  have hXm : ∀ i, Measurable (X i) := fun i => (measurable_const_mul (a i)).comp (hYm i)
  have hX : ∀ i, MemLp (X i) (ENNReal.ofReal p) μ := fun i => (hY i).const_mul (a i)
  have hXi : ∀ c, iIndepFun (fun i : {i // color i = c} => X i.val) μ := by
    intro c
    have h := (hIndep c).comp (fun i x => a i.val * x) (fun i => by fun_prop)
    simpa [X, Function.comp_def] using h
  have hXcenter : ∀ i, (∫ ω, X i ω ∂μ) = 0 := by
    intro i
    simp only [X]
    rw [integral_const_mul, hCenter i, mul_zero]
  have hb : ∀ i, 0 ≤ b i := fun i => mul_nonneg (abs_nonneg _) (hcapNonneg i)
  have hnorm (i : ι) :
      lpNorm (X i) (ENNReal.ofReal p) μ = |a i| * lpNorm (Y i) (ENNReal.ofReal p) μ := by
    change lpNorm (fun ω => a i * Y i ω) (ENNReal.ofReal p) μ = _
    rw [show (fun ω => a i * Y i ω) = (a i) • Y i from by
      funext ω
      simp [smul_eq_mul]]
    rw [lpNorm_const_smul]
    simp [Real.norm_eq_abs]
  have hcapX : ∀ i, lpNorm (X i) (ENNReal.ofReal p) μ ≤ b i := by
    intro i
    rw [hnorm i]
    exact mul_le_mul_of_nonneg_left (hcap i) (abs_nonneg _)
  let V := fun c : κ => ∑ i : {i // color i = c}, (b i.val) ^ 2
  let Z := fun c : κ => fun ω => ∑ i : {i // color i = c}, X i.val ω
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have hclass (c : κ) :
      lpNorm (Z c) (ENNReal.ofReal p) μ ≤ Real.sqrt (p - 1) * Real.sqrt (V c) := by
    have hsum := rio_independent_sum_sq_le μ hp
      (fun i : {i // color i = c} => X i.val) (fun i => hXm i.val)
      (hXi c) (fun i => hX i.val) (fun i => hXcenter i.val) Finset.univ
    have hcapSq :
        (∑ i : {i // color i = c}, (lpNorm (X i.val) (ENNReal.ofReal p) μ) ^ 2) ≤ V c := by
      dsimp [V]
      exact Finset.sum_le_sum (fun i _ =>
        (sq_le_sq₀ lpNorm_nonneg (hb i.val)).mpr (hcapX i.val))
    have hsum' : (lpNorm (Z c) (ENNReal.ofReal p) μ) ^ 2 ≤ (p - 1) * V c := by
      have h := hsum.trans (mul_le_mul_of_nonneg_left hcapSq (by linarith : 0 ≤ p - 1))
      simpa only [lpNorm, Z] using h
    have hroot : (Real.sqrt (p - 1) * Real.sqrt (V c)) ^ 2 = (p - 1) * V c := by
      rw [mul_pow, Real.sq_sqrt (by linarith : 0 ≤ p - 1), Real.sq_sqrt
        (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
    apply (sq_le_sq₀ lpNorm_nonneg (by positivity)).mp
    rw [hroot]
    exact hsum'
  have hclassMem (c : κ) : MemLp (Z c) (ENNReal.ofReal p) μ :=
    memLp_finsetSum Finset.univ (fun i _ => hX i.val)
  have hsumColor := (lpNorm_sum_le (s := Finset.univ)
      (fun c _ => hclassMem c) hp1).trans
    (Finset.sum_le_sum (fun c _ => hclass c))
  have hfiber : (∑ c : κ, Z c) = ∑ i, X i := by
    funext ω
    simp only [Z, Finset.sum_apply]
    exact Fintype.sum_fiberwise color (fun i => X i ω)
  rw [hfiber] at hsumColor
  have hVnonneg : ∀ c, 0 ≤ V c := by
    intro c
    dsimp [V]
    exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hVsum : (∑ c : κ, V c) = ∑ i, (b i) ^ 2 := by
    dsimp [V]
    exact Fintype.sum_fiberwise color (fun i => (b i) ^ 2)
  have hpopulation := mul_le_mul_of_nonneg_left
    (nativeHeat_colour_sqrt_sum_le V hVnonneg) (Real.sqrt_nonneg (p - 1))
  rw [hVsum] at hpopulation
  have hpopulationSum :
      (∑ c : κ, Real.sqrt (p - 1) * Real.sqrt (V c)) ≤
        Real.sqrt (Fintype.card κ : ℝ) * Real.sqrt (p - 1) *
          Real.sqrt (∑ i, (b i) ^ 2) := by
    have he : (∑ c : κ, Real.sqrt (p - 1) * Real.sqrt (V c)) =
        Real.sqrt (p - 1) * ∑ c : κ, Real.sqrt (V c) := by
      rw [Finset.mul_sum]
    rw [he]
    nlinarith only [hpopulation]
  have hsumFinal := hsumColor.trans hpopulationSum
  have hcardpos : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  have hcardne : Fintype.card ι ≠ 0 := Fintype.card_ne_zero
  rw [lpNorm_fun_div_natCast hcardne]
  have hpoint : (fun ω => ∑ i, X i ω) = ∑ i, X i := by
    funext ω
    simp only [Finset.sum_apply]
  rw [hpoint]
  exact div_le_div_of_nonneg_right hsumFinal hcardpos.le

/-- Integrate the fixed-fresh colour estimate over a product old/fresh
law. The right side is precisely the fresh moment of the weighted square sum. -/
theorem nativeHeat_colour_product_independent_average_moment
    {Ω Η ι κ : Type*} [Fintype κ] [MeasurableSpace Ω] [MeasurableSpace Η]
    {μ : Measure Ω} {ν : Measure Η} [IsProbabilityMeasure μ] [SFinite ν]
    [Fintype ι] [Nonempty ι] (color : ι → κ) (p : ℝ) (hp : 2 ≤ p)
    {Y : ι → Ω → ℝ} (G : ι → Η → ℝ) (cap : ι → ℝ)
    (hYm : ∀ i, Measurable (Y i))
    (hY : ∀ i, MemLp (Y i) (ENNReal.ofReal p) μ)
    (hIndep : ∀ c, iIndepFun (fun i : {i // color i = c} => Y i.val) μ)
    (hCenter : ∀ i, (∫ ω, Y i ω ∂μ) = 0)
    (hcapNonneg : ∀ i, 0 ≤ cap i)
    (hcap : ∀ i, lpNorm (Y i) (ENNReal.ofReal p) μ ≤ cap i)
    (hG : ∀ i, Measurable (G i)) :
    ∫⁻ z : Ω × Η,
        ‖(∑ i, G i z.2 * Y i z.1) / (Fintype.card ι : ℝ)‖ₑ ^ p ∂μ.prod ν ≤
      ∫⁻ η, (ENNReal.ofReal
        (Real.sqrt (Fintype.card κ : ℝ) * Real.sqrt (p - 1) *
          Real.sqrt (∑ i, (|G i η| * cap i) ^ 2) / (Fintype.card ι : ℝ))) ^ p ∂ν := by
  classical
  let N : ℝ := Fintype.card ι
  let F : Ω × Η → ℝ := fun z => (∑ i, G i z.2 * Y i z.1) / N
  let B : Η → ℝ := fun η =>
    Real.sqrt (Fintype.card κ : ℝ) * Real.sqrt (p - 1) * Real.sqrt (∑ i, (|G i η| * cap i) ^ 2) / N
  let q : Η → ℝ≥0∞ := fun η => ENNReal.ofReal (B η) ^ p
  have hF : Measurable F := by
    fun_prop
  have hB : Measurable B := by
    fun_prop
  have hq : Measurable q := by
    fun_prop
  have hp0 : 0 < p := by linarith
  have hpENN0 : ENNReal.ofReal p ≠ 0 := by
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (by linarith))
  have hpENNtop : ENNReal.ofReal p ≠ ∞ := ENNReal.ofReal_ne_top
  have hfiber (η : Η) :
      ∫⁻ ω, ‖F (ω, η)‖ₑ ^ p ∂μ ≤ q η := by
    let f : Ω → ℝ := fun ω => F (ω, η)
    have hnorm := nativeHeat_colour_independent_coefficients_average_typeTwo
      color p hp (Y := Y) (fun i => G i η) cap hYm hY hIndep hCenter
      hcapNonneg hcap
    have hbound : lpNorm f (ENNReal.ofReal p) μ ≤ B η := by
      simpa [f, F, B, N] using hnorm
    have hsum : MemLp (fun ω => ∑ i, G i η * Y i ω)
        (ENNReal.ofReal p) μ :=
      memLp_finsetSum Finset.univ (fun i _ => (hY i).const_mul (G i η))
    have hmem : MemLp f (ENNReal.ofReal p) μ := by
      simpa [f, F, N, div_eq_mul_inv, mul_comm] using hsum.const_mul (N⁻¹)
    have he : eLpNorm f (ENNReal.ofReal p) μ = eLpNorm' f p μ := by
      rw [eLpNorm_eq_eLpNorm' hpENN0 hpENNtop hmem.aestronglyMeasurable]
      rw [ENNReal.toReal_ofReal (by linarith)]
    have hnorm' : eLpNorm' f p μ ≤ ENNReal.ofReal (B η) := by
      rw [← he]
      rw [← ofReal_lpNorm hmem]
      exact ENNReal.ofReal_le_ofReal hbound
    calc
      ∫⁻ ω, ‖f ω‖ₑ ^ p ∂μ = eLpNorm' f p μ ^ p :=
        lintegral_rpow_enorm_eq_rpow_eLpNorm' hp0
      _ ≤ ENNReal.ofReal (B η) ^ p :=
        ENNReal.rpow_le_rpow hnorm' (le_of_lt hp0)
      _ = q η := rfl
  have hfiber' : ∀ η, ∫⁻ ω, ‖F (ω, η)‖ₑ ^ p ∂μ ≤ (1 : ℝ≥0∞) * q η := by
    intro η
    simpa using hfiber η
  have hprod := nativeHeat_product_moment_of_fiber_bounds
    (μ := μ) (ν := ν) F hF p 1 q hq hfiber'
  simpa [F, B, q, N, one_mul] using hprod


/-- On the actual cutoff carrier, a locally measurable old vector and a
measurable disjoint fresh-shell vector can be separated into their product
law. This composes the fixed-fresh colour estimate with the genuine
old/fresh cutoff independence and transfers all old-family hypotheses to the
old vector's pushforward law. -/
theorem nativeHeat_cutoff_oldFresh_average_moment_of_observables
    {ι Η κ : Type*} [Fintype κ] [MeasurableSpace Η] [Fintype ι] [Nonempty ι]
    (M : ABKModel 2) (mOld : ℤ) (J : Set ℤ)
    (hJ : Disjoint (Set.Iic mOld) J) (color : ι → κ)
    (p : ℝ) (hp : 2 ≤ p) (Y : ι → Cutoff.CutoffSample 2 → ℝ)
    (hYlocal : ∀ i, @Measurable (Cutoff.CutoffSample 2) ℝ
      (Cutoff.cutoffSampleLocalSigma M mOld Set.univ) (borel ℝ) (Y i))
    (hYmeas : ∀ i, Measurable (Y i))
    (hYmem : ∀ i, MemLp (Y i) (ENNReal.ofReal p)
      (Cutoff.cutoffSampleLaw M).toMeasure)
    (hIndep : ∀ c, iIndepFun (fun i : {i // color i = c} => Y i.val)
      (Cutoff.cutoffSampleLaw M).toMeasure)
    (hCenter : ∀ i, (∫ ω, Y i ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) = 0)
    (cap : ι → ℝ) (hcapNonneg : ∀ i, 0 ≤ cap i)
    (hcap : ∀ i, lpNorm (Y i) (ENNReal.ofReal p)
      (Cutoff.cutoffSampleLaw M).toMeasure ≤ cap i)
    {Fresh : Cutoff.CutoffSample 2 → Η}
    (hFreshLocal : @Measurable (Cutoff.CutoffSample 2) Η
      ((Cutoff.shellIndexSigma J).comap Subtype.val) _ Fresh)
    (hFreshMeas : Measurable Fresh) (coeff : ι → Η → ℝ)
    (hcoeff : ∀ i, Measurable (coeff i)) :
    ∫⁻ ω, ‖(∑ i, coeff i (Fresh ω) * Y i ω) /
        (Fintype.card ι : ℝ)‖ₑ ^ p ∂(Cutoff.cutoffSampleLaw M).toMeasure ≤
      ∫⁻ η, (ENNReal.ofReal (Real.sqrt (Fintype.card κ : ℝ) * Real.sqrt (p - 1) *
        Real.sqrt (∑ i, (|coeff i η| * cap i) ^ 2) /
          (Fintype.card ι : ℝ))) ^ p
        ∂((Cutoff.cutoffSampleLaw M).toMeasure.map Fresh) := by
  classical
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let X : Cutoff.CutoffSample 2 → ι → ℝ := fun ω i => Y i ω
  let μOld := μ.map X
  let ν := μ.map Fresh
  have hμOldProb : IsProbabilityMeasure μOld := by
    dsimp [μOld]
    infer_instance
  let YOld : ι → (ι → ℝ) → ℝ := fun i x => x i
  let F : (ι → ℝ) × Η → ℝ := fun z =>
    (∑ i, coeff i z.2 * z.1 i) / (Fintype.card ι : ℝ)
  have hYglobal : ∀ i, Measurable (Y i) := hYmeas
  have hXlocal : @Measurable (Cutoff.CutoffSample 2) (ι → ℝ)
      (Cutoff.cutoffSampleLocalSigma M mOld Set.univ) inferInstance X := by
    exact (@measurable_pi_iff (Cutoff.CutoffSample 2) ι (fun _ => ℝ)
      (Cutoff.cutoffSampleLocalSigma M mOld Set.univ) (fun _ => inferInstance)).mpr
        (fun i => hYlocal i)
  have hXglobal : Measurable X := by
    exact measurable_pi_iff.mpr (fun i => hYglobal i)
  have hYOldmeas (i : ι) : Measurable (YOld i) := by
    exact measurable_pi_apply i
  have hYOldmem (i : ι) : MemLp (YOld i) (ENNReal.ofReal p) μOld := by
    rw [memLp_map_measure_iff (hYOldmeas i).aestronglyMeasurable hXglobal.aemeasurable]
    simpa [YOld, X, Function.comp_def] using hYmem i
  have hYOldnorm (i : ι) : lpNorm (YOld i) (ENNReal.ofReal p) μOld =
      lpNorm (Y i) (ENNReal.ofReal p) μ := by
    calc
      lpNorm (YOld i) (ENNReal.ofReal p) μOld =
          (eLpNorm (YOld i) (ENNReal.ofReal p) μOld).toReal := rfl
      _ = (eLpNorm (YOld i ∘ X) (ENNReal.ofReal p) μ).toReal := by
        rw [eLpNorm_map_measure (hYOldmeas i).aestronglyMeasurable
          hXglobal.aemeasurable]
      _ = lpNorm (Y i) (ENNReal.ofReal p) μ := by
        simpa [YOld, X, Function.comp_def] using
          (toReal_eLpNorm (f := Y i) (p := ENNReal.ofReal p) (μ := μ))
  have hYOldcap (i : ι) : lpNorm (YOld i) (ENNReal.ofReal p) μOld ≤ cap i := by
    rw [hYOldnorm i]
    exact hcap i
  have hYOldcenter (i : ι) : ∫ x, YOld i x ∂μOld = 0 := by
    rw [integral_map hXglobal.aemeasurable (hYOldmeas i).aestronglyMeasurable]
    simpa [YOld, X] using hCenter i
  have hYOldIndep (c : κ) : iIndepFun
      (fun i : {i // color i = c} => YOld i.val) μOld := by
    let π : (ι → ℝ) → ({i // color i = c} → ℝ) := fun x i => x i.val
    have hπ : Measurable π := by fun_prop
    have hmap : μOld.map π = Measure.pi (fun i => μOld.map (YOld i.val)) := by
      calc
        μOld.map π = μ.map (π ∘ X) := Measure.map_map hπ hXglobal
        _ = μ.map (fun ω i => Y i.val ω) := rfl
        _ = Measure.pi (fun i => μ.map (Y i.val)) :=
          (hIndep c).map_fun_eq_pi_map (fun i => (hYmeas i.val).aemeasurable)
        _ = Measure.pi (fun i => μOld.map (YOld i.val)) := by
          congr 1
          funext (i : {i // color i = c})
          symm
          exact Measure.map_map (hYOldmeas i.val) hXglobal
    exact (iIndepFun_iff_map_fun_eq_pi_map
      (fun (i : {i // color i = c}) => (hYOldmeas i.val).aemeasurable)).2 (by
        simpa [π, YOld] using hmap)
  have hPair := nativeHeat_cutoffLocal_freshBlock_independent
    M mOld J hJ X hXlocal Fresh hFreshLocal
  have hF : Measurable F := by fun_prop
  have hProd := @nativeHeat_colour_product_independent_average_moment
    (ι → ℝ) Η ι κ inferInstance inferInstance inferInstance μOld ν hμOldProb
    inferInstance inferInstance inferInstance color p hp YOld coeff cap
    (fun i => hYOldmeas i) (fun i => hYOldmem i) hYOldIndep hYOldcenter
    hcapNonneg hYOldcap hcoeff
  have hPairMoment := nativeHeat_independent_pair_moment_eq_product
    X Fresh hXglobal hFreshMeas hPair F hF p
  calc
    _ = ∫⁻ ω, ‖F (X ω, Fresh ω)‖ₑ ^ p ∂μ := by
      congr 1
    _ = ∫⁻ z, ‖F z‖ₑ ^ p ∂μOld.prod ν := hPairMoment
    _ ≤ ∫⁻ η, (ENNReal.ofReal
        (Real.sqrt (Fintype.card κ : ℝ) * Real.sqrt (p - 1) *
          Real.sqrt (∑ i, (|coeff i η| * cap i) ^ 2) /
            (Fintype.card ι : ℝ))) ^ p ∂ν := hProd


/-- Apply the old/fresh product estimate to the actual cutoff child-shear
array. Measurability and centering are derived from the full response
and scalar block-mean interfaces; only the moment caps and the stated
colour independence remain as hypotheses. -/
theorem nativeHeat_oldShear_fresh_average_moment_of_caps
    {ι Η κ : Type*} [Fintype κ] [MeasurableSpace Η] [Fintype ι] [Nonempty ι]
    (M : ABKModel 2) (mOld : ℤ) (J : Set ℤ)
    (hJ : Disjoint (Set.Iic mOld) J) (C : ι → TriadicCube 2)
    (color : ι → κ) (p : ℝ) (hp : 2 ≤ p)
    (htrace : ∀ i, MemLp (Cold.coldNativeCellTrace M mOld (C i)) 2
      (Cutoff.cutoffSampleLaw M).toMeasure)
    (hYmem : ∀ i, MemLp (fun ω : Cutoff.CutoffSample 2 =>
      Variational.shearTraceLinear (coarseBlockMatrix (cubeSet (C i))
        (Cutoff.coefficientCutoff M.nu mOld ω).toFun)) (ENNReal.ofReal p)
          (Cutoff.cutoffSampleLaw M).toMeasure)
    (hIndep : ∀ c, iIndepFun
      (fun i : {i // color i = c} => fun ω : Cutoff.CutoffSample 2 =>
        Variational.shearTraceLinear (coarseBlockMatrix (cubeSet (C i.val))
          (Cutoff.coefficientCutoff M.nu mOld ω).toFun))
      (Cutoff.cutoffSampleLaw M).toMeasure)
    (cap : ι → ℝ) (hcapNonneg : ∀ i, 0 ≤ cap i)
    (hcap : ∀ i, lpNorm (fun ω : Cutoff.CutoffSample 2 =>
      Variational.shearTraceLinear (coarseBlockMatrix (cubeSet (C i))
        (Cutoff.coefficientCutoff M.nu mOld ω).toFun)) (ENNReal.ofReal p)
          (Cutoff.cutoffSampleLaw M).toMeasure ≤ cap i)
    {Fresh : Cutoff.CutoffSample 2 → Η}
    (hFreshLocal : @Measurable (Cutoff.CutoffSample 2) Η
      ((Cutoff.shellIndexSigma J).comap Subtype.val) _ Fresh)
    (hFreshMeas : Measurable Fresh) (coeff : ι → Η → ℝ)
    (hcoeff : ∀ i, Measurable (coeff i)) :
    ∫⁻ ω, ‖(∑ i, coeff i (Fresh ω) *
        Variational.shearTraceLinear (coarseBlockMatrix (cubeSet (C i))
          (Cutoff.coefficientCutoff M.nu mOld ω).toFun)) /
          (Fintype.card ι : ℝ)‖ₑ ^ p ∂(Cutoff.cutoffSampleLaw M).toMeasure ≤
      ∫⁻ η, (ENNReal.ofReal (Real.sqrt (Fintype.card κ : ℝ) * Real.sqrt (p - 1) *
        Real.sqrt (∑ i, (|coeff i η| * cap i) ^ 2) /
          (Fintype.card ι : ℝ))) ^ p
        ∂((Cutoff.cutoffSampleLaw M).toMeasure.map Fresh) := by
  classical
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let Y : ι → Cutoff.CutoffSample 2 → ℝ := fun i ω =>
    Variational.shearTraceLinear (coarseBlockMatrix (cubeSet (C i))
      (Cutoff.coefficientCutoff M.nu mOld ω).toFun)
  let shear : FullBlockMat 2 → ℝ := fun A =>
    A (Sum.inl 1) (Sum.inr 0) - A (Sum.inl 0) (Sum.inr 1)
  have hshear : Measurable shear := by
    fun_prop
  have hYlocal (i : ι) : @Measurable (Cutoff.CutoffSample 2) ℝ
      (Cutoff.cutoffSampleLocalSigma M mOld Set.univ) (borel ℝ) (Y i) := by
    have hresp := (Cold.coldNativeResponse_local M mOld (C i)).mono
      (Algsuperdiff.Section3.Provider.BadEvents.cutoffSampleLocalSigma_mono
        M le_rfl (Set.subset_univ (cubeSet (C i)))) le_rfl
    have hEq (ω : Cutoff.CutoffSample 2) : Y i ω =
        shear (Cold.coldNativeResponse M mOld (C i) ω) := by
      simp [Y, shear, Cold.coldNativeResponse, Variational.shearTraceLinear,
        Variational.frameMatrix, Homogenization.toFullBlockMat]
    rw [show Y i = fun ω => shear (Cold.coldNativeResponse M mOld (C i) ω) from
      funext hEq]
    exact hshear.comp hresp
  have hYmeas (i : ι) : Measurable (Y i) := by
    have hresp := Cold.coldNativeResponse_measurable M mOld (C i)
    have hEq (ω : Cutoff.CutoffSample 2) : Y i ω =
        shear (Cold.coldNativeResponse M mOld (C i) ω) := by
      simp [Y, shear, Cold.coldNativeResponse, Variational.shearTraceLinear,
        Variational.frameMatrix, Homogenization.toFullBlockMat]
    rw [show Y i = fun ω => shear (Cold.coldNativeResponse M mOld (C i) ω) from
      funext hEq]
    exact hshear.comp hresp
  have hCenter (i : ι) : (∫ ω, Y i ω ∂μ) = 0 := by
    simpa [Y, μ] using nativeHeat_oldShear_centered M mOld (C i) (htrace i)
  simpa [Y, μ] using nativeHeat_cutoff_oldFresh_average_moment_of_observables
    M mOld J hJ color p hp Y hYlocal hYmeas
    hYmem hIndep hCenter cap hcapNonneg hcap
    hFreshLocal hFreshMeas coeff hcoeff


/-- The `9 × 9` residue colouring of the integer cell coordinates. -/
def nativeHeatRefinedColor81 (Q : TriadicCube 2) : Fin 9 × Fin 9 :=
  (⟨(Q.index 0 % 9).toNat, by
      have h0 := Int.emod_nonneg (Q.index 0) (by norm_num : (9 : ℤ) ≠ 0)
      have h1 := Int.emod_lt_of_pos (Q.index 0) (by norm_num : (0 : ℤ) < 9)
      omega⟩,
    ⟨(Q.index 1 % 9).toNat, by
      have h0 := Int.emod_nonneg (Q.index 1) (by norm_num : (9 : ℤ) ≠ 0)
      have h1 := Int.emod_lt_of_pos (Q.index 1) (by norm_num : (0 : ℤ) < 9)
      omega⟩)

theorem nativeHeatRefinedColor81_parity {Q R : TriadicCube 2}
    (h : nativeHeatRefinedColor81 Q = nativeHeatRefinedColor81 R) (i : Fin 2) :
    Q.index i % 9 = R.index i % 9 := by
  have h0 := congrArg (fun z : Fin 9 × Fin 9 => z.1.val) h
  have h1 := congrArg (fun z : Fin 9 × Fin 9 => z.2.val) h
  simp only [nativeHeatRefinedColor81] at h0 h1
  have hQ0 := Int.emod_nonneg (Q.index 0) (by norm_num : (9 : ℤ) ≠ 0)
  have hQ1 := Int.emod_nonneg (Q.index 1) (by norm_num : (9 : ℤ) ≠ 0)
  have hR0 := Int.emod_nonneg (R.index 0) (by norm_num : (9 : ℤ) ≠ 0)
  have hR1 := Int.emod_nonneg (R.index 1) (by norm_num : (9 : ℤ) ≠ 0)
  fin_cases i
  · change Q.index 0 % 9 = R.index 0 % 9
    omega
  · change Q.index 1 % 9 = R.index 1 % 9
    omega

/-- Distinct equal-colour cells of one scale are nine cell sides apart in some coordinate,
so at least `3^(scale+1)` apart. -/
theorem nativeHeatRefined_color_separation {Q R : TriadicCube 2}
    (hscale : Q.scale = R.scale) (hneq : Q ≠ R)
    (hcolor : nativeHeatRefinedColor81 Q = nativeHeatRefinedColor81 R)
    {x y : Vec 2} (hx : x ∈ cubeSet Q) (hy : y ∈ cubeSet R) :
    ∃ k : Fin 2, (3 : ℝ) ^ (Q.scale + 1) ≤ |(x - y) k| := by
  have hidx : ∃ k : Fin 2, Q.index k ≠ R.index k := by
    by_contra hn
    push Not at hn
    have he : Q.index = R.index := funext hn
    apply hneq
    cases Q
    cases R
    simp_all
  obtain ⟨i, hi⟩ := hidx
  have hp := nativeHeatRefinedColor81_parity hcolor i
  have hd : Q.index i + 9 ≤ R.index i ∨ R.index i + 9 ≤ Q.index i := by omega
  have hs : (0 : ℝ) < (3 : ℝ) ^ Q.scale := zpow_pos (by norm_num) _
  have hs3 : (3 : ℝ) ^ (Q.scale + 1) = 3 * (3 : ℝ) ^ Q.scale := by
    rw [zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    ring
  have hxlo := (hx i).1
  have hxhi := (hx i).2.le
  have hylo := (hy i).1
  have hyhi := (hy i).2.le
  simp only [cubeScaleFactor, ← hscale] at hxlo hxhi hylo hyhi
  refine ⟨i, ?_⟩
  rw [hs3]
  rcases hd with hd | hd
  · have hreal : (Q.index i : ℝ) + 9 ≤ (R.index i : ℝ) := by exact_mod_cast hd
    have hm := mul_le_mul_of_nonneg_right hreal hs.le
    have hgap : 3 * (3 : ℝ) ^ Q.scale ≤ y i - x i := by nlinarith only [hm, hxhi, hylo, hs]
    exact hgap.trans (by simpa only [Pi.sub_apply, neg_sub] using neg_le_abs (x i - y i))
  · have hreal : (R.index i : ℝ) + 9 ≤ (Q.index i : ℝ) := by exact_mod_cast hd
    have hm := mul_le_mul_of_nonneg_right hreal hs.le
    have hgap : 3 * (3 : ℝ) ^ Q.scale ≤ x i - y i := by nlinarith only [hm, hyhi, hxlo, hs]
    exact hgap.trans (le_abs_self _)

/-- The refined child shears of one `9 × 9` colour are independent at the completed
cutoff `m+1`. -/
theorem nativeHeatRefined_shear_colour_independent
    {ι : Type*} (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (m : ℤ)
    (C : ι → TriadicCube 2) (hC : Function.Injective C)
    (hscale : ∀ i, (C i).scale = m) :
    ∀ c : Fin 9 × Fin 9, iIndepFun
      (fun i : {i // nativeHeatRefinedColor81 (C i) = c} => fun ω : Cutoff.CutoffSample 2 =>
        Variational.shearTraceLinear (coarseBlockMatrix (cubeSet (C i.val))
          (Cutoff.coefficientCutoff M.nu (m + 1) ω).toFun))
      (Cutoff.cutoffSampleLaw M).toMeasure := by
  classical
  intro c
  let shear : FullBlockMat 2 → ℝ := fun A =>
    A (Sum.inl 1) (Sum.inr 0) - A (Sum.inl 0) (Sum.inr 1)
  have hshear : Measurable shear := by fun_prop
  have hEq (i : {i // nativeHeatRefinedColor81 (C i) = c}) :
      (fun ω : Cutoff.CutoffSample 2 => shear (Cold.coldNativeResponse M (m + 1) (C i.val) ω)) =
      (fun ω => Variational.shearTraceLinear (coarseBlockMatrix (cubeSet (C i.val))
        (Cutoff.coefficientCutoff M.nu (m + 1) ω).toFun)) := by
    funext ω
    simp [shear, Cold.coldNativeResponse, Variational.shearTraceLinear,
      Variational.frameMatrix, Homogenization.toFullBlockMat]
  have hind : iIndepFun (fun i : {i // nativeHeatRefinedColor81 (C i) = c} =>
      fun ω : Cutoff.CutoffSample 2 => shear (Cold.coldNativeResponse M (m + 1) (C i.val) ω))
      (Cutoff.cutoffSampleLaw M).toMeasure := by
    apply Cold.cold_iIndepFun_cutoffLocal M h hM (m + 1)
      (fun i : {i // nativeHeatRefinedColor81 (C i) = c} => cubeSet (C i.val))
      (fun i => measurableSet_cubeSet (C i.val))
    · intro i j hij x hx y hy
      have hval : i.val ≠ j.val := fun he => hij (Subtype.ext he)
      have hneq : C i.val ≠ C j.val := fun he => hval (hC he)
      have hsc : (C i.val).scale = (C j.val).scale := (hscale _).trans (hscale _).symm
      obtain ⟨k, hk⟩ := nativeHeatRefined_color_separation hsc hneq
        (i.property.trans j.property.symm) hx hy
      refine ⟨k, ?_⟩
      rw [hscale] at hk
      exact hk
    · intro i
      exact hshear.comp (Cold.coldNativeResponse_local M (m + 1) (C i.val))
  have hEqAE : ∀ i : {i // nativeHeatRefinedColor81 (C i) = c},
      (fun ω : Cutoff.CutoffSample 2 => shear (Cold.coldNativeResponse M (m + 1) (C i.val) ω)) =ᵐ[
        (Cutoff.cutoffSampleLaw M).toMeasure]
      (fun ω => Variational.shearTraceLinear (coarseBlockMatrix (cubeSet (C i.val))
        (Cutoff.coefficientCutoff M.nu (m + 1) ω).toFun)) := fun i =>
    Filter.Eventually.of_forall (fun ω => congrFun (hEq i) ω)
  exact (ProbabilityTheory.iIndepFun_congr hEqAE).mp hind

/-- The state-driven child-shear cross-scale estimate supplies both the
finite p-moment and the real Lp cap used by the old/fresh type-two adapter. -/
theorem nativeHeatRefined_childShear_lpCap
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hgamma : M.gamma ≤ gammaZero) (Q : TriadicCube 2) (m : ℤ)
    (hscale : Q.scale = m)
    (hpast : ∀ n < m + 1, nativeInductionState M h n)
    (k : ℕ) (hk2 : 2 ≤ k) (hk20 : k ≤ 20) :
    MemLp (fun ω : Cutoff.CutoffSample 2 =>
      Variational.shearTraceLinear (coarseBlockMatrix (cubeSet Q)
        (Cutoff.coefficientCutoff M.nu (m + 1) ω).toFun)) (ENNReal.ofReal (k : ℝ))
        (Cutoff.cutoffSampleLaw M).toMeasure ∧
      lpNorm (fun ω : Cutoff.CutoffSample 2 =>
        Variational.shearTraceLinear (coarseBlockMatrix (cubeSet Q)
          (Cutoff.coefficientCutoff M.nu (m + 1) ω).toFun)) (ENNReal.ofReal (k : ℝ))
          (Cutoff.cutoffSampleLaw M).toMeasure ≤
        Real.sqrt (2 * ((nativeHeatB : ℝ) *
          nativeHeatHnReal nativeHeatParametersData ((k : ℚ) / 2) +
          ((nativeHeatEps * nativeHeatParametersData.hp : ℚ) : ℝ))) := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let z : Cutoff.CutoffSample 2 → ℝ := fun ω =>
    Variational.shearTraceLinear (coarseBlockMatrix (cubeSet Q)
      (Cutoff.coefficientCutoff M.nu (m + 1) ω).toFun)
  let B : ℝ := 2 * ((nativeHeatB : ℝ) *
    nativeHeatHnReal nativeHeatParametersData ((k : ℚ) / 2) +
    ((nativeHeatEps * nativeHeatParametersData.hp : ℚ) : ℝ))
  have hkpos : 0 < (k : ℝ) := by
    have hk : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk2
    linarith
  have hp0 : ENNReal.ofReal (k : ℝ) ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr hkpos)
  have hptop : ENNReal.ofReal (k : ℝ) ≠ ∞ := ENNReal.ofReal_ne_top
  have hzmeas : Measurable z := by
    let shear : FullBlockMat 2 → ℝ := fun A =>
      A (Sum.inl 1) (Sum.inr 0) - A (Sum.inl 0) (Sum.inr 1)
    have hs : Measurable shear := by fun_prop
    have hEq (ω : Cutoff.CutoffSample 2) : z ω =
        shear (Cold.coldNativeResponse M (m + 1) Q ω) := by
      simp [z, shear, Cold.coldNativeResponse, Variational.shearTraceLinear,
        Variational.frameMatrix, Homogenization.toFullBlockMat]
    rw [show z = fun ω => shear (Cold.coldNativeResponse M (m + 1) Q ω) from funext hEq]
    exact hs.comp (Cold.coldNativeResponse_measurable M (m + 1) Q)
  have hcross := nativeHeatRefined_childShear_eLpNorm
    M h hM hgamma m hpast Q hscale k hk2 hk20
  have hcrossZ : eLpNorm' z (k : ℝ) μ ^ 2 ≤ ENNReal.ofReal B := by
    simpa [z, μ, B] using hcross
  have hprime : eLpNorm' z (k : ℝ) μ < ∞ := by
    apply lt_top_iff_ne_top.mpr
    intro htop
    have htopSq : eLpNorm' z (k : ℝ) μ ^ 2 = ∞ := by simp [htop]
    rw [htopSq] at hcrossZ
    exact (not_le_of_gt ENNReal.ofReal_lt_top) hcrossZ
  have hmem : MemLp z (ENNReal.ofReal (k : ℝ)) μ := by
    rw [memLp_iff]
    rw [eLpNorm_eq_eLpNorm' hp0 hptop hzmeas.aestronglyMeasurable]
    simpa [ENNReal.toReal_ofReal hkpos.le] using hprime
  have hnormEq : ENNReal.ofReal (lpNorm z (ENNReal.ofReal (k : ℝ)) μ) =
      eLpNorm' z (k : ℝ) μ := by
    calc
      _ = eLpNorm z (ENNReal.ofReal (k : ℝ)) μ := ofReal_lpNorm hmem
      _ = eLpNorm' z (k : ℝ) μ := by
        rw [eLpNorm_eq_eLpNorm' hp0 hptop hzmeas.aestronglyMeasurable,
          ENNReal.toReal_ofReal hkpos.le]
  have hB0 : 0 ≤ B := by
    dsimp [B]
    have hBq : (0 : ℚ) ≤ nativeHeatB := by decide +kernel
    have hEq : (0 : ℚ) ≤ nativeHeatEps := by decide +kernel
    have hhpq : (0 : ℚ) ≤ nativeHeatParametersData.hp := by
      norm_num [nativeHeatParametersData]
    have hqstar : (0 : ℚ) ≤ nativeQstar := by norm_num [nativeQstar]
    have hH : 0 ≤ nativeHeatHnReal nativeHeatParametersData ((k : ℚ) / 2) := by
      rw [nativeHeatHnReal]
      apply mul_nonneg (by exact_mod_cast hqstar)
      apply Real.rpow_nonneg
      exact_mod_cast (div_nonneg hhpq hqstar)
    exact mul_nonneg (by norm_num)
      (add_nonneg (mul_nonneg (by exact_mod_cast hBq) hH)
        (by exact_mod_cast mul_nonneg hEq hhpq))
  have hsqENN : ENNReal.ofReal (lpNorm z (ENNReal.ofReal (k : ℝ)) μ) ^ 2 ≤
      ENNReal.ofReal B := by
    rw [hnormEq]
    exact hcrossZ
  have hsq : (lpNorm z (ENNReal.ofReal (k : ℝ)) μ) ^ 2 ≤ B :=
    (ENNReal.ofReal_le_ofReal_iff hB0).mp (by simpa [ENNReal.ofReal_pow] using hsqENN)
  refine ⟨hmem, ?_⟩
  exact Real.le_sqrt_of_sq_le (by simpa [z, μ, B] using hsq)


/-- The refined child trace is square integrable. -/
theorem nativeHeatRefined_childTrace_memLp_two
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (hg : M.gamma ≤ gammaZero)
    (m : ℤ) (hpast : ∀ n < m + 1, nativeInductionState M h n)
    (Q : TriadicCube 2) (hscale : Q.scale = m) :
    MemLp (Cold.coldNativeCellTrace M (m + 1) Q) 2
      (Cutoff.cutoffSampleLaw M).toMeasure := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  letI : IsProbabilityMeasure μ := (Cutoff.cutoffSampleLaw M).property
  let f := Cold.coldNativeCellTrace M (m + 1) Q
  have hcap := nativeHeatRefined_coldTrace_L20 M h hM hg m hpast Q hscale
  have hf : AEStronglyMeasurable f μ :=
    (Cold.coldNativeCellTrace_measurable M (m + 1) Q).aestronglyMeasurable
  have h20Eq : eLpNorm f (20 : ℝ≥0∞) μ = eLpNorm' f 20 μ := by
    simpa using (eLpNorm_eq_eLpNorm' (p := (20 : ℝ≥0∞)) (by norm_num) (by norm_num) hf)
  have h20 : MemLp f (20 : ℝ≥0∞) μ := by
    rw [memLp_iff, h20Eq]
    exact lt_of_le_of_lt hcap ENNReal.ofReal_lt_top
  exact h20.mono_exponent (by norm_num : (2 : ℝ≥0∞) ≤ 20)

/-- On a probability space, an integer moment bound for a nonnegative
observable controls the lower fractional moments of its square root. -/
theorem nativeHeat_lintegral_sqrt_rpow_le_of_moment
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (F : Ω → ℝ) (q k : ℕ) (hq : 1 ≤ q) (hk2 : 2 ≤ k)
    (hk2q : k ≤ 2 * q) (hF0 : ∀ ω, 0 ≤ F ω)
    (hFmem : MemLp F (ENNReal.ofReal (q : ℝ)) μ)
    (V : ℝ) (hMoment : ∫ ω, F ω ^ q ∂μ ≤ V) :
    ∫⁻ ω, (ENNReal.ofReal (Real.sqrt (F ω))) ^ (k : ℝ) ∂μ ≤
      (ENNReal.ofReal V) ^ ((k : ℝ) / (2 * (q : ℝ))) := by
  let p : ℝ := (k : ℝ) / 2
  have hqpos : 0 < (q : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hq)
  have hkpos : 0 < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hp0 : 0 < p := by dsimp [p]; positivity
  have hpq : p ≤ (q : ℝ) := by
    dsimp [p]
    have hkR : (k : ℝ) ≤ 2 * (q : ℝ) := by exact_mod_cast hk2q
    linarith
  have hpq_nonneg : 0 ≤ p / (q : ℝ) := by positivity
  have hqpowInt : Integrable (fun ω => F ω ^ q) μ := by
    have hFmemNat : MemLp F q μ := by simpa using hFmem
    have hi := hFmemNat.integrable_norm_pow (p := q) (by omega : q ≠ 0)
    convert hi using 1
    ext ω
    rw [Real.norm_eq_abs, abs_of_nonneg (hF0 ω)]
  have htoENN :
      ∫⁻ ω, ‖F ω‖ₑ ^ (q : ℝ) ∂μ =
        ENNReal.ofReal (∫ ω, F ω ^ q ∂μ) := by
    calc
      _ = ∫⁻ ω, ENNReal.ofReal (F ω ^ q) ∂μ := by
        apply lintegral_congr
        intro ω
        simp [Real.enorm_eq_ofReal_abs, abs_of_nonneg (hF0 ω),
          ENNReal.rpow_natCast, ENNReal.ofReal_pow (hF0 ω)]
      _ = ENNReal.ofReal (∫ ω, F ω ^ q ∂μ) :=
        (ofReal_integral_eq_lintegral_ofReal hqpowInt
          (Filter.Eventually.of_forall fun ω => pow_nonneg (hF0 ω) q)).symm
  have hnormq :
      (eLpNorm' F (q : ℝ) μ) ^ (q : ℝ) ≤ ENNReal.ofReal V := by
    rw [lintegral_rpow_enorm_eq_rpow_eLpNorm' hqpos] at htoENN
    exact (le_of_eq htoENN).trans (ENNReal.ofReal_le_ofReal hMoment)
  have hinterp : eLpNorm' F p μ ≤ eLpNorm' F (q : ℝ) μ :=
    eLpNorm'_le_eLpNorm'_of_exponent_le hp0 hpq μ hFmem.aestronglyMeasurable
  have hnormqpow :
      (eLpNorm' F (q : ℝ) μ) ^ p ≤ (ENNReal.ofReal V) ^ (p / (q : ℝ)) := by
    calc
      _ = ((eLpNorm' F (q : ℝ) μ) ^ (q : ℝ)) ^ (p / (q : ℝ)) := by
        rw [← ENNReal.rpow_mul]
        congr 1
        dsimp [p]
        field_simp
      _ ≤ _ := ENNReal.rpow_le_rpow hnormq hpq_nonneg
  have hnormppow :
      (eLpNorm' F p μ) ^ p ≤ (ENNReal.ofReal V) ^ (p / (q : ℝ)) :=
    (ENNReal.rpow_le_rpow hinterp (by positivity : 0 ≤ p)).trans hnormqpow
  have hsqrtFunction :
      (fun ω => Real.sqrt (F ω)) = fun ω => |F ω| ^ (1 / (2 : ℝ)) := by
    funext ω
    rw [abs_of_nonneg (hF0 ω), ← Real.sqrt_eq_rpow]
  have hsqrtNorm :
      eLpNorm' (fun ω => Real.sqrt (F ω)) (k : ℝ) μ =
        eLpNorm' F p μ ^ (1 / (2 : ℝ)) := by
    rw [hsqrtFunction]
    have hh := eLpNorm'_norm_rpow F (k : ℝ) (1 / (2 : ℝ)) (by norm_num) (μ := μ)
    simpa [Real.norm_eq_abs, p, div_eq_mul_inv, mul_comm] using hh
  have htargetEq :
      ∫⁻ ω, (ENNReal.ofReal (Real.sqrt (F ω))) ^ (k : ℝ) ∂μ =
        (eLpNorm' F p μ) ^ p := by
    calc
      _ = ∫⁻ ω, ‖Real.sqrt (F ω)‖ₑ ^ (k : ℝ) ∂μ := by
        apply lintegral_congr
        intro ω
        simp [Real.enorm_eq_ofReal_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      _ = (eLpNorm' (fun ω => Real.sqrt (F ω)) (k : ℝ) μ) ^ (k : ℝ) :=
        lintegral_rpow_enorm_eq_rpow_eLpNorm' hkpos
      _ = (eLpNorm' F p μ ^ (1 / (2 : ℝ))) ^ (k : ℝ) := by rw [hsqrtNorm]
      _ = eLpNorm' F p μ ^ ((1 / (2 : ℝ)) * (k : ℝ)) := by
        rw [ENNReal.rpow_mul]
      _ = _ := by
        have hexp : (1 / (2 : ℝ)) * (k : ℝ) = p := by dsimp [p]; ring
        rw [hexp]
  calc
    _ = (eLpNorm' F p μ) ^ p := htargetEq
    _ ≤ (ENNReal.ofReal V) ^ (p / (q : ℝ)) := hnormppow
    _ = (ENNReal.ofReal V) ^ ((k : ℝ) / (2 * (q : ℝ))) := by
      have hexp : p / (q : ℝ) = (k : ℝ) / (2 * (q : ℝ)) := by
        dsimp [p]
        ring
      rw [hexp]



theorem nativeHeat_qMoment_root_valid (q : ℕ)
    (hq1 : 1 ≤ q) (hq10 : q ≤ 10) :
    nativeRootValid (nativeHeat009Qm.getD q 0) q = true := by
  interval_cases q <;> decide +kernel

/-- Outward roots turn an interpolated RMS moment bound into the generated cap. -/
theorem nativeHeat_rms_cap (k : ℕ) (hk2 : 2 ≤ k) (hk20 : k ≤ 20) {X : ℝ≥0∞}
    (hMoment : X ≤ (ENNReal.ofReal ((nativeHeat009Qm.getD ((k + 1) / 2) 0 : ℚ) : ℝ)) ^
      ((k : ℝ) / (2 * (((k + 1) / 2 : ℕ) : ℝ)))) :
    X ≤ (ENNReal.ofReal ((nativeRootUp
      (nativeRootUp (nativeHeat009Qm.getD ((k + 1) / 2) 0) ((k + 1) / 2)) 2 : ℚ) : ℝ)) ^
        (k : ℝ) := by
  let q : ℕ := (k + 1) / 2
  have hq1 : 1 ≤ q := by dsimp [q]; omega
  have hq10 : q ≤ 10 := by dsimp [q]; omega
  have hq20 : q ≤ 20 := by omega
  have hk2q : k ≤ 2 * q := by dsimp [q]; omega
  let v : ℚ := nativeHeat009Qm.getD q 0
  let u : ℚ := nativeRootUp v q
  let cap : ℚ := nativeRootUp u 2
  have hvValid := nativeHeat_qMoment_root_valid q hq1 hq10
  have huValid := nativeHeat009_qMoment_outer_root_valid q hq1 hq10
  have hvData : 0 < q ∧ 0 ≤ v ∧ 0 ≤ u ∧ v ≤ u ^ q := by
    simpa [v, u] using of_decide_eq_true hvValid
  have huValid' : nativeRootValid u 2 = true := by
    simpa [v, u] using huValid
  have huData : 0 < 2 ∧ 0 ≤ u ∧ 0 ≤ cap ∧ u ≤ cap ^ 2 := by
    exact of_decide_eq_true huValid'
  have hvcap : v ≤ cap ^ (2 * q) := by
    calc
      v ≤ u ^ q := hvData.2.2.2
      _ ≤ (cap ^ 2) ^ q := pow_le_pow_left₀ huData.2.1 huData.2.2.2 q
      _ = cap ^ (2 * q) := by rw [← pow_mul]
  have hvcapReal : (v : ℝ) ≤ (cap : ℝ) ^ (2 * (q : ℝ)) := by
    exact_mod_cast hvcap
  have hcapReal0 : 0 ≤ (cap : ℝ) := by exact_mod_cast huData.2.2.1
  have hqRpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hrootExpNonneg : 0 ≤ 2 * (q : ℝ) := mul_nonneg (by norm_num) hqRpos.le
  have hbase : ENNReal.ofReal (v : ℝ) ≤
      ENNReal.ofReal (cap : ℝ) ^ (2 * (q : ℝ)) := by
    calc
      ENNReal.ofReal (v : ℝ) ≤
          ENNReal.ofReal ((cap : ℝ) ^ (2 * (q : ℝ))) :=
        ENNReal.ofReal_le_ofReal hvcapReal
      _ = ENNReal.ofReal (cap : ℝ) ^ (2 * (q : ℝ)) :=
        (ENNReal.ofReal_rpow_of_nonneg hcapReal0 hrootExpNonneg).symm
  have hexp : 0 ≤ (k : ℝ) / (2 * (q : ℝ)) := by positivity
  have hpower := ENNReal.rpow_le_rpow hbase hexp
  have hflat :
      (ENNReal.ofReal (cap : ℝ) ^ (2 * (q : ℝ))) ^
          ((k : ℝ) / (2 * (q : ℝ))) =
        ENNReal.ofReal (cap : ℝ) ^ (k : ℝ) := by
    have hExpEq : (2 * (q : ℝ)) * ((k : ℝ) / (2 * (q : ℝ))) = (k : ℝ) := by
      field_simp
    rw [← ENNReal.rpow_mul, hExpEq]
  have hpower' : (ENNReal.ofReal (v : ℝ)) ^ ((k : ℝ) / (2 * (q : ℝ))) ≤
      ENNReal.ofReal (cap : ℝ) ^ (k : ℝ) := by
    rw [← hflat]
    exact hpower
  have hresult := hMoment.trans hpower'
  simpa [q, v, u, cap] using hresult


theorem nativeHeatRefined_centerQuadratic_measurable (M : ABKModel 2) (m : ℤ) :
    Measurable (nativeHeatQ3RefinedCarrierSourceCenterQuadratic M m) := by
  unfold nativeHeatQ3RefinedCarrierSourceCenterQuadratic
  apply measurable_const.mul
  apply Finset.measurable_sum
  intro i _
  exact (nativeHeatQ3RefinedZ_measurable M m i).pow_const 2

theorem nativeHeatRefined_centerQuadratic_nonneg (M : ABKModel 2) (m : ℤ)
    (ω : Cutoff.CutoffSample 2) :
    0 ≤ nativeHeatQ3RefinedCarrierSourceCenterQuadratic M m ω := by
  unfold nativeHeatQ3RefinedCarrierSourceCenterQuadratic
  exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
    (Finset.sum_nonneg fun i _ => sq_nonneg _)

/-- RMS moments of the refined centre vector, from its quadratic moment row. -/
theorem nativeHeatRefined_fresh_rms_moment
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (hg : M.gamma ≤ gammaZero)
    (m : ℤ) (hstate : nativeInductionState M h (m + 1))
    (k : ℕ) (hk2 : 2 ≤ k) (hk20 : k ≤ 20) :
    ∫⁻ ω, (ENNReal.ofReal (Real.sqrt
        (nativeHeatQ3RefinedCarrierSourceCenterQuadratic M m ω))) ^ (k : ℝ)
      ∂(Cutoff.cutoffSampleLaw M).toMeasure ≤
      (ENNReal.ofReal ((nativeRootUp
        (nativeRootUp (nativeHeat009Qm.getD ((k + 1) / 2) 0) ((k + 1) / 2)) 2 : ℚ) : ℝ)) ^
          (k : ℝ) := by
  classical
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  letI : IsProbabilityMeasure μ := (Cutoff.cutoffSampleLaw M).property
  let F := nativeHeatQ3RefinedCarrierSourceCenterQuadratic M m
  let q : ℕ := (k + 1) / 2
  have hq1 : 1 ≤ q := by dsimp [q]; omega
  have hq20 : q ≤ 20 := by dsimp [q]; omega
  have hk2q : k ≤ 2 * q := by dsimp [q]; omega
  have hF0 : ∀ ω, 0 ≤ F ω := nativeHeatRefined_centerQuadratic_nonneg M m
  have hFmeas : Measurable F := nativeHeatRefined_centerQuadratic_measurable M m
  have hlin := nativeHeatQ3RefinedCarrierSourceCenterQuadraticMoment_le_009
    M h hM hg m hstate q hq1 hq20
  have hfin : ∫⁻ ω, ENNReal.ofReal (F ω ^ q) ∂μ < ∞ :=
    lt_of_le_of_lt hlin ENNReal.ofReal_lt_top
  have hintPow : Integrable (fun ω => F ω ^ q) μ := by
    refine ⟨(hFmeas.pow_const q).aestronglyMeasurable, ?_⟩
    have : ∀ ω, ‖F ω ^ q‖ₑ = ENNReal.ofReal (F ω ^ q) := fun ω =>
      Real.enorm_eq_ofReal (pow_nonneg (hF0 ω) q)
    simp only [HasFiniteIntegral, this]
    exact hfin
  have hFmem : MemLp F (ENNReal.ofReal (q : ℝ)) μ := by
    have hnat : MemLp F (q : ℝ≥0∞) μ := by
      have h1 : Integrable (fun ω => ‖F ω‖ ^ (((q : ℝ≥0∞)).toReal)) μ := by
        simp only [ENNReal.toReal_natCast, Real.rpow_natCast]
        have heq : (fun ω => ‖F ω‖ ^ q) = fun ω => F ω ^ q := by
          funext ω
          rw [Real.norm_eq_abs, abs_of_nonneg (hF0 ω)]
        rw [heq]
        exact hintPow
      exact (integrable_norm_rpow_iff hFmeas.aestronglyMeasurable
        (by simp; omega) (by simp)).mp h1
    simpa using hnat
  have hMomentReal : ∫ ω, F ω ^ q ∂μ ≤ ((nativeHeat009Qm.getD q 0 : ℚ) : ℝ) := by
    have h1 : ENNReal.ofReal (∫ ω, F ω ^ q ∂μ) = ∫⁻ ω, ENNReal.ofReal (F ω ^ q) ∂μ :=
      ofReal_integral_eq_lintegral_ofReal hintPow
        (Filter.Eventually.of_forall fun ω => pow_nonneg (hF0 ω) q)
    have h2 : ENNReal.ofReal (∫ ω, F ω ^ q ∂μ) ≤
        ENNReal.ofReal ((nativeHeat009Qm.getD q 0 : ℚ) : ℝ) := by
      rw [h1]; exact hlin
    have hnn : (0 : ℝ) ≤ ((nativeHeat009Qm.getD q 0 : ℚ) : ℝ) := by
      have : ∀ i : Fin 21, (0 : ℚ) ≤ nativeHeat009Qm.getD i 0 := by decide +kernel
      exact_mod_cast this ⟨q, by omega⟩
    exact (ENNReal.ofReal_le_ofReal_iff hnn).mp h2
  have hrms := nativeHeat_lintegral_sqrt_rpow_le_of_moment F q k hq1 hk2 hk2q hF0
    hFmem ((nativeHeat009Qm.getD q 0 : ℚ) : ℝ) hMomentReal
  exact nativeHeat_rms_cap k hk2 hk20 hrms

theorem nativeHeat_cross_bound_all (k : ℕ) (hk2 : 2 ≤ k) (hk20 : k ≤ 20) :
    nativeHeatCrossReal nativeHeatParametersData k ≤
      ((nativeHeatParametersData.cross.getD k 0 : ℚ) : ℝ) := by
  interval_cases k <;> first
    | omega
    | exact nativeHeatCross02_bound
    | exact nativeHeatCross03_bound
    | exact nativeHeatCross04_bound
    | exact nativeHeatCross05_bound
    | exact nativeHeatCross06_bound
    | exact nativeHeatCross07_bound
    | exact nativeHeatCross08_bound
    | exact nativeHeatCross09_bound
    | exact nativeHeatCross10_bound
    | exact nativeHeatCross11_bound
    | exact nativeHeatCross12_bound
    | exact nativeHeatCross13_bound
    | exact nativeHeatCross14_bound
    | exact nativeHeatCross15_bound
    | exact nativeHeatCross16_bound
    | exact nativeHeatCross17_bound
    | exact nativeHeatCross18_bound
    | exact nativeHeatCross19_bound
    | exact nativeHeatCross20_bound

theorem nativeHeat_typeTwoFactor_eq_source
    {ι Η : Type*} [Fintype ι] (hcard : Fintype.card ι = 9^10)
    (k : ℕ) (hk2 : 2 ≤ k) (coeff : ι → Η → ℝ) (η : Η) (B : ℝ)
    (hB : 0 ≤ B) :
    Real.sqrt (Fintype.card (Fin 9 × Fin 9) : ℝ) * Real.sqrt ((k : ℝ) - 1) *
        Real.sqrt (∑ i, (|coeff i η| * B) ^ 2) /
          (Fintype.card ι : ℝ) =
      Real.sqrt ((((k - 1) * 9^2 : ℕ) / (9^10 : ℚ) : ℚ) : ℝ) * B *
        Real.sqrt ((Fintype.card ι : ℝ)⁻¹ * ∑ i, (coeff i η) ^ 2) := by
  have h81 : Real.sqrt (Fintype.card (Fin 9 × Fin 9) : ℝ) = 9 := by
    rw [show (Fintype.card (Fin 9 × Fin 9) : ℝ) = 9 ^ 2 by
      rw [Fintype.card_prod, Fintype.card_fin]; norm_num]
    exact Real.sqrt_sq (by norm_num)
  rw [h81]
  let N : ℝ := (Fintype.card ι : ℝ)
  let S : ℝ := ∑ i, (coeff i η) ^ 2
  let Q : ℝ := N⁻¹ * S
  have hN : N = (9 : ℝ)^10 := by
    dsimp [N]
    exact_mod_cast hcard
  have hNpos : 0 < N := by rw [hN]; positivity
  have hNne : N ≠ 0 := hNpos.ne'
  have hS : 0 ≤ S := by
    dsimp [S]
    exact Finset.sum_nonneg fun i _ => sq_nonneg (coeff i η)
  have hQ : 0 ≤ Q := by
    dsimp [Q]
    exact mul_nonneg (inv_nonneg.mpr hNpos.le) hS
  have hsum : ∑ i, (|coeff i η| * B) ^ 2 = B^2 * S := by
    dsimp [S]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [mul_pow, sq_abs]
    ring
  have hcoef :
      81 * ((k : ℝ) - 1) / N^2 =
        ((((k - 1) * 9^2 : ℕ) / (9^10 : ℚ) : ℚ) : ℝ) / N := by
    have hkCast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
      exact_mod_cast Nat.cast_sub (by omega : (1 : ℕ) ≤ k)
    rw [hN]
    push_cast
    rw [hkCast]
    norm_num
    field_simp
    ring
  have hk1R : 0 ≤ (k : ℝ) - 1 := by
    have hkNat : (1 : ℕ) ≤ k := by omega
    have hk : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hkNat
    linarith
  have hleftSq :
      (9 * Real.sqrt ((k : ℝ) - 1) *
        Real.sqrt (∑ i, (|coeff i η| * B) ^ 2) / N) ^ 2 =
        (81 * ((k : ℝ) - 1) / N^2) * B^2 * S := by
    rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt hk1R,
      Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg (|coeff i η| * B)), hsum]
    ring_nf
  have hrightSq :
      (Real.sqrt ((((k - 1) * 9^2 : ℕ) / (9^10 : ℚ) : ℚ) : ℝ) * B *
        Real.sqrt Q) ^ 2 =
        ((((k - 1) * 9^2 : ℕ) / (9^10 : ℚ) : ℚ) : ℝ) * B^2 * Q := by
    rw [mul_pow, mul_pow,
      Real.sq_sqrt (by positivity : 0 ≤
        ((((k - 1) * 9^2 : ℕ) / (9^10 : ℚ) : ℚ) : ℝ)),
      Real.sq_sqrt hQ]
  have hcoef' :
      81 * ((k : ℝ) - 1) / N^2 =
        ((((k - 1) * 9^2 : ℕ) / (9^10 : ℚ) : ℚ) : ℝ) * N⁻¹ := by
    simpa only [div_eq_mul_inv] using hcoef
  have hsquares :
      (9 * Real.sqrt ((k : ℝ) - 1) *
        Real.sqrt (∑ i, (|coeff i η| * B) ^ 2) / N) ^ 2 =
      (Real.sqrt ((((k - 1) * 9^2 : ℕ) / (9^10 : ℚ) : ℚ) : ℝ) * B *
        Real.sqrt Q) ^ 2 := by
    rw [hleftSq, hrightSq]
    dsimp [Q, S]
    rw [hcoef']
    ring_nf
  apply (sq_eq_sq₀ (by positivity) (by positivity)).mp hsquares


/-- A fresh vector RMS moment bound composes with the actual state-driven
four-colour shear estimate and the literal generated cross row. The fresh RMS
premise is deliberately stated on the pushforward fresh law, so the q3 grid
moment theorem can discharge it without any old-field hypotheses. -/
theorem nativeHeatRefined_oldShear_fresh_average_initialCrossMoment
    {ι Η : Type*} [MeasurableSpace Η] [Fintype ι] [Nonempty ι]
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hgamma : M.gamma ≤ gammaZero) (m : ℤ) (C : ι → TriadicCube 2)
    (hC : Function.Injective C) (hcard : Fintype.card ι = 9^10)
    (hscale : ∀ i, (C i).scale = m)
    (J : Set ℤ) (hJ : Disjoint (Set.Iic (m + 1)) J)
    (k : ℕ) (hk2 : 2 ≤ k) (hk20 : k ≤ 20)
    (hpast : ∀ n < m + 1, nativeInductionState M h n)
    {Fresh : Cutoff.CutoffSample 2 → Η}
    (hFreshLocal : @Measurable (Cutoff.CutoffSample 2) Η
      ((Cutoff.shellIndexSigma J).comap Subtype.val) _ Fresh)
    (hFreshMeas : Measurable Fresh) (coeff : ι → Η → ℝ)
    (hcoeff : ∀ i, Measurable (coeff i)) (freshCap : ℝ) (_hfreshCap : 0 ≤ freshCap)
    (hfresh :
      ∫⁻ η, (ENNReal.ofReal (Real.sqrt
        ((Fintype.card ι : ℝ)⁻¹ * ∑ i, (coeff i η)^2))) ^ (k : ℝ)
        ∂((Cutoff.cutoffSampleLaw M).toMeasure.map Fresh) ≤
        (ENNReal.ofReal freshCap) ^ (k : ℝ)) :
    ∫⁻ ω, ‖(2 * (∑ i, coeff i (Fresh ω) *
        Variational.shearTraceLinear (coarseBlockMatrix (cubeSet (C i))
          (Cutoff.coefficientCutoff M.nu (m + 1) ω).toFun))) /
          (Fintype.card ι : ℝ)‖ₑ ^ (k : ℝ)
        ∂(Cutoff.cutoffSampleLaw M).toMeasure ≤
      (ENNReal.ofReal
        ((nativeHeatParametersData.cross.getD k 0 : ℚ) * freshCap)) ^ (k : ℝ) := by
  have hk2R : 2 ≤ (k : ℝ) := by exact_mod_cast hk2
  have hkR0 : 0 ≤ (k : ℝ) := by positivity
  have hCross := nativeHeat_cross_bound_all k hk2 hk20
  let shearCap : ℝ := Real.sqrt (2 * ((nativeHeatB : ℝ) *
    nativeHeatHnReal nativeHeatParametersData ((k : ℚ) / 2) +
      ((nativeHeatEps * nativeHeatParametersData.hp : ℚ) : ℝ)))
  let N : ℝ := (Fintype.card ι : ℝ)
  let rms : Η → ℝ := fun η => Real.sqrt (N⁻¹ * ∑ i, (coeff i η)^2)
  let coeff₂ : ι → Η → ℝ := fun i η => 2 * coeff i η
  have hshearCap : 0 ≤ shearCap := by exact Real.sqrt_nonneg _
  have hN : N = (9 : ℝ)^10 := by
    dsimp [N]
    exact_mod_cast hcard
  have hrms (η : Η) : 0 ≤ rms η := by exact Real.sqrt_nonneg _
  have hrms₂ (η : Η) :
      Real.sqrt (N⁻¹ * ∑ i, (coeff₂ i η)^2) = 2 * rms η := by
    have hsum : ∑ i, (coeff₂ i η)^2 = 4 * ∑ i, (coeff i η)^2 := by
      dsimp [coeff₂]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    rw [hsum, show N⁻¹ * (4 * ∑ i, (coeff i η)^2) =
      4 * (N⁻¹ * ∑ i, (coeff i η)^2) by ring,
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
    rw [show (4 : ℝ) = 2^2 by norm_num,
      Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  have hfactor (η : Η) :
      Real.sqrt (Fintype.card (Fin 9 × Fin 9) : ℝ) * Real.sqrt ((k : ℝ) - 1) *
          Real.sqrt (∑ i, (|coeff₂ i η| * shearCap) ^ 2) / N ≤
        ((nativeHeatParametersData.cross.getD k 0 : ℚ) : ℝ) * rms η := by
    have heq := nativeHeat_typeTwoFactor_eq_source hcard k hk2 coeff₂ η shearCap hshearCap
    have hCrossReal :
        nativeHeatCrossReal nativeHeatParametersData k =
          2 * Real.sqrt ((((k - 1) * 9^2 : ℕ) / (9^10 : ℚ) : ℚ) : ℝ) * shearCap := rfl
    have hbound := mul_le_mul_of_nonneg_right hCross (hrms η)
    calc
      _ = Real.sqrt ((((k - 1) * 9^2 : ℕ) / (9^10 : ℚ) : ℚ) : ℝ) *
          shearCap * Real.sqrt (N⁻¹ * ∑ i, (coeff₂ i η)^2) := heq
      _ = nativeHeatCrossReal nativeHeatParametersData k * rms η := by
        rw [hrms₂ η, hCrossReal]
        ring
      _ ≤ ((nativeHeatParametersData.cross.getD k 0 : ℚ) : ℝ) * rms η := hbound
  have hrow0 :
      0 ≤ ((nativeHeatParametersData.cross.getD k 0 : ℚ) : ℝ) := by
    have hsource0 : 0 ≤ nativeHeatCrossReal nativeHeatParametersData k := by
      unfold nativeHeatCrossReal
      positivity
    exact hsource0.trans hCross
  have hcoeff₂ (i : ι) : Measurable (coeff₂ i) := by
    dsimp [coeff₂]
    exact measurable_const.mul (hcoeff i)
  have htrace : ∀ i, MemLp (Cold.coldNativeCellTrace M (m + 1) (C i)) 2
      (Cutoff.cutoffSampleLaw M).toMeasure := fun i =>
    nativeHeatRefined_childTrace_memLp_two M h hM hgamma m hpast (C i) (hscale i)
  have hcaps (i : ι) := nativeHeatRefined_childShear_lpCap M h hM hgamma (C i) m (hscale i)
    hpast k hk2 hk20
  have hIndep := nativeHeatRefined_shear_colour_independent M h hM m C hC hscale
  have hAdapter := nativeHeat_oldShear_fresh_average_moment_of_caps M (m + 1) J hJ C
    (fun i => nativeHeatRefinedColor81 (C i)) (k : ℝ) hk2R htrace
    (fun i => (hcaps i).1) hIndep (fun _ => shearCap) (fun _ => hshearCap)
    (fun i => (hcaps i).2) hFreshLocal hFreshMeas coeff₂ hcoeff₂
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let ν := μ.map Fresh
  have hsumEq (ω : Cutoff.CutoffSample 2) :
      (∑ i, coeff₂ i (Fresh ω) *
        Variational.shearTraceLinear (coarseBlockMatrix (cubeSet (C i))
          (Cutoff.coefficientCutoff M.nu (m + 1) ω).toFun)) =
      2 * (∑ i, coeff i (Fresh ω) *
        Variational.shearTraceLinear (coarseBlockMatrix (cubeSet (C i))
          (Cutoff.coefficientCutoff M.nu (m + 1) ω).toFun)) := by
    calc
      _ = ∑ i, 2 * (coeff i (Fresh ω) *
          Variational.shearTraceLinear (coarseBlockMatrix (cubeSet (C i))
            (Cutoff.coefficientCutoff M.nu (m + 1) ω).toFun)) := by
          apply Finset.sum_congr rfl
          intro i hi
          simp [coeff₂]
          ring
      _ = _ := by rw [Finset.mul_sum]
  have hAdapter' :
      ∫⁻ ω, ‖(2 * (∑ i, coeff i (Fresh ω) *
          Variational.shearTraceLinear (coarseBlockMatrix (cubeSet (C i))
            (Cutoff.coefficientCutoff M.nu (m + 1) ω).toFun))) /
            (Fintype.card ι : ℝ)‖ₑ ^ (k : ℝ) ∂μ ≤
        ∫⁻ η, (ENNReal.ofReal (Real.sqrt (Fintype.card (Fin 9 × Fin 9) : ℝ) * Real.sqrt ((k : ℝ) - 1) *
          Real.sqrt (∑ i, (|coeff₂ i η| * shearCap) ^ 2) / N)) ^
            (k : ℝ) ∂ν := by
    calc
      _ = ∫⁻ ω, ‖(∑ i, coeff₂ i (Fresh ω) *
            Variational.shearTraceLinear (coarseBlockMatrix (cubeSet (C i))
              (Cutoff.coefficientCutoff M.nu (m + 1) ω).toFun)) /
              (Fintype.card ι : ℝ)‖ₑ ^ (k : ℝ) ∂μ := by
          apply lintegral_congr
          intro ω
          rw [← hsumEq ω]
      _ ≤ _ := by simpa only [μ, ν, N, shearCap] using hAdapter
  have hpoint (η : Η) :
      (ENNReal.ofReal (Real.sqrt (Fintype.card (Fin 9 × Fin 9) : ℝ) * Real.sqrt ((k : ℝ) - 1) *
        Real.sqrt (∑ i, (|coeff₂ i η| * shearCap)^2) / N)) ^ (k : ℝ) ≤
      (ENNReal.ofReal (((nativeHeatParametersData.cross.getD k 0 : ℚ) : ℝ) *
        rms η)) ^ (k : ℝ) := by
    exact ENNReal.rpow_le_rpow
      (ENNReal.ofReal_le_ofReal (hfactor η)) hkR0
  have hIntegral := hAdapter'.trans (lintegral_mono hpoint)
  have hsumMeas : Measurable (fun η => ∑ i, coeff i η ^ 2) := by
    apply Finset.measurable_sum
    intro i hi
    exact (hcoeff i).pow_const 2
  have hrmsMeas : Measurable rms := by
    dsimp [rms]
    exact Real.continuous_sqrt.measurable.comp (measurable_const.mul hsumMeas)
  have hpowMeas : Measurable (fun η => (ENNReal.ofReal (rms η)) ^ (k : ℝ)) :=
    ENNReal.continuous_rpow_const.measurable.comp
      (ENNReal.measurable_ofReal.comp hrmsMeas)
  have hFactorization :
      ∫⁻ η, (ENNReal.ofReal (((nativeHeatParametersData.cross.getD k 0 : ℚ) : ℝ) *
        rms η)) ^ (k : ℝ) ∂ν =
        (ENNReal.ofReal ((nativeHeatParametersData.cross.getD k 0 : ℚ) : ℝ)) ^
            (k : ℝ) *
          ∫⁻ η, (ENNReal.ofReal (rms η)) ^ (k : ℝ) ∂ν := by
    calc
      _ = ∫⁻ η, (ENNReal.ofReal ((nativeHeatParametersData.cross.getD k 0 : ℚ) : ℝ)) ^
            (k : ℝ) * (ENNReal.ofReal (rms η)) ^ (k : ℝ) ∂ν := by
          apply lintegral_congr_ae
          filter_upwards with η
          calc
            (ENNReal.ofReal (((nativeHeatParametersData.cross.getD k 0 : ℚ) : ℝ) *
              rms η)) ^ (k : ℝ) =
                (ENNReal.ofReal ((nativeHeatParametersData.cross.getD k 0 : ℚ) : ℝ) *
                  ENNReal.ofReal (rms η)) ^ (k : ℝ) := by
                    rw [← ENNReal.ofReal_mul hrow0]
            _ = (ENNReal.ofReal ((nativeHeatParametersData.cross.getD k 0 : ℚ) : ℝ)) ^
                  (k : ℝ) * (ENNReal.ofReal (rms η)) ^ (k : ℝ) :=
                ENNReal.mul_rpow_of_nonneg _ _ hkR0
      _ = _ := lintegral_const_mul _ hpowMeas
  calc
    _ ≤ (ENNReal.ofReal ((nativeHeatParametersData.cross.getD k 0 : ℚ) : ℝ)) ^
          (k : ℝ) * ∫⁻ η, (ENNReal.ofReal (rms η)) ^ (k : ℝ) ∂ν :=
        hIntegral.trans_eq hFactorization
    _ ≤ (ENNReal.ofReal ((nativeHeatParametersData.cross.getD k 0 : ℚ) : ℝ)) ^
          (k : ℝ) * (ENNReal.ofReal freshCap) ^ (k : ℝ) :=
        by
          gcongr
    _ = (ENNReal.ofReal (((nativeHeatParametersData.cross.getD k 0 : ℚ) : ℝ) *
          freshCap)) ^ (k : ℝ) := by
        calc
          _ = (ENNReal.ofReal ((nativeHeatParametersData.cross.getD k 0 : ℚ) : ℝ) *
                ENNReal.ofReal freshCap) ^ (k : ℝ) := by
              rw [← ENNReal.mul_rpow_of_nonneg _ _ hkR0]
          _ = _ := by rw [← ENNReal.ofReal_mul hrow0]


theorem nativeHeat_generatedCap_nonneg (q : ℕ) (hq1 : 1 ≤ q) (hq10 : q ≤ 10) :
    0 ≤ (nativeRootUp (nativeRootUp (nativeHeat009Qm.getD q 0) q) 2 : ℚ) := by
  let u : ℚ := nativeRootUp (nativeHeat009Qm.getD q 0) q
  let cap : ℚ := nativeRootUp u 2
  have hvalid := nativeHeat009_qMoment_outer_root_valid q hq1 hq10
  have hvalid' : nativeRootValid u 2 = true := by simpa [u] using hvalid
  have hdata : 0 < 2 ∧ 0 ≤ u ∧ 0 ≤ cap ∧ u ≤ cap ^ 2 := of_decide_eq_true hvalid'
  exact_mod_cast hdata.2.2.1

theorem nativeHeatQ3RefinedCarrierChild_injective (m : ℤ) :
    Function.Injective (nativeHeatQ3RefinedCarrierChild m) := by
  intro i j hij
  have h1 : nativeHeatQ3RefinedChildCube (originCube 2 (m + 10)) (finProdFinEquiv.symm i) =
      nativeHeatQ3RefinedChildCube (originCube 2 (m + 10)) (finProdFinEquiv.symm j) := hij
  have h2 := Triadic.diagMeshCell_injective (originCube 2 (m + 10)) 10 h1
  have h3 : finProdFinEquiv.symm i = finProdFinEquiv.symm j := by
    have := congrFun h2
    apply Prod.ext
    · simpa [nativeHeatQ3RefinedChildDigits] using congrFun h2 0
    · simpa [nativeHeatQ3RefinedChildDigits] using congrFun h2 1
  exact finProdFinEquiv.symm.injective h3

/-- The refined shear-cross bound. -/
theorem nativeHeatQ3RefinedCarrierSourceShearCrossMoment_le_009
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (m : ℤ) (hgamma : M.gamma ≤ gammaZero)
    (hstate : nativeInductionState M h (m + 1))
    (hpast : ∀ n < m + 1, nativeInductionState M h n)
    (k : ℕ) (hk2 : 2 ≤ k) (hk20 : k ≤ 20) :
    ∫⁻ ω, ‖nativeHeatQ3RefinedCarrierSourceShearCross M m ω‖ₑ ^ (k : ℝ)
      ∂(Cutoff.cutoffSampleLaw M).toMeasure ≤
      (ENNReal.ofReal ((nativeHeatParametersData.cross.getD k 0 : ℚ) *
        (nativeRootUp (nativeRootUp
          (nativeHeat009Qm.getD ((k + 1) / 2) 0) ((k + 1) / 2)) 2 : ℚ) : ℝ)) ^
            (k : ℝ) := by
  classical
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let ι := nativeHeatQ3RefinedCarrierIndex
  let C : ι → TriadicCube 2 := nativeHeatQ3RefinedCarrierChild m
  let J : Set ℤ := Set.Icc (m + 2) (m + 10)
  let Fresh : Cutoff.CutoffSample 2 → ι → ℝ := fun ω i =>
    nativeHeatQ3RefinedCarrierSourceZ M m ω i
  let coeff : ι → (ι → ℝ) → ℝ := fun i η => η i
  haveI : Nonempty ι := ⟨⟨0, by norm_num⟩⟩
  have hJ : Disjoint (Set.Iic (m + 1)) J := by
    apply Set.disjoint_left.mpr
    intro z hz hzJ
    rcases hzJ with ⟨hzLo, hzHi⟩
    change z ≤ m + 1 at hz
    omega
  have hFreshMeas : Measurable Fresh :=
    measurable_pi_iff.mpr fun i => nativeHeatQ3RefinedZ_measurable M m i
  have hFreshLocal : @Measurable (Cutoff.CutoffSample 2) (ι → ℝ)
      ((Cutoff.shellIndexSigma J).comap Subtype.val) inferInstance Fresh := by
    refine (@measurable_pi_iff (Cutoff.CutoffSample 2) ι (fun _ => ℝ)
      ((Cutoff.shellIndexSigma J).comap Subtype.val) (fun _ => inferInstance)).mpr ?_
    intro i
    exact nativeHeatQ3RefinedZ_shellLocal M m i
  have hcoeff (i : ι) : Measurable (coeff i) := measurable_pi_apply i
  let q : ℕ := (k + 1) / 2
  have hq1 : 1 ≤ q := by dsimp [q]; omega
  have hq10 : q ≤ 10 := by dsimp [q]; omega
  let freshCap : ℝ := (nativeRootUp (nativeRootUp (nativeHeat009Qm.getD q 0) q) 2 : ℚ)
  have hcap : 0 ≤ freshCap := by
    change 0 ≤ ((nativeRootUp (nativeRootUp (nativeHeat009Qm.getD q 0) q) 2 : ℚ) : ℝ)
    exact_mod_cast nativeHeat_generatedCap_nonneg q hq1 hq10
  have hRmeas : Measurable (fun η : ι → ℝ =>
      (ENNReal.ofReal (Real.sqrt ((Fintype.card ι : ℝ)⁻¹ *
        ∑ i : ι, (coeff i η) ^ 2))) ^ (k : ℝ)) := by
    have hsum : Measurable (fun η : ι → ℝ => ∑ i : ι, (coeff i η) ^ 2) := by
      apply Finset.measurable_sum
      intro i _
      exact (hcoeff i).pow_const 2
    exact ENNReal.continuous_rpow_const.measurable.comp
      (ENNReal.measurable_ofReal.comp
        (Real.continuous_sqrt.measurable.comp (measurable_const.mul hsum)))
  have hfresh :
      ∫⁻ η, (ENNReal.ofReal (Real.sqrt ((Fintype.card ι : ℝ)⁻¹ *
        ∑ i : ι, (coeff i η) ^ 2))) ^ (k : ℝ) ∂(μ.map Fresh) ≤
        (ENNReal.ofReal freshCap) ^ (k : ℝ) := by
    calc
      _ = ∫⁻ ω, (ENNReal.ofReal (Real.sqrt ((Fintype.card ι : ℝ)⁻¹ *
          ∑ i : ι, (coeff i (Fresh ω)) ^ 2))) ^ (k : ℝ) ∂μ := by
        rw [MeasureTheory.lintegral_map hRmeas hFreshMeas]
      _ = ∫⁻ ω, (ENNReal.ofReal (Real.sqrt
          (nativeHeatQ3RefinedCarrierSourceCenterQuadratic M m ω))) ^ (k : ℝ) ∂μ := by
        apply lintegral_congr
        intro ω
        rfl
      _ ≤ _ := nativeHeatRefined_fresh_rms_moment M h hM hgamma m hstate k hk2 hk20
  have hmain := nativeHeatRefined_oldShear_fresh_average_initialCrossMoment M h hM hgamma m C
    (nativeHeatQ3RefinedCarrierChild_injective m) nativeHeatQ3RefinedCarrierIndex_card
    (fun i => nativeHeatQ3RefinedCarrierChild_scale m i) J hJ k hk2 hk20 hpast
    hFreshLocal hFreshMeas coeff hcoeff freshCap hcap hfresh
  refine le_of_eq_of_le ?_ hmain
  apply lintegral_congr
  intro ω
  unfold nativeHeatQ3RefinedCarrierSourceShearCross
  congr 2
  rw [div_eq_inv_mul]
  simp only [coeff, Fresh, C, ι]
  ring

end ASDExplicitGamma.Native
