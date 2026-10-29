/-
Copyright (c) 2026 Scott N. Armstrong. All rights reserved.
-/
module

public import ASDExplicitGamma.AllOrder.CirGenerator19
public import ASDExplicitGamma.AllOrder.CirModelHeatData
public import ASDExplicitGamma.Gaussian.ChildResponse
public import ASDExplicitGamma.Inverse.PureFluxGeneratorTraceLimit

/-! # Heat data for actual weighted translated-square CIR traces -/

@[expose] public section

open Homogenization MeasureTheory Set ASDExplicitGamma.Gaussian
  ASDExplicitGamma.Main ASDExplicitGamma.Response ASDExplicitGamma.Triadic
  ASDExplicitGamma.Variational
open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open scoped Topology ENNReal

namespace ASDExplicitGamma.AllOrder

local instance cirFamilyHeatDataFiniteMeasure (Q : TriadicCube 2) :
    IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
  (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume

local instance cirFamilyHeatDataCompactClosure (Q : TriadicCube 2) :
    CompactSpace (closure (openCubeSet Q)) :=
  isCompact_iff_compactSpace.mp (isBounded_openCubeSet Q).isCompact_closure

/-- Restrict a compact parent scalar field to a translated response square and
view that restriction in the exact bounded-continuous response carrier. -/
noncomputable def cirSquareRestrictionCLM {K : Set (Vec 2)} [CompactSpace K]
    (Q : TriadicCube 2) (hQ : closure (openCubeSet Q) ⊆ K) :
    C(K, ℝ) →L[ℝ] ResponseCoefficient (openCubeSet Q) :=
  (ContinuousMap.linearIsometryBoundedOfCompact
      (closure (openCubeSet Q)) ℝ ℝ).toLinearIsometry.toContinuousLinearMap.comp
    (ContinuousMap.compCLM ℝ ℝ
      ⟨fun x => ⟨x.1, hQ x.2⟩, by fun_prop⟩)

theorem cirSquareRestrictionCLM_norm_le {K : Set (Vec 2)} [CompactSpace K]
    (Q : TriadicCube 2) (hQ : closure (openCubeSet Q) ⊆ K) (f : C(K, ℝ)) :
    ‖cirSquareRestrictionCLM Q hQ f‖ ≤ ‖f‖ := by
  let e := ContinuousMap.linearIsometryBoundedOfCompact
    (closure (openCubeSet Q)) ℝ ℝ |>.toLinearIsometry
  change ‖e ((ContinuousMap.compCLM ℝ ℝ
    ⟨fun x => ⟨x.1, hQ x.2⟩, by fun_prop⟩) f)‖ ≤ ‖f‖
  rw [e.norm_map]
  apply (ContinuousMap.norm_le _ (norm_nonneg _)).2
  intro x
  exact f.norm_coe_le_norm ⟨x.1, hQ x.2⟩

/-- The finite weighted trace of translated squares, as one observable on a
common parent coefficient field. -/
noncomputable def cirWeightedSquareTraceObservable {K : Set (Vec 2)}
    [CompactSpace K] {ι : Type*} (s : Finset ι) (w : ι → ℝ)
    (Q : ι → TriadicCube 2) (hQ : ∀ a, closure (openCubeSet (Q a)) ⊆ K)
    (ν σ : ℝ) : C(K, ℝ) → ℝ := fun f =>
  ∑ a ∈ s, w a * squareTrace (Q a) ν σ
    (cirSquareRestrictionCLM (Q a) (hQ a) f)

theorem cirWeightedSquareTraceObservable_hasPolynomiallyBoundedC2Derivatives
    {K : Set (Vec 2)} [CompactSpace K] {ι : Type*}
    (s : Finset ι) (w : ι → ℝ) (Q : ι → TriadicCube 2)
    (hQ : ∀ a, closure (openCubeSet (Q a)) ⊆ K)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ) :
    HasPolynomiallyBoundedC2Derivatives
      (cirWeightedSquareTraceObservable s w Q hQ ν σ) := by
  classical
  let L (a : ι) : C(K, ℝ) →L[ℝ] ResponseCoefficient (openCubeSet (Q a)) :=
    cirSquareRestrictionCLM (Q a) (hQ a)
  have hsingle (a : ι) :
      HasPolynomiallyBoundedC2Derivatives
        (fun f : C(K, ℝ) => squareTrace (Q a) ν σ (L a f)) := by
    let E (p : Fin 2 × Bool) (f : C(K, ℝ)) :=
      squareLoadEnergy (Q a) ν σ hν hσ p (L a f)
    have hE (p : Fin 2 × Bool) : HasPolynomiallyBoundedC2Derivatives (E p) := by
      have hload := responseFrameEnergyObservable_hasPolynomiallyBoundedC2Derivatives
        (measurableSet_openCubeSet (Q a)) (square_volume_pos (Q a))
        ν σ hν hσ (orthonormalFrameLoad p.1 (lemmaVLoadSign p.2))
      have hcomp := Gaussian.c2_polynomial_comp_contraction
        (L a) (fun f => cirSquareRestrictionCLM_norm_le (Q a) (hQ a) f) hload
      simpa only [E, squareLoadEnergy] using hcomp
    have hsum : HasPolynomiallyBoundedC2Derivatives
        (fun f : C(K, ℝ) => ∑ p : Fin 2 × Bool, E p f) :=
      Gaussian.c2_polynomial_sum Finset.univ E (by intro p hp; exact hE p)
    have heq : (fun f : C(K, ℝ) => squareTrace (Q a) ν σ (L a f)) =
        fun f => (∑ p : Fin 2 × Bool, E p f) - 4 := by
      funext f
      simpa only [E, squareLoadEnergy, L, cirSquareRestrictionCLM,
        ContinuousLinearMap.comp_apply] using
        (squareTrace_eq_load_sum (Q a) ν σ hν hσ (L a f))
    rw [heq]
    exact Gaussian.hasPolynomiallyBoundedC2Derivatives_sub_const hsum 4
  have hterm (a : ι) :
      HasPolynomiallyBoundedC2Derivatives
        (fun f : C(K, ℝ) => w a * squareTrace (Q a) ν σ (L a f)) :=
    Gaussian.c2_polynomial_mul
      (Gaussian.c2_polynomial_const (E := C(K, ℝ)) (w a)) (hsingle a)
  have hsum : HasPolynomiallyBoundedC2Derivatives
      (fun f : C(K, ℝ) => ∑ a ∈ s,
        w a * squareTrace (Q a) ν σ (L a f)) := by
    apply Gaussian.c2_polynomial_sum s
      (fun a f => w a * squareTrace (Q a) ν σ (L a f))
    intro a ha
    exact hterm a
  have heq : cirWeightedSquareTraceObservable s w Q hQ ν σ = fun f =>
      ∑ a ∈ s, w a * squareTrace (Q a) ν σ (L a f) := by
    funext f
    rfl
  rw [heq]
  exact hsum

theorem cirWeightedSquareTraceObservable_nonneg
    {K : Set (Vec 2)} [CompactSpace K] {ι : Type*}
    (s : Finset ι) (w : ι → ℝ) (Q : ι → TriadicCube 2)
    (hQ : ∀ a, closure (openCubeSet (Q a)) ⊆ K)
    (hw : ∀ a ∈ s, 0 ≤ w a) (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (f : C(K, ℝ)) :
    0 ≤ cirWeightedSquareTraceObservable s w Q hQ ν σ f := by
  classical
  unfold cirWeightedSquareTraceObservable
  apply Finset.sum_nonneg
  intro a ha
  apply mul_nonneg (hw a ha)
  exact traceDefect_nonneg_of_ellipticFieldOn_triCube (div_pos hν hσ)
    (lemmaV_frameCoefficient_isEllipticOn (measurableSet_cubeSet (Q a))
      ν σ hν hσ (cirSquareRestrictionCLM (Q a) (hQ a) f)) (by norm_num)

/-- Restricting the actual MainCube heat factor to any contained translated
square gives exactly the globally indexed physical q3 direction. -/
theorem aoCir_mainCube_restrict_direction
    (n : ℤ) (Q : TriadicCube 2) (b : ℝ) (L : {l : ℝ // 0 < l})
    (hQ : closure (openCubeSet Q) ⊆ closure (cubeSet (originCube 2 n)))
    (j : ℕ) :
    cirSquareRestrictionCLM Q hQ
      (Main.mainCubeH3Value n b L (Main.mainCubeQ3Directions n b L j)) =
    squareQ3Directions Q b L j := by
  ext x
  change Main.mainCubeH3Value n b L (Main.mainCubeQ3Directions n b L j)
      ⟨x.1, hQ x.2⟩ =
    q3Convolution b L h3Zero (gaussEnumerated whiteBasis j) x.1
  rw [Main.mainCubeH3Value_direction]
  rfl

/-- Positive-shift heat data when the shell being inserted and the completed
true frame are different labels.  The Gaussian directions come from the
actual fresh shell, while the trace observable retains the fixed CIR frame. -/
theorem aoCir_weightedSquareTrace_shell_heat_data
    (n : ℤ) (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (frameLabel baseLabel : ℤ) {ι : Type*} (s : Finset ι) (w : ι → ℝ)
    (Q : ι → TriadicCube 2)
    (hQ : ∀ a, closure (openCubeSet (Q a)) ⊆ closure (cubeSet (originCube 2 n)))
    (hw : ∀ a ∈ s, 0 ≤ w a)
    {p ε : ℝ} (hp : 1 < p) (hε : 0 < ε) :
    let K := closure (cubeSet (originCube 2 n))
    let σ := (Annealed.sigmaBar M frameLabel : ℝ)
    let Φ := cirWeightedSquareTraceObservable s w Q hQ M.nu σ
    let b := q3ModelAmplitude M h (baseLabel + 1)
    let L := q3ModelLength (baseLabel + 1)
    let H := fun j => Main.mainCubeH3Value n b L (Main.mainCubeQ3Directions n b L j)
    P12RegularizedHeatData (Cutoff.cutoffSampleLaw M).toMeasure
      (p12ModelObservablePath K baseLabel Φ)
      (p12ModelGeneratorPath K baseLabel Φ H)
      (p12ModelBracketPath K baseLabel Φ H) p ε := by
  let K := closure (cubeSet (originCube 2 n))
  let σ : ℝ := Annealed.sigmaBar M frameLabel
  let Φ := cirWeightedSquareTraceObservable s w Q hQ M.nu σ
  let b := q3ModelAmplitude M h (baseLabel + 1)
  let L := q3ModelLength (baseLabel + 1)
  let H := fun j => Main.mainCubeH3Value n b L (Main.mainCubeQ3Directions n b L j)
  obtain ⟨ell, hK⟩ := exists_originCube_containing_compact K
    (isBounded_cubeSet (originCube 2 n)).isCompact_closure
  have hσ : 0 < σ := (Annealed.sigmaBar_characterization M frameLabel).1
  have hΦ : HasPolynomiallyBoundedC2Derivatives Φ :=
    cirWeightedSquareTraceObservable_hasPolynomiallyBoundedC2Derivatives
      s w Q hQ M.nu σ M.nu_pos hσ
  have hΦ0 : ∀ x, 0 ≤ Φ x :=
    fun x => cirWeightedSquareTraceObservable_nonneg s w Q hQ hw M.nu σ
      M.nu_pos hσ x
  have hlaw := Main.main_actual_fresh_cube_factor_law n M h hM baseLabel
  let T : Main.MainCubeH3 n b L →L[ℝ] C(K, ℝ) := Main.mainCubeH3Value n b L
  let v : ℕ → Main.MainCubeH3 n b L := Main.mainCubeQ3Directions n b L
  have hA : Summable (fun j => ‖v j‖ ^ 2) := Main.mainCubeQ3Directions_summable n b L
  have hlaw' : (Cutoff.cutoffSampleLaw M).toMeasure.map
      (fun ω : Cutoff.CutoffSample 2 => shellFieldScalarRestriction K (ω.1 (baseLabel + 1))) =
      standardGaussianInfinitePi.map
        (@gaussianSeriesLimitE (Main.MainCubeH3 n b L) C(K, ℝ)
          inferInstance (Main.mainCubeH3InnerProductSpace n b L) inferInstance inferInstance
          inferInstance inferInstance inferInstance inferInstance inferInstance v hA T) := by
    simpa [K, b, L, T, v, Main.mainCubeQ3Series] using hlaw
  have hdata := @aoCir_p12_regularized_model_heat_data_of_realization
    (Main.MainCubeH3 n b L) inferInstance (Main.mainCubeH3InnerProductSpace n b L)
    inferInstance inferInstance inferInstance inferInstance inferInstance
    K inferInstance M ell baseLabel hK v hA T hlaw' Φ hΦ hΦ0 p ε hp hε
  exact hdata

private theorem aoCir_secondDirectionalDerivative_comp_linear
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : F → ℝ) (hf : ContDiff ℝ 2 f) (L : E →L[ℝ] F) (x v : E) :
    secondDirectionalDerivative (fun y => f (L y)) x v =
      secondDirectionalDerivative f (L x) (L v) := by
  have hfd : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hfirst (y : E) :
      fderiv ℝ (fun z => f (L z)) y = (fderiv ℝ f (L y)).comp L :=
    (hfd (L y)).hasFDerivAt.comp y L.hasFDerivAt |>.fderiv
  have hdir : (fun y => fderiv ℝ (fun z => f (L z)) y v) =
      fun y => fderiv ℝ f (L y) (L v) := by
    funext y
    rw [hfirst]
    rfl
  let g : F → ℝ := fun y => fderiv ℝ f y (L v)
  have hg : DifferentiableAt ℝ g (L x) :=
    ((hf.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).clm_apply
      contDiff_const).differentiable_one.differentiableAt
  have hsecond := hg.hasFDerivAt.comp x L.hasFDerivAt
  have hsecond' : fderiv ℝ (fun y : E => g (L y)) x =
      (fderiv ℝ g (L x)).comp L := by
    simpa only [Function.comp_def] using hsecond.fderiv
  unfold secondDirectionalDerivative
  rw [hdir]
  change fderiv ℝ (fun y => g (L y)) x v =
    fderiv ℝ (fun y => fderiv ℝ f y (L v)) (L x) (L v)
  rw [hsecond']
  rfl

private theorem aoCir_secondDirectionalDerivative_weighted_sum
    {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s : Finset ι) (w : ι → ℝ) (f : ι → E → ℝ)
    (hf : ∀ i, ContDiff ℝ 2 (f i)) (x v : E) :
    secondDirectionalDerivative (fun y => ∑ i ∈ s, w i * f i y) x v =
      ∑ i ∈ s, w i * secondDirectionalDerivative (f i) x v := by
  let F : ι → E → ℝ := fun i y => w i * f i y
  have hF : ∀ i, ContDiff ℝ 2 (F i) := by
    intro i
    exact contDiff_const.mul (hf i)
  have hfirst (y : E) :
      fderiv ℝ (fun z => ∑ i ∈ s, F i z) y =
        ∑ i ∈ s, fderiv ℝ (F i) y := by
    have hD (i : ι) (_hi : i ∈ s) : DifferentiableAt ℝ (F i) y :=
      (hF i).differentiable (by norm_num) y
    exact fderiv_fun_sum (fun i hi => hD i hi)
  have hfirstDir : (fun y => fderiv ℝ (fun z => ∑ i ∈ s, F i z) y v) =
      fun y => ∑ i ∈ s, fderiv ℝ (F i) y v := by
    funext y
    rw [hfirst y]
    simp
  unfold secondDirectionalDerivative
  rw [hfirstDir]
  have hD (i : ι) (_hi : i ∈ s) :
      DifferentiableAt ℝ (fun y => fderiv ℝ (F i) y v) x := by
    have hFd : ContDiffAt ℝ 1 (fderiv ℝ (F i)) x :=
      (hF i).contDiffAt.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)
    exact (hFd.clm_apply contDiffAt_const).differentiableAt (by norm_num)
  have hsecond := fderiv_fun_sum (fun i hi => hD i hi)
  have happly :
      fderiv ℝ (fun y => ∑ i ∈ s, fderiv ℝ (F i) y v) x v =
        ∑ i ∈ s, fderiv ℝ (fun y => fderiv ℝ (F i) y v) x v := by
    calc
      _ = (∑ i ∈ s, fderiv ℝ (fun y => fderiv ℝ (F i) y v) x) v :=
        congrArg (fun L : E →L[ℝ] ℝ => L v) hsecond
      _ = _ := by simp
  rw [happly]
  apply Finset.sum_congr rfl
  intro i hi
  have hfirstScalar (y : E) :
      fderiv ℝ (F i) y = (w i) • fderiv ℝ (f i) y := by
    dsimp [F]
    exact fderiv_const_mul ((hf i).differentiable (by norm_num) y) (w i)
  have hdir : (fun y => fderiv ℝ (F i) y v) =
      fun y => w i * fderiv ℝ (f i) y v := by
    funext y
    rw [hfirstScalar y]
    rfl
  rw [hdir]
  have hfd : DifferentiableAt ℝ (fun y => fderiv ℝ (f i) y v) x := by
    have hFd : ContDiffAt ℝ 1 (fderiv ℝ (f i)) x :=
      (hf i).contDiffAt.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)
    exact (hFd.clm_apply contDiffAt_const).differentiableAt (by norm_num)
  rw [fderiv_const_mul hfd (w i)]
  rfl

private theorem aoCir_modelCovarianceTrace_weighted_sum
    {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s : Finset ι) (w : ι → ℝ) (f : ι → E → ℝ)
    (hf : ∀ i, ContDiff ℝ 2 (f i))
    (H : ℕ → E) (hH : Summable (fun j => ‖H j‖ ^ 2)) (x : E) :
    modelCovarianceTrace (fun y => ∑ i ∈ s, w i * f i y) H x =
      ∑ i ∈ s, w i * modelCovarianceTrace (f i) H x := by
  have hsum (i : ι) : Summable (fun j =>
      secondDirectionalDerivative (f i) x (H j)) :=
    ASDExplicitGamma.Inverse.pureFlux_secondDirectionalDerivative_summable
      (f i) (hf i) H hH x
  calc
    _ = ∑' j, ∑ i ∈ s, w i *
        secondDirectionalDerivative (f i) x (H j) := by
      apply tsum_congr
      intro j
      exact aoCir_secondDirectionalDerivative_weighted_sum s w f hf x (H j)
    _ = ∑ i ∈ s, ∑' j, w i *
        secondDirectionalDerivative (f i) x (H j) := by
      exact Summable.tsum_finsetSum (fun i hi => (hsum i).mul_left (w i))
    _ = ∑ i ∈ s, w i * modelCovarianceTrace (f i) H x := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [tsum_mul_left]
      rfl

/-- The actual finite weighted child trace has the first variation prescribed
by the common physical Q3 coordinates.  This is the non-regularized heat
identity used as `hheat1` in the all-real CIR transport. -/
theorem aoCir_weightedSquareTrace_first_variation
    (n : ℤ) (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (frameLabel baseLabel : ℤ) {ι : Type*} (s : Finset ι) (w : ι → ℝ)
    (Q : ι → TriadicCube 2) (j : ι → ℕ)
    (hQ : ∀ a, closure (openCubeSet (Q a)) ⊆ closure (cubeSet (originCube 2 n)))
    (hw : ∀ a ∈ s, 0 ≤ w a) (hsum : ∑ a ∈ s, w a = 1) :
    let K := closure (cubeSet (originCube 2 n))
    let b := q3ModelAmplitude M h (baseLabel + 1)
    let L := q3ModelLength (baseLabel + 1)
    let F := cirSquareResponseFamily s w Q j M frameLabel b L
      (fun a t ω => cirSquareRestrictionCLM (Q a) (hQ a)
        (modelInsertedScalar K baseLabel t ω)) hw hsum
    ContinuousOn (fun t => ∫ ω, cirFamilyTrace F t ω
      ∂(Cutoff.cutoffSampleLaw M).toMeasure) (Icc 0 1) ∧
    ∀ t ∈ Ioo (0 : ℝ) 1,
      HasDerivAt (fun r => ∫ ω, cirFamilyTrace F r ω
        ∂(Cutoff.cutoffSampleLaw M).toMeasure)
        (∫ ω, cirFamilyGenerator F t ω
          ∂(Cutoff.cutoffSampleLaw M).toMeasure) t := by
  intro K b L F
  let σ : ℝ := Annealed.sigmaBar M frameLabel
  let H := fun k => Main.mainCubeH3Value n b L (Main.mainCubeQ3Directions n b L k)
  let Φ := cirWeightedSquareTraceObservable s w Q hQ M.nu σ
  let R (a : ι) : C(K, ℝ) →L[ℝ] ResponseCoefficient (openCubeSet (Q a)) :=
    cirSquareRestrictionCLM (Q a) (hQ a)
  let f (a : ι) : C(K, ℝ) → ℝ := fun x =>
    squareTrace (Q a) M.nu σ (R a x)
  have hσ : 0 < σ := (Annealed.sigmaBar_characterization M frameLabel).1
  have hΦC2 : HasPolynomiallyBoundedC2Derivatives Φ :=
    cirWeightedSquareTraceObservable_hasPolynomiallyBoundedC2Derivatives
      s w Q hQ M.nu σ M.nu_pos hσ
  have hf (a : ι) : ContDiff ℝ 2 (f a) := by
    let s₁ : Finset Unit := Finset.univ
    let w₁ : Unit → ℝ := fun _ => 1
    let Q₁ : Unit → TriadicCube 2 := fun _ => Q a
    let hQ₁ : ∀ u, closure (openCubeSet (Q₁ u)) ⊆ K := fun u => hQ a
    have hsingle := cirWeightedSquareTraceObservable_hasPolynomiallyBoundedC2Derivatives
      s₁ w₁ Q₁ hQ₁ M.nu σ M.nu_pos hσ
    have heq : cirWeightedSquareTraceObservable s₁ w₁ Q₁ hQ₁ M.nu σ = f a := by
      funext x
      simp [cirWeightedSquareTraceObservable, s₁, w₁, Q₁, f, R]
    rw [heq] at hsingle
    exact hsingle.1
  have hRawTrace (a : ι) : ContDiff ℝ 2 (squareTrace (Q a) M.nu σ) := by
    let E (p : Fin 2 × Bool) : ResponseCoefficient (openCubeSet (Q a)) → ℝ :=
      squareLoadEnergy (Q a) M.nu σ M.nu_pos hσ p
    have hE (p : Fin 2 × Bool) : ContDiff ℝ 2 (E p) := by
      simpa only [E, squareLoadEnergy] using
        responseFrameEnergyObservable_contDiff
          (measurableSet_openCubeSet (Q a)) (square_volume_pos (Q a))
          M.nu σ M.nu_pos hσ (orthonormalFrameLoad p.1 (lemmaVLoadSign p.2))
    have hEq : squareTrace (Q a) M.nu σ =
        fun z => (∑ p : Fin 2 × Bool, E p z) - 4 := by
      funext z
      simpa [E, squareLoadEnergy] using
        squareTrace_eq_load_sum (Q a) M.nu σ M.nu_pos hσ z
    have hSum : ContDiff ℝ 2 (fun z => ∑ p : Fin 2 × Bool, E p z) := by
      exact ContDiff.sum (s := Finset.univ) (fun p _ => hE p)
    rw [hEq]
    exact hSum.sub contDiff_const
  have hΦsum : Φ = fun x => ∑ a ∈ s, w a * f a x := by
    funext x
    simp [Φ, cirWeightedSquareTraceObservable, f, R]
  let T : Main.MainCubeH3 n b L →L[ℝ] C(K, ℝ) := Main.mainCubeH3Value n b L
  let v : ℕ → Main.MainCubeH3 n b L := Main.mainCubeQ3Directions n b L
  have hv : Summable (fun k => ‖v k‖ ^ 2) := Main.mainCubeQ3Directions_summable n b L
  have hH : Summable (fun k => ‖H k‖ ^ 2) :=
    @summable_sq_norm_gaussianDirections (Main.MainCubeH3 n b L) C(K, ℝ)
      inferInstance (Main.mainCubeH3InnerProductSpace n b L).toNormedSpace
      inferInstance inferInstance v hv T
  have hCov (x : C(K, ℝ)) :
      modelCovarianceTrace Φ H x =
        ∑ a ∈ s, w a * modelCovarianceTrace
          (squareTrace (Q a) M.nu σ) (squareQ3Directions (Q a) b L) (R a x) := by
    rw [hΦsum]
    rw [aoCir_modelCovarianceTrace_weighted_sum s w f hf H hH x]
    apply Finset.sum_congr rfl
    intro a ha
    have hcomp : modelCovarianceTrace (f a) H x =
        modelCovarianceTrace (squareTrace (Q a) M.nu σ)
          (fun k => R a (H k)) (R a x) := by
      unfold modelCovarianceTrace
      apply tsum_congr
      intro k
      exact aoCir_secondDirectionalDerivative_comp_linear
        (squareTrace (Q a) M.nu σ) (hRawTrace a) (R a) x (H k)
    have hdirs : (fun k => R a (H k)) = squareQ3Directions (Q a) b L := by
      funext k
      exact aoCir_mainCube_restrict_direction n (Q a) b L (hQ a) k
    rw [hcomp, hdirs]
  have hpath (t : ℝ) (ω : Cutoff.CutoffSample 2) :
      cirWeightedSquareTraceObservable s w Q hQ M.nu σ
          (modelInsertedScalar K baseLabel t ω) = cirFamilyTrace F t ω := by
    classical
    simp [F, σ, cirWeightedSquareTraceObservable, cirFamilyTrace,
      cirSquareResponseFamily, cirSquareRestrictionCLM]
  have hmeanEq : (fun t => ∫ ω, cirFamilyTrace F t ω
      ∂(Cutoff.cutoffSampleLaw M).toMeasure) =
      fun t => modelHeatAverage K M baseLabel Φ t := by
    funext t
    unfold modelHeatAverage
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun ω => (hpath t ω).symm
  obtain ⟨ell, hK⟩ := exists_originCube_containing_compact K
    (isBounded_cubeSet (originCube 2 n)).isCompact_closure
  have hlaw := Main.main_actual_fresh_cube_factor_law n M h hM baseLabel
  have hlaw' : (Cutoff.cutoffSampleLaw M).toMeasure.map
      (fun ω : Cutoff.CutoffSample 2 => shellFieldScalarRestriction K (ω.1 (baseLabel + 1))) =
      standardGaussianInfinitePi.map
        (@gaussianSeriesLimitE (Main.MainCubeH3 n b L) C(K, ℝ)
          inferInstance (Main.mainCubeH3InnerProductSpace n b L) inferInstance inferInstance
          inferInstance inferInstance inferInstance inferInstance inferInstance v hv T) := by
    simpa [K, b, L, T, v, Main.mainCubeQ3Series] using hlaw
  have hbase := @Main.main_c1On_modelHeatAverage_of_realization
    (Main.MainCubeH3 n b L) inferInstance (Main.mainCubeH3InnerProductSpace n b L)
    inferInstance inferInstance inferInstance inferInstance
    K inferInstance M ell baseLabel hK v hv T hlaw' Φ hΦC2
  refine ⟨?_, ?_⟩
  · rw [hmeanEq]
    exact hbase.1.mono Icc_subset_Ici_self
  · intro t ht
    have hder := hbase.2.2.1 t ht.1
    have hderValue : (1 / 2 : ℝ) *
        modelHeatTraceAverage K M baseLabel Φ H t =
        ∫ ω, cirFamilyGenerator F t ω ∂(Cutoff.cutoffSampleLaw M).toMeasure := by
      change (1 / 2 : ℝ) *
          (∫ ω, modelCovarianceTrace Φ H (modelInsertedScalar K baseLabel t ω)
            ∂(Cutoff.cutoffSampleLaw M).toMeasure) = _
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun ω => by
        unfold cirFamilyGenerator
        change (1 / 2 : ℝ) * modelCovarianceTrace Φ H
          (modelInsertedScalar K baseLabel t ω) = cirFamilyGenerator F t ω
        have hc := hCov (modelInsertedScalar K baseLabel t ω)
        rw [hc]
        simp only [F, cirSquareResponseFamily]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a ha
        rw [show R a (modelInsertedScalar K baseLabel t ω) =
          cirSquareRestrictionCLM (Q a) (hQ a)
            (modelInsertedScalar K baseLabel t ω) by rfl]
        ring
    rw [hmeanEq, ← hderValue]
    exact hder

end ASDExplicitGamma.AllOrder
