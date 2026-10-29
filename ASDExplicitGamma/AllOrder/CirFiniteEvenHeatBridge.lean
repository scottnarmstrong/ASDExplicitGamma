/-
Copyright (c) 2026 Scott N. Armstrong. All rights reserved.
-/
module

public import ASDExplicitGamma.AllOrder.CirFamilyHeatData

/-! # P12 heat data for the actual finite-even CIR response family -/

@[expose] public section

open Homogenization MeasureTheory Set Filter
  ASDExplicitGamma.Gaussian ASDExplicitGamma.Main ASDExplicitGamma.Response
  ASDExplicitGamma.Triadic ASDExplicitGamma.Variational
open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open scoped Topology ENNReal

namespace ASDExplicitGamma.AllOrder

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
  have hfirstDir :
      (fun y => fderiv ℝ (fun z => ∑ i ∈ s, F i z) y v) =
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
    _ = ∑ i ∈ s, ∑' j,
        w i * secondDirectionalDerivative (f i) x (H j) := by
      exact Summable.tsum_finsetSum (fun i hi => (hsum i).mul_left (w i))
    _ = ∑ i ∈ s, w i * modelCovarianceTrace (f i) H x := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [tsum_mul_left]
      rfl

private theorem aoCir_fderiv_comp_linear
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : F → ℝ) (hf : ContDiff ℝ 2 f) (L : E →L[ℝ] F) (x v : E) :
    fderiv ℝ (fun y => f (L y)) x v = fderiv ℝ f (L x) (L v) := by
  have hfd : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hcomp := (hfd (L x)).hasFDerivAt.comp x L.hasFDerivAt
  have hcomp' : fderiv ℝ (fun y => f (L y)) x =
      (fderiv ℝ f (L x)).comp L := hcomp.fderiv
  rw [hcomp']
  rfl

private theorem aoCir_weighted_fderiv_sum
    {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s : Finset ι) (w : ι → ℝ) (f : ι → E → ℝ)
    (hf : ∀ i, ContDiff ℝ 2 (f i)) (x v : E) :
    fderiv ℝ (fun y => ∑ i ∈ s, w i * f i y) x v =
      ∑ i ∈ s, w i * fderiv ℝ (f i) x v := by
  let F : ι → E → ℝ := fun i y => w i * f i y
  have hF : ∀ i, ContDiff ℝ 2 (F i) := by
    intro i
    exact contDiff_const.mul (hf i)
  have hD (i : ι) (_hi : i ∈ s) : DifferentiableAt ℝ (F i) x :=
    (hF i).differentiable (by norm_num) x
  have hsum := fderiv_fun_sum (fun i hi => hD i hi)
  have hsumApp := congrArg (fun D : E →L[ℝ] ℝ => D v) hsum
  calc
    _ = fderiv ℝ (fun y => ∑ i ∈ s, F i y) x v := by rfl
    _ = _ := by
      rw [hsumApp]
      simp only [sum_apply]
      apply Finset.sum_congr rfl
      intro i hi
      have hmul : fderiv ℝ (F i) x = (w i) • fderiv ℝ (f i) x := by
        dsimp [F]
        exact fderiv_const_mul ((hf i).differentiable (by norm_num) x) (w i)
      rw [hmul]
      rfl

private theorem aoCir_squareTrace_contDiff
    (Q : TriadicCube 2) (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ) :
    ContDiff ℝ 2 (squareTrace Q ν σ) := by
  let E (p : Fin 2 × Bool) : ResponseCoefficient (openCubeSet Q) → ℝ :=
    squareLoadEnergy Q ν σ hν hσ p
  have hE (p : Fin 2 × Bool) : ContDiff ℝ 2 (E p) := by
    simpa only [E, squareLoadEnergy] using
      responseFrameEnergyObservable_contDiff
        (measurableSet_openCubeSet Q) (square_volume_pos Q)
        ν σ hν hσ (orthonormalFrameLoad p.1 (lemmaVLoadSign p.2))
  have hEq : squareTrace Q ν σ = fun z => (∑ p : Fin 2 × Bool, E p z) - 4 := by
    funext z
    simpa [E, squareLoadEnergy] using
      squareTrace_eq_load_sum Q ν σ hν hσ z
  have hSum : ContDiff ℝ 2 (fun z => ∑ p : Fin 2 × Bool, E p z) :=
    ContDiff.sum (s := Finset.univ) (fun p _ => hE p)
  rw [hEq]
  exact hSum.sub contDiff_const

/-- The regularized heat data from the actual fresh-shell Q3 law is exactly
the data required for the corresponding translated-square CIR family.  Both
the Hessian trace and the common-coordinate square-gradient trace are
identified before the pathwise bounds are applied. -/
theorem aoCir_weightedSquareTrace_shell_family_heat_data
    (n : ℤ) (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (frameLabel baseLabel : ℤ) {ι : Type*} (s : Finset ι) (w : ι → ℝ)
    (Q : ι → TriadicCube 2) (j : ι → ℕ)
    (hQ : ∀ a, closure (openCubeSet (Q a)) ⊆
      closure (cubeSet (originCube 2 n)))
    (hw : ∀ a ∈ s, 0 ≤ w a) (hsum : ∑ a ∈ s, w a = 1)
    {p ε : ℝ} (hp : 1 < p) (hε : 0 < ε) :
    let K := closure (cubeSet (originCube 2 n))
    let b := q3ModelAmplitude M h (baseLabel + 1)
    let L := q3ModelLength (baseLabel + 1)
    let k := fun a τ ω => cirSquareRestrictionCLM (Q a) (hQ a)
      (modelInsertedScalar K baseLabel τ ω)
    let F := cirSquareResponseFamily s w Q j M frameLabel b L k hw hsum
    P12RegularizedHeatData (Cutoff.cutoffSampleLaw M).toMeasure
      (cirFamilyTrace F) (cirFamilyGenerator F) (cirFamilyBracket F) p ε := by
  let K := closure (cubeSet (originCube 2 n))
  let σ : ℝ := Annealed.sigmaBar M frameLabel
  let b := q3ModelAmplitude M h (baseLabel + 1)
  let L := q3ModelLength (baseLabel + 1)
  let H := fun k => Main.mainCubeH3Value n b L (Main.mainCubeQ3Directions n b L k)
  let Φ := cirWeightedSquareTraceObservable s w Q hQ M.nu σ
  let R (a : ι) : C(K, ℝ) →L[ℝ] ResponseCoefficient (openCubeSet (Q a)) :=
    cirSquareRestrictionCLM (Q a) (hQ a)
  let f (a : ι) : C(K, ℝ) → ℝ := fun x => squareTrace (Q a) M.nu σ (R a x)
  let k : (a : ι) → ℝ → Cutoff.CutoffSample 2 →
      ResponseCoefficient (openCubeSet (Q a)) := fun a τ ω =>
    R a (modelInsertedScalar K baseLabel τ ω)
  let F := cirSquareResponseFamily s w Q j M frameLabel b L k hw hsum
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  change P12RegularizedHeatData μ
    (cirFamilyTrace F) (cirFamilyGenerator F) (cirFamilyBracket F) p ε
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
  have hΦsum : Φ = fun x => ∑ a ∈ s, w a * f a x := by
    funext x
    simp [Φ, cirWeightedSquareTraceObservable, f, R]
  have hRawTrace (a : ι) : ContDiff ℝ 2 (squareTrace (Q a) M.nu σ) :=
    aoCir_squareTrace_contDiff (Q a) M.nu σ M.nu_pos hσ
  have hPath (t : ℝ) (ω : Cutoff.CutoffSample 2) :
      p12ModelObservablePath K baseLabel Φ t ω = cirFamilyTrace F t ω := by
    classical
    simp [p12ModelObservablePath, Φ, F, σ, cirWeightedSquareTraceObservable,
      cirFamilyTrace, cirSquareResponseFamily, cirSquareRestrictionCLM, k, R]
  have hCov (x : C(K, ℝ)) :
      modelCovarianceTrace Φ H x =
        ∑ a ∈ s, w a * modelCovarianceTrace
          (squareTrace (Q a) M.nu σ)
          (squareQ3Directions (Q a) b L) (R a x) := by
    rw [hΦsum]
    let T : Main.MainCubeH3 n b L →L[ℝ] C(K, ℝ) := Main.mainCubeH3Value n b L
    let v : ℕ → Main.MainCubeH3 n b L := Main.mainCubeQ3Directions n b L
    have hv : Summable (fun q => ‖v q‖ ^ 2) := Main.mainCubeQ3Directions_summable n b L
    have hH : Summable (fun q => ‖H q‖ ^ 2) :=
      @summable_sq_norm_gaussianDirections (Main.MainCubeH3 n b L) C(K, ℝ)
        inferInstance (Main.mainCubeH3InnerProductSpace n b L).toNormedSpace
        inferInstance inferInstance v hv T
    rw [aoCir_modelCovarianceTrace_weighted_sum s w f hf H
      hH x]
    apply Finset.sum_congr rfl
    intro a ha
    have hcomp : modelCovarianceTrace (f a) H x =
        modelCovarianceTrace (squareTrace (Q a) M.nu σ)
          (fun k => R a (H k)) (R a x) := by
      unfold modelCovarianceTrace
      apply tsum_congr
      intro k₀
      exact aoCir_secondDirectionalDerivative_comp_linear
        (squareTrace (Q a) M.nu σ) (hRawTrace a) (R a) x (H k₀)
    have hdirs : (fun k₀ => R a (H k₀)) =
        squareQ3Directions (Q a) b L := by
      funext k₀
      exact aoCir_mainCube_restrict_direction n (Q a) b L (hQ a) k₀
    rw [hcomp, hdirs]
  have hGenerator (t : ℝ) (ω : Cutoff.CutoffSample 2) :
      p12ModelGeneratorPath K baseLabel Φ H t ω = cirFamilyGenerator F t ω := by
    change (1 / 2 : ℝ) * modelCovarianceTrace Φ H
        (modelInsertedScalar K baseLabel t ω) = _
    rw [hCov]
    change (1 / 2 : ℝ) *
        (∑ a ∈ s, w a * modelCovarianceTrace
          (squareTrace (Q a) M.nu σ)
          (squareQ3Directions (Q a) b L)
          (R a (modelInsertedScalar K baseLabel t ω))) =
      ∑ a ∈ s, w a * ((1 / 2 : ℝ) *
        modelCovarianceTrace (squareTrace (Q a) M.nu σ)
          (squareQ3Directions (Q a) b L)
          (R a (modelInsertedScalar K baseLabel t ω))
      )
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    ring
  have hDerivative (t : ℝ) (ω : Cutoff.CutoffSample 2) (q : ℕ) :
      fderiv ℝ Φ (modelInsertedScalar K baseLabel t ω) (H q) =
        cirFamilyDerivative F t ω q := by
    rw [hΦsum, aoCir_weighted_fderiv_sum s w f hf
      (modelInsertedScalar K baseLabel t ω) (H q)]
    unfold cirFamilyDerivative
    apply Finset.sum_congr rfl
    intro a ha
    have hcomp := aoCir_fderiv_comp_linear (squareTrace (Q a) M.nu σ)
      (hRawTrace a) (R a) (modelInsertedScalar K baseLabel t ω) (H q)
    have hdir : R a (H q) = squareQ3Directions (Q a) b L q := by
      exact aoCir_mainCube_restrict_direction n (Q a) b L (hQ a) q
    rw [hcomp, hdir]
    rfl
  have hBracket (t : ℝ) (ω : Cutoff.CutoffSample 2) :
      p12ModelBracketPath K baseLabel Φ H t ω = cirFamilyBracket F t ω := by
    change modelGradientSquareTrace Φ H (modelInsertedScalar K baseLabel t ω) = _
    unfold modelGradientSquareTrace cirFamilyBracket
    apply tsum_congr
    intro q
    rw [hDerivative]
  have hdata := aoCir_weightedSquareTrace_shell_heat_data n M h hM
    frameLabel baseLabel s w Q hQ hw hp hε
  have hMomentFun :
      (fun t => ∫ ω, (p12ModelObservablePath K baseLabel Φ t ω + ε) ^ p ∂μ) =
        (fun t => ∫ ω, (cirFamilyTrace F t ω + ε) ^ p ∂μ) := by
    funext t
    apply integral_congr_ae
    exact ae_of_all _ fun ω =>
      congrArg (fun z : ℝ => (z + ε) ^ p) (hPath t ω)
  have hHeatIntegrand (t : ℝ) :
      (fun ω => p * (p12ModelObservablePath K baseLabel Φ t ω + ε) ^ (p - 1) *
          p12ModelGeneratorPath K baseLabel Φ H t ω +
        (p * (p - 1) / 2) *
          (p12ModelObservablePath K baseLabel Φ t ω + ε) ^ (p - 2) *
          p12ModelBracketPath K baseLabel Φ H t ω) =
        (fun ω => p * (cirFamilyTrace F t ω + ε) ^ (p - 1) *
          cirFamilyGenerator F t ω +
        (p * (p - 1) / 2) *
          (cirFamilyTrace F t ω + ε) ^ (p - 2) *
          cirFamilyBracket F t ω) := by
    funext ω
    rw [hPath, hGenerator, hBracket]
  have hHeatIntegral (t : ℝ) :
      (∫ ω, p * (p12ModelObservablePath K baseLabel Φ t ω + ε) ^ (p - 1) *
            p12ModelGeneratorPath K baseLabel Φ H t ω +
          (p * (p - 1) / 2) *
            (p12ModelObservablePath K baseLabel Φ t ω + ε) ^ (p - 2) *
            p12ModelBracketPath K baseLabel Φ H t ω ∂μ) =
        (∫ ω, p * (cirFamilyTrace F t ω + ε) ^ (p - 1) *
            cirFamilyGenerator F t ω +
          (p * (p - 1) / 2) *
            (cirFamilyTrace F t ω + ε) ^ (p - 2) *
            cirFamilyBracket F t ω ∂μ) := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun ω => congrFun (hHeatIntegrand t) ω
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← hMomentFun]
    exact hdata.moment_continuous
  · intro t ht
    rw [← congrFun hMomentFun t]
    exact hdata.moment_positive t ht
  · intro t ht
    rw [← hMomentFun, ← hHeatIntegral t]
    exact hdata.heat_derivative t ht
  · intro t ht
    rw [← hHeatIntegrand t]
    exact hdata.heat_integrable t ht

end ASDExplicitGamma.AllOrder
