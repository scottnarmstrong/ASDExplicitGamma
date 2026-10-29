module

public import ASDExplicitGamma.Scalar.Lambda8ProjectionHessian
public import ASDExplicitGamma.Scalar.DirichletDensity
public import ASDExplicitGamma.Scalar.DirichletPolynomial
public import ASDExplicitGamma.Scalar.DirichletSquareHessian

/-! Exact Dirichlet H² regularity and source identification for the local
projection of an actual H¹ vector load. -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open Homogenization MeasureTheory
open Triadic
open scoped BigOperators

private theorem lambda8_rawMeasure_eq_normalized (Q : TriadicCube 2) :
    volume.restrict (openCubeSet Q) =
      ENNReal.ofReal (cubeVolume Q) • normalizedCubeMeasure Q := by
  rw [normalizedCubeMeasure, cubeMeasure, smul_smul]
  have hcoeff : ENNReal.ofReal (cubeVolume Q) *
      ENNReal.ofReal ((cubeVolume Q)⁻¹) = 1 := by
    rw [← ENNReal.ofReal_mul (cubeVolume_pos Q).le]
    rw [mul_inv_cancel₀ (ne_of_gt (cubeVolume_pos Q)), ENNReal.ofReal_one]
  rw [hcoeff, one_smul]
  exact (volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q).symm

private noncomputable def lambda8DirichletModeH10 (Q : TriadicCube 2)
    (q : Fin 2 → ℕ) : H10Function (openCubeSet Q) :=
  dirichletPolynomialH10 Q {q} (fun p => if p = q then 1 else 0)

private theorem lambda8DirichletModeH10_ae (Q : TriadicCube 2)
    (q : Fin 2 → ℕ) :
    (lambda8DirichletModeH10 Q q).toH1Function.toFun =ᵐ[normalizedCubeMeasure Q]
      cubeDirichletMode Q q := by
  have hpoly : dirichletPolynomial Q {q} (fun p => if p = q then 1 else 0) =
      cubeDirichletMode Q q := by
    funext x
    simp [dirichletPolynomial]
  have hraw : (lambda8DirichletModeH10 Q q).toH1Function.toFun =ᵐ[
      volume.restrict (openCubeSet Q)] cubeDirichletMode Q q := by
    simpa only [lambda8DirichletModeH10, hpoly, volumeMeasureOn] using
      dirichlet_polynomial_H10_value Q {q} (fun p => if p = q then 1 else 0)
  have hc : ENNReal.ofReal (cubeVolume Q) ≠ 0 := by
    exact ENNReal.ofReal_ne_zero_iff.mpr (cubeVolume_pos Q)
  rw [lambda8_rawMeasure_eq_normalized] at hraw
  exact (Measure.ae_ennreal_smul_measure_iff hc).mp hraw

private theorem lambda8_weakPoisson_forcing_unique (Q : TriadicCube 2)
    (u : H10Function (openCubeSet Q)) (f g : Vec 2 → ℝ)
    (hf : MemLp f 2 (normalizedCubeMeasure Q))
    (hg : MemLp g 2 (normalizedCubeMeasure Q))
    (hF : CubeDirichletWeakPoissonProblem Q u f)
    (hG : CubeDirichletWeakPoissonProblem Q u g) :
    f =ᵐ[normalizedCubeMeasure Q] g := by
  let fL2 : DirichletL2 Q := hf.toLp f
  let gL2 : DirichletL2 Q := hg.toLp g
  let dL2 : DirichletL2 Q := fL2 - gL2
  have hd : MemLp (fun x => f x - g x) 2 (normalizedCubeMeasure Q) := hf.sub hg
  have hDae : (dL2 : Vec 2 → ℝ) =ᵐ[normalizedCubeMeasure Q]
      (fun x => f x - g x) := by
    filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp,
      Lp.coeFn_sub fL2 gL2] with x hfx hgx hsub
    change (fL2 : Vec 2 → ℝ) x = f x at hfx
    change (gL2 : Vec 2 → ℝ) x = g x at hgx
    have hsub' : (dL2 : Vec 2 → ℝ) x =
        (fL2 : Vec 2 → ℝ) x - (gL2 : Vec 2 → ℝ) x := by
      simpa only [dL2, Pi.sub_apply] using hsub
    calc
      (dL2 : Vec 2 → ℝ) x =
          (fL2 : Vec 2 → ℝ) x - (gL2 : Vec 2 → ℝ) x := hsub'
      _ = f x - g x := by rw [hfx, hgx]
  have hcoeff (q : Fin 2 → ℕ) :
      inner ℝ (dirichletModeL2 Q q) dL2 = 0 := by
    let φ := lambda8DirichletModeH10 Q q
    have hφmem : MemLp φ.toH1Function.toFun 2 (normalizedCubeMeasure Q) :=
      memLp_normalized_of_memL2On φ.toH1Function.memL2
    have hφf : IntegrableOn (fun x => f x * φ.toH1Function x)
        (openCubeSet Q) volume :=
      (memL2On_openCubeSet_of_memLp_normalizedCubeMeasure Q hf).integrable_mul
        φ.toH1Function.memL2
    have hφg : IntegrableOn (fun x => g x * φ.toH1Function x)
        (openCubeSet Q) volume :=
      (memL2On_openCubeSet_of_memLp_normalizedCubeMeasure Q hg).integrable_mul
        φ.toH1Function.memL2
    have hfg :
        (∫ x in openCubeSet Q, f x * φ.toH1Function x ∂volume) =
        ∫ x in openCubeSet Q, g x * φ.toH1Function x ∂volume := by
      calc
        _ = ∫ x in openCubeSet Q,
            vecDot (u.toH1Function.grad x) (φ.toH1Function.grad x) ∂volume :=
              (hF φ).symm
        _ = _ := hG φ
    have hsub :
        ∫ x in openCubeSet Q, (f x - g x) * φ.toH1Function x ∂volume = 0 := by
      calc
        _ = ∫ x in openCubeSet Q,
            f x * φ.toH1Function x - g x * φ.toH1Function x ∂volume := by
              apply integral_congr_ae
              filter_upwards with x
              ring
        _ = (∫ x in openCubeSet Q, f x * φ.toH1Function x ∂volume) -
            ∫ x in openCubeSet Q, g x * φ.toH1Function x ∂volume :=
              integral_sub hφf hφg
        _ = 0 := by rw [hfg]; ring
    have hnormsub :
        ∫ x, (f x - g x) * φ.toH1Function x ∂normalizedCubeMeasure Q = 0 := by
      rw [integral_normalized_eq_open]
      rw [hsub]
      simp
    have hmode : φ.toH1Function.toFun =ᵐ[normalizedCubeMeasure Q]
        cubeDirichletMode Q q := lambda8DirichletModeH10_ae Q q
    have hpair :
        ∫ x, cubeDirichletMode Q q x * (f x - g x)
          ∂normalizedCubeMeasure Q = 0 := by
      have hmodepair :
          (fun x => cubeDirichletMode Q q x * (f x - g x)) =ᵐ[
            normalizedCubeMeasure Q]
          (fun x => φ.toH1Function x * (f x - g x)) := by
        filter_upwards [hmode] with x hx
        rw [hx]
      calc
        _ = ∫ x, φ.toH1Function x * (f x - g x)
            ∂normalizedCubeMeasure Q := integral_congr_ae hmodepair
        _ = ∫ x, (f x - g x) * φ.toH1Function x
            ∂normalizedCubeMeasure Q := by
              apply integral_congr_ae
              filter_upwards with x
              ring
        _ = 0 := hnormsub
    have hinner : inner ℝ (dirichletModeL2 Q q) dL2 =
        ∫ x, cubeDirichletMode Q q x * (f x - g x)
          ∂normalizedCubeMeasure Q := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [(memLp_dirichlet_mode Q q).coeFn_toLp, hDae] with x hq hd'
      change (dirichletModeL2 Q q : Vec 2 → ℝ) x = _ at hq
      change (dL2 : Vec 2 → ℝ) x = _ at hd'
      simp [hq, hd']
      ring
    rw [hinner, hpair]
  have hdorth : dL2 ∈
      (Submodule.span ℝ (Set.range (dirichletModeL2 Q)))ᗮ := by
    apply (Submodule.mem_orthogonal' _ _).2
    intro y hy
    induction hy using Submodule.span_induction with
    | mem z hz =>
        obtain ⟨q, rfl⟩ := hz
        rw [real_inner_comm]
        exact hcoeff q
    | zero => simp
    | add y z hy hz ihy ihz => simp [inner_add_right, ihy, ihz]
    | smul a y hy ih => simp [inner_smul_right, ih]
  have hdzero : dL2 = 0 := by
    rw [dirichlet_sine_span_orthogonal_eq_bot Q] at hdorth
    exact hdorth
  have hzeroFn : (dL2 : Vec 2 → ℝ) =ᵐ[normalizedCubeMeasure Q] 0 := by
    have h := congrArg (fun z : DirichletL2 Q => (z : Vec 2 → ℝ)) hdzero
    filter_upwards [Lp.coeFn_zero ℝ (2 : ENNReal) (normalizedCubeMeasure Q)] with x h0
    have hx := congrFun h x
    rw [h0] at hx
    exact hx
  filter_upwards [hDae, hzeroFn] with x hdx hzero
  have hsubzero : f x - g x = 0 := by
    calc
      f x - g x = (dL2 : Vec 2 → ℝ) x := hdx.symm
      _ = 0 := hzero
  exact sub_eq_zero.mp hsubzero

/-- The actual local projection of an H¹ component load has an H² zero-trace
potential. Its weak Laplacian is exactly the load divergence, and the square
Dirichlet identity gives the exact Frobenius/Laplacian energy equality. -/
theorem lambda8DirichletProjection_hessian_source (Q : TriadicCube 2)
    (F : Fin 2 → H1Function (openCubeSet Q)) :
    ∃ u : H10Function (openCubeSet Q),
      ∃ H : HasWeakHessianOn (openCubeSet Q) u.toH1Function,
        lambda8DirichletProjection (isOpenBoundedConvexDomain_openCubeSet Q)
          (toHilbertVectorL2OfVecField (lambda8H1ComponentField_memVectorL2 F)) =
            u.toH1Function.gradToHilbertVectorL2 ∧
        dirichletWeakLaplacian H =ᵐ[normalizedCubeMeasure Q]
          lambda8H1ComponentDivergence F ∧
        H.frobeniusNormalizedL2 Q =
          cubeLpNorm Q 2 (dirichletWeakLaplacian H) := by
  obtain ⟨u, hu, hweak⟩ := lambda8DirichletProjection_poisson Q F
  let f : Vec 2 → ℝ := fun x => -lambda8H1ComponentDivergence F x
  have hf : MemLp f 2 (normalizedCubeMeasure Q) := by
    exact (lambda8H1ComponentDivergence_memLp Q F).neg
  obtain ⟨H, _hbound⟩ :=
    (CubeDirichletWeakPoissonProblem.cubeDirichletH2RegularityExact Q).2
      u f hf (by simpa only [f] using hweak)
  have hweakH := dirichlet_weak_poisson_of_hessian Q u H
  have hunique := lambda8_weakPoisson_forcing_unique Q u f
    (fun x => -dirichletWeakLaplacian H x) hf
    (memLp_dirichlet_weak_laplacian H).neg
    (by simpa only [f] using hweak) hweakH
  have htrace : dirichletWeakLaplacian H =ᵐ[normalizedCubeMeasure Q]
      lambda8H1ComponentDivergence F := by
    filter_upwards [hunique] with x hx
    dsimp [f, dirichletWeakLaplacian] at hx ⊢
    linarith
  exact ⟨u, H, hu, htrace, dirichlet_square_hessian_identity Q u H⟩

end ASDExplicitGamma.Scalar
