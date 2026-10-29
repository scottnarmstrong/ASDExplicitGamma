module

public import ASDExplicitGamma.Inverse.RawShellMixedShearLoads
public import ASDExplicitGamma.Inverse.RawShellPureFluxRows
public import ASDExplicitGamma.Variational.LemmaVRowEstimate

/-! Source-specific first-variation bounds for the OLD mixed shear loads. -/

@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Variational
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Triadic
noncomputable section

local instance rawTraceMixedShearRowsFiniteMeasure (n : ℤ) :
    IsFiniteMeasure (volumeMeasureOn (openCubeSet (originCube 2 n))) :=
  (isOpenBoundedConvexDomain_openCubeSet (originCube 2 n)).isFiniteMeasure_restrict_volume

private theorem rawTraceMixedShear_volumeAverage_congr_ae {U : Set (Vec 2)}
    {f g : Vec 2 → ℝ} (hfg : f =ᵐ[volumeMeasureOn U] g) :
    volumeAverage U f = volumeAverage U g := by
  unfold volumeAverage
  congr 1
  exact integral_congr_ae hfg

noncomputable def rawTraceMixedShearDefect (n : ℤ) (L : ℝ) :
    C(closure (cubeSet (originCube 2 n)), ℝ) :=
  ⟨fun y => q3CovarianceDefect L (cubeCenter (originCube 2 n)) y.1,
    (q3CovarianceDefect_contDiff L (cubeCenter (originCube 2 n))).continuous.comp
      continuous_subtype_val⟩

private theorem rawTraceMixedShearEnergy_fderiv_comp
    (n : ℤ) (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ) (P : BlockVec 2)
    (x d : C(closure (cubeSet (originCube 2 n)), ℝ)) :
    fderiv ℝ (rawTraceMixedShearEnergy n ν σ hν hσ P) x d =
      fderiv ℝ (responseFrameEnergyObservable
        (measurableSet_openCubeSet (originCube 2 n))
        (volume_openCubeSet_originCube_toReal_pos (d := 2) n)
        ν σ hν hσ P) (pureFluxOpenResponseRestriction n x)
          (pureFluxOpenResponseRestriction n d) := by
  let R := pureFluxOpenResponseRestriction n
  let Φ : ResponseCoefficient (openCubeSet (originCube 2 n)) → ℝ :=
    responseFrameEnergyObservable (measurableSet_openCubeSet (originCube 2 n))
      (volume_openCubeSet_originCube_toReal_pos (d := 2) n) ν σ hν hσ P
  have hΦ : DifferentiableAt ℝ Φ (R x) := by
    exact (responseFrameEnergyObservable_contDiff
      (measurableSet_openCubeSet (originCube 2 n))
      (volume_openCubeSet_originCube_toReal_pos (d := 2) n) ν σ hν hσ P).differentiable
        (by norm_num) |>.differentiableAt
  have hcomp := hΦ.hasFDerivAt.comp x R.hasFDerivAt
  have hderiv : fderiv ℝ (fun y => Φ (R y)) x =
      (fderiv ℝ Φ (R x)).comp R := hcomp.fderiv
  have hfun : rawTraceMixedShearEnergy n ν σ hν hσ P = fun y => Φ (R y) := rfl
  rw [hfun, hderiv]
  rfl

/-- A single orthogonal mixed load has the source `κ_f` derivative bound.
The coefficient direction is the actual q3 covariance defect; the factor
`1/σ` comes from the fixed response-frame normalization. -/
theorem raw_trace_mixed_load_defect_direction_bound_tight
    (n : ℤ) (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ) (j : ℕ)
    {L : ℝ} (hL : 0 < L) (P : BlockVec 2)
    (horth : vecDot P.1 P.2 = 0)
    (x : C(closure (cubeSet (originCube 2 n)), ℝ)) :
    |fderiv ℝ (rawTraceMixedShearEnergy n ν σ hν hσ P) x
        (rawTraceMixedShearDefect n L)| ≤
      (2 * lemmaVH2kn
          (cubeScaleFactor (originCube 2 n) / L)
          (diagMeshRadius (originCube 2 n) j / L) / σ) *
        lemmaVTileHistory (originCube 2 n) j
          (responseFramePlanarCoefficientField ν σ
            (pureFluxOpenResponseRestriction n x)) *
        rawTraceMixedShearEnergy n ν σ hν hσ P x := by
  let Q := originCube 2 n
  let K := closure (cubeSet Q)
  let U := openCubeSet Q
  let R : C(K, ℝ) →L[ℝ] ResponseCoefficient U := pureFluxOpenResponseRestriction n
  let Φ : ResponseCoefficient U → ℝ :=
    responseFrameEnergyObservable (measurableSet_openCubeSet Q)
      (volume_openCubeSet_originCube_toReal_pos (d := 2) n) ν σ hν hσ P
  let d := rawTraceMixedShearDefect n L
  let k := R x
  let a := responseFramePlanarCoefficientField ν σ k
  let B := lemmaVTileHistory Q j a
  let κ := lemmaVH2kn (cubeScaleFactor Q / L) (diagMeshRadius Q j / L)
  have hEll : IsEllipticFieldOn (ν / σ)
      (((ν / σ) ^ 2 + (‖k‖ / σ) ^ 2) / (ν / σ)) U a :=
    lemmaV_frameCoefficient_isEllipticOn (measurableSet_openCubeSet Q) ν σ hν hσ k
  obtain ⟨r, u, v, hmid, hEv, hEu, hderiv⟩ :=
    lemmaV_response_load_pair n ν σ hν hσ k P
  let V := lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) P.1 r
  let η : ℕ → H1Function U := fun l => (q3CovarianceDefectFamily Q L l).value
  let I : H1Function U →ₗ[ℝ] H1Function U := diagInterpolant Q j
  let s : Finset ℕ := {0}
  let c : ℕ → ℝ := fun _ => 1
  let H0 : ResponseCoefficient U := σ • R d
  let H : ℕ → ResponseCoefficient U := fun l => if l = 0 then H0 else 0
  let D : ℕ → ℝ := fun l => fderiv ℝ Φ k (H l)
  have hH2 := raw_trace_q3_covariance_defect_H2_row_tight Q j hL P.1 r s c
  have hres : MemH10 U (V - I V).toFun := by
    simpa [V, I] using diagInterpolant_affine_residual_memH10 Q j P.1 r
  have hη : ∀ l, MemLp (η l) (⊤ : ENNReal) (volume.restrict U) := by
    intro l
    exact (q3CovarianceDefectFamily Q L l).value_memLp_top
  have hDη : ∀ l b, MemLp (fun y => (η l).grad y b) (⊤ : ENNReal)
      (volume.restrict U) := by
    intro l b
    exact (q3CovarianceDefectFamily Q L l).gradient_memLp_top_volume b
  have hlink : ∀ l, (η l).toFun =ᵐ[volume.restrict U]
      fun y => responseCoefficientExtension (H l) y / σ := by
    intro l
    by_cases hl : l = 0
    · subst l
      filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_openCubeSet Q)] with y hy
      rw [show (q3CovarianceDefectFamily Q L 0).value.toFun y =
          q3CovarianceDefect L (cubeCenter Q) y by
            change (q3CovarianceDefectWitness Q L (cubeCenter Q)).value.toFun y = _
            rw [q3CovarianceDefectWitness, PlanarW2Infinity.ofContDiff_value]]
      rw [show responseCoefficientExtension (H 0) y =
          σ * responseCoefficientExtension (R d) y by
            simp [H, H0, responseCoefficientExtension_smul_on, hy]]
      rw [pureFluxOpenResponseRestriction_value n d hy]
      simp [d, hσ.ne']
      rfl
    · filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_openCubeSet Q)] with y hy
      have hleft : (η l).toFun y = 0 := by
        simp [η, q3CovarianceDefectFamily, hl, PlanarW2Infinity.zero]
      have hzero : H l = (0 : ResponseCoefficient U) := by simp [H, hl]
      have hright : responseCoefficientExtension (H l) y / σ = 0 := by
        rw [hzero, responseCoefficientExtension_eq (0 : ResponseCoefficient U) hy]
        simp
      rw [hleft, hright]
  have hUenergyFull : cubeAverage Q (scalarVariationEnergyIntegrand a u) =
      Φ k + 2 * vecDot P.1 P.2 := by
    rw [cubeAverage_eq_integralAverage_openCubeSet]
    exact hEu.symm
  have hVenergyFull : cubeAverage Q
      (scalarVariationEnergyIntegrand (adjointCoeffField a) v) =
      Φ k - 2 * vecDot P.1 P.2 := by
    rw [cubeAverage_eq_integralAverage_openCubeSet]
    exact hEv.symm
  have hUenergy : cubeAverage Q (scalarVariationEnergyIntegrand a u) = Φ k := by
    rw [hUenergyFull, horth]
    ring
  have hVenergy : cubeAverage Q
      (scalarVariationEnergyIntegrand (adjointCoeffField a) v) = Φ k := by
    rw [hVenergyFull, horth]
    ring
  have hEnonneg : 0 ≤ Φ k := by
    have hEu0 : Φ k = volumeAverage U (scalarVariationEnergyIntegrand a u) := by
      simpa [horth] using hEu
    rw [hEu0]
    exact volumeAverage_scalarVariationEnergyIntegrand_nonneg_of_isEllipticFieldOn
      U a hEll u
  have hUweak : lemmaVTiledWeakEnergy Q j u.toH1.grad ≤ B * Φ k := by
    have h := lemmaV_harmonic_tiledWeakEnergy_le Q j hEll u
    rw [hUenergy] at h
    simpa [B, a] using h
  have hVweak : lemmaVTiledWeakEnergy Q j v.toH1.grad ≤ B * Φ k := by
    have h := lemmaV_adjoint_tiledWeakEnergy_le Q j hEll v
    rw [hVenergy] at h
    simpa [B, a] using h
  have hVbound : lemmaVTiledWeakEnergy Q j V.grad ≤ B * Φ k := by
    have h := lemmaV_tiledWeakEnergy_midpoint_le Q j V u.toH1 v.toH1 hmid
    linarith
  have hsumBound : Real.sqrt (lemmaVTiledPositiveEnergy Q j
      (lemmaVRowCombination I η V s c)) ≤
      κ * Real.sqrt (∑ l ∈ s, c l ^ 2) * Real.sqrt (lemmaVTiledWeakEnergy Q j V.grad) := by
    simpa [η, I, V, s, c, κ, lemmaVH2kn] using hH2.2
  have hpos : ∀ R' ∈ descendantsAtDepth Q j, ∀ b,
      Summable (fun m => (Real.sqrt 3) ^ (m + 1) * energy R'
        (cubeIncrement R' (m + 1) (fun y =>
          lemmaVRowCombination I η V s c y b))) := by
    simpa [η, I, V, s, c] using hH2.1
  have hDer : ∀ l, D l = 2 * 1 * volumeAverage U (fun y => vecDot
      ((responseCoefficientExtension (H l) y / σ) •
        matVecMul responsePlanarJ (V.grad y)) (v.toH1.grad y)) := by
    intro l
    by_cases hl : l = 0
    · subst l
      have hz : fderiv ℝ Φ k H0 = 2 * volumeAverage U (fun y =>
          vecDot ((responseCoefficientExtension H0 y / σ) •
            matVecMul responsePlanarJ (V.grad y)) (v.toH1.grad y)) := by
        calc
          _ = 2 * volumeAverage U (fun y =>
              (responseCoefficientExtension H0 y / σ) *
                vecDot (v.toH1.grad y) (matVecMul responsePlanarJ (V.grad y))) :=
              (hderiv H0).1
          _ = _ := by
            congr 1
            congr 1
            funext y
            rw [vecDot_smul_left, vecDot_comm]
      have hvar : fderiv ℝ Φ k H0 = 2 * volumeAverage U (fun y =>
          vecDot ((responseCoefficientExtension H0 y / σ) •
            matVecMul responsePlanarJ (V.grad y)) (v.toH1.grad y)) := by
        exact hz
      dsimp [D, H]
      rw [hvar]
      ring
    · have hextZero : (fun y => responseCoefficientExtension
          (0 : ResponseCoefficient U) y) =ᵐ[volumeMeasureOn U] 0 := by
        filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_openCubeSet Q)] with y hy
        rw [responseCoefficientExtension_eq (0 : ResponseCoefficient U) hy]
        rfl
      have havg : volumeAverage U (fun y => vecDot
          ((responseCoefficientExtension (H l) y / σ) •
            matVecMul responsePlanarJ (V.grad y)) (v.toH1.grad y)) = 0 := by
        have hzero : (fun y => vecDot
            ((responseCoefficientExtension (H l) y / σ) •
              matVecMul responsePlanarJ (V.grad y)) (v.toH1.grad y)) =ᵐ[volumeMeasureOn U]
            fun _ => 0 := by
          filter_upwards [hextZero] with y hy
          have hcoeff : responseCoefficientExtension (H l) y = 0 := by
            simpa [H, hl] using hy
          simp [hcoeff, vecDot]
        calc
          _ = volumeAverage U (fun _ => 0) :=
            rawTraceMixedShear_volumeAverage_congr_ae hzero
          _ = 0 := by simp [volumeAverage]
      rw [havg]
      simp [D, H, hl]
  have hDer' : ∀ l, D l = 2 * 1 * volumeAverage (openCubeSet Q) (fun y => vecDot
      ((responseCoefficientExtension (H l) y / σ) •
        matVecMul responsePlanarJ (V.grad y)) (v.toH1.grad y)) := by
    simpa [U] using hDer
  have hε : |(1 : ℝ)| = 1 := by norm_num
  have hrow := lemmaV_directional_row_bound Q j I η V v.toH1 H σ D
      (1 : ℝ) hε s c κ hres hη hDη hlink hDer' hpos hsumBound
  have hρ : 0 ≤ cubeScaleFactor Q / L :=
    div_nonneg (ASDExplicitGamma.Triadic.cubeScaleFactor_pos' Q).le hL.le
  have hδ : 0 ≤ diagMeshRadius Q j / L :=
    div_nonneg (diagMeshRadius_pos Q j).le hL.le
  have hκ : 0 ≤ κ := by
    have hkn : 0 ≤ lemmaVH2kn (cubeScaleFactor Q / L) (diagMeshRadius Q j / L) := by
      unfold lemmaVH2kn lemmaVH2C1 lemmaVH2C2 lemmaVH2R1
      positivity
    dsimp [κ]
    exact hkn
  have hB : 0 ≤ B := lemmaVTileHistory_nonneg Q j a
  have hweakWnonneg : 0 ≤ lemmaVTiledWeakEnergy Q j v.toH1.grad :=
    lemmaVTiledWeakEnergy_nonneg Q j _
  have hweakVnonneg : 0 ≤ lemmaVTiledWeakEnergy Q j V.grad :=
    lemmaVTiledWeakEnergy_nonneg Q j _
  have hsqrtW : Real.sqrt (lemmaVTiledWeakEnergy Q j v.toH1.grad) ≤
      Real.sqrt (B * Φ k) := Real.sqrt_le_sqrt (by simpa using hVweak)
  have hsqrtV : Real.sqrt (lemmaVTiledWeakEnergy Q j V.grad) ≤
      Real.sqrt (B * Φ k) := Real.sqrt_le_sqrt hVbound
  have hprod : Real.sqrt (lemmaVTiledWeakEnergy Q j v.toH1.grad) *
      Real.sqrt (lemmaVTiledWeakEnergy Q j V.grad) ≤ B * Φ k := by
    calc
      _ ≤ Real.sqrt (B * Φ k) * Real.sqrt (B * Φ k) :=
        mul_le_mul hsqrtW hsqrtV (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = B * Φ k := by
        calc
          _ = Real.sqrt (B * Φ k) ^ 2 := by ring
          _ = B * Φ k := Real.sq_sqrt (mul_nonneg hB hEnonneg)
  have hD0 : |D 0| ≤ 2 * κ *
      (Real.sqrt (lemmaVTiledWeakEnergy Q j v.toH1.grad) *
        Real.sqrt (lemmaVTiledWeakEnergy Q j V.grad)) := by
    simpa [D, H, s, c] using hrow
  have hD0bound : |fderiv ℝ Φ k H0| ≤ 2 * κ * B * Φ k := by
    change |D 0| ≤ 2 * κ * B * Φ k
    calc
      |D 0| ≤ 2 * κ * (B * Φ k) :=
        hD0.trans (mul_le_mul_of_nonneg_left hprod (by positivity))
      _ = 2 * κ * B * Φ k := by ring
  have hcomp := rawTraceMixedShearEnergy_fderiv_comp n ν σ hν hσ P x d
  have hscale : R d = σ⁻¹ • H0 := by
    dsimp [H0]
    rw [smul_smul]
    simp [hσ.ne']
  have hderivScaled :
      fderiv ℝ Φ k (R d) = σ⁻¹ * fderiv ℝ Φ k H0 := by
    rw [hscale, map_smul]
    simp only [smul_eq_mul]
  have hσinv : 0 ≤ σ⁻¹ := (inv_pos.mpr hσ).le
  have hfinal : |fderiv ℝ Φ k (R d)| ≤ σ⁻¹ * (2 * κ * B * Φ k) := by
    rw [hderivScaled, abs_mul, abs_of_nonneg hσinv]
    exact mul_le_mul_of_nonneg_left hD0bound hσinv
  have hcomp' : fderiv ℝ (rawTraceMixedShearEnergy n ν σ hν hσ P) x d =
      fderiv ℝ Φ k (R d) := by
    simpa [Q, U, R, Φ, k, rawTraceMixedShearEnergy] using hcomp
  rw [hcomp']
  change |fderiv ℝ Φ k (R d)| ≤ (2 * κ / σ) * B * Φ k
  calc
    _ ≤ σ⁻¹ * (2 * κ * B * Φ k) := hfinal
    _ = (2 * κ / σ) * B * Φ k := by rw [div_eq_mul_inv]; ring

theorem raw_trace_mixed_load_defect_direction_bound
    (n : ℤ) (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ) (j : ℕ)
    {L : ℝ} (hL : 0 < L) (P : BlockVec 2)
    (horth : vecDot P.1 P.2 = 0)
    (x : C(closure (cubeSet (originCube 2 n)), ℝ)) :
    |fderiv ℝ (rawTraceMixedShearEnergy n ν σ hν hσ P) x
        (rawTraceMixedShearDefect n L)| ≤
      (2 * rawTraceRemainderKappaF
          (cubeScaleFactor (originCube 2 n) / L)
          (diagMeshRadius (originCube 2 n) j / L) / σ) *
        lemmaVTileHistory (originCube 2 n) j
          (responseFramePlanarCoefficientField ν σ
            (pureFluxOpenResponseRestriction n x)) *
        rawTraceMixedShearEnergy n ν σ hν hσ P x := by
  let Q := originCube 2 n
  let K := closure (cubeSet Q)
  let U := openCubeSet Q
  let R : C(K, ℝ) →L[ℝ] ResponseCoefficient U := pureFluxOpenResponseRestriction n
  let Φ : ResponseCoefficient U → ℝ :=
    responseFrameEnergyObservable (measurableSet_openCubeSet Q)
      (volume_openCubeSet_originCube_toReal_pos (d := 2) n) ν σ hν hσ P
  let d := rawTraceMixedShearDefect n L
  let k := R x
  let a := responseFramePlanarCoefficientField ν σ k
  let B := lemmaVTileHistory Q j a
  let κ := rawTraceRemainderKappaF (cubeScaleFactor Q / L) (diagMeshRadius Q j / L)
  have hEll : IsEllipticFieldOn (ν / σ)
      (((ν / σ) ^ 2 + (‖k‖ / σ) ^ 2) / (ν / σ)) U a :=
    lemmaV_frameCoefficient_isEllipticOn (measurableSet_openCubeSet Q) ν σ hν hσ k
  obtain ⟨r, u, v, hmid, hEv, hEu, hderiv⟩ :=
    lemmaV_response_load_pair n ν σ hν hσ k P
  let V := lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) P.1 r
  let η : ℕ → H1Function U := fun l => (q3CovarianceDefectFamily Q L l).value
  let I : H1Function U →ₗ[ℝ] H1Function U := diagInterpolant Q j
  let s : Finset ℕ := {0}
  let c : ℕ → ℝ := fun _ => 1
  let H0 : ResponseCoefficient U := σ • R d
  let H : ℕ → ResponseCoefficient U := fun l => if l = 0 then H0 else 0
  let D : ℕ → ℝ := fun l => fderiv ℝ Φ k (H l)
  have hH2 := raw_trace_q3_covariance_defect_H2_row Q j hL P.1 r s c
  have hres : MemH10 U (V - I V).toFun := by
    simpa [V, I] using diagInterpolant_affine_residual_memH10 Q j P.1 r
  have hη : ∀ l, MemLp (η l) (⊤ : ENNReal) (volume.restrict U) := by
    intro l
    exact (q3CovarianceDefectFamily Q L l).value_memLp_top
  have hDη : ∀ l b, MemLp (fun y => (η l).grad y b) (⊤ : ENNReal)
      (volume.restrict U) := by
    intro l b
    exact (q3CovarianceDefectFamily Q L l).gradient_memLp_top_volume b
  have hlink : ∀ l, (η l).toFun =ᵐ[volume.restrict U]
      fun y => responseCoefficientExtension (H l) y / σ := by
    intro l
    by_cases hl : l = 0
    · subst l
      filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_openCubeSet Q)] with y hy
      rw [show (q3CovarianceDefectFamily Q L 0).value.toFun y =
          q3CovarianceDefect L (cubeCenter Q) y by
            change (q3CovarianceDefectWitness Q L (cubeCenter Q)).value.toFun y = _
            rw [q3CovarianceDefectWitness, PlanarW2Infinity.ofContDiff_value]]
      rw [show responseCoefficientExtension (H 0) y =
          σ * responseCoefficientExtension (R d) y by
            simp [H, H0, responseCoefficientExtension_smul_on, hy]]
      rw [pureFluxOpenResponseRestriction_value n d hy]
      simp [d, hσ.ne']
      rfl
    · filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_openCubeSet Q)] with y hy
      have hleft : (η l).toFun y = 0 := by
        simp [η, q3CovarianceDefectFamily, hl, PlanarW2Infinity.zero]
      have hzero : H l = (0 : ResponseCoefficient U) := by simp [H, hl]
      have hright : responseCoefficientExtension (H l) y / σ = 0 := by
        rw [hzero, responseCoefficientExtension_eq (0 : ResponseCoefficient U) hy]
        simp
      rw [hleft, hright]
  have hUenergyFull : cubeAverage Q (scalarVariationEnergyIntegrand a u) =
      Φ k + 2 * vecDot P.1 P.2 := by
    rw [cubeAverage_eq_integralAverage_openCubeSet]
    exact hEu.symm
  have hVenergyFull : cubeAverage Q
      (scalarVariationEnergyIntegrand (adjointCoeffField a) v) =
      Φ k - 2 * vecDot P.1 P.2 := by
    rw [cubeAverage_eq_integralAverage_openCubeSet]
    exact hEv.symm
  have hUenergy : cubeAverage Q (scalarVariationEnergyIntegrand a u) = Φ k := by
    rw [hUenergyFull, horth]
    ring
  have hVenergy : cubeAverage Q
      (scalarVariationEnergyIntegrand (adjointCoeffField a) v) = Φ k := by
    rw [hVenergyFull, horth]
    ring
  have hEnonneg : 0 ≤ Φ k := by
    have hEu0 : Φ k = volumeAverage U (scalarVariationEnergyIntegrand a u) := by
      simpa [horth] using hEu
    rw [hEu0]
    exact volumeAverage_scalarVariationEnergyIntegrand_nonneg_of_isEllipticFieldOn
      U a hEll u
  have hUweak : lemmaVTiledWeakEnergy Q j u.toH1.grad ≤ B * Φ k := by
    have h := lemmaV_harmonic_tiledWeakEnergy_le Q j hEll u
    rw [hUenergy] at h
    simpa [B, a] using h
  have hVweak : lemmaVTiledWeakEnergy Q j v.toH1.grad ≤ B * Φ k := by
    have h := lemmaV_adjoint_tiledWeakEnergy_le Q j hEll v
    rw [hVenergy] at h
    simpa [B, a] using h
  have hVbound : lemmaVTiledWeakEnergy Q j V.grad ≤ B * Φ k := by
    have h := lemmaV_tiledWeakEnergy_midpoint_le Q j V u.toH1 v.toH1 hmid
    linarith
  have hsumBound : Real.sqrt (lemmaVTiledPositiveEnergy Q j
      (lemmaVRowCombination I η V s c)) ≤
      κ * Real.sqrt (∑ l ∈ s, c l ^ 2) * Real.sqrt (lemmaVTiledWeakEnergy Q j V.grad) := by
    simpa [η, I, V, s, c, κ, rawTraceRemainderKappaF] using hH2.2
  have hpos : ∀ R' ∈ descendantsAtDepth Q j, ∀ b,
      Summable (fun m => (Real.sqrt 3) ^ (m + 1) * energy R'
        (cubeIncrement R' (m + 1) (fun y =>
          lemmaVRowCombination I η V s c y b))) := by
    simpa [η, I, V, s, c] using hH2.1
  have hDer : ∀ l, D l = 2 * 1 * volumeAverage U (fun y => vecDot
      ((responseCoefficientExtension (H l) y / σ) •
        matVecMul responsePlanarJ (V.grad y)) (v.toH1.grad y)) := by
    intro l
    by_cases hl : l = 0
    · subst l
      have hz : fderiv ℝ Φ k H0 = 2 * volumeAverage U (fun y =>
          vecDot ((responseCoefficientExtension H0 y / σ) •
            matVecMul responsePlanarJ (V.grad y)) (v.toH1.grad y)) := by
        calc
          _ = 2 * volumeAverage U (fun y =>
              (responseCoefficientExtension H0 y / σ) *
                vecDot (v.toH1.grad y) (matVecMul responsePlanarJ (V.grad y))) :=
              (hderiv H0).1
          _ = _ := by
            congr 1
            congr 1
            funext y
            rw [vecDot_smul_left, vecDot_comm]
      have hvar : fderiv ℝ Φ k H0 = 2 * volumeAverage U (fun y =>
          vecDot ((responseCoefficientExtension H0 y / σ) •
            matVecMul responsePlanarJ (V.grad y)) (v.toH1.grad y)) := by
        exact hz
      dsimp [D, H]
      rw [hvar]
      ring
    · have hextZero : (fun y => responseCoefficientExtension
          (0 : ResponseCoefficient U) y) =ᵐ[volumeMeasureOn U] 0 := by
        filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_openCubeSet Q)] with y hy
        rw [responseCoefficientExtension_eq (0 : ResponseCoefficient U) hy]
        rfl
      have havg : volumeAverage U (fun y => vecDot
          ((responseCoefficientExtension (H l) y / σ) •
            matVecMul responsePlanarJ (V.grad y)) (v.toH1.grad y)) = 0 := by
        have hzero : (fun y => vecDot
            ((responseCoefficientExtension (H l) y / σ) •
              matVecMul responsePlanarJ (V.grad y)) (v.toH1.grad y)) =ᵐ[volumeMeasureOn U]
            fun _ => 0 := by
          filter_upwards [hextZero] with y hy
          have hcoeff : responseCoefficientExtension (H l) y = 0 := by
            simpa [H, hl] using hy
          simp [hcoeff, vecDot]
        calc
          _ = volumeAverage U (fun _ => 0) :=
            rawTraceMixedShear_volumeAverage_congr_ae hzero
          _ = 0 := by simp [volumeAverage]
      rw [havg]
      simp [D, H, hl]
  have hDer' : ∀ l, D l = 2 * 1 * volumeAverage (openCubeSet Q) (fun y => vecDot
      ((responseCoefficientExtension (H l) y / σ) •
        matVecMul responsePlanarJ (V.grad y)) (v.toH1.grad y)) := by
    simpa [U] using hDer
  have hε : |(1 : ℝ)| = 1 := by norm_num
  have hrow := lemmaV_directional_row_bound Q j I η V v.toH1 H σ D
      (1 : ℝ) hε s c κ hres hη hDη hlink hDer' hpos hsumBound
  have hρ : 0 ≤ cubeScaleFactor Q / L :=
    div_nonneg (ASDExplicitGamma.Triadic.cubeScaleFactor_pos' Q).le hL.le
  have hδ : 0 ≤ diagMeshRadius Q j / L :=
    div_nonneg (diagMeshRadius_pos Q j).le hL.le
  have hκ : 0 ≤ κ := by
    have hkn : 0 ≤ lemmaVH2kn (cubeScaleFactor Q / L) (diagMeshRadius Q j / L) := by
      unfold lemmaVH2kn lemmaVH2C1 lemmaVH2C2 lemmaVH2R1
      positivity
    have hcoeff := lemmaVH2kn_le_rawTraceRemainderKappaF hρ hδ
    dsimp [κ]
    exact hkn.trans hcoeff
  have hB : 0 ≤ B := lemmaVTileHistory_nonneg Q j a
  have hweakWnonneg : 0 ≤ lemmaVTiledWeakEnergy Q j v.toH1.grad :=
    lemmaVTiledWeakEnergy_nonneg Q j _
  have hweakVnonneg : 0 ≤ lemmaVTiledWeakEnergy Q j V.grad :=
    lemmaVTiledWeakEnergy_nonneg Q j _
  have hsqrtW : Real.sqrt (lemmaVTiledWeakEnergy Q j v.toH1.grad) ≤
      Real.sqrt (B * Φ k) := Real.sqrt_le_sqrt (by simpa using hVweak)
  have hsqrtV : Real.sqrt (lemmaVTiledWeakEnergy Q j V.grad) ≤
      Real.sqrt (B * Φ k) := Real.sqrt_le_sqrt hVbound
  have hprod : Real.sqrt (lemmaVTiledWeakEnergy Q j v.toH1.grad) *
      Real.sqrt (lemmaVTiledWeakEnergy Q j V.grad) ≤ B * Φ k := by
    calc
      _ ≤ Real.sqrt (B * Φ k) * Real.sqrt (B * Φ k) :=
        mul_le_mul hsqrtW hsqrtV (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = B * Φ k := by
        calc
          _ = Real.sqrt (B * Φ k) ^ 2 := by ring
          _ = B * Φ k := Real.sq_sqrt (mul_nonneg hB hEnonneg)
  have hD0 : |D 0| ≤ 2 * κ *
      (Real.sqrt (lemmaVTiledWeakEnergy Q j v.toH1.grad) *
        Real.sqrt (lemmaVTiledWeakEnergy Q j V.grad)) := by
    simpa [D, H, s, c] using hrow
  have hD0bound : |fderiv ℝ Φ k H0| ≤ 2 * κ * B * Φ k := by
    change |D 0| ≤ 2 * κ * B * Φ k
    calc
      |D 0| ≤ 2 * κ * (B * Φ k) :=
        hD0.trans (mul_le_mul_of_nonneg_left hprod (by positivity))
      _ = 2 * κ * B * Φ k := by ring
  have hcomp := rawTraceMixedShearEnergy_fderiv_comp n ν σ hν hσ P x d
  have hscale : R d = σ⁻¹ • H0 := by
    dsimp [H0]
    rw [smul_smul]
    simp [hσ.ne']
  have hderivScaled :
      fderiv ℝ Φ k (R d) = σ⁻¹ * fderiv ℝ Φ k H0 := by
    rw [hscale, map_smul]
    simp only [smul_eq_mul]
  have hσinv : 0 ≤ σ⁻¹ := (inv_pos.mpr hσ).le
  have hfinal : |fderiv ℝ Φ k (R d)| ≤ σ⁻¹ * (2 * κ * B * Φ k) := by
    rw [hderivScaled, abs_mul, abs_of_nonneg hσinv]
    exact mul_le_mul_of_nonneg_left hD0bound hσinv
  have hcomp' : fderiv ℝ (rawTraceMixedShearEnergy n ν σ hν hσ P) x d =
      fderiv ℝ Φ k (R d) := by
    simpa [Q, U, R, Φ, k, rawTraceMixedShearEnergy] using hcomp
  rw [hcomp']
  change |fderiv ℝ Φ k (R d)| ≤ (2 * κ / σ) * B * Φ k
  calc
    _ ≤ σ⁻¹ * (2 * κ * B * Φ k) := hfinal
    _ = (2 * κ / σ) * B * Φ k := by rw [div_eq_mul_inv]; ring

private theorem rawTraceMixedShearEnergy_differentiableAt
    (n : ℤ) (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ) (P : BlockVec 2)
    (x : C(closure (cubeSet (originCube 2 n)), ℝ)) :
    DifferentiableAt ℝ (rawTraceMixedShearEnergy n ν σ hν hσ P) x := by
  let R := pureFluxOpenResponseRestriction n
  let Φ : ResponseCoefficient (openCubeSet (originCube 2 n)) → ℝ :=
    responseFrameEnergyObservable (measurableSet_openCubeSet (originCube 2 n))
      (volume_openCubeSet_originCube_toReal_pos (d := 2) n) ν σ hν hσ P
  have hΦ : DifferentiableAt ℝ Φ (R x) := by
    exact (responseFrameEnergyObservable_contDiff
      (measurableSet_openCubeSet (originCube 2 n))
      (volume_openCubeSet_originCube_toReal_pos (d := 2) n) ν σ hν hσ P).differentiable
        (by norm_num) |>.differentiableAt
  have hcomp := hΦ.hasFDerivAt.comp x R.hasFDerivAt
  change DifferentiableAt ℝ (fun y => Φ (R y)) x
  exact hcomp.differentiableAt

private theorem rawTraceMixedShearLoad_orthogonal (i j : Fin 2) (hij : i ≠ j)
    (b : Bool) :
    vecDot (rawTraceMixedShearLoad i j b).1
      (rawTraceMixedShearLoad i j b).2 = 0 := by
  cases b <;>
    simp [rawTraceMixedShearLoad, vecDot, Pi.single_apply] <;> exact hij.symm

/-- The actual OLD mixed shear coefficient has the source finite-variation
bound. Its four orthogonal load energies sum exactly to `T+4`. -/
theorem raw_trace_model_shear_linear_defect_direction_bound_tight
    (n : ℤ) (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ) (j : ℕ)
    {L : ℝ} (hL : 0 < L)
    (x : C(closure (cubeSet (originCube 2 n)), ℝ)) :
    |fderiv ℝ (rawTraceModelShearLinear n ν) x (rawTraceMixedShearDefect n L)| ≤
      (lemmaVH2kn
        (cubeScaleFactor (originCube 2 n) / L)
        (diagMeshRadius (originCube 2 n) j / L) / σ) *
      lemmaVTileHistory (originCube 2 n) j
        (responseFramePlanarCoefficientField ν σ
          (pureFluxOpenResponseRestriction n x)) *
      (modelTraceObservable n ν σ x + 4) := by
  let Q := originCube 2 n
  let P10p := rawTraceMixedShearLoad 1 0 true
  let P10m := rawTraceMixedShearLoad 1 0 false
  let P01p := rawTraceMixedShearLoad 0 1 true
  let P01m := rawTraceMixedShearLoad 0 1 false
  let E10p := rawTraceMixedShearEnergy n ν σ hν hσ P10p
  let E10m := rawTraceMixedShearEnergy n ν σ hν hσ P10m
  let E01p := rawTraceMixedShearEnergy n ν σ hν hσ P01p
  let E01m := rawTraceMixedShearEnergy n ν σ hν hσ P01m
  let d := rawTraceMixedShearDefect n L
  let B := lemmaVTileHistory Q j
    (responseFramePlanarCoefficientField ν σ (pureFluxOpenResponseRestriction n x))
  let κ := lemmaVH2kn (cubeScaleFactor Q / L) (diagMeshRadius Q j / L)
  let C := (2 * κ / σ) * B
  have hρ : 0 ≤ cubeScaleFactor Q / L :=
    div_nonneg (ASDExplicitGamma.Triadic.cubeScaleFactor_pos' Q).le hL.le
  have hδ : 0 ≤ diagMeshRadius Q j / L :=
    div_nonneg (diagMeshRadius_pos Q j).le hL.le
  have hκ : 0 ≤ κ := by
    have hkn : 0 ≤ lemmaVH2kn (cubeScaleFactor Q / L) (diagMeshRadius Q j / L) := by
      unfold lemmaVH2kn lemmaVH2C1 lemmaVH2C2 lemmaVH2R1
      positivity
    exact hkn
  have hB : 0 ≤ B := lemmaVTileHistory_nonneg Q j _
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have horth10p : vecDot P10p.1 P10p.2 = 0 :=
    rawTraceMixedShearLoad_orthogonal 1 0 (by decide) true
  have horth10m : vecDot P10m.1 P10m.2 = 0 :=
    rawTraceMixedShearLoad_orthogonal 1 0 (by decide) false
  have horth01p : vecDot P01p.1 P01p.2 = 0 :=
    rawTraceMixedShearLoad_orthogonal 0 1 (by decide) true
  have horth01m : vecDot P01m.1 P01m.2 = 0 :=
    rawTraceMixedShearLoad_orthogonal 0 1 (by decide) false
  have hD10p : |fderiv ℝ E10p x d| ≤ C * E10p x := by
    simpa [E10p, d, B, κ, C, Q, rawTraceMixedShearEnergy] using
      (raw_trace_mixed_load_defect_direction_bound_tight n ν σ hν hσ j hL P10p horth10p x)
  have hD10m : |fderiv ℝ E10m x d| ≤ C * E10m x := by
    simpa [E10m, d, B, κ, C, Q, rawTraceMixedShearEnergy] using
      (raw_trace_mixed_load_defect_direction_bound_tight n ν σ hν hσ j hL P10m horth10m x)
  have hD01p : |fderiv ℝ E01p x d| ≤ C * E01p x := by
    simpa [E01p, d, B, κ, C, Q, rawTraceMixedShearEnergy] using
      (raw_trace_mixed_load_defect_direction_bound_tight n ν σ hν hσ j hL P01p horth01p x)
  have hD01m : |fderiv ℝ E01m x d| ≤ C * E01m x := by
    simpa [E01m, d, B, κ, C, Q, rawTraceMixedShearEnergy] using
      (raw_trace_mixed_load_defect_direction_bound_tight n ν σ hν hσ j hL P01m horth01m x)
  have hDiff10p := rawTraceMixedShearEnergy_differentiableAt n ν σ hν hσ P10p x
  have hDiff10m := rawTraceMixedShearEnergy_differentiableAt n ν σ hν hσ P10m x
  have hDiff01p := rawTraceMixedShearEnergy_differentiableAt n ν σ hν hσ P01p x
  have hDiff01m := rawTraceMixedShearEnergy_differentiableAt n ν σ hν hσ P01m x
  have hPolarization : rawTraceModelShearLinear n ν = fun y =>
      ((E10p y - E10m y) - (E01p y - E01m y)) / 2 := by
    funext y
    simpa [E10p, E10m, E01p, E01m, P10p, P10m, P01p, P01m,
      rawTraceMixedShearEnergy] using
      raw_trace_model_shear_linear_eq_mixed_load_energies n ν σ hν hσ y
  let A := fun y => E10p y - E10m y
  let D := fun y => E01p y - E01m y
  have hDiffA : DifferentiableAt ℝ A x := hDiff10p.sub hDiff10m
  have hDiffD : DifferentiableAt ℝ D x := hDiff01p.sub hDiff01m
  have hDiffAD : DifferentiableAt ℝ (fun y => A y - D y) x := hDiffA.sub hDiffD
  have hAD : (fun y => ((E10p y - E10m y) - (E01p y - E01m y)) / 2) =
      fun y => (1 / 2 : ℝ) • (A y - D y) := by
    funext y
    dsimp [A, D]
    ring
  have hDerExpr : fderiv ℝ
      (fun y => ((E10p y - E10m y) - (E01p y - E01m y)) / 2) x =
        (1 / 2 : ℝ) •
          ((fderiv ℝ E10p x - fderiv ℝ E10m x) -
            (fderiv ℝ E01p x - fderiv ℝ E01m x)) := by
    rw [hAD, fderiv_fun_smul (differentiableAt_const (1 / 2 : ℝ)) hDiffAD,
      fderiv_fun_sub hDiffA hDiffD,
      fderiv_fun_sub hDiff10p hDiff10m,
      fderiv_fun_sub hDiff01p hDiff01m]
    simp [A, D, E10p, E10m, E01p, E01m]
  have hDerShear : fderiv ℝ (rawTraceModelShearLinear n ν) x d =
      ((fderiv ℝ E10p x d - fderiv ℝ E10m x d) -
        (fderiv ℝ E01p x d - fderiv ℝ E01m x d)) / 2 := by
    rw [hPolarization]
    have h := congrArg (fun L : C(closure (cubeSet Q), ℝ) →L[ℝ] ℝ => L d) hDerExpr
    have h' : fderiv ℝ (fun y => ((E10p y - E10m y) -
        (E01p y - E01m y)) / 2) x d =
        (1 / 2 : ℝ) * ((fderiv ℝ E10p x - fderiv ℝ E10m x) -
          (fderiv ℝ E01p x - fderiv ℝ E01m x)) d := by
      simpa [smul_eq_mul] using h
    calc
      _ = (1 / 2 : ℝ) *
          ((fderiv ℝ E10p x - fderiv ℝ E10m x) -
            (fderiv ℝ E01p x - fderiv ℝ E01m x)) d := h'
      _ = _ := by simp; ring
  have htriangle : |fderiv ℝ (rawTraceModelShearLinear n ν) x d| ≤
      (|fderiv ℝ E10p x d| + |fderiv ℝ E10m x d| +
        |fderiv ℝ E01p x d| + |fderiv ℝ E01m x d|) / 2 := by
    have hsub (a b : ℝ) : |a - b| ≤ |a| + |b| := by
      simpa [abs_neg] using abs_sub_le a 0 b
    have houter := hsub (fderiv ℝ E10p x d - fderiv ℝ E10m x d)
      (fderiv ℝ E01p x d - fderiv ℝ E01m x d)
    have h10 := hsub (fderiv ℝ E10p x d) (fderiv ℝ E10m x d)
    have h01 := hsub (fderiv ℝ E01p x d) (fderiv ℝ E01m x d)
    have htotalAbs :
        |(fderiv ℝ E10p x d - fderiv ℝ E10m x d) -
          (fderiv ℝ E01p x d - fderiv ℝ E01m x d)| ≤
        |fderiv ℝ E10p x d| + |fderiv ℝ E10m x d| +
          |fderiv ℝ E01p x d| + |fderiv ℝ E01m x d| := by
      calc
        _ ≤ (|fderiv ℝ E10p x d| + |fderiv ℝ E10m x d|) +
            (|fderiv ℝ E01p x d| + |fderiv ℝ E01m x d|) :=
          houter.trans (add_le_add h10 h01)
        _ = _ := by ring
    calc
      |fderiv ℝ (rawTraceModelShearLinear n ν) x d| =
          |(fderiv ℝ E10p x d - fderiv ℝ E10m x d) -
            (fderiv ℝ E01p x d - fderiv ℝ E01m x d)| / 2 := by
        rw [hDerShear, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      _ ≤ (|fderiv ℝ E10p x d| + |fderiv ℝ E10m x d| +
            |fderiv ℝ E01p x d| + |fderiv ℝ E01m x d|) / 2 :=
        div_le_div_of_nonneg_right htotalAbs (by norm_num)
  have htotal : E10p x + E10m x + E01p x + E01m x =
      modelTraceObservable n ν σ x + 4 := by
    simpa [E10p, E10m, E01p, E01m, P10p, P10m, P01p, P01m] using
      raw_trace_model_mixed_loads_sum_eq_trace_plus_four n ν σ hν hσ x
  calc
    |fderiv ℝ (rawTraceModelShearLinear n ν) x d| ≤
        (|fderiv ℝ E10p x d| + |fderiv ℝ E10m x d| +
          |fderiv ℝ E01p x d| + |fderiv ℝ E01m x d|) / 2 := htriangle
    _ ≤ (C * E10p x + C * E10m x + C * E01p x + C * E01m x) / 2 := by
      nlinarith [hD10p, hD10m, hD01p, hD01m]
    _ = (κ / σ) * B * (modelTraceObservable n ν σ x + 4) := by
      rw [← htotal]
      dsimp [C]
      ring

theorem raw_trace_model_shear_linear_defect_direction_bound
    (n : ℤ) (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ) (j : ℕ)
    {L : ℝ} (hL : 0 < L)
    (x : C(closure (cubeSet (originCube 2 n)), ℝ)) :
    |fderiv ℝ (rawTraceModelShearLinear n ν) x (rawTraceMixedShearDefect n L)| ≤
      (rawTraceRemainderKappaF
        (cubeScaleFactor (originCube 2 n) / L)
        (diagMeshRadius (originCube 2 n) j / L) / σ) *
      lemmaVTileHistory (originCube 2 n) j
        (responseFramePlanarCoefficientField ν σ
          (pureFluxOpenResponseRestriction n x)) *
      (modelTraceObservable n ν σ x + 4) := by
  let Q := originCube 2 n
  let P10p := rawTraceMixedShearLoad 1 0 true
  let P10m := rawTraceMixedShearLoad 1 0 false
  let P01p := rawTraceMixedShearLoad 0 1 true
  let P01m := rawTraceMixedShearLoad 0 1 false
  let E10p := rawTraceMixedShearEnergy n ν σ hν hσ P10p
  let E10m := rawTraceMixedShearEnergy n ν σ hν hσ P10m
  let E01p := rawTraceMixedShearEnergy n ν σ hν hσ P01p
  let E01m := rawTraceMixedShearEnergy n ν σ hν hσ P01m
  let d := rawTraceMixedShearDefect n L
  let B := lemmaVTileHistory Q j
    (responseFramePlanarCoefficientField ν σ (pureFluxOpenResponseRestriction n x))
  let κ := rawTraceRemainderKappaF (cubeScaleFactor Q / L) (diagMeshRadius Q j / L)
  let C := (2 * κ / σ) * B
  have hρ : 0 ≤ cubeScaleFactor Q / L :=
    div_nonneg (ASDExplicitGamma.Triadic.cubeScaleFactor_pos' Q).le hL.le
  have hδ : 0 ≤ diagMeshRadius Q j / L :=
    div_nonneg (diagMeshRadius_pos Q j).le hL.le
  have hκ : 0 ≤ κ := by
    have hkn : 0 ≤ lemmaVH2kn (cubeScaleFactor Q / L) (diagMeshRadius Q j / L) := by
      unfold lemmaVH2kn lemmaVH2C1 lemmaVH2C2 lemmaVH2R1
      positivity
    exact hkn.trans (lemmaVH2kn_le_rawTraceRemainderKappaF hρ hδ)
  have hB : 0 ≤ B := lemmaVTileHistory_nonneg Q j _
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have horth10p : vecDot P10p.1 P10p.2 = 0 :=
    rawTraceMixedShearLoad_orthogonal 1 0 (by decide) true
  have horth10m : vecDot P10m.1 P10m.2 = 0 :=
    rawTraceMixedShearLoad_orthogonal 1 0 (by decide) false
  have horth01p : vecDot P01p.1 P01p.2 = 0 :=
    rawTraceMixedShearLoad_orthogonal 0 1 (by decide) true
  have horth01m : vecDot P01m.1 P01m.2 = 0 :=
    rawTraceMixedShearLoad_orthogonal 0 1 (by decide) false
  have hD10p : |fderiv ℝ E10p x d| ≤ C * E10p x := by
    simpa [E10p, d, B, κ, C, Q, rawTraceMixedShearEnergy] using
      (raw_trace_mixed_load_defect_direction_bound n ν σ hν hσ j hL P10p horth10p x)
  have hD10m : |fderiv ℝ E10m x d| ≤ C * E10m x := by
    simpa [E10m, d, B, κ, C, Q, rawTraceMixedShearEnergy] using
      (raw_trace_mixed_load_defect_direction_bound n ν σ hν hσ j hL P10m horth10m x)
  have hD01p : |fderiv ℝ E01p x d| ≤ C * E01p x := by
    simpa [E01p, d, B, κ, C, Q, rawTraceMixedShearEnergy] using
      (raw_trace_mixed_load_defect_direction_bound n ν σ hν hσ j hL P01p horth01p x)
  have hD01m : |fderiv ℝ E01m x d| ≤ C * E01m x := by
    simpa [E01m, d, B, κ, C, Q, rawTraceMixedShearEnergy] using
      (raw_trace_mixed_load_defect_direction_bound n ν σ hν hσ j hL P01m horth01m x)
  have hDiff10p := rawTraceMixedShearEnergy_differentiableAt n ν σ hν hσ P10p x
  have hDiff10m := rawTraceMixedShearEnergy_differentiableAt n ν σ hν hσ P10m x
  have hDiff01p := rawTraceMixedShearEnergy_differentiableAt n ν σ hν hσ P01p x
  have hDiff01m := rawTraceMixedShearEnergy_differentiableAt n ν σ hν hσ P01m x
  have hPolarization : rawTraceModelShearLinear n ν = fun y =>
      ((E10p y - E10m y) - (E01p y - E01m y)) / 2 := by
    funext y
    simpa [E10p, E10m, E01p, E01m, P10p, P10m, P01p, P01m,
      rawTraceMixedShearEnergy] using
      raw_trace_model_shear_linear_eq_mixed_load_energies n ν σ hν hσ y
  let A := fun y => E10p y - E10m y
  let D := fun y => E01p y - E01m y
  have hDiffA : DifferentiableAt ℝ A x := hDiff10p.sub hDiff10m
  have hDiffD : DifferentiableAt ℝ D x := hDiff01p.sub hDiff01m
  have hDiffAD : DifferentiableAt ℝ (fun y => A y - D y) x := hDiffA.sub hDiffD
  have hAD : (fun y => ((E10p y - E10m y) - (E01p y - E01m y)) / 2) =
      fun y => (1 / 2 : ℝ) • (A y - D y) := by
    funext y
    dsimp [A, D]
    ring
  have hDerExpr : fderiv ℝ
      (fun y => ((E10p y - E10m y) - (E01p y - E01m y)) / 2) x =
        (1 / 2 : ℝ) •
          ((fderiv ℝ E10p x - fderiv ℝ E10m x) -
            (fderiv ℝ E01p x - fderiv ℝ E01m x)) := by
    rw [hAD, fderiv_fun_smul (differentiableAt_const (1 / 2 : ℝ)) hDiffAD,
      fderiv_fun_sub hDiffA hDiffD,
      fderiv_fun_sub hDiff10p hDiff10m,
      fderiv_fun_sub hDiff01p hDiff01m]
    simp [A, D, E10p, E10m, E01p, E01m]
  have hDerShear : fderiv ℝ (rawTraceModelShearLinear n ν) x d =
      ((fderiv ℝ E10p x d - fderiv ℝ E10m x d) -
        (fderiv ℝ E01p x d - fderiv ℝ E01m x d)) / 2 := by
    rw [hPolarization]
    have h := congrArg (fun L : C(closure (cubeSet Q), ℝ) →L[ℝ] ℝ => L d) hDerExpr
    have h' : fderiv ℝ (fun y => ((E10p y - E10m y) -
        (E01p y - E01m y)) / 2) x d =
        (1 / 2 : ℝ) * ((fderiv ℝ E10p x - fderiv ℝ E10m x) -
          (fderiv ℝ E01p x - fderiv ℝ E01m x)) d := by
      simpa [smul_eq_mul] using h
    calc
      _ = (1 / 2 : ℝ) *
          ((fderiv ℝ E10p x - fderiv ℝ E10m x) -
            (fderiv ℝ E01p x - fderiv ℝ E01m x)) d := h'
      _ = _ := by simp; ring
  have htriangle : |fderiv ℝ (rawTraceModelShearLinear n ν) x d| ≤
      (|fderiv ℝ E10p x d| + |fderiv ℝ E10m x d| +
        |fderiv ℝ E01p x d| + |fderiv ℝ E01m x d|) / 2 := by
    have hsub (a b : ℝ) : |a - b| ≤ |a| + |b| := by
      simpa [abs_neg] using abs_sub_le a 0 b
    have houter := hsub (fderiv ℝ E10p x d - fderiv ℝ E10m x d)
      (fderiv ℝ E01p x d - fderiv ℝ E01m x d)
    have h10 := hsub (fderiv ℝ E10p x d) (fderiv ℝ E10m x d)
    have h01 := hsub (fderiv ℝ E01p x d) (fderiv ℝ E01m x d)
    have htotalAbs :
        |(fderiv ℝ E10p x d - fderiv ℝ E10m x d) -
          (fderiv ℝ E01p x d - fderiv ℝ E01m x d)| ≤
        |fderiv ℝ E10p x d| + |fderiv ℝ E10m x d| +
          |fderiv ℝ E01p x d| + |fderiv ℝ E01m x d| := by
      calc
        _ ≤ (|fderiv ℝ E10p x d| + |fderiv ℝ E10m x d|) +
            (|fderiv ℝ E01p x d| + |fderiv ℝ E01m x d|) :=
          houter.trans (add_le_add h10 h01)
        _ = _ := by ring
    calc
      |fderiv ℝ (rawTraceModelShearLinear n ν) x d| =
          |(fderiv ℝ E10p x d - fderiv ℝ E10m x d) -
            (fderiv ℝ E01p x d - fderiv ℝ E01m x d)| / 2 := by
        rw [hDerShear, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      _ ≤ (|fderiv ℝ E10p x d| + |fderiv ℝ E10m x d| +
            |fderiv ℝ E01p x d| + |fderiv ℝ E01m x d|) / 2 :=
        div_le_div_of_nonneg_right htotalAbs (by norm_num)
  have htotal : E10p x + E10m x + E01p x + E01m x =
      modelTraceObservable n ν σ x + 4 := by
    simpa [E10p, E10m, E01p, E01m, P10p, P10m, P01p, P01m] using
      raw_trace_model_mixed_loads_sum_eq_trace_plus_four n ν σ hν hσ x
  calc
    |fderiv ℝ (rawTraceModelShearLinear n ν) x d| ≤
        (|fderiv ℝ E10p x d| + |fderiv ℝ E10m x d| +
          |fderiv ℝ E01p x d| + |fderiv ℝ E01m x d|) / 2 := htriangle
    _ ≤ (C * E10p x + C * E10m x + C * E01p x + C * E01m x) / 2 := by
      nlinarith [hD10p, hD10m, hD01p, hD01m]
    _ = (κ / σ) * B * (modelTraceObservable n ν σ x + 4) := by
      rw [← htotal]
      dsimp [C]
      ring

/-- The actual q3 mixed generator is bounded by the finite-variation `κ_f`
row with exactly the factor `2v`. -/
theorem raw_trace_model_q3_mixed_generator_abs_le_tight
    (n : ℤ) (ν σ b : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (j : ℕ) (L : {l : ℝ // 0 < l})
    (x : C(closure (cubeSet (originCube 2 n)), ℝ)) :
    let K := closure (cubeSet (originCube 2 n))
    let center := pureFluxParentCenter n
    let H := pureFluxMainCubeQ3Directions n b L
    let C : C(K, ℝ) →L[ℝ] (Fin 1 → ℝ) :=
      ContinuousLinearMap.pi fun _ => ContinuousMap.evalCLM ℝ center
    let I : (Fin 1 → ℝ) →L[ℝ] C(K, ℝ) :=
      (ContinuousLinearMap.proj (0 : Fin 1)).smulRight (1 : C(K, ℝ))
    let R := centeringMap center
    let B := fderiv ℝ (fderiv ℝ (modelTraceObservable n ν σ)) x
    |mixedGenerator H C I R B| ≤
      2 * (b ^ 2 / σ ^ 2) *
        lemmaVH2kn (cubeScaleFactor (originCube 2 n) / L.1)
          (diagMeshRadius (originCube 2 n) j / L.1) *
        lemmaVTileHistory (originCube 2 n) j
          (responseFramePlanarCoefficientField ν σ (pureFluxOpenResponseRestriction n x)) *
        (modelTraceObservable n ν σ x + 4) := by
  intro K center H C I R B
  let defect : C(K, ℝ) := ⟨fun y : K => q3CovarianceDefect L.1 center.1 y.1,
    (q3CovarianceDefect_contDiff L.1 center.1).continuous.comp continuous_subtype_val⟩
  have hderiv := raw_trace_model_shear_linear_defect_direction_bound_tight
    n ν σ hν hσ j L.2 x
  have hderiv' : |fderiv ℝ (rawTraceModelShearLinear n ν) x defect| ≤
      (lemmaVH2kn
        (cubeScaleFactor (originCube 2 n) / L.1)
        (diagMeshRadius (originCube 2 n) j / L.1) / σ) *
        lemmaVTileHistory (originCube 2 n) j
          (responseFramePlanarCoefficientField ν σ (pureFluxOpenResponseRestriction n x)) *
        (modelTraceObservable n ν σ x + 4) := by
    have hcenter : center.1 = cubeCenter (originCube 2 n) := rfl
    simpa [defect, rawTraceMixedShearDefect, hcenter] using hderiv
  have hEq : mixedGenerator H C I R B =
      (2 * b ^ 2 / σ) * fderiv ℝ (rawTraceModelShearLinear n ν) x defect := by
    simpa [defect] using
      raw_trace_model_q3_mixed_generator_eq_shear_derivative n ν σ b hν hσ L x
  have hcoef : 0 ≤ 2 * b ^ 2 / σ := by positivity
  rw [hEq, abs_mul, abs_of_nonneg hcoef]
  calc
    (2 * b ^ 2 / σ) * |fderiv ℝ (rawTraceModelShearLinear n ν) x defect| ≤
        (2 * b ^ 2 / σ) *
          ((lemmaVH2kn
            (cubeScaleFactor (originCube 2 n) / L.1)
            (diagMeshRadius (originCube 2 n) j / L.1) / σ) *
            lemmaVTileHistory (originCube 2 n) j
              (responseFramePlanarCoefficientField ν σ
                (pureFluxOpenResponseRestriction n x)) *
            (modelTraceObservable n ν σ x + 4)) :=
      mul_le_mul_of_nonneg_left hderiv' hcoef
    _ = 2 * (b ^ 2 / σ ^ 2) *
          lemmaVH2kn
            (cubeScaleFactor (originCube 2 n) / L.1)
            (diagMeshRadius (originCube 2 n) j / L.1) *
          lemmaVTileHistory (originCube 2 n) j
            (responseFramePlanarCoefficientField ν σ
              (pureFluxOpenResponseRestriction n x)) *
          (modelTraceObservable n ν σ x + 4) := by
      field_simp [hσ.ne']

theorem raw_trace_model_q3_mixed_generator_abs_le
    (n : ℤ) (ν σ b : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (j : ℕ) (L : {l : ℝ // 0 < l})
    (x : C(closure (cubeSet (originCube 2 n)), ℝ)) :
    let K := closure (cubeSet (originCube 2 n))
    let center := pureFluxParentCenter n
    let H := pureFluxMainCubeQ3Directions n b L
    let C : C(K, ℝ) →L[ℝ] (Fin 1 → ℝ) :=
      ContinuousLinearMap.pi fun _ => ContinuousMap.evalCLM ℝ center
    let I : (Fin 1 → ℝ) →L[ℝ] C(K, ℝ) :=
      (ContinuousLinearMap.proj (0 : Fin 1)).smulRight (1 : C(K, ℝ))
    let R := centeringMap center
    let B := fderiv ℝ (fderiv ℝ (modelTraceObservable n ν σ)) x
    |mixedGenerator H C I R B| ≤
      2 * (b ^ 2 / σ ^ 2) *
        rawTraceRemainderKappaF (cubeScaleFactor (originCube 2 n) / L.1)
          (diagMeshRadius (originCube 2 n) j / L.1) *
        lemmaVTileHistory (originCube 2 n) j
          (responseFramePlanarCoefficientField ν σ (pureFluxOpenResponseRestriction n x)) *
        (modelTraceObservable n ν σ x + 4) := by
  intro K center H C I R B
  let defect : C(K, ℝ) := ⟨fun y : K => q3CovarianceDefect L.1 center.1 y.1,
    (q3CovarianceDefect_contDiff L.1 center.1).continuous.comp continuous_subtype_val⟩
  have hderiv := raw_trace_model_shear_linear_defect_direction_bound
    n ν σ hν hσ j L.2 x
  have hderiv' : |fderiv ℝ (rawTraceModelShearLinear n ν) x defect| ≤
      (rawTraceRemainderKappaF
        (cubeScaleFactor (originCube 2 n) / L.1)
        (diagMeshRadius (originCube 2 n) j / L.1) / σ) *
        lemmaVTileHistory (originCube 2 n) j
          (responseFramePlanarCoefficientField ν σ (pureFluxOpenResponseRestriction n x)) *
        (modelTraceObservable n ν σ x + 4) := by
    have hcenter : center.1 = cubeCenter (originCube 2 n) := rfl
    simpa [defect, rawTraceMixedShearDefect, hcenter] using hderiv
  have hEq : mixedGenerator H C I R B =
      (2 * b ^ 2 / σ) * fderiv ℝ (rawTraceModelShearLinear n ν) x defect := by
    simpa [defect] using
      raw_trace_model_q3_mixed_generator_eq_shear_derivative n ν σ b hν hσ L x
  have hcoef : 0 ≤ 2 * b ^ 2 / σ := by positivity
  rw [hEq, abs_mul, abs_of_nonneg hcoef]
  calc
    (2 * b ^ 2 / σ) * |fderiv ℝ (rawTraceModelShearLinear n ν) x defect| ≤
        (2 * b ^ 2 / σ) *
          ((rawTraceRemainderKappaF
            (cubeScaleFactor (originCube 2 n) / L.1)
            (diagMeshRadius (originCube 2 n) j / L.1) / σ) *
            lemmaVTileHistory (originCube 2 n) j
              (responseFramePlanarCoefficientField ν σ
                (pureFluxOpenResponseRestriction n x)) *
            (modelTraceObservable n ν σ x + 4)) :=
      mul_le_mul_of_nonneg_left hderiv' hcoef
    _ = 2 * (b ^ 2 / σ ^ 2) *
          rawTraceRemainderKappaF
            (cubeScaleFactor (originCube 2 n) / L.1)
            (diagMeshRadius (originCube 2 n) j / L.1) *
          lemmaVTileHistory (originCube 2 n) j
            (responseFramePlanarCoefficientField ν σ
              (pureFluxOpenResponseRestriction n x)) *
          (modelTraceObservable n ν σ x + 4) := by
      field_simp [hσ.ne']

end
end ASDExplicitGamma.Inverse
