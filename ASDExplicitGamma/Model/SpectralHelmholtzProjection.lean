module

public import ASDExplicitGamma.Model.SpectralHelmholtz
public import ASDExplicitGamma.Model.SpectralPointProjection

@[expose] public section

open MeasureTheory Complex

namespace ASDExplicitGamma.Model

/-- The pointwise representative of a spectral vector. -/
noncomputable def q3SpectralVectorValue {h : ℝ} (F : Q3SpectralVector h)
    (ξ : Q3FrequencyPlane) : Q3ComplexPlane := WithLp.toLp 2 (F.fst ξ, F.snd ξ)

/-- The Hilbert product inner product is the integral of the pointwise one. -/
theorem q3SpectralVector_inner (h : ℝ) (F G : Q3SpectralVector h) :
    inner ℂ F G = ∫ ξ, inner ℂ (q3SpectralVectorValue F ξ) (q3SpectralVectorValue G ξ)
      ∂q3SpectralMeasure h := by
  rw [WithLp.prod_inner_apply]
  simp only [WithLp.ofLp_fst, WithLp.ofLp_snd, L2.inner_def]
  rw [← integral_add (L2.integrable_inner F.fst G.fst) (L2.integrable_inner F.snd G.snd)]
  apply integral_congr_ae
  filter_upwards [] with ξ
  simp only [q3SpectralVectorValue, WithLp.prod_inner_apply]

private theorem point_projection_fst (ξ : Q3FrequencyPlane) (X : Q3ComplexPlane) :
    (q3PointHelmholtz ξ X).fst =
      (((ξ.fst : ℂ) * X.fst + (ξ.snd : ℂ) * X.snd) /
        ((ξ.fst ^ 2 + ξ.snd ^ 2 : ℝ) : ℂ)) * (ξ.fst : ℂ) := by
  rw [q3PointHelmholtz_apply, WithLp.smul_fst]
  rfl

private theorem point_projection_snd (ξ : Q3FrequencyPlane) (X : Q3ComplexPlane) :
    (q3PointHelmholtz ξ X).snd =
      (((ξ.fst : ℂ) * X.fst + (ξ.snd : ℂ) * X.snd) /
        ((ξ.fst ^ 2 + ξ.snd ^ 2 : ℝ) : ℂ)) * (ξ.snd : ℂ) := by
  rw [q3PointHelmholtz_apply, WithLp.smul_snd]
  rfl

theorem q3SpectralProjected_fst_memLp (h : ℝ) (F : Q3SpectralVector h) :
    MemLp (fun ξ => (q3PointHelmholtz ξ (q3SpectralVectorValue F ξ)).fst)
      2 (q3SpectralMeasure h) := by
  apply ((Lp.memLp F.fst).norm.add (Lp.memLp F.snd).norm).mono'
  · have h0 := (Lp.memLp F.fst).aestronglyMeasurable.aemeasurable
    have h1 := (Lp.memLp F.snd).aestronglyMeasurable.aemeasurable
    apply AEMeasurable.aestronglyMeasurable
    simp only [point_projection_fst, q3SpectralVectorValue, WithLp.toLp_fst, WithLp.toLp_snd]
    fun_prop
  · exact Filter.Eventually.of_forall fun ξ => q3PointHelmholtz_fst_bound ξ _ _

theorem q3SpectralProjected_snd_memLp (h : ℝ) (F : Q3SpectralVector h) :
    MemLp (fun ξ => (q3PointHelmholtz ξ (q3SpectralVectorValue F ξ)).snd)
      2 (q3SpectralMeasure h) := by
  apply ((Lp.memLp F.fst).norm.add (Lp.memLp F.snd).norm).mono'
  · have h0 := (Lp.memLp F.fst).aestronglyMeasurable.aemeasurable
    have h1 := (Lp.memLp F.snd).aestronglyMeasurable.aemeasurable
    apply AEMeasurable.aestronglyMeasurable
    simp only [point_projection_snd, q3SpectralVectorValue, WithLp.toLp_fst, WithLp.toLp_snd]
    fun_prop
  · exact Filter.Eventually.of_forall fun ξ => q3PointHelmholtz_snd_bound ξ _ _

/-- The fieldwise Helmholtz projection, realized on spectral `L²`. -/
noncomputable def q3HelmholtzProjection (h : ℝ) (F : Q3SpectralVector h) : Q3SpectralVector h :=
  WithLp.toLp 2
    ((q3SpectralProjected_fst_memLp h F).toLp
      (fun ξ => (q3PointHelmholtz ξ (q3SpectralVectorValue F ξ)).fst),
     (q3SpectralProjected_snd_memLp h F).toLp
      (fun ξ => (q3PointHelmholtz ξ (q3SpectralVectorValue F ξ)).snd))

theorem q3HelmholtzProjection_fst_coeFn (h : ℝ) (F : Q3SpectralVector h) :
    ((q3HelmholtzProjection h F).fst : Q3FrequencyPlane → ℂ) =ᵐ[q3SpectralMeasure h]
      fun ξ => (q3PointHelmholtz ξ (q3SpectralVectorValue F ξ)).fst :=
  (q3SpectralProjected_fst_memLp h F).coeFn_toLp

theorem q3HelmholtzProjection_snd_coeFn (h : ℝ) (F : Q3SpectralVector h) :
    ((q3HelmholtzProjection h F).snd : Q3FrequencyPlane → ℂ) =ᵐ[q3SpectralMeasure h]
      fun ξ => (q3PointHelmholtz ξ (q3SpectralVectorValue F ξ)).snd :=
  (q3SpectralProjected_snd_memLp h F).coeFn_toLp

theorem q3HelmholtzProjection_value (h : ℝ) (F : Q3SpectralVector h) :
    (fun ξ => q3SpectralVectorValue (q3HelmholtzProjection h F) ξ) =ᵐ[q3SpectralMeasure h]
      fun ξ => q3PointHelmholtz ξ (q3SpectralVectorValue F ξ) := by
  filter_upwards [q3HelmholtzProjection_fst_coeFn h F, q3HelmholtzProjection_snd_coeFn h F]
    with ξ h0 h1
  apply WithLp.ofLp_injective 2
  exact Prod.ext h0 h1

/-- The multiplier field lies in the closed gradient range. -/
theorem q3HelmholtzProjection_mem (h : ℝ) (F : Q3SpectralVector h) :
    q3HelmholtzProjection h F ∈ q3SpectralPotentialSubspace h := by
  rw [← Submodule.orthogonal_orthogonal (K := q3SpectralPotentialSubspace h), Submodule.mem_orthogonal']
  intro G hG
  have hr := (q3SpectralPotential_orthogonal_iff h G).mp hG
  rw [q3SpectralVector_inner]
  calc
    (∫ ξ, inner ℂ (q3SpectralVectorValue (q3HelmholtzProjection h F) ξ)
        (q3SpectralVectorValue G ξ) ∂q3SpectralMeasure h) =
        ∫ _ : Q3FrequencyPlane, (0 : ℂ) ∂q3SpectralMeasure h := by
      apply integral_congr_ae
      filter_upwards [q3HelmholtzProjection_value h F, hr] with ξ hP hGξ
      rw [hP]
      apply q3PointHelmholtz_inner_perp
      simpa [q3SpectralRadialPairing, q3FrequencyCoordinate, q3SpectralVectorValue] using hGξ
    _ = 0 := integral_zero _ _

/-- The residual is orthogonal to the full closed gradient range. -/
theorem q3HelmholtzProjection_residual_mem (h : ℝ) (F : Q3SpectralVector h) :
    F - q3HelmholtzProjection h F ∈ (q3SpectralPotentialSubspace h)ᗮ := by
  apply (q3SpectralPotential_orthogonal_iff h _).mpr
  filter_upwards [q3HelmholtzProjection_fst_coeFn h F, q3HelmholtzProjection_snd_coeFn h F,
    Lp.coeFn_sub F.fst (q3HelmholtzProjection h F).fst,
    Lp.coeFn_sub F.snd (q3HelmholtzProjection h F).snd] with ξ h0 h1 hs0 hs1
  simp only [Pi.sub_apply] at hs0 hs1
  simp only [q3SpectralRadialPairing, q3FrequencyCoordinate, WithLp.sub_fst,
    WithLp.sub_snd, Pi.zero_apply, ite_true]
  rw [hs0, hs1, h0, h1]
  exact q3PointHelmholtz_residual_perp ξ (q3SpectralVectorValue F ξ)

/-- The stationary spectral potential projection is the pointwise multiplier
`ξ ξᵀ / |ξ|²`. Its value at frequency zero is zero. -/
theorem q3HelmholtzMultiplier (h : ℝ) (F : Q3SpectralVector h) :
    (q3SpectralPotentialSubspace h).starProjection F = q3HelmholtzProjection h F :=
  Submodule.eq_starProjection_of_mem_orthogonal
    (q3HelmholtzProjection_mem h F) (q3HelmholtzProjection_residual_mem h F)

end ASDExplicitGamma.Model
