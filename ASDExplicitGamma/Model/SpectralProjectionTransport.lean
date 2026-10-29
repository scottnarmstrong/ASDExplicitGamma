module

public import ASDExplicitGamma.Model.SpectralRealTransport
public import ASDExplicitGamma.Model.SpectralHelmholtzEnergy

@[expose] public section

open MeasureTheory Homogenization Complex
open Algsuperdiff.Probability.Stationary

namespace ASDExplicitGamma.Model

abbrev Q3StationaryComplexVector (M : Algsuperdiff.Section3.ABKModel 2) :=
  WithLp 2 (Lp ℂ 2 (planarRegLaw M) × Lp ℂ 2 (planarRegLaw M))

theorem q3ComplexifyScalar_norm (M : Algsuperdiff.Section3.ABKModel 2)
    (f : ScalarL2 (planarRegLaw M)) : ‖q3ComplexifyScalar M f‖ = ‖f‖ := by
  have hc := q3ComplexifyScalar_coeFn M f
  apply le_antisymm
  · apply Lp.norm_le_norm_of_ae_le
    filter_upwards [hc] with a ha
    rw [ha, Complex.norm_real]
  · apply Lp.norm_le_norm_of_ae_le
    filter_upwards [hc] with a ha
    rw [ha, Complex.norm_real]

/-- The canonical isometric complexification of a scalar observable. -/
noncomputable def q3ComplexifyScalarIsometry (M : Algsuperdiff.Section3.ABKModel 2) :
    ScalarL2 (planarRegLaw M) →ₗᵢ[ℝ] Lp ℂ 2 (planarRegLaw M) where
  toLinearMap := (q3ComplexifyScalar M).toLinearMap
  norm_map' := q3ComplexifyScalar_norm M

/-- The canonical real vector carrier as a Hilbert pair of scalar coordinates. -/
noncomputable def q3RealVectorCoordinateIsometry (M : Algsuperdiff.Section3.ABKModel 2) :
    VectorL2 2 (planarRegLaw M) →ₗᵢ[ℝ]
      WithLp 2 (ScalarL2 (planarRegLaw M) × ScalarL2 (planarRegLaw M)) where
  toLinearMap := ((WithLp.prodContinuousLinearEquiv 2 ℝ _ _).symm.toContinuousLinearMap.comp
    ((vectorL2Coord 0).prod (vectorL2Coord 1))).toLinearMap
  norm_map' F := by
    change ‖WithLp.toLp 2 (vectorL2Coord 0 F, vectorL2Coord 1 F)‖ = ‖F‖
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [WithLp.prod_norm_sq_eq_of_L2]
    have hn := q3VectorL2_inner_eq_sum_coord M F F
    simp only [Fin.sum_univ_two, real_inner_self_eq_norm_sq] at hn
    exact hn.symm

/-- Isometric embedding of the literal real J4 vector carrier in complex coordinates. -/
noncomputable def q3ComplexVectorEmbedding (M : Algsuperdiff.Section3.ABKModel 2) :
    VectorL2 2 (planarRegLaw M) →ₗᵢ[ℝ] Q3StationaryComplexVector M :=
  (LinearIsometry.withLpProdMap 2 (q3ComplexifyScalarIsometry M) (q3ComplexifyScalarIsometry M)).comp
    (q3RealVectorCoordinateIsometry M)

theorem q3ComplexVectorEmbedding_fst (M : Algsuperdiff.Section3.ABKModel 2)
    (F : VectorL2 2 (planarRegLaw M)) :
    (q3ComplexVectorEmbedding M F).fst = q3ComplexifyScalar M (vectorL2Coord 0 F) := rfl

theorem q3ComplexVectorEmbedding_snd (M : Algsuperdiff.Section3.ABKModel 2)
    (F : VectorL2 2 (planarRegLaw M)) :
    (q3ComplexVectorEmbedding M F).snd = q3ComplexifyScalar M (vectorL2Coord 1 F) := rfl

theorem q3ComplexVectorEmbedding_inner (M : Algsuperdiff.Section3.ABKModel 2)
    (F G : VectorL2 2 (planarRegLaw M)) :
    inner ℂ (q3ComplexVectorEmbedding M F) (q3ComplexVectorEmbedding M G) = (inner ℝ F G : ℂ) := by
  rw [WithLp.prod_inner_apply]
  simp only [WithLp.ofLp_fst, WithLp.ofLp_snd, q3ComplexVectorEmbedding_fst,
    q3ComplexVectorEmbedding_snd, q3ComplexifyScalar_inner]
  rw [q3VectorL2_inner_eq_sum_coord, Fin.sum_univ_two, Complex.ofReal_add]

/-- The vector spectral isometry, applied coordinatewise. -/
noncomputable def q3SpectralVectorInverse (M : Algsuperdiff.Section3.ABKModel 2) (h : ℝ)
    (hM : ASDExplicitGamma.PlanarQ3Gaussian M h) :
    Q3SpectralVector h →ₗᵢ[ℂ] Q3StationaryComplexVector M :=
  LinearIsometry.withLpProdMap 2 (q3SpectralInverse M h hM) (q3SpectralInverse M h hM)

/-- The complex stationary potential space obtained from the actual spectral gradient range. -/
noncomputable def q3StationarySpectralPotentialSubspace
    (M : Algsuperdiff.Section3.ABKModel 2) (h : ℝ)
    (hM : ASDExplicitGamma.PlanarQ3Gaussian M h) : Submodule ℂ (Q3StationaryComplexVector M) :=
  (q3SpectralPotentialSubspace h).map (q3SpectralVectorInverse M h hM).toLinearMap

theorem q3StationarySpectralPotentialSubspace_isClosed
    (M : Algsuperdiff.Section3.ABKModel 2) (h : ℝ)
    (hM : ASDExplicitGamma.PlanarQ3Gaussian M h) :
    IsClosed (q3StationarySpectralPotentialSubspace M h hM : Set (Q3StationaryComplexVector M)) := by
  change IsClosed ((q3SpectralVectorInverse M h hM) '' (q3SpectralPotentialSubspace h : Set _))
  exact (q3SpectralVectorInverse M h hM).isometry.isClosedEmbedding.isClosedMap _
    (Submodule.isClosed_topologicalClosure _)

instance q3StationarySpectralPotentialSubspace_hasOrthogonalProjection
    (M : Algsuperdiff.Section3.ABKModel 2) (h : ℝ)
    (hM : ASDExplicitGamma.PlanarQ3Gaussian M h) :
    (q3StationarySpectralPotentialSubspace M h hM).HasOrthogonalProjection := by
  have hcomplete : CompleteSpace (q3StationarySpectralPotentialSubspace M h hM) :=
    (q3StationarySpectralPotentialSubspace_isClosed M h hM).completeSpace_coe
  infer_instance

/-- Normalize the complex derivative factor when transporting vector gradients. -/
theorem q3SpectralVectorInverse_gradient
    (M : Algsuperdiff.Section3.ABKModel 2) (h : ℝ)
    (hM : ASDExplicitGamma.PlanarQ3Gaussian M h)
    (p : Lp ℂ 2 (q3SpectralGraphMeasure h)) :
    q3SpectralVectorInverse M h hM
      ((((2 * Real.pi : ℝ) : ℂ) * I) • q3SpectralGradientMap h p) =
      WithLp.toLp 2 (q3ComplexGraphGradient M h hM p 0, q3ComplexGraphGradient M h hM p 1) := by
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · change q3SpectralInverse M h hM
      ((((2 * Real.pi : ℝ) : ℂ) * I) • q3SpectralGraphCoordinate h 0 p) =
        q3ComplexGraphGradient M h hM p 0
    exact (q3ComplexGraphGradient_apply M h hM p 0).symm
  · change q3SpectralInverse M h hM
      ((((2 * Real.pi : ℝ) : ℂ) * I) • q3SpectralGraphCoordinate h 1 p) =
        q3ComplexGraphGradient M h hM p 1
    exact (q3ComplexGraphGradient_apply M h hM p 1).symm

theorem q3ComplexVectorEmbedding_gradient_mem
    (M : Algsuperdiff.Section3.ABKModel 2) (h : ℝ)
    (hM : ASDExplicitGamma.PlanarQ3Gaussian M h)
    (F : VectorL2 2 (planarRegLaw M)) (hF : F ∈ q3FirstChaosHorizontalGradientRange M) :
    q3ComplexVectorEmbedding M F ∈ q3StationarySpectralPotentialSubspace M h hM := by
  obtain ⟨φ, hφ, hd⟩ := hF
  have hc : q3ComplexifyVectorCoords M F ∈ q3ComplexGradientRangeOn M (q3ComplexFirstChaos M) :=
    ⟨q3ComplexifyScalar M φ, q3ComplexifyScalar_firstChaos_mem M φ hφ,
      q3Complexify_horizontalGradient M hd⟩
  obtain ⟨p, hp⟩ := q3ComplexGradient_weighted_representation M h hM _ hc
  refine ⟨(((2 * Real.pi : ℝ) : ℂ) * I) • q3SpectralGradientMap h p,
    (q3SpectralPotentialSubspace h).smul_mem _ (Submodule.le_topologicalClosure _ ⟨p, rfl⟩), ?_⟩
  change q3SpectralVectorInverse M h hM
    ((((2 * Real.pi : ℝ) : ℂ) * I) • q3SpectralGradientMap h p) = q3ComplexVectorEmbedding M F
  rw [q3SpectralVectorInverse_gradient]
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · exact congrFun hp 0
  · exact congrFun hp 1

theorem q3ComplexVectorEmbedding_potential_mem
    (M : Algsuperdiff.Section3.ABKModel 2) (h : ℝ)
    (hM : ASDExplicitGamma.PlanarQ3Gaussian M h)
    (F : VectorL2 2 (planarRegLaw M)) (hF : F ∈ q3FirstChaosPotentialSubspace M) :
    q3ComplexVectorEmbedding M F ∈ q3StationarySpectralPotentialSubspace M h hM := by
  let L := (q3StationarySpectralPotentialSubspace M h hM).restrictScalars ℝ
  have hS : q3FirstChaosHorizontalGradientRange M ≤
      L.comap (q3ComplexVectorEmbedding M).toLinearMap := by
    intro G hG
    exact q3ComplexVectorEmbedding_gradient_mem M h hM G hG
  have hclosed : IsClosed (L.comap (q3ComplexVectorEmbedding M).toLinearMap :
      Set (VectorL2 2 (planarRegLaw M))) := by
    change IsClosed ((q3ComplexVectorEmbedding M) ⁻¹'
      (q3StationarySpectralPotentialSubspace M h hM : Set _))
    exact (q3StationarySpectralPotentialSubspace_isClosed M h hM).preimage
      (q3ComplexVectorEmbedding M).continuous
  exact Submodule.topologicalClosure_minimal _ hS hclosed hF

private theorem q3CharacterGradient_realization
    (M : Algsuperdiff.Section3.ABKModel 2) (h : ℝ)
    (hM : ASDExplicitGamma.PlanarQ3Gaussian M h) (x : Q3FrequencyPlane) :
    ∃ G : VectorL2 2 (planarRegLaw M),
      (∃ φ, HasHorizontalGradient φ G) ∧
      q3ComplexVectorEmbedding M G = WithLp.toLp 2
        (q3ComplexGraphGradient M h hM (q3SpectralGraphCharacter h x) 0,
         q3ComplexGraphGradient M h hM (q3SpectralGraphCharacter h x) 1) := by
  obtain ⟨z, rfl⟩ := q3SpectralPoint_surjective x
  let p := q3SpectralGraphCharacter h (q3SpectralPoint z)
  let D := q3ComplexGraphGradient M h hM p
  let φ := q3StreamKoopman M z (q3StreamOriginL2 M)
  have hd (i : Fin 2) : HasDerivAt
      (fun t : ℝ => q3ComplexKoopman M (t • (Pi.single i 1 : Vec 2))
        (q3ComplexifyScalar M φ)) (D i) 0 := by
    have hh := q3ComplexGraphGradient_hasDeriv M h hM p i
    simpa only [p, q3SpectralGraphToBase_character, q3SpectralInverse_character,
      q3ComplexStream] using hh
  let G := q3RealCoordinatesToVector M D
  have hgrad : HasHorizontalGradient φ G := by
    have hh := q3RealPart_horizontalGradient M hd
    rwa [q3RealPart_complexify] at hh
  refine ⟨G, ⟨φ, hgrad⟩, ?_⟩
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · change q3ComplexifyScalar M (vectorL2Coord 0 (q3RealCoordinatesToVector M D)) = D 0
    rw [q3RealCoordinatesToVector_coord]
    exact q3Complexify_realPart_derivative M 0 φ (D 0) (hd 0)
  · change q3ComplexifyScalar M (vectorL2Coord 1 (q3RealCoordinatesToVector M D)) = D 1
    rw [q3RealCoordinatesToVector_coord]
    exact q3Complexify_realPart_derivative M 1 φ (D 1) (hd 1)

/-- Orthogonality to real stationary gradients implies orthogonality to the
complex spectral potential space. The tests are actual real stream gradients. -/
theorem q3ComplexVectorEmbedding_orthogonal
    (M : Algsuperdiff.Section3.ABKModel 2) (h : ℝ)
    (hM : ASDExplicitGamma.PlanarQ3Gaussian M h)
    (R : VectorL2 2 (planarRegLaw M))
    (hR : R ∈ (stationaryPotentialSubspace (μ := planarRegLaw M) (d := 2))ᗮ) :
    q3ComplexVectorEmbedding M R ∈ (q3StationarySpectralPotentialSubspace M h hM)ᗮ := by
  let U := q3SpectralVectorInverse M h hM
  let C := U.toContinuousLinearMap.comp (q3SpectralGradientMap h)
  let H := (Submodule.span ℂ {q3ComplexVectorEmbedding M R})ᗮ
  let S := Submodule.span ℂ (Set.range (q3SpectralGraphCharacter h))
  let c : ℂ := ((2 * Real.pi : ℝ) : ℂ) * I
  have hc : c ≠ 0 := mul_ne_zero
    (Complex.ofReal_ne_zero.mpr (mul_ne_zero (by norm_num) Real.pi_ne_zero)) I_ne_zero
  have hcstar : (starRingEnd ℂ) c ≠ 0 := by
    intro h0
    apply hc
    have hh := congrArg (starRingEnd ℂ) h0
    simpa only [starRingEnd_self_apply, map_zero] using hh
  have hchar (x : Q3FrequencyPlane) : C (q3SpectralGraphCharacter h x) ∈ H := by
    obtain ⟨G, hG, heq⟩ := q3CharacterGradient_realization M h hM x
    have hGR := hR G (Submodule.le_topologicalClosure _ hG)
    have hz := q3ComplexVectorEmbedding_inner M G R
    rw [hGR, Complex.ofReal_zero] at hz
    have he : q3ComplexVectorEmbedding M G =
        U (c • q3SpectralGradientMap h (q3SpectralGraphCharacter h x)) :=
      heq.trans (q3SpectralVectorInverse_gradient M h hM _).symm
    rw [he, map_smul, inner_smul_left] at hz
    apply Submodule.mem_orthogonal_singleton_iff_inner_left.mpr
    exact (mul_eq_zero.mp hz).resolve_left hcstar
  have hS : S ≤ H.comap C.toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨x, rfl⟩
    exact hchar x
  have hclosedC : IsClosed (H.comap C.toLinearMap : Set (Lp ℂ 2 (q3SpectralGraphMeasure h))) := by
    change IsClosed (C ⁻¹' (H : Set _))
    exact (Submodule.isClosed_orthogonal (Submodule.span ℂ {q3ComplexVectorEmbedding M R})).preimage C.continuous
  have hall := Submodule.topologicalClosure_minimal S hS hclosedC
  rw [q3SpectralGraphCharacter_span_dense h] at hall
  have hRange : LinearMap.range (q3SpectralGradientMap h).toLinearMap ≤ H.comap U.toLinearMap := by
    rintro _ ⟨p, rfl⟩
    exact hall Submodule.mem_top
  have hclosedU : IsClosed (H.comap U.toLinearMap : Set (Q3SpectralVector h)) := by
    change IsClosed (U ⁻¹' (H : Set _))
    exact (Submodule.isClosed_orthogonal (Submodule.span ℂ {q3ComplexVectorEmbedding M R})).preimage U.continuous
  have hK := Submodule.topologicalClosure_minimal _ hRange hclosedU
  rw [Submodule.mem_orthogonal]
  rintro _ ⟨f, hf, rfl⟩
  exact Submodule.mem_orthogonal_singleton_iff_inner_left.mp (hK hf)

theorem q3ComplexVectorEmbedding_originForcing
    (M : Algsuperdiff.Section3.ABKModel 2) (h : ℝ)
    (hM : ASDExplicitGamma.PlanarQ3Gaussian M h) :
    q3ComplexVectorEmbedding M (q3OriginForcingL2 M) =
      q3SpectralVectorInverse M h hM (q3SpectralSecondForcing h) := by
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · change q3ComplexifyScalar M (vectorL2Coord 0 (q3OriginForcingL2 M)) =
      q3SpectralInverse M h hM 0
    rw [q3OriginForcingL2_coord0_eq_zero, map_zero, map_zero]
  · change q3ComplexifyScalar M (q3StreamOriginL2 M) =
      q3SpectralInverse M h hM (q3SpectralCharacter h 0)
    have hu := q3SpectralInverse_character M h hM (0 : Vec 2)
    have hz : q3SpectralPoint (0 : Vec 2) = 0 := rfl
    rw [hz, q3ComplexStream, q3StreamKoopman_zero] at hu
    exact hu.symm

/-- The energy of the actual stationary potential projection used by J4. -/
theorem q3OriginPotentialProjection_energy
    (M : Algsuperdiff.Section3.ABKModel 2) (h : ℝ)
    (hM : ASDExplicitGamma.PlanarQ3Gaussian M h) :
    ‖stationaryPotentialProjection (μ := planarRegLaw M) (d := 2) (q3OriginForcingL2 M)‖ ^ 2 =
      h ^ 2 / 2 := by
  let Y := q3OriginForcingL2 M
  let P := stationaryPotentialProjection (μ := planarRegLaw M) (d := 2) Y
  let E := q3ComplexVectorEmbedding M
  let U := q3SpectralVectorInverse M h hM
  let L := q3StationarySpectralPotentialSubspace M h hM
  let X := q3SpectralSecondForcing h
  have hP : P ∈ q3FirstChaosPotentialSubspace M := by
    change stationaryPotentialProjection (μ := planarRegLaw M) (d := 2)
      (q3OriginForcingL2 M) ∈ q3FirstChaosPotentialSubspace M
    rw [q3FirstChaosReduction]
    exact (q3FirstChaosPotentialSubspace M).starProjection_apply_mem _
  have hEP := q3ComplexVectorEmbedding_potential_mem M h hM P hP
  have hER := q3ComplexVectorEmbedding_orthogonal M h hM (Y - P)
    (sub_stationaryPotentialProjection_mem_orthogonal Y)
  have hproj : L.starProjection (E Y) = E P :=
    Submodule.eq_starProjection_of_mem_orthogonal hEP (by
      rw [← E.map_sub]
      exact hER)
  have hforce : E Y = U X := q3ComplexVectorEmbedding_originForcing M h hM
  let instMapped : ((q3SpectralPotentialSubspace h).map U.toLinearMap).HasOrthogonalProjection :=
    q3StationarySpectralPotentialSubspace_hasOrthogonalProjection M h hM
  change ‖P‖ ^ 2 = _
  calc
    ‖P‖ ^ 2 = ‖E P‖ ^ 2 := by rw [E.norm_map]
    _ = ‖L.starProjection (E Y)‖ ^ 2 := by rw [hproj]
    _ = ‖U ((q3SpectralPotentialSubspace h).starProjection X)‖ ^ 2 := by
      rw [hforce]
      change ‖((q3SpectralPotentialSubspace h).map U.toLinearMap).starProjection (U X)‖ ^ 2 = _
      rw [← U.map_starProjection]
    _ = h ^ 2 / 2 := by
      rw [U.norm_map]
      exact q3SpectralSecondForcing_projection_energy h

end ASDExplicitGamma.Model
