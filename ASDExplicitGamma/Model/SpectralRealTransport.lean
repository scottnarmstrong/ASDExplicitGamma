module

public import ASDExplicitGamma.Model.SpectralComplexCore
public import ASDExplicitGamma.Model.SpectralGradientCore

@[expose] public section

open MeasureTheory Homogenization Complex
open Algsuperdiff.Probability.Stationary

namespace ASDExplicitGamma.Model

/-- Real part on stationary scalar `L²`. -/
noncomputable def q3RealPart (M : Algsuperdiff.Section3.ABKModel 2) :
    Lp ℂ 2 (planarRegLaw M) →L[ℝ] ScalarL2 (planarRegLaw M) :=
  Complex.reCLM.compLpL 2 (planarRegLaw M)

theorem q3RealPart_coeFn (M : Algsuperdiff.Section3.ABKModel 2)
    (f : Lp ℂ 2 (planarRegLaw M)) :
    (q3RealPart M f : RegCoeffField 2 → ℝ) =ᵐ[planarRegLaw M] fun a => (f a).re := by
  simpa only [q3RealPart, Complex.reCLM_apply] using Complex.reCLM.coeFn_compLpL f

theorem q3ComplexifyScalar_coeFn (M : Algsuperdiff.Section3.ABKModel 2)
    (f : ScalarL2 (planarRegLaw M)) :
    (q3ComplexifyScalar M f : RegCoeffField 2 → ℂ) =ᵐ[planarRegLaw M]
      fun a => (f a : ℂ) := by
  simpa only [q3ComplexifyScalar, Complex.ofRealCLM_apply] using Complex.ofRealCLM.coeFn_compLpL f

theorem q3RealPart_complexify (M : Algsuperdiff.Section3.ABKModel 2)
    (f : ScalarL2 (planarRegLaw M)) : q3RealPart M (q3ComplexifyScalar M f) = f := by
  apply Lp.ext
  filter_upwards [q3RealPart_coeFn M (q3ComplexifyScalar M f),
    q3ComplexifyScalar_coeFn M f] with a hr hc
  rw [hr, hc, Complex.ofReal_re]

private theorem q3RealPart_smul_stream (M : Algsuperdiff.Section3.ABKModel 2)
    (c : ℂ) (x : Vec 2) :
    q3RealPart M (c • q3ComplexStream M x) =
      c.re • q3StreamKoopman M x (q3StreamOriginL2 M) := by
  apply Lp.ext
  filter_upwards [q3RealPart_coeFn M (c • q3ComplexStream M x),
    Lp.coeFn_smul c (q3ComplexStream M x), q3ComplexStream_coeFn M x,
    Lp.coeFn_smul c.re (q3StreamKoopman M x (q3StreamOriginL2 M)),
    q3StreamKoopman_apply M x] with a hr hs hc hrs he
  simp only [Pi.smul_apply] at hs hrs
  rw [hr, hs, hrs, he, hc]
  simp only [smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero]

theorem q3RealPart_complexSpan_mem (M : Algsuperdiff.Section3.ABKModel 2)
    (f : Lp ℂ 2 (planarRegLaw M))
    (hf : f ∈ Submodule.span ℂ (Set.range (q3ComplexStream M))) :
    q3RealPart M f ∈ q3StreamOrbitSpan M := by
  classical
  rw [← Finsupp.range_linearCombination ℂ] at hf
  obtain ⟨c, rfl⟩ := hf
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, q3RealPart_smul_stream]
  apply Submodule.sum_mem
  intro x _
  exact (q3StreamOrbitSpan M).smul_mem _ (Submodule.subset_span (Set.mem_range_self x))

theorem q3ComplexifyScalar_firstChaos_mem (M : Algsuperdiff.Section3.ABKModel 2)
    (φ : ScalarL2 (planarRegLaw M)) (hφ : φ ∈ q3StreamFirstChaos M) :
    q3ComplexifyScalar M φ ∈ q3ComplexFirstChaos M := by
  let K := (q3ComplexFirstChaos M).restrictScalars ℝ
  have hS : q3StreamOrbitSpan M ≤ K.comap (q3ComplexifyScalar M).toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨x, rfl⟩
    exact Submodule.le_topologicalClosure _ (Submodule.subset_span (Set.mem_range_self x))
  have hclosed : IsClosed (K.comap (q3ComplexifyScalar M).toLinearMap :
      Set (ScalarL2 (planarRegLaw M))) := by
    change IsClosed ((q3ComplexifyScalar M) ⁻¹' (q3ComplexFirstChaos M : Set _))
    exact (Submodule.isClosed_topologicalClosure _).preimage (q3ComplexifyScalar M).continuous
  exact Submodule.topologicalClosure_minimal (q3StreamOrbitSpan M) hS hclosed hφ

theorem q3StreamKoopman_coeFn (M : Algsuperdiff.Section3.ABKModel 2)
    (z : Vec 2) (f : ScalarL2 (planarRegLaw M)) :
    (q3StreamKoopman M z f : RegCoeffField 2 → ℝ) =ᵐ[planarRegLaw M]
      fun a => f (z +ᵥ a) := by
  have hc := Lp.coeFn_compMeasurePreserving f
    (measurePreserving_const_vadd (μ := planarRegLaw M) z)
  simpa [q3StreamKoopman, koopman, Function.comp_def,
    Algsuperdiff.Frozen.Assumptions.ShellField.regCoeffFieldAddAction] using hc

theorem q3ComplexKoopman_coeFn (M : Algsuperdiff.Section3.ABKModel 2)
    (z : Vec 2) (f : Lp ℂ 2 (planarRegLaw M)) :
    (q3ComplexKoopman M z f : RegCoeffField 2 → ℂ) =ᵐ[planarRegLaw M]
      fun a => f (z +ᵥ a) :=
  Lp.coeFn_compMeasurePreserving f (measurePreserving_const_vadd (μ := planarRegLaw M) z)

theorem q3RealPart_koopman (M : Algsuperdiff.Section3.ABKModel 2)
    (z : Vec 2) (f : Lp ℂ 2 (planarRegLaw M)) :
    q3RealPart M (q3ComplexKoopman M z f) = q3StreamKoopman M z (q3RealPart M f) := by
  let mp := measurePreserving_const_vadd (μ := planarRegLaw M) z
  apply Lp.ext
  filter_upwards [q3RealPart_coeFn M (q3ComplexKoopman M z f),
    q3ComplexKoopman_coeFn M z f, q3StreamKoopman_coeFn M z (q3RealPart M f),
    mp.quasiMeasurePreserving.ae_eq_comp (q3RealPart_coeFn M f)] with a hr hc hs ht
  rw [hr, hc, hs]
  exact ht.symm

theorem q3ComplexifyScalar_koopman (M : Algsuperdiff.Section3.ABKModel 2)
    (z : Vec 2) (f : ScalarL2 (planarRegLaw M)) :
    q3ComplexifyScalar M (q3StreamKoopman M z f) =
      q3ComplexKoopman M z (q3ComplexifyScalar M f) := by
  let mp := measurePreserving_const_vadd (μ := planarRegLaw M) z
  apply Lp.ext
  filter_upwards [q3ComplexifyScalar_coeFn M (q3StreamKoopman M z f),
    q3StreamKoopman_coeFn M z f, q3ComplexKoopman_coeFn M z (q3ComplexifyScalar M f),
    mp.quasiMeasurePreserving.ae_eq_comp (q3ComplexifyScalar_coeFn M f)] with a hc hs ht hp
  rw [hc, hs, ht]
  exact hp.symm

/-- Reassemble the real parts of complex scalar coordinates on the J4 vector carrier. -/
noncomputable def q3RealCoordinatesToVector (M : Algsuperdiff.Section3.ABKModel 2) :
    (Fin 2 → Lp ℂ 2 (planarRegLaw M)) →L[ℝ] VectorL2 2 (planarRegLaw M) :=
  ∑ i : Fin 2, (q3VectorCoordLift M i).comp
    ((q3RealPart M).comp (ContinuousLinearMap.proj i))

theorem q3RealCoordinatesToVector_coord (M : Algsuperdiff.Section3.ABKModel 2)
    (F : Fin 2 → Lp ℂ 2 (planarRegLaw M)) (i : Fin 2) :
    vectorL2Coord i (q3RealCoordinatesToVector M F) = q3RealPart M (F i) := by
  change vectorL2Coord i (∑ j : Fin 2, q3VectorCoordLift M j (q3RealPart M (F j))) = _
  rw [map_sum]
  simp only [q3VectorCoordLift_coord]
  simp

/-- Embed a real stationary vector in the complex scalar-coordinate model. -/
noncomputable def q3ComplexifyVectorCoords (M : Algsuperdiff.Section3.ABKModel 2) :
    VectorL2 2 (planarRegLaw M) →L[ℝ] (Fin 2 → Lp ℂ 2 (planarRegLaw M)) :=
  ContinuousLinearMap.pi fun i => (q3ComplexifyScalar M).comp (vectorL2Coord i)

theorem q3RealCoordinatesToVector_complexify (M : Algsuperdiff.Section3.ABKModel 2)
    (F : VectorL2 2 (planarRegLaw M)) :
    q3RealCoordinatesToVector M (q3ComplexifyVectorCoords M F) = F := by
  apply q3VectorL2_ext_coord M
  intro i
  rw [q3RealCoordinatesToVector_coord]
  exact q3RealPart_complexify M (vectorL2Coord i F)

/-- Complexification carries the literal real horizontal gradient to the complex one. -/
theorem q3Complexify_horizontalGradient (M : Algsuperdiff.Section3.ABKModel 2)
    {φ : ScalarL2 (planarRegLaw M)} {F : VectorL2 2 (planarRegLaw M)}
    (hgrad : HasHorizontalGradient φ F) (i : Fin 2) :
    HasDerivAt
      (fun t : ℝ => q3ComplexKoopman M (t • (Pi.single i 1 : Vec 2))
        (q3ComplexifyScalar M φ)) (q3ComplexifyVectorCoords M F i) 0 := by
  have hdreal : HasDerivAt
      (fun t : ℝ => q3StreamKoopman M (t • (Pi.single i 1 : Vec 2)) φ)
      (vectorL2Coord i F) 0 := by
    simpa only [q3StreamKoopman] using hgrad i
  have hd := (q3ComplexifyScalar M).hasFDerivAt.comp_hasDerivAt 0 hdreal
  have hfun :
      (fun t : ℝ => q3ComplexKoopman M (t • (Pi.single i 1 : Vec 2))
        (q3ComplexifyScalar M φ)) =
      (fun t : ℝ => q3ComplexifyScalar M
        (q3StreamKoopman M (t • (Pi.single i 1 : Vec 2)) φ)) := by
    funext t
    exact (q3ComplexifyScalar_koopman M _ φ).symm
  rw [hfun]
  exact hd

/-- Taking real parts carries complex strong gradients to the exact J4 gradient. -/
theorem q3RealPart_horizontalGradient (M : Algsuperdiff.Section3.ABKModel 2)
    {φ : Lp ℂ 2 (planarRegLaw M)} {F : Fin 2 → Lp ℂ 2 (planarRegLaw M)}
    (hgrad : ∀ i : Fin 2, HasDerivAt
      (fun t : ℝ => q3ComplexKoopman M (t • (Pi.single i 1 : Vec 2)) φ) (F i) 0) :
    HasHorizontalGradient (q3RealPart M φ) (q3RealCoordinatesToVector M F) := by
  intro i
  rw [q3RealCoordinatesToVector_coord]
  have hd := (q3RealPart M).hasFDerivAt.comp_hasDerivAt 0 (hgrad i)
  have hfun :
      (fun t : ℝ => q3RealPart M (q3ComplexKoopman M (t • (Pi.single i 1 : Vec 2)) φ)) =
      (fun t : ℝ => q3StreamKoopman M (t • (Pi.single i 1 : Vec 2)) (q3RealPart M φ)) := by
    funext t
    exact q3RealPart_koopman M _ φ
  simp only [Function.comp_def] at hd
  rw [hfun] at hd
  simpa only [q3StreamKoopman] using hd

/-- The graph-core equality on the literal real stationary carrier used by J4. -/
theorem q3FirstChaosGradientCore
    (M : Algsuperdiff.Section3.ABKModel 2) (h : ℝ)
    (hM : ASDExplicitGamma.PlanarQ3Gaussian M h) :
    (q3OrbitHorizontalGradientRange M).topologicalClosure = q3FirstChaosPotentialSubspace M := by
  apply le_antisymm (q3OrbitHorizontalGradientRange_closure_le M)
  apply Submodule.topologicalClosure_minimal
  · rintro F ⟨φ, hφ, hdφ⟩
    have hc : q3ComplexifyVectorCoords M F ∈
        q3ComplexGradientRangeOn M (q3ComplexFirstChaos M) :=
      ⟨q3ComplexifyScalar M φ, q3ComplexifyScalar_firstChaos_mem M φ hφ,
        q3Complexify_horizontalGradient M hdφ⟩
    have hcore : q3ComplexifyVectorCoords M F ∈
        (q3ComplexGradientRangeOn M
          (Submodule.span ℂ (Set.range (q3ComplexStream M)))).topologicalClosure := by
      rw [q3ComplexFirstChaosGradientCore M h hM]
      exact Submodule.le_topologicalClosure _ hc
    let K := q3OrbitHorizontalGradientRange M
    have hsub : (q3ComplexGradientRangeOn M
        (Submodule.span ℂ (Set.range (q3ComplexStream M))) : Set _) ⊆
        (q3RealCoordinatesToVector M) ⁻¹' (K.topologicalClosure : Set _) := by
      rintro G ⟨ψ, hψ, hdψ⟩
      apply Submodule.le_topologicalClosure
      exact ⟨q3RealPart M ψ, q3RealPart_complexSpan_mem M ψ hψ,
        q3RealPart_horizontalGradient M hdψ⟩
    have hclosed : IsClosed ((q3RealCoordinatesToVector M) ⁻¹' (K.topologicalClosure : Set _)) :=
      (Submodule.isClosed_topologicalClosure K).preimage (q3RealCoordinatesToVector M).continuous
    have hmem := closure_minimal hsub hclosed hcore
    change q3RealCoordinatesToVector M (q3ComplexifyVectorCoords M F) ∈ K.topologicalClosure at hmem
    rwa [q3RealCoordinatesToVector_complexify] at hmem
  · exact Submodule.isClosed_topologicalClosure _

/-- A complex derivative of a real orbit is itself real. -/
theorem q3Complexify_realPart_derivative
    (M : Algsuperdiff.Section3.ABKModel 2) (i : Fin 2)
    (φ : ScalarL2 (planarRegLaw M)) (G : Lp ℂ 2 (planarRegLaw M))
    (hd : HasDerivAt
      (fun t : ℝ => q3ComplexKoopman M (t • (Pi.single i 1 : Vec 2))
        (q3ComplexifyScalar M φ)) G 0) :
    q3ComplexifyScalar M (q3RealPart M G) = G := by
  let Q := (q3ComplexifyScalar M).comp (q3RealPart M)
  have hQ (z : Vec 2) : Q (q3ComplexKoopman M z (q3ComplexifyScalar M φ)) =
      q3ComplexKoopman M z (q3ComplexifyScalar M φ) := by
    change q3ComplexifyScalar M (q3RealPart M
      (q3ComplexKoopman M z (q3ComplexifyScalar M φ))) = _
    rw [q3RealPart_koopman, q3RealPart_complexify, q3ComplexifyScalar_koopman]
  have h := Q.hasFDerivAt.comp_hasDerivAt 0 hd
  have hf : (Q ∘ fun t : ℝ => q3ComplexKoopman M (t • (Pi.single i 1 : Vec 2))
      (q3ComplexifyScalar M φ)) =
      (fun t : ℝ => q3ComplexKoopman M (t • (Pi.single i 1 : Vec 2))
        (q3ComplexifyScalar M φ)) := by
    funext t
    exact hQ _
  rw [hf] at h
  exact h.unique hd

end ASDExplicitGamma.Model
