module

public import ASDExplicitGamma.Model.SpectralHorizontalDerivative

@[expose] public section

open MeasureTheory Homogenization Complex

namespace ASDExplicitGamma.Model

/-- The range of complex strong horizontal gradients with potential in `K`. -/
noncomputable def q3ComplexGradientRangeOn
    (M : Algsuperdiff.Section3.ABKModel 2)
    (K : Submodule ℂ (Lp ℂ 2 (planarRegLaw M))) :
    Submodule ℂ (Fin 2 → Lp ℂ 2 (planarRegLaw M)) where
  carrier := {F | ∃ φ, φ ∈ K ∧ ∀ i : Fin 2,
    HasDerivAt (fun t : ℝ => q3ComplexKoopman M (t • (Pi.single i 1 : Vec 2)) φ) (F i) 0}
  zero_mem' := by
    refine ⟨0, K.zero_mem, ?_⟩
    intro i
    simpa only [map_zero, Pi.zero_apply] using
      hasDerivAt_const (x := (0 : ℝ)) (c := (0 : Lp ℂ 2 (planarRegLaw M)))
  add_mem' := by
    rintro F G ⟨φ, hφ, hdφ⟩ ⟨ψ, hψ, hdψ⟩
    refine ⟨φ + ψ, K.add_mem hφ hψ, ?_⟩
    intro i
    change HasDerivAt
      (fun t : ℝ => q3ComplexKoopman M (t • (Pi.single i 1 : Vec 2)) (φ + ψ))
      (F i + G i) 0
    have hfun :
        (fun t : ℝ => q3ComplexKoopman M (t • (Pi.single i 1 : Vec 2)) (φ + ψ)) =
        (fun t : ℝ => q3ComplexKoopman M (t • (Pi.single i 1 : Vec 2)) φ) +
          (fun t : ℝ => q3ComplexKoopman M (t • (Pi.single i 1 : Vec 2)) ψ) := by
      funext t
      simp only [map_add, Pi.add_apply]
    rw [hfun]
    exact (hdφ i).add (hdψ i)
  smul_mem' := by
    rintro c F ⟨φ, hφ, hdφ⟩
    refine ⟨c • φ, K.smul_mem c hφ, ?_⟩
    intro i
    change HasDerivAt
      (fun t : ℝ => q3ComplexKoopman M (t • (Pi.single i 1 : Vec 2)) (c • φ))
      (c • F i) 0
    have hfun :
        (fun t : ℝ => q3ComplexKoopman M (t • (Pi.single i 1 : Vec 2)) (c • φ)) =
        c • (fun t : ℝ => q3ComplexKoopman M (t • (Pi.single i 1 : Vec 2)) φ) := by
      funext t
      simp only [map_smul, Pi.smul_apply]
    rw [hfun]
    exact (hdφ i).const_smul c

/-- The gradient map from the weighted spectral domain to stationary coordinates. -/
noncomputable def q3ComplexGraphGradient
    (M : Algsuperdiff.Section3.ABKModel 2) (h : ℝ)
    (hM : ASDExplicitGamma.PlanarQ3Gaussian M h) :
    Lp ℂ 2 (q3SpectralGraphMeasure h) →L[ℂ] (Fin 2 → Lp ℂ 2 (planarRegLaw M)) :=
  ContinuousLinearMap.pi fun i => (q3SpectralInverse M h hM).toContinuousLinearMap.comp
    ((((2 * Real.pi : ℝ) : ℂ) * I) • q3SpectralGraphCoordinate h i)

theorem q3ComplexGraphGradient_apply
    (M : Algsuperdiff.Section3.ABKModel 2) (h : ℝ)
    (hM : ASDExplicitGamma.PlanarQ3Gaussian M h)
    (p : Lp ℂ 2 (q3SpectralGraphMeasure h)) (i : Fin 2) :
    q3ComplexGraphGradient M h hM p i = q3SpectralInverse M h hM
      ((((2 * Real.pi : ℝ) : ℂ) * I) • q3SpectralGraphCoordinate h i p) := rfl

/-- The weighted spectral gradient is the full strong horizontal gradient. -/
theorem q3ComplexGraphGradient_hasDeriv
    (M : Algsuperdiff.Section3.ABKModel 2) (h : ℝ)
    (hM : ASDExplicitGamma.PlanarQ3Gaussian M h)
    (p : Lp ℂ 2 (q3SpectralGraphMeasure h)) (i : Fin 2) :
    HasDerivAt
      (fun t : ℝ => q3ComplexKoopman M (t • (Pi.single i 1 : Vec 2))
        (q3SpectralInverse M h hM (q3SpectralGraphToBase h p)))
      (q3ComplexGraphGradient M h hM p i) 0 := by
  rw [q3ComplexGraphGradient_apply]
  apply (q3SpectralInverse_horizontal_derivative_iff M h hM i _ _).mpr
  filter_upwards [Lp.coeFn_smul (((2 * Real.pi : ℝ) : ℂ) * I)
      (q3SpectralGraphCoordinate h i p),
    q3SpectralGraphCoordinate_coeFn h i p, q3SpectralGraphToBase_coeFn h p]
      with ξ hs hc hb
  simp only [Pi.smul_apply] at hs
  rw [hs, hc, hb]
  simp only [smul_eq_mul, ofReal_mul]
  ring

/-- The same characters, represented in graph-weight `L²`. -/
noncomputable def q3SpectralGraphCharacter (h : ℝ) (x : Q3FrequencyPlane) :
    Lp ℂ 2 (q3SpectralGraphMeasure h) :=
  BoundedContinuousFunction.toLp 2 (q3SpectralGraphMeasure h) ℂ
    (BoundedContinuousFunction.innerProbChar ((2 * Real.pi) • x))

theorem q3SpectralGraphCharacter_span_dense (h : ℝ) :
    (Submodule.span ℂ (Set.range (q3SpectralGraphCharacter h))).topologicalClosure = ⊤ :=
  exponential_span_dense_rescale (q3SpectralGraphMeasure h) (2 * Real.pi)
    (mul_ne_zero (by norm_num) Real.pi_ne_zero)

theorem q3SpectralGraphToBase_character (h : ℝ) (x : Q3FrequencyPlane) :
    q3SpectralGraphToBase h (q3SpectralGraphCharacter h x) = q3SpectralCharacter h x := by
  apply Lp.ext
  have hw := ae_mono (q3SpectralMeasure_le_graphMeasure h)
    (BoundedContinuousFunction.coeFn_toLp 2 (q3SpectralGraphMeasure h) ℂ
      (BoundedContinuousFunction.innerProbChar ((2 * Real.pi) • x)))
  have hb := BoundedContinuousFunction.coeFn_toLp 2 (q3SpectralMeasure h) ℂ
    (BoundedContinuousFunction.innerProbChar ((2 * Real.pi) • x))
  filter_upwards [q3SpectralGraphToBase_coeFn h (q3SpectralGraphCharacter h x), hw, hb]
    with ξ hbase hw hb
  exact hbase.trans (hw.trans hb.symm)

/-- Every weighted gradient is approximated by gradients of algebraic stream sums. -/
theorem q3ComplexGraphGradient_mem_orbitClosure
    (M : Algsuperdiff.Section3.ABKModel 2) (h : ℝ)
    (hM : ASDExplicitGamma.PlanarQ3Gaussian M h)
    (p : Lp ℂ 2 (q3SpectralGraphMeasure h)) :
    q3ComplexGraphGradient M h hM p ∈
      (q3ComplexGradientRangeOn M (Submodule.span ℂ (Set.range (q3ComplexStream M)))).topologicalClosure := by
  let K := q3ComplexGradientRangeOn M (Submodule.span ℂ (Set.range (q3ComplexStream M)))
  let S := Submodule.span ℂ (Set.range (q3SpectralGraphCharacter h))
  let D := q3ComplexGraphGradient M h hM
  have hS : S ≤ K.topologicalClosure.comap D.toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨x, rfl⟩
    apply Submodule.le_topologicalClosure
    obtain ⟨z, rfl⟩ := q3SpectralPoint_surjective x
    refine ⟨q3ComplexStream M z, Submodule.subset_span (Set.mem_range_self z), ?_⟩
    intro i
    have hd := q3ComplexGraphGradient_hasDeriv M h hM
      (q3SpectralGraphCharacter h (q3SpectralPoint z)) i
    rwa [q3SpectralGraphToBase_character, q3SpectralInverse_character] at hd
  have hclosed : IsClosed (K.topologicalClosure.comap D.toLinearMap :
      Set (Lp ℂ 2 (q3SpectralGraphMeasure h))) := by
    change IsClosed (D ⁻¹' (K.topologicalClosure : Set _))
    exact (Submodule.isClosed_topologicalClosure K).preimage D.continuous
  have htop := Submodule.topologicalClosure_minimal S hS hclosed
  rw [q3SpectralGraphCharacter_span_dense h] at htop
  exact htop Submodule.mem_top

/-- Every strong first-chaos gradient comes from the weighted spectral domain. -/
theorem q3ComplexGradient_weighted_representation
    (M : Algsuperdiff.Section3.ABKModel 2) (h : ℝ)
    (hM : ASDExplicitGamma.PlanarQ3Gaussian M h)
    (F : Fin 2 → Lp ℂ 2 (planarRegLaw M))
    (hF : F ∈ q3ComplexGradientRangeOn M (q3ComplexFirstChaos M)) :
    ∃ p : Lp ℂ 2 (q3SpectralGraphMeasure h), q3ComplexGraphGradient M h hM p = F := by
  classical
  obtain ⟨φ, hφ, hd⟩ := hF
  rw [← q3SpectralInverse_range M h hM] at hφ
  obtain ⟨f, rfl⟩ := hφ
  have hG (i : Fin 2) : ∃ g : Lp ℂ 2 (q3SpectralMeasure h),
      q3SpectralInverse M h hM g = F i := by
    have hmem := q3ComplexHorizontalDerivative_mem M h hM i
      (q3SpectralInverse M h hM f) (F i)
      (by rw [← q3SpectralInverse_range M h hM]; exact ⟨f, rfl⟩) (hd i)
    rwa [← q3SpectralInverse_range M h hM] at hmem
  choose g hg using hG
  let c : ℂ := ((2 * Real.pi : ℝ) : ℂ) * I
  have hc : c ≠ 0 := mul_ne_zero
    (Complex.ofReal_ne_zero.mpr (mul_ne_zero (by norm_num) Real.pi_ne_zero)) I_ne_zero
  have hcoef (i : Fin 2) : (g i : Q3FrequencyPlane → ℂ) =ᵐ[q3SpectralMeasure h]
      fun ξ => c * ((q3FrequencyCoordinate i ξ : ℂ) * f ξ) := by
    have hdg : HasDerivAt
        (fun t : ℝ => q3ComplexKoopman M (t • (Pi.single i 1 : Vec 2))
          (q3SpectralInverse M h hM f)) (q3SpectralInverse M h hM (g i)) 0 := by
      rw [hg i]
      exact hd i
    have hae := (q3SpectralInverse_horizontal_derivative_iff M h hM i f (g i)).mp hdg
    filter_upwards [hae] with ξ hξ
    rw [hξ]
    dsimp [c]
    push_cast
    ring
  have hf (i : Fin 2) : MemLp (fun ξ => (q3FrequencyCoordinate i ξ : ℂ) * f ξ)
      2 (q3SpectralMeasure h) := by
    apply ((Lp.memLp (g i)).const_mul c⁻¹).ae_eq
    filter_upwards [hcoef i] with ξ hξ
    rw [hξ, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]
  let hp := q3Spectral_memLp_graphWeight h f hf
  let p : Lp ℂ 2 (q3SpectralGraphMeasure h) := hp.toLp f
  have hpf : (p : Q3FrequencyPlane → ℂ) =ᵐ[q3SpectralMeasure h] f :=
    ae_mono (q3SpectralMeasure_le_graphMeasure h) hp.coeFn_toLp
  refine ⟨p, ?_⟩
  funext i
  rw [q3ComplexGraphGradient_apply, ← hg i]
  apply congrArg (q3SpectralInverse M h hM)
  apply Lp.ext
  filter_upwards [Lp.coeFn_smul c (q3SpectralGraphCoordinate h i p),
    q3SpectralGraphCoordinate_coeFn h i p, hpf, hcoef i] with ξ hs hξ hp hg
  simp only [Pi.smul_apply] at hs
  rw [hs, hξ, hp, hg]
  rfl

/-- The algebraic stream span is a strong-gradient core on the complex first chaos. -/
theorem q3ComplexFirstChaosGradientCore
    (M : Algsuperdiff.Section3.ABKModel 2) (h : ℝ)
    (hM : ASDExplicitGamma.PlanarQ3Gaussian M h) :
    (q3ComplexGradientRangeOn M (Submodule.span ℂ (Set.range (q3ComplexStream M)))).topologicalClosure =
      (q3ComplexGradientRangeOn M (q3ComplexFirstChaos M)).topologicalClosure := by
  apply le_antisymm
  · apply Submodule.topologicalClosure_mono
    rintro F ⟨φ, hφ, hd⟩
    exact ⟨φ, Submodule.le_topologicalClosure _ hφ, hd⟩
  · apply Submodule.topologicalClosure_minimal
    · intro F hF
      obtain ⟨p, rfl⟩ := q3ComplexGradient_weighted_representation M h hM F hF
      exact q3ComplexGraphGradient_mem_orbitClosure M h hM p
    · exact Submodule.isClosed_topologicalClosure _

end ASDExplicitGamma.Model
