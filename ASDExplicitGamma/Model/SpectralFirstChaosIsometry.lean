module

public import ASDExplicitGamma.Model.SpectralIsometry
public import Mathlib.Analysis.Normed.Operator.Extend

@[expose] public section

open MeasureTheory Homogenization Complex

namespace ASDExplicitGamma.Model

/-- Real stationary observables viewed as complex stationary observables. -/
noncomputable def q3ComplexifyScalar (M : Algsuperdiff.Section3.ABKModel 2) :
    Lp ℝ 2 (planarRegLaw M) →L[ℝ] Lp ℂ 2 (planarRegLaw M) :=
  Complex.ofRealCLM.compLpL 2 (planarRegLaw M)

/-- The complex stream generator indexed by a source spatial point. -/
noncomputable def q3ComplexStream (M : Algsuperdiff.Section3.ABKModel 2) (x : Vec 2) :
    Lp ℂ 2 (planarRegLaw M) :=
  q3ComplexifyScalar M (q3StreamKoopman M x (q3StreamOriginL2 M))

/-- The complexification of the scalar stream first chaos. -/
noncomputable def q3ComplexFirstChaos (M : Algsuperdiff.Section3.ABKModel 2) :
    Submodule ℂ (Lp ℂ 2 (planarRegLaw M)) :=
  (Submodule.span ℂ (Set.range (q3ComplexStream M))).topologicalClosure

private theorem complexify_inner {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f g : Lp ℝ 2 μ) :
    inner ℂ ((Complex.ofRealCLM.compLpL 2 μ) f) ((Complex.ofRealCLM.compLpL 2 μ) g) =
      (inner ℝ f g : ℂ) := by
  rw [L2.inner_def]
  calc
    (∫ ω, inner ℂ ((Complex.ofRealCLM.compLpL 2 μ) f ω)
        ((Complex.ofRealCLM.compLpL 2 μ) g ω) ∂μ) =
        ∫ ω, ((f ω * g ω : ℝ) : ℂ) ∂μ := by
      apply integral_congr_ae
      filter_upwards [Complex.ofRealCLM.coeFn_compLpL f,
        Complex.ofRealCLM.coeFn_compLpL g] with ω hf hg
      rw [hf, hg]
      simp only [Complex.ofRealCLM_apply, RCLike.inner_apply, Complex.conj_ofReal, ofReal_mul]
      ring
    _ = _ := by
      rw [integral_complex_ofReal, L2.inner_def]
      congr 1
      apply integral_congr_ae
      filter_upwards [] with ω
      simp only [Real.inner_apply]

private theorem q3ComplexStream_inner
    (M : Algsuperdiff.Section3.ABKModel 2) (h : ℝ)
    (hM : ASDExplicitGamma.PlanarQ3Gaussian M h) (x y : Vec 2) :
    inner ℂ (q3ComplexStream M x) (q3ComplexStream M y) =
      inner ℂ (q3SpectralCharacter h (q3SpectralPoint x))
        (q3SpectralCharacter h (q3SpectralPoint y)) := by
  rw [q3ComplexStream, q3ComplexStream, q3ComplexifyScalar, complexify_inner,
    q3StreamKoopman_inner M h hM, q3SpectralCharacter_inner]
  simp only [q3SpectralPoint, WithLp.toLp_fst, WithLp.toLp_snd, Pi.sub_apply]
  have h0 : q3Cov (y 0 - x 0) = q3Cov (x 0 - y 0) := by
    rw [show y 0 - x 0 = -(x 0 - y 0) by ring, q3Cov_even]
  have h1 : q3Cov (y 1 - x 1) = q3Cov (x 1 - y 1) := by
    rw [show y 1 - x 1 = -(x 1 - y 1) by ring, q3Cov_even]
  rw [h0, h1]

theorem q3SpectralPoint_surjective : Function.Surjective q3SpectralPoint := by
  intro ξ
  refine ⟨![ξ.fst, ξ.snd], ?_⟩
  apply WithLp.ofLp_injective 2
  exact Prod.ext rfl rfl

theorem q3SpectralCombination_dense (h : ℝ) :
    DenseRange (Finsupp.linearCombination ℂ
      (fun x : Vec 2 => q3SpectralCharacter h (q3SpectralPoint x))) := by
  change Dense (Set.range (Finsupp.linearCombination ℂ
    (fun x : Vec 2 => q3SpectralCharacter h (q3SpectralPoint x)) : (Vec 2 →₀ ℂ) → _))
  rw [← LinearMap.coe_range, Finsupp.range_linearCombination]
  apply Submodule.dense_iff_topologicalClosure_eq_top.mpr
  have hr : Set.range (fun x : Vec 2 => q3SpectralCharacter h (q3SpectralPoint x)) =
      Set.range (q3SpectralCharacter h) := by
    ext f
    constructor
    · rintro ⟨x, rfl⟩
      exact Set.mem_range_self _
    · rintro ⟨ξ, rfl⟩
      obtain ⟨x, rfl⟩ := q3SpectralPoint_surjective ξ
      exact Set.mem_range_self _
  rw [hr]
  exact q3SpectralCharacter_span_dense h

theorem q3ComplexCombination_norm
    (M : Algsuperdiff.Section3.ABKModel 2) (h : ℝ)
    (hM : ASDExplicitGamma.PlanarQ3Gaussian M h) (c : Vec 2 →₀ ℂ) :
    ‖(Finsupp.linearCombination ℂ (q3ComplexStream M)) c‖ =
      ‖(Finsupp.linearCombination ℂ (fun x =>
        q3SpectralCharacter h (q3SpectralPoint x))) c‖ := by
  simp_rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), Finsupp.linearCombination_apply,
    Finsupp.sum_inner, Finsupp.inner_sum, inner_smul_left, inner_smul_right,
    q3ComplexStream_inner M h hM]

/-- The spectral model mapped isometrically to the complex stationary stream space. -/
noncomputable def q3SpectralInverse
    (M : Algsuperdiff.Section3.ABKModel 2) (h : ℝ)
    (hM : ASDExplicitGamma.PlanarQ3Gaussian M h) :
    Lp ℂ 2 (q3SpectralMeasure h) →ₗᵢ[ℂ] Lp ℂ 2 (planarRegLaw M) :=
  (Finsupp.linearCombination ℂ (q3ComplexStream M)).extendOfIsometry
    (e := Finsupp.linearCombination ℂ (fun x : Vec 2 =>
      q3SpectralCharacter h (q3SpectralPoint x)))
    (q3SpectralCombination_dense h) (q3ComplexCombination_norm M h hM)

/-- The isometry sends each spectral character to its stationary stream value. -/
theorem q3SpectralInverse_character
    (M : Algsuperdiff.Section3.ABKModel 2) (h : ℝ)
    (hM : ASDExplicitGamma.PlanarQ3Gaussian M h) (x : Vec 2) :
    q3SpectralInverse M h hM (q3SpectralCharacter h (q3SpectralPoint x)) =
      q3ComplexStream M x := by
  have he := LinearMap.extendOfIsometry_eq
    (Finsupp.linearCombination ℂ (q3ComplexStream M))
    (e := Finsupp.linearCombination ℂ (fun x : Vec 2 =>
      q3SpectralCharacter h (q3SpectralPoint x)))
    (q3SpectralCombination_dense h) (q3ComplexCombination_norm M h hM) (Finsupp.single x 1)
  simpa only [q3SpectralInverse, Finsupp.linearCombination_single, one_smul] using he

/-- The isometry has exactly the complexified first chaos as its range. -/
theorem q3SpectralInverse_range
    (M : Algsuperdiff.Section3.ABKModel 2) (h : ℝ)
    (hM : ASDExplicitGamma.PlanarQ3Gaussian M h) :
    LinearMap.range (q3SpectralInverse M h hM).toLinearMap = q3ComplexFirstChaos M := by
  let U := q3SpectralInverse M h hM
  have hclosed : IsClosed (LinearMap.range U.toLinearMap : Set (Lp ℂ 2 (planarRegLaw M))) := by
    rw [LinearMap.coe_range]
    exact U.isometry.isClosedEmbedding.isClosed_range
  apply le_antisymm
  · rintro _ ⟨f, rfl⟩
    change U f ∈ q3ComplexFirstChaos M
    apply DenseRange.induction_on (q3SpectralCombination_dense h)
      (p := fun g => U g ∈ q3ComplexFirstChaos M) f
    · exact (Submodule.isClosed_topologicalClosure _).preimage U.continuous
    · intro c
      have he := LinearMap.extendOfIsometry_eq
        (Finsupp.linearCombination ℂ (q3ComplexStream M))
        (e := Finsupp.linearCombination ℂ (fun x : Vec 2 =>
          q3SpectralCharacter h (q3SpectralPoint x)))
        (q3SpectralCombination_dense h) (q3ComplexCombination_norm M h hM) c
      change U ((Finsupp.linearCombination ℂ (fun x : Vec 2 =>
        q3SpectralCharacter h (q3SpectralPoint x))) c) ∈ q3ComplexFirstChaos M
      rw [show U ((Finsupp.linearCombination ℂ (fun x : Vec 2 =>
          q3SpectralCharacter h (q3SpectralPoint x))) c) =
          (Finsupp.linearCombination ℂ (q3ComplexStream M)) c from he]
      apply Submodule.le_topologicalClosure
      rw [← Finsupp.range_linearCombination ℂ]
      exact ⟨c, rfl⟩
  · apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      rintro _ ⟨x, rfl⟩
      exact ⟨q3SpectralCharacter h (q3SpectralPoint x), q3SpectralInverse_character M h hM x⟩
    · exact hclosed

/-- The concrete spectral isometry onto the complexified stream first chaos. -/
noncomputable def q3SpectralIsometry
    (M : Algsuperdiff.Section3.ABKModel 2) (h : ℝ)
    (hM : ASDExplicitGamma.PlanarQ3Gaussian M h) :
    Lp ℂ 2 (q3SpectralMeasure h) ≃ₗᵢ[ℂ] q3ComplexFirstChaos M :=
  (q3SpectralInverse M h hM).equivRange.trans
    (LinearIsometryEquiv.ofEq _ _ (q3SpectralInverse_range M h hM))

theorem q3ComplexifyScalar_inner (M : Algsuperdiff.Section3.ABKModel 2)
    (f g : Lp ℝ 2 (planarRegLaw M)) :
    inner ℂ (q3ComplexifyScalar M f) (q3ComplexifyScalar M g) = (inner ℝ f g : ℂ) :=
  complexify_inner (planarRegLaw M) f g

end ASDExplicitGamma.Model
