module

public import ASDExplicitGamma.Inverse.AssemblyShearSign

/-! Colored concentration for the actual added-stream conjugator. -/

@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory ProbabilityTheory Algsuperdiff.Section3
open scoped ENNReal NNReal Matrix.Norms.Elementwise
noncomputable section

/-- The old clipped-matrix family and the complete later physical shear family
have the product law required by the random-conjugator matrix estimate. -/
theorem assembly_old_later_shear_product_law {I : Type*} [Fintype I]
    (A : ABKModel 2) (m N : ℤ) (hmN : m ≤ N) (τ : ℝ)
    (Q : I → TriadicCube 2) (n : I → ℤ) (a c : I → ℝ) (weights : ℤ → ℝ) :
    let μ := (Cutoff.cutoffSampleLaw A).toMeasure
    μ.map (fun ω =>
      ((fun i => assemblyPhysicalShearMatrix A m (n i) N (a i) (c i) weights ω),
       (fun i => clippedCellMatrix A m (Q i) τ ω))) =
      (μ.map (fun ω i => assemblyPhysicalShearMatrix A m (n i) N (a i) (c i) weights ω)).prod
        (μ.map (fun ω i => clippedCellMatrix A m (Q i) τ ω) : Measure (I → FullBlockMat 2)) := by
  let μ := (Cutoff.cutoffSampleLaw A).toMeasure
  let R : Cutoff.CutoffSample 2 → I → FullBlockMat 2 := fun ω i =>
    assemblyPhysicalShearMatrix A m (n i) N (a i) (c i) weights ω
  let X : Cutoff.CutoffSample 2 → I → FullBlockMat 2 := fun ω i =>
    clippedCellMatrix A m (Q i) τ ω
  have hRlater : @Measurable (Cutoff.CutoffSample 2) (I → FullBlockMat 2)
      (Model.cutoffLaterSigma (Set.Ioi m)) _ R := by
    let assemblyLaterMeasurable : MeasurableSpace (Cutoff.CutoffSample 2) := Model.cutoffLaterSigma (Set.Ioi m)
    apply measurable_pi_iff.mpr
    intro i
    exact assembly_physical_shear_later_measurable A m (n i) N hmN (a i) (c i) weights
  have hXlocal : @Measurable (Cutoff.CutoffSample 2) (I → FullBlockMat 2)
      (Cutoff.cutoffSampleLocalSigma A m Set.univ) _ X := by
    let assemblyLocalMeasurable : MeasurableSpace (Cutoff.CutoffSample 2) :=
      Cutoff.cutoffSampleLocalSigma A m Set.univ
    apply measurable_pi_iff.mpr
    intro i
    exact clipped_cell_matrix_local_measurable A m (Q i) τ (Set.subset_univ _)
  have hSigma := Model.cutoff_lower_later_independent A m Set.univ (Set.Ioi m)
    (Set.Subset.rfl)
  have hIndep := ProbabilityTheory.indep_of_indep_of_le hSigma
    hXlocal.comap_le hRlater.comap_le
  have hIndep' : Indep
      ((inferInstance : MeasurableSpace (I → FullBlockMat 2)).comap R)
      ((inferInstance : MeasurableSpace (I → FullBlockMat 2)).comap X) μ := hIndep.symm
  have hIndepFun : IndepFun R X μ :=
    (ProbabilityTheory.IndepFun_iff_Indep R X μ).mpr hIndep'
  have hR : Measurable R := by
    apply measurable_pi_iff.mpr
    intro i
    exact assembly_physical_shear_measurable A m (n i) N (a i) (c i) weights
  have hX : Measurable X := by
    apply measurable_pi_iff.mpr
    intro i
    exact clipped_cell_matrix_measurable A m (Q i) τ
  have hpair := hIndepFun.map_prod_eq_prod_map_map hR.aemeasurable hX.aemeasurable
  simpa only [R, X, μ] using hpair

/-- Actual clipped matrices conjugated by their later physical shears obey
the all-order source matrix estimate. The colored law, the old/later product
law, and every shear moment are derived from the cutoff model. -/
theorem assembly_source_sheared_family_Lp {I : Type*} [Fintype I]
    (A : ABKModel 2) (h : ℝ) (hA : PlanarQ3Gaussian A h)
    (j N : ℤ) (hstrict : j+40 < N) (hstate : nativeInductionState A h (j+40))
    (τ : ℝ) (hτ : 0 ≤ τ) (Q : I → TriadicCube 2)
    (hscale : ∀ i, (Q i).scale=j) (hinj : Function.Injective Q)
    (a c : I → ℝ) (weights : ℤ → ℝ)
    (hw : ∀ k ∈ Finset.Ioc (j+40) N, 0 ≤ weights k ∧ weights k ≤ 1)
    (w : I → ℝ) (p : ℝ) (hp : 2 ≤ p) :
    let μ := (Cutoff.cutoffSampleLaw A).toMeasure
    eLpNorm (fun ω => ‖Matrix.toEuclideanCLM (n := BlockCoord 2) (𝕜 := ℝ)
      (∑ i, w i • ((assemblyPhysicalShearMatrix A (j+40) (Q i).scale N (a i) (c i) weights ω).transpose *
        (clippedCellMatrix A (j+40) (Q i) τ ω -
          ∫ ζ, clippedCellMatrix A (j+40) (Q i) τ ζ ∂μ) *
        assemblyPhysicalShearMatrix A (j+40) (Q i).scale N (a i) (c i) weights ω))‖)
      (ENNReal.ofReal p) μ ≤ ENNReal.ofReal
        (256*(3:ℝ)^40*(1+τ+Real.sqrt (τ*(τ+2)))*Real.sqrt p*
          Real.sqrt (∑ i, w i^2)*
          (2+80*(p+2)*(A.gamma*((N-(j+40):ℤ):ℝ)*
            (3:ℝ)^(2*A.gamma*((N-(j+40):ℤ):ℝ))))) := by
  let μ := (Cutoff.cutoffSampleLaw A).toMeasure
  let m : ℤ := j+40
  let X : Cutoff.CutoffSample 2 → I → FullBlockMat 2 := fun ω i =>
    clippedCellMatrix A m (Q i) τ ω
  let R : Cutoff.CutoffSample 2 → I → FullBlockMat 2 := fun ω i =>
    assemblyPhysicalShearMatrix A m (Q i).scale N (a i) (c i) weights ω
  let η : Measure (I → FullBlockMat 2) := μ.map X
  let ρ : Measure (I → FullBlockMat 2) := μ.map R
  let color : I → ClippedCellColor := fun i => clippedCellColor (Q i)
  let G : ℝ := 1+τ+Real.sqrt (τ*(τ+2))
  let B : ℝ := 2+80*(p+2)*(A.gamma*((N-m:ℤ):ℝ)*
    (3:ℝ)^(2*A.gamma*((N-m:ℤ):ℝ)))
  let assemblyMatrixSecondCountable : SecondCountableTopology (FullBlockMat 2) := by
    change SecondCountableTopology (BlockCoord 2 → BlockCoord 2 → ℝ)
    infer_instance
  have hmN : m ≤ N := by dsimp [m]; omega
  have hX : Measurable X := by
    apply measurable_pi_iff.mpr
    intro i
    exact clipped_cell_matrix_measurable A m (Q i) τ
  have hR : Measurable R := by
    apply measurable_pi_iff.mpr
    intro i
    exact assembly_physical_shear_measurable A m (Q i).scale N (a i) (c i) weights
  have hjoint : μ.map (fun ω => (R ω, X ω)) = ρ.prod η := by
    simpa only [m, R, X, ρ, η, μ] using
      (assembly_old_later_shear_product_law A (j+40) N (by omega) τ Q
        (fun i => (Q i).scale) a c weights)
  have hcolor : ∀ k, iIndepFun
      (fun i : {i // color i=k} => fun y : I → FullBlockMat 2 => y i.1) η := by
    intro k
    have hindμ := clipped_cell_matrices_colored_independent A h hA j τ Q hscale hinj k
    have hindμ' : iIndepFun
        (fun i : {i // color i=k} => fun ω : Cutoff.CutoffSample 2 => X ω i.1) μ := by
      simpa only [X, m] using hindμ
    have hsource := (iIndepFun_iff_map_fun_eq_pi_map
      (fun i : {i // color i=k} =>
        (clipped_cell_matrix_measurable A (j+40) (Q i.1) τ).aemeasurable)).mp hindμ'
    let P : (I → FullBlockMat 2) → {i // color i=k} → FullBlockMat 2 :=
      fun y i => y i.1
    have hP : Measurable P := by
      apply measurable_pi_iff.mpr
      intro i
      exact measurable_pi_apply i.1
    have hmap : η.map P = μ.map (fun (ω : Cutoff.CutoffSample 2)
        (i : {i // color i=k}) => X ω i.1) := by
      dsimp [η]
      rw [Measure.map_map hP hX]
      rfl
    have hcoord (i : {i // color i=k}) :
        η.map (fun y : I → FullBlockMat 2 => y i.1) =
          μ.map (fun ω => X ω i.1) := by
      dsimp [η]
      rw [Measure.map_map (measurable_pi_apply i.1) hX]
      rfl
    apply (iIndepFun_iff_map_fun_eq_pi_map
      (fun i : {i // color i=k} => (measurable_pi_apply i.1).aemeasurable)).mpr
    rw [hmap, hsource]
    congr 1
    funext i
    exact (hcoord i).symm
  have hG0 : 0 ≤ G := by dsimp [G]; positivity
  have hY : ∀ i, ∀ᵐ y ∂η,
      ‖Matrix.toEuclideanCLM (n := BlockCoord 2) (𝕜 := ℝ) (y i)‖ ≤ G := by
    intro i
    have hnorm : Measurable (fun y : I → FullBlockMat 2 =>
        ‖Matrix.toEuclideanCLM (n := BlockCoord 2) (𝕜 := ℝ) (y i)‖) := by
      let T := Matrix.toEuclideanCLM (n := BlockCoord 2) (𝕜 := ℝ)
      let L : FullBlockMat 2 →ₗ[ℝ]
          (EuclideanSpace ℝ (BlockCoord 2) →L[ℝ] EuclideanSpace ℝ (BlockCoord 2)) :=
        { toFun := T
          map_add' := fun B C => map_add T B C
          map_smul' := fun r B => map_smul T r B }
      exact L.continuous_of_finiteDimensional.norm.measurable.comp (measurable_pi_apply i)
    rw [ae_map_iff hX.aemeasurable (measurableSet_le hnorm measurable_const)]
    filter_upwards with ω
    simpa only [X, m, G] using clipped_cell_matrix_norm_le A (j+40) (Q i) τ hτ ω
  have hYint : ∀ i, Integrable (fun y : I → FullBlockMat 2 => y i) η := by
    intro i
    have hbase : Integrable (fun ω => X ω i) μ := by
      simpa only [X, m, μ] using clipped_cell_matrix_integrable A (j+40) (Q i) τ
    apply (integrable_map_measure
      ((measurable_pi_apply i).aestronglyMeasurable) hX.aemeasurable).mpr
    exact hbase
  let T := Matrix.toEuclideanCLM (n := BlockCoord 2) (𝕜 := ℝ)
  let S : I → (I → FullBlockMat 2) → ℝ := fun i r => ‖T (r i)‖^2
  have hSameas (i : I) : (Q i).scale=j := hscale i
  have hSmeas (i : I) : Measurable (S i) := by
    let L : FullBlockMat 2 →ₗ[ℝ]
        (EuclideanSpace ℝ (BlockCoord 2) →L[ℝ] EuclideanSpace ℝ (BlockCoord 2)) :=
      { toFun := T
        map_add' := fun B C => map_add T B C
        map_smul' := fun r B => map_smul T r B }
    exact (L.continuous_of_finiteDimensional.norm.measurable.comp
      (measurable_pi_apply i)).pow_const 2
  have hS0 (i : I) (r : I → FullBlockMat 2) : 0 ≤ S i r := by
    dsimp [S]
    positivity
  have hB0 : 0 ≤ B := by
    have hγ : 0 ≤ A.gamma := le_of_lt A.shellPrefix.gamma_pos
    dsimp [B]
    have hgap : 0 ≤ ((N-m:ℤ):ℝ) := by
      have hz : 0 ≤ N-m := sub_nonneg.mpr hmN
      exact_mod_cast hz
    positivity
  have hSLp (i : I) : eLpNorm (S i) (ENNReal.ofReal p) ρ ≤ ENNReal.ofReal B := by
    let g : (I → FullBlockMat 2) → ℝ := S i
    have hg : Measurable g := hSmeas i
    have hmap := eLpNorm_map_measure (μ := μ) (p := ENNReal.ofReal p)
      (f := R) (g := g) hg.aestronglyMeasurable hR.aemeasurable
    have hmoment := assembly_physical_shear_sq_Lp A h hA (j+40) j N hstrict hstate
      (a i) (c i) weights hw p (by linarith)
    calc
      eLpNorm (S i) (ENNReal.ofReal p) ρ =
          eLpNorm (fun ω => S i (R ω)) (ENNReal.ofReal p) μ := by
            dsimp [ρ]
            exact hmap
      _ ≤ ENNReal.ofReal B := by
        have hcomp : (fun ω => S i (R ω)) =
            (fun ω => ‖T (assemblyPhysicalShearMatrix A (j+40) j N (a i) (c i) weights ω)‖^2) := by
          funext ω
          simp only [S, R, m, hscale i]
        rw [hcomp]
        simpa only [T, B, m, Int.cast_sub] using hmoment
  have hRadius : eLpNorm (fun r => Real.sqrt (∑ i, w i^2 *
      ‖T (r i)‖^4)) (ENNReal.ofReal p) ρ ≤
      ENNReal.ofReal (Real.sqrt (∑ i, (w i*B)^2)) := by
    have h := weighted_shear_radius_Lp ρ p hp S hSmeas hS0 w (fun _ => B)
      (fun _ => hB0) hSLp
    have heq : (fun r => Real.sqrt (∑ i, w i^2*(S i r)^2)) =
        (fun r => Real.sqrt (∑ i, w i^2*‖T (r i)‖^4)) := by
      funext r
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      dsimp [S]
      ring
    rw [heq] at h
    exact h
  have hconc := independent_random_shear_matrix_concentration_Lp μ η ρ X R hjoint
    hX hR color hcolor G hG0 hY hYint w p hp
    (Real.sqrt (∑ i, (w i*B)^2)) hRadius
  have hmean (i : I) : (∫ y, y i ∂η) = ∫ ζ, X ζ i ∂μ := by
    exact integral_map hX.aemeasurable (hYint i).aestronglyMeasurable
  have heq :
      (fun ω => ‖T (∑ i, w i • ((R ω i).transpose *
        (X ω i-∫ y, y i ∂η) * (R ω i)))‖) =
      (fun ω => ‖T (∑ i, w i • ((R ω i).transpose *
        (X ω i-∫ ζ, X ζ i ∂μ) * (R ω i)))‖) := by
    funext ω
    apply congrArg (fun B : FullBlockMat 2 => ‖T B‖)
    apply Finset.sum_congr rfl
    intro i hi
    rw [hmean i]
  rw [heq] at hconc
  have hcolorCard : Real.sqrt (Fintype.card ClippedCellColor:ℝ) = 4*(3:ℝ)^40 := by
    calc
      Real.sqrt (Fintype.card ClippedCellColor:ℝ) =
          Real.sqrt ((4*(3:ℝ)^40)^2) := by rw [clipped_cell_color_card]; norm_num
      _ = 4*(3:ℝ)^40 := Real.sqrt_sq (by positivity)
  have hradiusEq : Real.sqrt (∑ i, (w i*B)^2) =
      B*Real.sqrt (∑ i, w i^2) := by
    have hsum : (∑ i, (w i*B)^2) = B^2*(∑ i, w i^2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    rw [hsum, Real.sqrt_mul (sq_nonneg B), Real.sqrt_sq hB0]
  calc
    _ ≤ ENNReal.ofReal
        (4*4^2*G*Real.sqrt p*Real.sqrt (Fintype.card ClippedCellColor:ℝ)*
          Real.sqrt (∑ i, (w i*B)^2)) := by
      simpa only [m, G, B, T, R, X, μ] using hconc
    _ = ENNReal.ofReal
        (256*(3:ℝ)^40*(1+τ+Real.sqrt (τ*(τ+2)))*Real.sqrt p*
          Real.sqrt (∑ i, w i^2)*B) := by
      congr 1
      rw [hcolorCard, hradiusEq]
      ring


end
end ASDExplicitGamma.Inverse
