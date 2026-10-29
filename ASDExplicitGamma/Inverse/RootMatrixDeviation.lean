module

public import ASDExplicitGamma.Inverse.RootDefinitions
public import ASDExplicitGamma.Inverse.ClippedMatrixDirectionalSup
public import ASDExplicitGamma.Inverse.ClippedMatrixConditional

/-! Actual positive directional matrix errors: measurability and operator
norm domination before any stochastic concentration or root comparison. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open scoped Matrix.Norms.Elementwise ENNReal
noncomputable section

/-- Unit pure-flux loadings in the genuine doubled Euclidean space. -/
def clippedUnitFluxLoads : Set (EuclideanSpace ℝ (BlockCoord 2)) :=
  {u | ∃ v : Vec 2, dotProduct v v=1 ∧ u=WithLp.toLp 2 (toFullBlockVec (0,v))}

theorem clipped_unit_flux_loads_nonempty : clippedUnitFluxLoads.Nonempty := by
  refine ⟨WithLp.toLp 2 (toFullBlockVec (0,basisVec 0)),basisVec 0,?_,rfl⟩
  norm_num [dotProduct,Fin.sum_univ_two,basisVec]

theorem clipped_unit_flux_loads_norm {u : EuclideanSpace ℝ (BlockCoord 2)}
    (hu : u ∈ clippedUnitFluxLoads) : ‖u‖=1 := by
  obtain ⟨v,hv,rfl⟩ := hu
  have hn : ‖WithLp.toLp 2 (toFullBlockVec (0,v))‖^2=1 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simpa only [toFullBlockVec,Fintype.sum_sum_type,Pi.zero_apply,zero_pow (by decide : 2≠0),
      zero_mul,Finset.sum_const_zero,zero_add,pow_two,dotProduct] using hv
  nlinarith only [hn,norm_nonneg (WithLp.toLp 2 (toFullBlockVec (0,v)))]

/-- Literal positive largest pure-flux directional deviation of a full matrix. -/
def clippedPositiveFluxDeviation (A : FullBlockMat 2) : ℝ :=
  max 0 (sSup {a : ℝ | ∃ v : Vec 2, dotProduct v v=1 ∧
    a=fullMatrixQuadratic (toFullBlockVec (0,v)) A})

theorem clipped_positive_flux_deviation_eq_sup (A : FullBlockMat 2) :
    clippedPositiveFluxDeviation A = max 0 (sSup ((fun u : EuclideanSpace ℝ (BlockCoord 2) =>
      inner ℝ u (Matrix.toEuclideanCLM (n := BlockCoord 2) (𝕜 := ℝ) A u)) '' clippedUnitFluxLoads)) := by
  have he (v : Vec 2) : inner ℝ (WithLp.toLp 2 (toFullBlockVec (0,v)))
      (Matrix.toEuclideanCLM (n := BlockCoord 2) (𝕜 := ℝ) A (WithLp.toLp 2 (toFullBlockVec (0,v)))) =
      fullMatrixQuadratic (toFullBlockVec (0,v)) A := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp only [Matrix.ofLp_toEuclideanCLM,star_trivial]
    rw [dotProduct_comm]
    rfl
  unfold clippedPositiveFluxDeviation
  congr 2
  ext a
  constructor
  · rintro ⟨v,hv,rfl⟩
    exact ⟨WithLp.toLp 2 (toFullBlockVec (0,v)),⟨v,hv,rfl⟩,he v⟩
  · rintro ⟨u,⟨v,hv,rfl⟩,rfl⟩
    exact ⟨v,hv,he v⟩

/-- No symmetry or eigenvector selection is needed for measurability. -/
theorem clipped_positive_flux_deviation_continuous : Continuous clippedPositiveFluxDeviation := by
  let L : FullBlockMat 2 →ₗ[ℝ]
      (EuclideanSpace ℝ (BlockCoord 2) →L[ℝ] EuclideanSpace ℝ (BlockCoord 2)) :=
    { toFun := Matrix.toEuclideanCLM (n := BlockCoord 2) (𝕜 := ℝ)
      map_add' := fun A B => map_add (Matrix.toEuclideanCLM (n := BlockCoord 2) (𝕜 := ℝ)) A B
      map_smul' := fun r A => map_smul (Matrix.toEuclideanCLM (n := BlockCoord 2) (𝕜 := ℝ)) r A }
  have hh := (clipped_positive_directional_sup_lipschitz clippedUnitFluxLoads
    clipped_unit_flux_loads_nonempty (fun _ hx => clipped_unit_flux_loads_norm hx)).continuous.comp
    L.continuous_of_finiteDimensional
  exact hh.congr (fun A => (clipped_positive_flux_deviation_eq_sup A).symm)

theorem clipped_positive_flux_deviation_le (A : FullBlockMat 2) :
    clippedPositiveFluxDeviation A ≤ ‖Matrix.toEuclideanCLM (n := BlockCoord 2) (𝕜 := ℝ) A‖ := by
  rw [clipped_positive_flux_deviation_eq_sup]
  exact clipped_positive_directional_sup_le clippedUnitFluxLoads clipped_unit_flux_loads_nonempty
    (fun _ hx => clipped_unit_flux_loads_norm hx) _

/-- Actual centered full layer, with its literal deterministic cell weights. -/
theorem root_centered_layer_matrix_measurable (M : ABKModel 2) (Q : TriadicCube 2)
    (r : RootRow) (hk : ℕ × ℕ) : Measurable (rootCenteredLayerMatrix M Q r hk) := by
  apply Measurable.of_eval_matrix
  intro i j
  simp only [rootCenteredLayerMatrix,Matrix.sum_apply,Matrix.smul_apply,
    Matrix.sub_apply,smul_eq_mul]
  apply Finset.measurable_sum
  intro U _
  exact (((measurable_pi_apply j).comp ((measurable_pi_apply i).comp
    (clipped_cell_matrix_measurable M (rootLayerOldLabel Q (rootH0 r) hk) U (rootTau r)))).sub_const _).const_mul _

/-- The actual positive error is measurable on the same law, before any
response inequality, using the whole loading population at once. -/
theorem root_matrix_positive_error_measurable (M : ABKModel 2) (Q : TriadicCube 2)
    (r : RootRow) (hk : ℕ × ℕ) : Measurable (rootMatrixPositiveError M Q r hk) :=
  clipped_positive_flux_deviation_continuous.measurable.comp
    (root_centered_layer_matrix_measurable M Q r hk)

theorem root_matrix_positive_error_le (M : ABKModel 2) (Q : TriadicCube 2)
    (r : RootRow) (hk : ℕ × ℕ) (ω : Cutoff.CutoffSample 2) :
    rootMatrixPositiveError M Q r hk ω ≤
      ‖Matrix.toEuclideanCLM (n := BlockCoord 2) (𝕜 := ℝ) (rootCenteredLayerMatrix M Q r hk ω)‖ :=
  clipped_positive_flux_deviation_le _

end
end ASDExplicitGamma.Inverse
