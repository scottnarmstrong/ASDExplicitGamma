module

public import ASDExplicitGamma.Scalar.DirichletFiniteEnergy
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
public import Mathlib.MeasureTheory.Function.L2Space

/-! Completeness of the actual square Dirichlet sine modes in normalized L2. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization Triadic Torus MeasureTheory
open scoped RealInnerProductSpace

/-- Normalized L2 on the actual square. -/
noncomputable abbrev DirichletL2 (Q : TriadicCube 2) := Lp ℝ 2 (normalizedCubeMeasure Q)

/-- Each sine mode is genuinely square-integrable. -/
theorem memLp_dirichlet_mode (Q : TriadicCube 2) (q : Fin 2 → ℕ) :
    MemLp (cubeDirichletMode Q q) 2 (normalizedCubeMeasure Q) := by
  exact memLp_normalized_of_memL2On
    (H1Function.ofContDiffOnIsOpenBoundedConvexDomain (isOpenBoundedConvexDomain_openCubeSet Q)
      (contDiff_cubeDirichletMode Q Finset.univ (natVec q) (m := 1))).memL2

/-- The actual sine mode as an L2 equivalence class. -/
noncomputable def dirichletModeL2 (Q : TriadicCube 2) (q : Fin 2 → ℕ) : DirichletL2 Q :=
  (memLp_dirichlet_mode Q q).toLp (cubeDirichletMode Q q)

/-- Its Hilbert coordinate is exactly the existing signed sine Fourier coefficient. -/
theorem inner_dirichlet_mode_L2 (Q : TriadicCube 2) (q : Fin 2 → ℕ) (f : DirichletL2 Q) :
    inner ℝ (dirichletModeL2 Q q) f=dirichletFourierCoeff Q f (natVec q) := by
  rw [L2.inner_def]
  unfold dirichletFourierCoeff
  rw [boxMeasure_eq_normalizedCubeMeasure]
  apply integral_congr_ae
  filter_upwards [(memLp_dirichlet_mode Q q).coeFn_toLp] with x hx
  change (dirichletModeL2 Q q : Vec 2 → ℝ) x=cubeDirichletMode Q q x at hx
  rw [hx]
  simp only [Real.inner_apply, cubeDirichletMode]

/-- The finite sine span contains no nonzero orthogonal L2 vector. -/
theorem dirichlet_sine_span_orthogonal_eq_bot (Q : TriadicCube 2) :
    (Submodule.span ℝ (Set.range (dirichletModeL2 Q)))ᗮ=⊥ := by
  apply (Submodule.eq_bot_iff _).mpr
  intro f hf
  have hq (q : Fin 2 → ℕ) : dirichletFourierCoeff Q f (natVec q)=0 := by
    rw [← inner_dirichlet_mode_L2]
    exact (Submodule.mem_orthogonal _ _).mp hf _ (Submodule.subset_span ⟨q,rfl⟩)
  have hp (p : Fin 2 → ℤ) : dirichletFourierCoeff Q f p^2=0 := by
    rw [dirichletFourierCoeff_sq_natAbsVec,hq,pow_two,zero_mul]
  have hm : MemLp (f : Vec 2 → ℝ) 2 (boxMeasure (cubeCorner Q) (cubeScaleFactor Q)) := by
    rw [boxMeasure_eq_normalizedCubeMeasure]
    exact Lp.memLp f
  have hparseval := hasSum_sq_dirichletFourierCoeff Q hm
  rw [boxMeasure_eq_normalizedCubeMeasure] at hparseval
  have hi : (∫ x,(f x)^2 ∂normalizedCubeMeasure Q)=0 := by
    have h := hparseval.tsum_eq.symm
    simpa only [hp,tsum_zero] using h
  apply (inner_self_eq_zero (𝕜 := ℝ)).mp
  rw [L2.inner_def]
  simpa only [real_inner_self_eq_norm_sq,Real.norm_eq_abs,sq_abs] using hi

/-- Completeness of the square sine modes, with no approximation assumption. -/
theorem dirichlet_sine_span_dense (Q : TriadicCube 2) :
    (Submodule.span ℝ (Set.range (dirichletModeL2 Q))).topologicalClosure=⊤ :=
  Submodule.topologicalClosure_eq_top_iff.mpr (dirichlet_sine_span_orthogonal_eq_bot Q)

end ASDExplicitGamma.Scalar
