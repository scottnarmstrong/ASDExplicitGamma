module

public import ASDExplicitGamma.Inverse.ClippedMatrixQuadraticNorm
public import Mathlib.Analysis.InnerProductSpace.Rayleigh
public import Mathlib.Analysis.Matrix.Hermitian

/-! Euclidean norm cap from nonnegative quadratic bounds on one symmetric matrix. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse

/-- Quadratic bounds over the whole loading space give the actual operator
norm bound, rather than separate direction-dependent exceptional events. -/
theorem clipped_symmetric_norm_le_of_quadratic {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (hA : A.IsHermitian) (B : ℝ) (hB : 0 ≤ B)
    (hpos : ∀ v, 0 ≤ dotProduct v (A.mulVec v))
    (hcap : ∀ v, dotProduct v (A.mulVec v) ≤ B*dotProduct v v) :
    ‖Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) A‖ ≤ B := by
  let T := Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) A
  have hT : T.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr hA
  rw [T.norm_eq_iSup_rayleighQuotient hT]
  apply ciSup_le
  intro x
  by_cases hx : x=0
  · subst x
    simpa only [T.rayleighQuotient_apply_zero,abs_zero] using hB
  have hd : 0 < ‖x‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hx)
  have he : inner ℝ (T x) x = dotProduct (WithLp.ofLp x) (A.mulVec (WithLp.ofLp x)) := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp only [T,Matrix.ofLp_toEuclideanCLM,star_trivial]
  change |inner ℝ (T x) x/‖x‖^2| ≤ B
  rw [he,abs_of_nonneg (div_nonneg (hpos _) hd.le),div_le_iff₀ hd]
  have hh := hcap (WithLp.ofLp x)
  have hn : ‖x‖^2=dotProduct (WithLp.ofLp x) (WithLp.ofLp x) :=
    clipped_euclidean_norm_sq (WithLp.ofLp x)
  simpa only [hn] using hh

end ASDExplicitGamma.Inverse
