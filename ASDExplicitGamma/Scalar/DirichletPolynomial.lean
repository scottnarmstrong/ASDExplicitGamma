module

public import ASDExplicitGamma.Triadic.PlanarDirichletSpectral
public import Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.FaceVanishCollar

/-! Actual finite Dirichlet sine polynomials, before the H2 limit passage. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization Triadic Torus MeasureTheory

/-- The actual finite sine polynomial whose Hessian is the existing dirichletTestHess. -/
noncomputable def dirichletPolynomial {d : ℕ} (Q : TriadicCube d)
    (S : Finset (Fin d → ℕ)) (beta : (Fin d → ℕ) → ℝ) (x : Vec d) : ℝ :=
  ∑ q ∈ S,beta q*cubeDirichletMode Q q x

/-- Finite sine polynomials are smooth on the whole ambient space. -/
theorem dirichlet_polynomial_contDiff {d : ℕ} (Q : TriadicCube d)
    (S : Finset (Fin d → ℕ)) (beta : (Fin d → ℕ) → ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (dirichletPolynomial Q S beta) := by
  apply ContDiff.sum
  intro q hq
  exact contDiff_const.mul (contDiff_cubeDirichletMode Q Finset.univ (natVec q))

/-- The sine mode vanishes on every lower coordinate face. -/
theorem dirichlet_mode_lower_face {d : ℕ} (Q : TriadicCube d)
    (q : Fin d → ℕ) (i : Fin d) (x : Vec d) :
    cubeDirichletMode Q q (cubeLowerFaceProjection Q i x)=0 := by
  unfold cubeDirichletMode boxMode
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simp [cubeLowerFaceProjection,cubeLowerFaceCoord,cubeCorner]

/-- The sine mode vanishes on every upper coordinate face. -/
theorem dirichlet_mode_upper_face {d : ℕ} (Q : TriadicCube d)
    (q : Fin d → ℕ) (i : Fin d) (x : Vec d) :
    cubeDirichletMode Q q (cubeUpperFaceProjection Q i x)=0 := by
  unfold cubeDirichletMode boxMode
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simp only [Finset.mem_univ,ite_true,cubeUpperFaceProjection,Function.update_self]
  have hd : cubeUpperFaceCoord Q i-cubeCorner Q i=cubeScaleFactor Q := by
    unfold cubeUpperFaceCoord cubeCorner
    ring
  rw [hd,mul_div_cancel_right₀ _ (cubeScaleFactor_pos' Q).ne']
  simpa only [mul_comm] using Real.sin_int_mul_pi (natVec q i)

/-- The finite Dirichlet polynomial is a genuine zero-trace Sobolev function. -/
noncomputable def dirichletPolynomialH10 {d : ℕ} (Q : TriadicCube d)
    (S : Finset (Fin d → ℕ)) (beta : (Fin d → ℕ) → ℝ) : H10Function (openCubeSet Q) :=
  H10Function.ofContDiffFaceZeroOnOpenCubeSetNoCompact Q (dirichlet_polynomial_contDiff Q S beta)
    (fun i x => by simp [dirichletPolynomial,dirichlet_mode_lower_face])
    (fun i x => by simp [dirichletPolynomial,dirichlet_mode_upper_face])

/-- This zero-trace realization equals the actual polynomial almost everywhere on the square. -/
theorem dirichlet_polynomial_H10_value {d : ℕ} (Q : TriadicCube d)
    (S : Finset (Fin d → ℕ)) (beta : (Fin d → ℕ) → ℝ) :
    (dirichletPolynomialH10 Q S beta).toH1Function.toFun =ᵐ[volumeMeasureOn (openCubeSet Q)]
      dirichletPolynomial Q S beta :=
  H10Function.ofContDiffFaceZeroOnOpenCubeSetNoCompact_toFun_ae Q _ _ _

end ASDExplicitGamma.Scalar
