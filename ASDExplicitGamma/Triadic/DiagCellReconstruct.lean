module

public import ASDExplicitGamma.Triadic.DiagCellPolynomial
public import ASDExplicitGamma.Triadic.DiagMesh

/-! Four-corner uniqueness for the actual centered source cell polynomials. -/

@[expose] public section

namespace ASDExplicitGamma.Triadic

open Homogenization

noncomputable section

/-- A closed physical corner of a source cell. -/
def diagCellCorner (Q : TriadicCube 2) (b : Fin 2 → Fin 2) : Vec 2 :=
  fun i => cubeCorner Q i + (b i).val * cubeScaleFactor Q

theorem diagCenteredCoordinate_corner (Q : TriadicCube 2) (b : Fin 2 → Fin 2) (i : Fin 2) :
    diagCenteredCoordinate Q i (diagCellCorner Q b) = (b i).val - (1/2:ℝ) := by
  unfold diagCenteredCoordinate diagCellCorner
  field_simp [(cubeScaleFactor_pos' Q).ne']
  ring

/-- Every centered cell polynomial is bilinear in the physical coordinates. -/
theorem diagBilinearPolynomial_bilinear (Q : TriadicCube 2) (c : Fin 4 → ℝ) :
    ∃ A B C D : ℝ, ∀ x : Vec 2, diagBilinearPolynomial Q c x =
      A+B*x 0+C*x 1+D*x 0*x 1 := by
  let a := cubeCorner Q 0 / cubeScaleFactor Q + 1/2
  let b := cubeCorner Q 1 / cubeScaleFactor Q + 1/2
  let L := cubeScaleFactor Q
  refine ⟨c 0-c 1*a-c 2*b+c 3*a*b, c 1/L-c 3*b/L,
    c 2/L-c 3*a/L, c 3/L^2, ?_⟩
  intro x
  rw [diagBilinearPolynomial_explicit]
  dsimp [diagCenteredCoordinate, a, b, L]
  ring

/-- Four exact vertex values determine all four bilinear coefficients. -/
theorem diagBilinear_coefficients_unique {r : ℝ} (hr : r ≠ 0) (a b : ℝ)
    (A B C D A' B' C' D' : ℝ)
    (h00 : A+B*a+C*b+D*a*b = A'+B'*a+C'*b+D'*a*b)
    (h10 : A+B*(a+r)+C*b+D*(a+r)*b = A'+B'*(a+r)+C'*b+D'*(a+r)*b)
    (h01 : A+B*a+C*(b+r)+D*a*(b+r) = A'+B'*a+C'*(b+r)+D'*a*(b+r))
    (h11 : A+B*(a+r)+C*(b+r)+D*(a+r)*(b+r) =
      A'+B'*(a+r)+C'*(b+r)+D'*(a+r)*(b+r)) :
    A=A' ∧ B=B' ∧ C=C' ∧ D=D' := by
  have hd : (D-D')*r^2 = 0 := by linear_combination h11-h10-h01+h00
  have hD : D=D' := sub_eq_zero.mp ((mul_eq_zero.mp hd).resolve_right (pow_ne_zero _ hr))
  subst D'
  have hb : (B-B')*r = 0 := by linear_combination h10-h00
  have hB : B=B' := sub_eq_zero.mp ((mul_eq_zero.mp hb).resolve_right hr)
  subst B'
  have hc : (C-C')*r = 0 := by linear_combination h01-h00
  have hC : C=C' := sub_eq_zero.mp ((mul_eq_zero.mp hc).resolve_right hr)
  subst C'
  have hA : A=A' := by linarith only [h00]
  exact ⟨hA, rfl, rfl, rfl⟩

/-- A bilinear source function with the same four physical values is this cell polynomial. -/
theorem diagBilinear_eq_polynomial_of_corners (Q : TriadicCube 2) (F : Vec 2 → ℝ)
    (c : Fin 4 → ℝ)
    (hF : ∃ A B C D : ℝ, ∀ x : Vec 2,
      (∀ i, cubeCorner Q i ≤ x i ∧ x i ≤ cubeCorner Q i + cubeScaleFactor Q) →
        F x = A+B*x 0+C*x 1+D*x 0*x 1)
    (hcorner : ∀ b : Fin 2 → Fin 2, F (diagCellCorner Q b) =
      diagBilinearPolynomial Q c (diagCellCorner Q b)) :
    ∀ x : Vec 2, (∀ i, cubeCorner Q i ≤ x i ∧ x i ≤ cubeCorner Q i + cubeScaleFactor Q) →
      F x = diagBilinearPolynomial Q c x := by
  obtain ⟨A, B, C, D, hF⟩ := hF
  obtain ⟨A', B', C', D', hP⟩ := diagBilinearPolynomial_bilinear Q c
  have hbound (b : Fin 2 → Fin 2) (i : Fin 2) :
      cubeCorner Q i ≤ diagCellCorner Q b i ∧
        diagCellCorner Q b i ≤ cubeCorner Q i+cubeScaleFactor Q := by
    have hp := cubeScaleFactor_pos' Q
    have hb : (b i).val = 0 ∨ (b i).val = 1 := by have := (b i).isLt; omega
    rcases hb with hb | hb <;> simp [diagCellCorner, hb, hp.le]
  have hvals (b : Fin 2 → Fin 2) := hcorner b
  simp_rw [hF _ (hbound _), hP] at hvals
  have h := diagBilinear_coefficients_unique (cubeScaleFactor_pos' Q).ne'
    (cubeCorner Q 0) (cubeCorner Q 1) A B C D A' B' C' D'
    (by simpa [diagCellCorner] using hvals ![0,0])
    (by simpa [diagCellCorner] using hvals ![1,0])
    (by simpa [diagCellCorner] using hvals ![0,1])
    (by simpa [diagCellCorner] using hvals ![1,1])
  rcases h with ⟨rfl, rfl, rfl, rfl⟩
  intro x hx
  rw [hF x hx, hP]

end

end ASDExplicitGamma.Triadic
