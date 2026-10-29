module

public import ASDExplicitGamma.Inverse.WeakHistoryIneq

/-! Finite-sup and discounted-history interfaces for finite inverse-root
families, used by the mixed-bridge observer history. -/
@[expose] public section

namespace ASDExplicitGamma.Inverse

open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Scalar ASDExplicitGamma.Variational

noncomputable section

theorem rawFiniteInverseDepthMax_lower_of_mem
    (s : Finset (TriadicCube 2)) {Q : TriadicCube 2}
    (hQ : Q ∈ s) (a : CoeffField 2) (sigma : ℝ) (j : ℕ) :
    sigma * lemmaVInverseDepthMax Q a j ≤
      rawFiniteInverseDepthMax s a sigma j := by
  unfold rawFiniteInverseDepthMax
  exact Algsuperdiff.Section3.Provider.ErrorComparison.le_finsetSupReal
    (α := TriadicCube 2) s (fun R => sigma * lemmaVInverseDepthMax R a j) hQ

theorem rawFiniteInverseHistoryMax_lower_of_mem
    (s : Finset (TriadicCube 2)) {Q : TriadicCube 2}
    (hQ : Q ∈ s) (a : CoeffField 2) (sigma : ℝ) :
    sigma * lemmaVInverseHistory Q a ((3 : ℝ) ^ (1 / 4 : ℝ)) ≤
      rawFiniteInverseHistoryMax s a sigma := by
  unfold rawFiniteInverseHistoryMax
  exact Algsuperdiff.Section3.Provider.ErrorComparison.le_finsetSupReal
    (α := TriadicCube 2) s
    (fun R => sigma * lemmaVInverseHistory R a ((3 : ℝ) ^ (1 / 4 : ℝ))) hQ

theorem raw_finite_inverse_depth_discount_bound_of_per_root_ellipticity
    (s : Finset (TriadicCube 2)) (hs : s.Nonempty) (a : CoeffField 2)
    (lam sigma : ℝ) (hsigma : 0 ≤ sigma)
    (hEll : ∀ Q ∈ s, ∃ Lam : ℝ,
      IsEllipticFieldOn lam Lam (openCubeSet Q) a) (j : ℕ) :
    Scalar.inverseHistoryDiscount ^ j * rawFiniteInverseDepthMax s a sigma j ≤
      rawFiniteInverseHistoryMax s a sigma := by
  let α := Scalar.inverseHistoryDiscount
  have hα := Scalar.inverse_history_discount_range
  change α ^ j * Book.Ch02.finsetSupReal s
      (fun Q => sigma * lemmaVInverseDepthMax Q a j) ≤ _
  rw [← Scalar.inverse_history_finset_max_mul s hs
    (fun Q => sigma * lemmaVInverseDepthMax Q a j) (α ^ j)
    (pow_pos hα.1 j)]
  change Book.Ch02.finsetSupReal s
      (fun Q => α ^ j * (sigma * lemmaVInverseDepthMax Q a j)) ≤
    Book.Ch02.finsetSupReal s
      (fun Q => sigma * lemmaVInverseHistory Q a
        ((3 : ℝ) ^ (1 / 4 : ℝ)))
  apply Book.Ch02.finsetSupReal_le _ hs
  intro Q hQ
  obtain ⟨Lam, hEllQ⟩ := hEll Q hQ
  have hlocal := actual_inverse_depth_discount_bound Q a hEllQ sigma hsigma j
  have hglobal := rawFiniteInverseHistoryMax_lower_of_mem s hQ a sigma
  exact hlocal.trans hglobal

end
end ASDExplicitGamma.Inverse
