module

public import ASDExplicitGamma.Gaussian.H3KernelSections
public import ASDExplicitGamma.Gaussian.Q3KernelLipschitz
public import Mathlib.MeasureTheory.Constructions.Pi

/-! # The actual spatial derivative of each continuous q3 section coordinate -/

@[expose] public section

open MeasureTheory Homogenization Set Filter
open scoped Topology RealInnerProductSpace

namespace ASDExplicitGamma.Gaussian

/-- The spatial derivative is expressed in the two successor weak-derivative kernels. -/
noncomputable def q3SectionDerivative (b : ℝ) (L : {l : ℝ // 0 < l}) (a : H3Index)
    (ha : a.1.1.val + a.1.2.val ≤ 2) (x y : Vec 2) : Vec 2 →L[ℝ] ℝ :=
  q3SectionFunction b L (h3Next a 0 ha) x y • ContinuousLinearMap.proj 0 +
    q3SectionFunction b L (h3Next a 1 ha) x y • ContinuousLinearMap.proj 1

theorem q3SectionFunction_hasFDerivAt (b : ℝ) (L : {l : ℝ // 0 < l}) (a : H3Index)
    (ha : a.1.1.val + a.1.2.val ≤ 2) (x y : Vec 2)
    (hy : ∀ i : Fin 2, |(x i - y i) / L.1| ≠ 1 / 2) :
    HasFDerivAt (fun z => q3SectionFunction b L a z y)
      (q3SectionDerivative b L a ha x y) x := by
  have harg (i : Fin 2) : HasFDerivAt (fun z : Vec 2 => (z i - y i) / L.1)
      (L.1⁻¹ • (ContinuousLinearMap.proj i : Vec 2 →L[ℝ] ℝ)) x := by
    convert (((ContinuousLinearMap.proj i : Vec 2 →L[ℝ] ℝ).hasFDerivAt).sub_const (y i)).const_mul L.1⁻¹ using 1
    ext z
    dsimp
    ring
  have h₀ := (q3Derivative_hasDerivAt a.1.1 (by omega) (hy 0)).comp_hasFDerivAt x (harg 0)
  have h₁ := (q3Derivative_hasDerivAt a.1.2 (by omega) (hy 1)).comp_hasFDerivAt x (harg 1)
  have hh := (h₀.mul h₁).const_mul (b / L.1 ^ (1 + a.1.1.val + a.1.2.val))
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  convert hh using 1
  · rfl
  · ext h
    simp only [q3SectionDerivative, q3SectionFunction, h3Next, h10, ↓reduceIte,
      add_apply, smul_apply,
      ContinuousLinearMap.proj_apply, smul_eq_mul, Function.comp_apply]
    have he₀ : 1 + (a.1.1.val + 1) + a.1.2.val = (1 + a.1.1.val + a.1.2.val) + 1 := by omega
    have he₁ : 1 + a.1.1.val + (a.1.2.val + 1) = (1 + a.1.1.val + a.1.2.val) + 1 := by omega
    simp only [he₀, he₁, pow_succ, div_eq_mul_inv, mul_inv_rev]
    ring

/-- For every fixed spatial point the exceptional white-noise hyperplanes have zero measure. -/
theorem q3SectionFunction_hasFDerivAt_ae (b : ℝ) (L : {l : ℝ // 0 < l}) (a : H3Index)
    (ha : a.1.1.val + a.1.2.val ≤ 2) (x : Vec 2) :
    ∀ᵐ y, HasFDerivAt (fun z => q3SectionFunction b L a z y)
      (q3SectionDerivative b L a ha x y) x := by
  have hz (i : Fin 2) (c : ℝ) : ∀ᵐ y : Vec 2, y i ≠ c := by
    rw [ae_iff]
    simp only [not_not]
    rw [show (volume : Measure (Vec 2)) = Measure.pi (fun _ : Fin 2 => (volume : Measure ℝ)) from volume_pi]
    exact Measure.pi_hyperplane (fun _ : Fin 2 => (volume : Measure ℝ)) i c
  filter_upwards [hz 0 (x 0 - L.1 / 2), hz 0 (x 0 + L.1 / 2),
    hz 1 (x 1 - L.1 / 2), hz 1 (x 1 + L.1 / 2)] with y h₀m h₀p h₁m h₁p
  apply q3SectionFunction_hasFDerivAt b L a ha x y
  intro i he
  have hh := (abs_eq (by norm_num : (0 : ℝ) ≤ 1 / 2)).mp he
  have hL := L.2.ne'
  rcases hh with hh | hh
  · have heq : y i = x i - L.1 / 2 := by
      have := (div_eq_iff hL).mp hh
      linarith
    fin_cases i <;> contradiction
  · have heq : y i = x i + L.1 / 2 := by
      have := (div_eq_iff hL).mp hh
      linarith
    fin_cases i <;> contradiction

end ASDExplicitGamma.Gaussian
