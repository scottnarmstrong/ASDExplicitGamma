module

public import ASDExplicitGamma.Gaussian.H3KernelSections
public import Mathlib.Analysis.Calculus.ParametricIntegral

/-! # Differentiation of a locally supported convolution against an L² input -/

@[expose] public section

open MeasureTheory Homogenization Set Filter
open scoped Topology NNReal RealInnerProductSpace

namespace ASDExplicitGamma.Gaussian

/-- Compact localization supplies an integrable Lipschitz envelope from ordinary white-noise
L². The derivative hypothesis is almost everywhere, allowing derivative-kernel cutoff jumps. -/
theorem hasFDerivAt_localized_kernel_integral
    (k : Vec 2 → Vec 2 → ℝ) (k' : Vec 2 → Vec 2 →L[ℝ] ℝ)
    (x : Vec 2) (u : WhiteNoise) (Q : Set (Vec 2)) (hQ : IsCompact Q)
    (s : Set (Vec 2)) (hs : s ∈ 𝓝 x) (C : ℝ≥0)
    (hk : ∀ z, Measurable (k z)) (hk2 : MemLp (k x) 2 volume)
    (hk' : AEStronglyMeasurable k' volume)
    (hlip : ∀ y, LipschitzWith C (fun z => k z y))
    (hsupp : ∀ z ∈ s, ∀ y ∉ Q, k z y = 0)
    (hd : ∀ᵐ y, HasFDerivAt (fun z => k z y) (k' y) x) :
    Integrable (fun y => u y • k' y) ∧
      HasFDerivAt (fun z => ∫ y, k z y * u y) (∫ y, u y • k' y) x := by
  let B : Vec 2 → ℝ := Q.indicator (fun y => (C : ℝ) * ‖u y‖)
  have hBQ : IntegrableOn (fun y => (C : ℝ) * ‖u y‖) Q :=
    (((Lp.memLp u).locallyIntegrable (by norm_num)).integrableOn_isCompact hQ).norm.const_mul (C : ℝ)
  have hB : Integrable B := hBQ.integrable_indicator hQ.measurableSet
  have hF : ∀ᶠ z in 𝓝 x, AEStronglyMeasurable (fun y => k z y * u y) :=
    Eventually.of_forall fun z => (hk z).aestronglyMeasurable.mul (Lp.memLp u).aestronglyMeasurable
  have hFi : Integrable (fun y => k x y * u y) := hk2.integrable_mul (Lp.memLp u)
  have hFm : AEStronglyMeasurable (fun y => u y • k' y) :=
    (Lp.memLp u).aestronglyMeasurable.smul hk'
  have hL : ∀ᵐ y, LipschitzOnWith (Real.nnabs (B y)) (fun z => k z y * u y) s := by
    exact Eventually.of_forall fun y => by
      apply lipschitzOnWith_iff_norm_sub_le.mpr
      intro z hz w hw
      by_cases hy : y ∈ Q
      · have he : (Real.nnabs (B y) : ℝ) = (C : ℝ) * ‖u y‖ := by
          simp only [B, indicator_of_mem hy, Real.coe_nnabs]
          exact abs_of_nonneg (mul_nonneg C.2 (norm_nonneg _))
        rw [he, ← sub_mul, norm_mul]
        calc
          ‖k z y - k w y‖ * ‖u y‖ ≤ ((C : ℝ) * ‖z - w‖) * ‖u y‖ :=
            mul_le_mul_of_nonneg_right ((hlip y).norm_sub_le z w) (norm_nonneg _)
          _ = _ := by ring
      · rw [hsupp z hz y hy, hsupp w hw y hy]
        simp only [zero_mul, sub_self, norm_zero]
        exact mul_nonneg (Real.nnabs (B y)).2 (norm_nonneg _)
  have hD : ∀ᵐ y, HasFDerivAt (fun z => k z y * u y) (u y • k' y) x := by
    filter_upwards [hd] with y hy
    convert hy.const_smul (u y) using 1
    ext z
    exact mul_comm _ _
  exact hasFDerivAt_integral_of_dominated_loc_of_lip hs hF hFi hFm hL hB hD

end ASDExplicitGamma.Gaussian
