module

public import ASDExplicitGamma.Native.Q3GridOverlap
public import ASDExplicitGamma.Native.VanishingBracketGridTranslation
public import ASDExplicitGamma.Native.HeatQuadraticMoments
public import ASDExplicitGamma.Gaussian.DerivativeLawValueCovariance
public import ASDExplicitGamma.Gaussian.SpatialKernelSupport

/-! The sharp support-overlap estimate for q3 child-center covariance vectors. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open MeasureTheory Homogenization ASDExplicitGamma.Gaussian
open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open scoped RealInnerProductSpace

/-- The source's q3 support-overlap clock controls the averaged Hilbert kernel
of arbitrary weighted child-center values on an `s`-level grid. -/
theorem nativeHeat_q3GridSectionAverage_sq_le_support_overlap
    (s n : ℕ) (hn : 1 ≤ n) (β : ℝ)
    (t : Fin (3^s) × Fin (3^s) → ℝ) :
    ‖(((Finset.univ : Finset (Fin (3^s) × Fin (3^s))).card : ℝ)⁻¹) •
        ∑ ij : Fin (3^s) × Fin (3^s),
          t ij • q3Section β (q3GridKernelScale s n) h3Zero
            (q3GridRectangleCenter s ij)‖ ^ 2 ≤
      q3GridOverlapFactor s n *
        (((Finset.univ : Finset (Fin (3^s) × Fin (3^s))).card : ℝ)⁻¹) *
          ∑ ij : Fin (3^s) × Fin (3^s), (t ij) ^ 2 * β ^ 2 := by
  classical
  let I := Fin (3^s) × Fin (3^s)
  let S : Finset I := Finset.univ
  let U : Vec 2 → Finset I := q3GridActiveFinset s n
  let N : ℝ := (S.card : ℝ)
  let C : ℝ := q3GridOverlapFactor s n
  let M : ℝ := C * N
  let A : I → Set (Vec 2) := q3GridExpandedSupport s n
  let L : I → {l : ℝ // 0 < l} := fun _ => q3GridKernelScale s n
  let X : I → WhiteNoise := fun ij =>
    t ij • q3Section β (L ij) h3Zero (q3GridRectangleCenter s ij)
  have hNcard : S.card = (3^s)^2 := by
    simp [S, I, pow_two, Fintype.card_prod]
  have hNpos : 0 < N := by
    dsimp [N]
    rw [hNcard]
    positivity
  have hNreal : N = ((3 : ℝ)^s)^2 := by
    dsimp [N]
    rw [hNcard]
    push_cast
    rfl
  have hactive : ∀ x ij, ij ∈ U x ↔ x ∈ A ij := by
    intro x ij
    simp [U, A, q3GridActiveFinset]
  have hratio (x : Vec 2) : ((U x).card : ℝ) / N ≤ C := by
    by_cases hns : n ≤ s
    · have hh := q3GridActiveFinset_card_ratio_le s n hn hns x
      rw [← hNreal] at hh
      dsimp [C]
      simpa [U] using hh
    · have hsub : s - n = 0 := by omega
      have hC : C = 1 := by
        dsimp [C, q3GridOverlapFactor]
        rw [hsub]
        norm_num
      have hcard : ((U x).card : ℝ) ≤ N := by
        dsimp [N]
        exact_mod_cast (Finset.card_le_univ (U x))
      have hratioOne : ((U x).card : ℝ) / N ≤ 1 :=
        (div_le_iff₀ hNpos).2 (by nlinarith [hcard])
      rw [hC]
      exact hratioOne
  have hM : 0 ≤ M := by
    dsimp [M, C, q3GridOverlapFactor]
    positivity
  have hoverlap (x : Vec 2) : ((S ∩ U x).card : ℝ) ≤ M := by
    have hcard : (S ∩ U x).card = (U x).card := by simp [S]
    rw [hcard]
    dsimp [M, C]
    exact (div_le_iff₀ hNpos).mp (hratio x)
  have hzero (ij : I) (hij : ij ∈ S) :
      ∀ᵐ y : Vec 2 ∂(volume : Measure (Vec 2)), y ∉ A ij → X ij y = 0 := by
    have hrepr :=
      (q3SectionFunction_memLp β (L ij) h3Zero
        (q3GridRectangleCenter s ij)).coeFn_toLp
    have hX : X ij = (t ij) • q3Section β (L ij) h3Zero
        (q3GridRectangleCenter s ij) := rfl
    have hsmul : ∀ᵐ y : Vec 2 ∂(volume : Measure (Vec 2)),
        ((t ij) • q3Section β (L ij) h3Zero
          (q3GridRectangleCenter s ij)) y =
          (t ij) * q3Section β (L ij) h3Zero
            (q3GridRectangleCenter s ij) y := by
      filter_upwards [Lp.coeFn_smul (t ij)
        (q3Section β (L ij) h3Zero (q3GridRectangleCenter s ij))] with y hy
      simpa only [Pi.smul_apply, smul_eq_mul] using hy
    filter_upwards [hrepr, hsmul] with y hy hs hyA
    change q3Section β (L ij) h3Zero
      (q3GridRectangleCenter s ij) y =
      q3SectionFunction β (L ij) h3Zero
        (q3GridRectangleCenter s ij) y at hy
    have hker : q3SectionFunction β (L ij) h3Zero
        (q3GridRectangleCenter s ij) y = 0 := by
      apply q3SectionFunction_zero_outside_expandedRectangle
      simpa [A, q3GridExpandedSupport, q3ExpandedRectangle, L] using hyA
    rw [hX]
    calc
      ((t ij) • q3Section β (L ij) h3Zero
        (q3GridRectangleCenter s ij)) y =
          (t ij) * q3Section β (L ij) h3Zero
            (q3GridRectangleCenter s ij) y := hs
      _ = 0 := by simp [hy, hker]
  have hSpos : 0 < (S.card : ℝ) := by
    dsimp [N] at hNpos
    exact hNpos
  have hgeneric := whiteNoise_average_sq_le_supportOverlap S X A U M hM
    hSpos hactive hzero
    (Filter.Eventually.of_forall hoverlap)
  have hnorm (ij : I) : ‖X ij‖ ^ 2 = (t ij) ^ 2 * β ^ 2 := by
    dsimp [X]
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, q3Section_norm_sq]
  have hright : M * ((S.card : ℝ)⁻¹) ^ 2 *
      ∑ ij ∈ S, ‖X ij‖ ^ 2 =
        C * ((S.card : ℝ)⁻¹) *
          ∑ ij : I, (t ij) ^ 2 * β ^ 2 := by
    rw [show M = C * ((S.card : ℝ)) by rfl]
    have hsum : (∑ ij ∈ S, ‖X ij‖ ^ 2) =
        ∑ ij : I, (t ij) ^ 2 * β ^ 2 := by
      apply Finset.sum_congr rfl
      intro ij hij
      rw [hnorm]
    rw [hsum]
    have hcard : (∑ ij ∈ S, (t ij) ^ 2 * β ^ 2) =
        ∑ ij : I, (t ij) ^ 2 * β ^ 2 := by rfl
    rw [hcard]
    dsimp [N] at hNpos
    field_simp [ne_of_gt hNpos]
    have hcomm : (∑ ij : I, (t ij) ^ 2 * β ^ 2) =
        ∑ ij : I, β ^ 2 * (t ij) ^ 2 := by
      apply Finset.sum_congr rfl
      intro ij _
      ring
    rw [hcomm]
  simpa [S, N, I, X, C, L] using hgeneric.trans_eq hright

/-- The squared Hilbert norm of a finite weighted section sum is its full Gram
quadratic form. -/
theorem nativeHeat_norm_sum_smul_sq {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (u : ι → E) (a : ι → ℝ) :
    ‖∑ i, a i • u i‖ ^ 2 =
      ∑ i, ∑ j, a i * a j * ⟪u i, u j⟫ := by
  calc
    ‖∑ i, a i • u i‖ ^ 2 =
        ⟪∑ i, a i • u i, ∑ j, a j • u j⟫ := (real_inner_self_eq_norm_sq _).symm
    _ = ∑ i, ∑ j, ⟪a i • u i, a j • u j⟫ := by
      rw [sum_inner]
      apply Finset.sum_congr rfl
      intro i _
      exact inner_sum Finset.univ (fun j => a j • u j) (a i • u i)
    _ = ∑ i, ∑ j, a i * a j * ⟪u i, u j⟫ := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [real_inner_smul_left, real_inner_smul_right]
      ring

/-- The physical q3 grid kernel has the signed scale `3^(n-s)` even when the
shell is coarser than the child grid. -/
theorem nativeHeat_q3GridKernelScale_eq_zpow_any (s n : ℕ) :
    (q3GridKernelScale s n).1 = (3 : ℝ)^((n : ℤ) - (s : ℤ)) := by
  dsimp [q3GridKernelScale]
  rw [← zpow_natCast, ← zpow_natCast,
    ← zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0)]

/-- Squaring the physical q3 shell amplitude gives its exact covariance
prefactor. -/
theorem nativeHeat_q3ShellAmplitude_sq (h γ : ℝ) (k : ℤ) :
    (h * (3 : ℝ)^(γ * (k : ℝ))) ^ 2 = h ^ 2 * (3 : ℝ)^(2 * γ * (k : ℝ)) := by
  have hpow : ((3 : ℝ)^(γ * (k : ℝ))) ^ 2 =
      (3 : ℝ)^(2 * γ * (k : ℝ)) := by
    calc
      ((3 : ℝ)^(γ * (k : ℝ))) ^ 2 =
          (3 : ℝ)^((γ * (k : ℝ)) * 2) :=
            (Real.rpow_mul_natCast (x := (3 : ℝ)) (by norm_num) _ _).symm
      _ = (3 : ℝ)^(2 * γ * (k : ℝ)) := by congr 1; ring
  rw [mul_pow]
  exact congrArg (fun x : ℝ => h ^ 2 * x) hpow

end ASDExplicitGamma.Native
