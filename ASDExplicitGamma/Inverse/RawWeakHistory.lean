module

public import ASDExplicitGamma.Scalar.InverseHistory
public import ASDExplicitGamma.Scalar.InverseHistoryBlocks
public import ASDExplicitGamma.Variational.ProjectedSource
public import Mathlib.Analysis.SpecificLimits.Basic

/-! The corrected intrinsic weak-history normalization, separated from bank estimates. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization Variational MeasureTheory

noncomputable section

/-- The normalized complete inverse history of a nonnegative depth sequence. -/
def rawCompleteInverseHistory (b : ℕ → ℝ) : ℝ :=
  (1 - Scalar.inverseHistoryDiscount) *
    ∑' j : ℕ, Scalar.inverseHistoryDiscount ^ j * b j

/-- The weak history uses the quarter-discount normalization. -/
def rawWeakTraceHistory (T : ℕ → ℝ) : ℝ :=
  (1 - Scalar.inverseHistoryDiscount) *
    ∑' j : ℕ, Scalar.inverseHistoryDiscount ^ j * T j

/-- The local proxy uses squared weights and depthwise inverse maxima. -/
def rawWeakTraceProxy (b T : ℕ → ℝ) : ℝ :=
  (1 - Scalar.inverseHistoryDiscount ^ 2) *
    ∑' j : ℕ,
      Scalar.inverseHistoryDiscount ^ (2 * j) * b j * T j

/-- The depthwise inverse maximum over a finite family of source roots. -/
noncomputable def rawFiniteInverseDepthMax (s : Finset (TriadicCube 2))
    (a : CoeffField 2) (sigma : ℝ) (j : ℕ) : ℝ :=
  Book.Ch02.finsetSupReal s (fun Q => sigma * lemmaVInverseDepthMax Q a j)

/-- The actual complete inverse-history maximum over the same finite family. -/
noncomputable def rawFiniteInverseHistoryMax (s : Finset (TriadicCube 2))
    (a : CoeffField 2) (sigma : ℝ) : ℝ :=
  Book.Ch02.finsetSupReal s
    (fun Q => sigma * lemmaVInverseHistory Q a ((3 : ℝ) ^ (1 / 4 : ℝ)))

/-- Refinement monotonicity makes the complete history dominate every discounted depth maximum. -/
theorem raw_inverse_depth_discount_bound (b : ℕ → ℝ) (j : ℕ)
    (hb : Monotone b) (hb0 : ∀ d, 0 ≤ b d)
    (hs : Summable (fun d : ℕ => Scalar.inverseHistoryDiscount ^ d * b d)) :
    Scalar.inverseHistoryDiscount ^ j * b j ≤ rawCompleteInverseHistory b := by
  let α := Scalar.inverseHistoryDiscount
  have hα := Scalar.inverse_history_discount_range
  have hα0 : 0 ≤ α := hα.1.le
  have hα1 : α < 1 := hα.2
  have hGeom : Summable (fun d : ℕ => α ^ d) :=
    summable_geometric_of_lt_one hα0 hα1
  have hTailGeom : Summable (fun d : ℕ => if j ≤ d then α ^ d else 0) := by
    have hEq : (fun d : ℕ => if j ≤ d then α ^ d else 0) =
        ({d | j ≤ d}.indicator fun d => α ^ d) := by
      funext d
      rw [Set.indicator_apply]
      simp only [Set.mem_ofPred_eq]
    rw [hEq]
    exact hGeom.indicator {d | j ≤ d}
  have hTailGeomZero : (∑ i ∈ Finset.range j, (if j ≤ i then α ^ i else 0)) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have hij : i < j := Finset.mem_range.mp hi
    simp [not_le_of_gt hij]
  have hTailGeomEq : (∑' d : ℕ, if j ≤ d then α ^ d else 0) = α ^ j * (1 - α)⁻¹ := by
    have hdecomp := hTailGeom.sum_add_tsum_nat_add j
    rw [hTailGeomZero, zero_add] at hdecomp
    rw [hdecomp.symm]
    calc
      (∑' n : ℕ, if j ≤ n + j then α ^ (n + j) else 0) =
          ∑' n : ℕ, α ^ j * α ^ n := by
        apply tsum_congr
        intro n
        have hjn : j ≤ n + j := by omega
        simp only [hjn, ite_true, pow_add]
        ring
      _ = α ^ j * ∑' n : ℕ, α ^ n := tsum_mul_left
      _ = α ^ j * (1 - α)⁻¹ := by
        rw [tsum_geometric_of_lt_one hα0 hα1]
  have hTail : Summable (fun d : ℕ => if j ≤ d then α ^ d * b j else 0) := by
    have hmul := hGeom.mul_right (b j)
    have hEq : (fun d : ℕ => if j ≤ d then α ^ d * b j else 0) =
        ({d | j ≤ d}.indicator fun d => α ^ d * b j) := by
      funext d
      rw [Set.indicator_apply]
      simp only [Set.mem_ofPred_eq]
    rw [hEq]
    exact hmul.indicator {d | j ≤ d}
  have hTailEq :
      (∑' d : ℕ, if j ≤ d then α ^ d * b j else 0) =
        (α ^ j * b j) * (1 - α)⁻¹ := by
    calc
      _ = ∑' d : ℕ, (if j ≤ d then α ^ d else 0) * b j := by
        apply tsum_congr
        intro d
        by_cases hd : j ≤ d <;> simp [hd]
      _ = (∑' d : ℕ, if j ≤ d then α ^ d else 0) * b j := tsum_mul_right
      _ = (α ^ j * (1 - α)⁻¹) * b j := by rw [hTailGeomEq]
      _ = (α ^ j * b j) * (1 - α)⁻¹ := by ring
  have hTailLe :
      (∑' d : ℕ, if j ≤ d then α ^ d * b j else 0) ≤
        ∑' d : ℕ, α ^ d * b d := by
    exact hTail.tsum_le_tsum (fun d => by
      by_cases hd : j ≤ d
      · simp only [hd, ite_true]
        exact mul_le_mul_of_nonneg_left (hb hd) (pow_nonneg hα0 d)
      · simp [hd, mul_nonneg (pow_nonneg hα0 d) (hb0 d)]) hs
  have hFactor : 0 ≤ 1 - α := sub_nonneg.mpr hα1.le
  have hScaled := mul_le_mul_of_nonneg_left hTailLe hFactor
  rw [hTailEq] at hScaled
  change (1 - α) * ((α ^ j * b j) * (1 - α)⁻¹) ≤
    (1 - α) * (∑' d : ℕ, α ^ d * b d) at hScaled
  have hCancel : (1 - α) * ((α ^ j * b j) * (1 - α)⁻¹) = α ^ j * b j := by
    have hne : 1 - α ≠ 0 := (sub_pos.mpr hα1).ne'
    field_simp
  rw [hCancel] at hScaled
  exact hScaled

/-- The sequence lemma applies to the actual framed Lemma-V inverse maxima. -/
theorem actual_inverse_depth_discount_bound (Q : TriadicCube 2) (a : CoeffField 2)
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (sigma : ℝ) (hsigma : 0 ≤ sigma) (j : ℕ) :
    Scalar.inverseHistoryDiscount ^ j * (sigma * lemmaVInverseDepthMax Q a j) ≤
      sigma * lemmaVInverseHistory Q a ((3 : ℝ) ^ (1 / 4 : ℝ)) := by
  let b : ℕ → ℝ := fun d => sigma * lemmaVInverseDepthMax Q a d
  have hb0 (d : ℕ) : 0 ≤ b d :=
    mul_nonneg hsigma (lemmaVInverseDepthMax_nonneg Q a d)
  have hstep (d : ℕ) : b d ≤ b (d + 1) :=
    mul_le_mul_of_nonneg_left (lemmaVInverseDepthMax_le_succ Q hEll d) hsigma
  have hb : Monotone b := monotone_nat_of_le_succ hstep
  have hs : Summable (fun d : ℕ => Scalar.inverseHistoryDiscount ^ d * b d) := by
    have h := Scalar.inverse_history_weighted_summable Q a hEll sigma
    convert h using 1
    funext d
    dsimp [b]
    ring
  have hEq : rawCompleteInverseHistory b =
      sigma * lemmaVInverseHistory Q a ((3 : ℝ) ^ (1 / 4 : ℝ)) := by
    have hα : Scalar.inverseHistoryDiscount = ((3 : ℝ) ^ (1 / 4 : ℝ))⁻¹ :=
      Scalar.inverse_history_discount_eq
    rw [rawCompleteInverseHistory, lemmaVInverseHistory, hα]
    calc
      (1 - ((3 : ℝ) ^ (1 / 4 : ℝ))⁻¹) *
          (∑' d : ℕ, ((3 : ℝ) ^ (1 / 4 : ℝ))⁻¹ ^ d * b d) =
        (1 - ((3 : ℝ) ^ (1 / 4 : ℝ))⁻¹) *
          (sigma * ∑' d : ℕ,
            ((3 : ℝ) ^ (1 / 4 : ℝ))⁻¹ ^ d * lemmaVInverseDepthMax Q a d) := by
        congr 2
        calc
          (∑' d : ℕ, ((3 : ℝ) ^ (1 / 4 : ℝ))⁻¹ ^ d * b d) =
              ∑' d : ℕ, sigma * (((3 : ℝ) ^ (1 / 4 : ℝ))⁻¹ ^ d *
                lemmaVInverseDepthMax Q a d) := by
            apply tsum_congr
            intro d
            simp only [b]
            ring
          _ = _ := tsum_mul_left
      _ = sigma * ((1 - ((3 : ℝ) ^ (1 / 4 : ℝ))⁻¹) *
          ∑' d : ℕ, ((3 : ℝ) ^ (1 / 4 : ℝ))⁻¹ ^ d *
            lemmaVInverseDepthMax Q a d) := by ring
  have hDepth := raw_inverse_depth_discount_bound b j hb hb0 hs
  rw [hEq] at hDepth
  simpa [b] using hDepth

/-- The corrected weak-history estimate: squared local weights are bounded by
the complete inverse history times the weak history with constant `1 + α`. -/
theorem raw_weak_trace_proxy_le (b T : ℕ → ℝ) (H : ℝ)
    (hdepth : ∀ j, Scalar.inverseHistoryDiscount ^ j * b j ≤ H)
    (hT : ∀ j, 0 ≤ T j)
    (hProxy : Summable (fun j : ℕ =>
      Scalar.inverseHistoryDiscount ^ (2 * j) * b j * T j))
    (hTrace : Summable (fun j : ℕ => Scalar.inverseHistoryDiscount ^ j * T j)) :
    rawWeakTraceProxy b T ≤ (1 + Scalar.inverseHistoryDiscount) * H * rawWeakTraceHistory T := by
  let α := Scalar.inverseHistoryDiscount
  have hα := Scalar.inverse_history_discount_range
  have hα0 : 0 ≤ α := hα.1.le
  have hα1 : α < 1 := hα.2
  have hProxyTerm (j : ℕ) : α ^ (2 * j) * b j * T j ≤ α ^ j * H * T j := by
    have hmul := mul_le_mul_of_nonneg_right (hdepth j)
      (mul_nonneg (pow_nonneg hα0 j) (hT j))
    calc
      α ^ (2 * j) * b j * T j = (α ^ j * b j) * (α ^ j * T j) := by
        rw [show 2 * j = j + j by omega, pow_add]
        ring
      _ ≤ H * (α ^ j * T j) := hmul
      _ = α ^ j * H * T j := by ring
  have hTraceRight : Summable (fun j : ℕ => α ^ j * H * T j) := by
    have h := hTrace.mul_left H
    convert h using 1
    funext j
    ring
  have hsum := hProxy.tsum_le_tsum hProxyTerm hTraceRight
  have hCoef : 0 ≤ 1 - α ^ 2 := by
    have hpow : α ^ 2 ≤ 1 := (pow_le_one₀ hα0 hα1.le)
    linarith
  have hTraceFactor :
      (∑' j : ℕ, α ^ j * H * T j) = H * (∑' j : ℕ, α ^ j * T j) := by
    calc
      _ = ∑' j : ℕ, H * (α ^ j * T j) := by
        apply tsum_congr
        intro j
        ring
      _ = _ := hTrace.tsum_mul_left H
  unfold rawWeakTraceProxy rawWeakTraceHistory
  calc
    (1 - Scalar.inverseHistoryDiscount ^ 2) *
        (∑' j : ℕ, Scalar.inverseHistoryDiscount ^ (2 * j) * b j * T j) ≤
      (1 - Scalar.inverseHistoryDiscount ^ 2) *
        (∑' j : ℕ, Scalar.inverseHistoryDiscount ^ j * H * T j) :=
      mul_le_mul_of_nonneg_left hsum hCoef
    _ = (1 + Scalar.inverseHistoryDiscount) * H *
        ((1 - Scalar.inverseHistoryDiscount) *
          ∑' j : ℕ, Scalar.inverseHistoryDiscount ^ j * T j) := by
      rw [hTraceFactor]
      ring

/-- The corrected proxy inequality holds almost everywhere for random depth
profiles, once the source history and trace series are pointwise summable. -/
theorem raw_weak_trace_proxy_le_ae {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (b T : Ω → ℕ → ℝ) (Bstar : Ω → ℝ)
    (hdepth : ∀ᵐ ω ∂μ, ∀ j,
      Scalar.inverseHistoryDiscount ^ j * b ω j ≤ Bstar ω)
    (hT : ∀ᵐ ω ∂μ, ∀ j, 0 ≤ T ω j)
    (hProxy : ∀ᵐ ω ∂μ, Summable (fun j : ℕ =>
      Scalar.inverseHistoryDiscount ^ (2 * j) * b ω j * T ω j))
    (hTrace : ∀ᵐ ω ∂μ, Summable (fun j : ℕ =>
      Scalar.inverseHistoryDiscount ^ j * T ω j)) :
    ∀ᵐ ω ∂μ,
      rawWeakTraceProxy (b ω) (T ω) ≤
        (1 + Scalar.inverseHistoryDiscount) * Bstar ω * rawWeakTraceHistory (T ω) := by
  filter_upwards [hdepth, hT, hProxy, hTrace] with ω hdepthω hTω hProxyω hTraceω
  exact raw_weak_trace_proxy_le (b ω) (T ω) (Bstar ω) hdepthω hTω hProxyω hTraceω

end
end ASDExplicitGamma.Inverse
