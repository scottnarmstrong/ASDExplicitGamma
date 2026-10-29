module

public import ASDExplicitGamma.Triadic.HilbertOperatorResidual
public import ASDExplicitGamma.Triadic.HilbertProductSequence

/-! Exact general-weight positive Haar product bound for Hilbert and operator fields. -/

@[expose] public section
namespace ASDExplicitGamma.Triadic
open Homogenization MeasureTheory
open scoped BigOperators ENNReal
noncomputable section

/-- TR-PRODUCT for arbitrary Hilbert-valued positive-Haar input and a genuine
operator W^{1,∞} multiplier, with explicit essential supremum bounds. -/
theorem hilbert_positive_product_of_bounds {d : ℕ} {Q : TriadicCube d} {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]
    (b : HilbertOperatorW1Infinity Q H K) {q : ℝ} (hqgt : 1 < q) (hq9' : q < 9)
    {f : Vec d → H} (hf : MemLp f 2 (normalizedCubeMeasure Q))
    (hP : Summable (fun k => q^(k+1)*hilbertEnergy Q (hilbertCubeIncrement Q (k+1) f)))
    {M D : ℝ} (hM : 0 ≤ M) (hD : 0 ≤ D)
    (hb : ∀ᵐ x ∂normalizedCubeMeasure Q, ‖b.toFun x‖ ≤ M)
    (hdb : ∀ᵐ x ∂normalizedCubeMeasure Q, (∑ i, ‖b.grad x i‖^2) ≤ D^2) :
    Summable (fun k => q^(k+1)*hilbertEnergy Q (hilbertCubeIncrement Q (k+1) (fun x => b.toFun x (f x)))) ∧
    hilbertPositiveHaarNorm Q q (fun x => b.toFun x (f x)) ≤ M*hilbertPositiveHaarNorm Q q f+
      cubeScaleFactor Q*Real.sqrt (haarPoincareM2 q)*D*hilbertL2Norm Q f := by
  let δ : ℝ := q - 1
  let R : ℝ := cubeScaleFactor Q
  let E : ℝ := hilbertEnergy Q f
  let F : Vec d → K := fun x => b.toFun x (f x)
  let Fres : ℕ → Vec d → K := fun j x => F x - hilbertCubeProjection Q j F x
  let α : ℕ → ℝ := fun j => Real.sqrt (δ * q ^ j)
  let β : ℕ → ℝ := fun j => (R / ((3 : ℝ) ^ j * Real.pi)) * D * Real.sqrt E
  let a : ℕ → ℝ := fun n => Nat.casesOn n
    (M * Real.sqrt E) (fun j => α j * (M * Real.sqrt
      (hilbertEnergy Q (fun x => f x - hilbertCubeProjection Q j f x))))
  let bseq : ℕ → ℝ := fun n => Nat.casesOn n 0 (fun j => α j * β j)
  let c : ℕ → ℝ := fun n => Nat.casesOn n
    (Real.sqrt (hilbertEnergy Q F))
    (fun j => α j * Real.sqrt (hilbertEnergy Q (Fres j)))
  have hqpos : 0 < q := zero_lt_one.trans hqgt
  have hδ : 0 < δ := sub_pos.mpr hqgt
  have hδnonneg : 0 ≤ δ := hδ.le
  have hq9 : q/9 < 1 := (div_lt_one (by norm_num)).2 hq9'
  have hR : 0 < R := cubeScaleFactor_pos' Q
  have hE : 0 ≤ E := by dsimp [E]; exact hilbertEnergy_nonneg Q f
  have hpos := (hilbert_sensitivity_tail_of_weight Q hqgt hf hP).1
  have hFmem : MemLp F 2 (normalizedCubeMeasure Q) := b.product_memLp hf
  have hresVecNonneg : ∀ j, 0 ≤ hilbertEnergy Q (Fres j) := by
    intro j
    exact hilbertEnergy_nonneg Q _
  have hEresNonneg : ∀ j, 0 ≤ hilbertEnergy Q
      (fun x => f x - hilbertCubeProjection Q j f x) := by
    intro j
    exact hilbertEnergy_nonneg Q _
  have hrootBound : Real.sqrt (hilbertEnergy Q F) ≤ M * Real.sqrt E := by
    have hmul := hilbert_operator_product_energy_le Q hM hb hf hFmem
    apply (Real.sqrt_le_iff).2
    refine ⟨?_, ?_⟩
    · positivity
    · calc
        hilbertEnergy Q F ≤
            M ^ 2 * hilbertEnergy Q f := hmul
        _ = (M * Real.sqrt (hilbertEnergy Q f)) ^ 2 := by
              rw [mul_pow, Real.sq_sqrt (hilbertEnergy_nonneg Q f)]
  have hroot : c 0 ≤ a 0 + bseq 0 := by
    simpa [a, bseq, c, F, E] using hrootBound
  have htail : ∀ j, c (j + 1) ≤ a (j + 1) + bseq (j + 1) := by
    intro j
    have hlocal := hilbert_operator_product_residual_le b j hf hM hD hb hdb
    change α j*hilbertL2Norm Q (Fres j) ≤
      α j*(M*hilbertL2Norm Q (fun x => f x-hilbertCubeProjection Q j f x))+α j*β j
    calc
      _ ≤ α j*(M*hilbertL2Norm Q (fun x => f x-hilbertCubeProjection Q j f x)+β j) :=
        mul_le_mul_of_nonneg_left hlocal (Real.sqrt_nonneg _)
      _ = _ := mul_add _ _ _
  have hpoint : ∀ n, c n ≤ a n + bseq n := by
    intro n
    cases n with
    | zero => exact hroot
    | succ j => exact htail j
  have hnonneg : ∀ n, 0 ≤ a n ∧ 0 ≤ bseq n ∧ 0 ≤ c n := by
    intro n
    cases n with
    | zero =>
        change 0 ≤ M * Real.sqrt E ∧ 0 ≤ (0 : ℝ) ∧
          0 ≤ Real.sqrt (hilbertEnergy Q F)
        exact ⟨mul_nonneg hM (Real.sqrt_nonneg _), le_rfl, Real.sqrt_nonneg _⟩
    | succ j =>
        dsimp [a, bseq, c]
        have hα : 0 ≤ α j := Real.sqrt_nonneg _
        exact ⟨mul_nonneg hα (mul_nonneg hM (Real.sqrt_nonneg _)),
          mul_nonneg hα (by dsimp [β]; positivity),
          mul_nonneg hα (Real.sqrt_nonneg _)⟩
  have haTail : Summable (fun j => a (j + 1) ^ 2) := by
    refine (hpos.mul_left (δ * M ^ 2)).congr ?_
    intro j
    have hcoeff : 0 ≤ δ * q ^ j := mul_nonneg hδnonneg (pow_nonneg hqpos.le _)
    rw [show a (j + 1) = α j * (M * Real.sqrt
        (hilbertEnergy Q (fun x => f x - hilbertCubeProjection Q j f x))) by rfl,
      mul_pow, Real.sq_sqrt hcoeff, mul_pow, Real.sq_sqrt (hEresNonneg j)]
    ring
  have ha : Summable (fun n => a n ^ 2) :=
    (summable_nat_add_iff 1).1 haTail
  let C : ℝ := δ * (R ^ 2 / Real.pi ^ 2) * D ^ 2 * E
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hgeom : Summable (fun j : ℕ => C * (q / 9) ^ j) :=
    (summable_geometric_of_lt_one (by positivity) hq9).mul_left C
  have hbetaSq : ∀ j, bseq (j + 1) ^ 2 = C * (q / 9) ^ j := by
    intro j
    have hpow : ((3 : ℝ) ^ j) ^ 2 = (9 : ℝ) ^ j := by
      rw [← pow_mul, Nat.mul_comm j 2, pow_mul]
      norm_num
    have hcoeff : 0 ≤ δ * q ^ j := mul_nonneg hδnonneg (pow_nonneg hqpos.le _)
    have hβ : β j ^ 2 = R ^ 2 / (9 ^ j * Real.pi ^ 2) * D ^ 2 * E := by
      dsimp [β]
      rw [mul_pow, mul_pow, div_pow, mul_pow, Real.sq_sqrt hE, hpow]
    calc
      bseq (j + 1) ^ 2 =
          (Real.sqrt (δ * q ^ j) *
            ((R / ((3 : ℝ) ^ j * Real.pi)) * D * Real.sqrt E)) ^ 2 := by
              rfl
      _ = C * (q / 9) ^ j := by
            rw [mul_pow, Real.sq_sqrt hcoeff, hβ]
            dsimp [C]
            rw [div_pow]
            field_simp [Real.pi_ne_zero,
              pow_ne_zero j (by norm_num : (9 : ℝ) ≠ 0)]
  have hbTail : Summable (fun j => bseq (j + 1) ^ 2) := by
    refine hgeom.congr ?_
    intro j
    exact (hbetaSq j).symm
  have hb : Summable (fun n => bseq n ^ 2) :=
    (summable_nat_add_iff 1).1 hbTail
  have hadd : Summable (fun n => (a n + bseq n) ^ 2) := by
    have hmajor : Summable (fun n => 2 * a n ^ 2 + 2 * bseq n ^ 2) :=
      (ha.mul_left 2).add (hb.mul_left 2)
    apply hmajor.of_norm_bounded
    intro n
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [sq_nonneg (a n - bseq n)]
  have hc : Summable (fun n => c n ^ 2) := by
    apply hadd.of_norm_bounded
    intro n
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hsumNonneg : 0 ≤ a n + bseq n := add_nonneg (hnonneg n).1 (hnonneg n).2.1
    exact (sq_le_sq₀ (hnonneg n).2.2 hsumNonneg).2 (hpoint n)
  have hcTail : Summable (fun j => c (j + 1) ^ 2) :=
    (summable_nat_add_iff 1).2 hc
  have hctailEq : ∀ j, c (j + 1) ^ 2 = δ * q ^ j *
      hilbertEnergy Q (Fres j) := by
    intro j
    have hcoeff : 0 ≤ δ * q ^ j := mul_nonneg hδnonneg (pow_nonneg hqpos.le _)
    rw [show c (j + 1) = α j *
        Real.sqrt (hilbertEnergy Q (Fres j)) by rfl,
      mul_pow, Real.sq_sqrt hcoeff, Real.sq_sqrt (hresVecNonneg j)]
  have hvecResSummable : Summable (fun j => q ^ j *
      hilbertEnergy Q (Fres j)) := by
    refine (hcTail.mul_left δ⁻¹).congr ?_
    intro j
    rw [hctailEq j]
    have hδne : δ ≠ 0 := ne_of_gt hδ
    field_simp
  have hctsum : ∑' n, c n ^ 2 = hilbertEnergy Q F +
      δ * ∑' j, q ^ j * hilbertEnergy Q (Fres j) := by
    have hsplit := hc.sum_add_tsum_nat_add 1
    have htailTsum : ∑' j, c (j + 1) ^ 2 =
        δ * ∑' j, q ^ j * hilbertEnergy Q (Fres j) := by
      rw [show (fun j => c (j + 1) ^ 2) =
        (fun j => δ * (q ^ j * hilbertEnergy Q (Fres j))) by
          funext j
          rw [hctailEq j]
          ring, tsum_mul_left]
    calc
      ∑' n, c n ^ 2 = c 0 ^ 2 + ∑' j, c (j + 1) ^ 2 := by
        simpa only [Finset.sum_range_one] using hsplit.symm
      _ = hilbertEnergy Q F +
          δ * ∑' j, q ^ j * hilbertEnergy Q (Fres j) := by
            rw [htailTsum]
            have hcsq0 : c 0 ^ 2 = hilbertEnergy Q F := by
              change (Real.sqrt (hilbertEnergy Q F)) ^ 2 = _
              exact Real.sq_sqrt (hilbertEnergy_nonneg Q F)
            rw [hcsq0]
  have hproductP := hilbert_positive_summable_of_residual Q q hFmem hvecResSummable
  have hproductEnergy : hilbertPrimalEnergy Q q F = ∑' n, c n^2 := by
    rw [(hilbert_sensitivity_tail_of_weight Q hqgt hFmem hproductP).2.1]
    exact hctsum.symm
  have hAtsum : ∑' n, a n ^ 2 = M ^ 2 * hilbertPrimalEnergy Q q f := by
    have hsplit := ha.sum_add_tsum_nat_add 1
    have htailTsum : ∑' j, a (j + 1) ^ 2 = δ * M ^ 2 * ∑' j, q ^ j *
        hilbertEnergy Q (fun x => f x - hilbertCubeProjection Q j f x) := by
      rw [show (fun j => a (j + 1) ^ 2) = (fun j =>
        (δ * M ^ 2) * (q ^ j * hilbertEnergy Q
          (fun x => f x - hilbertCubeProjection Q j f x))) by
          funext j
          have hcoeff : 0 ≤ δ * q ^ j := mul_nonneg hδnonneg (pow_nonneg hqpos.le _)
          rw [show a (j + 1) = α j * (M * Real.sqrt
            (hilbertEnergy Q (fun x => f x - hilbertCubeProjection Q j f x))) by rfl,
            mul_pow, Real.sq_sqrt hcoeff, mul_pow,
            Real.sq_sqrt (hEresNonneg j)]
          ring, tsum_mul_left]
    have habelF := (hilbert_sensitivity_tail_of_weight Q hqgt hf hP).2.1
    have ha0 : a 0 ^ 2 = M ^ 2 * E := by
      change (M * Real.sqrt E) ^ 2 = M ^ 2 * E
      rw [mul_pow, Real.sq_sqrt hE]
    calc
      ∑' n, a n ^ 2 = a 0 ^ 2 + ∑' j, a (j + 1) ^ 2 := by
        simpa only [Finset.sum_range_one] using hsplit.symm
      _ = M ^ 2 * E + δ * M ^ 2 * ∑' j, q ^ j *
          hilbertEnergy Q (fun x => f x - hilbertCubeProjection Q j f x) := by
            rw [ha0, htailTsum]
      _ = M ^ 2 * hilbertPrimalEnergy Q q f := by
            calc
              _ = M ^ 2 * (E + δ * ∑' j, q ^ j *
                    hilbertEnergy Q (fun x => f x - hilbertCubeProjection Q j f x)) := by
                      ring
              _ = M ^ 2 * hilbertPrimalEnergy Q q f := by
                    rw [← habelF]
  have hPnorm : (hilbertPositiveHaarNorm Q q f)^2 = hilbertPrimalEnergy Q q f := by
    apply Real.sq_sqrt
    unfold hilbertPrimalEnergy
    exact add_nonneg (hilbertEnergy_nonneg Q _) (tsum_nonneg fun k => mul_nonneg (pow_nonneg hqpos.le _) (hilbertEnergy_nonneg Q _))
  have hAroot : Real.sqrt (∑' n, a n ^ 2) =
      M * hilbertPositiveHaarNorm Q q f := by
    have hsq : ∑' n, a n ^ 2 = (M * hilbertPositiveHaarNorm Q q f) ^ 2 := by
      rw [hAtsum, ← hPnorm]
      ring
    have hPnonneg : 0 ≤ hilbertPositiveHaarNorm Q q f := by
      dsimp [hilbertPositiveHaarNorm]
      positivity
    rw [hsq, Real.sqrt_sq_eq_abs,
      abs_of_nonneg (mul_nonneg hM hPnonneg)]
  have hBtsum : ∑' n, bseq n ^ 2 =
      (R * Real.sqrt (haarPoincareM2 q) * D * Real.sqrt E) ^ 2 := by
    have hsplit := hb.sum_add_tsum_nat_add 1
    have htailTsum : ∑' j, bseq (j + 1) ^ 2 = C * (1 - q / 9)⁻¹ := by
      rw [show (fun j => bseq (j + 1) ^ 2) =
        (fun j => C * (q / 9) ^ j) by
          funext j
          exact hbetaSq j, tsum_mul_left,
        tsum_geometric_of_lt_one (by positivity) hq9]
    have hc1 : (Real.sqrt (haarPoincareM2 q))^2 = δ/(Real.pi^2*(1-q/9)) := by
      have hM2 : 0 ≤ haarPoincareM2 q := div_nonneg (sub_nonneg.mpr hqgt.le) (mul_nonneg (sub_nonneg.mpr hq9.le) (sq_nonneg Real.pi))
      rw [Real.sq_sqrt hM2]
      unfold haarPoincareM2 δ
      rw [mul_comm]
    calc
      ∑' n, bseq n ^ 2 = bseq 0 ^ 2 + ∑' j, bseq (j + 1) ^ 2 := by
        simpa only [Finset.sum_range_one] using hsplit.symm
      _ = C * (1 - q / 9)⁻¹ := by
            rw [htailTsum]
            simp [bseq]
      _ = (R * Real.sqrt (haarPoincareM2 q) * D * Real.sqrt E) ^ 2 := by
            calc
              C * (1 - q / 9)⁻¹ =
                  R ^ 2 * (δ / (Real.pi ^ 2 * (1 - q / 9))) * D ^ 2 * E := by
                    dsimp [C]
                    field_simp [Real.pi_ne_zero]
              _ = R ^ 2 * Real.sqrt (haarPoincareM2 q) ^ 2 * D ^ 2 * E := by rw [← hc1]
              _ = (R * Real.sqrt (haarPoincareM2 q) * D * Real.sqrt E) ^ 2 := by
                    rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt hE]
  have hBroot : Real.sqrt (∑' n, bseq n ^ 2) =
      R * Real.sqrt (haarPoincareM2 q) * D * Real.sqrt E := by
    have hc1nonneg : 0 ≤ Real.sqrt (haarPoincareM2 q) := Real.sqrt_nonneg _
    have hcoefNonneg : 0 ≤ R * Real.sqrt (haarPoincareM2 q) * D :=
      mul_nonneg (mul_nonneg hR.le hc1nonneg) hD
    rw [hBtsum, Real.sqrt_sq_eq_abs,
      abs_of_nonneg (mul_nonneg hcoefNonneg (Real.sqrt_nonneg E))]
  have hsumle : (∑' n, c n ^ 2) ≤ ∑' n, (a n + bseq n) ^ 2 := by
    apply hc.tsum_le_tsum ?_ hadd
    intro n
    exact (sq_le_sq₀ (hnonneg n).2.2
      (add_nonneg (hnonneg n).1 (hnonneg n).2.1)).2 (hpoint n)
  have hnormProduct : hilbertPositiveHaarNorm Q q F =
      Real.sqrt (∑' n, c n ^ 2) := by
    unfold hilbertPositiveHaarNorm
    rw [hproductEnergy]
  refine ⟨hproductP, ?_⟩
  calc
    hilbertPositiveHaarNorm Q q F = Real.sqrt (∑' n, c n ^ 2) := hnormProduct
    _ ≤ Real.sqrt (∑' n, (a n + bseq n) ^ 2) := Real.sqrt_le_sqrt hsumle
    _ ≤ Real.sqrt (∑' n, a n ^ 2) + Real.sqrt (∑' n, bseq n ^ 2) :=
      sqrt_tsum_sq_add_le a bseq ha hb
    _ = M * hilbertPositiveHaarNorm Q q f + R * Real.sqrt (haarPoincareM2 q) * D * Real.sqrt E := by
      rw [hAroot, hBroot]


end
end ASDExplicitGamma.Triadic
