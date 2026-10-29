module

public import ASDExplicitGamma.Scalar.ResolventHilbert
public import Mathlib.MeasureTheory.Integral.Prod

/-! Symmetric-law parity for the Hilbert-space finite-amplitude resolvent
identity. This is the measure-theoretic consumer of the operator identity. -/
@[expose] public section

namespace ASDExplicitGamma.Scalar

open MeasureTheory
open scoped InnerProduct InnerProductSpace

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

def hilbertG1LinearTerm (B J : H →L[ℝ] H) (f : H) (C : H →L[ℝ] H) : ℝ :=
  -⟪J (B f), C (B f)⟫_ℝ

def hilbertG1HessianTerm (B J : H →L[ℝ] H) (f : H) (C : H →L[ℝ] H) : ℝ :=
  ⟪J (B f), (C * B * C) (B f)⟫_ℝ

def hilbertG1CubicTerm (B J : H →L[ℝ] H) (f : H) (C : H →L[ℝ] H) : ℝ :=
  -⟪J (B f), (C * B * C * B * C) (B f)⟫_ℝ

def hilbertG1QuarticTerm (B J : H →L[ℝ] H) (f : H)
    (C N : H →L[ℝ] H) : ℝ :=
  let s := (C * B * C) (B f)
  ⟪J s, N s⟫_ℝ

theorem hilbertG1LinearTerm_neg (B J : H →L[ℝ] H) (f : H)
    {C D : H →L[ℝ] H} (hD : D = -C) :
    hilbertG1LinearTerm B J f D = -hilbertG1LinearTerm B J f C := by
  rw [hilbertG1LinearTerm, hilbertG1LinearTerm, hD]
  simp

theorem hilbertG1CubicTerm_neg (B J : H →L[ℝ] H) (f : H)
    {C D : H →L[ℝ] H} (hD : D = -C) :
    hilbertG1CubicTerm B J f D = -hilbertG1CubicTerm B J f C := by
  rw [hilbertG1CubicTerm, hilbertG1CubicTerm, hD]
  have hprod : (-C) * B * (-C) * B * (-C) = -(C * B * C * B * C) := by
    noncomm_ring
  rw [hprod]
  simp

private theorem integral_eq_zero_of_negate
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (neg : Ω → Ω) (hneg : Measurable neg)
    (hmap : Measure.map neg μ = μ) (g : Ω → ℝ)
    (hg : Integrable g μ) (hodd : ∀ x, g (neg x) = -g x) :
    ∫ x, g x ∂μ = 0 := by
  have hmeas : AEStronglyMeasurable g (Measure.map neg μ) := by
    rw [hmap]
    exact hg.aestronglyMeasurable
  have hi := integral_map hneg.aemeasurable (f := g) (μ := μ) hmeas
  rw [hmap] at hi
  have hflip : (∫ x, g (neg x) ∂μ) = -(∫ x, g x ∂μ) := by
    rw [integral_congr_ae]
    · rw [integral_neg]
    · exact Filter.Eventually.of_forall hodd
  rw [hflip] at hi
  linarith

/-- Conditional version for a random OLD coefficient: the inverse `B ω` is
unchanged by the fresh-noise sign flip, while the NEW operator may vary with
both the old state and the fresh perturbation. This is the form needed on the
product law of an old cutoff and its independent next shell. -/
theorem resolvent_hilbert_parity_random_old {Ω : Type*} [MeasurableSpace Ω]
    [CompleteSpace H]
    (μ : Measure Ω) (neg : Ω → Ω) (hneg : Measurable neg)
    (hmap : Measure.map neg μ = μ)
    (M B : Ω → H →L[ℝ] H) (J : H →L[ℝ] H)
    (hM : ∀ ω, (M ω).adjoint * J = J * (M ω))
    (hBM : ∀ ω, (B ω) * (M ω) = 1) (hMB : ∀ ω, (M ω) * (B ω) = 1)
    (C N : Ω → H →L[ℝ] H)
    (hC : ∀ ω, (C ω).adjoint * J = J * (C ω))
    (hMN : ∀ ω, ((M ω) + (C ω)) * (N ω) = 1)
    (hNM : ∀ ω, (N ω) * ((M ω) + (C ω)) = 1)
    (hBneg : ∀ ω, B (neg ω) = B ω)
    (hCneg : ∀ ω, C (neg ω) = -(C ω))
    (f : H) (hf : J f = f)
    (hlinear : Integrable
      (fun ω => hilbertG1LinearTerm (B ω) J f (C ω)) μ)
    (hhessian : Integrable
      (fun ω => hilbertG1HessianTerm (B ω) J f (C ω)) μ)
    (hcubic : Integrable
      (fun ω => hilbertG1CubicTerm (B ω) J f (C ω)) μ)
    (hquartic : Integrable
      (fun ω => hilbertG1QuarticTerm (B ω) J f (C ω) (N ω)) μ) :
    (∫ ω, hilbertG1LinearTerm (B ω) J f (C ω) ∂μ = 0) ∧
    (∫ ω, hilbertG1CubicTerm (B ω) J f (C ω) ∂μ = 0) ∧
    (∫ ω, ⟪f, (N ω) f⟫_ℝ - ⟪f, (B ω) f⟫_ℝ ∂μ =
      (∫ ω, hilbertG1HessianTerm (B ω) J f (C ω) ∂μ) +
      (∫ ω, hilbertG1QuarticTerm (B ω) J f (C ω) (N ω) ∂μ)) := by
  have hfirst := integral_eq_zero_of_negate μ neg hneg hmap
    (fun ω => hilbertG1LinearTerm (B ω) J f (C ω)) hlinear (by
      intro ω
      rw [hBneg, hCneg]
      exact hilbertG1LinearTerm_neg (B ω) J f rfl)
  have hthird := integral_eq_zero_of_negate μ neg hneg hmap
    (fun ω => hilbertG1CubicTerm (B ω) J f (C ω)) hcubic (by
      intro ω
      rw [hBneg, hCneg]
      exact hilbertG1CubicTerm_neg (B ω) J f rfl)
  refine ⟨hfirst, hthird, ?_⟩
  have hpoint (ω : Ω) :
      ⟪f, (N ω) f⟫_ℝ - ⟪f, (B ω) f⟫_ℝ =
        hilbertG1LinearTerm (B ω) J f (C ω) +
          hilbertG1HessianTerm (B ω) J f (C ω) +
          hilbertG1CubicTerm (B ω) J f (C ω) +
          hilbertG1QuarticTerm (B ω) J f (C ω) (N ω) := by
    have h := resolvent_four_term_hilbert_pairing (M ω) (C ω) (B ω) (N ω) J
      (hM ω) (hC ω) (hBM ω) (hMB ω) (hMN ω) (hNM ω) f hf
    unfold hilbertG1LinearTerm hilbertG1HessianTerm
      hilbertG1CubicTerm hilbertG1QuarticTerm
    linarith
  calc
    (∫ ω, ⟪f, (N ω) f⟫_ℝ - ⟪f, (B ω) f⟫_ℝ ∂μ) =
        ∫ ω, hilbertG1LinearTerm (B ω) J f (C ω) +
          hilbertG1HessianTerm (B ω) J f (C ω) +
          hilbertG1CubicTerm (B ω) J f (C ω) +
          hilbertG1QuarticTerm (B ω) J f (C ω) (N ω) ∂μ := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall hpoint
    _ = ∫ ω,
          (hilbertG1LinearTerm (B ω) J f (C ω) +
            hilbertG1HessianTerm (B ω) J f (C ω)) +
          (hilbertG1CubicTerm (B ω) J f (C ω) +
            hilbertG1QuarticTerm (B ω) J f (C ω) (N ω)) ∂μ := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall (fun ω => by ring)
    _ = (∫ ω, hilbertG1LinearTerm (B ω) J f (C ω) +
          hilbertG1HessianTerm (B ω) J f (C ω) ∂μ) +
        (∫ ω, hilbertG1CubicTerm (B ω) J f (C ω) +
          hilbertG1QuarticTerm (B ω) J f (C ω) (N ω) ∂μ) :=
            integral_add (hlinear.add hhessian) (hcubic.add hquartic)
    _ = (∫ ω, hilbertG1LinearTerm (B ω) J f (C ω) ∂μ) +
          (∫ ω, hilbertG1HessianTerm (B ω) J f (C ω) ∂μ) +
          ((∫ ω, hilbertG1CubicTerm (B ω) J f (C ω) ∂μ) +
            (∫ ω, hilbertG1QuarticTerm (B ω) J f (C ω) (N ω) ∂μ) : ℝ) := by
            rw [integral_add hlinear hhessian, integral_add hcubic hquartic]
    _ = _ := by rw [hfirst, hthird]; ring

end

end ASDExplicitGamma.Scalar
