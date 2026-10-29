module

public import ASDExplicitGamma.Scalar.ResolventAlgebra
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Tactic.NoncommRing

/-! The four-term resolvent identity on a Hilbert space with the G1
parity-adjoint symmetry. This is the operator form of the source identity;
the OLD and NEW block operators need not be self-adjoint. -/
@[expose] public section

namespace ASDExplicitGamma.Scalar
open scoped InnerProduct InnerProductSpace

private theorem inverse_parityAdjoint {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A B J : H →L[ℝ] H) (hA : A.adjoint * J = J * A)
    (hAB : A * B = 1) : B.adjoint * J = J * B := by
  have hB'A : B.adjoint * A.adjoint = 1 := by
    have h := congrArg ContinuousLinearMap.adjoint hAB
    simpa [ContinuousLinearMap.mul_def, ContinuousLinearMap.adjoint_comp,
      ContinuousLinearMap.adjoint_one] using h
  calc
    B.adjoint * J = B.adjoint * (J * (A * B)) := by rw [hAB]; simp
    _ = B.adjoint * (A.adjoint * J) * B := by rw [hA]; noncomm_ring
    _ = (B.adjoint * A.adjoint) * (J * B) := by noncomm_ring
    _ = J * B := by rw [hB'A]; simp

private theorem parityAdjoint_apply {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (T J : H →L[ℝ] H) (hT : T.adjoint * J = J * T) (x : H) :
    T.adjoint (J x) = J (T x) := by
  have h := congrArg (fun F : H →L[ℝ] H => F x) hT
  simpa [ContinuousLinearMap.mul_def] using h

private theorem pairing_parityAdjoint {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (T J : H →L[ℝ] H) (hT : T.adjoint * J = J * T)
    (f x : H) (hf : J f = f) :
    ⟪f, T x⟫_ℝ = ⟪J (T f), x⟫_ℝ := by
  have hTf : T.adjoint f = J (T f) := by
    calc
      T.adjoint f = T.adjoint (J f) := by rw [hf]
      _ = (T.adjoint * J) f := by simp [ContinuousLinearMap.mul_def]
      _ = (J * T) f := by rw [hT]
      _ = J (T f) := by simp [ContinuousLinearMap.mul_def]
  calc
    ⟪f, T x⟫_ℝ = ⟪T.adjoint f, x⟫_ℝ := (T.adjoint_inner_left x f).symm
    _ = ⟪J (T f), x⟫_ℝ := by rw [hTf]

private theorem move_parity_source {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (T J : H →L[ℝ] H) (hT : T.adjoint * J = J * T) (x y : H) :
    ⟪J x, T y⟫_ℝ = ⟪J (T x), y⟫_ℝ := by
  calc
    ⟪J x, T y⟫_ℝ = ⟪T.adjoint (J x), y⟫_ℝ := by
      exact (T.adjoint_inner_left y (J x)).symm
    _ = ⟪J (T x), y⟫_ℝ := by
      rw [parityAdjoint_apply T J hT x]

/-- The finite-amplitude quadratic response identity for invertible bounded
operators with the G1 parity-adjoint symmetry. `J` fixes the load and
`T.adjoint * J = J * T` for the OLD operator and insertion. This applies to
the accretive OLD/NEW block operators on the physical constraint space. -/
theorem resolvent_four_term_hilbert_pairing {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (M C B N J : H →L[ℝ] H)
    (hM : M.adjoint * J = J * M) (hC : C.adjoint * J = J * C)
    (hBM : B * M = 1) (hMB : M * B = 1)
    (hMN : (M + C) * N = 1) (hNM : N * (M + C) = 1)
    (f : H) (hf : J f = f) :
    let u := B f
    let s := (C * B * C) u
    ⟪f, N f⟫_ℝ - ⟪f, B f⟫_ℝ =
      -⟪J u, C u⟫_ℝ + ⟪J u, (C * B * C) u⟫_ℝ -
        ⟪J u, (C * B * C * B * C) u⟫_ℝ + ⟪J s, N s⟫_ℝ := by
  dsimp only
  let u := B f
  let S := C * B * C
  let s := S u
  have hB : B.adjoint * J = J * B := inverse_parityAdjoint M B J hM hMB
  have hMC : (M + C).adjoint * J = J * (M + C) := by
    rw [map_add ContinuousLinearMap.adjoint M C]
    rw [add_mul, hM, hC, ← mul_add]
  have hN : N.adjoint * J = J * N :=
    inverse_parityAdjoint (M + C) N J hMC hMN
  have hS : S.adjoint * J = J * S := by
    have hSapply (x : H) :
        (C * B * C).adjoint (J x) = J ((C * B * C) x) := by
      calc
        (C * B * C).adjoint (J x) =
            C.adjoint (B.adjoint (C.adjoint (J x))) := by
              simp [ContinuousLinearMap.mul_def, ContinuousLinearMap.adjoint_comp]
        _ = C.adjoint (B.adjoint (J (C x))) := by
              rw [parityAdjoint_apply C J hC x]
        _ = C.adjoint (J (B (C x))) := by
              rw [parityAdjoint_apply B J hB (C x)]
        _ = J (C (B (C x))) := parityAdjoint_apply C J hC (B (C x))
    ext x
    simpa [S, ContinuousLinearMap.mul_def] using hSapply x
  have hres := resolvent_four_term_expansion B C N
    (resolvent_left_right M C B N hBM hMN hMB hNM).1
    (resolvent_left_right M C B N hBM hMN hMB hNM).2
  have hpair := congrArg (fun T : H →L[ℝ] H => ⟪f, T f⟫_ℝ) hres
  have hterm₁ : ⟪f, (B * C * B) f⟫_ℝ = ⟪J u, C u⟫_ℝ := by
    change ⟪f, B (C (B f))⟫_ℝ = _
    rw [pairing_parityAdjoint B J hB f (C (B f)) hf]
  have hterm₂ : ⟪f, (B * C * B * C * B) f⟫_ℝ =
      ⟪J u, (C * B * C) u⟫_ℝ := by
    change ⟪f, B (C (B (C (B f))))⟫_ℝ = _
    rw [pairing_parityAdjoint B J hB f (C (B (C (B f)))) hf]
    simp [u, mul_apply_eq_comp]
  have hterm₃ : ⟪f, (B * C * B * C * B * C * B) f⟫_ℝ =
      ⟪J u, (C * B * C * B * C) u⟫_ℝ := by
    change ⟪f, B (C (B (C (B (C (B f))))))⟫_ℝ = _
    rw [pairing_parityAdjoint B J hB f (C (B (C (B (C (B f))))) ) hf]
    simp [u, mul_apply_eq_comp]
  have hterm₄ :
      ⟪f, (B * C * B * C * N * C * B * C * B) f⟫_ℝ = ⟪J s, N s⟫_ℝ := by
    have hfactor : B * C * B * C * N * C * B * C * B = B * S * N * S * B := by
      dsimp [S]
      noncomm_ring
    rw [hfactor]
    change ⟪f, B (S (N (S (B f))))⟫_ℝ = _
    rw [pairing_parityAdjoint B J hB f (S (N (S (B f)))) hf]
    rw [move_parity_source S J hS (B f) (N (S (B f)))]
  have hpair' :
      ⟪f, N f⟫_ℝ - ⟪f, B f⟫_ℝ =
        -⟪f, (B * C * B) f⟫_ℝ + ⟪f, (B * C * B * C * B) f⟫_ℝ -
          ⟪f, (B * C * B * C * B * C * B) f⟫_ℝ +
            ⟪f, (B * C * B * C * N * C * B * C * B) f⟫_ℝ := by
    simpa only [mul_apply_eq_comp, sub_apply, add_apply, neg_apply, inner_sub_right,
      inner_add_right, inner_neg_right] using hpair
  rw [hterm₁, hterm₂, hterm₃, hterm₄] at hpair'
  simpa [u, S, s] using hpair'

end ASDExplicitGamma.Scalar
