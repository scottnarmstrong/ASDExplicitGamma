module

public import Mathlib.Tactic.NoncommRing

/-! Exact finite-amplitude resolvent expansion. Both odd terms remain pathwise. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar

/-- The left and right resolvent identities follow solely from actual inverse relations. -/
theorem resolvent_left_right {R : Type*} [Ring R] (M C B N : R)
    (hBM : B*M=1) (hMN : (M+C)*N=1) (hMB : M*B=1) (hNM : N*(M+C)=1) :
    N=B-B*C*N ∧ N=B-N*C*B := by
  constructor
  · calc
      N = (B*M)*N := by rw [hBM,one_mul]
      _ = B*((M+C)*N)-B*C*N := by noncomm_ring
      _ = B-B*C*N := by rw [hMN,mul_one]
  · calc
      N = N*(M*B) := by rw [hMB,mul_one]
      _ = (N*(M+C))*B-N*C*B := by noncomm_ring
      _ = B-N*C*B := by rw [hNM,one_mul]

/-- Two iterations give the symmetric sandwich remainder without smallness assumptions. -/
theorem resolvent_four_term_expansion {R : Type*} [Ring R] (B C N : R)
    (hl : N=B-B*C*N) (hr : N=B-N*C*B) :
    N-B = -B*C*B+B*C*B*C*B-B*C*B*C*B*C*B+B*C*B*C*N*C*B*C*B := by
  have htwo : N=B-B*C*B+B*C*N*C*B := by
    calc
      N = B-B*C*N := hl
      _ = B-B*C*(B-N*C*B) := by rw [← hr]
      _ = B-B*C*B+B*C*N*C*B := by noncomm_ring
  calc
    N-B = (B-B*C*B+B*C*N*C*B)-B := by rw [← htwo]
    _ = (B-B*C*B+B*C*(B-B*C*B+B*C*N*C*B)*C*B)-B := by
      exact congrArg (fun X => (B-B*C*B+B*C*X*C*B)-B) htwo
    _ = _ := by noncomm_ring

end ASDExplicitGamma.Scalar
