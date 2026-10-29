module

public import ASDExplicitGamma.Response.FrameAlgebra

/-! Pointwise identities for Lemma V in the fixed scalar frame. -/

@[expose] public section

namespace ASDExplicitGamma.Variational

open Homogenization ASDExplicitGamma.Response

noncomputable section

/-- The conjugate gradient `s⁻¹(q − k∇v)` for the coefficient divided by `σ`.
Here `ν` is the physical symmetric coefficient and `σ` is the frame. -/
def lemmaVConjugateGradient (ν σ κ : ℝ) (X : BlockVec 2) : Vec 2 :=
  (σ / ν) • (X.2 - (κ / σ) • matVecMul responsePlanarJ X.1)

theorem lemmaVFrameEnergy_split (ν σ κ : ℝ)
    (hν : ν ≠ 0) (hσ : σ ≠ 0) (X : BlockVec 2) :
    responseFrameEnergyDensity ν σ κ X =
      (ν / σ) * (vecNormSq X.1 +
        vecNormSq (lemmaVConjugateGradient ν σ κ X)) := by
  rw [responseFrameEnergyDensity, lemmaVConjugateGradient, vecNormSq_smul]
  field_simp

/-- The plus-load envelope sign in half-pair coordinates. -/
theorem lemmaV_halfPair_envelope_plus (η : ℝ) (u v : Vec 2) :
    -η * vecDot ((1 / 2 : ℝ) • (u - v))
        (matVecMul responsePlanarJ ((1 / 2 : ℝ) • (u + v))) =
      η * vecDot v (matVecMul responsePlanarJ ((1 / 2 : ℝ) • (u + v))) := by
  simp only [vecDot, Homogenization.matVecMul, Fin.sum_univ_two]
  dsimp [responsePlanarJ]
  ring

/-- The minus-load envelope sign in half-pair coordinates. -/
theorem lemmaV_halfPair_envelope_minus (η : ℝ) (u v : Vec 2) :
    -η * vecDot ((1 / 2 : ℝ) • (u - v))
        (matVecMul responsePlanarJ ((1 / 2 : ℝ) • (u + v))) =
      -η * vecDot u (matVecMul responsePlanarJ ((1 / 2 : ℝ) • (u + v))) := by
  simp only [vecDot, Homogenization.matVecMul, Fin.sum_univ_two]
  dsimp [responsePlanarJ]
  ring

end

end ASDExplicitGamma.Variational
