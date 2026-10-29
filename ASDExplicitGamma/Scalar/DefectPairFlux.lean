module

public import ASDExplicitGamma.Scalar.PairBilinear

/-! The `Y`-component of the first-response defect lies in any subspace containing the ranges of
the coefficient operators. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar

open scoped BigOperators InnerProductSpace

noncomputable section

section Generic

variable {Y X : Type*}
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]

theorem blockInverse_fst_mem {α : ℝ} (hα : 0 < α) (A : X →L[ℝ] Y) (K : Submodule ℝ Y)
    (hA : ∀ x, A x ∈ K) (w : pureFluxPair (Y := Y) (X := X)) (hw : w.ofLp.1 ∈ K) :
    ((pureFluxBlockInverse α hα A) w).ofLp.1 ∈ K := by
  have hmul := pureFluxBlockInverse_left (Y := Y) (X := X) α hα A
  have h1 : pureFluxBlockOperator α A (pureFluxBlockInverse α hα A w) = w := by
    have := congrArg (fun T => T w) hmul
    simpa using this
  have h2 := congrArg (fun z : pureFluxPair (Y := Y) (X := X) => z.ofLp.1) h1
  simp only [pureFluxBlockOperator_apply] at h2
  set y := (pureFluxBlockInverse α hα A w) with hy
  have hy1 : y.ofLp.1 = α⁻¹ • (w.ofLp.1 - A y.ofLp.2) := by
    rw [← h2]
    simp [smul_smul, inv_mul_cancel₀ hα.ne']
  rw [hy1]
  exact K.smul_mem _ (K.sub_mem hw (hA _))

theorem delta_fst_mem (𝓗 : Type*) [NormedAddCommGroup 𝓗] [NormedSpace ℝ 𝓗]
    (Vm : 𝓗 →L[ℝ] (X →L[ℝ] Y)) (Fl : 𝓗 →L[ℝ] X) {α : ℝ} (hα : 0 < α) (A : X →L[ℝ] Y)
    (u : pureFluxPair (Y := Y) (X := X)) (σ : ℝ) (K : Submodule ℝ Y)
    (hA : ∀ x, A x ∈ K) (hV : ∀ H x, Vm H x ∈ K) (H : 𝓗) :
    (delta' Vm Fl (pureFluxBlockInverse α hα A) u σ H).ofLp.1 ∈ K := by
  rw [delta_apply']
  have h1 : ((pureFluxBlockInverse α hα A)
      (pureFluxBlockOperator 0 (Vm H) u)).ofLp.1 ∈ K := by
    refine blockInverse_fst_mem hα A K hA _ ?_
    rw [pureFluxBlockOperator_apply]
    simpa using hV H _
  have h3 : ((pureFluxBlockInverse α hα A) (pureFluxBlockOperator 0 (Vm H) u) -
      σ • inr'' (Y := Y) (Fl H)).ofLp.1 =
      ((pureFluxBlockInverse α hα A) (pureFluxBlockOperator 0 (Vm H) u)).ofLp.1 := by
    simp [inr_apply']
  rw [h3]
  exact h1

end Generic

end

end ASDExplicitGamma.Scalar
