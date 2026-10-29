module

public import ASDExplicitGamma.Scalar.SmoothFeedbackForcedFeedback
public import ASDExplicitGamma.Scalar.SmoothFeedbackResponse
public import ASDExplicitGamma.Scalar.PairInner

/-! T4 v2, weak energies: scaling and a.e. transport of the depth-134 tiled weak energies. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar

open Homogenization ASDExplicitGamma.Response ASDExplicitGamma.Triadic
  ASDExplicitGamma.Variational ASDExplicitGamma.Native MeasureTheory

attribute [local irreducible] Homogenization.descendantsAtDepth

noncomputable section

theorem t4v2_dualEnergy_smul {d : ℕ} (Q : TriadicCube d) (c : ℝ) (f : Vec d → ℝ) :
    dualEnergy Q (Real.sqrt 3) (fun x => c * f x) = c ^ 2 * dualEnergy Q (Real.sqrt 3) f := by
  unfold dualEnergy primalEnergy
  have hinc (k : ℕ) : cubeIncrement Q k (fun x => c * f x) =
      fun x => c * cubeIncrement Q k f x := by
    cases k with
    | zero => simp [cubeIncrement_zero, projection_smul]
    | succ k => simp [cubeIncrement, projection_smul, mul_sub]
  have henergy (g : Vec d → ℝ) : energy Q (fun x => c * g x) = c ^ 2 * energy Q g := by
    unfold energy pairing
    rw [cubeAverage_eq_integral_normalizedCubeMeasure,
      cubeAverage_eq_integral_normalizedCubeMeasure]
    have hpoint : (fun x : Vec d => (c * g x) * (c * g x)) =
        fun x => c ^ 2 * (g x * g x) := by
      funext x
      ring
    rw [hpoint, integral_const_mul]
  change energy Q (cubeIncrement Q 0 (fun x => c * f x)) +
      ∑' k, (Real.sqrt 3)⁻¹ ^ (k + 1) *
        energy Q (cubeIncrement Q (k + 1) (fun x => c * f x)) = _
  rw [hinc 0, henergy]
  have hseries : (∑' k, (Real.sqrt 3)⁻¹ ^ (k + 1) *
      energy Q (cubeIncrement Q (k + 1) (fun x => c * f x))) =
      c ^ 2 * ∑' k, (Real.sqrt 3)⁻¹ ^ (k + 1) *
        energy Q (cubeIncrement Q (k + 1) f) := by
    calc
      _ = ∑' k, (Real.sqrt 3)⁻¹ ^ (k + 1) *
          (c ^ 2 * energy Q (cubeIncrement Q (k + 1) f)) := by
            apply tsum_congr
            intro k
            rw [hinc (k + 1), henergy]
      _ = _ := by rw [← tsum_mul_left]; congr 1; funext k; ring
  rw [hseries]
  ring

theorem t4v2_vwhe_smul (Q : TriadicCube 2) (c : ℝ) (F : Vec 2 → Vec 2) :
    vectorWeakHaarEnergy Q (fun x i => c * F x i) = c ^ 2 * vectorWeakHaarEnergy Q F := by
  unfold vectorWeakHaarEnergy
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact t4v2_dualEnergy_smul Q c (fun x => F x i)

/-- Tiled weak energy of a scalar multiple of a field (a.e. on the parent square). -/
theorem t4v2_tiled_scale (Q : TriadicCube 2) (c : ℝ) {F G : Vec 2 → Vec 2}
    (h : F =ᵐ[volumeMeasureOn (openCubeSet Q)] fun x => c • G x) :
    lemmaVTiledWeakEnergy Q 134 F = c ^ 2 * lemmaVTiledWeakEnergy Q 134 G := by
  have key : ∀ R ∈ descendantsAtDepth Q 134,
      vectorWeakHaarEnergy R F = c ^ 2 * vectorWeakHaarEnergy R G := by
    intro R hR
    have hsub := openCubeSet_subset_of_mem_descendantsAtDepth hR
    have hR' : F =ᵐ[volumeMeasureOn (openCubeSet R)] fun x => c • G x :=
      ae_restrict_of_ae_restrict_of_subset hsub h
    rw [smooth_feedback_vector_weak_energy_congr_ae R hR']
    have : (fun x => c • G x) = fun x i => c * G x i := by
      funext x i; simp
    rw [this, t4v2_vwhe_smul]
  unfold lemmaVTiledWeakEnergy descendantsAverage
  dsimp only
  rw [Finset.sum_congr rfl key, ← Finset.mul_sum]
  ring

end

end ASDExplicitGamma.Scalar
