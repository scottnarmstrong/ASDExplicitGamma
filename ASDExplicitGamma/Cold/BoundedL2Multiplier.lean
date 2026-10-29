module

public import ASDExplicitGamma.Cold.SquareVectorEnergy

/-! # Bounded measurable multiplication on L² and weighted-pairing continuity -/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace ASDExplicitGamma.Cold

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {φ : α → ℝ}

/-- Multiplication by a bounded measurable coefficient as an actual L² element. -/
def boundedL2Mul (hφ : MemLp φ ⊤ μ) (F : Lp ℝ 2 μ) : Lp ℝ 2 μ :=
  (hφ.mul (Lp.memLp F)).toLp (φ * F)

/-- The pointwise representative of bounded multiplication. -/
theorem boundedL2Mul_coe (hφ : MemLp φ ⊤ μ) (F : Lp ℝ 2 μ) :
    boundedL2Mul hφ F =ᵐ[μ] (fun x => φ x * F x) :=
  (hφ.mul (Lp.memLp F)).coeFn_toLp

/-- Bounded multiplication is linear in its L² argument. -/
def boundedL2MulLinear (hφ : MemLp φ ⊤ μ) : Lp ℝ 2 μ →ₗ[ℝ] Lp ℝ 2 μ where
  toFun := boundedL2Mul hφ
  map_add' F G := by
    apply Lp.ext
    filter_upwards [boundedL2Mul_coe hφ (F + G), boundedL2Mul_coe hφ F,
      boundedL2Mul_coe hφ G, Lp.coeFn_add F G,
      Lp.coeFn_add (boundedL2Mul hφ F) (boundedL2Mul hφ G)] with x hsum hF hG hadd hout
    dsimp only [Pi.add_apply] at hadd hout
    rw [hsum, hadd, hout, hF, hG]
    ring
  map_smul' c F := by
    simp only [RingHom.id_apply]
    apply Lp.ext
    filter_upwards [boundedL2Mul_coe hφ (c • F), boundedL2Mul_coe hφ F,
      Lp.coeFn_smul c F, Lp.coeFn_smul c (boundedL2Mul hφ F)] with x hsum hF hsmul hout
    dsimp only [Pi.smul_apply, smul_eq_mul] at hsmul hout
    rw [hsum, hsmul, hout, hF]
    ring

/-- The norm bound for multiplication uses precisely the essential bound of its coefficient. -/
theorem norm_boundedL2Mul_le (hφ : MemLp φ ⊤ μ) {M : ℝ}
    (hM : ∀ᵐ x ∂μ, ‖φ x‖ ≤ M) (F : Lp ℝ 2 μ) :
    ‖boundedL2Mul hφ F‖ ≤ M * ‖F‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [boundedL2Mul_coe hφ F, hM] with x hx hMx
  rw [hx, norm_mul]
  exact mul_le_mul_of_nonneg_right hMx (norm_nonneg _)

/-- The bounded coefficient defines a continuous linear multiplier on L². -/
def boundedL2Multiplier (hφ : MemLp φ ⊤ μ) (M : ℝ)
    (hM : ∀ᵐ x ∂μ, ‖φ x‖ ≤ M) : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  (boundedL2MulLinear hφ).mkContinuous M (norm_boundedL2Mul_le hφ hM)

/-- The weighted pairing, represented in the actual L² Hilbert space. -/
def weightedL2Pairing (hφ : MemLp φ ⊤ μ) (F G : Lp ℝ 2 μ) : ℝ :=
  inner ℝ (boundedL2Mul hφ F) G

/-- Additivity of the weighted pairing in its first L² field. -/
theorem weightedL2Pairing_add_left (hφ : MemLp φ ⊤ μ) (F G H : Lp ℝ 2 μ) :
    weightedL2Pairing hφ (F + G) H = weightedL2Pairing hφ F H + weightedL2Pairing hφ G H := by
  have hlin : boundedL2Mul hφ (F + G) = boundedL2Mul hφ F + boundedL2Mul hφ G :=
    (boundedL2MulLinear hφ).map_add F G
  unfold weightedL2Pairing
  rw [hlin, inner_add_left]

/-- The Hilbert pairing agrees with the spatial weighted integral. -/
theorem weightedL2Pairing_eq_integral (hφ : MemLp φ ⊤ μ) (F G : Lp ℝ 2 μ) :
    weightedL2Pairing hφ F G = ∫ x, φ x * F x * G x ∂μ := by
  rw [weightedL2Pairing, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [boundedL2Mul_coe hφ F] with x hx
  rw [hx, RCLike.inner_apply]
  simp only [conj_trivial]
  ring

/-- The pairing identity for any chosen spatial representatives. -/
theorem weightedL2Pairing_eq_integral_of_ae (hφ : MemLp φ ⊤ μ)
    (F G : Lp ℝ 2 μ) {f g : α → ℝ} (hF : F =ᵐ[μ] f) (hG : G =ᵐ[μ] g) :
    weightedL2Pairing hφ F G = ∫ x, φ x * f x * g x ∂μ := by
  rw [weightedL2Pairing_eq_integral]
  apply integral_congr_ae
  filter_upwards [hF, hG] with x hx hy
  rw [hx, hy]

/-- Strong L² convergence of both fields passes through every bounded-coefficient pairing. -/
theorem tendsto_weightedL2Pairing {ι : Type*} {l : Filter ι}
    (hφ : MemLp φ ⊤ μ) (M : ℝ) (hM : ∀ᵐ x ∂μ, ‖φ x‖ ≤ M)
    {F G : ι → Lp ℝ 2 μ} {f g : Lp ℝ 2 μ}
    (hF : Tendsto F l (𝓝 f)) (hG : Tendsto G l (𝓝 g)) :
    Tendsto (fun n => weightedL2Pairing hφ (F n) (G n)) l
      (𝓝 (weightedL2Pairing hφ f g)) := by
  exact ((boundedL2Multiplier hφ M hM).continuous.tendsto f |>.comp hF).inner hG

end ASDExplicitGamma.Cold
