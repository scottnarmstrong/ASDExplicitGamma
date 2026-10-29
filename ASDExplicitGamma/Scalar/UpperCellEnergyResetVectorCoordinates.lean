module

public import ASDExplicitGamma.Scalar.UpperCellEnergyResetStationaryProjection

/-! Coordinatewise stationary L2 projection on the actual Euclidean vector
carrier, for preservation of the Gaussian closed span. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Algsuperdiff.Probability.Stationary
noncomputable section
variable {Ω : Type*} [MeasurableSpace Ω]

noncomputable def upperCellResetCoordEmbedding (i : Fin 2) :
    ℝ →L[ℝ] HilbertVec 2 :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.single ℝ (fun _ : Fin 2 => ℝ) i)

noncomputable def upperCellResetCoordLift
    (μ : Measure Ω) (i : Fin 2) :
    ScalarL2 μ →L[ℝ]
      VectorL2 2 μ :=
  (upperCellResetCoordEmbedding i).compLpL 2 μ

theorem upper_cell_reset_coord_lift
    (μ : Measure Ω) (i j : Fin 2)
    (f : ScalarL2 μ) :
    vectorL2Coord i
      (upperCellResetCoordLift μ j f) = if i = j then f else 0 := by
  change (PiLp.proj (𝕜 := ℝ) (p := 2) (β := fun _ : Fin 2 => ℝ) i).compLpL
      2 μ (upperCellResetCoordLift μ j f) = if i = j then f else 0
  apply Lp.ext
  have hL := (upperCellResetCoordEmbedding j).coeFn_compLpL f
  have hproj := (PiLp.proj (𝕜 := ℝ) (p := 2) (β := fun _ : Fin 2 => ℝ) i)
    |>.coeFn_compLpL (upperCellResetCoordLift μ j f)
  have hzero : ((0 : ScalarL2 μ) :
      Ω → ℝ) =ᵐ[μ] 0 :=
    Lp.coeFn_zero ℝ 2 μ
  filter_upwards [hL, hproj, hzero] with a hL hproj hzero
  have hLift : (upperCellResetCoordLift μ j f : Ω → HilbertVec 2) a =
      upperCellResetCoordEmbedding j ((f : Ω → ℝ) a) := hL
  rw [hproj, hLift]
  by_cases hij : i = j
  · subst i
    simp [upperCellResetCoordEmbedding]
  · simpa [upperCellResetCoordEmbedding, hij] using hzero.symm

theorem upper_cell_reset_vector_inner
    (μ : Measure Ω)
    (F G : VectorL2 2 μ) :
    inner ℝ F G = ∑ i : Fin 2,
      inner ℝ
        (vectorL2Coord i F)
        (vectorL2Coord i G) := by
  rw [MeasureTheory.L2.inner_def]
  simp only [PiLp.inner_apply]
  have hcoordF (i : Fin 2) :=
    (PiLp.proj (𝕜 := ℝ) (p := 2) (β := fun _ : Fin 2 => ℝ) i).coeFn_compLpL F
  have hcoordG (i : Fin 2) :=
    (PiLp.proj (𝕜 := ℝ) (p := 2) (β := fun _ : Fin 2 => ℝ) i).coeFn_compLpL G
  have hterm (i : Fin 2) :
      ∫ a : Ω, inner ℝ ((F a).ofLp i) ((G a).ofLp i) ∂μ =
        inner ℝ (vectorL2Coord i F)
          (vectorL2Coord i G) := by
    rw [MeasureTheory.L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hcoordF i, hcoordG i] with a ha hb
    change (vectorL2Coord i F :
      Ω → ℝ) a = _ at ha
    change (vectorL2Coord i G :
      Ω → ℝ) a = _ at hb
    calc
      inner ℝ ((F a).ofLp i) ((G a).ofLp i) =
          inner ℝ ((PiLp.proj (𝕜 := ℝ) (p := 2) (β := fun _ : Fin 2 => ℝ) i) (F a))
            ((PiLp.proj (𝕜 := ℝ) (p := 2) (β := fun _ : Fin 2 => ℝ) i) (G a)) := rfl
      _ = inner ℝ
          ((vectorL2Coord i F : Ω → ℝ) a)
          ((vectorL2Coord i G : Ω → ℝ) a) :=
        by rw [← ha, ← hb]
  have hInt (i : Fin 2) :
      Integrable (fun a : Ω => inner ℝ ((F a).ofLp i) ((G a).ofLp i))
        μ := by
    apply (MeasureTheory.L2.integrable_inner
      (vectorL2Coord i F)
      (vectorL2Coord i G)).congr
    filter_upwards [hcoordF i, hcoordG i] with a ha hb
    change (vectorL2Coord i F :
      Ω → ℝ) a = _ at ha
    change (vectorL2Coord i G :
      Ω → ℝ) a = _ at hb
    calc
      inner ℝ
          ((vectorL2Coord i F : Ω → ℝ) a)
          ((vectorL2Coord i G : Ω → ℝ) a) =
          inner ℝ ((PiLp.proj (𝕜 := ℝ) (p := 2) (β := fun _ : Fin 2 => ℝ) i) (F a))
            ((PiLp.proj (𝕜 := ℝ) (p := 2) (β := fun _ : Fin 2 => ℝ) i) (G a)) := by
              rw [ha, hb]
      _ = inner ℝ ((F a).ofLp i) ((G a).ofLp i) := rfl
  rw [integral_finsetSum]
  · simp_rw [hterm]
  · intro i hi
    exact hInt i

theorem upper_cell_reset_vector_ext
    (μ : Measure Ω)
    {F G : VectorL2 2 μ}
    (h : ∀ i : Fin 2,
      vectorL2Coord i F =
        vectorL2Coord i G) : F = G := by
  apply Lp.ext
  have hF (i : Fin 2) :=
    (PiLp.proj (𝕜 := ℝ) (p := 2) (β := fun _ : Fin 2 => ℝ) i).coeFn_compLpL F
  have hG (i : Fin 2) :=
    (PiLp.proj (𝕜 := ℝ) (p := 2) (β := fun _ : Fin 2 => ℝ) i).coeFn_compLpL G
  have he (i : Fin 2) := Lp.ext_iff.mp (h i)
  filter_upwards [hF 0, hG 0, hF 1, hG 1, he 0, he 1] with a hf0 hg0 hf1 hg1 he0 he1
  apply PiLp.ext
  intro i
  fin_cases i
  · calc
      (F a).ofLp 0 = PiLp.proj (𝕜 := ℝ) (p := 2) (β := fun _ : Fin 2 => ℝ) 0 (F a) := rfl
      _ = (vectorL2Coord 0 F :
        Ω → ℝ) a := hf0.symm
      _ = (vectorL2Coord 0 G :
        Ω → ℝ) a := he0
      _ = PiLp.proj (𝕜 := ℝ) (p := 2) (β := fun _ : Fin 2 => ℝ) 0 (G a) := hg0
      _ = (G a).ofLp 0 := rfl
  · calc
      (F a).ofLp 1 = PiLp.proj (𝕜 := ℝ) (p := 2) (β := fun _ : Fin 2 => ℝ) 1 (F a) := rfl
      _ = (vectorL2Coord 1 F :
        Ω → ℝ) a := hf1.symm
      _ = (vectorL2Coord 1 G :
        Ω → ℝ) a := he1
      _ = PiLp.proj (𝕜 := ℝ) (p := 2) (β := fun _ : Fin 2 => ℝ) 1 (G a) := hg1
      _ = (G a).ofLp 1 := rfl


end
end ASDExplicitGamma.Scalar
