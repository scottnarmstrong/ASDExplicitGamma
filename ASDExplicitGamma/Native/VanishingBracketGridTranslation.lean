module

public import ASDExplicitGamma.Native.VanishingBracketTranslation

/-! Translation of the child-grid q3 remainder observations to centered cubes. -/
@[expose] public section

open MeasureTheory Homogenization Set ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Native ASDExplicitGamma.Main ASDExplicitGamma.Variational
open ASDExplicitGamma.Response ASDExplicitGamma.Triadic
open scoped RealInnerProductSpace

namespace ASDExplicitGamma.Native

noncomputable section

def q3GridCenterAxis (s : ℕ) (i : Fin (3^s)) : ℝ :=
  ((i.val : ℝ) + 1 / 2) / (3 : ℝ)^s

def q3GridCenterVector (s : ℕ) (ij : Fin (3^s) × Fin (3^s)) : Vec 2 :=
  ![q3GridCenterAxis s ij.1, q3GridCenterAxis s ij.2]

theorem q3GridHalfSide (s : ℕ) :
    mainCubeHalfSide (-(s : ℤ)) = (1 / 2 : ℝ) / (3 : ℝ)^s := by
  unfold mainCubeHalfSide cubeScaleFactor originCube
  rw [zpow_neg]
  simp only [zpow_natCast]
  ring

theorem q3GridCenter_left (s : ℕ) (i : Fin (3^s)) :
    q3GridCenterAxis s i - mainCubeHalfSide (-(s : ℤ)) =
      (i.val : ℝ) / (3 : ℝ)^s := by
  rw [q3GridHalfSide]
  dsimp [q3GridCenterAxis]
  have hd : 0 < (3 : ℝ)^s := by positivity
  field_simp
  ring

theorem q3GridCenter_right (s : ℕ) (i : Fin (3^s)) :
    q3GridCenterAxis s i + mainCubeHalfSide (-(s : ℤ)) =
      ((i.val + 1 : ℕ) : ℝ) / (3 : ℝ)^s := by
  rw [q3GridHalfSide]
  dsimp [q3GridCenterAxis]
  have hd : 0 < (3 : ℝ)^s := by positivity
  push_cast
  field_simp
  ring

/-- The geometric center of a q3 child rectangle, retained in its closed carrier. -/
noncomputable def q3GridRectangleCenter (s : ℕ)
    (ij : Fin (3^s) × Fin (3^s)) :
      closedRectangle
        ((ij.1.val : ℝ) / (3 : ℝ)^s) (((ij.1.val + 1 : ℕ) : ℝ) / (3 : ℝ)^s)
        ((ij.2.val : ℝ) / (3 : ℝ)^s) (((ij.2.val + 1 : ℕ) : ℝ) / (3 : ℝ)^s) := by
  refine ⟨q3GridCenterVector s ij, ?_⟩
  simp only [Gaussian.closedRectangle, mem_Icc]
  constructor
  · constructor
    · have h := q3GridCenter_left s ij.1
      have hhalf : 0 ≤ mainCubeHalfSide (-(s : ℤ)) := by
        rw [q3GridHalfSide]
        positivity
      have hcenter : (ij.1.val : ℝ) / (3 : ℝ)^s ≤ q3GridCenterAxis s ij.1 := by
        rw [← h]
        dsimp [q3GridCenterAxis]
        nlinarith [hhalf]
      have hrewrite : q3GridCenterVector s ij 0 = q3GridCenterAxis s ij.1 := by
        simp [q3GridCenterVector]
      rw [hrewrite]
      exact hcenter
    · have h := q3GridCenter_right s ij.1
      have hhalf : 0 ≤ mainCubeHalfSide (-(s : ℤ)) := by
        rw [q3GridHalfSide]
        positivity
      have hcenter : q3GridCenterAxis s ij.1 ≤
          ((ij.1.val + 1 : ℕ) : ℝ) / (3 : ℝ)^s := by
        rw [← h]
        dsimp [q3GridCenterAxis]
        nlinarith [hhalf]
      have hrewrite : q3GridCenterVector s ij 0 = q3GridCenterAxis s ij.1 := by
        simp [q3GridCenterVector]
      rw [hrewrite]
      exact hcenter
  · constructor
    · have h := q3GridCenter_left s ij.2
      have hhalf : 0 ≤ mainCubeHalfSide (-(s : ℤ)) := by
        rw [q3GridHalfSide]
        positivity
      have hcenter : (ij.2.val : ℝ) / (3 : ℝ)^s ≤ q3GridCenterAxis s ij.2 := by
        rw [← h]
        dsimp [q3GridCenterAxis]
        nlinarith [hhalf]
      have hrewrite : q3GridCenterVector s ij 1 = q3GridCenterAxis s ij.2 := by
        simp [q3GridCenterVector]
      rw [hrewrite]
      exact hcenter
    · have h := q3GridCenter_right s ij.2
      have hhalf : 0 ≤ mainCubeHalfSide (-(s : ℤ)) := by
        rw [q3GridHalfSide]
        positivity
      have hcenter : q3GridCenterAxis s ij.2 ≤
          ((ij.2.val + 1 : ℕ) : ℝ) / (3 : ℝ)^s := by
        rw [← h]
        dsimp [q3GridCenterAxis]
        nlinarith [hhalf]
      have hrewrite : q3GridCenterVector s ij 1 = q3GridCenterAxis s ij.2 := by
        simp [q3GridCenterVector]
      rw [hrewrite]
      exact hcenter

/- The point map carries the centered closed square onto the grid rectangle. -/
noncomputable def q3GridTranslatePoint (s : ℕ)
    (ij : Fin (3^s) × Fin (3^s)) :
    closedRectangle (-mainCubeHalfSide (-(s : ℤ)))
      (mainCubeHalfSide (-(s : ℤ))) (-mainCubeHalfSide (-(s : ℤ)))
      (mainCubeHalfSide (-(s : ℤ))) →
    closedRectangle
      ((ij.1.val : ℝ) / (3 : ℝ)^s) (((ij.1.val + 1 : ℕ) : ℝ) / (3 : ℝ)^s)
      ((ij.2.val : ℝ) / (3 : ℝ)^s) (((ij.2.val + 1 : ℕ) : ℝ) / (3 : ℝ)^s) := by
  let c := q3GridCenterVector s ij
  intro x
  refine ⟨x.1 + c, ?_⟩
  have hleft0 := q3GridCenter_left s ij.1
  have hright0 := q3GridCenter_right s ij.1
  have hleft1 := q3GridCenter_left s ij.2
  have hright1 := q3GridCenter_right s ij.2
  have hx0 := x.2.1
  have hx1 := x.2.2
  change (x.1 + c) 0 ∈ Set.Icc
        ((ij.1.val : ℝ) / (3 : ℝ)^s)
        (((ij.1.val + 1 : ℕ) : ℝ) / (3 : ℝ)^s) ∧
      (x.1 + c) 1 ∈ Set.Icc
        ((ij.2.val : ℝ) / (3 : ℝ)^s)
        (((ij.2.val + 1 : ℕ) : ℝ) / (3 : ℝ)^s)
  constructor
  · constructor
    · have hc : c 0 = q3GridCenterAxis s ij.1 := by simp [c, q3GridCenterVector]
      rw [Pi.add_apply, hc, ← hleft0]
      nlinarith [hx0.1]
    · have hc : c 0 = q3GridCenterAxis s ij.1 := by simp [c, q3GridCenterVector]
      rw [Pi.add_apply, hc, ← hright0]
      nlinarith [hx0.2]
  · constructor
    · have hc : c 1 = q3GridCenterAxis s ij.2 := by simp [c, q3GridCenterVector]
      rw [Pi.add_apply, hc, ← hleft1]
      nlinarith [hx1.1]
    · have hc : c 1 = q3GridCenterAxis s ij.2 := by simp [c, q3GridCenterVector]
      rw [Pi.add_apply, hc, ← hright1]
      nlinarith [hx1.2]

/-- Pull a child-grid field back to the centered square of the same side. -/
noncomputable def q3GridTranslateField (s : ℕ)
    (ij : Fin (3^s) × Fin (3^s)) :
    C(closedRectangle
        ((ij.1.val : ℝ) / (3 : ℝ)^s) (((ij.1.val + 1 : ℕ) : ℝ) / (3 : ℝ)^s)
        ((ij.2.val : ℝ) / (3 : ℝ)^s) (((ij.2.val + 1 : ℕ) : ℝ) / (3 : ℝ)^s), ℝ) →L[ℝ]
      C(closedRectangle (-mainCubeHalfSide (-(s : ℤ)))
        (mainCubeHalfSide (-(s : ℤ)))
        (-mainCubeHalfSide (-(s : ℤ)))
        (mainCubeHalfSide (-(s : ℤ))), ℝ) :=
  ContinuousMap.compCLM ℝ ℝ
    ⟨q3GridTranslatePoint s ij,
      (continuous_subtype_val.add continuous_const).subtype_mk _⟩

@[simp] theorem q3GridTranslateField_apply (s : ℕ)
    (ij : Fin (3^s) × Fin (3^s))
    (f : C(closedRectangle
      ((ij.1.val : ℝ) / (3 : ℝ)^s) (((ij.1.val + 1 : ℕ) : ℝ) / (3 : ℝ)^s)
      ((ij.2.val : ℝ) / (3 : ℝ)^s) (((ij.2.val + 1 : ℕ) : ℝ) / (3 : ℝ)^s), ℝ))
    (x : closedRectangle (-mainCubeHalfSide (-(s : ℤ)))
      (mainCubeHalfSide (-(s : ℤ))) (-mainCubeHalfSide (-(s : ℤ)))
      (mainCubeHalfSide (-(s : ℤ)))) :
    q3GridTranslateField s ij f x = f (q3GridTranslatePoint s ij x) := by
  rfl

/-- Translating a centered q3 remainder observation to a child rectangle is
exactly the white-noise translate of the centered remainder observation. -/
theorem q3GridRangeValue_translate (s n : ℕ) (β : ℝ)
    (ij : Fin (3^s) × Fin (3^s)) (u : WhiteNoise) :
    q3GridTranslateField s ij
        (q3H3RangeValue
          ((ij.1.val : ℝ) / (3 : ℝ)^s)
          (((ij.1.val + 1 : ℕ) : ℝ) / (3 : ℝ)^s)
          ((ij.2.val : ℝ) / (3 : ℝ)^s)
          (((ij.2.val + 1 : ℕ) : ℝ) / (3 : ℝ)^s)
          β (q3GridKernelScale s n)
          (q3H3RangeFactor
            ((ij.1.val : ℝ) / (3 : ℝ)^s)
            (((ij.1.val + 1 : ℕ) : ℝ) / (3 : ℝ)^s)
            ((ij.2.val : ℝ) / (3 : ℝ)^s)
            (((ij.2.val + 1 : ℕ) : ℝ) / (3 : ℝ)^s)
            β (q3GridKernelScale s n) u)) =
      q3H3RangeValue
        (-mainCubeHalfSide (-(s : ℤ))) (mainCubeHalfSide (-(s : ℤ)))
        (-mainCubeHalfSide (-(s : ℤ))) (mainCubeHalfSide (-(s : ℤ)))
        β (q3GridKernelScale s n)
        (q3H3RangeFactor
          (-mainCubeHalfSide (-(s : ℤ))) (mainCubeHalfSide (-(s : ℤ)))
          (-mainCubeHalfSide (-(s : ℤ))) (mainCubeHalfSide (-(s : ℤ)))
          β (q3GridKernelScale s n) (q3WhiteNoiseTranslate (q3GridCenterVector s ij) u)) := by
  let a := (ij.1.val : ℝ) / (3 : ℝ)^s
  let b := ((ij.1.val + 1 : ℕ) : ℝ) / (3 : ℝ)^s
  let c := (ij.2.val : ℝ) / (3 : ℝ)^s
  let d := ((ij.2.val + 1 : ℕ) : ℝ) / (3 : ℝ)^s
  let center := q3GridCenterVector s ij
  have hd : 0 < (3 : ℝ)^s := by positivity
  have hab : a < b := by
    dsimp [a, b]
    apply (div_lt_div_iff₀ hd hd).2
    have hnum : (ij.1.val : ℝ) < ((ij.1.val + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.lt_succ_self ij.1.val
    exact mul_lt_mul_of_pos_right hnum hd
  have hcd : c < d := by
    dsimp [c, d]
    apply (div_lt_div_iff₀ hd hd).2
    have hnum : (ij.2.val : ℝ) < ((ij.2.val + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.lt_succ_self ij.2.val
    exact mul_lt_mul_of_pos_right hnum hd
  ext x
  rw [q3GridTranslateField_apply,
    q3H3RangeValue_factor a b c d β hab hcd (q3GridKernelScale s n) u,
    q3H3RangeValue_factor
      (-mainCubeHalfSide (-(s : ℤ))) (mainCubeHalfSide (-(s : ℤ)))
      (-mainCubeHalfSide (-(s : ℤ))) (mainCubeHalfSide (-(s : ℤ))) β
      (by
        have hp : 0 < mainCubeHalfSide (-(s : ℤ)) := by
          rw [q3GridHalfSide]
          positivity
        linarith)
      (by
        have hp : 0 < mainCubeHalfSide (-(s : ℤ)) := by
          rw [q3GridHalfSide]
          positivity
        linarith)
      (q3GridKernelScale s n) (q3WhiteNoiseTranslate center u) x]
  change q3Convolution β (q3GridKernelScale s n) h3Zero u
      (q3GridTranslatePoint s ij x).1 =
    q3Convolution β (q3GridKernelScale s n) h3Zero
      (q3WhiteNoiseTranslate center u) x.1
  rw [q3Convolution_translate]
  rfl

theorem q3GridCenterPoint (s : ℕ) (ij : Fin (3^s) × Fin (3^s)) :
    q3GridTranslatePoint s ij (mainCubeRectangleCenter (-(s : ℤ))) =
      q3GridRectangleCenter s ij := by
  have hc : (mainCubeRectangleCenter (-(s : ℤ))).1 = 0 := by
    change cubeCenter (originCube 2 (-(s : ℤ))) = 0
    ext i
    simp [cubeCenter, originCube]
  apply Subtype.ext
  change (mainCubeRectangleCenter (-(s : ℤ))).1 + q3GridCenterVector s ij =
    q3GridCenterVector s ij
  rw [hc]
  simp

theorem q3GridCenteringMap_translate (s : ℕ)
    (ij : Fin (3^s) × Fin (3^s))
    (f : C(closedRectangle
      ((ij.1.val : ℝ) / (3 : ℝ)^s) (((ij.1.val + 1 : ℕ) : ℝ) / (3 : ℝ)^s)
      ((ij.2.val : ℝ) / (3 : ℝ)^s) (((ij.2.val + 1 : ℕ) : ℝ) / (3 : ℝ)^s), ℝ)) :
    q3GridTranslateField s ij (centeringMap (q3GridRectangleCenter s ij) f) =
      centeringMap (mainCubeRectangleCenter (-(s : ℤ)))
        (q3GridTranslateField s ij f) := by
  ext x
  simp only [q3GridTranslateField_apply, centeringMap_apply]
  rw [← q3GridCenterPoint s ij]

theorem q3GridRemainderValueFactor_translate (s n : ℕ) (β : ℝ)
    (ij : Fin (3^s) × Fin (3^s)) (u : WhiteNoise) :
    q3GridTranslateField s ij
        (q3RemainderValueFactor
          ((ij.1.val : ℝ) / (3 : ℝ)^s)
          (((ij.1.val + 1 : ℕ) : ℝ) / (3 : ℝ)^s)
          ((ij.2.val : ℝ) / (3 : ℝ)^s)
          (((ij.2.val + 1 : ℕ) : ℝ) / (3 : ℝ)^s)
          β (q3GridKernelScale s n) (q3GridRectangleCenter s ij) u) =
      q3RemainderValueFactor
        (-mainCubeHalfSide (-(s : ℤ))) (mainCubeHalfSide (-(s : ℤ)))
        (-mainCubeHalfSide (-(s : ℤ))) (mainCubeHalfSide (-(s : ℤ)))
        β (q3GridKernelScale s n) (mainCubeRectangleCenter (-(s : ℤ)))
        (q3WhiteNoiseTranslate (q3GridCenterVector s ij) u) := by
  simp only [q3RemainderValueFactor, ContinuousLinearMap.comp_apply]
  rw [q3GridCenteringMap_translate, q3GridRangeValue_translate]

noncomputable def q3GridRemainderRieszGradientExplicit (s n : ℕ) (β : ℝ)
    (ij : Fin (3^s) × Fin (3^s))
    (x₀ : closedRectangle
      ((ij.1.val : ℝ) / (3 : ℝ)^s) (((ij.1.val + 1 : ℕ) : ℝ) / (3 : ℝ)^s)
      ((ij.2.val : ℝ) / (3 : ℝ)^s) (((ij.2.val + 1 : ℕ) : ℝ) / (3 : ℝ)^s))
    (O : C(closedRectangle
      ((ij.1.val : ℝ) / (3 : ℝ)^s) (((ij.1.val + 1 : ℕ) : ℝ) / (3 : ℝ)^s)
      ((ij.2.val : ℝ) / (3 : ℝ)^s) (((ij.2.val + 1 : ℕ) : ℝ) / (3 : ℝ)^s), ℝ)
      →L[ℝ] ℝ) : WhiteNoise :=
  (InnerProductSpace.toDual ℝ WhiteNoise).symm
    (O.comp (q3RemainderValueFactor
      ((ij.1.val : ℝ) / (3 : ℝ)^s) (((ij.1.val + 1 : ℕ) : ℝ) / (3 : ℝ)^s)
      ((ij.2.val : ℝ) / (3 : ℝ)^s) (((ij.2.val + 1 : ℕ) : ℝ) / (3 : ℝ)^s)
      β (q3GridKernelScale s n) x₀))

noncomputable def q3GridTranslatedTraceObservation (s : ℕ)
    (ij : Fin (3^s) × Fin (3^s)) (ν σ : ℝ)
    (k : ResponseCoefficient (openCubeSet (originCube 2 (-(s : ℤ))))) :
    C(closedRectangle
      ((ij.1.val : ℝ) / (3 : ℝ)^s) (((ij.1.val + 1 : ℕ) : ℝ) / (3 : ℝ)^s)
      ((ij.2.val : ℝ) / (3 : ℝ)^s) (((ij.2.val + 1 : ℕ) : ℝ) / (3 : ℝ)^s), ℝ)
      →L[ℝ] ℝ :=
  (mainCubeTraceDerivativeObservation (-(s : ℤ)) ν σ k).comp
    (q3GridTranslateField s ij)

theorem q3Riesz_comp_linearIsometry
    (U : WhiteNoise ≃ₗᵢ[ℝ] WhiteNoise)
    (A : WhiteNoise →L[ℝ] ℝ) :
    (InnerProductSpace.toDual ℝ WhiteNoise).symm
        (A.comp U.toLinearIsometry.toContinuousLinearMap) =
      U.symm ((InnerProductSpace.toDual ℝ WhiteNoise).symm A) := by
  apply (InnerProductSpace.toDual ℝ WhiteNoise).injective
  rw [(InnerProductSpace.toDual ℝ WhiteNoise).apply_symm_apply]
  ext u
  change A (U u) =
    ⟪U.symm ((InnerProductSpace.toDual ℝ WhiteNoise).symm A), u⟫
  have hdual : A (U u) =
      ⟪(InnerProductSpace.toDual ℝ WhiteNoise).symm A, U u⟫ := by
    have h := congrArg (fun f : WhiteNoise →L[ℝ] ℝ => f (U u))
      ((InnerProductSpace.toDual ℝ WhiteNoise).apply_symm_apply A)
    change ⟪(InnerProductSpace.toDual ℝ WhiteNoise).symm A, U u⟫ = A (U u) at h
    exact h.symm
  calc
    A (U u) = ⟪(InnerProductSpace.toDual ℝ WhiteNoise).symm A, U u⟫ := hdual
    _ = ⟪U.symm ((InnerProductSpace.toDual ℝ WhiteNoise).symm A), u⟫ := by
      simpa only [U.apply_symm_apply] using
        (U.inner_map_map
          (U.symm ((InnerProductSpace.toDual ℝ WhiteNoise).symm A)) u)

noncomputable def q3GridRemainderAverageGradientExplicit (s n : ℕ) (β : ℝ)
    (x₀ : ∀ ij : Fin (3^s) × Fin (3^s),
      closedRectangle
        ((ij.1.val : ℝ) / (3 : ℝ)^s) (((ij.1.val + 1 : ℕ) : ℝ) / (3 : ℝ)^s)
        ((ij.2.val : ℝ) / (3 : ℝ)^s) (((ij.2.val + 1 : ℕ) : ℝ) / (3 : ℝ)^s))
    (O : ∀ ij : Fin (3^s) × Fin (3^s), C(closedRectangle
      ((ij.1.val : ℝ) / (3 : ℝ)^s) (((ij.1.val + 1 : ℕ) : ℝ) / (3 : ℝ)^s)
      ((ij.2.val : ℝ) / (3 : ℝ)^s) (((ij.2.val + 1 : ℕ) : ℝ) / (3 : ℝ)^s), ℝ)
      →L[ℝ] ℝ) : WhiteNoise :=
  (((Finset.univ : Finset (Fin (3^s) × Fin (3^s))).card : ℝ)⁻¹) •
    ∑ ij : Fin (3^s) × Fin (3^s),
      q3GridRemainderRieszGradientExplicit s n β ij (x₀ ij) (O ij)

theorem q3GridRemainderRiesz_average_sq_le_support_overlap_explicit
    (s n : ℕ) (hn : 1 ≤ n) (hns : n ≤ s) (β : ℝ)
    (x₀ : ∀ ij : Fin (3^s) × Fin (3^s),
      closedRectangle
        ((ij.1.val : ℝ) / (3 : ℝ)^s) (((ij.1.val + 1 : ℕ) : ℝ) / (3 : ℝ)^s)
        ((ij.2.val : ℝ) / (3 : ℝ)^s) (((ij.2.val + 1 : ℕ) : ℝ) / (3 : ℝ)^s))
    (O : ∀ ij : Fin (3^s) × Fin (3^s), C(closedRectangle
      ((ij.1.val : ℝ) / (3 : ℝ)^s) (((ij.1.val + 1 : ℕ) : ℝ) / (3 : ℝ)^s)
      ((ij.2.val : ℝ) / (3 : ℝ)^s) (((ij.2.val + 1 : ℕ) : ℝ) / (3 : ℝ)^s), ℝ)
      →L[ℝ] ℝ) :
    ‖q3GridRemainderAverageGradientExplicit s n β x₀ O‖ ^ 2 ≤
      q3GridOverlapFactor s n *
        (((Finset.univ : Finset (Fin (3^s) × Fin (3^s))).card : ℝ)⁻¹) *
          ∑ ij : Fin (3^s) × Fin (3^s),
            ‖q3GridRemainderRieszGradientExplicit s n β ij (x₀ ij) (O ij)‖ ^ 2 := by
  classical
  let S : Finset (Fin (3^s) × Fin (3^s)) := Finset.univ
  let U : Vec 2 → Finset (Fin (3^s) × Fin (3^s)) := q3GridActiveFinset s n
  let N : ℝ := (S.card : ℝ)
  let M : ℝ := q3GridOverlapFactor s n * N
  let a : Fin (3^s) × Fin (3^s) → ℝ := fun ij => (ij.1.val : ℝ) / (3 : ℝ)^s
  let b : Fin (3^s) × Fin (3^s) → ℝ := fun ij => ((ij.1.val + 1 : ℕ) : ℝ) / (3 : ℝ)^s
  let c : Fin (3^s) × Fin (3^s) → ℝ := fun ij => (ij.2.val : ℝ) / (3 : ℝ)^s
  let d : Fin (3^s) × Fin (3^s) → ℝ := fun ij => ((ij.2.val + 1 : ℕ) : ℝ) / (3 : ℝ)^s
  let L : Fin (3^s) × Fin (3^s) → {l : ℝ // 0 < l} := fun _ => q3GridKernelScale s n
  let A : (Fin (3^s) × Fin (3^s)) → Set (Vec 2) := fun ij =>
    q3ExpandedRectangle (a ij) (b ij) (c ij) (d ij) (L ij)
  have hK : 0 < (3 : ℝ)^s := by positivity
  have hab : ∀ ij ∈ S, a ij < b ij := by
    intro ij _
    dsimp [a, b]
    apply (div_lt_div_iff₀ hK hK).2
    push_cast
    exact mul_lt_mul_of_pos_right
      (by exact_mod_cast Nat.lt_succ_self ij.1.val) hK
  have hcd : ∀ ij ∈ S, c ij < d ij := by
    intro ij _
    dsimp [c, d]
    apply (div_lt_div_iff₀ hK hK).2
    push_cast
    exact mul_lt_mul_of_pos_right
      (by exact_mod_cast Nat.lt_succ_self ij.2.val) hK
  have hNcard : S.card = (3^s)^2 := by simp [S, pow_two, Fintype.card_prod]
  have hN : 0 < N := by
    dsimp [N]
    rw [hNcard]
    positivity
  have hactive : ∀ x ij, ij ∈ U x ↔ x ∈ A ij := by
    intro x ij
    simp [U, A, q3GridActiveFinset, q3GridExpandedSupport,
      q3GridKernelScale, q3ExpandedRectangle, a, b, c, d, L]
  have hratio (x : Vec 2) :
      ((U x).card : ℝ) / N ≤ q3GridOverlapFactor s n := by
    have h := q3GridActiveFinset_card_ratio_le s n hn hns x
    simpa [U, N, S, hNcard, pow_two] using h
  have hM : 0 ≤ M := by
    dsimp [M, q3GridOverlapFactor]
    positivity
  have hoverlap : ∀ x : Vec 2, ((S ∩ U x).card : ℝ) ≤ M := by
    intro x
    have hcard : (S ∩ U x).card = (U x).card := by simp [S]
    rw [hcard]
    dsimp [M]
    exact (div_le_iff₀ hN).1 (by simpa [N] using hratio x)
  have hgeneric := q3RemainderRiesz_average_sq_le_support_overlap
    S a b c d (fun _ => β) L x₀ O hab hcd M hM hN U hactive hoverlap
  have hconvert : M * N⁻¹ ^ 2 = q3GridOverlapFactor s n * N⁻¹ := by
    dsimp [M]
    calc
      (q3GridOverlapFactor s n * N) * N⁻¹ ^ 2 =
          q3GridOverlapFactor s n * (N * N⁻¹ ^ 2) := by ring
      _ = q3GridOverlapFactor s n * N⁻¹ := by
        congr 1
        field_simp [ne_of_gt hN]
  have hgeneric' := hgeneric
  rw [show M * (S.card : ℝ)⁻¹ ^ 2 =
      q3GridOverlapFactor s n * (S.card : ℝ)⁻¹ by
        simpa [N] using hconvert] at hgeneric'
  simpa [q3GridRemainderAverageGradientExplicit,
    q3GridRemainderRieszGradientExplicit, S, N, hNcard, pow_two] using hgeneric'

/-- At shell depths beyond the grid depth the overlap cap is one, so ordinary
finite Cauchy--Schwarz gives the all-child average bound. This extends the
localized support estimate above to every source shell `n ≥ 1`. -/
theorem q3GridRemainderRiesz_average_sq_le_support_overlap_explicit_all
    (s n : ℕ) (hn : 1 ≤ n) (β : ℝ)
    (x₀ : ∀ ij : Fin (3^s) × Fin (3^s),
      closedRectangle
        ((ij.1.val : ℝ) / (3 : ℝ)^s) (((ij.1.val + 1 : ℕ) : ℝ) / (3 : ℝ)^s)
        ((ij.2.val : ℝ) / (3 : ℝ)^s) (((ij.2.val + 1 : ℕ) : ℝ) / (3 : ℝ)^s))
    (O : ∀ ij : Fin (3^s) × Fin (3^s), C(closedRectangle
      ((ij.1.val : ℝ) / (3 : ℝ)^s) (((ij.1.val + 1 : ℕ) : ℝ) / (3 : ℝ)^s)
      ((ij.2.val : ℝ) / (3 : ℝ)^s) (((ij.2.val + 1 : ℕ) : ℝ) / (3 : ℝ)^s), ℝ)
      →L[ℝ] ℝ) :
    ‖q3GridRemainderAverageGradientExplicit s n β x₀ O‖ ^ 2 ≤
      q3GridOverlapFactor s n *
        (((Finset.univ : Finset (Fin (3^s) × Fin (3^s))).card : ℝ)⁻¹) *
          ∑ ij : Fin (3^s) × Fin (3^s),
            ‖q3GridRemainderRieszGradientExplicit s n β ij (x₀ ij) (O ij)‖ ^ 2 := by
  classical
  by_cases hns : n ≤ s
  · exact q3GridRemainderRiesz_average_sq_le_support_overlap_explicit
      s n hn hns β x₀ O
  · have hsn : s - n = 0 := by omega
    have hfactor : q3GridOverlapFactor s n = 1 := by
      unfold q3GridOverlapFactor
      rw [hsn]
      exact min_eq_left (by norm_num)
    let S : Finset (Fin (3^s) × Fin (3^s)) := Finset.univ
    let N : ℝ := (S.card : ℝ)
    have hNcard : S.card = (3^s)^2 := by
      simp [S, pow_two, Fintype.card_prod]
    have hN : 0 < N := by
      dsimp [N]
      rw [hNcard]
      positivity
    have hgeneric := whiteNoise_average_sq_le_supportOverlap
      S
      (fun ij => q3GridRemainderRieszGradientExplicit s n β ij (x₀ ij) (O ij))
      (fun _ => Set.univ) (fun _ => S) N (le_of_lt hN) hN
      (by intro x ij; simp [S])
      (by intro ij hij; simp)
      (by
        filter_upwards [] with x
        simp [S, N])
    have hconvert : N * N⁻¹ ^ 2 = N⁻¹ := by
      field_simp [ne_of_gt hN]
    have hgeneric' := hgeneric
    rw [hconvert] at hgeneric'
    simpa [q3GridRemainderAverageGradientExplicit,
      q3GridRemainderRieszGradientExplicit, S, N, hNcard, hfactor,
      pow_two] using hgeneric'

end

end ASDExplicitGamma.Native
