module

public import ASDExplicitGamma.Scalar.GSlotTheta

/-! Measurability in the old field of the tiled positive-Haar energy of the potential-slot
Wick source, through the continuity of the partial forms in the increment space. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar

open Homogenization MeasureTheory Filter ASDExplicitGamma.Triadic ASDExplicitGamma.Variational
  ASDExplicitGamma.Gaussian ASDExplicitGamma.Native
open scoped BigOperators Topology InnerProductSpace ENNReal

noncomputable section

section Form

variable {Q : TriadicCube 2} {m : ℕ}

theorem partialForm_eq (N : ℕ) (a b : TiledHaarField Q m) :
    (tiledPartialForm Q m N).form a b =
      ∑ j ∈ Finset.univ ×ˢ Finset.univ ×ˢ Finset.range (N + 1),
        ⟪(PhiL Q m a : GSpace Q m) j, (PhiL Q m b : GSpace Q m) j⟫_ℝ := by
  simp only [tiledPartialForm, PsdForm.ofMaps, LinearMap.mk₂_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [phiL_apply, phiL_apply]
  unfold gseqFun
  rw [real_inner_smul_left, real_inner_smul_right, ← mul_assoc,
    Real.mul_self_sqrt (gWt_nonneg (Real.sqrt_nonneg _) j)]
  rfl

end Form

variable (nQ : ℤ) (m : ℕ) (b : ℝ) (L : {l : ℝ // 0 < l})

local notation "QQ" => originCube 2 nQ

/-- The increment-space image of the potential-slot field of an optional mode. -/
def cOpt (o : Option whiteBasisIndex) (y : GSpace QQ m) : GSpace QQ m :=
  match o with
  | none => 0
  | some a => gSlotA nQ m b L a y

theorem gSlotOpt_spec (o : Option whiteBasisIndex) (g : TiledL2Field QQ m) (j : GIdx QQ m) :
    (PhiL QQ m (gSlotOpt nQ m b L o g) : GSpace QQ m) j =
      incL j.1.1 j.2.2 ((cOpt nQ m b L o (PsiL QQ m g) : GSpace QQ m) j) := by
  cases o with
  | none =>
    have h1 : gSlotOpt nQ m b L none g = 0 := rfl
    have h2 : cOpt nQ m b L none (PsiL QQ m g) = 0 := rfl
    rw [h1, h2, map_zero]
    simp
  | some a =>
    have h1 : gSlotOpt nQ m b L (some a) g = gSlot nQ m b L a g := rfl
    have h2 : cOpt nQ m b L (some a) (PsiL QQ m g) = gSlotA nQ m b L a (PsiL QQ m g) := rfl
    rw [h1, h2]
    exact gSlot_spec nQ m b L a g j

theorem gform_eq (N : ℕ) (ea ec : Option whiteBasisIndex) (g g' : TiledL2Field QQ m) :
    (tiledPartialForm QQ m N).form (gSlotOpt nQ m b L ea g) (gSlotOpt nQ m b L ec g') =
      ∑ j ∈ (Finset.univ ×ˢ Finset.univ ×ˢ Finset.range (N + 1) : Finset (GIdx QQ m)),
        ⟪incL j.1.1 j.2.2 ((cOpt nQ m b L ea (PsiL QQ m g) : GSpace QQ m) j),
          incL j.1.1 j.2.2 ((cOpt nQ m b L ec (PsiL QQ m g') : GSpace QQ m) j)⟫_ℝ := by
  rw [partialForm_eq]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [gSlotOpt_spec, gSlotOpt_spec]

theorem cOpt_continuous (o : Option whiteBasisIndex) :
    Continuous (cOpt nQ m b L o) := by
  cases o with
  | none => exact continuous_const
  | some a => exact (gSlotA nQ m b L a).continuous

theorem theta_continuous : Continuous (gSlotTheta nQ m) := by
  have hC : 0 ≤ (cubeVolume QQ)⁻¹ := (inv_pos.2 (cubeVolume_pos QQ)).le
  refine (LipschitzWith.of_dist_le_mul (K := ⟨Real.sqrt (cubeVolume QQ)⁻¹, Real.sqrt_nonneg _⟩)
    fun u u' => ?_).continuous
  rw [dist_eq_norm, dist_eq_norm]
  have h := theta_sub_norm_sq nQ m u u'
  have h2 : ‖gSlotTheta nQ m u - gSlotTheta nQ m u'‖ ^ 2 ≤
      (Real.sqrt (cubeVolume QQ)⁻¹ * ‖u - u'‖) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hC]; exact h
  show ‖gSlotTheta nQ m u - gSlotTheta nQ m u'‖ ≤ Real.sqrt (cubeVolume QQ)⁻¹ * ‖u - u'‖
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).1 h2

theorem theta_norm_sq (u : HilbertVectorL2 (openCubeSet QQ)) :
    ‖gSlotTheta nQ m u‖ ^ 2 = lemmaVTiledWeakEnergy QQ m (rep2 nQ m u).1 :=
  psi_norm_sq QQ m _

theorem gcoef_continuous (N : ℕ) (ea ec : Option whiteBasisIndex) :
    Continuous fun p : HilbertVectorL2 (openCubeSet QQ) × HilbertVectorL2 (openCubeSet QQ) =>
      (tiledPartialForm QQ m N).form (gSlotOpt nQ m b L ea (rep2 nQ m p.1))
        (gSlotOpt nQ m b L ec (rep2 nQ m p.2)) := by
  have hform : (fun p : HilbertVectorL2 (openCubeSet QQ) × HilbertVectorL2 (openCubeSet QQ) =>
      (tiledPartialForm QQ m N).form (gSlotOpt nQ m b L ea (rep2 nQ m p.1))
        (gSlotOpt nQ m b L ec (rep2 nQ m p.2))) = fun p =>
      ∑ j ∈ (Finset.univ ×ˢ Finset.univ ×ˢ Finset.range (N + 1) : Finset (GIdx QQ m)),
        ⟪incL j.1.1 j.2.2 ((cOpt nQ m b L ea (gSlotTheta nQ m p.1) : GSpace QQ m) j),
          incL j.1.1 j.2.2 ((cOpt nQ m b L ec (gSlotTheta nQ m p.2) : GSpace QQ m) j)⟫_ℝ := by
    funext p
    exact gform_eq nQ m b L N ea ec _ _
  rw [hform]
  refine continuous_finsetSum _ fun j _ => Continuous.inner ?_ ?_
  · exact (incL j.1.1 j.2.2).continuous.comp
      ((lp.evalCLM (𝕜 := ℝ) (E := GFib QQ m) (p := 2) j).continuous.comp
        ((cOpt_continuous nQ m b L ea).comp
          ((theta_continuous nQ m).comp continuous_fst)))
  · exact (incL j.1.1 j.2.2).continuous.comp
      ((lp.evalCLM (𝕜 := ℝ) (E := GFib QQ m) (p := 2) j).continuous.comp
        ((cOpt_continuous nQ m b L ec).comp
          ((theta_continuous nQ m).comp continuous_snd)))

end

end ASDExplicitGamma.Scalar
