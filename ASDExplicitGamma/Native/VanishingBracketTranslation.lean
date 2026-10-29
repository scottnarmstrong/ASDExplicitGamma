module

public import ASDExplicitGamma.Native.Q3GridOverlap
public import ASDExplicitGamma.Native.VanishingBracketOverlap

/-! # Translation covariance for the localized q3 remainder bracket -/

@[expose] public section

open MeasureTheory Homogenization Set ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Native ASDExplicitGamma.Main ASDExplicitGamma.Variational
open scoped RealInnerProductSpace

namespace ASDExplicitGamma.Native

noncomputable section

/-- Translate white noise by composing its L² representative with a spatial
translation. Lebesgue measure makes this a linear isometry equivalence. -/
noncomputable def q3WhiteNoiseTranslate (c : Vec 2) :
    WhiteNoise ≃ₗᵢ[ℝ] WhiteNoise := by
  let f : WhiteNoise →ₗᵢ[ℝ] WhiteNoise :=
    Lp.compMeasurePreservingₗᵢ ℝ (fun y : Vec 2 => y + c)
      (measurePreserving_add_right volume c)
  let g : WhiteNoise →ₗ[ℝ] WhiteNoise :=
    Lp.compMeasurePreservingₗ ℝ (fun y : Vec 2 => y + (-c))
      (measurePreserving_add_right volume (-c))
  refine LinearIsometryEquiv.ofLinearIsometry f g ?_ ?_
  · ext u
    have mpPlus := measurePreserving_add_right volume c
    have mpMinus := measurePreserving_add_right volume (-c)
    have hinner := mpPlus.quasiMeasurePreserving.ae_eq_comp
      (Lp.coeFn_compMeasurePreserving u mpMinus)
    change Lp.compMeasurePreserving (fun y : Vec 2 => y + c) mpPlus
      (Lp.compMeasurePreserving (fun y : Vec 2 => y + -c) mpMinus u) =ᵐ[volume] u
    filter_upwards [Lp.coeFn_compMeasurePreserving
      (Lp.compMeasurePreserving (fun y : Vec 2 => y + -c) mpMinus u) mpPlus,
      hinner] with y houter hinner
    simp only [Function.comp_apply] at hinner
    rw [houter]
    change (Lp.compMeasurePreserving (fun y : Vec 2 => y + -c) mpMinus u) (y + c) = u y
    rw [hinner]
    simp
  · ext u
    have mpPlus := measurePreserving_add_right volume c
    have mpMinus := measurePreserving_add_right volume (-c)
    have hinner := mpMinus.quasiMeasurePreserving.ae_eq_comp
      (Lp.coeFn_compMeasurePreserving u mpPlus)
    change Lp.compMeasurePreserving (fun y : Vec 2 => y + -c) mpMinus
      (Lp.compMeasurePreserving (fun y : Vec 2 => y + c) mpPlus u) =ᵐ[volume] u
    filter_upwards [Lp.coeFn_compMeasurePreserving
      (Lp.compMeasurePreserving (fun y : Vec 2 => y + c) mpPlus u) mpMinus,
      hinner] with y houter hinner
    simp only [Function.comp_apply] at hinner
    rw [houter]
    change (Lp.compMeasurePreserving (fun y : Vec 2 => y + c) mpPlus u) (y + -c) = u y
    rw [hinner]
    simp

@[simp] theorem q3WhiteNoiseTranslate_apply (c : Vec 2) (u : WhiteNoise) :
    q3WhiteNoiseTranslate c u =
      Lp.compMeasurePreserving (fun y : Vec 2 => y + c)
        (measurePreserving_add_right volume c) u := by
  simp [q3WhiteNoiseTranslate, Lp.compMeasurePreservingₗᵢ,
    Lp.compMeasurePreservingₗ]

@[simp] theorem q3WhiteNoiseTranslate_symm_apply (c : Vec 2) (u : WhiteNoise) :
    (q3WhiteNoiseTranslate c).symm u =
      Lp.compMeasurePreserving (fun y : Vec 2 => y - c)
        (measurePreserving_add_right volume (-c)) u := by
  simpa only [sub_eq_add_neg] using
    (by simp [q3WhiteNoiseTranslate, Lp.compMeasurePreservingₗᵢ,
      Lp.compMeasurePreservingₗ])

/-- The translated kernel section is the inverse-shift of the original
white-noise section. -/
theorem q3WhiteNoiseTranslate_symm_section (c : Vec 2) (β : ℝ)
    (L : {l : ℝ // 0 < l}) (x : Vec 2) :
    (q3WhiteNoiseTranslate c).symm (q3Section β L h3Zero x) =
      q3Section β L h3Zero (x + c) := by
  rw [q3WhiteNoiseTranslate_symm_apply]
  let mp := measurePreserving_add_right volume (-c)
  have h0 := (q3SectionFunction_memLp β L h3Zero x).coeFn_toLp
  have ht := mp.quasiMeasurePreserving.ae h0
  have hx := (q3SectionFunction_memLp β L h3Zero (x + c)).coeFn_toLp
  change Lp.compMeasurePreserving (fun y : Vec 2 => y + -c) mp
      (q3Section β L h3Zero x) = q3Section β L h3Zero (x + c)
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving
      (q3Section β L h3Zero x) mp, ht, hx] with y hshift hty hy
  change q3Section β L h3Zero (x + c) y =
      q3SectionFunction β L h3Zero (x + c) y at hy
  change q3Section β L h3Zero x (y - c) =
      q3SectionFunction β L h3Zero x (y - c) at hty
  rw [hshift]
  change q3Section β L h3Zero x (y - c) = _
  rw [hty, hy]
  have harg (i : Fin 2) :
      (x i - (y i - c i)) / L.1 = ((x + c) i - y i) / L.1 := by
    simp only [Pi.add_apply]
    ring
  simp only [q3SectionFunction, Pi.add_apply, Pi.sub_apply]
  rw [harg 0, harg 1]
  simp only [Pi.add_apply]

/-- Convolution by the actual q3 kernel commutes with translating white noise
and the observation point by the same vector. -/
theorem q3Convolution_translate (c : Vec 2) (β : ℝ)
    (L : {l : ℝ // 0 < l}) (u : WhiteNoise) (x : Vec 2) :
    q3Convolution β L h3Zero (q3WhiteNoiseTranslate c u) x =
      q3Convolution β L h3Zero u (x + c) := by
  change ⟪q3WhiteNoiseTranslate c u, q3Section β L h3Zero x⟫ =
    ⟪u, q3Section β L h3Zero (x + c)⟫
  calc
    _ = ⟪q3WhiteNoiseTranslate c u,
          q3WhiteNoiseTranslate c
            ((q3WhiteNoiseTranslate c).symm (q3Section β L h3Zero x))⟫ := by
          rw [q3WhiteNoiseTranslate_apply,
            (q3WhiteNoiseTranslate c).apply_symm_apply]
    _ = ⟪u, (q3WhiteNoiseTranslate c).symm
          (q3Section β L h3Zero x)⟫ :=
        (q3WhiteNoiseTranslate c).inner_map_map u
          ((q3WhiteNoiseTranslate c).symm (q3Section β L h3Zero x))
    _ = ⟪u, q3Section β L h3Zero (x + c)⟫ := by
        rw [q3WhiteNoiseTranslate_symm_section]

end

end ASDExplicitGamma.Native
