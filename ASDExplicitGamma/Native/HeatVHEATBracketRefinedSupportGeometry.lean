module

public import ASDExplicitGamma.Native.HeatVHEATBracketRefinedGeometry
import ASDExplicitGamma.Native.VanishingBracketGridTranslation

/-! The physical depth-ten child supports have exactly the overlap count of
the normalized q3 grid after affine normalization of the parent cube. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open Homogenization ASDExplicitGamma.Triadic ASDExplicitGamma.Gaussian

/-- The physical q3 enlargement of one depth-ten descendant of `Q`. -/
noncomputable def nativeHeatQ3RefinedGridExpandedSupport
    (Q : TriadicCube 2) (L : {l : ℝ // 0 < l})
    (ij : Fin (3 ^ 10) × Fin (3 ^ 10)) : Set (Vec 2) :=
  let C := nativeHeatQ3RefinedChildCube Q ij
  q3ExpandedRectangle (cubeCorner C 0) (cubeCorner C 0 + cubeScaleFactor C)
    (cubeCorner C 1) (cubeCorner C 1 + cubeScaleFactor C) L

/-- Membership in the physical enlarged child is equivalent to membership
in the normalized grid enlargement, with the point sent to parent coordinates. -/
theorem nativeHeatQ3RefinedGridExpandedSupport_mem_iff
    (Q : TriadicCube 2) (n : ℕ) (L : {l : ℝ // 0 < l})
    (hL : L.1 / cubeScaleFactor Q = (q3GridKernelScale 10 n).1)
    (ij : Fin (3 ^ 10) × Fin (3 ^ 10)) (x : Vec 2) :
    x ∈ nativeHeatQ3RefinedGridExpandedSupport Q L ij ↔
      (fun a => (x a - cubeCorner Q a) / cubeScaleFactor Q) ∈
        q3GridExpandedSupport 10 n ij := by
  let C := nativeHeatQ3RefinedChildCube Q ij
  let s := cubeScaleFactor Q
  have hs : 0 < s := by
    dsimp [s, cubeScaleFactor]
    positivity
  have hrad : diagMeshRadius Q 10 = s / (3 : ℝ) ^ 10 := by
    simp [diagMeshRadius, s]
  have hcorner (a : Fin 2) :
      cubeCorner C a = cubeCorner Q a +
        (nativeHeatQ3RefinedChildDigits ij a).val * (s / (3 : ℝ) ^ 10) := by
    dsimp [C, nativeHeatQ3RefinedChildCube]
    rw [Triadic.diagMeshCell_corner, hrad]
  have hside : cubeScaleFactor C = s / (3 : ℝ) ^ 10 := by
    dsimp [C, nativeHeatQ3RefinedChildCube]
    rw [Triadic.diagMeshCell_side, hrad]
  have hdigit0 : nativeHeatQ3RefinedChildDigits ij 0 = ij.1 := by
    simp [nativeHeatQ3RefinedChildDigits]
  have hdigit1 : nativeHeatQ3RefinedChildDigits ij 1 = ij.2 := by
    simp [nativeHeatQ3RefinedChildDigits]
  have hq : (q3GridKernelScale 10 n).1 =
      (3 : ℝ) ^ n / (3 : ℝ) ^ 10 := by
    simp [q3GridKernelScale]
  have hratio : L.1 = s * ((3 : ℝ) ^ n / (3 : ℝ) ^ 10) := by
    calc
      L.1 = s * (L.1 / s) := by field_simp [hs.ne']
      _ = s * ((3 : ℝ) ^ n / (3 : ℝ) ^ 10) := by rw [hL, hq]
  have hcorner0 : cubeCorner C 0 = cubeCorner Q 0 +
      (ij.1.val : ℝ) * (s / (3 : ℝ) ^ 10) := by
    simpa only [hdigit0] using hcorner 0
  have hcorner1 : cubeCorner C 1 = cubeCorner Q 1 +
      (ij.2.val : ℝ) * (s / (3 : ℝ) ^ 10) := by
    simpa only [hdigit1] using hcorner 1
  have haxis (a : Fin 2) (i : Fin (3 ^ 10))
      (hc : cubeCorner C a = cubeCorner Q a +
        (i.val : ℝ) * (s / (3 : ℝ) ^ 10)) :
      (x a ∈ Set.Icc (cubeCorner C a - L.1 / 2)
        (cubeCorner C a + cubeScaleFactor C + L.1 / 2)) ↔
      q3GridAxisActive 10 n ((x a - cubeCorner Q a) / s) i := by
    rw [Set.mem_Icc]
    change (_ ∧ _) ↔
      ((i.val : ℝ) - (3 : ℝ) ^ n / 2 ≤
        ((x a - cubeCorner Q a) / s) * (3 : ℝ) ^ 10) ∧
      (((x a - cubeCorner Q a) / s) * (3 : ℝ) ^ 10 ≤
        (i.val : ℝ) + 1 + (3 : ℝ) ^ n / 2)
    constructor
    · rintro ⟨hlo, hhi⟩
      constructor
      · have hmul := mul_le_mul_of_nonneg_right hlo
          (show 0 ≤ (3 : ℝ) ^ 10 by positivity)
        rw [hc, hratio] at hmul
        have hgoal : ((i.val : ℝ) - (3 : ℝ) ^ n / 2) * s ≤
            (x a - cubeCorner Q a) * (3 : ℝ) ^ 10 := by
          nlinarith [hmul]
        have hdiv : ((i.val : ℝ) - (3 : ℝ) ^ n / 2) ≤
            ((x a - cubeCorner Q a) * (3 : ℝ) ^ 10) / s :=
          (le_div_iff₀ hs).2 hgoal
        simpa [div_mul_eq_mul_div] using hdiv
      · have hmul := mul_le_mul_of_nonneg_right hhi
          (show 0 ≤ (3 : ℝ) ^ 10 by positivity)
        rw [hc, hside, hratio] at hmul
        have hgoal : (x a - cubeCorner Q a) * (3 : ℝ) ^ 10 ≤
            ((i.val : ℝ) + 1 + (3 : ℝ) ^ n / 2) * s := by
          nlinarith [hmul]
        have hdiv : ((x a - cubeCorner Q a) * (3 : ℝ) ^ 10) / s ≤
            (i.val : ℝ) + 1 + (3 : ℝ) ^ n / 2 :=
          (div_le_iff₀ hs).2 hgoal
        simpa [div_mul_eq_mul_div] using hdiv
    · rintro ⟨hlo, hhi⟩
      rw [div_mul_eq_mul_div] at hlo hhi
      constructor
      · have hgoal : ((i.val : ℝ) - (3 : ℝ) ^ n / 2) * s ≤
          (x a - cubeCorner Q a) * (3 : ℝ) ^ 10 := by
          have hh := (le_div_iff₀ hs).1 hlo
          exact hh
        have hlow : cubeCorner C a - L.1 / 2 ≤ x a := by
          rw [hc, hratio]
          field_simp
          nlinarith [hgoal]
        exact hlow
      · have hgoal : (x a - cubeCorner Q a) * (3 : ℝ) ^ 10 ≤
          ((i.val : ℝ) + 1 + (3 : ℝ) ^ n / 2) * s := by
          have hh := (div_le_iff₀ hs).1 hhi
          exact hh
        have hhigh : x a ≤ cubeCorner C a + cubeScaleFactor C + L.1 / 2 := by
          rw [hc, hside, hratio]
          field_simp
          nlinarith [hgoal]
        exact hhigh
  rw [q3GridExpandedSupport_mem_iff]
  constructor
  · intro hx
    have hx' :
        x 0 ∈ Set.Icc (cubeCorner C 0 - L.1 / 2)
          (cubeCorner C 0 + cubeScaleFactor C + L.1 / 2) ∧
        x 1 ∈ Set.Icc (cubeCorner C 1 - L.1 / 2)
          (cubeCorner C 1 + cubeScaleFactor C + L.1 / 2) := by
      simpa [nativeHeatQ3RefinedGridExpandedSupport, C,
        q3ExpandedRectangle, Gaussian.closedRectangle] using hx
    exact ⟨(haxis 0 ij.1 hcorner0).1 hx'.1,
      (haxis 1 ij.2 hcorner1).1 hx'.2⟩
  · intro hx
    have h0 := (haxis 0 ij.1 hcorner0).2 hx.1
    have h1 := (haxis 1 ij.2 hcorner1).2 hx.2
    have hmem :
        x 0 ∈ Set.Icc (cubeCorner C 0 - L.1 / 2)
          (cubeCorner C 0 + cubeScaleFactor C + L.1 / 2) ∧
        x 1 ∈ Set.Icc (cubeCorner C 1 - L.1 / 2)
          (cubeCorner C 1 + cubeScaleFactor C + L.1 / 2) := ⟨h0, h1⟩
    simpa [nativeHeatQ3RefinedGridExpandedSupport, C,
      q3ExpandedRectangle, Gaussian.closedRectangle] using hmem

/-- The actual physical enlarged supports, indexed in Cartesian parent
coordinates. The classical filter stays opaque to callers. -/
noncomputable def nativeHeatQ3RefinedGridActiveFinset
    (Q : TriadicCube 2) (L : {l : ℝ // 0 < l}) (x : Vec 2) :
    Finset (Fin (3 ^ 10) × Fin (3 ^ 10)) := by
  classical
  exact Finset.univ.filter fun ij =>
    x ∈ nativeHeatQ3RefinedGridExpandedSupport Q L ij

/-- The normalized multiplicity of physical supports on the actual refined
children is the source's exact depth-ten q3 overlap factor. -/
theorem nativeHeatQ3RefinedGridSupportOverlap_card_ratio_le
    (Q : TriadicCube 2) (n : ℕ) (hn : 1 ≤ n) (hns : n ≤ 10)
    (L : {l : ℝ // 0 < l})
    (hL : L.1 / cubeScaleFactor Q = (q3GridKernelScale 10 n).1)
    (x : Vec 2) :
    ((nativeHeatQ3RefinedGridActiveFinset Q L x).card : ℝ) /
        ((Finset.univ : Finset (Fin (3 ^ 10) × Fin (3 ^ 10))).card : ℝ) ≤
      q3GridOverlapFactor 10 n := by
  classical
  have hfilter :
      nativeHeatQ3RefinedGridActiveFinset Q L x =
      q3GridActiveFinset 10 n
        (fun a => (x a - cubeCorner Q a) / cubeScaleFactor Q) := by
    ext ij
    simp only [nativeHeatQ3RefinedGridActiveFinset,
      q3GridActiveFinset, Finset.mem_filter, Finset.mem_univ, true_and]
    exact nativeHeatQ3RefinedGridExpandedSupport_mem_iff Q n L hL ij x
  rw [hfilter]
  have hden :
      ((Finset.univ : Finset (Fin (3 ^ 10) × Fin (3 ^ 10))).card : ℝ) =
        ((3 : ℝ) ^ 10) ^ 2 := by
    simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
      Nat.cast_mul, Nat.cast_pow]
    ring
  rw [hden]
  exact q3GridActiveFinset_card_ratio_le 10 n hn hns _

end ASDExplicitGamma.Native

end
