module

public import ASDExplicitGamma.Cold.NativeLocalTrace

/-! # Exact four-colour geometry of planar triadic cells -/

@[expose] public section
noncomputable section
open Homogenization
namespace ASDExplicitGamma.Cold

/-- Literal parity colouring of the two integer cell coordinates, encoded by four colours. -/
def coldCubeColor (Q : TriadicCube 2) : Fin 4 :=
  ⟨(Q.index 0%2).toNat+2*(Q.index 1%2).toNat,by
    have h0 := Int.emod_nonneg (Q.index 0) (by norm_num : (2:ℤ) ≠ 0)
    have h1 := Int.emod_nonneg (Q.index 1) (by norm_num : (2:ℤ) ≠ 0)
    have h0' := Int.emod_lt_of_pos (Q.index 0) (by norm_num : (0:ℤ) < 2)
    have h1' := Int.emod_lt_of_pos (Q.index 1) (by norm_num : (0:ℤ) < 2)
    omega⟩

/-- Equal colours imply coordinatewise integer parity equality. -/
theorem coldCubeColor_parity {Q R : TriadicCube 2} (h : coldCubeColor Q = coldCubeColor R) (i : Fin 2) :
    Q.index i%2 = R.index i%2 := by
  have he := congrArg Fin.val h
  change (Q.index 0%2).toNat+2*(Q.index 1%2).toNat =
    (R.index 0%2).toNat+2*(R.index 1%2).toNat at he
  have hQ0 := Int.emod_nonneg (Q.index 0) (by norm_num : (2:ℤ) ≠ 0)
  have hQ1 := Int.emod_nonneg (Q.index 1) (by norm_num : (2:ℤ) ≠ 0)
  have hR0 := Int.emod_nonneg (R.index 0) (by norm_num : (2:ℤ) ≠ 0)
  have hR1 := Int.emod_nonneg (R.index 1) (by norm_num : (2:ℤ) ≠ 0)
  have hQ0' := Int.emod_lt_of_pos (Q.index 0) (by norm_num : (0:ℤ) < 2)
  have hQ1' := Int.emod_lt_of_pos (Q.index 1) (by norm_num : (0:ℤ) < 2)
  have hR0' := Int.emod_lt_of_pos (R.index 0) (by norm_num : (0:ℤ) < 2)
  have hR1' := Int.emod_lt_of_pos (R.index 1) (by norm_num : (0:ℤ) < 2)
  fin_cases i
  · change Q.index 0%2 = R.index 0%2
    omega
  · change Q.index 1%2 = R.index 1%2
    omega

/-- Distinct cells at the same scale and colour are separated by a full cell side in some coordinate. -/
theorem cold_same_color_separation {Q R : TriadicCube 2} (hscale : Q.scale = R.scale)
    (hneq : Q ≠ R) (hcolor : coldCubeColor Q = coldCubeColor R)
    {x y : Vec 2} (hx : x ∈ cubeSet Q) (hy : y ∈ cubeSet R) :
    ∃ k : Fin 2, (3:ℝ)^Q.scale ≤ |(x-y) k| := by
  have hidx : ∃ k : Fin 2, Q.index k ≠ R.index k := by
    by_contra hn
    push Not at hn
    have he : Q.index = R.index := funext hn
    apply hneq
    cases Q
    cases R
    simp_all
  obtain ⟨i,hi⟩ := hidx
  have hp := coldCubeColor_parity hcolor i
  have hd : Q.index i+2 ≤ R.index i ∨ R.index i+2 ≤ Q.index i := by omega
  have hs : (0:ℝ) < (3:ℝ)^Q.scale := zpow_pos (by norm_num) _
  have hxlo := (hx i).1
  have hxhi := (hx i).2.le
  have hylo := (hy i).1
  have hyhi := (hy i).2.le
  simp only [cubeScaleFactor,← hscale] at hxlo hxhi hylo hyhi
  refine ⟨i,?_⟩
  rcases hd with hd | hd
  · have hreal : (Q.index i:ℝ)+2 ≤ (R.index i:ℝ) := by exact_mod_cast hd
    have hm := mul_le_mul_of_nonneg_right hreal hs.le
    have hgap : (3:ℝ)^Q.scale ≤ y i-x i := by nlinarith only [hm,hxhi,hylo]
    exact hgap.trans (by simpa only [Pi.sub_apply,neg_sub] using neg_le_abs (x i-y i))
  · have hreal : (R.index i:ℝ)+2 ≤ (Q.index i:ℝ) := by exact_mod_cast hd
    have hm := mul_le_mul_of_nonneg_right hreal hs.le
    have hgap : (3:ℝ)^Q.scale ≤ x i-y i := by nlinarith only [hm,hyhi,hxlo]
    exact hgap.trans (le_abs_self _)

end ASDExplicitGamma.Cold
