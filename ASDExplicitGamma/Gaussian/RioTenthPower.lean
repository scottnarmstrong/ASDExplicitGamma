module

public import ASDExplicitGamma.Gaussian.RioCalculus

/-! # The exact second-derivative cancellation for a twentieth moment -/

@[expose] public section
noncomputable section
namespace ASDExplicitGamma.Gaussian

/-- Taking the one-tenth power of a positive twentieth moment has second derivative
at most `38*B`; the favorable squared first-derivative term is retained with its sign. -/
theorem rio_tenth_power_smoothness {f g h : ℝ → ℝ} {B : ℝ}
    (hf : ∀ x, HasDerivAt f (g x) x) (hg : ∀ x, HasDerivAt g (h x) x)
    (hpos : ∀ x, 0 < f x) (hHolder : ∀ x, h x ≤ 380*(f x)^((9:ℝ)/10)*B)
    (h0 : g 0 = 0) : (f 1)^((1:ℝ)/10) ≤ (f 0)^((1:ℝ)/10)+19*B := by
  let F := fun x => (f x)^((1:ℝ)/10)
  let G := fun x => (1/10:ℝ)*(f x)^(-(9:ℝ)/10)*g x
  let H := fun x => (1/10:ℝ)*(-(9:ℝ)/10)*(f x)^(-(19:ℝ)/10)*(g x)^2+
    (1/10:ℝ)*(f x)^(-(9:ℝ)/10)*h x
  have hF (x : ℝ) : HasDerivAt F (G x) x := by
    have hd := (hf x).rpow_const (p := (1:ℝ)/10) (Or.inl (hpos x).ne')
    norm_num only at hd
    dsimp only [G]
    norm_num only
    convert hd using 1
    ring
  have hG (x : ℝ) : HasDerivAt G (H x) x := by
    have hd := (((hf x).rpow_const (p := -(9:ℝ)/10) (Or.inl (hpos x).ne')).const_mul (1/10:ℝ)).mul (hg x)
    norm_num only at hd
    convert hd using 1
    · funext y
      dsimp only [G,Pi.mul_apply]
      norm_num only
    · dsimp only [H]
      norm_num only
      ring
  have hH (x : ℝ) : H x ≤ 38*B := by
    have hcancel : (f x)^(-(9:ℝ)/10)*(f x)^((9:ℝ)/10) = 1 := by
      rw [← Real.rpow_add (hpos x)]
      norm_num
    have hneg : (1/10:ℝ)*(-(9:ℝ)/10)*(f x)^(-(19:ℝ)/10)*(g x)^2 ≤ 0 := by
      apply mul_nonpos_of_nonpos_of_nonneg
      · apply mul_nonpos_of_nonpos_of_nonneg
        · norm_num
        · exact Real.rpow_nonneg (hpos x).le _
      · exact sq_nonneg _
    have hm := mul_le_mul_of_nonneg_left (hHolder x)
      (mul_nonneg (by norm_num : (0:ℝ) ≤ 1/10) (Real.rpow_nonneg (hpos x).le (-(9:ℝ)/10)))
    have heq : ((1/10:ℝ)*(f x)^(-(9:ℝ)/10))*(380*(f x)^((9:ℝ)/10)*B) = 38*B := by
      calc
        _ = 38*((f x)^(-(9:ℝ)/10)*(f x)^((9:ℝ)/10))*B := by ring
        _ = _ := by rw [hcancel]; ring
    rw [heq] at hm
    dsimp only [H]
    linarith only [hneg,hm]
  have hG0 : G 0 = 0 := by dsimp [G]; rw [h0]; ring
  have h := rio_quadratic_bound hF hG hH hG0
  dsimp only [F] at h
  convert h using 1
  ring

end ASDExplicitGamma.Gaussian
