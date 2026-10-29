module

public import ASDExplicitGamma.Inverse.FullResponseResetSeriesNumerics

/-! Complete double-geometric reset bounds, retaining the abscissa moment. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
noncomputable section

/-- Both complete reset series are bounded with their first abscissa moment;
no finite height/layer scan is substituted for either infinite sum. -/
theorem full_response_reset_moment_bounds (C N : ℕ) (rate c : ℝ)
    (hN : (N:ℝ) ≤ rate*((C+1:ℕ):ℝ)) (hrate : 0 ≤ rate)
    (hc : 0 ≤ c) (hc1 : c < 1) (hq : (3:ℝ)^(-rate) ≤ c) :
    (Summable (fun hk : ℕ × ℕ => (3:ℝ)^(-rate*(localizationResetAbscissa C hk.1 hk.2:ℝ))) ∧
      (∑' hk : ℕ × ℕ, (3:ℝ)^(-rate*(localizationResetAbscissa C hk.1 hk.2:ℝ))) ≤
        (3:ℝ)^(-(N:ℝ))*(1/(1-c))^2) ∧
    (Summable (fun hk : ℕ × ℕ => (localizationResetAbscissa C hk.1 hk.2:ℝ)*
      (3:ℝ)^(-rate*(localizationResetAbscissa C hk.1 hk.2:ℝ))) ∧
      (∑' hk : ℕ × ℕ, (localizationResetAbscissa C hk.1 hk.2:ℝ)*
        (3:ℝ)^(-rate*(localizationResetAbscissa C hk.1 hk.2:ℝ))) ≤
        (3:ℝ)^(-(N:ℝ))*(((C:ℝ)+2)*(1/(1-c))^2+3*c/(1-c)^3)) := by
  let g := fun n : ℕ => c^n
  let gm := fun n : ℕ => (n:ℝ)*c^n
  let A := 1/(1-c)
  let B := c/(1-c)^2
  let t := (3:ℝ)^(-(N:ℝ))
  have hgeom : HasSum g A := by
    simpa only [g,A,one_div] using hasSum_geometric_of_lt_one hc hc1
  have hm : HasSum gm B := by
    simpa only [gm,B] using
      hasSum_coe_mul_geometric_of_norm_lt_one (r := c) (by simpa only [Real.norm_eq_abs,abs_of_nonneg hc] using hc1)
  have hprod := localization_nonnegative_product_hasSum g g
    (fun _ => pow_nonneg hc _) (fun _ => pow_nonneg hc _) hgeom hgeom
  have hprodH := localization_nonnegative_product_hasSum gm g
    (fun n => mul_nonneg (Nat.cast_nonneg n) (pow_nonneg hc n))
    (fun _ => pow_nonneg hc _) hm hgeom
  have hprodK := localization_nonnegative_product_hasSum g gm
    (fun _ => pow_nonneg hc _)
    (fun n => mul_nonneg (Nat.cast_nonneg n) (pow_nonneg hc n)) hgeom hm
  let Z := fun hk : ℕ × ℕ => t*(g hk.1*g hk.2)
  let Z1 := fun hk : ℕ × ℕ => t*(((C:ℝ)+2+(hk.1:ℝ)+2*(hk.2:ℝ))*(g hk.1*g hk.2))
  have hZ : HasSum Z (t*A^2) := by
    convert hprod.mul_left t using 1
    ring
  have hZ1 : HasSum Z1 (t*(((C:ℝ)+2)*A^2+3*c/(1-c)^3)) := by
    have hh := ((hprod.mul_left ((C:ℝ)+2)).add hprodH).add (hprodK.mul_left 2)
    convert hh.mul_left t using 1
    · funext hk
      dsimp only [Z1,gm,g]
      ring
    · dsimp only [A,B]
      field_simp
      ring
  have ht0 : 0 ≤ t := by dsimp only [t]; positivity
  have hterm (hk : ℕ × ℕ) :
      (3:ℝ)^(-rate*(localizationResetAbscissa C hk.1 hk.2:ℝ)) ≤ Z hk :=
    full_response_reset_term_le C N rate c hN hrate hc hq hk
  have hxupper (hk : ℕ × ℕ) : (localizationResetAbscissa C hk.1 hk.2:ℝ) ≤
      (C:ℝ)+2+(hk.1:ℝ)+2*(hk.2:ℝ) := by
    have hh : localizationResetAbscissa C hk.1 hk.2 ≤ C+2+hk.1+2*hk.2 := by
      unfold localizationResetAbscissa localizationProfileDepth
      omega
    exact_mod_cast hh
  have hterm1 (hk : ℕ × ℕ) :
      (localizationResetAbscissa C hk.1 hk.2:ℝ)*
        (3:ℝ)^(-rate*(localizationResetAbscissa C hk.1 hk.2:ℝ)) ≤ Z1 hk := by
    have hh := mul_le_mul (hxupper hk) (hterm hk) (by positivity)
      (show 0 ≤ (C:ℝ)+2+(hk.1:ℝ)+2*(hk.2:ℝ) by positivity)
    convert hh using 1
    dsimp only [Z,Z1]
    ring
  have hs := Summable.of_nonneg_of_le (fun hk : ℕ × ℕ => by positivity) hterm hZ.summable
  have hs1 := Summable.of_nonneg_of_le (fun hk : ℕ × ℕ =>
    mul_nonneg (Nat.cast_nonneg _) (by positivity)) hterm1 hZ1.summable
  refine ⟨⟨hs,?som⟩,⟨hs1,?first⟩⟩
  case som =>
    exact (hs.tsum_le_tsum hterm hZ.summable).trans_eq hZ.tsum_eq
  case first =>
    exact (hs1.tsum_le_tsum hterm1 hZ1.summable).trans_eq hZ1.tsum_eq

end
end ASDExplicitGamma.Inverse
