module

public import ASDExplicitGamma.Inverse.StoppedHeightExponent
public import ASDExplicitGamma.Numerics.Scalar.Basic

/-! Exact source finite-root count and complete infinite stopped-height tail payments. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
noncomputable section

/-- The literal root-starting count is paid before any infinite height union. -/
theorem separation_count_exp (h : ℕ) :
    10*(3:ℝ)^(2*h) ≤ Real.exp (3+(11/5:ℝ)*(h:ℝ)) := by
  have ht := Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ) ≤ 3) 4
  have h10 : (10:ℝ) ≤ Real.exp 3 := by
    norm_num [Finset.sum_range_succ,Nat.factorial] at ht
    linarith only [ht]
  have hp : (3:ℝ)^(2*h) ≤ Real.exp ((11/5:ℝ)*(h:ℝ)) := by
    calc
      _ = Real.exp (((2*h:ℕ):ℝ)*Real.log 3) := by rw [Real.exp_nat_mul,Real.exp_log (by norm_num : (0:ℝ) < 3)]
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        have hh := mul_le_mul_of_nonneg_left ASDExplicitGamma.Numerics.Scalar.log_three_small.2.le
          (Nat.cast_nonneg (2*h) : (0:ℝ) ≤ ((2*h:ℕ):ℝ))
        push_cast at hh ⊢
        linarith only [hh]
  calc
    _ ≤ Real.exp 3*Real.exp ((11/5:ℝ)*(h:ℝ)) := mul_le_mul h10 hp (by positivity) (Real.exp_pos _).le
    _ = _ := (Real.exp_add _ _).symm

/-- The actual finite-root separation bound of source (4.1) is bounded by
exp(-Y_h/12) at every h>=333, with the full 3^(2h) population retained. -/
theorem separation_probability_payment (h : ℕ) (hh : 333 ≤ h) :
    10*(3:ℝ)^(2*h)*Real.exp (-heightExponent h/6) ≤ Real.exp (-heightExponent h/12) := by
  calc
    _ ≤ Real.exp (3+(11/5:ℝ)*(h:ℝ))*Real.exp (-heightExponent h/6) :=
      mul_le_mul_of_nonneg_right (separation_count_exp h) (Real.exp_pos _).le
    _ = Real.exp (3+(11/5:ℝ)*(h:ℝ)-heightExponent h/6) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith only [height_linear_payment h hh])

/-- The geometric prefactor is absorbed at the fixed planar entrance. -/
theorem height_geometric_prefactor (h : ℕ) (hh : 333 ≤ h) :
    (1000/999:ℝ)*Real.exp (-heightExponent h/12) ≤ Real.exp (-heightExponent h/32) := by
  have he := height_exponent_lower h hh
  have hbig : (10000:ℝ) ≤ heightExponent h := by norm_num at he; linarith only [he]
  have hb := Real.add_one_le_exp ((5/96:ℝ)*heightExponent h)
  have hc : (1000/999:ℝ) ≤ Real.exp ((5/96:ℝ)*heightExponent h) := by linarith only [hb,hbig]
  calc
    _ ≤ Real.exp ((5/96:ℝ)*heightExponent h)*Real.exp (-heightExponent h/12) :=
      mul_le_mul_of_nonneg_right hc (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

/-- The complete infinite future-height probability series has exactly the
source one-thirty-second exponent, for both entrances 333 and 377. -/
theorem stopped_height_probability_series (h : ℕ) (hh : 333 ≤ h) :
    (∑' n : ℕ, Real.exp (-heightExponent (h+n)/12)) ≤ Real.exp (-heightExponent h/32) := by
  have he : (fun n : ℕ => Real.exp (-heightExponent (h+n)/12)) =
      (fun n => Real.exp (-(heightExponent h/12)*((3:ℝ)^(1/4:ℝ))^n)) := by
    funext n
    rw [height_exponent_add]
    congr 1
    ring
  rw [he]
  have hl := height_exponent_lower h hh
  have hb : (10000:ℝ) ≤ heightExponent h/12 := by norm_num at hl; linarith only [hl]
  have hs := ASDExplicitGamma.Numerics.Inverse.inv_selected_probability_tail _ _ hb
    ASDExplicitGamma.Numerics.Inverse.inv_quarter_growth.le
  have hp : (1000/999:ℝ)*Real.exp (-(heightExponent h/12)) ≤ Real.exp (-heightExponent h/32) := by
    simpa only [neg_div] using! height_geometric_prefactor h hh
  exact hs.trans hp

end
end ASDExplicitGamma.Inverse
