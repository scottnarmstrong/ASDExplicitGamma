module
public import ASDExplicitGamma.Model.BflatModeCovariance
public import ASDExplicitGamma.Numerics.Model.Q3Modes
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
@[expose] public section

open MeasureTheory Set

namespace ASDExplicitGamma.Model

private theorem triangle_swap (H : ℝ → ℝ → ℝ) (hH : Continuous (Function.uncurry H)) :
    (∫ x in (0:ℝ)..1, ∫ r in 0..(1-x), H x r) =
      ∫ r in (0:ℝ)..1, ∫ x in 0..(1-r), H x r := by
  classical
  let T : Set (ℝ × ℝ) := {p | p.2 ≤ 1-p.1}
  let F : ℝ → ℝ → ℝ := fun x r => T.indicator (fun p => H p.1 p.2) (x,r)
  have hHintcc : IntegrableOn (Function.uncurry H) (Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1) volume :=
    hH.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have hHint : IntegrableOn (Function.uncurry H) (Ioc (0:ℝ) 1 ×ˢ Ioc (0:ℝ) 1) volume :=
    hHintcc.mono_set (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
  have hT : MeasurableSet T := by
    apply measurableSet_le measurable_snd
    exact measurable_const.sub measurable_fst
  have hFint : IntegrableOn (Function.uncurry F) (Set.uIoc (0:ℝ) 1 ×ˢ Set.uIoc (0:ℝ) 1) volume := by
    change IntegrableOn (T.indicator (Function.uncurry H)) _ _
    simpa only [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] using hHint.indicator hT
  have hinner (x : ℝ) (hx : x ∈ Icc (0:ℝ) 1) :
      (∫ r in (0:ℝ)..1, F x r) = ∫ r in (0:ℝ)..(1-x), H x r := by
    have hbound : 1-x ∈ Icc (0:ℝ) 1 := by constructor <;> linarith [hx.1, hx.2]
    calc
      (∫ r in (0:ℝ)..1, F x r) =
          ∫ r in (0:ℝ)..1, {r | r ≤ 1-x}.indicator (fun r => H x r) r := by
        apply intervalIntegral.integral_congr
        intro r hr
        change (if r ≤ 1-x then H x r else 0) = _
        rfl
      _ = _ := intervalIntegral.integral_indicator hbound
  have houter (r : ℝ) (hr : r ∈ Icc (0:ℝ) 1) :
      (∫ x in (0:ℝ)..1, F x r) = ∫ x in (0:ℝ)..(1-r), H x r := by
    have hbound : 1-r ∈ Icc (0:ℝ) 1 := by constructor <;> linarith [hr.1, hr.2]
    calc
      _ = ∫ x in (0:ℝ)..1, {x | x ≤ 1-r}.indicator (fun x => H x r) x := by
        apply intervalIntegral.integral_congr
        intro x hx
        have hcond : r ≤ 1-x ↔ x ≤ 1-r := by constructor <;> intro h <;> nlinarith
        change (if r ≤ 1-x then H x r else 0) = (if x ≤ 1-r then H x r else 0)
        simp only [hcond]
      _ = _ := intervalIntegral.integral_indicator hbound
  calc
    _ = ∫ x in (0:ℝ)..1, ∫ r in (0:ℝ)..1, F x r := by
      apply intervalIntegral.integral_congr
      intro x hx
      exact (hinner x (by simpa using hx)).symm
    _ = ∫ r in (0:ℝ)..1, ∫ x in (0:ℝ)..1, F x r :=
      intervalIntegral_intervalIntegral_swap hFint
    _ = ∫ r in (0:ℝ)..1, ∫ x in (0:ℝ)..(1-r), H x r := by
      apply intervalIntegral.integral_congr
      intro r hr
      exact houter r (by simpa using hr)

private theorem lower_eq_upper (H : ℝ → ℝ → ℝ)
    (hH : Continuous (Function.uncurry H))
    (hsym : ∀ x y, H x y = H y x) :
    (∫ x in (0:ℝ)..1, ∫ y in 0..x, H x y) =
      ∫ x in (0:ℝ)..1, ∫ y in x..1, H x y := by
  classical
  let T : Set (ℝ × ℝ) := {p | p.2 ≤ p.1}
  let F : ℝ → ℝ → ℝ := fun x y => T.indicator (fun p => H p.1 p.2) (x,y)
  have hHintcc : IntegrableOn (Function.uncurry H) (Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1) volume :=
    hH.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have hHint : IntegrableOn (Function.uncurry H) (Ioc (0:ℝ) 1 ×ˢ Ioc (0:ℝ) 1) volume :=
    hHintcc.mono_set (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
  have hT : MeasurableSet T := by
    apply measurableSet_le measurable_snd
    exact measurable_fst
  have hFint : IntegrableOn (Function.uncurry F) (Set.uIoc (0:ℝ) 1 ×ˢ Set.uIoc (0:ℝ) 1) volume := by
    change IntegrableOn (T.indicator (Function.uncurry H)) _ _
    simpa only [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] using hHint.indicator hT
  have hinner (x : ℝ) (hx : x ∈ Icc (0:ℝ) 1) :
      (∫ y in (0:ℝ)..1, F x y) = ∫ y in (0:ℝ)..x, H x y := by
    have hbound : x ∈ Icc (0:ℝ) 1 := hx
    calc
      (∫ y in (0:ℝ)..1, F x y) =
          ∫ y in (0:ℝ)..1, {y | y ≤ x}.indicator (fun y => H x y) y := by
        apply intervalIntegral.integral_congr
        intro y hy
        change (if y ≤ x then H x y else 0) = _
        rfl
      _ = _ := intervalIntegral.integral_indicator hbound
  have houter (y : ℝ) (hy : y ∈ Icc (0:ℝ) 1) :
      (∫ x in (0:ℝ)..1, F x y) = ∫ x in y..1, H x y := by
    have hbound : 1-y ∈ Icc (0:ℝ) 1 := by constructor <;> linarith [hy.1, hy.2]
    let K : ℝ → ℝ := fun z => {z | z ≤ 1-y}.indicator (fun z => H (1-z) y) z
    calc
      (∫ x in (0:ℝ)..1, F x y) = ∫ x in (0:ℝ)..1, K (1-x) := by
        apply intervalIntegral.integral_congr
        intro x hx
        change (if y ≤ x then H x y else 0) =
          (if 1-x ≤ 1-y then H (1-(1-x)) y else 0)
        have hcond : y ≤ x ↔ 1-x ≤ 1-y := by constructor <;> intro h <;> linarith
        simp only [hcond, sub_sub_cancel]
      _ = ∫ z in (0:ℝ)..1, K z := by
        simpa only [sub_self, sub_zero] using
          (intervalIntegral.integral_comp_sub_left (a := (0:ℝ)) (b := 1) K (1 : ℝ))
      _ = ∫ z in (0:ℝ)..(1-y), H (1-z) y := by
        dsimp [K]
        exact intervalIntegral.integral_indicator hbound
      _ = ∫ x in y..1, H x y := by
        simpa only [sub_sub_cancel, sub_zero] using
          (intervalIntegral.integral_comp_sub_left (a := (0:ℝ)) (b := 1-y) (fun x => H x y) (1 : ℝ))
  calc
    _ = ∫ x in (0:ℝ)..1, ∫ y in (0:ℝ)..1, F x y := by
      apply intervalIntegral.integral_congr
      intro x hx
      exact (hinner x (by simpa using hx)).symm
    _ = ∫ y in (0:ℝ)..1, ∫ x in (0:ℝ)..1, F x y :=
      intervalIntegral_intervalIntegral_swap hFint
    _ = ∫ y in (0:ℝ)..1, ∫ x in y..1, H x y := by
      apply intervalIntegral.integral_congr
      intro y hy
      exact houter y (by simpa using hy)
    _ = ∫ y in (0:ℝ)..1, ∫ x in y..1, H y x := by
      apply intervalIntegral.integral_congr
      intro y hy
      apply intervalIntegral.integral_congr
      intro x hx
      exact hsym x y
    _ = ∫ x in (0:ℝ)..1, ∫ y in x..1, H x y := by
      rfl

private theorem square_eq_twice_triangle (H : ℝ → ℝ → ℝ)
    (hH : Continuous (Function.uncurry H))
    (hsym : ∀ x y, H x y = H y x) :
    (∫ x in (0:ℝ)..1, ∫ y in (0:ℝ)..1, H x y) =
      2 * (∫ x in (0:ℝ)..1, ∫ y in x..1, H x y) := by
  let L : ℝ → ℝ := fun x => ∫ y in (0:ℝ)..x, H x y
  let U : ℝ → ℝ := fun x => ∫ y in x..1, H x y
  have hLcont : ContinuousOn L (Icc (0:ℝ) 1) := by
    let G : ℝ → ℝ := fun x => ∫ u in Icc (0:ℝ) 1, H x (x*u)
    have hG : Continuous G := by
      apply continuous_parametric_integral_of_continuous ?_ isCompact_Icc
      exact hH.comp (continuous_fst.prodMk (continuous_fst.mul continuous_snd))
    have heq (x : ℝ) (_hx : x ∈ Icc (0:ℝ) 1) : L x = x * G x := by
      dsimp [L, G]
      have hconv : (∫ u in (0:ℝ)..1, H x (x*u)) =
          ∫ u in Icc (0:ℝ) 1, H x (x*u) := by
        rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
          ← integral_Icc_eq_integral_Ioc]
      have hsmul := intervalIntegral.smul_integral_comp_mul_left
        (a := (0:ℝ)) (b := 1) (fun y => H x y) x
      have hsmul' : (∫ y in (0:ℝ)..x, H x y) =
          x * (∫ u in (0:ℝ)..1, H x (x*u)) := by
        convert hsmul.symm using 1 <;> simp
      calc
        (∫ y in (0:ℝ)..x, H x y) =
            x * (∫ u in (0:ℝ)..1, H x (x*u)) := hsmul'
        _ = x * G x := by rw [hconv]
    exact (continuous_id.mul hG).continuousOn.congr fun x hx => heq x hx
  have hUcont : ContinuousOn U (Icc (0:ℝ) 1) := by
    let G : ℝ → ℝ := fun x => ∫ u in Icc (0:ℝ) 1, H x ((1-x)*u+x)
    have hG : Continuous G := by
      apply continuous_parametric_integral_of_continuous ?_ isCompact_Icc
      exact hH.comp (continuous_fst.prodMk
        ((continuous_const.sub continuous_fst).mul continuous_snd |>.add continuous_fst))
    have heq (x : ℝ) (_hx : x ∈ Icc (0:ℝ) 1) : U x = (1-x) * G x := by
      dsimp [U, G]
      have hconv : (∫ u in (0:ℝ)..1, H x ((1-x)*u+x)) =
          ∫ u in Icc (0:ℝ) 1, H x ((1-x)*u+x) := by
        rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
          ← integral_Icc_eq_integral_Ioc]
      have hsmul := intervalIntegral.smul_integral_comp_mul_add
        (a := (0:ℝ)) (b := 1) (fun y => H x y) (1-x) x
      have hsmul' : (∫ y in x..1, H x y) =
          (1-x) * (∫ u in (0:ℝ)..1, H x ((1-x)*u+x)) := by
        convert hsmul.symm using 1 <;> simp
      calc
        (∫ y in x..1, H x y) =
            (1-x) * (∫ u in (0:ℝ)..1, H x ((1-x)*u+x)) := hsmul'
        _ = (1-x) * G x := by rw [hconv]
    exact ((continuous_const.sub continuous_id).mul hG).continuousOn.congr
      fun x hx => heq x hx
  have hLint : IntervalIntegrable L volume 0 1 :=
    hLcont.intervalIntegrable_of_Icc (by norm_num)
  have hUint : IntervalIntegrable U volume 0 1 :=
    hUcont.intervalIntegrable_of_Icc (by norm_num)
  have hsplit (x : ℝ) (hx : x ∈ Icc (0:ℝ) 1) :
      (∫ y in (0:ℝ)..1, H x y) = L x + U x := by
    dsimp [L,U]
    exact (intervalIntegral.integral_add_adjacent_intervals
      ((hH.comp (continuous_const.prodMk continuous_id)).intervalIntegrable 0 x)
      ((hH.comp (continuous_const.prodMk continuous_id)).intervalIntegrable x 1)).symm
  calc
    _ = ∫ x in (0:ℝ)..1, (L x + U x) := by
      apply intervalIntegral.integral_congr
      intro x hx
      exact hsplit x (by simpa using hx)
    _ = (∫ x in (0:ℝ)..1, L x) + ∫ x in (0:ℝ)..1, U x :=
      intervalIntegral.integral_add hLint hUint
    _ = 2 * (∫ x in (0:ℝ)..1, U x) := by
      rw [lower_eq_upper H hH hsym]
      ring

private theorem triangle_shift_swap (H : ℝ → ℝ → ℝ)
    (hH : Continuous (Function.uncurry H)) :
    (∫ x in (0:ℝ)..1, ∫ y in x..1, H x y) =
      ∫ r in (0:ℝ)..1, ∫ x in (0:ℝ)..(1-r), H x (x+r) := by
  let G : ℝ → ℝ → ℝ := fun x r => H x (x+r)
  have hG : Continuous (Function.uncurry G) := by
    exact hH.comp (continuous_fst.prodMk (continuous_fst.add continuous_snd))
  calc
    _ = ∫ x in (0:ℝ)..1, ∫ r in (0:ℝ)..(1-x), G x r := by
      apply intervalIntegral.integral_congr
      intro x hx
      dsimp [G]
      calc
        (∫ y in x..1, H x y) =
            ∫ r in (0:ℝ)..(1-x), H x (r+x) := by
          simpa only [zero_add, sub_add_cancel] using
            (intervalIntegral.integral_comp_add_right (a := (0:ℝ)) (b := 1-x)
              (f := fun y => H x y) x).symm
        _ = ∫ r in (0:ℝ)..(1-x), H x (x+r) := by
          apply intervalIntegral.integral_congr
          intro r hr
          simp only [add_comm]
    _ = ∫ r in (0:ℝ)..1, ∫ x in (0:ℝ)..(1-r), G x r :=
      triangle_swap G hG
    _ = ∫ r in (0:ℝ)..1, ∫ x in (0:ℝ)..(1-r), H x (x+r) := rfl

private theorem interval_eq_Icc {a b : ℝ} (hab : a ≤ b) (f : ℝ → ℝ) :
    (∫ x in a..b, f x) = ∫ x in Icc a b, f x := by
  rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]

private theorem centered_square_shift (F : ℝ → ℝ → ℝ) :
    (∫ x in Icc (-1/2:ℝ) (1/2), ∫ y in Icc (-1/2:ℝ) (1/2),
      F (x+1/2) (y+1/2)) =
      ∫ x in (0:ℝ)..1, ∫ y in (0:ℝ)..1, F x y := by
  calc
    _ = ∫ x in Icc (-1/2:ℝ) (1/2), ∫ y in (-1/2:ℝ)..(1/2),
        F (x+1/2) (y+1/2) := by
      congr 1
      funext x
      exact (interval_eq_Icc (by norm_num) (fun y => F (x+1/2) (y+1/2))).symm
    _ = ∫ x in (-1/2:ℝ)..(1/2), ∫ y in (-1/2:ℝ)..(1/2),
        F (x+1/2) (y+1/2) := by
      exact (interval_eq_Icc (by norm_num)
        (fun x => ∫ y in (-1/2:ℝ)..(1/2), F (x+1/2) (y+1/2))).symm
    _ = ∫ x in (-1/2:ℝ)..(1/2), ∫ y in (0:ℝ)..1, F (x+1/2) y := by
      congr 1
      funext x
      convert (intervalIntegral.integral_comp_add_right (a := (-1/2:ℝ)) (b := 1/2)
          (f := fun y => F (x+1/2) y) (1/2)) using 1 <;> norm_num
    _ = ∫ x in (0:ℝ)..1, ∫ y in (0:ℝ)..1, F x y := by
      convert (intervalIntegral.integral_comp_add_right (a := (-1/2:ℝ)) (b := 1/2)
          (f := fun x => ∫ y in (0:ℝ)..1, F x y) (1/2)) using 1 <;> norm_num

private theorem triangle_sine_inner (m : ℕ) (hm : 0 < m) (r : ℝ) :
    (∫ t in (0:ℝ)..(1-r),
      Real.sin (Real.pi*(m:ℝ)*(t+r))*Real.sin (Real.pi*(m:ℝ)*t)) =
      ((1-r)*Real.cos (Real.pi*(m:ℝ)*r) +
        Real.sin (Real.pi*(m:ℝ)*r)/(Real.pi*(m:ℝ)))/2 := by
  let w : ℝ := Real.pi*(m:ℝ)
  have hw : w ≠ 0 := by dsimp [w]; positivity
  have hpoint (t : ℝ) :
      Real.sin (w*(t+r))*Real.sin (w*t) =
        (Real.cos (w*r)-Real.cos (2*w*t+w*r))/2 := by
    have htrig := Real.two_mul_sin_mul_sin (w*(t+r)) (w*t)
    have hdiff : w*(t+r)-w*t=w*r := by ring
    have hadd : w*(t+r)+w*t=2*w*t+w*r := by ring
    rw [hdiff, hadd] at htrig
    linarith
  have hcosint :
      (∫ t in (0:ℝ)..(1-r), Real.cos (2*w*t+w*r)) =
        -Real.sin (w*r)/w := by
    have hc : 2*w ≠ 0 := mul_ne_zero two_ne_zero hw
    have hchange := intervalIntegral.integral_comp_mul_add
      (a := (0:ℝ)) (b := 1-r) Real.cos hc (w*r)
    have hend : 2*w*(1-r)+w*r = (m:ℝ)*(2*Real.pi)-w*r := by
      dsimp [w]
      ring
    rw [hchange, integral_cos, hend, Real.sin_nat_mul_two_pi_sub]
    have hstart : 2*w*0+w*r = w*r := by ring
    rw [hstart]
    simp only [smul_eq_mul]
    field_simp
    ring
  calc
    _ = ∫ t in (0:ℝ)..(1-r),
        ((1/2:ℝ)*Real.cos (w*r)-(1/2)*Real.cos (2*w*t+w*r)) := by
      apply intervalIntegral.integral_congr
      intro t ht
      change Real.sin (w*(t+r))*Real.sin (w*t) =
        (1/2:ℝ)*Real.cos (w*r)-(1/2)*Real.cos (2*w*t+w*r)
      rw [hpoint t]
      ring
    _ = (∫ t in (0:ℝ)..(1-r), (1/2:ℝ)*Real.cos (w*r)) -
        ∫ t in (0:ℝ)..(1-r), (1/2:ℝ)*Real.cos (2*w*t+w*r) := by
      have hcos : Continuous (fun t : ℝ => Real.cos (2*w*t+w*r)) := by fun_prop
      have hconst : Continuous (fun _ : ℝ => (1/2:ℝ)*Real.cos (w*r)) := continuous_const
      have hcosconst : Continuous (fun t : ℝ => (1/2:ℝ)*Real.cos (2*w*t+w*r)) :=
        continuous_const.mul hcos
      rw [intervalIntegral.integral_sub (hconst.intervalIntegrable 0 (1-r))
        (hcosconst.intervalIntegrable 0 (1-r))]
    _ = (1/2*Real.cos (w*r))*(1-r) -
        (1/2)*∫ t in (0:ℝ)..(1-r), Real.cos (2*w*t+w*r) := by
      rw [intervalIntegral.integral_const, intervalIntegral.integral_const_mul]
      simp only [smul_eq_mul]
      ring
    _ = _ := by rw [hcosint]; dsimp [w]; ring

private theorem triangle_cosine_inner (m : ℕ) (hm : 0 < m) (r : ℝ) :
    (∫ t in (0:ℝ)..(1-r),
      Real.cos (Real.pi*(m:ℝ)*(t+r))*Real.cos (Real.pi*(m:ℝ)*t)) =
      ((1-r)*Real.cos (Real.pi*(m:ℝ)*r) -
        Real.sin (Real.pi*(m:ℝ)*r)/(Real.pi*(m:ℝ)))/2 := by
  let w : ℝ := Real.pi*(m:ℝ)
  have hw : w ≠ 0 := by dsimp [w]; positivity
  have hpoint (t : ℝ) :
      Real.cos (w*(t+r))*Real.cos (w*t) =
        (Real.cos (w*r)+Real.cos (2*w*t+w*r))/2 := by
    have htrig := Real.two_mul_cos_mul_cos (w*(t+r)) (w*t)
    have hdiff : w*(t+r)-w*t=w*r := by ring
    have hadd : w*(t+r)+w*t=2*w*t+w*r := by ring
    rw [hdiff, hadd] at htrig
    linarith
  have hcosint :
      (∫ t in (0:ℝ)..(1-r), Real.cos (2*w*t+w*r)) =
        -Real.sin (w*r)/w := by
    have hc : 2*w ≠ 0 := mul_ne_zero two_ne_zero hw
    have hchange := intervalIntegral.integral_comp_mul_add
      (a := (0:ℝ)) (b := 1-r) Real.cos hc (w*r)
    have hend : 2*w*(1-r)+w*r = (m:ℝ)*(2*Real.pi)-w*r := by
      dsimp [w]
      ring
    rw [hchange, integral_cos, hend, Real.sin_nat_mul_two_pi_sub]
    have hstart : 2*w*0+w*r = w*r := by ring
    rw [hstart]
    simp only [smul_eq_mul]
    field_simp [hw]
    ring
  calc
    _ = ∫ t in (0:ℝ)..(1-r),
        ((1/2:ℝ)*Real.cos (w*r)+(1/2)*Real.cos (2*w*t+w*r)) := by
      apply intervalIntegral.integral_congr
      intro t ht
      change Real.cos (w*(t+r))*Real.cos (w*t) =
        (1/2:ℝ)*Real.cos (w*r)+(1/2)*Real.cos (2*w*t+w*r)
      rw [hpoint t]
      ring
    _ = (∫ t in (0:ℝ)..(1-r), (1/2:ℝ)*Real.cos (w*r)) +
        ∫ t in (0:ℝ)..(1-r), (1/2:ℝ)*Real.cos (2*w*t+w*r) := by
      have hcos : Continuous (fun t : ℝ => Real.cos (2*w*t+w*r)) := by fun_prop
      have hconst : Continuous (fun _ : ℝ => (1/2:ℝ)*Real.cos (w*r)) := continuous_const
      have hcosconst : Continuous (fun t : ℝ => (1/2:ℝ)*Real.cos (2*w*t+w*r)) :=
        continuous_const.mul hcos
      rw [intervalIntegral.integral_add (hconst.intervalIntegrable 0 (1-r))
        (hcosconst.intervalIntegrable 0 (1-r))]
    _ = (1/2*Real.cos (w*r))*(1-r) +
        (1/2)*∫ t in (0:ℝ)..(1-r), Real.cos (2*w*t+w*r) := by
      rw [intervalIntegral.integral_const, intervalIntegral.integral_const_mul]
      simp only [smul_eq_mul]
      ring
    _ = _ := by rw [hcosint]; dsimp [w]; ring

/-- Exact covariance integral of a positive sine mode on the unit interval. -/
theorem bflatQ3SineModeIntegral (ell : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1)
    (m : ℕ) (hm : 0 < m) :
    (∫ x in Icc (-1/2:ℝ) (1/2), ∫ y in Icc (-1/2:ℝ) (1/2),
      ASDExplicitGamma.q3Cov ((x-y)/ell) *
        Real.sin (Real.pi*(m:ℝ)*(x+1/2)) * Real.sin (Real.pi*(m:ℝ)*(y+1/2))) =
      ell * (∫ u in (0:ℝ)..1,
        ASDExplicitGamma.q3Cov u *
          ((1-ell*u)*Real.cos (Real.pi*(m:ℝ)*(ell*u)) +
            Real.sin (Real.pi*(m:ℝ)*(ell*u))/(Real.pi*(m:ℝ)))) := by
  let w : ℝ := Real.pi*(m:ℝ)
  let H : ℝ → ℝ → ℝ := fun x y =>
    ASDExplicitGamma.q3Cov ((x-y)/ell) * Real.sin (w*x) * Real.sin (w*y)
  have hq : Continuous ASDExplicitGamma.q3Cov :=
    ASDExplicitGamma.Model.q3Cov_contDiff_two.continuous
  have hH : Continuous (Function.uncurry H) := by
    dsimp [H]
    fun_prop (disch := assumption)
  have hsym (x y : ℝ) : H x y = H y x := by
    dsimp [H]
    rw [show (x-y)/ell = -((y-x)/ell) by ring, ASDExplicitGamma.Model.q3Cov_even]
    ring
  have hcentered := centered_square_shift H
  have htri := square_eq_twice_triangle H hH hsym
  have hshift := triangle_shift_swap H hH
  have htriEval :
      (∫ r in (0:ℝ)..1, ∫ x in (0:ℝ)..(1-r), H x (x+r)) =
        ∫ r in (0:ℝ)..1,
          ASDExplicitGamma.q3Cov (r/ell) *
            (((1-r)*Real.cos (w*r)+Real.sin (w*r)/w)/2) := by
    apply intervalIntegral.integral_congr
    intro r hr
    calc
      (∫ x in (0:ℝ)..(1-r), H x (x+r)) =
          ∫ x in (0:ℝ)..(1-r),
            ASDExplicitGamma.q3Cov (r/ell) *
              (Real.sin (w*(x+r))*Real.sin (w*x)) := by
        apply intervalIntegral.integral_congr
        intro x hx
        dsimp [H]
        have harg : (x-(x+r))/ell = -(r/ell) := by ring
        rw [harg, ASDExplicitGamma.Model.q3Cov_even]
        ring
      _ = ASDExplicitGamma.q3Cov (r/ell) *
          (∫ x in (0:ℝ)..(1-r), Real.sin (w*(x+r))*Real.sin (w*x)) := by
        rw [intervalIntegral.integral_const_mul]
      _ = ASDExplicitGamma.q3Cov (r/ell) *
          (((1-r)*Real.cos (w*r)+Real.sin (w*r)/w)/2) := by
        rw [triangle_sine_inner m hm r]
  have houter :
      (∫ r in (0:ℝ)..1,
        ASDExplicitGamma.q3Cov (r/ell) *
          ((1-r)*Real.cos (w*r)+Real.sin (w*r)/w)) =
        ell * (∫ u in (0:ℝ)..1,
          ASDExplicitGamma.q3Cov u *
            ((1-ell*u)*Real.cos (w*(ell*u))+Real.sin (w*(ell*u))/w)) := by
    let F : ℝ → ℝ := fun r => ASDExplicitGamma.q3Cov (r/ell) *
      ((1-r)*Real.cos (w*r)+Real.sin (w*r)/w)
    have hF : Continuous F := by dsimp [F]; fun_prop (disch := assumption)
    have hzero : ∫ r in ell..1, F r = 0 := by
      calc
        (∫ r in ell..1, F r) = ∫ r in ell..1, (0 : ℝ) := by
          apply intervalIntegral.integral_congr
          intro r hr
          have hr' : r ∈ Icc ell 1 := by simpa [Set.uIcc_of_le hell1] using hr
          have hr0 : 0 ≤ r := (le_of_lt hell).trans hr'.1
          have hnonneg : 0 ≤ r/ell := div_nonneg hr0 (le_of_lt hell)
          have habs : |r/ell| = r/ell := abs_of_nonneg hnonneg
          have hge : 1 ≤ |r/ell| := by
            rw [habs, le_div_iff₀ hell]
            simpa using hr'.1
          dsimp [F]
          rw [q3Cov_zero_of_abs_ge_one hge]
          ring
        _ = 0 := by simp
    have hsplit := intervalIntegral.integral_add_adjacent_intervals
      (hF.intervalIntegrable (μ := volume) 0 ell)
      (hF.intervalIntegrable (μ := volume) ell 1)
    have hchange : (∫ r in (0:ℝ)..ell, F r) =
        ell * (∫ u in (0:ℝ)..1, F (ell*u)) := by
      convert (intervalIntegral.smul_integral_comp_mul_left
        (a := (0:ℝ)) (b := 1) F ell).symm using 1 <;> simp
    calc
      (∫ r in (0:ℝ)..1, F r) =
          (∫ r in (0:ℝ)..ell, F r) + ∫ r in ell..1, F r := hsplit.symm
      _ = ∫ r in (0:ℝ)..ell, F r := by rw [hzero]; ring
      _ = ell * (∫ u in (0:ℝ)..1,
            ASDExplicitGamma.q3Cov u *
              ((1-ell*u)*Real.cos (w*(ell*u))+Real.sin (w*(ell*u))/w)) := by
        rw [hchange]
        congr 1
        apply intervalIntegral.integral_congr
        intro u hu
        dsimp [F]
        have harg : ell*u/ell = u := by field_simp [ne_of_gt hell]
        rw [harg]
  have hcoeff :
      (∫ u in (0:ℝ)..1,
        ASDExplicitGamma.q3Cov u *
          ((1-ell*u)*Real.cos (w*(ell*u))+Real.sin (w*(ell*u))/w)) =
        (∫ u in (0:ℝ)..1,
          ASDExplicitGamma.q3Cov u*(1-ell*u)*Real.cos ((w*ell)*u)) +
          (1/w)*(∫ u in (0:ℝ)..1,
            ASDExplicitGamma.q3Cov u*Real.sin ((w*ell)*u)) := by
    have hcos : Continuous (fun u : ℝ =>
        ASDExplicitGamma.q3Cov u*(1-ell*u)*Real.cos ((w*ell)*u)) := by fun_prop
    have hsin : Continuous (fun u : ℝ =>
        ASDExplicitGamma.q3Cov u*Real.sin ((w*ell)*u)) := by fun_prop
    have hscaled : Continuous (fun u : ℝ =>
        (1/w)*(ASDExplicitGamma.q3Cov u*Real.sin ((w*ell)*u))) :=
      continuous_const.mul hsin
    have hpoint (u : ℝ) :
        ASDExplicitGamma.q3Cov u *
          ((1-ell*u)*Real.cos (w*(ell*u))+Real.sin (w*(ell*u))/w) =
        ASDExplicitGamma.q3Cov u*(1-ell*u)*Real.cos ((w*ell)*u) +
          (1/w)*(ASDExplicitGamma.q3Cov u*Real.sin ((w*ell)*u)) := by
      rw [show w*(ell*u)=(w*ell)*u by ring]
      ring
    calc
      _ = ∫ u in (0:ℝ)..1,
          ASDExplicitGamma.q3Cov u*(1-ell*u)*Real.cos ((w*ell)*u) +
            (1/w)*(ASDExplicitGamma.q3Cov u*Real.sin ((w*ell)*u)) := by
        apply intervalIntegral.integral_congr
        intro u hu
        exact hpoint u
      _ = (∫ u in (0:ℝ)..1,
          ASDExplicitGamma.q3Cov u*(1-ell*u)*Real.cos ((w*ell)*u)) +
          ∫ u in (0:ℝ)..1,
            (1/w)*(ASDExplicitGamma.q3Cov u*Real.sin ((w*ell)*u)) :=
        intervalIntegral.integral_add (hcos.intervalIntegrable 0 1)
          (hscaled.intervalIntegrable 0 1)
      _ = _ := by rw [intervalIntegral.integral_const_mul]
  calc
    _ = ∫ x in Icc (-1/2:ℝ) (1/2), ∫ y in Icc (-1/2:ℝ) (1/2),
          H (x+1/2) (y+1/2) := by
      apply integral_congr_ae
      filter_upwards with x
      apply integral_congr_ae
      filter_upwards with y
      dsimp [H, w]
      rw [show ((x+1/2)-(y+1/2))/ell = (x-y)/ell by ring]
    _ = ∫ x in (0:ℝ)..1, ∫ y in (0:ℝ)..1, H x y := hcentered
    _ = 2 * (∫ r in (0:ℝ)..1,
          ASDExplicitGamma.q3Cov (r/ell) *
            (((1-r)*Real.cos (w*r)+Real.sin (w*r)/w)/2)) := by
      rw [htri, hshift, ← htriEval]
    _ = ∫ r in (0:ℝ)..1,
          ASDExplicitGamma.q3Cov (r/ell) *
            ((1-r)*Real.cos (w*r)+Real.sin (w*r)/w) := by
      rw [← intervalIntegral.integral_const_mul]
      congr 1
      funext r
      ring
    _ = ell * (∫ u in (0:ℝ)..1,
          ASDExplicitGamma.q3Cov u *
            ((1-ell*u)*Real.cos (w*(ell*u))+Real.sin (w*(ell*u))/w)) := houter
    _ = ell * ((∫ u in (0:ℝ)..1,
          ASDExplicitGamma.q3Cov u*(1-ell*u)*Real.cos ((w*ell)*u)) +
          (1/w)*(∫ u in (0:ℝ)..1,
            ASDExplicitGamma.q3Cov u*Real.sin ((w*ell)*u))) := by rw [hcoeff]
    _ = _ := by
      simpa only [w] using congrArg (fun z : ℝ => ell*z) hcoeff.symm

/-- Exact covariance integral of a positive cosine mode on the unit interval. -/
theorem bflatQ3CosineModeIntegral (ell : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1)
    (m : ℕ) (hm : 0 < m) :
    (∫ x in Icc (-1/2:ℝ) (1/2), ∫ y in Icc (-1/2:ℝ) (1/2),
      ASDExplicitGamma.q3Cov ((x-y)/ell) *
        Real.cos (Real.pi*(m:ℝ)*(x+1/2)) * Real.cos (Real.pi*(m:ℝ)*(y+1/2))) =
      ell * (∫ u in (0:ℝ)..1,
        ASDExplicitGamma.q3Cov u *
          ((1-ell*u)*Real.cos (Real.pi*(m:ℝ)*(ell*u)) -
            Real.sin (Real.pi*(m:ℝ)*(ell*u))/(Real.pi*(m:ℝ)))) := by
  let w : ℝ := Real.pi*(m:ℝ)
  let H : ℝ → ℝ → ℝ := fun x y =>
    ASDExplicitGamma.q3Cov ((x-y)/ell) * Real.cos (w*x) * Real.cos (w*y)
  have hq : Continuous ASDExplicitGamma.q3Cov :=
    ASDExplicitGamma.Model.q3Cov_contDiff_two.continuous
  have hH : Continuous (Function.uncurry H) := by
    dsimp [H]
    fun_prop (disch := assumption)
  have hsym (x y : ℝ) : H x y = H y x := by
    dsimp [H]
    rw [show (x-y)/ell = -((y-x)/ell) by ring, ASDExplicitGamma.Model.q3Cov_even]
    ring
  have hcentered := centered_square_shift H
  have htri := square_eq_twice_triangle H hH hsym
  have hshift := triangle_shift_swap H hH
  have htriEval :
      (∫ r in (0:ℝ)..1, ∫ x in (0:ℝ)..(1-r), H x (x+r)) =
        ∫ r in (0:ℝ)..1,
          ASDExplicitGamma.q3Cov (r/ell) *
            (((1-r)*Real.cos (w*r)-Real.sin (w*r)/w)/2) := by
    apply intervalIntegral.integral_congr
    intro r hr
    calc
      (∫ x in (0:ℝ)..(1-r), H x (x+r)) =
          ∫ x in (0:ℝ)..(1-r),
            ASDExplicitGamma.q3Cov (r/ell) *
              (Real.cos (w*(x+r))*Real.cos (w*x)) := by
        apply intervalIntegral.integral_congr
        intro x hx
        dsimp [H]
        have harg : (x-(x+r))/ell = -(r/ell) := by ring
        rw [harg, ASDExplicitGamma.Model.q3Cov_even]
        ring
      _ = ASDExplicitGamma.q3Cov (r/ell) *
          (∫ x in (0:ℝ)..(1-r), Real.cos (w*(x+r))*Real.cos (w*x)) := by
        rw [intervalIntegral.integral_const_mul]
      _ = ASDExplicitGamma.q3Cov (r/ell) *
          (((1-r)*Real.cos (w*r)-Real.sin (w*r)/w)/2) := by
        rw [triangle_cosine_inner m hm r]
  have houter :
      (∫ r in (0:ℝ)..1,
        ASDExplicitGamma.q3Cov (r/ell) *
          ((1-r)*Real.cos (w*r)-Real.sin (w*r)/w)) =
        ell * (∫ u in (0:ℝ)..1,
          ASDExplicitGamma.q3Cov u *
            ((1-ell*u)*Real.cos (w*(ell*u))-Real.sin (w*(ell*u))/w)) := by
    let F : ℝ → ℝ := fun r => ASDExplicitGamma.q3Cov (r/ell) *
      ((1-r)*Real.cos (w*r)-Real.sin (w*r)/w)
    have hF : Continuous F := by dsimp [F]; fun_prop (disch := assumption)
    have hzero : ∫ r in ell..1, F r = 0 := by
      calc
        (∫ r in ell..1, F r) = ∫ r in ell..1, (0 : ℝ) := by
          apply intervalIntegral.integral_congr
          intro r hr
          have hr' : r ∈ Icc ell 1 := by simpa [Set.uIcc_of_le hell1] using hr
          have hr0 : 0 ≤ r := (le_of_lt hell).trans hr'.1
          have hnonneg : 0 ≤ r/ell := div_nonneg hr0 (le_of_lt hell)
          have habs : |r/ell| = r/ell := abs_of_nonneg hnonneg
          have hge : 1 ≤ |r/ell| := by
            rw [habs, le_div_iff₀ hell]
            simpa using hr'.1
          dsimp [F]
          rw [q3Cov_zero_of_abs_ge_one hge]
          ring
        _ = 0 := by simp
    have hsplit := intervalIntegral.integral_add_adjacent_intervals
      (hF.intervalIntegrable (μ := volume) 0 ell)
      (hF.intervalIntegrable (μ := volume) ell 1)
    have hchange : (∫ r in (0:ℝ)..ell, F r) =
        ell * (∫ u in (0:ℝ)..1, F (ell*u)) := by
      convert (intervalIntegral.smul_integral_comp_mul_left
        (a := (0:ℝ)) (b := 1) F ell).symm using 1 <;> simp
    calc
      (∫ r in (0:ℝ)..1, F r) =
          (∫ r in (0:ℝ)..ell, F r) + ∫ r in ell..1, F r := hsplit.symm
      _ = ∫ r in (0:ℝ)..ell, F r := by rw [hzero]; ring
      _ = ell * (∫ u in (0:ℝ)..1,
            ASDExplicitGamma.q3Cov u *
              ((1-ell*u)*Real.cos (w*(ell*u))-Real.sin (w*(ell*u))/w)) := by
        rw [hchange]
        congr 1
        apply intervalIntegral.integral_congr
        intro u hu
        dsimp [F]
        have harg : ell*u/ell = u := by field_simp [ne_of_gt hell]
        rw [harg]
  have hcoeff :
      (∫ u in (0:ℝ)..1,
        ASDExplicitGamma.q3Cov u *
          ((1-ell*u)*Real.cos (w*(ell*u))-Real.sin (w*(ell*u))/w)) =
        (∫ u in (0:ℝ)..1,
          ASDExplicitGamma.q3Cov u*(1-ell*u)*Real.cos ((w*ell)*u)) -
          (1/w)*(∫ u in (0:ℝ)..1,
            ASDExplicitGamma.q3Cov u*Real.sin ((w*ell)*u)) := by
    have hcos : Continuous (fun u : ℝ =>
        ASDExplicitGamma.q3Cov u*(1-ell*u)*Real.cos ((w*ell)*u)) := by fun_prop
    have hsin : Continuous (fun u : ℝ =>
        ASDExplicitGamma.q3Cov u*Real.sin ((w*ell)*u)) := by fun_prop
    have hscaled : Continuous (fun u : ℝ =>
        (1/w)*(ASDExplicitGamma.q3Cov u*Real.sin ((w*ell)*u))) :=
      continuous_const.mul hsin
    have hpoint (u : ℝ) :
        ASDExplicitGamma.q3Cov u *
          ((1-ell*u)*Real.cos (w*(ell*u))-Real.sin (w*(ell*u))/w) =
        ASDExplicitGamma.q3Cov u*(1-ell*u)*Real.cos ((w*ell)*u) -
          (1/w)*(ASDExplicitGamma.q3Cov u*Real.sin ((w*ell)*u)) := by
      rw [show w*(ell*u)=(w*ell)*u by ring]
      ring
    calc
      _ = ∫ u in (0:ℝ)..1,
          ASDExplicitGamma.q3Cov u*(1-ell*u)*Real.cos ((w*ell)*u) -
            (1/w)*(ASDExplicitGamma.q3Cov u*Real.sin ((w*ell)*u)) := by
        apply intervalIntegral.integral_congr
        intro u hu
        exact hpoint u
      _ = (∫ u in (0:ℝ)..1,
          ASDExplicitGamma.q3Cov u*(1-ell*u)*Real.cos ((w*ell)*u)) -
          ∫ u in (0:ℝ)..1,
            (1/w)*(ASDExplicitGamma.q3Cov u*Real.sin ((w*ell)*u)) :=
        intervalIntegral.integral_sub (hcos.intervalIntegrable 0 1)
          (hscaled.intervalIntegrable 0 1)
      _ = _ := by rw [intervalIntegral.integral_const_mul]
  calc
    _ = ∫ x in Icc (-1/2:ℝ) (1/2), ∫ y in Icc (-1/2:ℝ) (1/2),
          H (x+1/2) (y+1/2) := by
      apply integral_congr_ae
      filter_upwards with x
      apply integral_congr_ae
      filter_upwards with y
      dsimp [H, w]
      rw [show ((x+1/2)-(y+1/2))/ell = (x-y)/ell by ring]
    _ = ∫ x in (0:ℝ)..1, ∫ y in (0:ℝ)..1, H x y := hcentered
    _ = 2 * (∫ r in (0:ℝ)..1,
          ASDExplicitGamma.q3Cov (r/ell) *
            (((1-r)*Real.cos (w*r)-Real.sin (w*r)/w)/2)) := by
      rw [htri, hshift, ← htriEval]
    _ = ∫ r in (0:ℝ)..1,
          ASDExplicitGamma.q3Cov (r/ell) *
            ((1-r)*Real.cos (w*r)-Real.sin (w*r)/w) := by
      rw [← intervalIntegral.integral_const_mul]
      congr 1
      funext r
      ring
    _ = ell * (∫ u in (0:ℝ)..1,
          ASDExplicitGamma.q3Cov u *
            ((1-ell*u)*Real.cos (w*(ell*u))-Real.sin (w*(ell*u))/w)) := houter
    _ = ell * ((∫ u in (0:ℝ)..1,
          ASDExplicitGamma.q3Cov u*(1-ell*u)*Real.cos ((w*ell)*u)) -
          (1/w)*(∫ u in (0:ℝ)..1,
            ASDExplicitGamma.q3Cov u*Real.sin ((w*ell)*u))) := by rw [hcoeff]
    _ = _ := by
      simpa only [w] using congrArg (fun z : ℝ => ell*z) hcoeff.symm

/-- The constant cosine mode covariance integral is the triangular q3 kernel mass. -/
theorem bflatQ3ConstantModeIntegral (ell : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1) :
    (∫ x in Icc (-1/2:ℝ) (1/2), ∫ y in Icc (-1/2:ℝ) (1/2),
      ASDExplicitGamma.q3Cov ((x-y)/ell)) =
      2*ell*(∫ u in (0:ℝ)..1,
        ASDExplicitGamma.q3Cov u*(1-ell*u)) := by
  let H : ℝ → ℝ → ℝ := fun x y => ASDExplicitGamma.q3Cov ((x-y)/ell)
  have hq : Continuous ASDExplicitGamma.q3Cov :=
    ASDExplicitGamma.Model.q3Cov_contDiff_two.continuous
  have hH : Continuous (Function.uncurry H) := by
    dsimp [H]
    fun_prop (disch := assumption)
  have hsym (x y : ℝ) : H x y = H y x := by
    dsimp [H]
    rw [show (x-y)/ell = -((y-x)/ell) by ring,
      ASDExplicitGamma.Model.q3Cov_even]
  have hcentered := centered_square_shift H
  have htri := square_eq_twice_triangle H hH hsym
  have hshift := triangle_shift_swap H hH
  have htriEval :
      (∫ r in (0:ℝ)..1, ∫ x in (0:ℝ)..(1-r), H x (x+r)) =
        ∫ r in (0:ℝ)..1, ASDExplicitGamma.q3Cov (r/ell)*(1-r) := by
    apply intervalIntegral.integral_congr
    intro r hr
    calc
      (∫ x in (0:ℝ)..(1-r), H x (x+r)) =
          ∫ x in (0:ℝ)..(1-r), ASDExplicitGamma.q3Cov (r/ell) := by
        apply intervalIntegral.integral_congr
        intro x hx
        dsimp [H]
        rw [show (x-(x+r))/ell = -(r/ell) by ring,
          ASDExplicitGamma.Model.q3Cov_even]
      _ = ASDExplicitGamma.q3Cov (r/ell)*(1-r) := by
        rw [intervalIntegral.integral_const]
        ring
  have houter :
      (∫ r in (0:ℝ)..1, ASDExplicitGamma.q3Cov (r/ell)*(1-r)) =
        ell*(∫ u in (0:ℝ)..1, ASDExplicitGamma.q3Cov u*(1-ell*u)) := by
    let F : ℝ → ℝ := fun r => ASDExplicitGamma.q3Cov (r/ell)*(1-r)
    have hF : Continuous F := by dsimp [F]; fun_prop (disch := assumption)
    have hzero : (∫ r in ell..1, F r) = 0 := by
      calc
        (∫ r in ell..1, F r) = ∫ r in ell..1, (0:ℝ) := by
          apply intervalIntegral.integral_congr
          intro r hr
          have hr' : r ∈ Icc ell 1 := by simpa [Set.uIcc_of_le hell1] using hr
          have hr0 : 0 ≤ r := (le_of_lt hell).trans hr'.1
          have hnonneg : 0 ≤ r/ell := div_nonneg hr0 hell.le
          have hge : 1 ≤ |r/ell| := by
            rw [abs_of_nonneg hnonneg, le_div_iff₀ hell]
            simpa using hr'.1
          dsimp [F]
          rw [q3Cov_zero_of_abs_ge_one hge]
          ring
        _ = 0 := by simp
    have hsplit := intervalIntegral.integral_add_adjacent_intervals
      (hF.intervalIntegrable (μ := volume) 0 ell)
      (hF.intervalIntegrable (μ := volume) ell 1)
    have hchange : (∫ r in (0:ℝ)..ell, F r) =
        ell*(∫ u in (0:ℝ)..1, F (ell*u)) := by
      convert (intervalIntegral.smul_integral_comp_mul_left
        (a := (0:ℝ)) (b := 1) F ell).symm using 1 <;> simp
    calc
      _ = (∫ r in (0:ℝ)..ell, F r) + ∫ r in ell..1, F r := hsplit.symm
      _ = ∫ r in (0:ℝ)..ell, F r := by rw [hzero]; ring
      _ = ell*(∫ u in (0:ℝ)..1, ASDExplicitGamma.q3Cov u*(1-ell*u)) := by
        rw [hchange]
        congr 1
        apply intervalIntegral.integral_congr
        intro u hu
        dsimp [F]
        rw [show ell*u/ell=u by field_simp [ne_of_gt hell]]
  calc
    _ = ∫ x in Icc (-1/2:ℝ) (1/2), ∫ y in Icc (-1/2:ℝ) (1/2),
          H (x+1/2) (y+1/2) := by
      apply integral_congr_ae
      filter_upwards with x
      apply integral_congr_ae
      filter_upwards with y
      dsimp [H]
      rw [show ((x+1/2)-(y+1/2))/ell=(x-y)/ell by ring]
    _ = ∫ x in (0:ℝ)..1, ∫ y in (0:ℝ)..1, H x y := hcentered
    _ = 2*(∫ r in (0:ℝ)..1, ∫ x in (0:ℝ)..(1-r), H x (x+r)) := by
      rw [htri, hshift]
    _ = 2*(∫ r in (0:ℝ)..1, ASDExplicitGamma.q3Cov (r/ell)*(1-r)) := by
      rw [htriEval]
    _ = 2*ell*(∫ u in (0:ℝ)..1, ASDExplicitGamma.q3Cov u*(1-ell*u)) := by
      rw [houter]
      ring

private theorem q3ModeLength_pos (j : ℕ) :
    0 < (ASDExplicitGamma.Numerics.Model.q3ModeLength j : ℝ) := by
  have h : (0 : ℚ) < 3 ^ j := pow_pos (by norm_num : (0 : ℚ) < 3) j
  rw [ASDExplicitGamma.Numerics.Model.q3ModeLength]
  exact_mod_cast (one_div_pos.mpr h)

private theorem q3ModeLength_le_one (j : ℕ) :
    (ASDExplicitGamma.Numerics.Model.q3ModeLength j : ℝ) ≤ 1 := by
  have hpow : (1 : ℚ) ≤ 3 ^ j := by
    induction j with
    | zero => norm_num
    | succ j ih =>
        rw [pow_succ]
        nlinarith
  have hden : (0 : ℚ) < 3 ^ j := pow_pos (by norm_num : (0 : ℚ) < 3) j
  have hq : ASDExplicitGamma.Numerics.Model.q3ModeLength j ≤ 1 := by
    rw [ASDExplicitGamma.Numerics.Model.q3ModeLength, div_le_iff₀ hden]
    simpa using hpow
  exact_mod_cast hq

private theorem q3ModeFrequency_eq (j n : ℕ) :
    ASDExplicitGamma.Numerics.Model.q3ModeFrequency j n =
      Real.pi * ((n+1 : ℕ) : ℝ) *
        (ASDExplicitGamma.Numerics.Model.q3ModeLength j : ℝ) := by
  unfold ASDExplicitGamma.Numerics.Model.q3ModeFrequency
    ASDExplicitGamma.Numerics.Model.q3ModeLength
  push_cast
  field_simp

/-- The exact square covariance of a sine mode is half of the source q3 mode coefficient. -/
theorem bflatQ3SineModeIntegral_eq_q3Mode (j n : ℕ) :
    (∫ x in Icc (-1/2:ℝ) (1/2), ∫ y in Icc (-1/2:ℝ) (1/2),
      ASDExplicitGamma.q3Cov ((x-y)/(ASDExplicitGamma.Numerics.Model.q3ModeLength j : ℝ)) *
        Real.sin (Real.pi*((n+1:ℕ):ℝ)*(x+1/2)) *
        Real.sin (Real.pi*((n+1:ℕ):ℝ)*(y+1/2))) =
      ASDExplicitGamma.Numerics.Model.q3ModeSine j n / 2 := by
  let ell : ℝ := (ASDExplicitGamma.Numerics.Model.q3ModeLength j : ℝ)
  let m : ℕ := n+1
  let w : ℝ := ASDExplicitGamma.Numerics.Model.q3ModeFrequency j n
  have hm : 0 < m := by dsimp [m]; omega
  have hell : 0 < ell := by exact q3ModeLength_pos j
  have hell1 : ell ≤ 1 := by exact q3ModeLength_le_one j
  have hfreq : w = Real.pi*(m:ℝ)*ell := by
    dsimp [w, m, ell]
    exact q3ModeFrequency_eq j n
  have hcos : ASDExplicitGamma.Numerics.Model.q3CosineCoefficient ell w =
      ∫ u in (0:ℝ)..1, ASDExplicitGamma.q3Cov u*(1-ell*u)*
        Real.cos (Real.pi*(m:ℝ)*(ell*u)) := by
    unfold ASDExplicitGamma.Numerics.Model.q3CosineCoefficient
    apply intervalIntegral.integral_congr
    intro u hu
    rw [hfreq]
    change ASDExplicitGamma.q3Cov u*(1-ell*u)*
      Real.cos ((Real.pi*(m:ℝ)*ell)*u) =
        ASDExplicitGamma.q3Cov u*(1-ell*u)*Real.cos (Real.pi*(m:ℝ)*(ell*u))
    congr 1
    congr 1
    ring
  have hsin : ASDExplicitGamma.Numerics.Model.q3SineCoefficient w =
      ∫ u in (0:ℝ)..1, ASDExplicitGamma.q3Cov u*
        Real.sin (Real.pi*(m:ℝ)*(ell*u)) := by
    unfold ASDExplicitGamma.Numerics.Model.q3SineCoefficient
    apply intervalIntegral.integral_congr
    intro u hu
    rw [hfreq]
    change ASDExplicitGamma.q3Cov u*Real.sin ((Real.pi*(m:ℝ)*ell)*u) =
      ASDExplicitGamma.q3Cov u*Real.sin (Real.pi*(m:ℝ)*(ell*u))
    congr 1
    congr 1
    ring
  have hq : Continuous ASDExplicitGamma.q3Cov :=
    ASDExplicitGamma.Model.q3Cov_contDiff_two.continuous
  have hf : IntervalIntegrable
      (fun u : ℝ => ASDExplicitGamma.q3Cov u*(1-ell*u)*
        Real.cos (Real.pi*(m:ℝ)*(ell*u))) volume 0 1 := by
    have hc : Continuous (fun u : ℝ => ASDExplicitGamma.q3Cov u*(1-ell*u)*
        Real.cos (Real.pi*(m:ℝ)*(ell*u))) := by
      fun_prop (disch := assumption)
    exact hc.intervalIntegrable 0 1
  have hg : IntervalIntegrable
      (fun u : ℝ => ASDExplicitGamma.q3Cov u*
        Real.sin (Real.pi*(m:ℝ)*(ell*u))/(Real.pi*(m:ℝ))) volume 0 1 := by
    have hc : Continuous (fun u : ℝ => ASDExplicitGamma.q3Cov u*
        Real.sin (Real.pi*(m:ℝ)*(ell*u))/(Real.pi*(m:ℝ))) := by
      fun_prop (disch := assumption)
    exact hc.intervalIntegrable 0 1
  have hgi : (∫ u in (0:ℝ)..1,
      ASDExplicitGamma.q3Cov u*Real.sin (Real.pi*(m:ℝ)*(ell*u))/(Real.pi*(m:ℝ))) =
      ASDExplicitGamma.Numerics.Model.q3SineCoefficient w/(Real.pi*(m:ℝ)) := by
    calc
      _ = ∫ u in (0:ℝ)..1, (1/(Real.pi*(m:ℝ))) *
          (ASDExplicitGamma.q3Cov u*Real.sin (Real.pi*(m:ℝ)*(ell*u))) := by
        apply intervalIntegral.integral_congr
        intro u hu
        ring
      _ = (1/(Real.pi*(m:ℝ))) *
          (∫ u in (0:ℝ)..1, ASDExplicitGamma.q3Cov u*
            Real.sin (Real.pi*(m:ℝ)*(ell*u))) := by
        rw [intervalIntegral.integral_const_mul]
      _ = _ := by rw [← hsin]; ring
  have hcombined : (∫ u in (0:ℝ)..1, ASDExplicitGamma.q3Cov u *
      ((1-ell*u)*Real.cos (Real.pi*(m:ℝ)*(ell*u)) +
        Real.sin (Real.pi*(m:ℝ)*(ell*u))/(Real.pi*(m:ℝ)))) =
      ASDExplicitGamma.Numerics.Model.q3CosineCoefficient ell w +
        ASDExplicitGamma.Numerics.Model.q3SineCoefficient w/(Real.pi*(m:ℝ)) := by
    calc
      _ = (∫ u in (0:ℝ)..1, ASDExplicitGamma.q3Cov u*(1-ell*u)*
            Real.cos (Real.pi*(m:ℝ)*(ell*u))) +
          (∫ u in (0:ℝ)..1, ASDExplicitGamma.q3Cov u*
            Real.sin (Real.pi*(m:ℝ)*(ell*u))/(Real.pi*(m:ℝ))) := by
        rw [← intervalIntegral.integral_add hf hg]
        apply intervalIntegral.integral_congr
        intro u hu
        ring
      _ = _ := by rw [← hcos, hgi]
  change (∫ x in Icc (-1/2:ℝ) (1/2), ∫ y in Icc (-1/2:ℝ) (1/2),
      ASDExplicitGamma.q3Cov ((x-y)/ell) *
        Real.sin (Real.pi*(m:ℝ)*(x+1/2)) *
        Real.sin (Real.pi*(m:ℝ)*(y+1/2))) = _
  calc
    _ = ell * (∫ u in (0:ℝ)..1, ASDExplicitGamma.q3Cov u *
          ((1-ell*u)*Real.cos (Real.pi*(m:ℝ)*(ell*u)) +
            Real.sin (Real.pi*(m:ℝ)*(ell*u))/(Real.pi*(m:ℝ)))) :=
      bflatQ3SineModeIntegral ell hell hell1 m hm
    _ = ASDExplicitGamma.Numerics.Model.q3ModeSine j n / 2 := by
      rw [hcombined]
      have hmode : ell * (ASDExplicitGamma.Numerics.Model.q3CosineCoefficient ell w +
          ASDExplicitGamma.Numerics.Model.q3SineCoefficient w/(Real.pi*(m:ℝ))) =
          ASDExplicitGamma.Numerics.Model.q3ModeSine j n / 2 := by
        unfold ASDExplicitGamma.Numerics.Model.q3ModeSine
        dsimp [ell, m, w]
        rw [q3ModeFrequency_eq j n]
        ring
      exact hmode

/-- The exact square covariance of a cosine mode is half of the source q3 mode coefficient. -/
theorem bflatQ3CosineModeIntegral_eq_q3Mode (j n : ℕ) :
    (∫ x in Icc (-1/2:ℝ) (1/2), ∫ y in Icc (-1/2:ℝ) (1/2),
      ASDExplicitGamma.q3Cov ((x-y)/(ASDExplicitGamma.Numerics.Model.q3ModeLength j : ℝ)) *
        Real.cos (Real.pi*((n+1:ℕ):ℝ)*(x+1/2)) *
        Real.cos (Real.pi*((n+1:ℕ):ℝ)*(y+1/2))) =
      ASDExplicitGamma.Numerics.Model.q3ModeCosine j n / 2 := by
  let ell : ℝ := (ASDExplicitGamma.Numerics.Model.q3ModeLength j : ℝ)
  let m : ℕ := n+1
  let w : ℝ := ASDExplicitGamma.Numerics.Model.q3ModeFrequency j n
  have hm : 0 < m := by dsimp [m]; omega
  have hell : 0 < ell := by exact q3ModeLength_pos j
  have hell1 : ell ≤ 1 := by exact q3ModeLength_le_one j
  have hfreq : w = Real.pi*(m:ℝ)*ell := by
    dsimp [w, m, ell]
    exact q3ModeFrequency_eq j n
  have hcos : ASDExplicitGamma.Numerics.Model.q3CosineCoefficient ell w =
      ∫ u in (0:ℝ)..1, ASDExplicitGamma.q3Cov u*(1-ell*u)*
        Real.cos (Real.pi*(m:ℝ)*(ell*u)) := by
    unfold ASDExplicitGamma.Numerics.Model.q3CosineCoefficient
    apply intervalIntegral.integral_congr
    intro u hu
    rw [hfreq]
    change ASDExplicitGamma.q3Cov u*(1-ell*u)*
      Real.cos ((Real.pi*(m:ℝ)*ell)*u) =
        ASDExplicitGamma.q3Cov u*(1-ell*u)*Real.cos (Real.pi*(m:ℝ)*(ell*u))
    congr 1
    congr 1
    ring
  have hsin : ASDExplicitGamma.Numerics.Model.q3SineCoefficient w =
      ∫ u in (0:ℝ)..1, ASDExplicitGamma.q3Cov u*
        Real.sin (Real.pi*(m:ℝ)*(ell*u)) := by
    unfold ASDExplicitGamma.Numerics.Model.q3SineCoefficient
    apply intervalIntegral.integral_congr
    intro u hu
    rw [hfreq]
    change ASDExplicitGamma.q3Cov u*Real.sin ((Real.pi*(m:ℝ)*ell)*u) =
      ASDExplicitGamma.q3Cov u*Real.sin (Real.pi*(m:ℝ)*(ell*u))
    congr 1
    congr 1
    ring
  have hq : Continuous ASDExplicitGamma.q3Cov :=
    ASDExplicitGamma.Model.q3Cov_contDiff_two.continuous
  have hf : IntervalIntegrable
      (fun u : ℝ => ASDExplicitGamma.q3Cov u*(1-ell*u)*
        Real.cos (Real.pi*(m:ℝ)*(ell*u))) volume 0 1 := by
    have hc : Continuous (fun u : ℝ => ASDExplicitGamma.q3Cov u*(1-ell*u)*
        Real.cos (Real.pi*(m:ℝ)*(ell*u))) := by
      fun_prop (disch := assumption)
    exact hc.intervalIntegrable 0 1
  have hg : IntervalIntegrable
      (fun u : ℝ => ASDExplicitGamma.q3Cov u*
        Real.sin (Real.pi*(m:ℝ)*(ell*u))/(Real.pi*(m:ℝ))) volume 0 1 := by
    have hc : Continuous (fun u : ℝ => ASDExplicitGamma.q3Cov u*
        Real.sin (Real.pi*(m:ℝ)*(ell*u))/(Real.pi*(m:ℝ))) := by
      fun_prop (disch := assumption)
    exact hc.intervalIntegrable 0 1
  have hgi : (∫ u in (0:ℝ)..1,
      ASDExplicitGamma.q3Cov u*Real.sin (Real.pi*(m:ℝ)*(ell*u))/(Real.pi*(m:ℝ))) =
      ASDExplicitGamma.Numerics.Model.q3SineCoefficient w/(Real.pi*(m:ℝ)) := by
    calc
      _ = ∫ u in (0:ℝ)..1, (1/(Real.pi*(m:ℝ))) *
          (ASDExplicitGamma.q3Cov u*Real.sin (Real.pi*(m:ℝ)*(ell*u))) := by
        apply intervalIntegral.integral_congr
        intro u hu
        ring
      _ = (1/(Real.pi*(m:ℝ))) *
          (∫ u in (0:ℝ)..1, ASDExplicitGamma.q3Cov u*
            Real.sin (Real.pi*(m:ℝ)*(ell*u))) := by
        rw [intervalIntegral.integral_const_mul]
      _ = _ := by rw [← hsin]; ring
  have hcombined : (∫ u in (0:ℝ)..1, ASDExplicitGamma.q3Cov u *
      ((1-ell*u)*Real.cos (Real.pi*(m:ℝ)*(ell*u)) -
        Real.sin (Real.pi*(m:ℝ)*(ell*u))/(Real.pi*(m:ℝ)))) =
      ASDExplicitGamma.Numerics.Model.q3CosineCoefficient ell w -
        ASDExplicitGamma.Numerics.Model.q3SineCoefficient w/(Real.pi*(m:ℝ)) := by
    calc
      _ = (∫ u in (0:ℝ)..1, ASDExplicitGamma.q3Cov u*(1-ell*u)*
            Real.cos (Real.pi*(m:ℝ)*(ell*u))) -
          (∫ u in (0:ℝ)..1, ASDExplicitGamma.q3Cov u*
            Real.sin (Real.pi*(m:ℝ)*(ell*u))/(Real.pi*(m:ℝ))) := by
        rw [← intervalIntegral.integral_sub hf hg]
        apply intervalIntegral.integral_congr
        intro u hu
        ring
      _ = _ := by rw [← hcos, hgi]
  change (∫ x in Icc (-1/2:ℝ) (1/2), ∫ y in Icc (-1/2:ℝ) (1/2),
      ASDExplicitGamma.q3Cov ((x-y)/ell) *
        Real.cos (Real.pi*(m:ℝ)*(x+1/2)) *
        Real.cos (Real.pi*(m:ℝ)*(y+1/2))) = _
  calc
    _ = ell * (∫ u in (0:ℝ)..1, ASDExplicitGamma.q3Cov u *
          ((1-ell*u)*Real.cos (Real.pi*(m:ℝ)*(ell*u)) -
            Real.sin (Real.pi*(m:ℝ)*(ell*u))/(Real.pi*(m:ℝ)))) :=
      bflatQ3CosineModeIntegral ell hell hell1 m hm
    _ = ASDExplicitGamma.Numerics.Model.q3ModeCosine j n / 2 := by
      rw [hcombined]
      have hmode : ell * (ASDExplicitGamma.Numerics.Model.q3CosineCoefficient ell w -
          ASDExplicitGamma.Numerics.Model.q3SineCoefficient w/(Real.pi*(m:ℝ))) =
          ASDExplicitGamma.Numerics.Model.q3ModeCosine j n / 2 := by
        unfold ASDExplicitGamma.Numerics.Model.q3ModeCosine
        dsimp [ell, m, w]
        rw [q3ModeFrequency_eq j n]
        ring
      exact hmode

end ASDExplicitGamma.Model
