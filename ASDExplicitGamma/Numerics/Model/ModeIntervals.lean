module

public import ASDExplicitGamma.Numerics.Model.SmallTrig
public import ASDExplicitGamma.Numerics.Model.MomentIntervals
public import ASDExplicitGamma.Numerics.Model.Q3Modes

/-! Certified intervals for the exact q3 cosine/sine covariance integrals. -/

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
open Mirror

structure ModeEnclosure where
  cosine : QInterval
  sine : QInterval
  difference : QInterval

structure ModeData where
  smallSine : QInterval
  smallCosine : QInterval
  enclosure : ModeEnclosure

def intervalWider (a b : QInterval) : Prop := b.lo ≤ a.lo ∧ a.hi ≤ b.hi
instance instDecidableIntervalWider (a b : QInterval) : Decidable (intervalWider a b) :=
  inferInstanceAs (Decidable (b.lo ≤ a.lo ∧ a.hi ≤ b.hi))

theorem interval_wider_sound {a b : QInterval} {x : ℝ}
    (h : intervalWider a b) (hx : QInterval.Contains a x) : QInterval.Contains b x := by
  have hl : (b.lo : ℝ) ≤ (a.lo : ℝ) := by exact_mod_cast h.1
  have hu : (a.hi : ℝ) ≤ (b.hi : ℝ) := by exact_mod_cast h.2
  exact ⟨hl.trans hx.1,hx.2.trans hu⟩

def smallTrigCheck (r : ℚ) (s c : QInterval) : Bool :=
  match smallTrigIntervals r with
  | none => false
  | some p => decide (0 ≤ r ∧ r ≤ 1/2 ∧ intervalWider p.1 s ∧ intervalWider p.2 c)

theorem small_trig_check_sound (r : ℚ) (s c : QInterval) (h : smallTrigCheck r s c = true) :
    QInterval.Contains s (Real.sin ((r : ℝ)*Real.pi)) ∧
    QInterval.Contains c (Real.cos ((r : ℝ)*Real.pi)) := by
  unfold smallTrigCheck at h
  cases he : smallTrigIntervals r with
  | none => simp only [he,Bool.false_eq_true] at h
  | some p =>
    rw [he] at h
    obtain ⟨hr0,hr1,hs,hc⟩ := of_decide_eq_true h
    have hb := small_trig_intervals_sound r hr0 hr1 p.1 p.2 he
    exact ⟨interval_wider_sound hs hb.1,interval_wider_sound hc hb.2⟩

def intervalSum (G : ℕ) (f : ℕ → QInterval) : ℕ → QInterval
  | 0 => gridConstant G 0
  | n+1 => add G (intervalSum G f n) (f n)

theorem interval_sum_sound (G : ℕ) (f : ℕ → QInterval) (g : ℕ → ℝ)
    (h : ∀ n, QInterval.Contains (f n) (g n)) (N : ℕ) :
    QInterval.Contains (intervalSum G f N) (∑ n ∈ Finset.range N, g n) := by
  induction N with
  | zero => simpa only [intervalSum,Finset.sum_range_zero,Rat.cast_zero] using gridConstant_sound G 0
  | succ N ih => simpa only [intervalSum,Finset.sum_range_succ] using add_sound G ih (h N)

def modeFrequencyInterval (j n : ℕ) : QInterval :=
  tightMul 140 bflatPiInterval (gridConstant 140 (((n+1 : ℕ) : ℚ)/(3 : ℚ)^j))
def modeDenominatorInterval (n : ℕ) : QInterval :=
  tightMul 140 bflatPiInterval (gridConstant 140 ((n+1 : ℕ) : ℚ))

def modePhase (j n : ℕ) : ℚ := ((n+1 : ℕ) : ℚ)/(64*(3 : ℚ)^j)

def modeCovarianceIntervals (j n : ℕ) (s c : QInterval) : Option ModeEnclosure := do
  let w := modeFrequencyInterval j n
  let d := modeDenominatorInterval n
  if hw : 0 < w.lo then
    if hd : 0 < d.lo then
      let p := repeatedDoubleIntervals 140 (s,c) 6
      let M := momentIntervals 140 w p.1 p.2 hw
      let ell := gridConstant 140 (q3ModeLength j)
      let co := intervalSum 140 (fun k => tightMul 140 (gridConstant 140 (q3ModeCoefficient k))
        (sub 140 (M k).1 (tightMul 140 ell (M (k+1)).1))) 14
      let si := tightDiv 140
        (intervalSum 140 (fun k => tightMul 140 (gridConstant 140 (q3ModeCoefficient k)) (M k).2) 14) d hd
      return ⟨tightMul 140 (gridConstant 140 (2*q3ModeLength j)) (sub 140 co si),
        tightMul 140 (gridConstant 140 (2*q3ModeLength j)) (add 140 co si),
        tightMul 140 (gridConstant 140 (4*q3ModeLength j)) si⟩
    else none
  else none

theorem mode_frequency_sound (j n : ℕ) :
    QInterval.Contains (modeFrequencyInterval j n) (q3ModeFrequency j n) := by
  have h := tightMul_sound 140 bflat_pi_sound
    (gridConstant_sound 140 (((n+1 : ℕ) : ℚ)/(3 : ℚ)^j))
  simpa only [modeFrequencyInterval,q3ModeFrequency,Rat.cast_div,Rat.cast_natCast,Rat.cast_pow,Rat.cast_ofNat] using h

theorem mode_denominator_sound (n : ℕ) :
    QInterval.Contains (modeDenominatorInterval n) (Real.pi*((n+1 : ℕ) : ℝ)) := by
  simpa only [modeDenominatorInterval,Rat.cast_natCast] using tightMul_sound 140 bflat_pi_sound
    (gridConstant_sound 140 ((n+1 : ℕ) : ℚ))

theorem mode_phase_formula (j n : ℕ) :
    (2 : ℝ)^6*((modePhase j n : ℚ) : ℝ)*Real.pi = q3ModeFrequency j n := by
  norm_num [modePhase,q3ModeFrequency]
  ring

theorem mode_covariance_intervals_sound (j n : ℕ) (s c : QInterval)
    (hs : QInterval.Contains s (Real.sin (((modePhase j n : ℚ) : ℝ)*Real.pi)))
    (hc : QInterval.Contains c (Real.cos (((modePhase j n : ℚ) : ℝ)*Real.pi)))
    (out : ModeEnclosure) (he : modeCovarianceIntervals j n s c = some out) :
    QInterval.Contains out.cosine (q3ModeCosine j n) ∧
    QInterval.Contains out.sine (q3ModeSine j n) ∧
    QInterval.Contains out.difference (q3ModeDifference j n) := by
  unfold modeCovarianceIntervals at he
  dsimp only at he
  split_ifs at he with hw hd
  · simp only [Option.pure_def,Option.some.injEq] at he
    subst out
    have hp := repeated_double_intervals_sound 140 s c
      ((((modePhase j n : ℚ) : ℝ))*Real.pi) hs hc 6
    have harg : (2 : ℝ)^6*(((modePhase j n : ℚ) : ℝ)*Real.pi) = q3ModeFrequency j n := by
      simpa only [mul_assoc] using mode_phase_formula j n
    rw [harg] at hp
    have hm := moment_intervals_sound 140 (modeFrequencyInterval j n) _ _ hw
      (q3ModeFrequency j n) (mode_frequency_sound j n) hp.1 hp.2
    have hell := gridConstant_sound 140 (q3ModeLength j)
    have hco := interval_sum_sound 140 _ _ (fun k =>
      tightMul_sound 140 (gridConstant_sound 140 (q3ModeCoefficient k))
        (sub_sound 140 (hm k).1 (tightMul_sound 140 hell (hm (k+1)).1))) 14
    have hsi := interval_sum_sound 140 _ _ (fun k =>
      tightMul_sound 140 (gridConstant_sound 140 (q3ModeCoefficient k)) (hm k).2) 14
    change QInterval.Contains _ (q3CosineMomentSum (q3ModeLength j) (q3ModeFrequency j n)) at hco
    change QInterval.Contains _ (q3SineMomentSum (q3ModeFrequency j n)) at hsi
    rw [← q3_cosine_coefficient_formula] at hco
    rw [← q3_sine_coefficient_formula] at hsi
    have hsid := tightDiv_sound 140 hsi hd (mode_denominator_sound n)
    have h2 : QInterval.Contains (gridConstant 140 (2*q3ModeLength j)) (2*(q3ModeLength j : ℝ)) := by
      simpa only [Rat.cast_mul,Rat.cast_ofNat] using gridConstant_sound 140 (2*q3ModeLength j)
    have h4 : QInterval.Contains (gridConstant 140 (4*q3ModeLength j)) (4*(q3ModeLength j : ℝ)) := by
      simpa only [Rat.cast_mul,Rat.cast_ofNat] using gridConstant_sound 140 (4*q3ModeLength j)
    refine ⟨tightMul_sound 140 h2 (sub_sound 140 hco hsid),
      tightMul_sound 140 h2 (add_sound 140 hco hsid), ?_⟩
    have hdiff := tightMul_sound 140 h4 hsid
    unfold q3ModeDifference q3ModeSine q3ModeCosine
    convert hdiff using 1; ring

def modeDataCheck (j n : ℕ) (d : ModeData) : Bool :=
  if smallTrigCheck (modePhase j n) d.smallSine d.smallCosine then
    match modeCovarianceIntervals j n d.smallSine d.smallCosine with
    | none => false
    | some I => decide (intervalWider I.cosine d.enclosure.cosine ∧
        intervalWider I.sine d.enclosure.sine ∧ intervalWider I.difference d.enclosure.difference ∧
        0 ≤ d.enclosure.cosine.lo ∧ 0 ≤ d.enclosure.sine.lo ∧ 0 ≤ d.enclosure.difference.lo)
  else false

/-- No covariance or trigonometric estimate is assumed: a closed data check proves all three. -/
theorem mode_data_sound (j n : ℕ) (d : ModeData) (h : modeDataCheck j n d = true) :
    QInterval.Contains d.enclosure.cosine (q3ModeCosine j n) ∧
    QInterval.Contains d.enclosure.sine (q3ModeSine j n) ∧
    QInterval.Contains d.enclosure.difference (q3ModeDifference j n) ∧
    0 ≤ q3ModeCosine j n ∧ 0 ≤ q3ModeSine j n ∧ 0 ≤ q3ModeDifference j n := by
  unfold modeDataCheck at h
  split_ifs at h with ht
  · have ht' : smallTrigCheck (modePhase j n) d.smallSine d.smallCosine = true := ht
    have htrig := small_trig_check_sound _ _ _ ht'
    cases he : modeCovarianceIntervals j n d.smallSine d.smallCosine with
    | none => simp only [he,Bool.false_eq_true] at h
    | some I =>
      rw [he] at h
      obtain ⟨hco,hsi,hdiff,hcop,hsip,hdiffp⟩ := of_decide_eq_true h
      obtain ⟨hc,hs,hd⟩ := mode_covariance_intervals_sound j n _ _ htrig.1 htrig.2 I he
      have hc' := interval_wider_sound hco hc
      have hs' := interval_wider_sound hsi hs
      have hd' := interval_wider_sound hdiff hd
      have hcp : (0 : ℝ) ≤ (d.enclosure.cosine.lo : ℝ) := by exact_mod_cast hcop
      have hsp : (0 : ℝ) ≤ (d.enclosure.sine.lo : ℝ) := by exact_mod_cast hsip
      have hdp : (0 : ℝ) ≤ (d.enclosure.difference.lo : ℝ) := by exact_mod_cast hdiffp
      exact ⟨hc',hs',hd', hcp.trans hc'.1,hsp.trans hs'.1,hdp.trans hd'.1⟩

end ASDExplicitGamma.Numerics.Model
