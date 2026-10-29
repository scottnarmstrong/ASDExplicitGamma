module

public import ASDExplicitGamma.Native.GenericSourcePass

/-! The scalar mean part of the generic OLD source producer, transcribed from the source statement.
The scaling theorem is intentionally a distinct-name helper: its
profile hypotheses are the exact inputs supplied by the full-response bank,
the local inverse bank, and the finite source recurrence. -/
@[expose] public section

namespace ASDExplicitGamma.Native

/-- The finite-domain rational majorant `E(2 γ h)`. -/
noncomputable def nativeSourceE (gamma : ℝ) (h : ℕ) : ℝ :=
  (1 - (11 / 10 : ℝ) * (2 * (h : ℝ) * gamma))⁻¹

/-- The entire source function `φ₁(c) = Σ cⁿ/(n+1)!`, including at `c=0`. -/
noncomputable def nativeSourcePhiOne (c : ℝ) : ℝ :=
  ∑' n : ℕ, c ^ n / ((n + 1).factorial : ℝ)

/-- The fixed scalar coefficient in the generic mean recurrence. -/
noncomputable def nativeSourceMeanC : ℝ :=
  2 * nativeSourceK * nativeSourceB128 +
    nativeSourceM * nativeSourceB128 ^ 2

/-- The error term `R_h`. -/
noncomputable def nativeSourceMeanR (h : ℕ) (epsilon x e : ℝ) : ℝ :=
  e * (2 * (h : ℝ) * epsilon +
    (2 * nativeSourceK + 2 * nativeSourceB128 * nativeSourceM) *
      (4 * epsilon + epsilon * x) +
    nativeSourceM * (4 * epsilon ^ 2 + epsilon ^ 2 * x))

/-- The coefficient `L_h`. -/
noncomputable def nativeSourceMeanL (h : ℕ) (epsilon x e : ℝ) : ℝ :=
  e * (2 * (h : ℝ) * nativeSourceB128 + 4 * nativeSourceMeanC) +
    nativeSourceMeanR h epsilon x e

/-- The generic scalar mean producer `G_h`. -/
noncomputable def nativeSourceGenericMean
    (gamma : ℝ) (h : ℕ) (a epsilon x e : ℝ) : ℝ :=
  nativeSourceE gamma h *
    (a * Real.exp (e * nativeSourceMeanC) +
      nativeSourceMeanL h epsilon x e * nativeSourcePhiOne
        (e * nativeSourceMeanC))

/-- The fixed Young parameter in the weak-inverse frame. -/
noncomputable def nativeSourceFrameEta : ℝ := 1 / 1000

/-- The weak-inverse frame cap `F_γ(h,x)`. -/
noncomputable def nativeSourceWeakFrame (gamma : ℝ) (h : ℕ) (x : ℝ) : ℝ :=
  nativeSourceE gamma h *
    ((1 + nativeSourceFrameEta) * x +
      8 * (1 + 1 / nativeSourceFrameEta) *
        ((11 / 10 : ℝ) * gamma * (h : ℝ)) ^ 2)

private theorem native_source_factorial_ge (n : ℕ) :
    (n.factorial : ℝ) ≤ ((n + 1).factorial : ℝ) := by
  exact_mod_cast Nat.factorial_le (Nat.le_succ n)

private theorem native_source_phiOne_summable (c : ℝ) (hc : 0 ≤ c) :
    Summable (fun n : ℕ => c ^ n / ((n + 1).factorial : ℝ)) := by
  have hexp := Real.summable_pow_div_factorial c
  apply Summable.of_nonneg_of_le (fun n => div_nonneg (pow_nonneg hc _) (by positivity))
  intro n
  have hden : 0 < (n.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos n)
  have hden' : 0 < ((n + 1).factorial : ℝ) :=
    Nat.cast_pos.mpr (Nat.factorial_pos (n + 1))
  exact (div_le_div_iff₀ hden' hden).2 (by
    exact mul_le_mul_of_nonneg_left (native_source_factorial_ge n)
      (pow_nonneg hc _))
  exact hexp

/-- `φ₁` is nonnegative on the source's nonnegative scalar range. -/
theorem native_source_phiOne_nonneg (c : ℝ) (hc : 0 ≤ c) :
    0 ≤ nativeSourcePhiOne c := by
  unfold nativeSourcePhiOne
  exact tsum_nonneg fun n => div_nonneg (pow_nonneg hc _) (by positivity)

/-- `φ₁` is increasing on the nonnegative source range. -/
theorem native_source_phiOne_mono {c d : ℝ} (hc : 0 ≤ c) (hcd : c ≤ d) :
    nativeSourcePhiOne c ≤ nativeSourcePhiOne d := by
  unfold nativeSourcePhiOne
  have hcSum := native_source_phiOne_summable c hc
  have hdSum := native_source_phiOne_summable d (hc.trans hcd)
  exact hcSum.tsum_le_tsum (fun n =>
    div_le_div_of_nonneg_right (pow_le_pow_left₀ hc hcd n) (by positivity)) hdSum

theorem native_source_E_le_endpoint (gamma : ℝ) (h : ℕ)
    (hgamma : 0 ≤ gamma) (hgamma0 : gamma ≤ 17 / 50000)
    (hh : h ≤ 1334) :
    nativeSourceE gamma h ≤ nativeSourceE (17 / 50000) h := by
  have hhR : (h : ℝ) ≤ 1334 := by exact_mod_cast hh
  have harg : 2 * (h : ℝ) * gamma ≤ 2 * 1334 * (17 / 50000 : ℝ) := by
    calc
      2 * (h : ℝ) * gamma ≤ (2 * 1334) * gamma := by
        apply mul_le_mul_of_nonneg_right _ hgamma
        nlinarith
      _ ≤ (2 * 1334) * (17 / 50000 : ℝ) :=
        mul_le_mul_of_nonneg_left hgamma0 (by norm_num)
  have hargEndpoint : 2 * (h : ℝ) * (17 / 50000 : ℝ) ≤
      2 * 1334 * (17 / 50000 : ℝ) := by
    exact mul_le_mul_of_nonneg_right (by nlinarith [hhR]) (by norm_num)
  have hdenEndpoint : 0 < 1 - (11 / 10 : ℝ) *
      (2 * (h : ℝ) * (17 / 50000 : ℝ)) := by
    have hglobal : 0 < 1 - (11 / 10 : ℝ) *
        (2 * 1334 * (17 / 50000 : ℝ)) := by norm_num
    nlinarith [hargEndpoint]
  have hdenLe : 1 - (11 / 10 : ℝ) * (2 * (h : ℝ) * (17 / 50000 : ℝ)) ≤
      1 - (11 / 10 : ℝ) * (2 * (h : ℝ) * gamma) := by
    have hargLe : 2 * (h : ℝ) * gamma ≤
        2 * (h : ℝ) * (17 / 50000 : ℝ) :=
      mul_le_mul_of_nonneg_left hgamma0 (by positivity)
    nlinarith [hargLe]
  unfold nativeSourceE
  simpa [one_div] using one_div_le_one_div_of_le hdenEndpoint hdenLe

/-- The finite rational frame factor is positive throughout the declared
source prefix domain. -/
theorem native_source_E_nonneg (gamma : ℝ) (h : ℕ)
    (hgamma : 0 ≤ gamma) (hgamma0 : gamma ≤ 17 / 50000)
    (hh : h ≤ 1334) : 0 ≤ nativeSourceE gamma h := by
  have hhR : (h : ℝ) ≤ 1334 := by exact_mod_cast hh
  have harg : 2 * (h : ℝ) * gamma ≤ 2 * 1334 * (17 / 50000 : ℝ) := by
    calc
      2 * (h : ℝ) * gamma ≤ (2 * 1334) * gamma := by
        apply mul_le_mul_of_nonneg_right _ hgamma
        nlinarith
      _ ≤ (2 * 1334) * (17 / 50000 : ℝ) :=
        mul_le_mul_of_nonneg_left hgamma0 (by norm_num)
  have hden : 0 < 1 - (11 / 10 : ℝ) *
      (2 * 1334 * (17 / 50000 : ℝ)) := by norm_num
  have hdenH : 0 < 1 - (11 / 10 : ℝ) *
      (2 * (h : ℝ) * gamma) := by nlinarith [harg]
  unfold nativeSourceE
  exact inv_nonneg.mpr hdenH.le

private theorem native_source_mean_R_nonneg
    (h : ℕ) (epsilon x e : ℝ)
    (he : 0 ≤ e) (heps : 0 ≤ epsilon) (hx : 0 ≤ x) :
    0 ≤ nativeSourceMeanR h epsilon x e := by
  unfold nativeSourceMeanR
  have hc1 : 0 ≤ 2 * nativeSourceK +
      2 * nativeSourceB128 * nativeSourceM := by
    norm_num [nativeSourceK, nativeSourceB128, nativeSourceM]
  have hc2 : 0 ≤ nativeSourceM := by norm_num [nativeSourceM]
  positivity

private theorem native_source_mean_R_degree
    (h : ℕ) (epsilon x x0 e e0 theta : ℝ)
    (htheta : 0 ≤ theta) (he0 : 0 ≤ e0) (he : e ≤ theta * e0)
    (heps : 0 ≤ epsilon) (hx : 0 ≤ x) (hx0 : 0 ≤ x0)
    (htheta1 : theta ≤ 1) (hxcap : x ≤ theta * x0) :
    nativeSourceMeanR h epsilon x e ≤
      theta * nativeSourceMeanR h epsilon x0 e0 := by
  have hxle : x ≤ x0 := by
    calc
      x ≤ theta * x0 := hxcap
      _ ≤ 1 * x0 := mul_le_mul_of_nonneg_right htheta1 hx0
      _ = x0 := one_mul _
  let B (z : ℝ) := 2 * (h : ℝ) * epsilon +
    (2 * nativeSourceK + 2 * nativeSourceB128 * nativeSourceM) *
      (4 * epsilon + epsilon * z) +
    nativeSourceM * (4 * epsilon ^ 2 + epsilon ^ 2 * z)
  have hBnonneg : 0 ≤ B x := by
    dsimp [B]
    have hc1 : 0 ≤ 2 * nativeSourceK +
        2 * nativeSourceB128 * nativeSourceM := by
      norm_num [nativeSourceK, nativeSourceB128, nativeSourceM]
    have hc2 : 0 ≤ nativeSourceM := by norm_num [nativeSourceM]
    positivity
  have hBmono : B x ≤ B x0 := by
    dsimp [B]
    have hc1 : 0 ≤ 2 * nativeSourceK +
        2 * nativeSourceB128 * nativeSourceM := by
      norm_num [nativeSourceK, nativeSourceB128, nativeSourceM]
    have hc2 : 0 ≤ nativeSourceM := by norm_num [nativeSourceM]
    gcongr
  unfold nativeSourceMeanR
  dsimp [B] at *
  calc
    e * (2 * (h : ℝ) * epsilon +
      (2 * nativeSourceK + 2 * nativeSourceB128 * nativeSourceM) *
        (4 * epsilon + epsilon * x) +
      nativeSourceM * (4 * epsilon ^ 2 + epsilon ^ 2 * x))
        ≤ (theta * e0) * (2 * (h : ℝ) * epsilon +
      (2 * nativeSourceK + 2 * nativeSourceB128 * nativeSourceM) *
        (4 * epsilon + epsilon * x) +
      nativeSourceM * (4 * epsilon ^ 2 + epsilon ^ 2 * x)) :=
      mul_le_mul_of_nonneg_right he hBnonneg
    _ ≤ (theta * e0) * (2 * (h : ℝ) * epsilon +
      (2 * nativeSourceK + 2 * nativeSourceB128 * nativeSourceM) *
        (4 * epsilon + epsilon * x0) +
      nativeSourceM * (4 * epsilon ^ 2 + epsilon ^ 2 * x0)) :=
      mul_le_mul_of_nonneg_left hBmono (mul_nonneg htheta he0)
    _ = theta * (e0 * (2 * (h : ℝ) * epsilon +
      (2 * nativeSourceK + 2 * nativeSourceB128 * nativeSourceM) *
        (4 * epsilon + epsilon * x0) +
      nativeSourceM * (4 * epsilon ^ 2 + epsilon ^ 2 * x0))) := by ring

/-- The scalar generic mean has degree one in γ once its source mean, variance
coefficient, and individual moment cap do. This is the exact formula;
in particular the `ε² x` term and the full `φ₁` series are retained. -/
theorem native_source_generic_mean_degree
    (gamma theta a a0 epsilon x x0 e e0 : ℝ) (h : ℕ)
    (hgamma : 0 ≤ gamma) (hgamma0 : gamma ≤ 17 / 50000)
    (hthetaEq : theta = gamma / (17 / 50000 : ℝ))
    (ha0 : 0 ≤ a0) (haNonneg : 0 ≤ a) (ha : a ≤ theta * a0)
    (heNonneg : 0 ≤ e) (he0 : 0 ≤ e0) (he : e ≤ theta * e0)
    (heps : 0 ≤ epsilon)
    (hx : 0 ≤ x) (hx0 : 0 ≤ x0) (hxcap : x ≤ theta * x0)
    (hh : h ≤ 1334) :
    nativeSourceGenericMean gamma h a epsilon x e ≤
      theta * nativeSourceGenericMean (17 / 50000) h a0 epsilon x0 e0 := by
  have hgammaZeroPos : (0 : ℝ) < 17 / 50000 := by norm_num
  have htheta : 0 ≤ theta := by
    rw [hthetaEq]
    exact div_nonneg hgamma (le_of_lt hgammaZeroPos)
  have htheta1 : theta ≤ 1 := by
    rw [hthetaEq]
    apply (div_le_iff₀ hgammaZeroPos).2
    nlinarith [hgamma0]
  have hE := native_source_E_le_endpoint gamma h hgamma hgamma0 hh
  have hxle : x ≤ x0 := by
    calc
      x ≤ theta * x0 := hxcap
      _ ≤ 1 * x0 := mul_le_mul_of_nonneg_right htheta1 hx0
      _ = x0 := one_mul _
  have heCap0 : e ≤ e0 := by
    calc
      e ≤ theta * e0 := he
      _ ≤ 1 * e0 := mul_le_mul_of_nonneg_right htheta1 he0
      _ = e0 := one_mul _
  have hc : 0 ≤ nativeSourceMeanC := by
    norm_num [nativeSourceMeanC, nativeSourceK, nativeSourceB128, nativeSourceM]
  have harg : 0 ≤ e * nativeSourceMeanC := mul_nonneg heNonneg hc
  have harg0 : 0 ≤ e0 * nativeSourceMeanC := mul_nonneg he0 hc
  have hargLe : e * nativeSourceMeanC ≤ e0 * nativeSourceMeanC :=
    mul_le_mul_of_nonneg_right heCap0 hc
  have hexpLe : Real.exp (e * nativeSourceMeanC) ≤
      Real.exp (e0 * nativeSourceMeanC) := Real.exp_le_exp.mpr hargLe
  have hphiLe := native_source_phiOne_mono harg hargLe
  have hRdegree := native_source_mean_R_degree h epsilon x x0 e e0 theta
    htheta he0 he heps hx hx0 htheta1 hxcap
  have hbaseCoeff : 0 ≤ 2 * (h : ℝ) * nativeSourceB128 +
      4 * nativeSourceMeanC := by
    have hb : 0 ≤ nativeSourceB128 := by norm_num [nativeSourceB128]
    have hc : 0 ≤ nativeSourceMeanC := by
      norm_num [nativeSourceMeanC, nativeSourceK, nativeSourceB128, nativeSourceM]
    positivity
  have hbaseDegree : e * (2 * (h : ℝ) * nativeSourceB128 +
      4 * nativeSourceMeanC) ≤ theta *
      (e0 * (2 * (h : ℝ) * nativeSourceB128 +
        4 * nativeSourceMeanC)) := by
    calc
      _ ≤ theta * e0 * (2 * (h : ℝ) * nativeSourceB128 +
          4 * nativeSourceMeanC) :=
        mul_le_mul_of_nonneg_right he hbaseCoeff
      _ = _ := by ring
  have hLdegree : nativeSourceMeanL h epsilon x e ≤
      theta * nativeSourceMeanL h epsilon x0 e0 := by
    unfold nativeSourceMeanL
    calc
      _ ≤ theta * (e0 * (2 * (h : ℝ) * nativeSourceB128 +
          4 * nativeSourceMeanC)) +
            theta * nativeSourceMeanR h epsilon x0 e0 :=
        add_le_add hbaseDegree hRdegree
      _ = theta * (e0 * (2 * (h : ℝ) * nativeSourceB128 +
          4 * nativeSourceMeanC) +
            nativeSourceMeanR h epsilon x0 e0) := by ring
  have hLnonneg : 0 ≤ nativeSourceMeanL h epsilon x e := by
    unfold nativeSourceMeanL
    exact add_nonneg (mul_nonneg heNonneg hbaseCoeff)
      (native_source_mean_R_nonneg h epsilon x e heNonneg heps hx)
  have hL0nonneg : 0 ≤ nativeSourceMeanL h epsilon x0 e0 := by
    unfold nativeSourceMeanL
    exact add_nonneg (mul_nonneg he0 hbaseCoeff)
      (native_source_mean_R_nonneg h epsilon x0 e0 he0 heps hx0)
  have hfirst : a * Real.exp (e * nativeSourceMeanC) ≤
      theta * (a0 * Real.exp (e0 * nativeSourceMeanC)) := by
    calc
      _ ≤ (theta * a0) * Real.exp (e * nativeSourceMeanC) :=
        mul_le_mul_of_nonneg_right ha (le_of_lt (Real.exp_pos _))
      _ ≤ (theta * a0) * Real.exp (e0 * nativeSourceMeanC) :=
        mul_le_mul_of_nonneg_left hexpLe (mul_nonneg htheta ha0)
      _ = _ := by ring
  have hsecond : nativeSourceMeanL h epsilon x e *
      nativeSourcePhiOne (e * nativeSourceMeanC) ≤
      theta * (nativeSourceMeanL h epsilon x0 e0 *
        nativeSourcePhiOne (e0 * nativeSourceMeanC)) := by
    calc
      _ ≤ (theta * nativeSourceMeanL h epsilon x0 e0) *
          nativeSourcePhiOne (e * nativeSourceMeanC) :=
        mul_le_mul_of_nonneg_right hLdegree (native_source_phiOne_nonneg _ harg)
      _ ≤ (theta * nativeSourceMeanL h epsilon x0 e0) *
          nativeSourcePhiOne (e0 * nativeSourceMeanC) :=
        mul_le_mul_of_nonneg_left hphiLe (mul_nonneg htheta hL0nonneg)
      _ = _ := by ring
  have hsum0 : 0 ≤ a0 * Real.exp (e0 * nativeSourceMeanC) +
      nativeSourceMeanL h epsilon x0 e0 *
        nativeSourcePhiOne (e0 * nativeSourceMeanC) := by
    exact add_nonneg (mul_nonneg ha0 (le_of_lt (Real.exp_pos _)))
      (mul_nonneg hL0nonneg (native_source_phiOne_nonneg _ harg0))
  have hsum : a * Real.exp (e * nativeSourceMeanC) +
      nativeSourceMeanL h epsilon x e *
        nativeSourcePhiOne (e * nativeSourceMeanC) ≤
      theta * (a0 * Real.exp (e0 * nativeSourceMeanC) +
        nativeSourceMeanL h epsilon x0 e0 *
          nativeSourcePhiOne (e0 * nativeSourceMeanC)) := by
    calc
      _ ≤ theta * (a0 * Real.exp (e0 * nativeSourceMeanC)) +
          theta * (nativeSourceMeanL h epsilon x0 e0 *
            nativeSourcePhiOne (e0 * nativeSourceMeanC)) := add_le_add hfirst hsecond
      _ = _ := by ring
  unfold nativeSourceGenericMean
  calc
    _ ≤ nativeSourceE (17 / 50000) h *
        (a * Real.exp (e * nativeSourceMeanC) +
          nativeSourceMeanL h epsilon x e *
            nativeSourcePhiOne (e * nativeSourceMeanC)) :=
      mul_le_mul_of_nonneg_right hE (by
        exact add_nonneg (mul_nonneg haNonneg
          (le_of_lt (Real.exp_pos _))) (mul_nonneg hLnonneg
          (native_source_phiOne_nonneg _ harg)))
    _ ≤ nativeSourceE (17 / 50000) h *
        (theta * (a0 * Real.exp (e0 * nativeSourceMeanC) +
          nativeSourceMeanL h epsilon x0 e0 *
            nativeSourcePhiOne (e0 * nativeSourceMeanC))) :=
      mul_le_mul_of_nonneg_left hsum (by
        unfold nativeSourceE
        have hhR : (h : ℝ) ≤ 1334 := by exact_mod_cast hh
        have hargEnd : 2 * (h : ℝ) * (17 / 50000 : ℝ) ≤
            2 * 1334 * (17 / 50000 : ℝ) := by
          exact mul_le_mul_of_nonneg_right (by nlinarith [hhR]) (by norm_num)
        have hden : 0 < 1 - (11 / 10 : ℝ) *
            (2 * 1334 * (17 / 50000 : ℝ)) := by norm_num
        have hdenH : 0 < 1 - (11 / 10 : ℝ) *
            (2 * (h : ℝ) * (17 / 50000 : ℝ)) := by nlinarith [hargEnd]
        have hpos : 0 < (1 - (11 / 10 : ℝ) *
            (2 * (h : ℝ) * (17 / 50000 : ℝ)))⁻¹ := inv_pos.mpr hdenH
        exact hpos.le)
    _ = theta * (nativeSourceE (17 / 50000) h *
        (a0 * Real.exp (e0 * nativeSourceMeanC) +
          nativeSourceMeanL h epsilon x0 e0 *
            nativeSourcePhiOne (e0 * nativeSourceMeanC))) := by ring

/-- Nonnegativity of the exact scalar generic-mean producer on its finite
rational domain. -/
theorem native_source_generic_mean_nonneg
    (gamma : ℝ) (h : ℕ) (a epsilon x e : ℝ)
    (hgamma : 0 ≤ gamma) (hgamma0 : gamma ≤ 17 / 50000)
    (ha : 0 ≤ a) (heps : 0 ≤ epsilon) (hx : 0 ≤ x) (he : 0 ≤ e)
    (hh : h ≤ 1334) :
    0 ≤ nativeSourceGenericMean gamma h a epsilon x e := by
  have hE := native_source_E_nonneg gamma h hgamma hgamma0 hh
  have hc : 0 ≤ nativeSourceMeanC := by
    norm_num [nativeSourceMeanC, nativeSourceK, nativeSourceB128, nativeSourceM]
  have hb : 0 ≤ nativeSourceB128 := by norm_num [nativeSourceB128]
  have hcoeff : 0 ≤ 2 * (h : ℝ) * nativeSourceB128 +
      4 * nativeSourceMeanC := by
    exact add_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) hb)
      (mul_nonneg (by norm_num) hc)
  have hR := native_source_mean_R_nonneg h epsilon x e he heps hx
  have hL : 0 ≤ nativeSourceMeanL h epsilon x e := by
    unfold nativeSourceMeanL
    exact add_nonneg (mul_nonneg he hcoeff) hR
  have harg : 0 ≤ e * nativeSourceMeanC := mul_nonneg he hc
  have hphi := native_source_phiOne_nonneg (e * nativeSourceMeanC) harg
  unfold nativeSourceGenericMean
  exact mul_nonneg hE (add_nonneg
    (mul_nonneg ha (le_of_lt (Real.exp_pos _)))
    (mul_nonneg hL hphi))

/-- The exact Young-frame weak-inverse envelope has degree one when its
input moment cap does.  The quadratic frame correction has degree two and is
therefore bounded by degree one on `0≤θ≤1`. -/
theorem native_source_weak_frame_degree
    (gamma theta x x0 : ℝ) (h : ℕ)
    (hgamma : 0 ≤ gamma) (hgamma0 : gamma ≤ 17 / 50000)
    (hthetaEq : theta = gamma / (17 / 50000 : ℝ))
    (hx : 0 ≤ x) (hxcap : x ≤ theta * x0)
    (hh : h ≤ 1334) :
    nativeSourceWeakFrame gamma h x ≤
      theta * nativeSourceWeakFrame (17 / 50000) h x0 := by
  have hgammaZeroPos : (0 : ℝ) < 17 / 50000 := by norm_num
  have htheta : 0 ≤ theta := by
    rw [hthetaEq]
    exact div_nonneg hgamma (le_of_lt hgammaZeroPos)
  have htheta1 : theta ≤ 1 := by
    rw [hthetaEq]
    apply (div_le_iff₀ hgammaZeroPos).2
    nlinarith [hgamma0]
  have hE := native_source_E_le_endpoint gamma h hgamma hgamma0 hh
  have hgammaScaled : gamma = theta * (17 / 50000 : ℝ) := by
    rw [hthetaEq]
    field_simp
  have hthetaSq : theta ^ 2 ≤ theta := by
    nlinarith [mul_nonneg htheta (sub_nonneg.mpr htheta1)]
  have hframeScale :
      ((11 / 10 : ℝ) * gamma * (h : ℝ)) ^ 2 ≤
        theta * ((11 / 10 : ℝ) * (17 / 50000 : ℝ) * (h : ℝ)) ^ 2 := by
    rw [hgammaScaled]
    have heq :
        ((11 / 10 : ℝ) * (theta * (17 / 50000 : ℝ)) * (h : ℝ)) ^ 2 =
          theta ^ 2 * ((11 / 10 : ℝ) * (17 / 50000 : ℝ) * (h : ℝ)) ^ 2 := by ring
    rw [heq]
    exact mul_le_mul_of_nonneg_right hthetaSq (sq_nonneg _)
  have hlinearCoeff : 0 ≤ 1 + nativeSourceFrameEta := by
    norm_num [nativeSourceFrameEta]
  have hquadCoeff : 0 ≤ 8 * (1 + 1 / nativeSourceFrameEta) := by
    norm_num [nativeSourceFrameEta]
  have hbracket :
      (1 + nativeSourceFrameEta) * x +
          8 * (1 + 1 / nativeSourceFrameEta) *
            ((11 / 10 : ℝ) * gamma * (h : ℝ)) ^ 2 ≤
        theta * ((1 + nativeSourceFrameEta) * x0 +
          8 * (1 + 1 / nativeSourceFrameEta) *
            ((11 / 10 : ℝ) * (17 / 50000 : ℝ) * (h : ℝ)) ^ 2) := by
    calc
      _ ≤ (1 + nativeSourceFrameEta) * (theta * x0) +
          8 * (1 + 1 / nativeSourceFrameEta) *
            (theta * ((11 / 10 : ℝ) * (17 / 50000 : ℝ) * (h : ℝ)) ^ 2) :=
        add_le_add
          (mul_le_mul_of_nonneg_left hxcap hlinearCoeff)
          (mul_le_mul_of_nonneg_left hframeScale hquadCoeff)
      _ = _ := by ring
  have hbracketNonneg : 0 ≤
      (1 + nativeSourceFrameEta) * x +
        8 * (1 + 1 / nativeSourceFrameEta) *
          ((11 / 10 : ℝ) * gamma * (h : ℝ)) ^ 2 := by
    positivity [nativeSourceFrameEta]
  have hhR : (h : ℝ) ≤ 1334 := by exact_mod_cast hh
  have hargEnd : 2 * (h : ℝ) * (17 / 50000 : ℝ) ≤
      2 * 1334 * (17 / 50000 : ℝ) := by
    exact mul_le_mul_of_nonneg_right (by nlinarith [hhR]) (by norm_num)
  have hden : 0 < 1 - (11 / 10 : ℝ) *
      (2 * 1334 * (17 / 50000 : ℝ)) := by norm_num
  have hdenH : 0 < 1 - (11 / 10 : ℝ) *
      (2 * (h : ℝ) * (17 / 50000 : ℝ)) := by nlinarith [hargEnd]
  have hE0 : 0 ≤ nativeSourceE (17 / 50000) h := by
    unfold nativeSourceE
    exact inv_nonneg.mpr hdenH.le
  unfold nativeSourceWeakFrame
  calc
    _ ≤ nativeSourceE (17 / 50000) h *
        ((1 + nativeSourceFrameEta) * x +
          8 * (1 + 1 / nativeSourceFrameEta) *
            ((11 / 10 : ℝ) * gamma * (h : ℝ)) ^ 2) :=
      mul_le_mul_of_nonneg_right hE hbracketNonneg
    _ ≤ nativeSourceE (17 / 50000) h *
        (theta * ((1 + nativeSourceFrameEta) * x0 +
          8 * (1 + 1 / nativeSourceFrameEta) *
            ((11 / 10 : ℝ) * (17 / 50000 : ℝ) * (h : ℝ)) ^ 2)) :=
      mul_le_mul_of_nonneg_left hbracket hE0
    _ = theta * (nativeSourceE (17 / 50000) h *
        ((1 + nativeSourceFrameEta) * x0 +
          8 * (1 + 1 / nativeSourceFrameEta) *
            ((11 / 10 : ℝ) * (17 / 50000 : ℝ) * (h : ℝ)) ^ 2)) := by ring

end ASDExplicitGamma.Native
