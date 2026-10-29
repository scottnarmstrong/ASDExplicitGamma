module

public import ASDExplicitGamma.Model.BflatModeTransforms

/-! # Exact variances of the actual B-flat square modes -/

@[expose] public section

open MeasureTheory Set

namespace ASDExplicitGamma.Model

private noncomputable def bflatSineWeight (k : ℕ) : C(ℝ, ℝ) :=
  ⟨fun x => Real.sin (Real.pi * ((k+1:ℕ):ℝ) * (x+1/2)), by fun_prop⟩

private noncomputable def bflatCosineWeight (k : ℕ) : C(ℝ, ℝ) :=
  ⟨fun x => Real.cos (Real.pi * ((k+1:ℕ):ℝ) * (x+1/2)), by fun_prop⟩

theorem bflatQ3ModeLength_pos (j : ℕ) :
    0 < (ASDExplicitGamma.Numerics.Model.q3ModeLength j : ℝ) := by
  have h : (0 : ℚ) < (3:ℚ)^j := pow_pos (by norm_num : (0:ℚ) < 3) j
  rw [ASDExplicitGamma.Numerics.Model.q3ModeLength]
  exact_mod_cast (one_div_pos.mpr h)

/-- The first actual observation has the sine/cosine q3 mode product. -/
theorem bflatModeSeriesVariance_zero_eq_q3Modes {ι : Type*} [Countable ι]
    (e : HilbertBasis ι ℝ Gaussian.WhiteNoise) (j m n : ℕ) :
    bflatModeSeriesVariance e 0 m n 1
        ⟨(ASDExplicitGamma.Numerics.Model.q3ModeLength j : ℝ), by
          have h : (0:ℚ) < (3:ℚ)^j := pow_pos (by norm_num : (0:ℚ)<3) j
          rw [ASDExplicitGamma.Numerics.Model.q3ModeLength]
          exact_mod_cast (one_div_pos.mpr h)⟩ =
      (((n+1:ℕ):ℝ)^2 /
        (((m+1:ℕ):ℝ)^2+((n+1:ℕ):ℝ)^2)) *
        ASDExplicitGamma.Numerics.Model.q3ModeSine j m *
        ASDExplicitGamma.Numerics.Model.q3ModeCosine j n := by
  let ell : ℝ := (ASDExplicitGamma.Numerics.Model.q3ModeLength j : ℝ)
  let L : {l : ℝ // 0 < l} := ⟨ell, bflatQ3ModeLength_pos j⟩
  let s := bflatSineWeight m
  let c := bflatCosineWeight n
  let a : ℝ := 2*Real.pi*((n+1:ℕ):ℝ)/
    Real.sqrt (Real.pi^2*(((m+1:ℕ):ℝ)^2+((n+1:ℕ):ℝ)^2))
  have hL : L.1 = (ASDExplicitGamma.Numerics.Model.q3ModeLength j : ℝ) := rfl
  have hweight (x : bflatClosedRectangle) :
      bflatModeObservationWeight 0 m n x = a*(s (x.1 0)*c (x.1 1)) := by
    rw [bflatModeObservationWeight_zero_apply]
    dsimp [a,s,c,bflatSineWeight,bflatCosineWeight]
  calc
    _ = ∫ p : bflatClosedRectangle × bflatClosedRectangle,
          ASDExplicitGamma.q3Cov ((p.1.1 0-p.2.1 0)/L.1) *
            ASDExplicitGamma.q3Cov ((p.1.1 1-p.2.1 1)/L.1) *
            bflatModeObservationWeight 0 m n p.1 *
            bflatModeObservationWeight 0 m n p.2
          ∂((volume : Measure bflatClosedRectangle).prod volume) := by
      rw [bflatModeSeriesVariance_eq_covariance_integral]
      simp [L, ell]
    _ = ∫ p : bflatClosedRectangle × bflatClosedRectangle,
          (a^2) *
            (ASDExplicitGamma.q3Cov ((p.1.1 0-p.2.1 0)/L.1) * s (p.1.1 0) * s (p.2.1 0)) *
            (ASDExplicitGamma.q3Cov ((p.1.1 1-p.2.1 1)/L.1) * c (p.1.1 1) * c (p.2.1 1))
          ∂((volume : Measure bflatClosedRectangle).prod volume) := by
      apply integral_congr_ae
      filter_upwards with p
      rw [hweight, hweight]
      ring
    _ = a^2 *
        ((∫ x in Icc (-1/2:ℝ) (1/2), ∫ y in Icc (-1/2:ℝ) (1/2),
          ASDExplicitGamma.q3Cov ((x-y)/L.1)*s x*s y) *
        (∫ x in Icc (-1/2:ℝ) (1/2), ∫ y in Icc (-1/2:ℝ) (1/2),
          ASDExplicitGamma.q3Cov ((x-y)/L.1)*c x*c y)) := by
      calc
        _ = (∫ p : bflatClosedRectangle × bflatClosedRectangle,
              ASDExplicitGamma.q3Cov ((p.1.1 0-p.2.1 0)/L.1) * s (p.1.1 0) * s (p.2.1 0) *
                (ASDExplicitGamma.q3Cov ((p.1.1 1-p.2.1 1)/L.1) * c (p.1.1 1) * c (p.2.1 1))
              ∂((volume : Measure bflatClosedRectangle).prod volume)) * a^2 := by
          calc
            _ = ∫ p : bflatClosedRectangle × bflatClosedRectangle,
                  (ASDExplicitGamma.q3Cov ((p.1.1 0-p.2.1 0)/L.1) * s (p.1.1 0) * s (p.2.1 0) *
                    (ASDExplicitGamma.q3Cov ((p.1.1 1-p.2.1 1)/L.1) * c (p.1.1 1) * c (p.2.1 1)))*a^2
                  ∂((volume : Measure bflatClosedRectangle).prod volume) := by
              apply integral_congr_ae
              filter_upwards with p
              ring
            _ = _ := by rw [integral_mul_const]
        _ = a^2 *
            ((∫ x in Icc (-1/2:ℝ) (1/2), ∫ y in Icc (-1/2:ℝ) (1/2),
              ASDExplicitGamma.q3Cov ((x-y)/L.1)*s x*s y) *
            (∫ x in Icc (-1/2:ℝ) (1/2), ∫ y in Icc (-1/2:ℝ) (1/2),
              ASDExplicitGamma.q3Cov ((x-y)/L.1)*c x*c y)) := by
          rw [bflatProductCovariance_factorization]
          ring
    _ = a^2 *
        (ASDExplicitGamma.Numerics.Model.q3ModeSine j m / 2) *
        (ASDExplicitGamma.Numerics.Model.q3ModeCosine j n / 2) := by
      dsimp [s,c,bflatSineWeight,bflatCosineWeight,L,ell]
      rw [bflatQ3SineModeIntegral_eq_q3Mode, bflatQ3CosineModeIntegral_eq_q3Mode]
      ring
    _ = _ := by
      have hm : 0 < ((m+1:ℕ):ℝ) := by exact_mod_cast Nat.succ_pos m
      have hn : 0 < ((n+1:ℕ):ℝ) := by exact_mod_cast Nat.succ_pos n
      have hd : 0 < ((m+1:ℕ):ℝ)^2+((n+1:ℕ):ℝ)^2 :=
        add_pos (sq_pos_of_pos hm) (sq_pos_of_pos hn)
      have ha : a^2/4 = ((n+1:ℕ):ℝ)^2 /
          (((m+1:ℕ):ℝ)^2+((n+1:ℕ):ℝ)^2) := by
        dsimp [a]
        rw [div_pow, Real.sq_sqrt (by positivity : 0 ≤ Real.pi^2 *
          (((m+1:ℕ):ℝ)^2+((n+1:ℕ):ℝ)^2))]
        field_simp [ne_of_gt hd, ne_of_gt Real.pi_pos]
        ring
      calc
        _ = (a^2/4) * ASDExplicitGamma.Numerics.Model.q3ModeSine j m *
            ASDExplicitGamma.Numerics.Model.q3ModeCosine j n := by ring
        _ = _ := by rw [ha]

/-- The second actual observation has the cosine/sine q3 mode product. -/
theorem bflatModeSeriesVariance_one_eq_q3Modes {ι : Type*} [Countable ι]
    (e : HilbertBasis ι ℝ Gaussian.WhiteNoise) (j m n : ℕ) :
    bflatModeSeriesVariance e 1 m n 1
        ⟨(ASDExplicitGamma.Numerics.Model.q3ModeLength j : ℝ), by
          have h : (0:ℚ) < (3:ℚ)^j := pow_pos (by norm_num : (0:ℚ)<3) j
          rw [ASDExplicitGamma.Numerics.Model.q3ModeLength]
          exact_mod_cast (one_div_pos.mpr h)⟩ =
      (((m+1:ℕ):ℝ)^2 /
        (((m+1:ℕ):ℝ)^2+((n+1:ℕ):ℝ)^2)) *
        ASDExplicitGamma.Numerics.Model.q3ModeCosine j m *
        ASDExplicitGamma.Numerics.Model.q3ModeSine j n := by
  let ell : ℝ := (ASDExplicitGamma.Numerics.Model.q3ModeLength j : ℝ)
  let L : {l : ℝ // 0 < l} := ⟨ell, bflatQ3ModeLength_pos j⟩
  let c := bflatCosineWeight m
  let s := bflatSineWeight n
  let a : ℝ := -(2*Real.pi*((m+1:ℕ):ℝ)/
    Real.sqrt (Real.pi^2*(((m+1:ℕ):ℝ)^2+((n+1:ℕ):ℝ)^2)))
  have hweight (x : bflatClosedRectangle) :
      bflatModeObservationWeight 1 m n x = a*(c (x.1 0)*s (x.1 1)) := by
    rw [bflatModeObservationWeight_one_apply]
    dsimp [a,c,s,bflatCosineWeight,bflatSineWeight]
  calc
    _ = ∫ p : bflatClosedRectangle × bflatClosedRectangle,
          ASDExplicitGamma.q3Cov ((p.1.1 0-p.2.1 0)/L.1) *
            ASDExplicitGamma.q3Cov ((p.1.1 1-p.2.1 1)/L.1) *
            bflatModeObservationWeight 1 m n p.1 *
            bflatModeObservationWeight 1 m n p.2
          ∂((volume : Measure bflatClosedRectangle).prod volume) := by
      rw [bflatModeSeriesVariance_eq_covariance_integral]
      simp [L, ell]
    _ = ∫ p : bflatClosedRectangle × bflatClosedRectangle,
          (a^2) *
            (ASDExplicitGamma.q3Cov ((p.1.1 0-p.2.1 0)/L.1) * c (p.1.1 0) * c (p.2.1 0)) *
            (ASDExplicitGamma.q3Cov ((p.1.1 1-p.2.1 1)/L.1) * s (p.1.1 1) * s (p.2.1 1))
          ∂((volume : Measure bflatClosedRectangle).prod volume) := by
      apply integral_congr_ae
      filter_upwards with p
      rw [hweight, hweight]
      ring
    _ = a^2 *
        ((∫ x in Icc (-1/2:ℝ) (1/2), ∫ y in Icc (-1/2:ℝ) (1/2),
          ASDExplicitGamma.q3Cov ((x-y)/L.1)*c x*c y) *
        (∫ x in Icc (-1/2:ℝ) (1/2), ∫ y in Icc (-1/2:ℝ) (1/2),
          ASDExplicitGamma.q3Cov ((x-y)/L.1)*s x*s y)) := by
      calc
        _ = (∫ p : bflatClosedRectangle × bflatClosedRectangle,
              ASDExplicitGamma.q3Cov ((p.1.1 0-p.2.1 0)/L.1) * c (p.1.1 0) * c (p.2.1 0) *
                (ASDExplicitGamma.q3Cov ((p.1.1 1-p.2.1 1)/L.1) * s (p.1.1 1) * s (p.2.1 1))
              ∂((volume : Measure bflatClosedRectangle).prod volume)) * a^2 := by
          calc
            _ = ∫ p : bflatClosedRectangle × bflatClosedRectangle,
                  (ASDExplicitGamma.q3Cov ((p.1.1 0-p.2.1 0)/L.1) * c (p.1.1 0) * c (p.2.1 0) *
                    (ASDExplicitGamma.q3Cov ((p.1.1 1-p.2.1 1)/L.1) * s (p.1.1 1) * s (p.2.1 1)))*a^2
                  ∂((volume : Measure bflatClosedRectangle).prod volume) := by
              apply integral_congr_ae
              filter_upwards with p
              ring
            _ = _ := by rw [integral_mul_const]
        _ = a^2 *
            ((∫ x in Icc (-1/2:ℝ) (1/2), ∫ y in Icc (-1/2:ℝ) (1/2),
              ASDExplicitGamma.q3Cov ((x-y)/L.1)*c x*c y) *
            (∫ x in Icc (-1/2:ℝ) (1/2), ∫ y in Icc (-1/2:ℝ) (1/2),
              ASDExplicitGamma.q3Cov ((x-y)/L.1)*s x*s y)) := by
          rw [bflatProductCovariance_factorization]
          ring
    _ = a^2 *
        (ASDExplicitGamma.Numerics.Model.q3ModeCosine j m / 2) *
        (ASDExplicitGamma.Numerics.Model.q3ModeSine j n / 2) := by
      dsimp [s,c,bflatSineWeight,bflatCosineWeight,L,ell]
      rw [bflatQ3CosineModeIntegral_eq_q3Mode, bflatQ3SineModeIntegral_eq_q3Mode]
      ring
    _ = _ := by
      have hm : 0 < ((m+1:ℕ):ℝ) := by exact_mod_cast Nat.succ_pos m
      have hn : 0 < ((n+1:ℕ):ℝ) := by exact_mod_cast Nat.succ_pos n
      have hd : 0 < ((m+1:ℕ):ℝ)^2+((n+1:ℕ):ℝ)^2 :=
        add_pos (sq_pos_of_pos hm) (sq_pos_of_pos hn)
      have ha : a^2/4 = ((m+1:ℕ):ℝ)^2 /
          (((m+1:ℕ):ℝ)^2+((n+1:ℕ):ℝ)^2) := by
        dsimp [a]
        rw [neg_sq, div_pow, Real.sq_sqrt (by positivity : 0 ≤ Real.pi^2 *
          (((m+1:ℕ):ℝ)^2+((n+1:ℕ):ℝ)^2))]
        field_simp [ne_of_gt hd, ne_of_gt Real.pi_pos]
        ring
      calc
        _ = (a^2/4) * ASDExplicitGamma.Numerics.Model.q3ModeCosine j m *
            ASDExplicitGamma.Numerics.Model.q3ModeSine j n := by ring
        _ = _ := by rw [ha]

/-- Changing the q3 shell amplitude scales every actual modal variance by its
point variance. -/
theorem bflatModeSeriesVariance_scale {ι : Type*} [Countable ι]
    (e : HilbertBasis ι ℝ Gaussian.WhiteNoise) (i : Fin 2) (m n : ℕ)
    (β : ℝ) (L : {l : ℝ // 0 < l}) :
    bflatModeSeriesVariance e i m n β L =
      β^2 * bflatModeSeriesVariance e i m n 1 L := by
  rw [bflatModeSeriesVariance_eq_covariance_integral,
    bflatModeSeriesVariance_eq_covariance_integral]
  simp only [one_pow, one_mul]
  calc
    _ = ∫ p : bflatClosedRectangle × bflatClosedRectangle,
        β^2 * (ASDExplicitGamma.q3Cov ((p.1.1 0-p.2.1 0)/L.1) *
          ASDExplicitGamma.q3Cov ((p.1.1 1-p.2.1 1)/L.1) *
          bflatModeObservationWeight i m n p.1 *
          bflatModeObservationWeight i m n p.2)
        ∂((volume : Measure bflatClosedRectangle).prod volume) := by
      apply integral_congr_ae
      filter_upwards with p
      ring
    _ = β^2 * ∫ p : bflatClosedRectangle × bflatClosedRectangle,
        ASDExplicitGamma.q3Cov ((p.1.1 0-p.2.1 0)/L.1) *
          ASDExplicitGamma.q3Cov ((p.1.1 1-p.2.1 1)/L.1) *
          bflatModeObservationWeight i m n p.1 *
          bflatModeObservationWeight i m n p.2
        ∂((volume : Measure bflatClosedRectangle).prod volume) := by
      rw [integral_const_mul]

/-- The two actual observations over a symmetric mode rectangle sum exactly to
the finite source projection in `q3Projection`. -/
theorem bflatModeSeriesVariance_finite_sum_eq_q3Projection {ι : Type*} [Countable ι]
    (e : HilbertBasis ι ℝ Gaussian.WhiteNoise) (j N : ℕ) :
    (∑ m ∈ Finset.range N, ∑ n ∈ Finset.range N,
      (bflatModeSeriesVariance e 0 m n 1
          ⟨(ASDExplicitGamma.Numerics.Model.q3ModeLength j : ℝ), by
            have h : (0:ℚ) < (3:ℚ)^j := pow_pos (by norm_num : (0:ℚ)<3) j
            rw [ASDExplicitGamma.Numerics.Model.q3ModeLength]
            exact_mod_cast (one_div_pos.mpr h)⟩ +
      bflatModeSeriesVariance e 1 m n 1
          ⟨(ASDExplicitGamma.Numerics.Model.q3ModeLength j : ℝ), by
            have h : (0:ℚ) < (3:ℚ)^j := pow_pos (by norm_num : (0:ℚ)<3) j
            rw [ASDExplicitGamma.Numerics.Model.q3ModeLength]
            exact_mod_cast (one_div_pos.mpr h)⟩)) =
      ASDExplicitGamma.Numerics.Model.q3Projection j N := by
  have hswap :
      (∑ m ∈ Finset.range N, ∑ n ∈ Finset.range N,
        (((n+1:ℕ):ℝ)^2 /
          (((m+1:ℕ):ℝ)^2+((n+1:ℕ):ℝ)^2)) *
          ASDExplicitGamma.Numerics.Model.q3ModeSine j m *
          ASDExplicitGamma.Numerics.Model.q3ModeCosine j n) =
      ∑ m ∈ Finset.range N, ∑ n ∈ Finset.range N,
        (((m+1:ℕ):ℝ)^2 /
          (((m+1:ℕ):ℝ)^2+((n+1:ℕ):ℝ)^2)) *
          ASDExplicitGamma.Numerics.Model.q3ModeCosine j m *
          ASDExplicitGamma.Numerics.Model.q3ModeSine j n := by
    calc
      _ = ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
          (((n+1:ℕ):ℝ)^2 /
            (((m+1:ℕ):ℝ)^2+((n+1:ℕ):ℝ)^2)) *
            ASDExplicitGamma.Numerics.Model.q3ModeSine j m *
            ASDExplicitGamma.Numerics.Model.q3ModeCosine j n := by
        rw [Finset.sum_comm]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro n hn
        apply Finset.sum_congr rfl
        intro m hm
        ring
  simp_rw [bflatModeSeriesVariance_zero_eq_q3Modes (e := e) (j := j),
    bflatModeSeriesVariance_one_eq_q3Modes (e := e) (j := j)]
  simp_rw [Finset.sum_add_distrib]
  unfold ASDExplicitGamma.Numerics.Model.q3Projection
  rw [hswap]
  ring

/-- The finite product-q3 modal projection at amplitude β is its unit-amplitude
projection multiplied by the point variance β². -/
theorem bflatModeSeriesVariance_finite_sum_eq_q3Projection_scaled
    {ι : Type*} [Countable ι]
    (e : HilbertBasis ι ℝ Gaussian.WhiteNoise) (j N : ℕ) (β : ℝ) :
    (∑ m ∈ Finset.range N, ∑ n ∈ Finset.range N,
      (bflatModeSeriesVariance e 0 m n β
          ⟨(ASDExplicitGamma.Numerics.Model.q3ModeLength j : ℝ), bflatQ3ModeLength_pos j⟩ +
        bflatModeSeriesVariance e 1 m n β
          ⟨(ASDExplicitGamma.Numerics.Model.q3ModeLength j : ℝ), bflatQ3ModeLength_pos j⟩)) =
      β^2 * ASDExplicitGamma.Numerics.Model.q3Projection j N := by
  let L : {l : ℝ // 0 < l} :=
    ⟨(ASDExplicitGamma.Numerics.Model.q3ModeLength j : ℝ), bflatQ3ModeLength_pos j⟩
  have h0 :
      (∑ m ∈ Finset.range N, ∑ n ∈ Finset.range N,
        bflatModeSeriesVariance e 0 m n β L) =
      β^2 * (∑ m ∈ Finset.range N, ∑ n ∈ Finset.range N,
        bflatModeSeriesVariance e 0 m n 1 L) := by
    calc
      _ = ∑ m ∈ Finset.range N, ∑ n ∈ Finset.range N,
          β^2 * bflatModeSeriesVariance e 0 m n 1 L := by
        apply Finset.sum_congr rfl
        intro m hm
        apply Finset.sum_congr rfl
        intro n hn
        exact bflatModeSeriesVariance_scale e 0 m n β L
      _ = ∑ m ∈ Finset.range N, β^2 *
          (∑ n ∈ Finset.range N, bflatModeSeriesVariance e 0 m n 1 L) := by
        apply Finset.sum_congr rfl
        intro m hm
        rw [Finset.mul_sum]
      _ = _ := by rw [Finset.mul_sum]
  have h1 :
      (∑ m ∈ Finset.range N, ∑ n ∈ Finset.range N,
        bflatModeSeriesVariance e 1 m n β L) =
      β^2 * (∑ m ∈ Finset.range N, ∑ n ∈ Finset.range N,
        bflatModeSeriesVariance e 1 m n 1 L) := by
    calc
      _ = ∑ m ∈ Finset.range N, ∑ n ∈ Finset.range N,
          β^2 * bflatModeSeriesVariance e 1 m n 1 L := by
        apply Finset.sum_congr rfl
        intro m hm
        apply Finset.sum_congr rfl
        intro n hn
        exact bflatModeSeriesVariance_scale e 1 m n β L
      _ = ∑ m ∈ Finset.range N, β^2 *
          (∑ n ∈ Finset.range N, bflatModeSeriesVariance e 1 m n 1 L) := by
        apply Finset.sum_congr rfl
        intro m hm
        rw [Finset.mul_sum]
      _ = _ := by rw [Finset.mul_sum]
  have hbase := bflatModeSeriesVariance_finite_sum_eq_q3Projection
    (e := e) (j := j) (N := N)
  have hbase' :
      (∑ m ∈ Finset.range N, ∑ n ∈ Finset.range N,
        bflatModeSeriesVariance e 0 m n 1 L) +
      (∑ m ∈ Finset.range N, ∑ n ∈ Finset.range N,
        bflatModeSeriesVariance e 1 m n 1 L) =
      ASDExplicitGamma.Numerics.Model.q3Projection j N := by
    simpa only [Finset.sum_add_distrib, ← Finset.sum_product',
      ← Finset.sum_product'] using hbase
  calc
    _ = (∑ m ∈ Finset.range N, ∑ n ∈ Finset.range N,
          bflatModeSeriesVariance e 0 m n β L) +
        (∑ m ∈ Finset.range N, ∑ n ∈ Finset.range N,
          bflatModeSeriesVariance e 1 m n β L) := by
      simp_rw [Finset.sum_add_distrib]
      rw [← Finset.sum_product', ← Finset.sum_product']
    _ = β^2 * ((∑ m ∈ Finset.range N, ∑ n ∈ Finset.range N,
          bflatModeSeriesVariance e 0 m n 1 L) +
        (∑ m ∈ Finset.range N, ∑ n ∈ Finset.range N,
          bflatModeSeriesVariance e 1 m n 1 L)) := by
      rw [h0, h1]
      ring
    _ = _ := by rw [hbase']

end ASDExplicitGamma.Model
