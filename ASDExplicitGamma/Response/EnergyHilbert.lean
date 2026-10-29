module

public import Homogenization.CoarseGraining.MuWellPosedness

@[expose] public section

namespace ASDExplicitGamma.Response

open Filter

universe u

noncomputable section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H]

/-- A symmetric coercive bilinear energy on a Hilbert carrier. -/
structure EnergyHilbertData where
  energy : H →L[ℝ] H →L[ℝ] ℝ
  symmetric : ∀ x y, energy x y = energy y x
  coercive : IsCoercive energy

/-- A type synonym whose inner product is a chosen coercive energy form. -/
def EnergyCarrier (_D : EnergyHilbertData (H := H)) := ULift.{u, u} H

instance instAddCommGroupEnergyCarrier (_D : EnergyHilbertData (H := H)) :
    AddCommGroup (EnergyCarrier _D) := inferInstanceAs (AddCommGroup (ULift H))

instance instModuleEnergyCarrier (_D : EnergyHilbertData (H := H)) :
    Module ℝ (EnergyCarrier _D) := inferInstanceAs (Module ℝ (ULift H))

/-- The energy inner product core, before its equivalent norm is installed. -/
@[instance_reducible]
def energyInnerProductCore (D : EnergyHilbertData (H := H)) :
    InnerProductSpace.Core ℝ (EnergyCarrier D) where
  inner x y := D.energy x.down y.down
  conj_inner_symm x y := by
    change D.energy y.down x.down = D.energy x.down y.down
    exact D.symmetric y.down x.down
  re_inner_nonneg x := by
    rcases D.coercive with ⟨c, hc, hcoer⟩
    change 0 ≤ D.energy x.down x.down
    let xH : H := x.down
    have h := hcoer xH
    have hnonneg : 0 ≤ c * ‖xH‖ * ‖xH‖ := by positivity
    change 0 ≤ D.energy xH xH
    linarith
  add_left x y z := by
    change D.energy (x.down + y.down) z.down =
      D.energy x.down z.down + D.energy y.down z.down
    rw [map_add, add_apply]
  smul_left x y r := by
    change D.energy (r • x.down) y.down = r * D.energy x.down y.down
    rw [map_smul, smul_apply, smul_eq_mul]
  definite x hx := by
    rcases D.coercive with ⟨c, hc, hcoer⟩
    let xH : H := x.down
    have hx' : D.energy xH xH = 0 := hx
    have h := hcoer xH
    have hnorm : ‖xH‖ = 0 := by
      rw [hx'] at h
      by_contra hne
      have hpos : 0 < ‖xH‖ := lt_of_le_of_ne (norm_nonneg xH) (Ne.symm hne)
      have hsq : 0 < ‖xH‖ * ‖xH‖ := mul_pos hpos hpos
      nlinarith
    have hz : xH = 0 := norm_eq_zero.mp hnorm
    change ULift.up x.down = ULift.up (0 : H)
    exact congrArg ULift.up hz

instance instNormedAddCommGroupEnergyCarrier (D : EnergyHilbertData (H := H)) :
    NormedAddCommGroup (EnergyCarrier D) :=
  (energyInnerProductCore D).toNormedAddCommGroup

instance instInnerProductSpaceEnergyCarrier (D : EnergyHilbertData (H := H)) :
    InnerProductSpace ℝ (EnergyCarrier D) :=
  letI : InnerProductSpace.Core ℝ (EnergyCarrier D) := energyInnerProductCore D
  InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℝ (EnergyCarrier D))

omit [CompleteSpace H] in
theorem energyCarrier_norm_sq (D : EnergyHilbertData (H := H)) (x : EnergyCarrier D) :
    ‖x‖ ^ 2 = D.energy x.down x.down := by
  rw [@InnerProductSpace.norm_sq_eq_re_inner ℝ (EnergyCarrier D)]
  change RCLike.re ((energyInnerProductCore D).inner x x) = _
  rfl

omit [CompleteSpace H] in
private theorem energy_form_norm_sq_le (D : EnergyHilbertData (H := H)) (x : H) :
    D.energy x x ≤ (‖D.energy‖ + 1) * ‖x‖ ^ 2 := by
  have hEval : |D.energy x x| ≤ ‖D.energy x‖ * ‖x‖ := by
    simpa only [Real.norm_eq_abs] using (D.energy x).le_opNorm x
  have hOp : ‖D.energy x‖ ≤ ‖D.energy‖ * ‖x‖ := D.energy.le_opNorm x
  calc
    D.energy x x ≤ |D.energy x x| := le_abs_self _
    _ ≤ ‖D.energy x‖ * ‖x‖ := hEval
    _ ≤ ‖D.energy‖ * ‖x‖ * ‖x‖ := by gcongr
    _ ≤ (‖D.energy‖ + 1) * ‖x‖ ^ 2 := by nlinarith [sq_nonneg ‖x‖]

omit [CompleteSpace H] in
theorem energyCarrier_norm_le (D : EnergyHilbertData (H := H)) (x : EnergyCarrier D) :
    ‖x‖ ≤ Real.sqrt (‖D.energy‖ + 1) * ‖x.down‖ := by
  have hC : 0 ≤ ‖D.energy‖ + 1 := by positivity
  have hSq : ‖x‖ ^ 2 ≤
      (Real.sqrt (‖D.energy‖ + 1) * ‖x.down‖) ^ 2 := by
    rw [energyCarrier_norm_sq]
    have h := energy_form_norm_sq_le D x.down
    calc
      D.energy x.down x.down ≤ (‖D.energy‖ + 1) * ‖x.down‖ ^ 2 := h
      _ = (Real.sqrt (‖D.energy‖ + 1) * ‖x.down‖) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hC]
  nlinarith [norm_nonneg x,
    mul_nonneg (Real.sqrt_nonneg (‖D.energy‖ + 1)) (norm_nonneg x.down)]

omit [CompleteSpace H] in
theorem energyCarrier_norm_lower (D : EnergyHilbertData (H := H))
    (x : EnergyCarrier D) :
    Real.sqrt D.coercive.choose * ‖x.down‖ ≤ ‖x‖ := by
  have hc : 0 < D.coercive.choose := D.coercive.choose_spec.1
  have hcoer := D.coercive.choose_spec.2 x.down
  have hsq : (Real.sqrt D.coercive.choose * ‖x.down‖) ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hc.le, energyCarrier_norm_sq]
    nlinarith [hcoer]
  nlinarith [norm_nonneg x,
    mul_nonneg (Real.sqrt_nonneg D.coercive.choose) (norm_nonneg x.down)]

instance instCompleteSpaceEnergyCarrier (D : EnergyHilbertData (H := H)) :
    CompleteSpace (EnergyCarrier D) := by
  apply Metric.complete_of_cauchySeq_tendsto
  intro u hu
  let uH : ℕ → H := fun n => (u n).down
  have hc : 0 < (D.coercive.choose : ℝ) := D.coercive.choose_spec.1
  have hcSqrt : 0 < Real.sqrt D.coercive.choose := Real.sqrt_pos.2 hc
  have hCauchyH : CauchySeq uH := by
    rw [Metric.cauchySeq_iff] at hu ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := hu (Real.sqrt D.coercive.choose * ε) (mul_pos hcSqrt hε)
    refine ⟨N, ?_⟩
    intro n hn m hm
    have hDist : dist (u n) (u m) < Real.sqrt D.coercive.choose * ε := hN n hn m hm
    have hCoer := D.coercive.choose_spec.2 ((uH n) - (uH m))
    have hEnergy : ‖u n - u m‖ ^ 2 =
        D.energy ((uH n) - (uH m)) ((uH n) - (uH m)) := by
      rw [energyCarrier_norm_sq]
      rfl
    have hNorm : ‖(u n : EnergyCarrier D) - u m‖ = dist (u n) (u m) := by
      rw [dist_eq_norm]
    have hEnergySq : ‖(u n : EnergyCarrier D) - u m‖ ^ 2 <
        (Real.sqrt D.coercive.choose * ε) ^ 2 := by
      rw [hNorm]
      have hdn : 0 ≤ dist (u n) (u m) := dist_nonneg
      nlinarith [hDist, hdn]
    have hOldSq : ‖uH n - uH m‖ ^ 2 < ε ^ 2 := by
      rw [show ‖uH n - uH m‖ ^ 2 = ‖uH n - uH m‖ * ‖uH n - uH m‖ by ring]
      have hCoer' : D.coercive.choose * ‖uH n - uH m‖ ^ 2 ≤
          ‖u n - u m‖ ^ 2 := by
        rw [hEnergy]
        nlinarith [hCoer]
      have hSqlt : D.coercive.choose * ‖uH n - uH m‖ ^ 2 <
          D.coercive.choose * ε ^ 2 := by
        calc
          D.coercive.choose * ‖uH n - uH m‖ ^ 2 ≤
              ‖u n - u m‖ ^ 2 := hCoer'
          _ < (Real.sqrt D.coercive.choose * ε) ^ 2 := hEnergySq
          _ = D.coercive.choose * ε ^ 2 := by
            rw [mul_pow, Real.sq_sqrt hc.le]
      have hNormSq : ‖uH n - uH m‖ ^ 2 < ε ^ 2 :=
        by nlinarith [hSqlt, hc]
      nlinarith [hNormSq]
    have hOld : ‖uH n - uH m‖ < ε := by
      nlinarith [sq_nonneg (‖uH n - uH m‖ - ε), norm_nonneg (uH n - uH m)]
    rw [dist_eq_norm]
    exact hOld
  obtain ⟨z, hz⟩ := cauchySeq_tendsto_of_complete hCauchyH
  let zE : EnergyCarrier D := ⟨z⟩
  have hOldNorm : Filter.Tendsto (fun n => ‖uH n - z‖) atTop (nhds 0) :=
    (tendsto_iff_norm_sub_tendsto_zero).1 hz
  have hScale : Filter.Tendsto (fun n => Real.sqrt (‖D.energy‖ + 1) * ‖uH n - z‖)
      atTop (nhds 0) := by
    have hConst : Filter.Tendsto (fun _ : ℕ => Real.sqrt (‖D.energy‖ + 1)) atTop
        (nhds (Real.sqrt (‖D.energy‖ + 1))) := tendsto_const_nhds
    have hmul := hConst.mul hOldNorm
    simpa using hmul
  have hNewNorm : Filter.Tendsto (fun n => ‖u n - zE‖)
      atTop (nhds 0) := by
    have hZero : Filter.Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0) :=
      tendsto_const_nhds
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le hZero hScale
      (fun _ => norm_nonneg _)
    intro n
    have h := energyCarrier_norm_le D (u n - zE)
    change ‖u n - zE‖ ≤ Real.sqrt (‖D.energy‖ + 1) * ‖(u n).down - z‖ at h
    simpa [uH] using h
  exact ⟨zE, (tendsto_iff_norm_sub_tendsto_zero).2 hNewNorm⟩

end

end ASDExplicitGamma.Response
