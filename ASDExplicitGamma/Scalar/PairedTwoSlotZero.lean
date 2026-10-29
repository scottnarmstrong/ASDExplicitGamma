module

public import ASDExplicitGamma.Scalar.PairedTwoSlotSum
public import ASDExplicitGamma.Scalar.PairedTwoSlotRep
public import ASDExplicitGamma.Native.OldSignedCenteredPositive

/-! Zero source fields and elementary real lemmas for the two-slot assembly. -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open Homogenization MeasureTheory ASDExplicitGamma.Triadic ASDExplicitGamma.Native
open scoped InnerProduct InnerProductSpace

noncomputable section

theorem cubeAverage_zero (R : TriadicCube 2) :
    cubeAverage R (fun _ : Vec 2 => (0 : ℝ)) = 0 := by
  simp [cubeAverage]

theorem cubeIncrement_zero' (Q : TriadicCube 2) (j : ℕ) :
    cubeIncrement Q j (fun _ : Vec 2 => (0 : ℝ)) = fun _ => 0 := by
  have h := cubeAverage_zero
  cases j with
  | zero =>
    classical
    funext x
    show (Finset.sum (descendantsAtDepth Q 0) fun R => if x ∈ cubeSet R then cubeAverage R _ else 0) = 0
    simp [h]
  | succ n =>
    simp [cubeIncrement, cubeProjection, h]

theorem energy_increment_zero (Q : TriadicCube 2) (j : ℕ) :
    energy Q (cubeIncrement Q j (fun _ : Vec 2 => (0 : ℝ))) = 0 := by
  rw [cubeIncrement_zero']
  simp [energy, pairing, cubeAverage_zero]

/-- The zero source field. -/
def zeroField : Vec 2 → Vec 2 := fun _ => 0

theorem zeroField_memL2 (U : Set (Vec 2)) [IsFiniteMeasure (volumeMeasureOn U)] : MemVectorL2 U zeroField :=
  memVectorL2_const (U := U) 0

theorem zeroField_memLp (U : TriadicCube 2) :
    MemLp zeroField 2 (normalizedCubeMeasure U) :=
  MeasureTheory.memLp_const 0

theorem zeroField_pos (U : TriadicCube 2) (i : Fin 2) :
    Summable (fun j : ℕ => (Real.sqrt 3) ^ (j + 1) *
      energy U (cubeIncrement U (j + 1) (fun x => zeroField x i))) := by
  have : ∀ j : ℕ, (Real.sqrt 3) ^ (j + 1) *
      energy U (cubeIncrement U (j + 1) (fun x => zeroField x i)) = 0 := fun j => by
    have := energy_increment_zero U (j + 1)
    simpa [zeroField] using this
  simp only [this]
  exact summable_zero

theorem zeroField_energy (U : TriadicCube 2) : vectorPositiveHaarEnergy U zeroField = 0 := by
  unfold vectorPositiveHaarEnergy
  simp [zeroField, old_signed_primal_zero]

theorem inner_zeroField {U : Set (Vec 2)} [IsFiniteMeasure (volumeMeasureOn U)]
    (u : HilbertVectorL2 U) :
    ⟪toHilbertVectorL2OfVecField (zeroField_memL2 U), u⟫_ℝ = 0 := by
  rw [← hilbert_rebuild u, inner_ofField]
  simp [zeroField, vecDot]

theorem le_of_le_sqrt_mul {e W : ℝ} (he : 0 ≤ e) (hW : 0 ≤ W)
    (h : e ≤ Real.sqrt e * Real.sqrt W) : e ≤ W := by
  by_cases h0 : e = 0
  · rw [h0]; exact hW
  · have hpos : 0 < Real.sqrt e := Real.sqrt_pos.2 (lt_of_le_of_ne he (Ne.symm h0))
    have h1 : Real.sqrt e * Real.sqrt e ≤ Real.sqrt e * Real.sqrt W := by
      rwa [Real.mul_self_sqrt he]
    have h2 : Real.sqrt e ≤ Real.sqrt W := le_of_mul_le_mul_left h1 hpos
    have h3 := Real.sqrt_le_sqrt_iff hW |>.1 h2
    exact h3

theorem three_pow_neg_quarter_le : (3 : ℝ) ^ (-(1 / 4 : ℝ)) ≤ 19 / 25 := by
  have h4 : ((3 : ℝ) ^ (-(1 / 4 : ℝ))) ^ 4 = 1 / 3 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    norm_num
  by_contra hlt
  have hlt := not_le.mp hlt
  have : (19 / 25 : ℝ) ^ 4 < ((3 : ℝ) ^ (-(1 / 4 : ℝ))) ^ 4 :=
    pow_lt_pow_left₀ hlt (by norm_num) (by norm_num)
  rw [h4] at this
  norm_num at this

end

end ASDExplicitGamma.Scalar
