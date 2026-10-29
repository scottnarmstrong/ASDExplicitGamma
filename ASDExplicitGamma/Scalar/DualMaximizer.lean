module

public import ASDExplicitGamma.Scalar.DualEnergy
public import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-! The actual OLD-law variational maximizer and its Euler energy identity. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization Response MeasureTheory

/-- The literal deterministic-source pairing with the first field component. -/
noncomputable def scalarSourcePairing (U : Set (Vec 2)) (w : Vec 2 → Vec 2)
    (Z : Vec 2 → BlockVec 2) : ℝ := volumeAverage U (fun x => vecDot (w x) (Z x).1)

/-- The OLD-law maximizer over the genuine source variation space. -/
def IsScalarOldMaximizer (Q : TriadicCube 2) (ν σ : ℝ)
    (k : ResponseCoefficient (openCubeSet Q)) (w : Vec 2 → Vec 2) (Z : Vec 2 → BlockVec 2) : Prop :=
  ScalarVariation (openCubeSet Q) Z ∧ ∀ Y : Vec 2 → BlockVec 2,
    ScalarVariation (openCubeSet Q) Y →
      2*scalarSourcePairing (openCubeSet Q) w Y-scalarFieldEnergy ν σ k Y ≤
        2*scalarSourcePairing (openCubeSet Q) w Z-scalarFieldEnergy ν σ k Z

/-- The source pairing is linear on scalar multiples. -/
theorem scalar_source_pairing_smul (U : Set (Vec 2)) (w : Vec 2 → Vec 2)
    (Z : Vec 2 → BlockVec 2) (t : ℝ) : scalarSourcePairing U w (t • Z)=t*scalarSourcePairing U w Z := by
  unfold scalarSourcePairing
  have he : (fun x => vecDot (w x) ((t • Z) x).1)=t • (fun x => vecDot (w x) (Z x).1) := by
    funext x
    simp [vecDot_smul_right]
  rw [he,volumeAverage_smul]

/-- An unconstrained quadratic maximum at t=1 gives the exact Euler energy identity. -/
theorem quadratic_maximum_euler (a b : ℝ)
    (h : ∀ t : ℝ,2*t*b-t^2*a ≤ 2*b-a) : b=a := by
  have hm : IsLocalMax (fun t : ℝ => 2*t*b-t^2*a) 1 := by
    apply (show IsMaxOn (fun t : ℝ => 2*t*b-t^2*a) Set.univ 1 from ?_).isLocalMax (by simp)
    intro t _
    change 2*t*b-t^2*a ≤ 2*1*b-(1:ℝ)^2*a
    convert h t using 1 <;> ring
  have hd : HasDerivAt (fun t : ℝ => 2*t*b-t^2*a) (2*b-2*a) 1 := by
    convert (((hasDerivAt_id (1:ℝ)).const_mul 2).mul_const b).sub
      (((hasDerivAt_id (1:ℝ)).pow 2).mul_const a) using 1 <;> norm_num <;> rfl
  have he := hm.hasDerivAt_eq_zero hd
  linarith only [he]

/-- No Euler equation is assumed: it follows from the actual source maximizing property. -/
theorem scalar_old_maximizer_energy_identity (Q : TriadicCube 2) (ν σ : ℝ)
    (k : ResponseCoefficient (openCubeSet Q)) (w : Vec 2 → Vec 2) (Z : Vec 2 → BlockVec 2)
    (hZ : IsScalarOldMaximizer Q ν σ k w Z) :
    scalarSourcePairing (openCubeSet Q) w Z=scalarFieldEnergy ν σ k Z := by
  apply quadratic_maximum_euler
  intro t
  have h := hZ.2 (t • Z) (scalar_variation_smul hZ.1 t)
  rw [scalar_source_pairing_smul,scalar_field_energy_smul] at h
  simpa only [mul_assoc] using h

end ASDExplicitGamma.Scalar
