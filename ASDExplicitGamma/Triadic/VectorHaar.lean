module

public import ASDExplicitGamma.Triadic.PlanarConstants

/-! Coordinatewise vector-valued order-`1/4` Haar energies. -/

@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators

namespace ASDExplicitGamma.Triadic

variable {d m : ℕ}

/-- The order-`1/4` positive Haar energy of a finite-dimensional vector field,
aggregated by the Euclidean sum over its coordinates. -/
noncomputable def vectorPositiveHaarEnergy (Q : TriadicCube d)
    (F : Vec d → Fin m → ℝ) : ℝ :=
  ∑ i, primalEnergy Q (Real.sqrt 3) (fun x => F x i)

/-- The order-`1/4` weak Haar energy of a finite-dimensional vector field,
aggregated by the Euclidean sum over its coordinates. -/
noncomputable def vectorWeakHaarEnergy (Q : TriadicCube d)
    (F : Vec d → Fin m → ℝ) : ℝ :=
  ∑ i, dualEnergy Q (Real.sqrt 3) (fun x => F x i)

/-- The vector positive Haar norm, including the root mean. -/
noncomputable def vectorPositiveHaarNorm (Q : TriadicCube d)
    (F : Vec d → Fin m → ℝ) : ℝ :=
  Real.sqrt (vectorPositiveHaarEnergy Q F)

/-- The vector weak Haar norm, including the root mean. -/
noncomputable def vectorWeakHaarNorm (Q : TriadicCube d)
    (F : Vec d → Fin m → ℝ) : ℝ :=
  Real.sqrt (vectorWeakHaarEnergy Q F)

theorem primalEnergy_nonneg (Q : TriadicCube d) (q : ℝ) (hq : 0 ≤ q)
    (f : Vec d → ℝ) : 0 ≤ primalEnergy Q q f := by
  unfold primalEnergy
  apply add_nonneg (energy_nonneg Q _)
  apply tsum_nonneg
  intro k
  exact mul_nonneg (pow_nonneg hq _) (energy_nonneg Q _)

theorem dualEnergy_nonneg (Q : TriadicCube d) (q : ℝ) (hq : 0 ≤ q)
    (f : Vec d → ℝ) : 0 ≤ dualEnergy Q q f := by
  unfold dualEnergy
  exact primalEnergy_nonneg Q q⁻¹ (inv_nonneg.mpr hq) f

theorem vectorPositiveHaarEnergy_nonneg (Q : TriadicCube d)
    (F : Vec d → Fin m → ℝ) : 0 ≤ vectorPositiveHaarEnergy Q F := by
  unfold vectorPositiveHaarEnergy
  apply Finset.sum_nonneg
  intro i hi
  exact primalEnergy_nonneg Q (Real.sqrt 3) (Real.sqrt_nonneg _) _

theorem vectorWeakHaarEnergy_nonneg (Q : TriadicCube d)
    (F : Vec d → Fin m → ℝ) : 0 ≤ vectorWeakHaarEnergy Q F := by
  unfold vectorWeakHaarEnergy
  apply Finset.sum_nonneg
  intro i hi
  exact dualEnergy_nonneg Q (Real.sqrt 3) (Real.sqrt_nonneg _) _

/-- Squaring the vector positive norm gives the sum of squared scalar positive
norms, so this is precisely coordinatewise `ℓ²` aggregation. -/
theorem vectorPositiveHaarNorm_sq (Q : TriadicCube d)
    (F : Vec d → Fin m → ℝ) :
    vectorPositiveHaarNorm Q F ^ 2 =
      ∑ i, positiveHaarNorm Q (fun x => F x i) ^ 2 := by
  change Real.sqrt (vectorPositiveHaarEnergy Q F) ^ 2 =
    ∑ i, Real.sqrt (primalEnergy Q (Real.sqrt 3) (fun x => F x i)) ^ 2
  rw [Real.sq_sqrt (vectorPositiveHaarEnergy_nonneg Q F)]
  unfold vectorPositiveHaarEnergy
  apply Finset.sum_congr rfl
  intro i hi
  rw [Real.sq_sqrt (primalEnergy_nonneg Q (Real.sqrt 3) (Real.sqrt_nonneg _) _)]

/-- Squaring the vector weak norm gives the sum of squared scalar weak norms,
so this is precisely coordinatewise `ℓ²` aggregation. -/
theorem vectorWeakHaarNorm_sq (Q : TriadicCube d)
    (F : Vec d → Fin m → ℝ) :
    vectorWeakHaarNorm Q F ^ 2 =
      ∑ i, weakHaarNorm Q (fun x => F x i) ^ 2 := by
  change Real.sqrt (vectorWeakHaarEnergy Q F) ^ 2 =
    ∑ i, Real.sqrt (dualEnergy Q (Real.sqrt 3) (fun x => F x i)) ^ 2
  rw [Real.sq_sqrt (vectorWeakHaarEnergy_nonneg Q F)]
  unfold vectorWeakHaarEnergy
  apply Finset.sum_congr rfl
  intro i hi
  rw [Real.sq_sqrt (dualEnergy_nonneg Q (Real.sqrt 3) (Real.sqrt_nonneg _) _)]

end ASDExplicitGamma.Triadic
