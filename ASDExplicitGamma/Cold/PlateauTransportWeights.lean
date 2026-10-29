module

public import ASDExplicitGamma.Cold.SquareProjectionAE

/-! # CO-PLATEAU-P2: actual gradient–solenoidal transport with the explicit source weights -/

@[expose] public section
noncomputable section
open MeasureTheory Homogenization Filter Topology
open ASDExplicitGamma.Triadic
open scoped BigOperators ENNReal
namespace ASDExplicitGamma.Cold

/-- The actual source transport agrees with the stream-function transport form. -/
theorem plateau_integral_eq_transport (Q : TriadicCube 2) (u w : H1Function (openCubeSet Q))
    {j : Vec 2 → Vec 2}
    (hj : j =ᵐ[volume.restrict (openCubeSet Q)] (fun x => squareQuarterTurn (w.grad x))) :
    (∫ x, plateauOnSquare Q x * (∑ i : Fin 2, u.grad x i * j x i)
      ∂normalizedCubeMeasure Q) = plateauTransport Q u w := by
  have hjn := (square_ae_normalized_iff Q).mpr hj
  have heq : (fun x => plateauOnSquare Q x * (∑ i : Fin 2, u.grad x i * j x i)) =ᵐ[normalizedCubeMeasure Q]
      (fun x => -(plateauOnSquare Q x * u.grad x 0 * w.grad x 1) +
        plateauOnSquare Q x * u.grad x 1 * w.grad x 0) := by
    filter_upwards [hjn] with x hx
    rw [hx]
    simp only [Fin.sum_univ_two, squareQuarterTurn, Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  rw [integral_congr_ae heq]
  have h0 : Integrable (fun x => plateauOnSquare Q x * u.grad x 0 * w.grad x 1)
      (normalizedCubeMeasure Q) :=
    ((memLp_plateauOnSquare Q ⊤).mul (r := 2)
      (memLp_normalized_of_memL2On (u.gradMemL2 0))).integrable_mul
      (memLp_normalized_of_memL2On (w.gradMemL2 1))
  have h1 : Integrable (fun x => plateauOnSquare Q x * u.grad x 1 * w.grad x 0)
      (normalizedCubeMeasure Q) :=
    ((memLp_plateauOnSquare Q ⊤).mul (r := 2)
      (memLp_normalized_of_memL2On (u.gradMemL2 1))).integrable_mul
      (memLp_normalized_of_memL2On (w.gradMemL2 0))
  rw [integral_add (f := fun x => -(plateauOnSquare Q x * u.grad x 0 * w.grad x 1))
    (g := fun x => plateauOnSquare Q x * u.grad x 1 * w.grad x 0) h0.neg h1, integral_neg]
  exact (normalizedSquareTransport_eq_integrals Q _ u w).symm

/-- CO-PLATEAU-P2. Every actual H¹ gradient and distributionally divergence-free L² flux
satisfy the source transport estimate. The sum is indexed by the even depths `2(k+1)`;
its exceptional first weight and all corrected tail identities are in `PlateauWeights`. -/
theorem plateau_transport_weights (Q : TriadicCube 2) (u : H1Function (openCubeSet Q))
    {j : Vec 2 → Vec 2} (hj : MemVectorL2 (openCubeSet Q) j)
    (hdiv : IsSolenoidalOn (openCubeSet Q) j) :
    |∫ x, plateauOnSquare Q x * (∑ i : Fin 2, u.grad x i * j x i) ∂normalizedCubeMeasure Q| ≤
      ∑' k : ℕ, plateauEvenWeight k *
        (squareVectorEnergy Q (squareProjection Q (2*(k+1)) u.grad) +
         squareVectorEnergy Q (squareProjection Q (2*(k+1)) j)) := by
  obtain ⟨w, _, hstream⟩ := square_stream_function Q hj hdiv
  rw [plateau_integral_eq_transport Q u w hstream]
  simp_rw [squareProjection_stream_energy Q w hstream]
  exact plateau_gradient_weights Q u w

end ASDExplicitGamma.Cold
