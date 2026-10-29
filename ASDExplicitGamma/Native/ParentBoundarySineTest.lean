module

public import ASDExplicitGamma.Triadic.PlanarDirichletSpectral

/-! Sharp finite sine tests for the parent Dirichlet Poincare clock. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Triadic ASDExplicitGamma.Triadic.Torus
noncomputable section

/-- Ordinary vector L2 Cauchy-Schwarz with all load coordinates retained. -/
theorem parent_boundary_vector_pairing_l2 (Q : TriadicCube 2)
    (F G : Vec 2 → Vec 2)
    (hF : ∀ i,MemLp (fun x => F x i) 2 (normalizedCubeMeasure Q))
    (hG : ∀ i,MemLp (fun x => G x i) 2 (normalizedCubeMeasure Q)) :
    |vectorPairing Q F G| ≤ Real.sqrt (∑ i,energy Q (fun x => F x i))*
      Real.sqrt (∑ i,energy Q (fun x => G x i)) := by
  have hc := Real.sum_sqrt_mul_sqrt_le Finset.univ
    (fun i => energy_nonneg Q (fun x => F x i))
    (fun i => energy_nonneg Q (fun x => G x i))
  exact (Finset.abs_sum_le_sum_abs _ _).trans
    ((Finset.sum_le_sum (fun i _ => abs_pairing_le Q (hF i) (hG i))).trans hc)

/-- Finite positive-frequency coefficient sums obey the FIRST Dirichlet
eigenvalue clock R²/(2π²), without a Haar loss. -/
theorem parent_boundary_finite_sine_poincare (Q : TriadicCube 2)
    (u : H10Function (openCubeSet Q)) (S : Finset (Fin 2 → ℕ))
    (hS : ∀ q ∈ S,∀ i,q i≠0) :
    (∑ q ∈ S,modeMult q*dirichletFourierCoeff Q u.toH1Function.toFun (natVec q)^2) ≤
      cubeScaleFactor Q^2/(2*Real.pi^2)*∑ i : Fin 2,energy Q (fun x => u.toH1Function.grad x i) := by
  let c : (Fin 2 → ℕ) → ℝ := fun q => dirichletFourierCoeff Q u.toH1Function.toFun (natVec q)
  let β : (Fin 2 → ℕ) → ℝ := fun q => modeMult q*c q/cubeEig Q (natVec q)
  let G : Vec 2 → Vec 2 := u.toH1Function.grad
  let F : Vec 2 → Vec 2 := fun x i => dirichletTestField Q S β i x
  have hG (i : Fin 2) : MemLp (fun x => G x i) 2 (normalizedCubeMeasure Q) :=
    u.toH1Function.grad_memL2_normalizedCubeMeasure i
  have hF (i : Fin 2) : MemLp (fun x => F x i) 2 (normalizedCubeMeasure Q) :=
    (dirichletTestFieldH1 Q S β i).memL2_normalizedCubeMeasure
  have hpair : vectorPairing Q G F =
      ∑ q ∈ S, modeMult q * c q ^ 2 := by
    unfold vectorPairing F
    rw [Finset.sum_congr rfl fun j _ => pairing_dirichletTestField Q S β j (hG j)]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun q hq => ?_
    have hcoef : ∀ j,
        ∫ x, cubeDirichletMixedMode Q j q x * G x j ∂normalizedCubeMeasure Q =
          cubeFreq Q (natVec q) j * c q := by
      intro j
      rw [show (fun x => cubeDirichletMixedMode Q j q x * G x j) =
        fun x => u.toH1Function.grad x j * cubeDirichletMixedMode Q j q x by
          funext x
          simp [G]
          ring]
      simpa [c] using integral_h10Deriv_mul_dirichletMixed Q u j q
    have hsum : ∑ j : Fin 2, (β q * cubeFreq Q (natVec q) j) *
          (cubeFreq Q (natVec q) j * c q) = β q * c q * cubeEig Q (natVec q) := by
      calc
        ∑ j : Fin 2, (β q * cubeFreq Q (natVec q) j) *
            (cubeFreq Q (natVec q) j * c q) =
          β q * c q * ∑ j : Fin 2, cubeFreq Q (natVec q) j ^ 2 := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun j _ => ?_
            ring
        _ = β q * c q * cubeEig Q (natVec q) := by rw [cubeEig]
    have hEigNonzero : cubeEig Q (natVec q) ≠ 0 := by
      have hpos := planar_cubeEig_lower_of_nonzero Q q (hS q hq)
      have hbase : 0 < 2 * Real.pi ^ 2 / cubeScaleFactor Q ^ 2 :=
        div_pos (by positivity) (sq_pos_of_pos (cubeScaleFactor_pos' Q))
      exact ne_of_gt (lt_of_lt_of_le hbase hpos)
    calc
      ∑ j : Fin 2, (β q * cubeFreq Q (natVec q) j) *
          ∫ x, cubeDirichletMixedMode Q j q x * G x j ∂normalizedCubeMeasure Q =
        β q * c q * cubeEig Q (natVec q) := by
          calc
            _ = ∑ j : Fin 2, (β q * cubeFreq Q (natVec q) j) *
                (cubeFreq Q (natVec q) j * c q) := by
                  refine Finset.sum_congr rfl fun j _ => ?_
                  rw [hcoef j]
            _ = β q * c q * cubeEig Q (natVec q) := hsum
      _ = modeMult q * c q ^ 2 := by
        dsimp [β]
        field_simp [hEigNonzero]
        
  let A := ∑ q ∈ S,modeMult q*c q^2
  let C := cubeScaleFactor Q^2/(2*Real.pi^2)
  have hA : 0≤A := Finset.sum_nonneg (fun q _ => mul_nonneg (modeMult_pos q).le (sq_nonneg _))
  have hC : 0≤C := by positivity
  have hFE : (∑ i : Fin 2,energy Q (fun x => F x i))≤C*A := by
    rw [show (∑ i : Fin 2,energy Q (fun x => F x i)) =
      ∑ q ∈ S,β q^2*cubeEig Q (natVec q)/modeMult q from sum_energy_dirichletTestField Q S β hS]
    dsimp only [A]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro q hq
    have he := planar_cubeEig_lower_of_nonzero Q q (hS q hq)
    have hRp : 0<cubeScaleFactor Q^2 := sq_pos_of_pos (ASDExplicitGamma.Triadic.cubeScaleFactor_pos' Q)
    have hEp : 0<cubeEig Q (natVec q) := lt_of_lt_of_le (by positivity) he
    have hm : 0<modeMult q := modeMult_pos q
    have hbase : 1≤C*cubeEig Q (natVec q) := by
      dsimp [C]
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ (by positivity : (0:ℝ)<2*Real.pi^2)).2
      have hh := (div_le_iff₀ hRp).1 he
      nlinarith only [hh]
    have hid : β q^2*cubeEig Q (natVec q)/modeMult q =modeMult q*c q^2/cubeEig Q (natVec q) := by
      dsimp [β]
      field_simp [hEp.ne',hm.ne']
    rw [hid]
    apply (div_le_iff₀ hEp).2
    have hh := mul_le_mul_of_nonneg_left hbase (mul_nonneg hm.le (sq_nonneg (c q)))
    nlinarith only [hh]
  have hp := parent_boundary_vector_pairing_l2 Q G F hG hF
  rw [hpair,abs_of_nonneg hA] at hp
  have hE : 0≤∑ i : Fin 2,energy Q (fun x => G x i) :=
    Finset.sum_nonneg (fun i _ => energy_nonneg Q _)
  have hFEn : 0≤∑ i : Fin 2,energy Q (fun x => F x i) :=
    Finset.sum_nonneg (fun i _ => energy_nonneg Q _)
  have hs := mul_self_le_mul_self hA hp
  rw [←pow_two,←pow_two,mul_pow,Real.sq_sqrt hE,Real.sq_sqrt hFEn] at hs
  have hsq : A^2≤(C*A)*(∑ i : Fin 2,energy Q (fun x => G x i)) :=
    hs.trans (by simpa only [mul_comm] using mul_le_mul_of_nonneg_left hFE hE)
  by_cases hAz : A=0
  · rw [show (∑ q ∈ S,modeMult q*dirichletFourierCoeff Q u.toH1Function.toFun (natVec q)^2)=A from rfl,hAz]
    exact mul_nonneg hC hE
  · have hAp : 0<A := lt_of_le_of_ne hA (Ne.symm hAz)
    change A≤C*(∑ i : Fin 2,energy Q (fun x => G x i))
    apply (mul_le_mul_iff_right₀ hAp).1
    convert hsq using 1 <;> ring

end
end ASDExplicitGamma.Native
