module

public import ASDExplicitGamma.Triadic.PoincareCell
public import ASDExplicitGamma.Triadic.TriadicDualNorms
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! Literal Bochner cell means and Haar energies for Hilbert-valued fields.
The Sobolev carrier records L2 values/derivatives and the usual weak derivative
identity against every scalar Hilbert functional, not any norm estimate. -/

@[expose] public section

namespace ASDExplicitGamma.Triadic

open Homogenization MeasureTheory
open scoped BigOperators

noncomputable section

/-- The normalized Bochner mean of a Hilbert-valued cell field. -/
def hilbertCubeAverage {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (Q : TriadicCube d) (F : Vec d → E) : E := ∫ x, F x ∂normalizedCubeMeasure Q

/-- The actual conditional cell-mean field at a complete triadic depth. -/
def hilbertCubeProjection {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (Q : TriadicCube d) (j : ℕ) (F : Vec d → E) : Vec d → E := by
  classical
  exact fun x => ∑ R ∈ descendantsAtDepth Q j, if x ∈ cubeSet R then hilbertCubeAverage R F else 0

/-- Orthogonal Haar increments, including the root mean. -/
def hilbertCubeIncrement {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (Q : TriadicCube d) (j : ℕ) (F : Vec d → E) : Vec d → E :=
  match j with
  | 0 => hilbertCubeProjection Q 0 F
  | n+1 => fun x => hilbertCubeProjection Q (n+1) F x-hilbertCubeProjection Q n F x

/-- The normalized squared Hilbert-valued L2 norm. -/
def hilbertEnergy {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    (Q : TriadicCube d) (F : Vec d → E) : ℝ := ∫ x, ‖F x‖^2 ∂normalizedCubeMeasure Q

/-- The positive Haar energy for any real weight. Finiteness is proved or
recorded by Summable at uses, rather than inferred from real-tsum defaults. -/
def hilbertPrimalEnergy {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (Q : TriadicCube d) (q : ℝ) (F : Vec d → E) : ℝ :=
  hilbertEnergy Q (hilbertCubeIncrement Q 0 F)+
    ∑' k, q^(k+1)*hilbertEnergy Q (hilbertCubeIncrement Q (k+1) F)

/-- The mean-zero positive Haar energy omits exactly the root coefficient. -/
def hilbertPrimalCircEnergy {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (Q : TriadicCube d) (q : ℝ) (F : Vec d → E) : ℝ :=
  ∑' k, q^(k+1)*hilbertEnergy Q (hilbertCubeIncrement Q (k+1) F)

/-- Genuine Hilbert-valued H1 functions, using the scalar-functional weak
partial derivative characterization. No Poincare or projection premise is a field. -/
structure HilbertH1Function {d : ℕ} (U : Set (Vec d)) (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] where
  toFun : Vec d → E
  grad : Vec d → Fin d → E
  memL2 : MemLp toFun 2 (volume.restrict U)
  gradMemL2 : ∀ i, MemLp (fun x => grad x i) 2 (volume.restrict U)
  hasWeakGradient : ∀ e : E, HasWeakGradientOn U (fun x => inner ℝ e (toFun x))
    (fun x i => inner ℝ e (grad x i))

theorem hilbertCubeAverage_real {d : ℕ} (Q : TriadicCube d) (f : Vec d → ℝ) :
    hilbertCubeAverage Q f = cubeAverage Q f :=
  (cubeAverage_eq_integral_normalizedCubeMeasure Q f).symm

theorem hilbertCubeProjection_real {d : ℕ} (Q : TriadicCube d) (j : ℕ) (f : Vec d → ℝ) :
    hilbertCubeProjection Q j f = cubeProjection Q j f := by
  unfold hilbertCubeProjection cubeProjection
  simp only [hilbertCubeAverage_real]

theorem hilbertCubeIncrement_real {d : ℕ} (Q : TriadicCube d) (j : ℕ) (f : Vec d → ℝ) :
    hilbertCubeIncrement Q j f = cubeIncrement Q j f := by
  cases j <;> simp only [hilbertCubeIncrement, cubeIncrement, hilbertCubeProjection_real]

theorem hilbertEnergy_real {d : ℕ} (Q : TriadicCube d) (f : Vec d → ℝ) :
    hilbertEnergy Q f = energy Q f := by
  rw [energy_eq_integral_sq]
  simp only [hilbertEnergy, Real.norm_eq_abs, sq_abs]

theorem hilbertPrimalEnergy_real {d : ℕ} (Q : TriadicCube d) (q : ℝ) (f : Vec d → ℝ) :
    hilbertPrimalEnergy Q q f = primalEnergy Q q f := by
  simp only [hilbertPrimalEnergy, primalEnergy, hilbertCubeIncrement_real, hilbertEnergy_real]

/-- The Bochner mean commutes with every bounded linear map. -/
theorem hilbertCubeAverage_map {d : ℕ} {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (Q : TriadicCube d) (L : E →L[ℝ] F) {u : Vec d → E}
    (hu : MemLp u 2 (normalizedCubeMeasure Q)) :
    hilbertCubeAverage Q (fun x => L (u x)) = L (hilbertCubeAverage Q u) :=
  L.integral_comp_comm (hu.integrable one_le_two)

/-- Scalar Hilbert coordinates of a vector H1 field are genuine scalar H1 witnesses. -/
def HilbertH1Function.scalar {d : ℕ} {U : Set (Vec d)} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] (u : HilbertH1Function U E) (e : E) : H1Function U where
  toFun x := inner ℝ e (u.toFun x)
  grad x i := inner ℝ e (u.grad x i)
  memL2 := (innerSL ℝ e).comp_memLp' u.memL2
  gradMemL2 i := (innerSL ℝ e).comp_memLp' (u.gradMemL2 i)
  hasWeakGradient := u.hasWeakGradient e

end

end ASDExplicitGamma.Triadic
