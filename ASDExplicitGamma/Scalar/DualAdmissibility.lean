module

public import ASDExplicitGamma.Scalar.DualMaximizer

/-! Global admissibility of zero-extended cellwise dual patches. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory

/-- The deterministic source in the bottom block. -/
def scalarBottomLoad (w : Vec 2 → Vec 2) (x : Vec 2) : BlockVec 2 := (0,w x)

/-- The actual bottom source field is L2 whenever the source is L2. -/
theorem scalar_bottom_load_memL2 {U : Set (Vec 2)} {w : Vec 2 → Vec 2} (hw : MemVectorL2 U w) :
    MemBlockL2 U (scalarBottomLoad w) := by
  exact (ContinuousLinearMap.inr ℝ (Vec 2) (Vec 2)).comp_memLp' hw

/-- Finite sums stay in the concrete source variation space. -/
theorem scalar_variation_finset_sum {ι : Type*} (U : Set (Vec 2)) (s : Finset ι)
    (F : ι → Vec 2 → BlockVec 2) (hF : ∀ i ∈ s,ScalarVariation U (F i)) :
    ScalarVariation U (∑ i ∈ s,F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using scalar_variation_zero U
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact scalar_variation_add (hF i (Finset.mem_insert_self i s))
      (ih (fun j hj => hF j (Finset.mem_insert_of_mem hj)))

end ASDExplicitGamma.Scalar
