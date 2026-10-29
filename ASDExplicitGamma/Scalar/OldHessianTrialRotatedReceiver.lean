module

public import ASDExplicitGamma.Scalar.OldHessianTrialPrincipalBudget
public import ASDExplicitGamma.Triadic.VectorHaarSymmetry

/-! The spatial and load quarter turns in the signed principal covariance
preserve the whole two-load weak budget exactly. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational
noncomputable section

/-- The two spatial/load quarter turns, with their actual signs. -/
def oldHessianRotatedReceiver (G : Fin 2 → Vec 2 → Vec 2) (i : Fin 2) (x : Vec 2) : Vec 2 :=
  if i=0 then planarQuarterTurn (G 1 x) else -planarQuarterTurn (G 0 x)

theorem old_hessian_receiver_weak_quarter_turn (Q : TriadicCube 2) (F : Vec 2 → Vec 2) :
    vectorWeakHaarEnergy Q (fun x => planarQuarterTurn (F x))=vectorWeakHaarEnergy Q F := by
  simp only [vectorWeakHaarEnergy,dualEnergy,Fin.sum_univ_two,planarQuarterTurn,
    ite_true,show (1:Fin 2)≠0 by decide,ite_false,primalEnergy_neg]
  ring

theorem old_hessian_receiver_weak_neg (Q : TriadicCube 2) (F : Vec 2 → Vec 2) :
    vectorWeakHaarEnergy Q (fun x => -F x)=vectorWeakHaarEnergy Q F := by
  simp only [vectorWeakHaarEnergy,dualEnergy,Pi.neg_apply,primalEnergy_neg]

/-- Both rotations preserve the complete fine weak energy, including means. -/
theorem old_hessian_rotated_receiver_weak (Q : TriadicCube 2) (fine : ℕ)
    (G : Fin 2 → Vec 2 → Vec 2) :
    (∑ i : Fin 2,lemmaVTiledWeakEnergy Q fine (oldHessianRotatedReceiver G i))=
      ∑ i : Fin 2,lemmaVTiledWeakEnergy Q fine (G i) := by
  rw [Fin.sum_univ_two,Fin.sum_univ_two]
  change lemmaVTiledWeakEnergy Q fine (fun x => planarQuarterTurn (G 1 x))+
    lemmaVTiledWeakEnergy Q fine (fun x => -planarQuarterTurn (G 0 x)) = _
  unfold lemmaVTiledWeakEnergy
  simp_rw [old_hessian_receiver_weak_neg,old_hessian_receiver_weak_quarter_turn]
  exact add_comm _ _

/-- These exact rotations also preserve coordinate square integrability. -/
theorem old_hessian_rotated_receiver_memLp (Q : TriadicCube 2)
    (G : Fin 2 → Vec 2 → Vec 2)
    (hG : ∀ i k, MemLp (fun x => G i x k) 2 (normalizedCubeMeasure Q)) :
    ∀ i k, MemLp (fun x => oldHessianRotatedReceiver G i x k) 2 (normalizedCubeMeasure Q) := by
  intro i k
  fin_cases i <;> fin_cases k
  · change MemLp (fun x => -G 1 x 1) 2 (normalizedCubeMeasure Q)
    exact (hG 1 1).neg
  · change MemLp (fun x => G 1 x 0) 2 (normalizedCubeMeasure Q)
    exact hG 1 0
  · change MemLp (fun x => -(-G 0 x 1)) 2 (normalizedCubeMeasure Q)
    simpa only [neg_neg] using hG 0 1
  · change MemLp (fun x => -G 0 x 0) 2 (normalizedCubeMeasure Q)
    exact (hG 0 0).neg

end
end ASDExplicitGamma.Scalar
