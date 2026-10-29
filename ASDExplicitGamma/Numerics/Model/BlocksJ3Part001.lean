module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ3Part000

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ3B1 : ModeBlockData :=
  ⟨⟨1, 2, (3541343242065906921/156250000000000000000 : ℚ), (39970929680827387/125000000000000000000 : ℚ)⟩, [
    (1, modeDataJ3M2)], (226645967492218042943/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j3_b1 : entryChecks 3 bflatBlockJ3B1.entries = true := by
  simp only [entryChecks,bflatBlockJ3B1,List.all_cons,List.all_nil,
    mode_checked_j3_m2,Bool.and_self]
theorem block_mass_checked_j3_b1 : blockMassCheck bflatBlockJ3B1 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
