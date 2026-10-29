module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ3Part002

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ3B35 : ModeBlockData :=
  ⟨⟨35, 36, (27709834765675528711/2000000000000000000000 : ℚ), (2360259329859144863/10000000000000000000000 : ℚ)⟩, [
    (35, modeDataJ3M36)], (69274586914188821777/5000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j3_b35 : entryChecks 3 bflatBlockJ3B35.entries = true := by
  simp only [entryChecks,bflatBlockJ3B35,List.all_cons,List.all_nil,
    mode_checked_j3_m36,Bool.and_self]
theorem block_mass_checked_j3_b35 : blockMassCheck bflatBlockJ3B35 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
