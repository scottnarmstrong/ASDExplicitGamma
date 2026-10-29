module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ0Part000

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ0B7 : ModeBlockData :=
  ⟨⟨7, 8, (16729252253473846559/2500000000000000000000 : ℚ), (104028544558136131/16000000000000000000 : ℚ)⟩, [
    (7, modeDataJ0M8)], (13383401802779077247/2000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j0_b7 : entryChecks 0 bflatBlockJ0B7.entries = true := by
  simp only [entryChecks,bflatBlockJ0B7,List.all_cons,List.all_nil,
    mode_checked_j0_m8,Bool.and_self]
theorem block_mass_checked_j0_b7 : blockMassCheck bflatBlockJ0B7 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
