module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ3Part001

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ3B28 : ModeBlockData :=
  ⟨⟨28, 29, (20647440330817720573/1250000000000000000000 : ℚ), (32793009073315219/125000000000000000000 : ℚ)⟩, [
    (28, modeDataJ3M29)], (165179522646541764583/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j3_b28 : entryChecks 3 bflatBlockJ3B28.entries = true := by
  simp only [entryChecks,bflatBlockJ3B28,List.all_cons,List.all_nil,
    mode_checked_j3_m29,Bool.and_self]
theorem block_mass_checked_j3_b28 : blockMassCheck bflatBlockJ3B28 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
