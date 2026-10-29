module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ5Part003

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ5B60 : ModeBlockData :=
  ⟨⟨60, 61, (6197145614907536283/2500000000000000000000 : ℚ), (4885512916071353/1250000000000000000000 : ℚ)⟩, [
    (60, modeDataJ5M61)], (24788582459630145131/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j5_b60 : entryChecks 5 bflatBlockJ5B60.entries = true := by
  simp only [entryChecks,bflatBlockJ5B60,List.all_cons,List.all_nil,
    mode_checked_j5_m61,Bool.and_self]
theorem block_mass_checked_j5_b60 : blockMassCheck bflatBlockJ5B60 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
