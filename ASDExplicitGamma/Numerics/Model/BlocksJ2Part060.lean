module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ2Part003

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ2B60 : ModeBlockData :=
  ⟨⟨60, 61, (1181969110036090003/10000000000000000000000 : ℚ), (282727883670773803/2500000000000000000000 : ℚ)⟩, [
    (60, modeDataJ2M61)], (590984555018045001/5000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j2_b60 : entryChecks 2 bflatBlockJ2B60.entries = true := by
  simp only [entryChecks,bflatBlockJ2B60,List.all_cons,List.all_nil,
    mode_checked_j2_m61,Bool.and_self]
theorem block_mass_checked_j2_b60 : blockMassCheck bflatBlockJ2B60 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
