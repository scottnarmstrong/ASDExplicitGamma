module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ3Part000

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ3B7 : ModeBlockData :=
  ⟨⟨7, 8, (221628452521587529591/10000000000000000000000 : ℚ), (3152197438228532743/10000000000000000000000 : ℚ)⟩, [
    (7, modeDataJ3M8)], (22162845252158752959/1000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j3_b7 : entryChecks 3 bflatBlockJ3B7.entries = true := by
  simp only [entryChecks,bflatBlockJ3B7,List.all_cons,List.all_nil,
    mode_checked_j3_m8,Bool.and_self]
theorem block_mass_checked_j3_b7 : blockMassCheck bflatBlockJ3B7 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
