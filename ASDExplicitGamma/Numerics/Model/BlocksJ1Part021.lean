module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ1Part001

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ1B21 : ModeBlockData :=
  ⟨⟨21, 22, (8987587356409363357/10000000000000000000000 : ℚ), (8642673262701959797/10000000000000000000000 : ℚ)⟩, [
    (21, modeDataJ1M22)], (2246896839102340839/2500000000000000000000 : ℚ)⟩

theorem block_entries_checked_j1_b21 : entryChecks 1 bflatBlockJ1B21.entries = true := by
  simp only [entryChecks,bflatBlockJ1B21,List.all_cons,List.all_nil,
    mode_checked_j1_m22,Bool.and_self]
theorem block_mass_checked_j1_b21 : blockMassCheck bflatBlockJ1B21 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
