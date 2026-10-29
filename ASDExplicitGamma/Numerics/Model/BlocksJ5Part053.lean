module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ5Part003

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ5B53 : ModeBlockData :=
  ⟨⟨53, 54, (24881440129247782877/10000000000000000000000 : ℚ), (19588464770189341/5000000000000000000000 : ℚ)⟩, [
    (53, modeDataJ5M54)], (6220360032311945719/2500000000000000000000 : ℚ)⟩

theorem block_entries_checked_j5_b53 : entryChecks 5 bflatBlockJ5B53.entries = true := by
  simp only [entryChecks,bflatBlockJ5B53,List.all_cons,List.all_nil,
    mode_checked_j5_m54,Bool.and_self]
theorem block_mass_checked_j5_b53 : blockMassCheck bflatBlockJ5B53 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
