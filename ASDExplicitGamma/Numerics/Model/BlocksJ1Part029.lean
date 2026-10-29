module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ1Part001

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ1B29 : ModeBlockData :=
  ⟨⟨29, 30, (4661032807393244559/10000000000000000000000 : ℚ), (2288924765934836877/5000000000000000000000 : ℚ)⟩, [
    (29, modeDataJ1M30)], (2330516403696622279/5000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j1_b29 : entryChecks 1 bflatBlockJ1B29.entries = true := by
  simp only [entryChecks,bflatBlockJ1B29,List.all_cons,List.all_nil,
    mode_checked_j1_m30,Bool.and_self]
theorem block_mass_checked_j1_b29 : blockMassCheck bflatBlockJ1B29 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
