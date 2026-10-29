module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ1Part001

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ1B27 : ModeBlockData :=
  ⟨⟨27, 28, (2689711810393174651/5000000000000000000000 : ℚ), (1317107849724042963/2500000000000000000000 : ℚ)⟩, [
    (27, modeDataJ1M28)], (5379423620786349301/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j1_b27 : entryChecks 1 bflatBlockJ1B27.entries = true := by
  simp only [entryChecks,bflatBlockJ1B27,List.all_cons,List.all_nil,
    mode_checked_j1_m28,Bool.and_self]
theorem block_mass_checked_j1_b27 : blockMassCheck bflatBlockJ1B27 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
