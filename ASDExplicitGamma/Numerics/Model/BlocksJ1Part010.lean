module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ1Part000

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ1B10 : ModeBlockData :=
  ⟨⟨10, 11, (33520798189270404369/5000000000000000000000 : ℚ), (40200434696297815369/10000000000000000000000 : ℚ)⟩, [
    (10, modeDataJ1M11)], (67041596378540808737/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j1_b10 : entryChecks 1 bflatBlockJ1B10.entries = true := by
  simp only [entryChecks,bflatBlockJ1B10,List.all_cons,List.all_nil,
    mode_checked_j1_m11,Bool.and_self]
theorem block_mass_checked_j1_b10 : blockMassCheck bflatBlockJ1B10 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
