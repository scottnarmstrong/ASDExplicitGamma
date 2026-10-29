module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ1Part001

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ1B20 : ModeBlockData :=
  ⟨⟨20, 21, (9915349800867095147/10000000000000000000000 : ℚ), (59481716429968879/62500000000000000000 : ℚ)⟩, [
    (20, modeDataJ1M21)], (4957674900433547573/5000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j1_b20 : entryChecks 1 bflatBlockJ1B20.entries = true := by
  simp only [entryChecks,bflatBlockJ1B20,List.all_cons,List.all_nil,
    mode_checked_j1_m21,Bool.and_self]
theorem block_mass_checked_j1_b20 : blockMassCheck bflatBlockJ1B20 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
