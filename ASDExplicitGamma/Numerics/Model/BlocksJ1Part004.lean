module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ1Part000

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ1B4 : ModeBlockData :=
  ⟨⟨4, 5, (20014470661807887301/200000000000000000000 : ℚ), (101196420753162451/6250000000000000000 : ℚ)⟩, [
    (4, modeDataJ1M5)], (1000723533090394365049/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j1_b4 : entryChecks 1 bflatBlockJ1B4.entries = true := by
  simp only [entryChecks,bflatBlockJ1B4,List.all_cons,List.all_nil,
    mode_checked_j1_m5,Bool.and_self]
theorem block_mass_checked_j1_b4 : blockMassCheck bflatBlockJ1B4 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
