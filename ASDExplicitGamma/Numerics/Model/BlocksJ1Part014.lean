module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ1Part000

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ1B14 : ModeBlockData :=
  ⟨⟨14, 15, (21871056647342076251/10000000000000000000000 : ℚ), (9696014758637698237/5000000000000000000000 : ℚ)⟩, [
    (14, modeDataJ1M15)], (17496845317873661/8000000000000000000 : ℚ)⟩

theorem block_entries_checked_j1_b14 : entryChecks 1 bflatBlockJ1B14.entries = true := by
  simp only [entryChecks,bflatBlockJ1B14,List.all_cons,List.all_nil,
    mode_checked_j1_m15,Bool.and_self]
theorem block_mass_checked_j1_b14 : blockMassCheck bflatBlockJ1B14 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
