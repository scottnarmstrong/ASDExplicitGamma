module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ3Part005

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ3B79 : ModeBlockData :=
  ⟨⟨94, 96, (1840314890655526619/2500000000000000000000 : ℚ), (1085673352092976321/10000000000000000000000 : ℚ)⟩, [
    (94, modeDataJ3M95),
    (95, modeDataJ3M96)], (3680629781311053237/5000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j3_b79 : entryChecks 3 bflatBlockJ3B79.entries = true := by
  simp only [entryChecks,bflatBlockJ3B79,List.all_cons,List.all_nil,
    mode_checked_j3_m95,
    mode_checked_j3_m96,Bool.and_self]
theorem block_mass_checked_j3_b79 : blockMassCheck bflatBlockJ3B79 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
