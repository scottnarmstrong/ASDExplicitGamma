module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ3Part003

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ3B56 : ModeBlockData :=
  ⟨⟨56, 57, (62928789075362602351/10000000000000000000000 : ℚ), (764113661538186261/5000000000000000000000 : ℚ)⟩, [
    (56, modeDataJ3M57)], (1258575781507252047/200000000000000000000 : ℚ)⟩

theorem block_entries_checked_j3_b56 : entryChecks 3 bflatBlockJ3B56.entries = true := by
  simp only [entryChecks,bflatBlockJ3B56,List.all_cons,List.all_nil,
    mode_checked_j3_m57,Bool.and_self]
theorem block_mass_checked_j3_b56 : blockMassCheck bflatBlockJ3B56 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
