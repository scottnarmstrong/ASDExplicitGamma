module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ3Part008

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ3B95 : ModeBlockData :=
  ⟨⟨139, 142, (1014800427892041649/10000000000000000000000 : ℚ), (654071530885220857/10000000000000000000000 : ℚ)⟩, [
    (139, modeDataJ3M140),
    (140, modeDataJ3M141),
    (141, modeDataJ3M142)], (507400213946020823/5000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j3_b95 : entryChecks 3 bflatBlockJ3B95.entries = true := by
  simp only [entryChecks,bflatBlockJ3B95,List.all_cons,List.all_nil,
    mode_checked_j3_m140,
    mode_checked_j3_m141,
    mode_checked_j3_m142,Bool.and_self]
theorem block_mass_checked_j3_b95 : blockMassCheck bflatBlockJ3B95 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
