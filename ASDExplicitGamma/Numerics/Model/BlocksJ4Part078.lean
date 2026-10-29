module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ4Part008
public import ASDExplicitGamma.Numerics.Model.ModesJ4Part009

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ4B78 : ModeBlockData :=
  ⟨⟨138, 145, (110446948412458015023/5000000000000000000000 : ℚ), (1481496506448540461/10000000000000000000000 : ℚ)⟩, [
    (138, modeDataJ4M139),
    (139, modeDataJ4M140),
    (140, modeDataJ4M141),
    (141, modeDataJ4M142),
    (142, modeDataJ4M143),
    (143, modeDataJ4M144),
    (144, modeDataJ4M145)], (220893896824916030039/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j4_b78 : entryChecks 4 bflatBlockJ4B78.entries = true := by
  simp only [entryChecks,bflatBlockJ4B78,List.all_cons,List.all_nil,
    mode_checked_j4_m139,
    mode_checked_j4_m140,
    mode_checked_j4_m141,
    mode_checked_j4_m142,
    mode_checked_j4_m143,
    mode_checked_j4_m144,
    mode_checked_j4_m145,Bool.and_self]
theorem block_mass_checked_j4_b78 : blockMassCheck bflatBlockJ4B78 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
