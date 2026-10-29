module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ4Part008

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ4B77 : ModeBlockData :=
  ⟨⟨131, 138, (60263059754402459817/2500000000000000000000 : ℚ), (1554742323768238767/10000000000000000000000 : ℚ)⟩, [
    (131, modeDataJ4M132),
    (132, modeDataJ4M133),
    (133, modeDataJ4M134),
    (134, modeDataJ4M135),
    (135, modeDataJ4M136),
    (136, modeDataJ4M137),
    (137, modeDataJ4M138)], (241052239017609839261/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j4_b77 : entryChecks 4 bflatBlockJ4B77.entries = true := by
  simp only [entryChecks,bflatBlockJ4B77,List.all_cons,List.all_nil,
    mode_checked_j4_m132,
    mode_checked_j4_m133,
    mode_checked_j4_m134,
    mode_checked_j4_m135,
    mode_checked_j4_m136,
    mode_checked_j4_m137,
    mode_checked_j4_m138,Bool.and_self]
theorem block_mass_checked_j4_b77 : blockMassCheck bflatBlockJ4B77 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
