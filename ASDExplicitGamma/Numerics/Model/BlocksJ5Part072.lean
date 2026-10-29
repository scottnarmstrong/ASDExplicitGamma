module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ5Part009

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ5B72 : ModeBlockData :=
  ⟨⟨144, 159, (339661171733813542187/10000000000000000000000 : ℚ), (2163197985269647/39062500000000000000 : ℚ)⟩, [
    (144, modeDataJ5M145),
    (145, modeDataJ5M146),
    (146, modeDataJ5M147),
    (147, modeDataJ5M148),
    (148, modeDataJ5M149),
    (149, modeDataJ5M150),
    (150, modeDataJ5M151),
    (151, modeDataJ5M152),
    (152, modeDataJ5M153),
    (153, modeDataJ5M154),
    (154, modeDataJ5M155),
    (155, modeDataJ5M156),
    (156, modeDataJ5M157),
    (157, modeDataJ5M158),
    (158, modeDataJ5M159)], (84915292933453385543/2500000000000000000000 : ℚ)⟩

theorem block_entries_checked_j5_b72 : entryChecks 5 bflatBlockJ5B72.entries = true := by
  simp only [entryChecks,bflatBlockJ5B72,List.all_cons,List.all_nil,
    mode_checked_j5_m145,
    mode_checked_j5_m146,
    mode_checked_j5_m147,
    mode_checked_j5_m148,
    mode_checked_j5_m149,
    mode_checked_j5_m150,
    mode_checked_j5_m151,
    mode_checked_j5_m152,
    mode_checked_j5_m153,
    mode_checked_j5_m154,
    mode_checked_j5_m155,
    mode_checked_j5_m156,
    mode_checked_j5_m157,
    mode_checked_j5_m158,
    mode_checked_j5_m159,Bool.and_self]
theorem block_mass_checked_j5_b72 : blockMassCheck bflatBlockJ5B72 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
