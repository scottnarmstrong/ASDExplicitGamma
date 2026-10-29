module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ4Part009

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ4B79 : ModeBlockData :=
  ⟨⟨145, 153, (28572149336334209007/1250000000000000000000 : ℚ), (802140359795697821/5000000000000000000000 : ℚ)⟩, [
    (145, modeDataJ4M146),
    (146, modeDataJ4M147),
    (147, modeDataJ4M148),
    (148, modeDataJ4M149),
    (149, modeDataJ4M150),
    (150, modeDataJ4M151),
    (151, modeDataJ4M152),
    (152, modeDataJ4M153)], (14286074668167104503/625000000000000000000 : ℚ)⟩

theorem block_entries_checked_j4_b79 : entryChecks 4 bflatBlockJ4B79.entries = true := by
  simp only [entryChecks,bflatBlockJ4B79,List.all_cons,List.all_nil,
    mode_checked_j4_m146,
    mode_checked_j4_m147,
    mode_checked_j4_m148,
    mode_checked_j4_m149,
    mode_checked_j4_m150,
    mode_checked_j4_m151,
    mode_checked_j4_m152,
    mode_checked_j4_m153,Bool.and_self]
theorem block_mass_checked_j4_b79 : blockMassCheck bflatBlockJ4B79 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
