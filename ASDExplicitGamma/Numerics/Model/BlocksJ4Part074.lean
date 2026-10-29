module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ4Part007

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ4B74 : ModeBlockData :=
  ⟨⟨112, 118, (64155729688136903747/2500000000000000000000 : ℚ), (188436083400452949/1250000000000000000000 : ℚ)⟩, [
    (112, modeDataJ4M113),
    (113, modeDataJ4M114),
    (114, modeDataJ4M115),
    (115, modeDataJ4M116),
    (116, modeDataJ4M117),
    (117, modeDataJ4M118)], (128311459376273807491/5000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j4_b74 : entryChecks 4 bflatBlockJ4B74.entries = true := by
  simp only [entryChecks,bflatBlockJ4B74,List.all_cons,List.all_nil,
    mode_checked_j4_m113,
    mode_checked_j4_m114,
    mode_checked_j4_m115,
    mode_checked_j4_m116,
    mode_checked_j4_m117,
    mode_checked_j4_m118,Bool.and_self]
theorem block_mass_checked_j4_b74 : blockMassCheck bflatBlockJ4B74 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
