module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ5Part006
public import ASDExplicitGamma.Numerics.Model.ModesJ5Part007

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ5B69 : ModeBlockData :=
  ⟨⟨107, 118, (261418873756446751771/10000000000000000000000 : ℚ), (418617669870956551/10000000000000000000000 : ℚ)⟩, [
    (107, modeDataJ5M108),
    (108, modeDataJ5M109),
    (109, modeDataJ5M110),
    (110, modeDataJ5M111),
    (111, modeDataJ5M112),
    (112, modeDataJ5M113),
    (113, modeDataJ5M114),
    (114, modeDataJ5M115),
    (115, modeDataJ5M116),
    (116, modeDataJ5M117),
    (117, modeDataJ5M118)], (3267735921955584397/125000000000000000000 : ℚ)⟩

theorem block_entries_checked_j5_b69 : entryChecks 5 bflatBlockJ5B69.entries = true := by
  simp only [entryChecks,bflatBlockJ5B69,List.all_cons,List.all_nil,
    mode_checked_j5_m108,
    mode_checked_j5_m109,
    mode_checked_j5_m110,
    mode_checked_j5_m111,
    mode_checked_j5_m112,
    mode_checked_j5_m113,
    mode_checked_j5_m114,
    mode_checked_j5_m115,
    mode_checked_j5_m116,
    mode_checked_j5_m117,
    mode_checked_j5_m118,Bool.and_self]
theorem block_mass_checked_j5_b69 : blockMassCheck bflatBlockJ5B69 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
