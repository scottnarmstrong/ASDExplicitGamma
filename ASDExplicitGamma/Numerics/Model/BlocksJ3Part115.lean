module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ3Part013

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ3B115 : ModeBlockData :=
  ⟨⟨219, 224, (220400376450923337/5000000000000000000000 : ℚ), (421583822450387629/10000000000000000000000 : ℚ)⟩, [
    (219, modeDataJ3M220),
    (220, modeDataJ3M221),
    (221, modeDataJ3M222),
    (222, modeDataJ3M223),
    (223, modeDataJ3M224)], (440800752901846669/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j3_b115 : entryChecks 3 bflatBlockJ3B115.entries = true := by
  simp only [entryChecks,bflatBlockJ3B115,List.all_cons,List.all_nil,
    mode_checked_j3_m220,
    mode_checked_j3_m221,
    mode_checked_j3_m222,
    mode_checked_j3_m223,
    mode_checked_j3_m224,Bool.and_self]
theorem block_mass_checked_j3_b115 : blockMassCheck bflatBlockJ3B115 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
