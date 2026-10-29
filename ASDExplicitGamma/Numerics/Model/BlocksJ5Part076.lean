module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ5Part013
public import ASDExplicitGamma.Numerics.Model.ModesJ5Part014

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ5B76 : ModeBlockData :=
  ⟨⟨214, 236, (109274424309875498651/2500000000000000000000 : ℚ), (187256933282001069/2500000000000000000000 : ℚ)⟩, [
    (214, modeDataJ5M215),
    (215, modeDataJ5M216),
    (216, modeDataJ5M217),
    (217, modeDataJ5M218),
    (218, modeDataJ5M219),
    (219, modeDataJ5M220),
    (220, modeDataJ5M221),
    (221, modeDataJ5M222),
    (222, modeDataJ5M223),
    (223, modeDataJ5M224),
    (224, modeDataJ5M225),
    (225, modeDataJ5M226),
    (226, modeDataJ5M227),
    (227, modeDataJ5M228),
    (228, modeDataJ5M229),
    (229, modeDataJ5M230),
    (230, modeDataJ5M231),
    (231, modeDataJ5M232),
    (232, modeDataJ5M233),
    (233, modeDataJ5M234),
    (234, modeDataJ5M235),
    (235, modeDataJ5M236)], (218548848619750997291/5000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j5_b76 : entryChecks 5 bflatBlockJ5B76.entries = true := by
  simp only [entryChecks,bflatBlockJ5B76,List.all_cons,List.all_nil,
    mode_checked_j5_m215,
    mode_checked_j5_m216,
    mode_checked_j5_m217,
    mode_checked_j5_m218,
    mode_checked_j5_m219,
    mode_checked_j5_m220,
    mode_checked_j5_m221,
    mode_checked_j5_m222,
    mode_checked_j5_m223,
    mode_checked_j5_m224,
    mode_checked_j5_m225,
    mode_checked_j5_m226,
    mode_checked_j5_m227,
    mode_checked_j5_m228,
    mode_checked_j5_m229,
    mode_checked_j5_m230,
    mode_checked_j5_m231,
    mode_checked_j5_m232,
    mode_checked_j5_m233,
    mode_checked_j5_m234,
    mode_checked_j5_m235,
    mode_checked_j5_m236,Bool.and_self]
theorem block_mass_checked_j5_b76 : blockMassCheck bflatBlockJ5B76 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
