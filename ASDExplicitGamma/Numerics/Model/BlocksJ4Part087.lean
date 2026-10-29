module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ4Part013
public import ASDExplicitGamma.Numerics.Model.ModesJ4Part014

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ4B87 : ModeBlockData :=
  ⟨⟨221, 233, (40249240091896453141/5000000000000000000000 : ℚ), (1239563755699950343/10000000000000000000000 : ℚ)⟩, [
    (221, modeDataJ4M222),
    (222, modeDataJ4M223),
    (223, modeDataJ4M224),
    (224, modeDataJ4M225),
    (225, modeDataJ4M226),
    (226, modeDataJ4M227),
    (227, modeDataJ4M228),
    (228, modeDataJ4M229),
    (229, modeDataJ4M230),
    (230, modeDataJ4M231),
    (231, modeDataJ4M232),
    (232, modeDataJ4M233)], (8049848018379290627/1000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j4_b87 : entryChecks 4 bflatBlockJ4B87.entries = true := by
  simp only [entryChecks,bflatBlockJ4B87,List.all_cons,List.all_nil,
    mode_checked_j4_m222,
    mode_checked_j4_m223,
    mode_checked_j4_m224,
    mode_checked_j4_m225,
    mode_checked_j4_m226,
    mode_checked_j4_m227,
    mode_checked_j4_m228,
    mode_checked_j4_m229,
    mode_checked_j4_m230,
    mode_checked_j4_m231,
    mode_checked_j4_m232,
    mode_checked_j4_m233,Bool.and_self]
theorem block_mass_checked_j4_b87 : blockMassCheck bflatBlockJ4B87 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
