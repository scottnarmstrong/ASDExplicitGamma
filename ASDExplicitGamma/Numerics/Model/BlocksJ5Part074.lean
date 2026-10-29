module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ5Part011
public import ASDExplicitGamma.Numerics.Model.ModesJ5Part012

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ5B74 : ModeBlockData :=
  ⟨⟨176, 194, (96628079261321205519/2500000000000000000000 : ℚ), (128581543935495921/2000000000000000000000 : ℚ)⟩, [
    (176, modeDataJ5M177),
    (177, modeDataJ5M178),
    (178, modeDataJ5M179),
    (179, modeDataJ5M180),
    (180, modeDataJ5M181),
    (181, modeDataJ5M182),
    (182, modeDataJ5M183),
    (183, modeDataJ5M184),
    (184, modeDataJ5M185),
    (185, modeDataJ5M186),
    (186, modeDataJ5M187),
    (187, modeDataJ5M188),
    (188, modeDataJ5M189),
    (189, modeDataJ5M190),
    (190, modeDataJ5M191),
    (191, modeDataJ5M192),
    (192, modeDataJ5M193),
    (193, modeDataJ5M194)], (193256158522642411029/5000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j5_b74 : entryChecks 5 bflatBlockJ5B74.entries = true := by
  simp only [entryChecks,bflatBlockJ5B74,List.all_cons,List.all_nil,
    mode_checked_j5_m177,
    mode_checked_j5_m178,
    mode_checked_j5_m179,
    mode_checked_j5_m180,
    mode_checked_j5_m181,
    mode_checked_j5_m182,
    mode_checked_j5_m183,
    mode_checked_j5_m184,
    mode_checked_j5_m185,
    mode_checked_j5_m186,
    mode_checked_j5_m187,
    mode_checked_j5_m188,
    mode_checked_j5_m189,
    mode_checked_j5_m190,
    mode_checked_j5_m191,
    mode_checked_j5_m192,
    mode_checked_j5_m193,
    mode_checked_j5_m194,Bool.and_self]
theorem block_mass_checked_j5_b74 : blockMassCheck bflatBlockJ5B74 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
