module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ5Part014
public import ASDExplicitGamma.Numerics.Model.ModesJ5Part015
public import ASDExplicitGamma.Numerics.Model.ModesJ5Part016

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ5B77 : ModeBlockData :=
  ⟨⟨236, 260, (45275825388684772019/1000000000000000000000 : ℚ), (39584673652434189/500000000000000000000 : ℚ)⟩, [
    (236, modeDataJ5M237),
    (237, modeDataJ5M238),
    (238, modeDataJ5M239),
    (239, modeDataJ5M240),
    (240, modeDataJ5M241),
    (241, modeDataJ5M242),
    (242, modeDataJ5M243),
    (243, modeDataJ5M244),
    (244, modeDataJ5M245),
    (245, modeDataJ5M246),
    (246, modeDataJ5M247),
    (247, modeDataJ5M248),
    (248, modeDataJ5M249),
    (249, modeDataJ5M250),
    (250, modeDataJ5M251),
    (251, modeDataJ5M252),
    (252, modeDataJ5M253),
    (253, modeDataJ5M254),
    (254, modeDataJ5M255),
    (255, modeDataJ5M256),
    (256, modeDataJ5M257),
    (257, modeDataJ5M258),
    (258, modeDataJ5M259),
    (259, modeDataJ5M260)], (226379126943423860083/5000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j5_b77 : entryChecks 5 bflatBlockJ5B77.entries = true := by
  simp only [entryChecks,bflatBlockJ5B77,List.all_cons,List.all_nil,
    mode_checked_j5_m237,
    mode_checked_j5_m238,
    mode_checked_j5_m239,
    mode_checked_j5_m240,
    mode_checked_j5_m241,
    mode_checked_j5_m242,
    mode_checked_j5_m243,
    mode_checked_j5_m244,
    mode_checked_j5_m245,
    mode_checked_j5_m246,
    mode_checked_j5_m247,
    mode_checked_j5_m248,
    mode_checked_j5_m249,
    mode_checked_j5_m250,
    mode_checked_j5_m251,
    mode_checked_j5_m252,
    mode_checked_j5_m253,
    mode_checked_j5_m254,
    mode_checked_j5_m255,
    mode_checked_j5_m256,
    mode_checked_j5_m257,
    mode_checked_j5_m258,
    mode_checked_j5_m259,
    mode_checked_j5_m260,Bool.and_self]
theorem block_mass_checked_j5_b77 : blockMassCheck bflatBlockJ5B77 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
