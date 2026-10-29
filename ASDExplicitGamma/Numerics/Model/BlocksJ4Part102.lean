module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ4Part029
public import ASDExplicitGamma.Numerics.Model.ModesJ4Part030

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ4B102 : ModeBlockData :=
  ⟨⟨472, 496, (702366037721206657/10000000000000000000000 : ℚ), (218025540506013651/5000000000000000000000 : ℚ)⟩, [
    (472, modeDataJ4M473),
    (473, modeDataJ4M474),
    (474, modeDataJ4M475),
    (475, modeDataJ4M476),
    (476, modeDataJ4M477),
    (477, modeDataJ4M478),
    (478, modeDataJ4M479),
    (479, modeDataJ4M480),
    (480, modeDataJ4M481),
    (481, modeDataJ4M482),
    (482, modeDataJ4M483),
    (483, modeDataJ4M484),
    (484, modeDataJ4M485),
    (485, modeDataJ4M486),
    (486, modeDataJ4M487),
    (487, modeDataJ4M488),
    (488, modeDataJ4M489),
    (489, modeDataJ4M490),
    (490, modeDataJ4M491),
    (491, modeDataJ4M492),
    (492, modeDataJ4M493),
    (493, modeDataJ4M494),
    (494, modeDataJ4M495),
    (495, modeDataJ4M496)], (702366037721206633/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j4_b102 : entryChecks 4 bflatBlockJ4B102.entries = true := by
  simp only [entryChecks,bflatBlockJ4B102,List.all_cons,List.all_nil,
    mode_checked_j4_m473,
    mode_checked_j4_m474,
    mode_checked_j4_m475,
    mode_checked_j4_m476,
    mode_checked_j4_m477,
    mode_checked_j4_m478,
    mode_checked_j4_m479,
    mode_checked_j4_m480,
    mode_checked_j4_m481,
    mode_checked_j4_m482,
    mode_checked_j4_m483,
    mode_checked_j4_m484,
    mode_checked_j4_m485,
    mode_checked_j4_m486,
    mode_checked_j4_m487,
    mode_checked_j4_m488,
    mode_checked_j4_m489,
    mode_checked_j4_m490,
    mode_checked_j4_m491,
    mode_checked_j4_m492,
    mode_checked_j4_m493,
    mode_checked_j4_m494,
    mode_checked_j4_m495,
    mode_checked_j4_m496,Bool.and_self]
theorem block_mass_checked_j4_b102 : blockMassCheck bflatBlockJ4B102 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
