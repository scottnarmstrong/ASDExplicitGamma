module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ4Part015
public import ASDExplicitGamma.Numerics.Model.ModesJ4Part016

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ4B89 : ModeBlockData :=
  ⟨⟨245, 258, (22655730670162222877/5000000000000000000000 : ℚ), (107010292697473671/1000000000000000000000 : ℚ)⟩, [
    (245, modeDataJ4M246),
    (246, modeDataJ4M247),
    (247, modeDataJ4M248),
    (248, modeDataJ4M249),
    (249, modeDataJ4M250),
    (250, modeDataJ4M251),
    (251, modeDataJ4M252),
    (252, modeDataJ4M253),
    (253, modeDataJ4M254),
    (254, modeDataJ4M255),
    (255, modeDataJ4M256),
    (256, modeDataJ4M257),
    (257, modeDataJ4M258)], (45311461340324445741/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j4_b89 : entryChecks 4 bflatBlockJ4B89.entries = true := by
  simp only [entryChecks,bflatBlockJ4B89,List.all_cons,List.all_nil,
    mode_checked_j4_m246,
    mode_checked_j4_m247,
    mode_checked_j4_m248,
    mode_checked_j4_m249,
    mode_checked_j4_m250,
    mode_checked_j4_m251,
    mode_checked_j4_m252,
    mode_checked_j4_m253,
    mode_checked_j4_m254,
    mode_checked_j4_m255,
    mode_checked_j4_m256,
    mode_checked_j4_m257,
    mode_checked_j4_m258,Bool.and_self]
theorem block_mass_checked_j4_b89 : blockMassCheck bflatBlockJ4B89 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
