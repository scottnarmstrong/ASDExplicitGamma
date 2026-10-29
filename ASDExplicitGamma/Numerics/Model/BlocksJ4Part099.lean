module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ4Part025
public import ASDExplicitGamma.Numerics.Model.ModesJ4Part026

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ4B99 : ModeBlockData :=
  ⟨⟨406, 427, (1281970945484739429/10000000000000000000000 : ℚ), (524898856382199191/10000000000000000000000 : ℚ)⟩, [
    (406, modeDataJ4M407),
    (407, modeDataJ4M408),
    (408, modeDataJ4M409),
    (409, modeDataJ4M410),
    (410, modeDataJ4M411),
    (411, modeDataJ4M412),
    (412, modeDataJ4M413),
    (413, modeDataJ4M414),
    (414, modeDataJ4M415),
    (415, modeDataJ4M416),
    (416, modeDataJ4M417),
    (417, modeDataJ4M418),
    (418, modeDataJ4M419),
    (419, modeDataJ4M420),
    (420, modeDataJ4M421),
    (421, modeDataJ4M422),
    (422, modeDataJ4M423),
    (423, modeDataJ4M424),
    (424, modeDataJ4M425),
    (425, modeDataJ4M426),
    (426, modeDataJ4M427)], (80123184092796213/625000000000000000000 : ℚ)⟩

theorem block_entries_checked_j4_b99 : entryChecks 4 bflatBlockJ4B99.entries = true := by
  simp only [entryChecks,bflatBlockJ4B99,List.all_cons,List.all_nil,
    mode_checked_j4_m407,
    mode_checked_j4_m408,
    mode_checked_j4_m409,
    mode_checked_j4_m410,
    mode_checked_j4_m411,
    mode_checked_j4_m412,
    mode_checked_j4_m413,
    mode_checked_j4_m414,
    mode_checked_j4_m415,
    mode_checked_j4_m416,
    mode_checked_j4_m417,
    mode_checked_j4_m418,
    mode_checked_j4_m419,
    mode_checked_j4_m420,
    mode_checked_j4_m421,
    mode_checked_j4_m422,
    mode_checked_j4_m423,
    mode_checked_j4_m424,
    mode_checked_j4_m425,
    mode_checked_j4_m426,
    mode_checked_j4_m427,Bool.and_self]
theorem block_mass_checked_j4_b99 : blockMassCheck bflatBlockJ4B99 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
