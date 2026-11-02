import ContextAssignmentLiteChunk00
import ContextAssignmentLiteChunk01
import ContextAssignmentLiteChunk02
import ContextAssignmentLiteChunk03
import ContextAssignmentLiteChunk04
import ContextAssignmentLiteChunk05
import ContextAssignmentLiteChunk06
import ContextAssignmentLiteChunk07
import ContextAssignmentLiteChunk08
import ContextAssignmentLiteChunk09
import ContextAssignmentLiteChunk10
import ContextAssignmentLiteChunk11
import ContextAssignmentLiteChunk12
import ContextAssignmentLiteChunk13
import ContextAssignmentLiteChunk14
import ContextAssignmentLiteChunk15
import ContextAssignmentLiteChunk16
import ContextAssignmentLiteChunk17
import ContextAssignmentLiteChunk18
import ContextAssignmentLiteChunk19
import ContextAssignmentLiteChunk20
import ContextAssignmentLiteChunk21
import ContextAssignmentLiteChunk22
import ContextAssignmentLiteChunk23
import ContextAssignmentLiteChunk24
import ContextAssignmentLiteChunk25

namespace Snake9.ContextLite92
theorem prefix_0 : prefixCheck 0 = true := rfl

theorem prefix_20 : prefixCheck 20 = true := by
  calc
    prefixCheck 20 = (prefixCheck 0 && chunkCheck 0 20) :=
      prefix_add 0 20
    _ = true := by rw [prefix_0,chunk_00]; rfl

theorem prefix_40 : prefixCheck 40 = true := by
  calc
    prefixCheck 40 = (prefixCheck 20 && chunkCheck 20 20) :=
      prefix_add 20 20
    _ = true := by rw [prefix_20,chunk_01]; rfl

theorem prefix_60 : prefixCheck 60 = true := by
  calc
    prefixCheck 60 = (prefixCheck 40 && chunkCheck 40 20) :=
      prefix_add 40 20
    _ = true := by rw [prefix_40,chunk_02]; rfl

theorem prefix_80 : prefixCheck 80 = true := by
  calc
    prefixCheck 80 = (prefixCheck 60 && chunkCheck 60 20) :=
      prefix_add 60 20
    _ = true := by rw [prefix_60,chunk_03]; rfl

theorem prefix_100 : prefixCheck 100 = true := by
  calc
    prefixCheck 100 = (prefixCheck 80 && chunkCheck 80 20) :=
      prefix_add 80 20
    _ = true := by rw [prefix_80,chunk_04]; rfl

theorem prefix_120 : prefixCheck 120 = true := by
  calc
    prefixCheck 120 = (prefixCheck 100 && chunkCheck 100 20) :=
      prefix_add 100 20
    _ = true := by rw [prefix_100,chunk_05]; rfl

theorem prefix_140 : prefixCheck 140 = true := by
  calc
    prefixCheck 140 = (prefixCheck 120 && chunkCheck 120 20) :=
      prefix_add 120 20
    _ = true := by rw [prefix_120,chunk_06]; rfl

theorem prefix_160 : prefixCheck 160 = true := by
  calc
    prefixCheck 160 = (prefixCheck 140 && chunkCheck 140 20) :=
      prefix_add 140 20
    _ = true := by rw [prefix_140,chunk_07]; rfl

theorem prefix_180 : prefixCheck 180 = true := by
  calc
    prefixCheck 180 = (prefixCheck 160 && chunkCheck 160 20) :=
      prefix_add 160 20
    _ = true := by rw [prefix_160,chunk_08]; rfl

theorem prefix_200 : prefixCheck 200 = true := by
  calc
    prefixCheck 200 = (prefixCheck 180 && chunkCheck 180 20) :=
      prefix_add 180 20
    _ = true := by rw [prefix_180,chunk_09]; rfl

theorem prefix_220 : prefixCheck 220 = true := by
  calc
    prefixCheck 220 = (prefixCheck 200 && chunkCheck 200 20) :=
      prefix_add 200 20
    _ = true := by rw [prefix_200,chunk_10]; rfl

theorem prefix_240 : prefixCheck 240 = true := by
  calc
    prefixCheck 240 = (prefixCheck 220 && chunkCheck 220 20) :=
      prefix_add 220 20
    _ = true := by rw [prefix_220,chunk_11]; rfl

theorem prefix_260 : prefixCheck 260 = true := by
  calc
    prefixCheck 260 = (prefixCheck 240 && chunkCheck 240 20) :=
      prefix_add 240 20
    _ = true := by rw [prefix_240,chunk_12]; rfl

theorem prefix_280 : prefixCheck 280 = true := by
  calc
    prefixCheck 280 = (prefixCheck 260 && chunkCheck 260 20) :=
      prefix_add 260 20
    _ = true := by rw [prefix_260,chunk_13]; rfl

theorem prefix_300 : prefixCheck 300 = true := by
  calc
    prefixCheck 300 = (prefixCheck 280 && chunkCheck 280 20) :=
      prefix_add 280 20
    _ = true := by rw [prefix_280,chunk_14]; rfl

theorem prefix_320 : prefixCheck 320 = true := by
  calc
    prefixCheck 320 = (prefixCheck 300 && chunkCheck 300 20) :=
      prefix_add 300 20
    _ = true := by rw [prefix_300,chunk_15]; rfl

theorem prefix_340 : prefixCheck 340 = true := by
  calc
    prefixCheck 340 = (prefixCheck 320 && chunkCheck 320 20) :=
      prefix_add 320 20
    _ = true := by rw [prefix_320,chunk_16]; rfl

theorem prefix_360 : prefixCheck 360 = true := by
  calc
    prefixCheck 360 = (prefixCheck 340 && chunkCheck 340 20) :=
      prefix_add 340 20
    _ = true := by rw [prefix_340,chunk_17]; rfl

theorem prefix_380 : prefixCheck 380 = true := by
  calc
    prefixCheck 380 = (prefixCheck 360 && chunkCheck 360 20) :=
      prefix_add 360 20
    _ = true := by rw [prefix_360,chunk_18]; rfl

theorem prefix_400 : prefixCheck 400 = true := by
  calc
    prefixCheck 400 = (prefixCheck 380 && chunkCheck 380 20) :=
      prefix_add 380 20
    _ = true := by rw [prefix_380,chunk_19]; rfl

theorem prefix_420 : prefixCheck 420 = true := by
  calc
    prefixCheck 420 = (prefixCheck 400 && chunkCheck 400 20) :=
      prefix_add 400 20
    _ = true := by rw [prefix_400,chunk_20]; rfl

theorem prefix_440 : prefixCheck 440 = true := by
  calc
    prefixCheck 440 = (prefixCheck 420 && chunkCheck 420 20) :=
      prefix_add 420 20
    _ = true := by rw [prefix_420,chunk_21]; rfl

theorem prefix_460 : prefixCheck 460 = true := by
  calc
    prefixCheck 460 = (prefixCheck 440 && chunkCheck 440 20) :=
      prefix_add 440 20
    _ = true := by rw [prefix_440,chunk_22]; rfl

theorem prefix_480 : prefixCheck 480 = true := by
  calc
    prefixCheck 480 = (prefixCheck 460 && chunkCheck 460 20) :=
      prefix_add 460 20
    _ = true := by rw [prefix_460,chunk_23]; rfl

theorem prefix_500 : prefixCheck 500 = true := by
  calc
    prefixCheck 500 = (prefixCheck 480 && chunkCheck 480 20) :=
      prefix_add 480 20
    _ = true := by rw [prefix_480,chunk_24]; rfl

theorem prefix_505 : prefixCheck 505 = true := by
  calc
    prefixCheck 505 = (prefixCheck 500 && chunkCheck 500 5) :=
      prefix_add 500 5
    _ = true := by rw [prefix_500,chunk_25]; rfl

theorem fast_checked : fastCheck = true := by
  rw [← prefix_full]
  exact prefix_505

theorem assignmentAt_true (di q : Nat) (hd : di < 505) (hq : q < 75) :
    assignmentAt di q = true := assignmentAt_of_fast fast_checked di q hd hq

#print axioms fast_checked
#print axioms assignmentAt_true
end Snake9.ContextLite92
