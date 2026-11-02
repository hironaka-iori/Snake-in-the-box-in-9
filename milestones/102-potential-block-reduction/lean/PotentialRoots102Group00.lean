import PotentialBlocks102

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Snake9.PotentialBlocks102
open Snake9.Potential99 Snake9.Balanced89

theorem completed_at_0 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (0+offset) =
      min 551 (value Completed.n5_5 offset) := by
  have hr : lookup Completed.roots 0 (.leaf 0) = Completed.n5_5 := by rfl
  simpa only [hr] using completed_block 0 offset hoff

#print axioms completed_at_0

theorem conditional_at_0 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (0+offset) =
      min 602 (value Conditional.n5_8 offset) := by
  have hr : lookup Conditional.roots 0 (.leaf 0) = Conditional.n5_8 := by rfl
  simpa only [hr] using conditional_block 0 offset hoff

#print axioms conditional_at_0

theorem completed_at_1 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (7776+offset) =
      min 551 (value Completed.n5_21 offset) := by
  have hr : lookup Completed.roots 1 (.leaf 0) = Completed.n5_21 := by rfl
  simpa only [hr] using completed_block 1 offset hoff

#print axioms completed_at_1

theorem conditional_at_1 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (7776+offset) =
      min 602 (value Conditional.n5_19 offset) := by
  have hr : lookup Conditional.roots 1 (.leaf 0) = Conditional.n5_19 := by rfl
  simpa only [hr] using conditional_block 1 offset hoff

#print axioms conditional_at_1

theorem completed_at_2 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (15552+offset) =
      min 551 (value Completed.n5_120 offset) := by
  have hr : lookup Completed.roots 2 (.leaf 0) = Completed.n5_120 := by rfl
  simpa only [hr] using completed_block 2 offset hoff

#print axioms completed_at_2

theorem conditional_at_2 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (15552+offset) =
      min 602 (value Conditional.n5_107 offset) := by
  have hr : lookup Conditional.roots 2 (.leaf 0) = Conditional.n5_107 := by rfl
  simpa only [hr] using conditional_block 2 offset hoff

#print axioms conditional_at_2

theorem completed_at_3 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (23328+offset) =
      min 551 (value Completed.n5_12 offset) := by
  have hr : lookup Completed.roots 3 (.leaf 0) = Completed.n5_12 := by rfl
  simpa only [hr] using completed_block 3 offset hoff

#print axioms completed_at_3

theorem conditional_at_3 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (23328+offset) =
      min 602 (value Conditional.n5_12 offset) := by
  have hr : lookup Conditional.roots 3 (.leaf 0) = Conditional.n5_12 := by rfl
  simpa only [hr] using conditional_block 3 offset hoff

#print axioms conditional_at_3

theorem completed_at_4 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (31104+offset) =
      min 551 (value Completed.n5_18 offset) := by
  have hr : lookup Completed.roots 4 (.leaf 0) = Completed.n5_18 := by rfl
  simpa only [hr] using completed_block 4 offset hoff

#print axioms completed_at_4

theorem conditional_at_4 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (31104+offset) =
      min 602 (value Conditional.n5_20 offset) := by
  have hr : lookup Conditional.roots 4 (.leaf 0) = Conditional.n5_20 := by rfl
  simpa only [hr] using conditional_block 4 offset hoff

#print axioms conditional_at_4

theorem completed_at_5 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (38880+offset) =
      min 551 (value Completed.n5_123 offset) := by
  have hr : lookup Completed.roots 5 (.leaf 0) = Completed.n5_123 := by rfl
  simpa only [hr] using completed_block 5 offset hoff

#print axioms completed_at_5

theorem conditional_at_5 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (38880+offset) =
      min 602 (value Conditional.n5_72 offset) := by
  have hr : lookup Conditional.roots 5 (.leaf 0) = Conditional.n5_72 := by rfl
  simpa only [hr] using conditional_block 5 offset hoff

#print axioms conditional_at_5

theorem completed_at_6 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (46656+offset) =
      min 551 (value Completed.n5_87 offset) := by
  have hr : lookup Completed.roots 6 (.leaf 0) = Completed.n5_87 := by rfl
  simpa only [hr] using completed_block 6 offset hoff

#print axioms completed_at_6

theorem conditional_at_6 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (46656+offset) =
      min 602 (value Conditional.n5_81 offset) := by
  have hr : lookup Conditional.roots 6 (.leaf 0) = Conditional.n5_81 := by rfl
  simpa only [hr] using conditional_block 6 offset hoff

#print axioms conditional_at_6

theorem completed_at_7 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (54432+offset) =
      min 551 (value Completed.n5_38 offset) := by
  have hr : lookup Completed.roots 7 (.leaf 0) = Completed.n5_38 := by rfl
  simpa only [hr] using completed_block 7 offset hoff

#print axioms completed_at_7

theorem conditional_at_7 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (54432+offset) =
      min 602 (value Conditional.n5_34 offset) := by
  have hr : lookup Conditional.roots 7 (.leaf 0) = Conditional.n5_34 := by rfl
  simpa only [hr] using conditional_block 7 offset hoff

#print axioms conditional_at_7

theorem completed_at_8 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (62208+offset) =
      min 551 (value Completed.n5_86 offset) := by
  have hr : lookup Completed.roots 8 (.leaf 0) = Completed.n5_86 := by rfl
  simpa only [hr] using completed_block 8 offset hoff

#print axioms completed_at_8

theorem conditional_at_8 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (62208+offset) =
      min 602 (value Conditional.n5_81 offset) := by
  have hr : lookup Conditional.roots 8 (.leaf 0) = Conditional.n5_81 := by rfl
  simpa only [hr] using conditional_block 8 offset hoff

#print axioms conditional_at_8

theorem completed_at_9 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (69984+offset) =
      min 551 (value Completed.n5_41 offset) := by
  have hr : lookup Completed.roots 9 (.leaf 0) = Completed.n5_41 := by rfl
  simpa only [hr] using completed_block 9 offset hoff

#print axioms completed_at_9

theorem conditional_at_9 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (69984+offset) =
      min 602 (value Conditional.n5_42 offset) := by
  have hr : lookup Conditional.roots 9 (.leaf 0) = Conditional.n5_42 := by rfl
  simpa only [hr] using conditional_block 9 offset hoff

#print axioms conditional_at_9

theorem completed_at_10 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (77760+offset) =
      min 551 (value Completed.n5_50 offset) := by
  have hr : lookup Completed.roots 10 (.leaf 0) = Completed.n5_50 := by rfl
  simpa only [hr] using completed_block 10 offset hoff

#print axioms completed_at_10

theorem conditional_at_10 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (77760+offset) =
      min 602 (value Conditional.n5_31 offset) := by
  have hr : lookup Conditional.roots 10 (.leaf 0) = Conditional.n5_31 := by rfl
  simpa only [hr] using conditional_block 10 offset hoff

#print axioms conditional_at_10

theorem completed_at_11 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (85536+offset) =
      min 551 (value Completed.n5_42 offset) := by
  have hr : lookup Completed.roots 11 (.leaf 0) = Completed.n5_42 := by rfl
  simpa only [hr] using completed_block 11 offset hoff

#print axioms completed_at_11

theorem conditional_at_11 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (85536+offset) =
      min 602 (value Conditional.n5_43 offset) := by
  have hr : lookup Conditional.roots 11 (.leaf 0) = Conditional.n5_43 := by rfl
  simpa only [hr] using conditional_block 11 offset hoff

#print axioms conditional_at_11

theorem completed_at_12 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (93312+offset) =
      min 551 (value Completed.n5_109 offset) := by
  have hr : lookup Completed.roots 12 (.leaf 0) = Completed.n5_109 := by rfl
  simpa only [hr] using completed_block 12 offset hoff

#print axioms completed_at_12

theorem conditional_at_12 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (93312+offset) =
      min 602 (value Conditional.n5_99 offset) := by
  have hr : lookup Conditional.roots 12 (.leaf 0) = Conditional.n5_99 := by rfl
  simpa only [hr] using conditional_block 12 offset hoff

#print axioms conditional_at_12

theorem completed_at_13 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (101088+offset) =
      min 551 (value Completed.n5_104 offset) := by
  have hr : lookup Completed.roots 13 (.leaf 0) = Completed.n5_104 := by rfl
  simpa only [hr] using completed_block 13 offset hoff

#print axioms completed_at_13

theorem conditional_at_13 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (101088+offset) =
      min 602 (value Conditional.n5_115 offset) := by
  have hr : lookup Conditional.roots 13 (.leaf 0) = Conditional.n5_115 := by rfl
  simpa only [hr] using conditional_block 13 offset hoff

#print axioms conditional_at_13

theorem completed_at_14 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (108864+offset) =
      min 551 (value Completed.n5_94 offset) := by
  have hr : lookup Completed.roots 14 (.leaf 0) = Completed.n5_94 := by rfl
  simpa only [hr] using completed_block 14 offset hoff

#print axioms completed_at_14

theorem conditional_at_14 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (108864+offset) =
      min 602 (value Conditional.n5_92 offset) := by
  have hr : lookup Conditional.roots 14 (.leaf 0) = Conditional.n5_92 := by rfl
  simpa only [hr] using conditional_block 14 offset hoff

#print axioms conditional_at_14

theorem completed_at_15 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (116640+offset) =
      min 551 (value Completed.n5_108 offset) := by
  have hr : lookup Completed.roots 15 (.leaf 0) = Completed.n5_108 := by rfl
  simpa only [hr] using completed_block 15 offset hoff

#print axioms completed_at_15

theorem conditional_at_15 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (116640+offset) =
      min 602 (value Conditional.n5_108 offset) := by
  have hr : lookup Conditional.roots 15 (.leaf 0) = Conditional.n5_108 := by rfl
  simpa only [hr] using conditional_block 15 offset hoff

#print axioms conditional_at_15

theorem completed_at_16 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (124416+offset) =
      min 551 (value Completed.n5_126 offset) := by
  have hr : lookup Completed.roots 16 (.leaf 0) = Completed.n5_126 := by rfl
  simpa only [hr] using completed_block 16 offset hoff

#print axioms completed_at_16

theorem conditional_at_16 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (124416+offset) =
      min 602 (value Conditional.n5_121 offset) := by
  have hr : lookup Conditional.roots 16 (.leaf 0) = Conditional.n5_121 := by rfl
  simpa only [hr] using conditional_block 16 offset hoff

#print axioms conditional_at_16

theorem completed_at_17 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (132192+offset) =
      min 551 (value Completed.n5_133 offset) := by
  have hr : lookup Completed.roots 17 (.leaf 0) = Completed.n5_133 := by rfl
  simpa only [hr] using completed_block 17 offset hoff

#print axioms completed_at_17

theorem conditional_at_17 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (132192+offset) =
      min 602 (value Conditional.n5_127 offset) := by
  have hr : lookup Conditional.roots 17 (.leaf 0) = Conditional.n5_127 := by rfl
  simpa only [hr] using conditional_block 17 offset hoff

#print axioms conditional_at_17

theorem completed_at_18 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (139968+offset) =
      min 551 (value Completed.n5_140 offset) := by
  have hr : lookup Completed.roots 18 (.leaf 0) = Completed.n5_140 := by rfl
  simpa only [hr] using completed_block 18 offset hoff

#print axioms completed_at_18

theorem conditional_at_18 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (139968+offset) =
      min 602 (value Conditional.n5_135 offset) := by
  have hr : lookup Conditional.roots 18 (.leaf 0) = Conditional.n5_135 := by rfl
  simpa only [hr] using conditional_block 18 offset hoff

#print axioms conditional_at_18

theorem completed_at_19 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (147744+offset) =
      min 551 (value Completed.n5_134 offset) := by
  have hr : lookup Completed.roots 19 (.leaf 0) = Completed.n5_134 := by rfl
  simpa only [hr] using completed_block 19 offset hoff

#print axioms completed_at_19

theorem conditional_at_19 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (147744+offset) =
      min 602 (value Conditional.n5_129 offset) := by
  have hr : lookup Conditional.roots 19 (.leaf 0) = Conditional.n5_129 := by rfl
  simpa only [hr] using conditional_block 19 offset hoff

#print axioms conditional_at_19

theorem completed_at_20 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (155520+offset) =
      min 551 (value Completed.n5_117 offset) := by
  have hr : lookup Completed.roots 20 (.leaf 0) = Completed.n5_117 := by rfl
  simpa only [hr] using completed_block 20 offset hoff

#print axioms completed_at_20

theorem conditional_at_20 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (155520+offset) =
      min 602 (value Conditional.n5_76 offset) := by
  have hr : lookup Conditional.roots 20 (.leaf 0) = Conditional.n5_76 := by rfl
  simpa only [hr] using conditional_block 20 offset hoff

#print axioms conditional_at_20

theorem completed_at_21 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (163296+offset) =
      min 551 (value Completed.n5_116 offset) := by
  have hr : lookup Completed.roots 21 (.leaf 0) = Completed.n5_116 := by rfl
  simpa only [hr] using completed_block 21 offset hoff

#print axioms completed_at_21

theorem conditional_at_21 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (163296+offset) =
      min 602 (value Conditional.n5_75 offset) := by
  have hr : lookup Conditional.roots 21 (.leaf 0) = Conditional.n5_75 := by rfl
  simpa only [hr] using conditional_block 21 offset hoff

#print axioms conditional_at_21

theorem completed_at_22 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (171072+offset) =
      min 551 (value Completed.n5_103 offset) := by
  have hr : lookup Completed.roots 22 (.leaf 0) = Completed.n5_103 := by rfl
  simpa only [hr] using completed_block 22 offset hoff

#print axioms completed_at_22

theorem conditional_at_22 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (171072+offset) =
      min 602 (value Conditional.n5_110 offset) := by
  have hr : lookup Conditional.roots 22 (.leaf 0) = Conditional.n5_110 := by rfl
  simpa only [hr] using conditional_block 22 offset hoff

#print axioms conditional_at_22

theorem completed_at_23 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (178848+offset) =
      min 551 (value Completed.n5_63 offset) := by
  have hr : lookup Completed.roots 23 (.leaf 0) = Completed.n5_63 := by rfl
  simpa only [hr] using completed_block 23 offset hoff

#print axioms completed_at_23

theorem conditional_at_23 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (178848+offset) =
      min 602 (value Conditional.n5_59 offset) := by
  have hr : lookup Conditional.roots 23 (.leaf 0) = Conditional.n5_59 := by rfl
  simpa only [hr] using conditional_block 23 offset hoff

#print axioms conditional_at_23

theorem completed_at_24 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (186624+offset) =
      min 551 (value Completed.n5_114 offset) := by
  have hr : lookup Completed.roots 24 (.leaf 0) = Completed.n5_114 := by rfl
  simpa only [hr] using completed_block 24 offset hoff

#print axioms completed_at_24

theorem conditional_at_24 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (186624+offset) =
      min 602 (value Conditional.n5_74 offset) := by
  have hr : lookup Conditional.roots 24 (.leaf 0) = Conditional.n5_74 := by rfl
  simpa only [hr] using conditional_block 24 offset hoff

#print axioms conditional_at_24

theorem completed_at_25 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (194400+offset) =
      min 551 (value Completed.n5_10 offset) := by
  have hr : lookup Completed.roots 25 (.leaf 0) = Completed.n5_10 := by rfl
  simpa only [hr] using completed_block 25 offset hoff

#print axioms completed_at_25

theorem conditional_at_25 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (194400+offset) =
      min 602 (value Conditional.n5_10 offset) := by
  have hr : lookup Conditional.roots 25 (.leaf 0) = Conditional.n5_10 := by rfl
  simpa only [hr] using conditional_block 25 offset hoff

#print axioms conditional_at_25

theorem completed_at_26 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (202176+offset) =
      min 551 (value Completed.n5_97 offset) := by
  have hr : lookup Completed.roots 26 (.leaf 0) = Completed.n5_97 := by rfl
  simpa only [hr] using completed_block 26 offset hoff

#print axioms completed_at_26

theorem conditional_at_26 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (202176+offset) =
      min 602 (value Conditional.n5_103 offset) := by
  have hr : lookup Conditional.roots 26 (.leaf 0) = Conditional.n5_103 := by rfl
  simpa only [hr] using conditional_block 26 offset hoff

#print axioms conditional_at_26

theorem completed_at_27 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (209952+offset) =
      min 551 (value Completed.n5_17 offset) := by
  have hr : lookup Completed.roots 27 (.leaf 0) = Completed.n5_17 := by rfl
  simpa only [hr] using completed_block 27 offset hoff

#print axioms completed_at_27

theorem conditional_at_27 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (209952+offset) =
      min 602 (value Conditional.n5_15 offset) := by
  have hr : lookup Conditional.roots 27 (.leaf 0) = Conditional.n5_15 := by rfl
  simpa only [hr] using conditional_block 27 offset hoff

#print axioms conditional_at_27

theorem completed_at_28 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (217728+offset) =
      min 551 (value Completed.n5_16 offset) := by
  have hr : lookup Completed.roots 28 (.leaf 0) = Completed.n5_16 := by rfl
  simpa only [hr] using completed_block 28 offset hoff

#print axioms completed_at_28

theorem conditional_at_28 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (217728+offset) =
      min 602 (value Conditional.n5_18 offset) := by
  have hr : lookup Conditional.roots 28 (.leaf 0) = Conditional.n5_18 := by rfl
  simpa only [hr] using conditional_block 28 offset hoff

#print axioms conditional_at_28

theorem completed_at_29 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (225504+offset) =
      min 551 (value Completed.n5_36 offset) := by
  have hr : lookup Completed.roots 29 (.leaf 0) = Completed.n5_36 := by rfl
  simpa only [hr] using completed_block 29 offset hoff

#print axioms completed_at_29

theorem conditional_at_29 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (225504+offset) =
      min 602 (value Conditional.n5_33 offset) := by
  have hr : lookup Conditional.roots 29 (.leaf 0) = Conditional.n5_33 := by rfl
  simpa only [hr] using conditional_block 29 offset hoff

#print axioms conditional_at_29

theorem completed_at_30 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (233280+offset) =
      min 551 (value Completed.n5_81 offset) := by
  have hr : lookup Completed.roots 30 (.leaf 0) = Completed.n5_81 := by rfl
  simpa only [hr] using completed_block 30 offset hoff

#print axioms completed_at_30

theorem conditional_at_30 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (233280+offset) =
      min 602 (value Conditional.n5_77 offset) := by
  have hr : lookup Conditional.roots 30 (.leaf 0) = Conditional.n5_77 := by rfl
  simpa only [hr] using conditional_block 30 offset hoff

#print axioms conditional_at_30

theorem completed_at_31 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (241056+offset) =
      min 551 (value Completed.n5_83 offset) := by
  have hr : lookup Completed.roots 31 (.leaf 0) = Completed.n5_83 := by rfl
  simpa only [hr] using completed_block 31 offset hoff

#print axioms completed_at_31

theorem conditional_at_31 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (241056+offset) =
      min 602 (value Conditional.n5_69 offset) := by
  have hr : lookup Conditional.roots 31 (.leaf 0) = Conditional.n5_69 := by rfl
  simpa only [hr] using conditional_block 31 offset hoff

#print axioms conditional_at_31

theorem completed_at_32 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (248832+offset) =
      min 551 (value Completed.n5_82 offset) := by
  have hr : lookup Completed.roots 32 (.leaf 0) = Completed.n5_82 := by rfl
  simpa only [hr] using completed_block 32 offset hoff

#print axioms completed_at_32

theorem conditional_at_32 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (248832+offset) =
      min 602 (value Conditional.n5_77 offset) := by
  have hr : lookup Conditional.roots 32 (.leaf 0) = Conditional.n5_77 := by rfl
  simpa only [hr] using conditional_block 32 offset hoff

#print axioms conditional_at_32

theorem completed_at_33 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (256608+offset) =
      min 551 (value Completed.n5_96 offset) := by
  have hr : lookup Completed.roots 33 (.leaf 0) = Completed.n5_96 := by rfl
  simpa only [hr] using completed_block 33 offset hoff

#print axioms completed_at_33

theorem conditional_at_33 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (256608+offset) =
      min 602 (value Conditional.n5_93 offset) := by
  have hr : lookup Conditional.roots 33 (.leaf 0) = Conditional.n5_93 := by rfl
  simpa only [hr] using conditional_block 33 offset hoff

#print axioms conditional_at_33

theorem completed_at_34 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (264384+offset) =
      min 551 (value Completed.n5_119 offset) := by
  have hr : lookup Completed.roots 34 (.leaf 0) = Completed.n5_119 := by rfl
  simpa only [hr] using completed_block 34 offset hoff

#print axioms completed_at_34

theorem conditional_at_34 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (264384+offset) =
      min 602 (value Conditional.n5_112 offset) := by
  have hr : lookup Conditional.roots 34 (.leaf 0) = Conditional.n5_112 := by rfl
  simpa only [hr] using conditional_block 34 offset hoff

#print axioms conditional_at_34

theorem completed_at_35 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (272160+offset) =
      min 551 (value Completed.n5_113 offset) := by
  have hr : lookup Completed.roots 35 (.leaf 0) = Completed.n5_113 := by rfl
  simpa only [hr] using completed_block 35 offset hoff

#print axioms completed_at_35

theorem conditional_at_35 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (272160+offset) =
      min 602 (value Conditional.n5_98 offset) := by
  have hr : lookup Conditional.roots 35 (.leaf 0) = Conditional.n5_98 := by rfl
  simpa only [hr] using conditional_block 35 offset hoff

#print axioms conditional_at_35

theorem completed_at_36 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (279936+offset) =
      min 551 (value Completed.n5_112 offset) := by
  have hr : lookup Completed.roots 36 (.leaf 0) = Completed.n5_112 := by rfl
  simpa only [hr] using completed_block 36 offset hoff

#print axioms completed_at_36

theorem conditional_at_36 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (279936+offset) =
      min 602 (value Conditional.n5_96 offset) := by
  have hr : lookup Conditional.roots 36 (.leaf 0) = Conditional.n5_96 := by rfl
  simpa only [hr] using conditional_block 36 offset hoff

#print axioms conditional_at_36

theorem completed_at_37 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (287712+offset) =
      min 551 (value Completed.n5_141 offset) := by
  have hr : lookup Completed.roots 37 (.leaf 0) = Completed.n5_141 := by rfl
  simpa only [hr] using completed_block 37 offset hoff

#print axioms completed_at_37

theorem conditional_at_37 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (287712+offset) =
      min 602 (value Conditional.n5_134 offset) := by
  have hr : lookup Conditional.roots 37 (.leaf 0) = Conditional.n5_134 := by rfl
  simpa only [hr] using conditional_block 37 offset hoff

#print axioms conditional_at_37

theorem completed_at_38 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (295488+offset) =
      min 551 (value Completed.n5_136 offset) := by
  have hr : lookup Completed.roots 38 (.leaf 0) = Completed.n5_136 := by rfl
  simpa only [hr] using completed_block 38 offset hoff

#print axioms completed_at_38

theorem conditional_at_38 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (295488+offset) =
      min 602 (value Conditional.n5_130 offset) := by
  have hr : lookup Conditional.roots 38 (.leaf 0) = Conditional.n5_130 := by rfl
  simpa only [hr] using conditional_block 38 offset hoff

#print axioms conditional_at_38

theorem completed_at_39 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (303264+offset) =
      min 551 (value Completed.n5_127 offset) := by
  have hr : lookup Completed.roots 39 (.leaf 0) = Completed.n5_127 := by rfl
  simpa only [hr] using completed_block 39 offset hoff

#print axioms completed_at_39

theorem conditional_at_39 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (303264+offset) =
      min 602 (value Conditional.n5_118 offset) := by
  have hr : lookup Conditional.roots 39 (.leaf 0) = Conditional.n5_118 := by rfl
  simpa only [hr] using conditional_block 39 offset hoff

#print axioms conditional_at_39

theorem completed_at_40 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (311040+offset) =
      min 551 (value Completed.n5_135 offset) := by
  have hr : lookup Completed.roots 40 (.leaf 0) = Completed.n5_135 := by rfl
  simpa only [hr] using completed_block 40 offset hoff

#print axioms completed_at_40

theorem conditional_at_40 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (311040+offset) =
      min 602 (value Conditional.n5_128 offset) := by
  have hr : lookup Conditional.roots 40 (.leaf 0) = Conditional.n5_128 := by rfl
  simpa only [hr] using conditional_block 40 offset hoff

#print axioms conditional_at_40

theorem completed_at_41 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (318816+offset) =
      min 551 (value Completed.n5_34 offset) := by
  have hr : lookup Completed.roots 41 (.leaf 0) = Completed.n5_34 := by rfl
  simpa only [hr] using completed_block 41 offset hoff

#print axioms completed_at_41

theorem conditional_at_41 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (318816+offset) =
      min 602 (value Conditional.n5_36 offset) := by
  have hr : lookup Conditional.roots 41 (.leaf 0) = Conditional.n5_36 := by rfl
  simpa only [hr] using conditional_block 41 offset hoff

#print axioms conditional_at_41

theorem completed_at_42 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (326592+offset) =
      min 551 (value Completed.n5_37 offset) := by
  have hr : lookup Completed.roots 42 (.leaf 0) = Completed.n5_37 := by rfl
  simpa only [hr] using completed_block 42 offset hoff

#print axioms completed_at_42

theorem conditional_at_42 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (326592+offset) =
      min 602 (value Conditional.n5_29 offset) := by
  have hr : lookup Conditional.roots 42 (.leaf 0) = Conditional.n5_29 := by rfl
  simpa only [hr] using conditional_block 42 offset hoff

#print axioms conditional_at_42

theorem completed_at_43 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (334368+offset) =
      min 551 (value Completed.n5_35 offset) := by
  have hr : lookup Completed.roots 43 (.leaf 0) = Completed.n5_35 := by rfl
  simpa only [hr] using completed_block 43 offset hoff

#print axioms completed_at_43

theorem conditional_at_43 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (334368+offset) =
      min 602 (value Conditional.n5_40 offset) := by
  have hr : lookup Conditional.roots 43 (.leaf 0) = Conditional.n5_40 := by rfl
  simpa only [hr] using conditional_block 43 offset hoff

#print axioms conditional_at_43

theorem completed_at_44 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (342144+offset) =
      min 551 (value Completed.n5_58 offset) := by
  have hr : lookup Completed.roots 44 (.leaf 0) = Completed.n5_58 := by rfl
  simpa only [hr] using completed_block 44 offset hoff

#print axioms completed_at_44

theorem conditional_at_44 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (342144+offset) =
      min 602 (value Conditional.n5_55 offset) := by
  have hr : lookup Conditional.roots 44 (.leaf 0) = Conditional.n5_55 := by rfl
  simpa only [hr] using conditional_block 44 offset hoff

#print axioms conditional_at_44

theorem completed_at_45 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (349920+offset) =
      min 551 (value Completed.n5_79 offset) := by
  have hr : lookup Completed.roots 45 (.leaf 0) = Completed.n5_79 := by rfl
  simpa only [hr] using completed_block 45 offset hoff

#print axioms completed_at_45

theorem conditional_at_45 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (349920+offset) =
      min 602 (value Conditional.n5_62 offset) := by
  have hr : lookup Conditional.roots 45 (.leaf 0) = Conditional.n5_62 := by rfl
  simpa only [hr] using conditional_block 45 offset hoff

#print axioms conditional_at_45

theorem completed_at_46 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (357696+offset) =
      min 551 (value Completed.n5_98 offset) := by
  have hr : lookup Completed.roots 46 (.leaf 0) = Completed.n5_98 := by rfl
  simpa only [hr] using completed_block 46 offset hoff

#print axioms completed_at_46

theorem conditional_at_46 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (357696+offset) =
      min 602 (value Conditional.n5_104 offset) := by
  have hr : lookup Conditional.roots 46 (.leaf 0) = Conditional.n5_104 := by rfl
  simpa only [hr] using conditional_block 46 offset hoff

#print axioms conditional_at_46

theorem completed_at_47 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (365472+offset) =
      min 551 (value Completed.n5_80 offset) := by
  have hr : lookup Completed.roots 47 (.leaf 0) = Completed.n5_80 := by rfl
  simpa only [hr] using completed_block 47 offset hoff

#print axioms completed_at_47

theorem conditional_at_47 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (365472+offset) =
      min 602 (value Conditional.n5_63 offset) := by
  have hr : lookup Conditional.roots 47 (.leaf 0) = Conditional.n5_63 := by rfl
  simpa only [hr] using conditional_block 47 offset hoff

#print axioms conditional_at_47

theorem completed_at_48 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (373248+offset) =
      min 551 (value Completed.n5_79 offset) := by
  have hr : lookup Completed.roots 48 (.leaf 0) = Completed.n5_79 := by rfl
  simpa only [hr] using completed_block 48 offset hoff

#print axioms completed_at_48

theorem conditional_at_48 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (373248+offset) =
      min 602 (value Conditional.n5_62 offset) := by
  have hr : lookup Conditional.roots 48 (.leaf 0) = Conditional.n5_62 := by rfl
  simpa only [hr] using conditional_block 48 offset hoff

#print axioms conditional_at_48

theorem completed_at_49 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (381024+offset) =
      min 551 (value Completed.n5_143 offset) := by
  have hr : lookup Completed.roots 49 (.leaf 0) = Completed.n5_143 := by rfl
  simpa only [hr] using completed_block 49 offset hoff

#print axioms completed_at_49

theorem conditional_at_49 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (381024+offset) =
      min 602 (value Conditional.n5_136 offset) := by
  have hr : lookup Conditional.roots 49 (.leaf 0) = Conditional.n5_136 := by rfl
  simpa only [hr] using conditional_block 49 offset hoff

#print axioms conditional_at_49

theorem completed_at_50 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (388800+offset) =
      min 551 (value Completed.n5_173 offset) := by
  have hr : lookup Completed.roots 50 (.leaf 0) = Completed.n5_173 := by rfl
  simpa only [hr] using completed_block 50 offset hoff

#print axioms completed_at_50

theorem conditional_at_50 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (388800+offset) =
      min 602 (value Conditional.n5_165 offset) := by
  have hr : lookup Conditional.roots 50 (.leaf 0) = Conditional.n5_165 := by rfl
  simpa only [hr] using conditional_block 50 offset hoff

#print axioms conditional_at_50

theorem completed_at_51 (offset : Nat) (hoff : offset < 7776) :
    Completed.potential (396576+offset) =
      min 551 (value Completed.n5_176 offset) := by
  have hr : lookup Completed.roots 51 (.leaf 0) = Completed.n5_176 := by rfl
  simpa only [hr] using completed_block 51 offset hoff

#print axioms completed_at_51

theorem conditional_at_51 (offset : Nat) (hoff : offset < 7776) :
    Conditional.potential (396576+offset) =
      min 602 (value Conditional.n5_170 offset) := by
  have hr : lookup Conditional.roots 51 (.leaf 0) = Conditional.n5_170 := by rfl
  simpa only [hr] using conditional_block 51 offset hoff

#print axioms conditional_at_51

end Snake9.PotentialBlocks102
