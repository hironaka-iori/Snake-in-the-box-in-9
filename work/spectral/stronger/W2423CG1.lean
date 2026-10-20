import WinG1Gen
import W2423CInputs
/-! G1 decoding tables of `2423_fwd_s01234` (window [0, 1, 3, 7, 15, 31], alpha [2, 4, 2, 3]), generated from
wincert.Encoding by scripts/gen.py.  Untrusted hints, validated by the kernel checker. -/
namespace W2423C
open WinCNF W223G1
set_option maxRecDepth 100000
def ballL : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 53, 54, 55, 57, 59, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 85, 86, 87, 89, 91, 93, 94, 95, 96, 97, 98, 99, 101, 102, 103, 105, 107, 109, 110, 111, 113, 115, 119, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 149, 150, 151, 153, 155, 157, 158, 159, 160, 161, 162, 163, 165, 166, 167, 169, 171, 173, 174, 175, 177, 179, 183, 191, 192, 193, 194, 195, 197, 198, 199, 201, 203, 205, 206, 207, 209, 211, 215, 223, 225, 227, 231, 239, 256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266, 267, 268, 269, 270, 271, 272, 273, 274, 275, 277, 278, 279, 281, 283, 285, 286, 287, 288, 289, 290, 291, 293, 294, 295, 297, 299, 301, 302, 303, 305, 307, 311, 319, 320, 321, 322, 323, 325, 326, 327, 329, 331, 333, 334, 335, 337, 339, 343, 351, 353, 355, 359, 367, 384, 385, 386, 387, 389, 390, 391, 393, 395, 397, 398, 399, 401, 403, 407, 415, 417, 419, 423, 431, 449, 451, 455, 463]
def endsL : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 21, 22, 23, 25, 27, 29, 30, 31, 32, 33, 34, 35, 37, 38, 39, 41, 43, 45, 46, 47, 49, 51, 55, 63, 64, 65, 66, 67, 69, 70, 71, 73, 75, 77, 78, 79, 81, 83, 87, 95, 97, 99, 103, 111, 128, 129, 130, 131, 133, 134, 135, 137, 139, 141, 142, 143, 145, 147, 151, 159, 161, 163, 167, 175, 193, 195, 199, 207, 256, 257, 258, 259, 261, 262, 263, 265, 267, 269, 270, 271, 273, 275, 279, 287, 289, 291, 295, 303, 321, 323, 327, 335, 385, 387, 391, 399]
/-- endpoint_budget -/
def B0 : Block := ⟨373, 2, 116, [pos 257, pos 258, pos 259, pos 260, pos 261, pos 262, pos 263, pos 264, pos 265, pos 266, pos 267, pos 268, pos 269, pos 270, pos 271, pos 272, pos 273, pos 274, pos 275, pos 276, pos 277, pos 278, pos 279, pos 280, pos 281, pos 282, pos 283, pos 284, pos 285, pos 286, pos 287, pos 288, pos 289, pos 290, pos 291, pos 292, pos 293, pos 294, pos 295, pos 296, pos 297, pos 298, pos 299, pos 300, pos 301, pos 302, pos 303, pos 304, pos 305, pos 306, pos 307, pos 308, pos 309, pos 310, pos 311, pos 312, pos 313, pos 314, pos 315, pos 316, pos 317, pos 318, pos 319, pos 320, pos 321, pos 322, pos 323, pos 324, pos 325, pos 326, pos 327, pos 328, pos 329, pos 330, pos 331, pos 332, pos 333, pos 334, pos 335, pos 336, pos 337, pos 338, pos 339, pos 340, pos 341, pos 342, pos 343, pos 344, pos 345, pos 346, pos 347, pos 348, pos 349, pos 350, pos 351, pos 352, pos 353, pos 354, pos 355, pos 356, pos 357, pos 358, pos 359, pos 360, pos 361, pos 362, pos 363, pos 364, pos 365, pos 366, pos 367, pos 368, pos 369, pos 370, pos 371, pos 372]⟩
/-- alpha<=2@1 -/
def B1 : Block := ⟨605, 2, 21, [neg 14, neg 22, neg 38, neg 66, neg 110, neg 174, neg 26, neg 42, neg 70, neg 114, neg 178, neg 50, neg 78, neg 122, neg 186, neg 90, neg 134, neg 198, neg 150, neg 214, neg 234]⟩
/-- alpha>=2@1 -/
def B2 : Block := ⟨647, 19, 21, [pos 14, pos 22, pos 38, pos 66, pos 110, pos 174, pos 26, pos 42, pos 70, pos 114, pos 178, pos 50, pos 78, pos 122, pos 186, pos 90, pos 134, pos 198, pos 150, pos 214, pos 234]⟩
/-- alpha<=4@3 -/
def B3 : Block := ⟨1046, 4, 21, [neg 11, neg 19, neg 35, neg 63, neg 107, neg 171, neg 28, neg 44, neg 72, neg 116, neg 180, neg 52, neg 80, neg 124, neg 188, neg 92, neg 136, neg 200, neg 152, neg 216, neg 236]⟩
/-- alpha>=4@3 -/
def B4 : Block := ⟨1130, 17, 21, [pos 11, pos 19, pos 35, pos 63, pos 107, pos 171, pos 28, pos 44, pos 72, pos 116, pos 180, pos 52, pos 80, pos 124, pos 188, pos 92, pos 136, pos 200, pos 152, pos 216, pos 236]⟩
/-- alpha<=2@7 -/
def B5 : Block := ⟨1487, 2, 21, [neg 5, neg 23, neg 39, neg 67, neg 111, neg 175, neg 22, neg 38, neg 66, neg 110, neg 174, neg 55, neg 83, neg 127, neg 191, neg 95, neg 139, neg 203, neg 155, neg 219, neg 239]⟩
/-- alpha>=2@7 -/
def B6 : Block := ⟨1529, 19, 21, [pos 5, pos 23, pos 39, pos 67, pos 111, pos 175, pos 22, pos 38, pos 66, pos 110, pos 174, pos 55, pos 83, pos 127, pos 191, pos 95, pos 139, pos 203, pos 155, pos 219, pos 239]⟩
/-- alpha<=3@15 -/
def B7 : Block := ⟨1928, 3, 21, [neg 13, neg 11, neg 47, neg 75, neg 119, neg 183, neg 10, neg 46, neg 74, neg 118, neg 182, neg 44, neg 72, neg 116, neg 180, neg 100, neg 144, neg 208, neg 160, neg 224, neg 244]⟩
/-- alpha>=3@15 -/
def B8 : Block := ⟨1991, 18, 21, [pos 13, pos 11, pos 47, pos 75, pos 119, pos 183, pos 10, pos 46, pos 74, pos 118, pos 182, pos 44, pos 72, pos 116, pos 180, pos 100, pos 144, pos 208, pos 160, pos 224, pos 244]⟩
def blocks : List Block := [B0, B1, B2, B3, B4, B5, B6, B7, B8]
def T : Tables := ⟨256, 116, ballL, endsL, [0, 1, 3, 7, 15, 31], blocks⟩
theorem blocksOK_T : blocksOK T = true := by decide +kernel
end W2423C
