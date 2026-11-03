# Concrete data parser revision

The first parser passed the grouped certificate source with SHA256
669f339956bf0aefbb59600b6606afdaf6e345b82ffc505ce8c9917491d4b692.
That receipt is preserved in `lean-data-review-grouped-before-noncomputable.json`,
and its exact parser is preserved in `check_lean_data_grouped.py.txt`.

After certificate definitions were marked noncomputable, the parser's end
delimiter left the word `noncomputable` after the meaning tree. Its strict
token-coverage assertion rejected that input before writing a new receipt.
The delimiter now recognizes the optional declaration modifier. The tree
parser, complete identifier checks, literal checks, and clause comparisons
are unchanged. The final receipt pins the corrected parser and final source.
