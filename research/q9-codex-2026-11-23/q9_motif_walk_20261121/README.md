# Q9 induced paths assembled from transition motifs

Every permitted next step before the free threshold must complete a length k+1 transition substring appearing in one of the two orientations of an input word, up to permutation of the coordinate labels. A previously unseen coordinate in the substring licenses any coordinate missing in the k-step suffix. From the threshold onward, any induced extension is allowed. The single-tip program starts from a verified prefix of either orientation of a source word. The two-tip program starts from a verified interior interval, alternates extending left and right, and uses the suffix oriented towards the chosen tip. Every search rejects repeated vertices and edges between nonconsecutive vertices. The programs include a separate quadratic checker using pairwise Hamming distances.

The two inputs are ../q9_four_piece_191_classes.txt (131 validated records) and corpus.txt (11,037 canonical words combined from that file and the historical /private/tmp/q9_191_from190_mix20.pts). Of the 11,037 words, exactly 131 are induced. All are self-avoiding. Counts by the number of chords, from 0 through 6, are 131, 1399, 1933, 2901, 3869, 801, 3. The remaining words supply motifs and individually verified partial paths. Coordinate relabeling, translation and reversal are factored out in the output class count.

## Reproduction

Compile in this directory using clang++ -O3 -std=c++20 search.cpp -o /tmp/q9motif-single and clang++ -O3 -std=c++20 center.cpp -o /tmp/q9motif-center. For a single-tip row of results.tsv, pass corpus-file k initial_edges free_from root_cap random_seed to the executable. For a two-tip row, pass corpus-file k initial_edges offset free_from root_cap random_seed. Zero truncated roots means this specific restricted family was exhausted. Capped trials may be sensitive to the implementation of std::shuffle. Node counts include duplicates across trials and other equivalent states.

All fifteen runs attained 191 edges. None found 192. There was no new 191-edge equivalence class relative to the 131 known parents. These statements apply only to the searched settings.
