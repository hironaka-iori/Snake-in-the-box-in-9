import LocalWindowDirGlue6

/-!
# Chunked key lists: assembling the seven-centre premise from proved certificate sets

The premise of a seven-centre chain is `AllRefuted7<T> = AllRefutedList dirKeys7<T> ∧
AllRefutedList hKeys7<T>`, where both lists are flattened lists of chunks
(`dirChunks7<T>`, `hChunks7<T>`, `gen_lean_automaton7.py`).  The new certificates of such a
chain are kept the same way, as a list of chunks whose premise is `AllRefutedSrcs chunks`
(every chunk is all-refuted), so that each chunk can be certified by its own module.

The glue (`LocalWindowDirGlue7<T>`, `gen_lean_glue7.py`) checks one key chunk of the chain at a
time with `mergeOK` (`LocalWindowDirGlue6`) against the full source list `[dirKeysR4b,
dirKeysR4, dirKeysK6] ++ newChunks`, one kernel declaration per chunk, and combines the
chunks here:

* `AllRefutedSrcs.flatten`: all-refuted chunks give an all-refuted flattened list.
* `AllRefutedSrcs.cons'`, `AllRefutedSrcs.nil'`: the two constructors, as lemmas (the
  generated instance builds `AllRefutedSrcs` of a chunk list with them).
* `allRefutedSrcs_four`: the sources `a :: b :: c :: chunks` from their four premises.

Core Lean only.
-/

namespace Snake9.LocalWindow

theorem AllRefutedSrcs.nil' : AllRefutedSrcs [] := trivial

theorem AllRefutedSrcs.cons' {s : List DirKey} {ss : List (List DirKey)}
    (h : AllRefutedList s) (hs : AllRefutedSrcs ss) : AllRefutedSrcs (s :: ss) :=
  ⟨h, hs⟩

/-- All-refuted chunks give an all-refuted flattened list. -/
theorem AllRefutedSrcs.flatten : ∀ {cs : List (List DirKey)},
    AllRefutedSrcs cs → AllRefutedList cs.flatten
  | [], _ => trivial
  | _ :: _, h => by
    rw [List.flatten_cons]
    exact AllRefutedList.append h.1 (AllRefutedSrcs.flatten h.2)

/-- The four-source form of the seven-centre chains: the 237 keys, the 236 keys, the k6
certificates of the bound 235, and the chunks of the new certificates. -/
theorem allRefutedSrcs_four {a b c : List DirKey} {ds : List (List DirKey)}
    (ha : AllRefutedList a) (hb : AllRefutedList b) (hc : AllRefutedList c)
    (hd : AllRefutedSrcs ds) : AllRefutedSrcs (a :: b :: c :: ds) :=
  ⟨ha, hb, hc, hd⟩

end Snake9.LocalWindow
