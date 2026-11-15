module

public import DirectionWindowBridge6SC
public import LocalWindowFamilies

/-! Lemmas of the 4.35 certificate glue (milestone 36): certificate lists given chunk by chunk.
A glue chunk proves `AllRefutedList c` (or the share / ctx form) for one chunk `c` of the chain's key
lists from the public `refuted` theorems of the certificate modules; these lemmas assemble the
chunks into the statements `AllRefuted6S<T>`, `AllRefutedShare6S<T>`, `AllRefutedCtx6SC<T>`. -/

@[expose] public section

namespace Snake9.Glue435
open Snake9.LocalWindow Snake9.DirectionWindow6S

theorem allRefutedList_append : ∀ {a b : List (List Nat × List Nat)},
    AllRefutedList a → AllRefutedList b → AllRefutedList (a ++ b)
  | [], _, _, hb => hb
  | _ :: _, _, ⟨h, ha⟩, hb => ⟨h, allRefutedList_append ha hb⟩

theorem allRefutedList_flatten : ∀ {L : List (List (List Nat × List Nat))},
    AllP AllRefutedList L → AllRefutedList L.flatten
  | [], _ => trivial
  | _ :: _, ⟨h, hL⟩ => by
    rw [List.flatten_cons]; exact allRefutedList_append h (allRefutedList_flatten hL)

theorem allRefutedShareList_append : ∀ {a b : List (List Nat × List Nat × Nat)},
    AllRefutedShareList a → AllRefutedShareList b → AllRefutedShareList (a ++ b)
  | [], _, _, hb => hb
  | _ :: _, _, ⟨h, ha⟩, hb => ⟨h, allRefutedShareList_append ha hb⟩

theorem allRefutedShareList_flatten : ∀ {L : List (List (List Nat × List Nat × Nat))},
    AllP AllRefutedShareList L → AllRefutedShareList L.flatten
  | [], _ => trivial
  | _ :: _, ⟨h, hL⟩ => by
    rw [List.flatten_cons]; exact allRefutedShareList_append h (allRefutedShareList_flatten hL)

theorem allP_append {α : Type} {P : α → Prop} : ∀ {a b : List α}, AllP P a → AllP P b → AllP P (a ++ b)
  | [], _, _, hb => hb
  | _ :: _, _, ⟨h, ha⟩, hb => ⟨h, allP_append ha hb⟩

theorem allP_flatten {α : Type} {P : α → Prop} : ∀ {L : List (List α)}, AllP (AllP P) L → AllP P L.flatten
  | [], _ => trivial
  | _ :: _, ⟨h, hL⟩ => by rw [List.flatten_cons]; exact allP_append h (allP_flatten hL)

end Snake9.Glue435
