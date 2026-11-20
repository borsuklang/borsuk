import Borsuk.Check

namespace Borsuk

theorem diagnose_eq_nil (p : Program) (h : check p = .ok ()) : diagnose p = [] := by
  unfold check at h
  cases hd : diagnose p with
  | nil => rfl
  | cons d ds => simp [hd] at h

theorem missingCells_eq_nil (p : Program) (h : check p = .ok ()) (m : Machine)
    (hm : Item.machine m ∈ p.items) : missingCells p m = [] := by
  have hd := diagnose_eq_nil p h
  simp only [diagnose, List.append_eq_nil_iff, List.flatMap_eq_nil_iff] at hd
  have hc := hd.2 (.machine m) hm
  simp only [cellDiags, List.append_eq_nil_iff, List.map_eq_nil_iff] at hc
  exact hc.2

theorem coverage (p : Program) (h : check p = .ok ()) (m : Machine)
    (hm : Item.machine m ∈ p.items) (s : Name) (hs : s ∈ m.states.map (·.name)) (i : Name)
    (hi : i ∈ inputNames p m) : (findCell m s i).isSome := by
  have hmiss := missingCells_eq_nil p h m hm
  simp only [missingCells, List.filter_eq_nil_iff] at hmiss
  have hpair : (s, i) ∈ pairs p m :=
    List.mem_flatMap.mpr ⟨s, hs, List.mem_map.mpr ⟨i, hi, rfl⟩⟩
  have hnone := hmiss (s, i) hpair
  cases hc : findCell m s i with
  | none => simp [hc] at hnone
  | some c => rfl

end Borsuk
