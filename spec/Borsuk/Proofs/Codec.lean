import Borsuk.Codec

namespace Borsuk

instance : LawfulBEq Node where
  eq_of_beq {a b} h := by
    cases a <;> cases b <;> simp_all [BEq.beq, instBEqNode.beq]
  rfl {a} := by
    cases a <;> simp [BEq.beq, instBEqNode.beq]

def walkTo (p : Program) : Node → List Node → Node → Prop
  | x, [], y => x = y
  | x, z :: zs, y => z ∈ edges p x ∧ walkTo p z zs y

theorem walkTo_suffix (p : Program) (y b : Node) (l2 : List Node) :
    ∀ (l1 : List Node) (x : Node), walkTo p x (l1 ++ y :: l2) b → walkTo p y l2 b
  | [], _, h => h.2
  | z :: l1, _, h => walkTo_suffix p y b l2 l1 z h.2

theorem walkTo_shorten (p : Program) (b : Node) :
    ∀ (zs : List Node) (a : Node), walkTo p a zs b →
      ∃ ws, walkTo p a ws b ∧ (a :: ws).Nodup ∧ ∀ x ∈ ws, x ∈ zs
  | [], _, h => ⟨[], h, by simp, by simp⟩
  | z :: zs, a, h => by
    obtain ⟨ws, hw, hn, hs⟩ := walkTo_shorten p b zs z h.2
    by_cases ha : a ∈ z :: ws
    · rcases List.mem_cons.mp ha with he | hm
      · subst he
        exact ⟨ws, hw, hn, fun x hx => List.mem_cons_of_mem _ (hs x hx)⟩
      · obtain ⟨l1, l2, rfl⟩ := List.append_of_mem hm
        refine ⟨l2, walkTo_suffix p a b l2 l1 z hw, ?_, ?_⟩
        · exact hn.sublist (List.Sublist.cons z (List.sublist_append_right l1 (a :: l2)))
        · intro x hx
          exact List.mem_cons_of_mem _ (hs x (by simp [hx]))
    · refine ⟨z :: ws, ⟨h.1, hw⟩, List.nodup_cons.mpr ⟨ha, hn⟩, fun x hx => ?_⟩
      rcases List.mem_cons.mp hx with he | hm
      · subst he
        simp
      · exact List.mem_cons_of_mem _ (hs x hm)

theorem addNew_cover (y : Node) :
    ∀ (seen l : List Node), y ∈ l → y ∈ seen ∨ y ∈ addNew seen l
  | _, [], h => by simp at h
  | seen, x :: xs, h => by
    simp only [addNew]
    split
    · rename_i hx
      rcases List.mem_cons.mp h with he | h
      · subst he
        exact Or.inl (by simpa using hx)
      · exact addNew_cover y seen xs h
    · rcases List.mem_cons.mp h with he | h
      · subst he
        exact Or.inr (by simp)
      · rcases addNew_cover y (x :: seen) xs h with h1 | h1
        · rcases List.mem_cons.mp h1 with he | h1
          · subst he
            exact Or.inr (by simp)
          · exact Or.inl h1
        · exact Or.inr (List.mem_cons_of_mem _ h1)

def Open (p : Program) (seen frontier : List Node) : Prop :=
  ∀ x ∈ seen, x ∉ frontier → ∀ y ∈ edges p x, y ∈ seen

theorem closed_walk (p : Program) (seen : List Node) (hc : ∀ x ∈ seen, ∀ y ∈ edges p x, y ∈ seen)
    (b : Node) : ∀ (zs : List Node) (a : Node), a ∈ seen → walkTo p a zs b → b ∈ seen
  | [], a, ha, h => by
    have hab : a = b := h
    subst hab
    exact ha
  | z :: zs, a, ha, h => closed_walk p seen hc b zs z (hc a ha z h.1) h.2

theorem reach_sub (p : Program) :
    ∀ (k : Nat) (seen frontier : List Node) (x : Node), x ∈ seen → x ∈ reach p k seen frontier
  | 0, _, _, _, h => h
  | k + 1, seen, frontier, x, h => by
    cases hn : addNew seen (frontier.flatMap (edges p)) with
    | nil => simp only [reach, hn]; exact h
    | cons y ys =>
      simp only [reach, hn]
      exact reach_sub p k _ _ x (List.mem_append_left _ h)

theorem reach_walk (p : Program) (b : Node) :
    ∀ (k : Nat) (seen frontier : List Node), Open p seen frontier → ∀ (zs : List Node) (a : Node),
      a ∈ seen → walkTo p a zs b → zs.length ≤ k → b ∈ reach p k seen frontier
  | k, seen, frontier, _, [], a, ha, h, _ => by
    have hab : a = b := h
    subst hab
    exact reach_sub p k seen frontier a ha
  | 0, _, _, _, _ :: _, _, _, _, hk => by simp at hk
  | k + 1, seen, frontier, ho, z :: zs, a, ha, h, hk => by
    have hsucc : ∀ x ∈ seen, ∀ y ∈ edges p x,
        y ∈ seen ∨ y ∈ addNew seen (frontier.flatMap (edges p)) := by
      intro x hx y hy
      by_cases hf : x ∈ frontier
      · exact addNew_cover y seen _ (List.mem_flatMap.mpr ⟨x, hf, hy⟩)
      · exact Or.inl (ho x hx hf y hy)
    cases hn : addNew seen (frontier.flatMap (edges p)) with
    | nil =>
      simp only [reach, hn]
      refine closed_walk p seen ?_ b (z :: zs) a ha h
      intro x hx y hy
      rcases hsucc x hx y hy with h1 | h1
      · exact h1
      · rw [hn] at h1
        simp at h1
    | cons y ys =>
      simp only [reach, hn]
      have hz : z ∈ seen ++ y :: ys := by
        rcases hsucc a ha z h.1 with h1 | h1
        · exact List.mem_append_left _ h1
        · rw [hn] at h1
          exact List.mem_append_right _ h1
      refine reach_walk p b k (seen ++ y :: ys) (y :: ys) ?_ zs z hz h.2 (by simp at hk; omega)
      intro x hx hxn w hw
      rcases List.mem_append.mp hx with hx | hx
      · rcases hsucc x hx w hw with h1 | h1
        · exact List.mem_append_left _ h1
        · rw [hn] at h1
          exact List.mem_append_right _ h1
      · exact absurd hx hxn

theorem reachFrom_walk (p : Program) (start : List Node) (a b : Node) (zs : List Node)
    (ha : a ∈ start) (h : walkTo p a zs b) (hl : zs.length ≤ nodeCount p) :
    b ∈ reachFrom p start := by
  have ha' : a ∈ addNew [] start := by
    rcases addNew_cover a [] start ha with h1 | h1
    · simp at h1
    · exact h1
  simp only [reachFrom]
  exact reach_walk p b _ _ _ (fun x hx hxn => absurd hx hxn) zs a ha' h hl

def nodeSet (p : Program) : List Node :=
  (typeNames p).map Node.named ++ [.stepId, .ticket]

theorem nodeSet_length (p : Program) : (nodeSet p).length = nodeCount p := by
  simp [nodeSet, nodeCount]

theorem mem_itemNodes (p : Program) (n : Name) (y : Node) (h : y ∈ itemNodes p n) :
    n ∈ typeNames p := by
  simp only [itemNodes, List.mem_flatMap] at h
  obtain ⟨it, hit, hy⟩ := h
  simp only [typeNames, List.mem_filterMap]
  refine ⟨it, hit, ?_⟩
  cases it with
  | record r fs is =>
    by_cases hr : r = n
    · simp [hr]
    · simp [hr] at hy
  | enum e vs =>
    by_cases hr : e = n
    · simp [hr]
    · simp [hr] at hy
  | newtype m t =>
    by_cases hr : m = n
    · simp [hr]
    · simp [hr] at hy
  | _ => simp at hy

theorem edge_src (p : Program) (x y : Node) (h : y ∈ edges p x) : x ∈ nodeSet p := by
  cases x with
  | named n =>
    simp only [nodeSet, List.mem_append, List.mem_map]
    exact Or.inl ⟨n, mem_itemNodes p n y h, rfl⟩
  | stepId => simp [nodeSet]
  | ticket => simp [nodeSet]

theorem walk_mem (p : Program) (b : Node) (hb : b ∈ nodeSet p) :
    ∀ (ws : List Node) (a : Node), walkTo p a ws b → ∀ x ∈ a :: ws, x ∈ nodeSet p
  | [], a, h, x, hx => by
    have hab : a = b := h
    simp at hx
    subst hx
    exact hab ▸ hb
  | z :: ws, a, h, x, hx => by
    rcases List.mem_cons.mp hx with he | hm
    · subst he
      exact edge_src p _ z h.1
    · exact walk_mem p b hb ws z h.2 x hm

theorem walk_short (p : Program) (a b : Node) (zs : List Node) (h : walkTo p a zs b)
    (hb : b ∈ nodeSet p) : ∃ ws, walkTo p a ws b ∧ ws.length < nodeCount p := by
  obtain ⟨ws, hw, hn, _⟩ := walkTo_shorten p b zs a h
  refine ⟨ws, hw, ?_⟩
  have hl := hn.length_le_of_subset (fun x hx => walk_mem p b hb ws a hw x hx)
  simp [nodeSet_length] at hl
  omega

theorem diag_nil (p : Program) (h : check p = .ok ()) : diagnose p = [] := by
  unfold check at h
  split at h
  · assumption
  · cases h

theorem rtd_nil (p : Program) (h : check p = .ok ()) : recursiveTypeDiags p = [] := by
  have hd := diag_nil p h
  simp only [diagnose, List.append_eq_nil_iff] at hd
  exact hd.1.2

theorem layout_nil (p : Program) (h : check p = .ok ()) : ∀ it ∈ p.items, layoutDiags it = [] := by
  have hd := diag_nil p h
  simp only [diagnose, List.append_eq_nil_iff, List.flatMap_eq_nil_iff] at hd
  exact hd.1.1.2

theorem rtd_facts (p : Program) (h : recursiveTypeDiags p = []) :
    (∀ n ∈ typeNames p, reachesSelf p (.named n) = false) ∧
    (∀ m, Item.machine m ∈ p.items →
      reachesSpecial p (tyNodes m.key) = true → firstSpecial p (nodeCount p) m.key = none) := by
  unfold recursiveTypeDiags at h
  split at h
  · simp at h
  · rename_i hf
    dsimp only at h
    split at h
    · simp at h
    · rename_i hk
      constructor
      · intro n hn
        have := List.find?_eq_none.mp hf n hn
        simpa using this
      · intro m hm hc
        have := List.findSome?_eq_none_iff.mp hk (.machine m) hm
        simp only [hc, ite_true] at this
        exact this


def isSpecial (n : Node) : Prop :=
  n = .stepId ∨ n = .ticket

theorem findSome_isSome {α β : Type} {l : List α} {f : α → Option β} {a : α} (h : a ∈ l)
    (hs : (f a).isSome) : (l.findSome? f).isSome := by
  cases hf : l.findSome? f with
  | some _ => rfl
  | none =>
    have := List.findSome?_eq_none_iff.mp hf a h
    simp [this] at hs

theorem fs_direct (p : Program) (k : Nat) (s : Node) (hs : isSpecial s) :
    ∀ u : Ty, s ∈ tyNodes u → (firstSpecial p k u).isSome
  | .stepId, _ => by cases k <;> simp [firstSpecial]
  | .ticket, _ => by cases k <;> simp [firstSpecial]
  | .option t, h => by
    have := fs_direct p k s hs t h
    cases k <;> simpa [firstSpecial] using this
  | .result a b, h => by
    simp only [tyNodes, List.mem_append] at h
    have ha := fs_direct p k s hs a
    have hb := fs_direct p k s hs b
    cases k <;> simp only [firstSpecial] <;>
      cases hx : firstSpecial p _ a <;> simp_all [Option.orElse]
  | .named n, h => by
    simp only [tyNodes, List.mem_singleton] at h
    rcases hs with rfl | rfl <;> cases h
  | .unit, h | .bool, h | .int, h | .text, h | .time, h | .duration, h | .principal, h
  | .f64, h | .f32, h | .decimal _, h => by simp [tyNodes] at h

theorem fs_named (p : Program) (k : Nat) (n : Name)
    (hn : (firstSpecial p (k + 1) (.named n)).isSome) :
    ∀ u : Ty, Node.named n ∈ tyNodes u → (firstSpecial p (k + 1) u).isSome
  | .option t, h => by
    have := fs_named p k n hn t h
    simpa [firstSpecial] using this
  | .result a b, h => by
    simp only [tyNodes, List.mem_append] at h
    have ha := fs_named p k n hn a
    have hb := fs_named p k n hn b
    simp only [firstSpecial]
    cases hx : firstSpecial p (k + 1) a <;> simp_all [Option.orElse]
  | .named m, h => by
    simp only [tyNodes, List.mem_singleton, Node.named.injEq] at h
    subst h
    exact hn
  | .stepId, h | .ticket, h => by simp [tyNodes] at h
  | .unit, h | .bool, h | .int, h | .text, h | .time, h | .duration, h | .principal, h
  | .f64, h | .f32, h | .decimal _, h => by simp [tyNodes] at h

theorem fs_walk (p : Program) (s : Node) (hs : isSpecial s) :
    ∀ (zs : List Node) (x : Node) (u : Ty) (k : Nat), x ∈ tyNodes u → walkTo p x zs s →
      zs.length ≤ k → k ≤ nodeCount p → (firstSpecial p k u).isSome
  | [], x, u, k, hx, hw, _, _ => by
    have hxs : x = s := hw
    subst hxs
    exact fs_direct p k x hs u hx
  | z :: zs, x, u, k, hx, hw, hk, hkn => by
    cases x with
    | stepId => exact fs_direct p k _ (Or.inl rfl) u hx
    | ticket => exact fs_direct p k _ (Or.inr rfl) u hx
    | named n =>
      obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by simp at hk; omega⟩
      have hk' : zs.length ≤ k := by simp at hk; omega
      apply fs_named p k n _ u hx
      have hrs : reachesSpecial p (edges p (.named n)) = true := by
        have hr := reachFrom_walk p (edges p (.named n)) z s zs hw.1 hw.2 (by omega)
        rcases hs with rfl | rfl <;> simp [reachesSpecial, hr]
      have hz : z ∈ itemNodes p n := hw.1
      simp only [itemNodes, List.mem_flatMap] at hz
      obtain ⟨it, hit, hzi⟩ := hz
      simp only [firstSpecial, hrs, ite_true]
      apply findSome_isSome hit
      cases it with
      | record r fs is =>
        by_cases hr : r = n
        · simp only [hr, beq_self_eq_true, ite_true, List.mem_flatMap] at hzi ⊢
          obtain ⟨f, hf, hzf⟩ := hzi
          exact findSome_isSome hf (fs_walk p s hs zs z f.ty k hzf hw.2 hk' (by omega))
        · simp [hr] at hzi
      | enum e vs =>
        by_cases hr : e = n
        · simp only [hr, beq_self_eq_true, ite_true, List.mem_flatMap] at hzi ⊢
          obtain ⟨v, hv, f, hf, hzf⟩ := hzi
          exact findSome_isSome hv (findSome_isSome hf (fs_walk p s hs zs z f k hzf hw.2 hk' (by omega)))
        · simp [hr] at hzi
      | newtype m t =>
        by_cases hr : m = n
        · simp only [hr, beq_self_eq_true, ite_true] at hzi ⊢
          exact fs_walk p s hs zs z t k hzi hw.2 hk' (by omega)
        · simp [hr] at hzi
      | _ => simp at hzi

theorem special_mem (p : Program) (s : Node) (hs : isSpecial s) : s ∈ nodeSet p := by
  rcases hs with rfl | rfl <;> simp [nodeSet]

theorem key_no_special (p : Program) (hc : check p = .ok ()) (m : Machine)
    (hm : Item.machine m ∈ p.items) (x s : Node) (hx : x ∈ tyNodes m.key) (zs : List Node)
    (hw : walkTo p x zs s) (hs : isSpecial s) : False := by
  obtain ⟨_, hkey⟩ := rtd_facts p (rtd_nil p hc)
  obtain ⟨ws, hws, hl⟩ := walk_short p x s zs hw (special_mem p s hs)
  have hr := reachFrom_walk p (tyNodes m.key) x s ws hx hws (by omega)
  have hfs := fs_walk p s hs ws x m.key (nodeCount p) hx hws (by omega) (Nat.le_refl _)
  have hnone := hkey m hm (by rcases hs with rfl | rfl <;> simp [reachesSpecial, hr])
  rw [hnone] at hfs
  simp at hfs

def norm : Node → Node
  | .ticket => .stepId
  | x => x

theorem no_return (p : Program) (hc : check p = .ok ()) (x d z : Node) (ws : List Node)
    (hw : walkTo p x (z :: ws) d) (hn : norm x = norm d) : False := by
  obtain ⟨hself, _⟩ := rtd_facts p (rtd_nil p hc)
  cases x with
  | named n =>
    have hd : d = .named n := by cases d <;> simp_all [norm]
    subst hd
    have hS : Node.named n ∈ nodeSet p := edge_src p _ z hw.1
    obtain ⟨ws', hw', hl⟩ := walk_short p z (.named n) ws hw.2 hS
    have hr := reachFrom_walk p (edges p (.named n)) z (.named n) ws' hw.1 hw' (by omega)
    have hn' : n ∈ typeNames p := mem_itemNodes p n z hw.1
    have := hself n hn'
    simp [reachesSelf, hr] at this
  | stepId | ticket =>
    have hd : isSpecial d := by cases d <;> simp_all [norm, isSpecial]
    have hz : z ∈ keyNodes p := hw.1
    simp only [keyNodes, List.mem_flatMap] at hz
    obtain ⟨it, hit, hzi⟩ := hz
    cases it with
    | machine m => exact key_no_special p hc m hit z d hzi ws hw.2 hd
    | _ => simp at hzi

def departures : Node → List Node → List Node
  | _, [] => []
  | x, z :: zs => x :: departures z zs

theorem departures_length : ∀ (x : Node) (zs : List Node), (departures x zs).length = zs.length
  | _, [] => rfl
  | _, z :: zs => by simp [departures, departures_length z zs]

theorem departures_walk (p : Program) (y : Node) :
    ∀ (zs : List Node) (x : Node), walkTo p x zs y → ∀ d ∈ departures x zs,
      (∃ e, e ∈ edges p d) ∧ ∃ ws, walkTo p x ws d
  | [], _, _, d, hd => by simp [departures] at hd
  | z :: zs, x, hw, d, hd => by
    simp only [departures, List.mem_cons] at hd
    rcases hd with rfl | hd
    · exact ⟨⟨z, hw.1⟩, [], rfl⟩
    · obtain ⟨he, ws, hws⟩ := departures_walk p y zs z hw.2 d hd
      exact ⟨he, z :: ws, hw.1, hws⟩

theorem dep_nodup (p : Program) (hc : check p = .ok ()) (y : Node) :
    ∀ (zs : List Node) (x : Node), walkTo p x zs y → ((departures x zs).map norm).Nodup
  | [], _, _ => by simp [departures]
  | z :: zs, x, hw => by
    simp only [departures, List.map_cons, List.nodup_cons, List.mem_map]
    refine ⟨?_, dep_nodup p hc y zs z hw.2⟩
    rintro ⟨d, hd, hn⟩
    obtain ⟨_, ws, hws⟩ := departures_walk p y zs z hw.2 d hd
    exact no_return p hc x d z ws ⟨hw.1, hws⟩ hn.symm

theorem walk_bound (p : Program) (hc : check p = .ok ()) (x y : Node) (zs : List Node)
    (hw : walkTo p x zs y) : zs.length < nodeCount p := by
  have hnd := dep_nodup p hc y zs x hw
  have hsub : (departures x zs).map norm ⊆ (typeNames p).map Node.named ++ [Node.stepId] := by
    intro a ha
    simp only [List.mem_map] at ha
    obtain ⟨d, hd, rfl⟩ := ha
    obtain ⟨⟨e, he⟩, _⟩ := departures_walk p y zs x hw d hd
    have hs := edge_src p d e he
    simp only [nodeSet, List.mem_append, List.mem_map, List.mem_cons] at hs
    simp only [List.mem_append, List.mem_map, List.mem_cons]
    rcases hs with ⟨n, hn, rfl⟩ | rfl | rfl | h
    · exact Or.inl ⟨n, hn, rfl⟩
    · simp [norm]
    · simp [norm]
    · simp at h
  have hl := hnd.length_le_of_subset hsub
  simp [departures_length, nodeCount] at hl ⊢
  omega

def Fine (p : Program) (k : Nat) (u : Ty) : Prop :=
  ∀ x ∈ tyNodes u, ∀ zs y, walkTo p x zs y → zs.length < k

theorem fine_all (p : Program) (hc : check p = .ok ()) (u : Ty) : Fine p (nodeCount p) u :=
  fun x _ zs y hw => walk_bound p hc x y zs hw

theorem fine_pos {p : Program} {k : Nat} {u : Ty} {x : Node} (h : Fine p k u)
    (hx : x ∈ tyNodes u) : 0 < k :=
  h x hx [] x rfl

theorem fine_step {p : Program} {k : Nat} {u f : Ty} {x : Node} (h : Fine p (k + 1) u)
    (hx : x ∈ tyNodes u) (hf : ∀ y ∈ tyNodes f, y ∈ edges p x) : Fine p k f := by
  intro y hy zs w hw
  have := h x hx (y :: zs) w ⟨hf y hy, hw⟩
  simp at this
  omega

theorem fine_left {p : Program} {k : Nat} {a b : Ty} (h : Fine p k (.result a b)) : Fine p k a :=
  fun x hx => h x (List.mem_append_left _ hx)

theorem fine_right {p : Program} {k : Nat} {a b : Ty} (h : Fine p k (.result a b)) : Fine p k b :=
  fun x hx => h x (List.mem_append_right _ hx)


theorem findRecord_item (p : Program) (n : Name) (fs : List Param) (h : findRecord p n = some fs) :
    ∃ fields inits, Item.record n fields inits ∈ p.items ∧ fs = fields ++ inits.map (·.1) := by
  obtain ⟨it, hit, he⟩ := List.exists_of_findSome?_eq_some h
  cases it with
  | record r fields inits =>
    by_cases hr : r = n
    · subst hr
      simp at he
      exact ⟨fields, inits, hit, he.symm⟩
    · simp [hr] at he
  | _ => simp at he

theorem findEnum_item (p : Program) (n : Name) (vs : List Variant) (h : findEnum p n = some vs) :
    Item.enum n vs ∈ p.items := by
  obtain ⟨it, hit, he⟩ := List.exists_of_findSome?_eq_some h
  cases it with
  | enum e ws =>
    by_cases hr : e = n
    · subst hr
      simp at he
      exact he ▸ hit
    · simp [hr] at he
  | _ => simp at he

theorem findNewtype_item (p : Program) (n : Name) (t : Ty) (h : findNewtype p n = some t) :
    Item.newtype n t ∈ p.items := by
  obtain ⟨it, hit, he⟩ := List.exists_of_findSome?_eq_some h
  cases it with
  | newtype m u =>
    by_cases hr : m = n
    · subst hr
      simp at he
      exact he ▸ hit
    · simp [hr] at he
  | _ => simp at he

theorem findMachine_item (p : Program) (m : Name) (mach : Machine) (h : findMachine p m = some mach) :
    Item.machine mach ∈ p.items := by
  obtain ⟨it, hit, he⟩ := List.exists_of_findSome?_eq_some h
  cases it with
  | machine q =>
    by_cases hr : q.name = m
    · simp [hr] at he
      exact he ▸ hit
    · simp [hr] at he
  | _ => simp at he

theorem record_nodes (p : Program) (n : Name) (fs : List Param) (h : findRecord p n = some fs)
    (f : Param) (hf : f ∈ fs) (y : Node) (hy : y ∈ tyNodes f.ty) : y ∈ edges p (.named n) := by
  obtain ⟨fields, inits, hit, rfl⟩ := findRecord_item p n fs h
  simp only [edges, itemNodes, List.mem_flatMap]
  refine ⟨_, hit, ?_⟩
  simp only [beq_self_eq_true, ite_true, List.mem_flatMap]
  exact ⟨f, hf, hy⟩

theorem enum_nodes (p : Program) (n : Name) (vs : List Variant) (h : findEnum p n = some vs)
    (v : Variant) (hv : v ∈ vs) (f : Ty) (hf : f ∈ v.fields) (y : Node) (hy : y ∈ tyNodes f) :
    y ∈ edges p (.named n) := by
  have hit := findEnum_item p n vs h
  simp only [edges, itemNodes, List.mem_flatMap]
  refine ⟨_, hit, ?_⟩
  simp only [beq_self_eq_true, ite_true, List.mem_flatMap]
  exact ⟨v, hv, f, hf, hy⟩

theorem newtype_nodes (p : Program) (n : Name) (t : Ty) (h : findNewtype p n = some t)
    (y : Node) (hy : y ∈ tyNodes t) : y ∈ edges p (.named n) := by
  have hit := findNewtype_item p n t h
  simp only [edges, itemNodes, List.mem_flatMap]
  refine ⟨_, hit, ?_⟩
  simp only [beq_self_eq_true, ite_true]
  exact hy

theorem key_nodes (p : Program) (m : Name) (mach : Machine) (h : findMachine p m = some mach)
    (y : Node) (hy : y ∈ tyNodes mach.key) : y ∈ keyNodes p := by
  have hit := findMachine_item p m mach h
  simp only [keyNodes, List.mem_flatMap]
  exact ⟨_, hit, hy⟩

theorem record_len (p : Program) (hc : check p = .ok ()) (n : Name) (fs : List Param)
    (h : findRecord p n = some fs) : fs.length < 2 ^ 16 := by
  obtain ⟨fields, inits, hit, rfl⟩ := findRecord_item p n fs h
  have hl := layout_nil p hc _ hit
  simp only [layoutDiags] at hl
  split at hl
  · simp at hl
  · simp
    omega

theorem enum_len (p : Program) (hc : check p = .ok ()) (n : Name) (vs : List Variant)
    (h : findEnum p n = some vs) : vs.length ≤ 256 := by
  have hl := layout_nil p hc _ (findEnum_item p n vs h)
  simp only [layoutDiags] at hl
  split at hl
  · simp at hl
  · omega

theorem enum_typeName (p : Program) (n : Name) (vs : List Variant) (h : findEnum p n = some vs) :
    isTypeName p n = true := by
  simp only [isTypeName, List.any_eq_true]
  exact ⟨_, findEnum_item p n vs h, by simp⟩

theorem record_typeName (p : Program) (n : Name) (fs : List Param) (h : findRecord p n = some fs) :
    isTypeName p n = true := by
  obtain ⟨_, _, hit, _⟩ := findRecord_item p n fs h
  simp only [isTypeName, List.any_eq_true]
  exact ⟨_, hit, by simp⟩

theorem newtype_typeName (p : Program) (n : Name) (t : Ty) (h : findNewtype p n = some t) :
    isTypeName p n = true := by
  simp only [isTypeName, List.any_eq_true]
  exact ⟨_, findNewtype_item p n t h, by simp⟩

theorem findInits_some (p : Program) (n : Name) (fs : List Param) (h : findRecord p n = some fs) :
    ∃ inits, findInits p n = some inits := by
  cases hi : findInits p n with
  | some inits => exact ⟨inits, rfl⟩
  | none =>
    have hn := List.findSome?_eq_none_iff.mp hi
    obtain ⟨fields, inits, hit, _⟩ := findRecord_item p n fs h
    have := hn _ hit
    simp at this

theorem findVariant_get (c : Name) :
    ∀ (vs : List Variant) (i : Nat) (v : Variant), findVariant c vs = some (i, v) →
      vs[i]? = some v ∧ v.name = c
  | [], _, _, h => by simp [findVariant] at h
  | w :: ws, i, v, h => by
    simp only [findVariant] at h
    by_cases hw : w.name = c
    · simp [hw] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, hw⟩
    · simp only [hw, beq_iff_eq, ite_false, Option.map_eq_some_iff] at h
      obtain ⟨⟨j, u⟩, hj, he⟩ := h
      simp at he
      obtain ⟨rfl, rfl⟩ := he
      have := findVariant_get c ws j u hj
      exact ⟨by simpa using this.1, this.2⟩

theorem findVariant_of_index (vs : List Variant) (i : Nat) (v : Variant) (hv : vs[i]? = some v)
    (hi : (findVariant v.name vs).map (·.1) = some i) : findVariant v.name vs = some (i, v) := by
  cases hf : findVariant v.name vs with
  | none => simp [hf] at hi
  | some r =>
    obtain ⟨j, w⟩ := r
    simp [hf] at hi
    subst hi
    have := (findVariant_get v.name vs j w hf).1
    rw [hv] at this
    cases this
    rfl

theorem allFixed_mono {r1 r2 : Ty → Option Bool} (h : ∀ u b, r1 u = some b → r2 u = some b) :
    ∀ (ts : List Ty) (b : Bool), allFixed r1 ts = some b → allFixed r2 ts = some b
  | [], _, hb => hb
  | t :: ts, b, hb => by
    cases h1 : r1 t with
    | none => simp [allFixed, h1] at hb
    | some x =>
      cases h2 : allFixed r1 ts with
      | none => simp [allFixed, h1, h2] at hb
      | some y =>
        simp only [allFixed, h1, h2, Option.bind_eq_bind, Option.bind_some] at hb
        simp only [allFixed, h _ _ h1, allFixed_mono h ts y h2, Option.bind_eq_bind,
          Option.bind_some]
        exact hb

theorem fixedTy_mono (p : Program) {r1 r2 : Ty → Option Bool}
    (h : ∀ u b, r1 u = some b → r2 u = some b) :
    ∀ (t : Ty) (b : Bool), fixedTy p r1 t = some b → fixedTy p r2 t = some b
  | .option t, b, hb => fixedTy_mono p h t b hb
  | .result a c, b, hb => by
    cases h1 : fixedTy p r1 a with
    | none => simp [fixedTy, h1] at hb
    | some x =>
      cases h2 : fixedTy p r1 c with
      | none => simp [fixedTy, h1, h2] at hb
      | some y =>
        simp only [fixedTy, h1, h2, Option.bind_eq_bind, Option.bind_some] at hb
        simp only [fixedTy, fixedTy_mono p h a x h1, fixedTy_mono p h c y h2,
          Option.bind_eq_bind, Option.bind_some]
        exact hb
  | .named n, b, hb => by
    simp only [fixedTy] at hb ⊢
    cases hr : findRecord p n with
    | some _ => simpa [hr] using hb
    | none =>
      cases he : findEnum p n with
      | some vs =>
        simp only [hr, he] at hb ⊢
        exact allFixed_mono h _ b hb
      | none =>
        cases hn : findNewtype p n with
        | some t =>
          simp only [hr, he, hn] at hb ⊢
          exact h t b hb
        | none => simpa [hr, he, hn] using hb
  | .unit, _, hb | .bool, _, hb | .int, _, hb | .text, _, hb | .time, _, hb
  | .duration, _, hb | .principal, _, hb | .stepId, _, hb | .ticket, _, hb | .f64, _, hb
  | .f32, _, hb | .decimal _, _, hb => hb

theorem isFixed_succ (p : Program) :
    ∀ (k : Nat) (t : Ty) (b : Bool), isFixed p k t = some b → isFixed p (k + 1) t = some b
  | 0, _, _, hb => by simp [isFixed] at hb
  | k + 1, t, b, hb => fixedTy_mono p (isFixed_succ p k) t b hb

theorem isFixed_le (p : Program) (k : Nat) (t : Ty) (b : Bool) (hb : isFixed p k t = some b) :
    ∀ j, k ≤ j → isFixed p j t = some b
  | j, hj => by
    induction j with
    | zero =>
      have : k = 0 := by omega
      subst this
      exact hb
    | succ j ih =>
      rcases Nat.eq_or_lt_of_le hj with h | h
      · rw [← h]
        exact hb
      · exact isFixed_succ p j t b (ih (by omega))

theorem sumSizes_mono {r1 r2 : Ty → Option Nat} (h : ∀ u n, r1 u = some n → r2 u = some n) :
    ∀ (ts : List Ty) (n : Nat), sumSizes r1 ts = some n → sumSizes r2 ts = some n
  | [], _, hb => hb
  | t :: ts, b, hb => by
    cases h1 : r1 t with
    | none => simp [sumSizes, h1] at hb
    | some x =>
      cases h2 : sumSizes r1 ts with
      | none => simp [sumSizes, h1, h2] at hb
      | some y =>
        simp only [sumSizes, h1, h2, Option.bind_eq_bind, Option.bind_some] at hb
        simp only [sumSizes, h _ _ h1, sumSizes_mono h ts y h2, Option.bind_eq_bind,
          Option.bind_some]
        exact hb

theorem maxSizes_mono {r1 r2 : Ty → Option Nat} (h : ∀ u n, r1 u = some n → r2 u = some n) :
    ∀ (vs : List Variant) (n : Nat), maxSizes r1 vs = some n → maxSizes r2 vs = some n
  | [], _, hb => hb
  | v :: vs, b, hb => by
    cases h1 : sumSizes r1 v.fields with
    | none => simp [maxSizes, h1] at hb
    | some x =>
      cases h2 : maxSizes r1 vs with
      | none => simp [maxSizes, h1, h2] at hb
      | some y =>
        simp only [maxSizes, h1, h2, Option.bind_eq_bind, Option.bind_some] at hb
        simp only [maxSizes, sumSizes_mono h _ _ h1, maxSizes_mono h vs y h2,
          Option.bind_eq_bind, Option.bind_some]
        exact hb

theorem sizeTy_mono (p : Program) {r1 r2 : Ty → Option Nat}
    (h : ∀ u n, r1 u = some n → r2 u = some n) :
    ∀ (t : Ty) (n : Nat), sizeTy p r1 t = some n → sizeTy p r2 t = some n
  | .option t, n, hb => by
    cases h1 : sizeTy p r1 t with
    | none => simp [sizeTy, h1] at hb
    | some x =>
      simp only [sizeTy, h1, Option.map_some] at hb
      simp only [sizeTy, sizeTy_mono p h t x h1, Option.map_some]
      exact hb
  | .result a c, b, hb => by
    cases h1 : sizeTy p r1 a with
    | none => simp [sizeTy, h1] at hb
    | some x =>
      cases h2 : sizeTy p r1 c with
      | none => simp [sizeTy, h1, h2] at hb
      | some y =>
        simp only [sizeTy, h1, h2, Option.bind_eq_bind, Option.bind_some] at hb
        simp only [sizeTy, sizeTy_mono p h a x h1, sizeTy_mono p h c y h2,
          Option.bind_eq_bind, Option.bind_some]
        exact hb
  | .named n, b, hb => by
    simp only [sizeTy] at hb ⊢
    cases hr : findRecord p n with
    | some _ => simp [hr] at hb
    | none =>
      cases he : findEnum p n with
      | some vs =>
        simp only [hr, he] at hb ⊢
        cases h1 : maxSizes r1 vs with
        | none => simp [h1] at hb
        | some x =>
          simp only [h1, Option.map_some] at hb
          simp only [maxSizes_mono h vs x h1, Option.map_some]
          exact hb
      | none =>
        cases hn : findNewtype p n with
        | some t =>
          simp only [hr, he, hn] at hb ⊢
          exact h t b hb
        | none => simp [hr, he, hn] at hb
  | .unit, _, hb | .bool, _, hb | .int, _, hb | .text, _, hb | .time, _, hb
  | .duration, _, hb | .principal, _, hb | .stepId, _, hb | .ticket, _, hb | .f64, _, hb
  | .f32, _, hb | .decimal _, _, hb => hb

theorem tySize_succ (p : Program) :
    ∀ (k : Nat) (t : Ty) (n : Nat), tySize p k t = some n → tySize p (k + 1) t = some n
  | 0, _, _, hb => by simp [tySize] at hb
  | k + 1, t, b, hb => sizeTy_mono p (tySize_succ p k) t b hb

theorem tySize_le (p : Program) (k : Nat) (t : Ty) (n : Nat) (hb : tySize p k t = some n) :
    ∀ j, k ≤ j → tySize p j t = some n
  | j, hj => by
    induction j with
    | zero =>
      have : k = 0 := by omega
      subst this
      exact hb
    | succ j ih =>
      rcases Nat.eq_or_lt_of_le hj with h | h
      · rw [← h]
        exact hb
      · exact tySize_succ p j t n (ih (by omega))


theorem isFixed_det (p : Program) (j k : Nat) (t : Ty) (a b : Bool) (ha : isFixed p j t = some a)
    (hb : isFixed p k t = some b) : a = b := by
  have h1 := isFixed_le p j t a ha (j + k) (by omega)
  have h2 := isFixed_le p k t b hb (j + k) (by omega)
  rw [h1] at h2
  cases h2
  rfl

theorem tySize_det (p : Program) (j k : Nat) (t : Ty) (a b : Nat) (ha : tySize p j t = some a)
    (hb : tySize p k t = some b) : a = b := by
  have h1 := tySize_le p j t a ha (j + k) (by omega)
  have h2 := tySize_le p k t b hb (j + k) (by omega)
  rw [h1] at h2
  cases h2
  rfl

theorem allFixed_true {r : Ty → Option Bool} :
    ∀ (ts : List Ty), allFixed r ts = some true → ∀ t ∈ ts, r t = some true
  | [], _, t, ht => by simp at ht
  | u :: ts, h, t, ht => by
    cases h1 : r u with
    | none => simp [allFixed, h1] at h
    | some x =>
      cases h2 : allFixed r ts with
      | none => simp [allFixed, h1, h2] at h
      | some y =>
        simp [allFixed, h1, h2] at h
        rcases List.mem_cons.mp ht with he | ht
        · subst he
          rw [h1, h.1]
        · exact allFixed_true ts (by rw [h2, h.2]) t ht

theorem allFixed_some {r : Ty → Option Bool} :
    ∀ (ts : List Ty), (∀ t ∈ ts, ∃ b, r t = some b) → ∃ b, allFixed r ts = some b
  | [], _ => ⟨true, rfl⟩
  | u :: ts, h => by
    obtain ⟨x, hx⟩ := h u (by simp)
    obtain ⟨y, hy⟩ := allFixed_some ts (fun t ht => h t (by simp [ht]))
    exact ⟨x && y, by simp [allFixed, hx, hy]⟩

theorem sumSizes_some {r : Ty → Option Nat} :
    ∀ (ts : List Ty), (∀ t ∈ ts, ∃ n, r t = some n) → ∃ n, sumSizes r ts = some n
  | [], _ => ⟨0, rfl⟩
  | u :: ts, h => by
    obtain ⟨x, hx⟩ := h u (by simp)
    obtain ⟨y, hy⟩ := sumSizes_some ts (fun t ht => h t (by simp [ht]))
    exact ⟨x + y, by simp [sumSizes, hx, hy]⟩

theorem maxSizes_some {r : Ty → Option Nat} :
    ∀ (vs : List Variant), (∀ v ∈ vs, ∀ t ∈ v.fields, ∃ n, r t = some n) →
      ∃ n, maxSizes r vs = some n
  | [], _ => ⟨0, rfl⟩
  | v :: vs, h => by
    obtain ⟨x, hx⟩ := sumSizes_some v.fields (h v (by simp))
    obtain ⟨y, hy⟩ := maxSizes_some vs (fun w hw => h w (by simp [hw]))
    exact ⟨max x y, by simp [maxSizes, hx, hy]⟩

theorem maxSizes_ge {r : Ty → Option Nat} :
    ∀ (vs : List Variant) (m : Nat), maxSizes r vs = some m → ∀ v ∈ vs,
      ∃ s, sumSizes r v.fields = some s ∧ s ≤ m
  | [], _, _, v, hv => by simp at hv
  | w :: vs, m, h, v, hv => by
    cases h1 : sumSizes r w.fields with
    | none => simp [maxSizes, h1] at h
    | some x =>
      cases h2 : maxSizes r vs with
      | none => simp [maxSizes, h1, h2] at h
      | some y =>
        simp [maxSizes, h1, h2] at h
        rcases List.mem_cons.mp hv with he | hv
        · subst he
          exact ⟨x, h1, by omega⟩
        · obtain ⟨s, hs, hle⟩ := maxSizes_ge vs y h2 v hv
          exact ⟨s, hs, by omega⟩

theorem sumSizes_each {r : Ty → Option Nat} :
    ∀ (ts : List Ty) (m : Nat), sumSizes r ts = some m → ∀ t ∈ ts, ∃ n, r t = some n
  | [], _, _, t, ht => by simp at ht
  | u :: ts, m, h, t, ht => by
    cases h1 : r u with
    | none => simp [sumSizes, h1] at h
    | some x =>
      cases h2 : sumSizes r ts with
      | none => simp [sumSizes, h1, h2] at h
      | some y =>
        rcases List.mem_cons.mp ht with he | ht
        · subst he
          exact ⟨x, h1⟩
        · exact sumSizes_each ts y h2 t ht

theorem sizeTy_some (p : Program) {rf : Ty → Option Bool} {rs : Ty → Option Nat}
    (h : ∀ u, rf u = some true → ∃ n, rs u = some n) :
    ∀ t, fixedTy p rf t = some true → ∃ n, sizeTy p rs t = some n
  | .option t, ht => by
    obtain ⟨n, hn⟩ := sizeTy_some p h t ht
    exact ⟨1 + n, by simp [sizeTy, hn]⟩
  | .result a c, ht => by
    cases h1 : fixedTy p rf a with
    | none => simp [fixedTy, h1] at ht
    | some x =>
      cases h2 : fixedTy p rf c with
      | none => simp [fixedTy, h1, h2] at ht
      | some y =>
        simp [fixedTy, h1, h2] at ht
        obtain ⟨hx, hy⟩ := ht
        subst hx
        subst hy
        obtain ⟨n1, hn1⟩ := sizeTy_some p h a h1
        obtain ⟨n2, hn2⟩ := sizeTy_some p h c h2
        exact ⟨1 + max n1 n2, by simp [sizeTy, hn1, hn2]⟩
  | .named n, ht => by
    simp only [fixedTy] at ht
    simp only [sizeTy]
    cases hr : findRecord p n with
    | some _ => simp [hr] at ht
    | none =>
      cases he : findEnum p n with
      | some vs =>
        simp only [hr, he] at ht ⊢
        have hall := allFixed_true _ ht
        obtain ⟨m, hm⟩ := maxSizes_some (r := rs) vs (fun v hv f hf =>
          h f (hall f (List.mem_flatMap.mpr ⟨v, hv, hf⟩)))
        exact ⟨1 + m, by simp [hm]⟩
      | none =>
        cases hn : findNewtype p n with
        | some t =>
          simp only [hr, he, hn] at ht ⊢
          exact h t ht
        | none => simp [hr, he, hn] at ht
  | .unit, _ => ⟨0, rfl⟩
  | .bool, _ => ⟨1, rfl⟩
  | .int, _ => ⟨8, rfl⟩
  | .time, _ => ⟨8, rfl⟩
  | .duration, _ => ⟨8, rfl⟩
  | .f64, _ => ⟨8, rfl⟩
  | .f32, _ => ⟨4, rfl⟩
  | .decimal _, _ => ⟨16, rfl⟩
  | .text, ht | .principal, ht | .stepId, ht | .ticket, ht => by simp [fixedTy] at ht

theorem fixed_size (p : Program) :
    ∀ (k : Nat) (t : Ty), isFixed p k t = some true → ∃ n, tySize p k t = some n
  | 0, _, ht => by simp [isFixed] at ht
  | k + 1, t, ht => sizeTy_some p (fixed_size p k) t ht

theorem fixedTy_some (p : Program) (rec : Ty → Option Bool) (k : Nat)
    (hrec : ∀ k' f, k = k' + 1 → Fine p k' f → ∃ b, rec f = some b) :
    ∀ t, Fine p k t → ∃ b, fixedTy p rec t = some b
  | .option t, h => fixedTy_some p rec k hrec t h
  | .result a c, h => by
    obtain ⟨x, hx⟩ := fixedTy_some p rec k hrec a (fine_left h)
    obtain ⟨y, hy⟩ := fixedTy_some p rec k hrec c (fine_right h)
    exact ⟨x && y, by simp [fixedTy, hx, hy]⟩
  | .named n, h => by
    have hk := fine_pos h (x := .named n) (by simp [tyNodes])
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    simp only [fixedTy]
    cases hr : findRecord p n with
    | some _ => exact ⟨false, rfl⟩
    | none =>
      cases he : findEnum p n with
      | some vs =>
        apply allFixed_some
        intro f hf
        obtain ⟨v, hv, hf⟩ := List.mem_flatMap.mp hf
        exact hrec k' f rfl (fine_step h (by simp [tyNodes])
          (fun y hy => enum_nodes p n vs he v hv f hf y hy))
      | none =>
        cases hn : findNewtype p n with
        | some t =>
          exact hrec k' t rfl (fine_step h (by simp [tyNodes])
            (fun y hy => newtype_nodes p n t hn y hy))
        | none => exact ⟨false, rfl⟩
  | .unit, _ | .bool, _ | .int, _ | .text, _ | .time, _ | .duration, _ | .principal, _
  | .stepId, _ | .ticket, _ | .f64, _ | .f32, _ | .decimal _, _ => ⟨_, rfl⟩

theorem fine_fixed (p : Program) :
    ∀ (k : Nat) (t : Ty), Fine p k t → ∃ b, isFixed p (k + 1) t = some b
  | 0, t, h => fixedTy_some p (isFixed p 0) 0 (fun _ _ hk _ => by omega) t h
  | k + 1, t, h => fixedTy_some p (isFixed p (k + 1)) (k + 1) (fun k' f hk hf => by
      have hk' : k' = k := by omega
      subst hk'
      exact fine_fixed p k' f hf) t h

theorem startFuel_eq (p : Program) : startFuel p = nodeCount p + 1 := by
  simp [startFuel, nodeCount]

theorem fixed_all (p : Program) (hc : check p = .ok ()) (t : Ty) :
    ∃ b, isFixed p (startFuel p) t = some b := by
  rw [startFuel_eq]
  exact fine_fixed p _ t (fine_all p hc t)

theorem slot_cases (p : Program) (hc : check p = .ok ()) (t : Ty) :
    (isFixed p (startFuel p) t = some false ∧ slotOf p t = some none) ∨
    (∃ n, isFixed p (startFuel p) t = some true ∧ tySize p (startFuel p) t = some n ∧
      slotOf p t = some (some n)) := by
  obtain ⟨b, hb⟩ := fixed_all p hc t
  cases b with
  | false => exact Or.inl ⟨hb, by simp [slotOf, hb]⟩
  | true =>
    obtain ⟨n, hn⟩ := fixed_size p _ t hb
    exact Or.inr ⟨n, hb, hn, by simp [slotOf, hb, hn]⟩

theorem slotOf_some (p : Program) (t : Ty) (k : Option Nat) (h : slotOf p t = some k) :
    (k = none ∧ isFixed p (startFuel p) t = some false) ∨
    (∃ n, k = some n ∧ isFixed p (startFuel p) t = some true ∧ tySize p (startFuel p) t = some n) := by
  simp only [slotOf] at h
  split at h
  · rename_i hf
    cases hs : tySize p (startFuel p) t with
    | none => simp [hs] at h
    | some n =>
      simp [hs] at h
      exact Or.inr ⟨n, h.symm, hf, rfl⟩
  · rename_i hf
    simp at h
    exact Or.inl ⟨h.symm, hf⟩
  · simp at h

theorem isFixed_option (p : Program) (k : Nat) (t : Ty) : isFixed p k (.option t) = isFixed p k t := by
  cases k <;> rfl

theorem isFixed_result (p : Program) (k : Nat) (a b : Ty) (h : isFixed p k (.result a b) = some true) :
    isFixed p k a = some true ∧ isFixed p k b = some true := by
  cases k with
  | zero => simp [isFixed] at h
  | succ k =>
    simp only [isFixed, fixedTy] at h ⊢
    cases h1 : fixedTy p (isFixed p k) a <;> cases h2 : fixedTy p (isFixed p k) b <;>
      simp_all

theorem isFixed_text (p : Program) (k : Nat) (t : Ty)
    (ht : t = .text ∨ t = .principal ∨ t = .stepId ∨ t = .ticket) : isFixed p k t ≠ some true := by
  cases k with
  | zero => simp [isFixed]
  | succ k => rcases ht with rfl | rfl | rfl | rfl <;> simp [isFixed, fixedTy]

theorem isFixed_record (p : Program) (k : Nat) (n : Name) (fs : List Param)
    (h : findRecord p n = some fs) : isFixed p k (.named n) ≠ some true := by
  cases k with
  | zero => simp [isFixed]
  | succ k => simp [isFixed, fixedTy, h]

theorem isFixed_enum (p : Program) (k : Nat) (n : Name) (vs : List Variant)
    (hr : findRecord p n = none) (he : findEnum p n = some vs)
    (h : isFixed p k (.named n) = some true) :
    ∃ j, k = j + 1 ∧ ∀ v ∈ vs, ∀ f ∈ v.fields, isFixed p j f = some true := by
  cases k with
  | zero => simp [isFixed] at h
  | succ j =>
    simp only [isFixed, fixedTy, hr, he] at h
    exact ⟨j, rfl, fun v hv f hf => allFixed_true _ h f (List.mem_flatMap.mpr ⟨v, hv, hf⟩)⟩

theorem tySize_enum (p : Program) (j : Nat) (n : Name) (vs : List Variant)
    (hr : findRecord p n = none) (he : findEnum p n = some vs) (m : Nat)
    (h : tySize p (j + 1) (.named n) = some m) :
    ∃ x, maxSizes (tySize p j) vs = some x ∧ m = 1 + x := by
  simp only [tySize, sizeTy, hr, he] at h
  cases hx : maxSizes (tySize p j) vs with
  | none => simp [hx] at h
  | some x =>
    simp [hx] at h
    exact ⟨x, rfl, h.symm⟩

theorem isFixed_newtype (p : Program) (k : Nat) (n : Name) (t : Ty)
    (hr : findRecord p n = none) (he : findEnum p n = none) (hn : findNewtype p n = some t)
    (h : isFixed p k (.named n) = some true) : ∃ j, k = j + 1 ∧ isFixed p j t = some true := by
  cases k with
  | zero => simp [isFixed] at h
  | succ j =>
    simp only [isFixed, fixedTy, hr, he, hn] at h
    exact ⟨j, rfl, h⟩

theorem tySize_newtype (p : Program) (j : Nat) (n : Name) (t : Ty)
    (hr : findRecord p n = none) (he : findEnum p n = none) (hn : findNewtype p n = some t) :
    tySize p (j + 1) (.named n) = tySize p j t := by
  simp [tySize, sizeTy, hr, he, hn]


theorem leBytes_length : ∀ (n x : Nat), (leBytes n x).length = n
  | 0, _ => rfl
  | n + 1, x => by simp [leBytes, leBytes_length n]

theorem leValue_leBytes : ∀ (n x : Nat), leValue (leBytes n x) = x % 256 ^ n
  | 0, x => by simp [leBytes, leValue, Nat.mod_one]
  | n + 1, x => by
    simp only [leBytes, leValue, leValue_leBytes n (x / 256)]
    rw [Nat.pow_succ', Nat.mod_mul]
    simp

theorem leValue_lt : ∀ bs : List UInt8, leValue bs < 256 ^ bs.length
  | [] => by simp [leValue]
  | b :: bs => by
    have h1 := leValue_lt bs
    have h2 := b.toNat_lt
    simp only [leValue, List.length_cons, Nat.pow_succ']
    simp only [Nat.reducePow] at h2
    omega

theorem leBytes_leValue : ∀ bs : List UInt8, leBytes bs.length (leValue bs) = bs
  | [] => rfl
  | b :: bs => by
    have h2 := b.toNat_lt
    simp only [Nat.reducePow] at h2
    have e1 : (b.toNat + 256 * leValue bs) % 256 = b.toNat := by omega
    have e2 : (b.toNat + 256 * leValue bs) / 256 = leValue bs := by omega
    simp only [List.length_cons, leBytes, leValue, e1, e2, leBytes_leValue bs, UInt8.ofNat_toNat]

theorem leBytes_eq (bs : List UInt8) (n : Nat) (h : bs.length = n) : leBytes n (leValue bs) = bs :=
  h ▸ leBytes_leValue bs

theorem leValue_small (n x : Nat) (h : x < 256 ^ n) : leValue (leBytes n x) = x := by
  rw [leValue_leBytes, Nat.mod_eq_of_lt h]

theorem takeBytes_append (a b : List UInt8) (n : Nat) (h : a.length = n) :
    takeBytes n (a ++ b) = some (a, b) := by
  subst h
  simp [takeBytes]

theorem takeBytes_inv (n : Nat) (bs a b : List UInt8) (h : takeBytes n bs = some (a, b)) :
    a.length = n ∧ bs = a ++ b := by
  simp only [takeBytes] at h
  split at h
  · simp at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨by simp; omega, by simp⟩
  · simp at h

theorem inRange_iff (x : Int) :
    inRange x = true ↔ -9223372036854775808 ≤ x ∧ x ≤ 9223372036854775807 := by
  simp only [inRange, minInt, maxInt, Bool.and_eq_true]
  constructor
  · intro h
    exact ⟨of_decide_eq_true h.1, of_decide_eq_true h.2⟩
  · intro h
    exact ⟨decide_eq_true h.1, decide_eq_true h.2⟩

theorem decIn_iff (x : Int) :
    decIn x = true ↔ -99999999999999999999999999999999999999 ≤ x ∧
      x ≤ 99999999999999999999999999999999999999 := by
  simp only [decIn, decMax, Bool.and_eq_true, Int.reducePow, Int.reduceSub, Int.reduceNeg]
  constructor
  · intro h
    exact ⟨of_decide_eq_true h.1, of_decide_eq_true h.2⟩
  · intro h
    exact ⟨decide_eq_true h.1, decide_eq_true h.2⟩

theorem intOf8_intBytes (x : Int) (h : inRange x = true) : intOf 8 (intBytes 8 x) = x := by
  rw [inRange_iff] at h
  simp only [intOf, intBytes, leValue_leBytes, Nat.reducePow, Nat.reduceMul, Nat.reduceSub,
    Int.reducePow]
  split <;> omega

theorem intBytes8_intOf (bs : List UInt8) (h : bs.length = 8) : intBytes 8 (intOf 8 bs) = bs := by
  have hl := leValue_lt bs
  rw [h] at hl
  simp only [Nat.reducePow] at hl
  have e : ((intOf 8 bs) % (2 : Int) ^ (8 * 8)).toNat = leValue bs := by
    simp only [intOf, Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Int.reducePow]
    split <;> omega
  simp only [intBytes, e]
  exact leBytes_eq bs 8 h

theorem inRange_intOf8 (bs : List UInt8) (h : bs.length = 8) : inRange (intOf 8 bs) = true := by
  have hl := leValue_lt bs
  rw [h] at hl
  simp only [Nat.reducePow] at hl
  rw [inRange_iff]
  simp only [intOf, Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Int.reducePow]
  split <;> omega

theorem intOf16_intBytes (x : Int) (h : decIn x = true) : intOf 16 (intBytes 16 x) = x := by
  rw [decIn_iff] at h
  simp only [intOf, intBytes, leValue_leBytes, Nat.reducePow, Nat.reduceMul, Nat.reduceSub,
    Int.reducePow]
  split <;> omega

theorem intBytes16_intOf (bs : List UInt8) (h : bs.length = 16) : intBytes 16 (intOf 16 bs) = bs := by
  have hl := leValue_lt bs
  rw [h] at hl
  simp only [Nat.reducePow] at hl
  have e : ((intOf 16 bs) % (2 : Int) ^ (8 * 16)).toNat = leValue bs := by
    simp only [intOf, Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Int.reducePow]
    split <;> omega
  simp only [intBytes, e]
  exact leBytes_eq bs 16 h

theorem utf8_length (s : String) : (utf8 s).length = s.utf8ByteSize := by
  simp only [utf8, String.toUTF8_eq_toByteArray, Array.length_toList]
  rfl

theorem fromUtf8_utf8 (s : String) : fromUtf8 (utf8 s) = some s := by
  simp [fromUtf8, utf8, String.fromUTF8?, s.isValidUTF8]

theorem utf8_fromUtf8 (bs : List UInt8) (s : String) (h : fromUtf8 bs = some s) : utf8 s = bs := by
  simp only [fromUtf8, String.fromUTF8?] at h
  split at h
  · cases h
    simp [utf8, String.fromUTF8]
  · cases h


def Fits : List (Option Nat) → List (List UInt8) → Prop
  | [], [] => True
  | some n :: ks, e :: es => e.length = n ∧ Fits ks es
  | none :: ks, _ :: es => Fits ks es
  | [], _ :: _ => False
  | _ :: _, [] => False

def posList : Nat → List (List UInt8) → List Nat
  | _, [] => []
  | pos, e :: es => pos :: posList (pos + e.length) es

def vparts : List (Option Nat × List UInt8) → List (List UInt8)
  | [] => []
  | (some _, _) :: fs => vparts fs
  | (none, e) :: fs => e :: vparts fs

theorem partBytes_eq : ∀ fs : List (Option Nat × List UInt8), partBytes fs = (vparts fs).flatten
  | [] => rfl
  | (some _, _) :: fs => partBytes_eq fs
  | (none, e) :: fs => by simp [partBytes, vparts, partBytes_eq fs]

theorem fits_length : ∀ (ks : List (Option Nat)) (es : List (List UInt8)), Fits ks es →
    ks.length = es.length
  | [], [], _ => rfl
  | some _ :: ks, _ :: es, h => by simp [fits_length ks es h.2]
  | none :: ks, _ :: es, h => by simp [fits_length ks es h]
  | [], _ :: _, h => h.elim
  | some _ :: _, [], h => h.elim
  | none :: _, [], h => h.elim

theorem slotBytes_length : ∀ (ks : List (Option Nat)) (es : List (List UInt8)) (pos : Nat),
    Fits ks es → (slotBytes pos (ks.zip es)).length = slotsWidth ks
  | [], [], _, _ => rfl
  | some n :: ks, e :: es, pos, h => by
    simp [slotBytes, slotsWidth, slotWidth, h.1, slotBytes_length ks es pos h.2]
  | none :: ks, e :: es, pos, h => by
    simp [slotBytes, slotsWidth, slotWidth, leBytes_length, slotBytes_length ks es _ h]
  | [], _ :: _, _, h => h.elim
  | some _ :: _, [], _, h => h.elim
  | none :: _, [], _, h => h.elim

theorem zip_fst (ks : List (Option Nat)) (es : List (List UInt8)) (hf : Fits ks es) :
    (ks.zip es).map (·.1) = ks :=
  List.map_fst_zip (by rw [fits_length ks es hf]; exact Nat.le_refl _)

theorem compose_eq (h : List UInt8) (ks : List (Option Nat)) (es : List (List UInt8))
    (hf : Fits ks es) :
    compose h (ks.zip es) =
      h ++ (slotBytes (h.length + slotsWidth ks) (ks.zip es) ++ partBytes (ks.zip es)) := by
  simp [compose, zip_fst ks es hf]

theorem compose_length (h : List UInt8) (ks : List (Option Nat)) (es : List (List UInt8))
    (hf : Fits ks es) :
    (compose h (ks.zip es)).length = h.length + slotsWidth ks + (partBytes (ks.zip es)).length := by
  rw [compose_eq h ks es hf]
  simp [slotBytes_length ks es _ hf]
  omega

theorem readSlots_fwd : ∀ (ks : List (Option Nat)) (es : List (List UInt8)) (pos : Nat)
    (rest : List UInt8), Fits ks es → pos + (partBytes (ks.zip es)).length < 2 ^ 32 →
    ∃ xs, readSlots ks (slotBytes pos (ks.zip es) ++ rest) = some xs ∧
      slotOffsets xs = posList pos (vparts (ks.zip es)) ∧
      placeParts xs (vparts (ks.zip es)) = some es
  | [], [], _, _, _, _ => ⟨[], by simp [readSlots], rfl, rfl⟩
  | some n :: ks, e :: es, pos, rest, hf, hb => by
    obtain ⟨xs, h1, h2, h3⟩ := readSlots_fwd ks es pos rest hf.2 (by simpa [partBytes] using hb)
    refine ⟨.bytes e :: xs, ?_, ?_, ?_⟩
    · simp only [List.zip_cons_cons, slotBytes, List.append_assoc, readSlots]
      rw [takeBytes_append e _ n hf.1]
      simp [h1]
    · simp [slotOffsets, vparts, h2]
    · simp [placeParts, vparts, h3]
  | none :: ks, e :: es, pos, rest, hf, hb => by
    have hb' : pos + e.length + (partBytes (ks.zip es)).length < 2 ^ 32 := by
      simp [partBytes] at hb
      omega
    obtain ⟨xs, h1, h2, h3⟩ := readSlots_fwd ks es (pos + e.length) rest hf hb'
    have hpos : leValue (leBytes 4 pos) = pos := leValue_small 4 pos (by simp at hb' ⊢; omega)
    refine ⟨.offset pos :: xs, ?_, ?_, ?_⟩
    · simp only [List.zip_cons_cons, slotBytes, List.append_assoc, readSlots]
      rw [takeBytes_append _ _ 4 (leBytes_length 4 pos)]
      simp [h1, hpos]
    · simp [slotOffsets, vparts, posList, h2]
    · simp [placeParts, vparts, h3]
  | [], _ :: _, _, _, hf, _ => hf.elim
  | some _ :: _, [], _, _, hf, _ => hf.elim
  | none :: _, [], _, _, hf, _ => hf.elim

theorem cutParts_fwd : ∀ (ps : List (List UInt8)) (q : Nat) (e : List UInt8),
    cutParts q (posList (q + e.length) ps) (e ++ ps.flatten) = some (e :: ps)
  | [], q, e => by simp [posList, cutParts]
  | p' :: ps, q, e => by
    have ih := cutParts_fwd ps (q + e.length) p'
    have h1 : q + e.length - q = e.length := by omega
    simp only [posList, cutParts, List.flatten_cons]
    simp [h1, ih]

theorem partsOf_fwd (F : Nat) (bs : List UInt8) (ps : List (List UInt8)) (h1 : F ≤ bs.length)
    (h2 : bs.drop F = ps.flatten) : partsOf F bs (posList F ps) = some ps := by
  cases ps with
  | nil =>
    simp at h2
    simp [posList, partsOf]
    omega
  | cons e ps =>
    simp only [posList, partsOf, beq_self_eq_true, ite_true, h2, List.flatten_cons]
    exact cutParts_fwd ps F e

theorem drop_app2 {α : Type} (a b c : List α) (n : Nat) (h : n = a.length + b.length) :
    (a ++ (b ++ c)).drop n = c := by
  subst h
  rw [← List.append_assoc]
  simp

theorem segments_fwd (p : Program) (h : List UInt8) (ts : List Ty) (ks : List (Option Nat))
    (es : List (List UInt8)) (hks : slotsOf p ts = some ks) (hf : Fits ks es)
    (hl : (compose h (ks.zip es)).length < 2 ^ 32) :
    segments p h.length ts (compose h (ks.zip es)) = some es := by
  have hlen := compose_length h ks es hf
  have hS := slotBytes_length ks es (h.length + slotsWidth ks) hf
  obtain ⟨xs, h1, h2, h3⟩ := readSlots_fwd ks es (h.length + slotsWidth ks)
    (partBytes (ks.zip es)) hf (by omega)
  have hc := compose_eq h ks es hf
  have hd : (compose h (ks.zip es)).drop h.length =
      slotBytes (h.length + slotsWidth ks) (ks.zip es) ++ partBytes (ks.zip es) := by
    rw [hc]
    simp
  have hdF : (compose h (ks.zip es)).drop (h.length + slotsWidth ks) = partBytes (ks.zip es) := by
    rw [hc]
    exact drop_app2 _ _ _ _ (by rw [hS])
  have hp := partsOf_fwd (h.length + slotsWidth ks) (compose h (ks.zip es))
    (vparts (ks.zip es)) (by omega) (by rw [hdF, partBytes_eq])
  have hle : h.length + slotsWidth ks ≤ (compose h (ks.zip es)).length := by omega
  simp only [segments, hks, Option.bind_eq_bind, Option.bind_some, hle, ↓reduceIte]
  rw [hd, h1]
  simp only [Option.bind_some]
  rw [h2, hp]
  simp only [Option.bind_some]
  exact h3

theorem allSome_slots : ∀ (ks : List (Option Nat)) (es : List (List UInt8)) (pos : Nat),
    Fits ks es → (∀ k ∈ ks, k ≠ none) →
    slotBytes pos (ks.zip es) = es.flatten ∧ vparts (ks.zip es) = []
  | [], [], _, _, _ => ⟨rfl, rfl⟩
  | some n :: ks, e :: es, pos, hf, hall => by
    obtain ⟨h1, h2⟩ := allSome_slots ks es pos hf.2 (fun k hk => hall k (by simp [hk]))
    exact ⟨by simp [slotBytes, h1], by simp [vparts, h2]⟩
  | none :: _, _ :: _, _, _, hall => absurd rfl (hall none (by simp))
  | [], _ :: _, _, hf, _ => hf.elim
  | some _ :: _, [], _, hf, _ => hf.elim
  | none :: _, [], _, hf, _ => hf.elim

theorem padded_fwd (p : Program) (ts : List Ty) (ks : List (Option Nat)) (es : List (List UInt8))
    (hks : slotsOf p ts = some ks) (hall : ∀ k ∈ ks, k ≠ none) (hf : Fits ks es) (m : Nat) :
    paddedSegments p ts (es.flatten ++ List.replicate m 0) = some es := by
  obtain ⟨hs, hv⟩ := allSome_slots ks es 0 hf hall
  obtain ⟨xs, h1, _, h3⟩ := readSlots_fwd ks es 0 (List.replicate m 0) hf
    (by rw [partBytes_eq, hv]; simp)
  rw [hs] at h1
  rw [hv] at h3
  have hw : es.flatten.length = slotsWidth ks := by
    rw [← hs, slotBytes_length ks es 0 hf]
  simp only [paddedSegments, hks, Option.bind_eq_bind, Option.bind_some, h1]
  rw [← hw, List.drop_left]
  simp [h3]


def slotsBytesOf : List Slot → List UInt8
  | [] => []
  | .bytes s :: xs => s ++ slotsBytesOf xs
  | .offset o :: xs => leBytes 4 o ++ slotsBytesOf xs

def SlotShape : List (Option Nat) → List Slot → Prop
  | [], [] => True
  | some n :: ks, .bytes s :: xs => s.length = n ∧ SlotShape ks xs
  | none :: ks, .offset _ :: xs => SlotShape ks xs
  | _, _ => False

theorem readSlots_inv : ∀ (ks : List (Option Nat)) (c : List UInt8) (xs : List Slot),
    readSlots ks c = some xs →
      SlotShape ks xs ∧ slotsWidth ks ≤ c.length ∧ c = slotsBytesOf xs ++ c.drop (slotsWidth ks)
  | [], c, xs, h => by
    simp [readSlots] at h
    subst h
    simp [SlotShape, slotsBytesOf, slotsWidth]
  | some n :: ks, c, xs, h => by
    simp only [readSlots] at h
    cases ht : takeBytes n c with
    | none => simp [ht] at h
    | some r =>
      obtain ⟨s, rest⟩ := r
      cases hr : readSlots ks rest with
      | none => simp [ht, hr] at h
      | some ys =>
        simp [ht, hr] at h
        subst h
        obtain ⟨hl, rfl⟩ := takeBytes_inv n c s rest ht
        obtain ⟨h1, h2, h3⟩ := readSlots_inv ks rest ys hr
        refine ⟨⟨hl, h1⟩, ?_, ?_⟩
        · simp [slotsWidth, slotWidth]
          omega
        · have hd : (s ++ rest).drop (slotsWidth (some n :: ks)) = rest.drop (slotsWidth ks) := by
            simp [slotsWidth, slotWidth, ← hl, List.drop_append]
          rw [hd, slotsBytesOf, List.append_assoc, ← h3]
  | none :: ks, c, xs, h => by
    simp only [readSlots] at h
    cases ht : takeBytes 4 c with
    | none => simp [ht] at h
    | some r =>
      obtain ⟨s, rest⟩ := r
      cases hr : readSlots ks rest with
      | none => simp [ht, hr] at h
      | some ys =>
        simp [ht, hr] at h
        subst h
        obtain ⟨hl, rfl⟩ := takeBytes_inv 4 c s rest ht
        obtain ⟨h1, h2, h3⟩ := readSlots_inv ks rest ys hr
        refine ⟨h1, ?_, ?_⟩
        · simp [slotsWidth, slotWidth]
          omega
        · have hd : (s ++ rest).drop (slotsWidth (none :: ks)) = rest.drop (slotsWidth ks) := by
            simp [slotsWidth, slotWidth, ← hl, List.drop_append]
          rw [hd, slotsBytesOf, leBytes_eq s 4 hl, List.append_assoc, ← h3]

theorem cutParts_inv : ∀ (os : List Nat) (pos : Nat) (rest : List UInt8) (ps : List (List UInt8)),
    cutParts pos os rest = some ps → pos :: os = posList pos ps ∧ rest = ps.flatten
  | [], pos, rest, ps, h => by
    simp [cutParts] at h
    subst h
    simp [posList]
  | o :: os, pos, rest, ps, h => by
    simp only [cutParts] at h
    split at h
    · rename_i hc
      simp at hc
      cases hcut : cutParts o os (rest.drop (o - pos)) with
      | none => simp [hcut] at h
      | some qs =>
        simp [hcut] at h
        subst h
        obtain ⟨h1, h2⟩ := cutParts_inv os o _ qs hcut
        constructor
        · have e : pos + min (o - pos) rest.length = o := by omega
          simp [posList, e, ← h1]
        · rw [List.flatten_cons, ← h2, List.take_append_drop]
    · simp at h

theorem partsOf_inv (F : Nat) (bs : List UInt8) (os : List Nat) (ps : List (List UInt8))
    (hF : F ≤ bs.length) (h : partsOf F bs os = some ps) :
    os = posList F ps ∧ bs.drop F = ps.flatten := by
  cases os with
  | nil =>
    simp only [partsOf] at h
    split at h
    · rename_i hl
      simp at h hl
      subst h
      simp [posList]
      omega
    · simp at h
  | cons o os =>
    simp only [partsOf] at h
    split at h
    · rename_i ho
      simp at ho
      subst ho
      exact cutParts_inv os o _ ps h
    · simp at h

theorem placeParts_inv : ∀ (ks : List (Option Nat)) (xs : List Slot) (ps ss : List (List UInt8))
    (F : Nat), SlotShape ks xs → placeParts xs ps = some ss → slotOffsets xs = posList F ps →
    Fits ks ss ∧ slotBytes F (ks.zip ss) = slotsBytesOf xs ∧ partBytes (ks.zip ss) = ps.flatten
  | [], [], ps, ss, F, _, h, _ => by
    cases ps with
    | nil =>
      simp [placeParts] at h
      subst h
      simp [Fits, slotBytes, slotsBytesOf, partBytes]
    | cons q ps => simp [placeParts] at h
  | some n :: ks, .bytes s :: xs, ps, ss, F, hs, h, ho => by
    simp only [placeParts] at h
    cases hp : placeParts xs ps with
    | none => simp [hp] at h
    | some ss' =>
      simp [hp] at h
      subst h
      obtain ⟨h1, h2, h3⟩ := placeParts_inv ks xs ps ss' F hs.2 hp (by simpa [slotOffsets] using ho)
      exact ⟨⟨hs.1, h1⟩, by simp [slotBytes, slotsBytesOf, h2], by simp [partBytes, h3]⟩
  | none :: ks, .offset o :: xs, ps, ss, F, hs, h, ho => by
    cases ps with
    | nil => simp [placeParts] at h
    | cons q ps =>
      simp only [placeParts] at h
      cases hp : placeParts xs ps with
      | none => simp [hp] at h
      | some ss' =>
        simp [hp] at h
        subst h
        simp only [slotOffsets, posList, List.cons.injEq] at ho
        obtain ⟨rfl, ho⟩ := ho
        obtain ⟨h1, h2, h3⟩ := placeParts_inv ks xs ps ss' (o + q.length) hs hp ho
        exact ⟨h1, by simp [slotBytes, slotsBytesOf, h2], by simp [partBytes, h3]⟩
  | [], .bytes _ :: _, _, _, _, hs, _, _ => hs.elim
  | [], .offset _ :: _, _, _, _, hs, _, _ => hs.elim
  | some _ :: _, [], _, _, _, hs, _, _ => hs.elim
  | some _ :: _, .offset _ :: _, _, _, _, hs, _, _ => hs.elim
  | none :: _, [], _, _, _, hs, _, _ => hs.elim
  | none :: _, .bytes _ :: _, _, _, _, hs, _, _ => hs.elim

theorem segments_inv (p : Program) (h : Nat) (ts : List Ty) (bs : List UInt8)
    (ss : List (List UInt8)) (hs : segments p h ts bs = some ss) :
    ∃ ks, slotsOf p ts = some ks ∧ Fits ks ss ∧ h ≤ bs.length ∧
      compose (bs.take h) (ks.zip ss) = bs := by
  simp only [segments] at hs
  cases hks : slotsOf p ts with
  | none => simp [hks] at hs
  | some ks =>
    simp only [hks, Option.bind_eq_bind, Option.bind_some] at hs
    split at hs
    · rename_i hle
      cases hx : readSlots ks (bs.drop h) with
      | none => simp [hx] at hs
      | some xs =>
        cases hp : partsOf (h + slotsWidth ks) bs (slotOffsets xs) with
        | none => simp [hx, hp] at hs
        | some ps =>
          simp only [hx, hp, Option.bind_some] at hs
          obtain ⟨r1, r2, r3⟩ := readSlots_inv ks (bs.drop h) xs hx
          obtain ⟨q1, q2⟩ := partsOf_inv _ bs _ ps hle hp
          obtain ⟨f1, f2, f3⟩ := placeParts_inv ks xs ps ss _ r1 hs q1
          refine ⟨ks, rfl, f1, by omega, ?_⟩
          have hth : (bs.take h).length = h := by simp; omega
          rw [compose_eq _ ks ss f1, hth, f2, f3, ← q2]
          have hdd : (bs.drop h).drop (slotsWidth ks) = bs.drop (h + slotsWidth ks) := by
            simp [List.drop_drop]
          rw [← hdd, ← r3, List.take_append_drop]
    · simp at hs

theorem placeParts_nil : ∀ (ks : List (Option Nat)) (xs : List Slot) (ss : List (List UInt8)),
    SlotShape ks xs → placeParts xs [] = some ss →
      Fits ks ss ∧ slotsBytesOf xs = ss.flatten
  | [], [], ss, _, h => by
    simp [placeParts] at h
    subst h
    simp [Fits, slotsBytesOf]
  | some n :: ks, .bytes s :: xs, ss, hs, h => by
    simp only [placeParts] at h
    cases hp : placeParts xs [] with
    | none => simp [hp] at h
    | some ss' =>
      simp [hp] at h
      subst h
      obtain ⟨h1, h2⟩ := placeParts_nil ks xs ss' hs.2 hp
      exact ⟨⟨hs.1, h1⟩, by simp [slotsBytesOf, h2]⟩
  | none :: _, .offset _ :: _, _, _, h => by simp [placeParts] at h
  | [], .bytes _ :: _, _, hs, _ => hs.elim
  | [], .offset _ :: _, _, hs, _ => hs.elim
  | some _ :: _, [], _, hs, _ => hs.elim
  | some _ :: _, .offset _ :: _, _, hs, _ => hs.elim
  | none :: _, [], _, hs, _ => hs.elim
  | none :: _, .bytes _ :: _, _, hs, _ => hs.elim

theorem padded_inv (p : Program) (ts : List Ty) (c : List UInt8) (ss : List (List UInt8))
    (h : paddedSegments p ts c = some ss) :
    ∃ ks, slotsOf p ts = some ks ∧ Fits ks ss ∧
      c = ss.flatten ++ List.replicate (c.length - ss.flatten.length) 0 := by
  simp only [paddedSegments] at h
  cases hks : slotsOf p ts with
  | none => simp [hks] at h
  | some ks =>
    cases hx : readSlots ks c with
    | none => simp [hks, hx] at h
    | some xs =>
      simp only [hks, hx, Option.bind_eq_bind, Option.bind_some] at h
      split at h
      · rename_i hz
        obtain ⟨r1, r2, r3⟩ := readSlots_inv ks c xs hx
        obtain ⟨f1, f2⟩ := placeParts_nil ks xs ss r1 h
        refine ⟨ks, rfl, f1, ?_⟩
        have hzero : c.drop (slotsWidth ks) = List.replicate (c.length - ss.flatten.length) 0 := by
          rw [List.eq_replicate_iff]
          constructor
          · have := congrArg List.length r3
            rw [f2] at this
            simp at this ⊢
            omega
          · intro b hb
            have := List.all_eq_true.mp hz b hb
            simpa using this
        rw [← hzero, ← f2]
        exact r3
      · simp at h

theorem le_flatten {α : Type} : ∀ (ss : List (List α)) (s : List α), s ∈ ss → s.length ≤ ss.flatten.length
  | [], _, h => by simp at h
  | t :: ts, s, h => by
    rcases List.mem_cons.mp h with rfl | h
    · simp
    · have := le_flatten ts s h
      simp only [List.flatten_cons, List.length_append]
      omega

theorem le_compose : ∀ (ks : List (Option Nat)) (es : List (List UInt8)) (pos : Nat) (s : List UInt8),
    Fits ks es → s ∈ es → s.length ≤ (slotBytes pos (ks.zip es)).length + (partBytes (ks.zip es)).length
  | [], [], _, _, _, h => by simp at h
  | some n :: ks, e :: es, pos, s, hf, h => by
    have ih := le_compose ks es pos s hf.2
    rcases List.mem_cons.mp h with rfl | h
    · simp [slotBytes]
      omega
    · have := ih h
      simp [slotBytes, partBytes]
      omega
  | none :: ks, e :: es, pos, s, hf, h => by
    have ih := le_compose ks es (pos + e.length) s hf
    rcases List.mem_cons.mp h with rfl | h
    · simp [slotBytes, partBytes]
      omega
    · have := ih h
      simp [slotBytes, partBytes]
      omega
  | [], _ :: _, _, _, hf, _ => hf.elim
  | some _ :: _, [], _, _, hf, _ => hf.elim
  | none :: _, [], _, _, hf, _ => hf.elim

theorem le_compose' (h : List UInt8) (ks : List (Option Nat)) (es : List (List UInt8)) (s : List UInt8)
    (hf : Fits ks es) (hs : s ∈ es) : s.length ≤ (compose h (ks.zip es)).length := by
  rw [compose_eq h ks es hf]
  have := le_compose ks es (h.length + slotsWidth ks) s hf hs
  simp
  omega


def FixLen (p : Program) : List Ty → List (List UInt8) → Prop
  | [], [] => True
  | t :: ts, e :: es =>
    (∀ j n, isFixed p j t = some true → tySize p j t = some n → e.length = n) ∧ FixLen p ts es
  | [], _ :: _ => False
  | _ :: _, [] => False

theorem fixLen_fits (p : Program) : ∀ (ts : List Ty) (es : List (List UInt8)) (ks : List (Option Nat)),
    FixLen p ts es → slotsOf p ts = some ks → Fits ks es
  | [], [], ks, _, h => by
    simp [slotsOf] at h
    subst h
    trivial
  | t :: ts, e :: es, ks, hf, h => by
    cases h1 : slotOf p t with
    | none => simp [slotsOf, h1] at h
    | some k =>
      cases h2 : slotsOf p ts with
      | none => simp [slotsOf, h1, h2] at h
      | some ks' =>
        simp [slotsOf, h1, h2] at h
        subst h
        rcases slotOf_some p t k h1 with ⟨rfl, _⟩ | ⟨n, rfl, hfx, hsz⟩
        · exact fixLen_fits p ts es ks' hf.2 h2
        · exact ⟨hf.1 _ n hfx hsz, fixLen_fits p ts es ks' hf.2 h2⟩
  | [], _ :: _, _, hf, _ => hf.elim
  | _ :: _, [], _, hf, _ => hf.elim

theorem fixLen_sum (p : Program) (j : Nat) : ∀ (ts : List Ty) (es : List (List UInt8)) (s : Nat),
    FixLen p ts es → (∀ t ∈ ts, isFixed p j t = some true) → sumSizes (tySize p j) ts = some s →
      es.flatten.length = s
  | [], [], s, _, _, h => by
    simp [sumSizes] at h
    simp [h]
  | t :: ts, e :: es, s, hf, hall, h => by
    cases h1 : tySize p j t with
    | none => simp [sumSizes, h1] at h
    | some x =>
      cases h2 : sumSizes (tySize p j) ts with
      | none => simp [sumSizes, h1, h2] at h
      | some y =>
        simp [sumSizes, h1, h2] at h
        have e1 := hf.1 j x (hall t (by simp)) h1
        have e2 := fixLen_sum p j ts es y hf.2 (fun u hu => hall u (by simp [hu])) h2
        simp only [List.flatten_cons, List.length_append]
        omega
  | [], _ :: _, _, hf, _, _ => hf.elim
  | _ :: _, [], _, hf, _, _ => hf.elim

theorem slots_fixed (p : Program) : ∀ (ts : List Ty), (∀ t ∈ ts, isFixed p (startFuel p) t = some true) →
    ∃ ks, slotsOf p ts = some ks ∧ ∀ k ∈ ks, k ≠ none
  | [], _ => ⟨[], rfl, by simp⟩
  | t :: ts, h => by
    have ht := h t (by simp)
    obtain ⟨n, hn⟩ := fixed_size p _ t ht
    obtain ⟨ks, hks, hall⟩ := slots_fixed p ts (fun u hu => h u (by simp [hu]))
    refine ⟨some n :: ks, by simp [slotsOf, slotOf, ht, hn, hks], ?_⟩
    intro k hk
    rcases List.mem_cons.mp hk with rfl | hk
    · simp
    · exact hall k hk

theorem tySize_option (p : Program) (k : Nat) (t : Ty) (n : Nat) (h : tySize p k (.option t) = some n) :
    ∃ m, tySize p k t = some m ∧ n = 1 + m := by
  cases k with
  | zero => simp [tySize] at h
  | succ j =>
    simp only [tySize, sizeTy] at h
    cases hm : sizeTy p (tySize p j) t with
    | none => simp [hm] at h
    | some m =>
      simp [hm] at h
      exact ⟨m, hm, h.symm⟩

theorem tySize_result (p : Program) (k : Nat) (a b : Ty) (n : Nat)
    (h : tySize p k (.result a b) = some n) :
    ∃ x y, tySize p k a = some x ∧ tySize p k b = some y ∧ n = 1 + max x y := by
  cases k with
  | zero => simp [tySize] at h
  | succ j =>
    simp only [tySize, sizeTy] at h
    cases hx : sizeTy p (tySize p j) a with
    | none => simp [hx] at h
    | some x =>
      cases hy : sizeTy p (tySize p j) b with
      | none => simp [hx, hy] at h
      | some y =>
        simp [hx, hy] at h
        exact ⟨x, y, hx, hy, h.symm⟩

theorem tagged_fixed_len (p : Program) (T : Ty) (tag : Nat) (ts : List Ty) (es : List (List UInt8))
    (e : List UInt8) (k n : Nat) (ht : tagged p T tag ts es = some e) (hf : isFixed p k T = some true)
    (hs : tySize p k T = some n) (hle : es.flatten.length + 1 ≤ n) : e.length = n := by
  simp only [tagged] at ht
  split at ht
  · cases hb : isFixed p (startFuel p) T with
    | none => simp [hb] at ht
    | some b =>
      have hbt := isFixed_det p _ _ T b true hb hf
      subst hbt
      simp only [hb] at ht
      cases hn : tySize p (startFuel p) T with
      | none => simp [hn] at ht
      | some n' =>
        have hnn := tySize_det p _ _ T n' n hn hs
        subst hnn
        simp only [hn, Option.bind_eq_bind, Option.bind_some, padTo] at ht
        split at ht
        · cases ht
          simp only [List.length_append, List.length_cons, List.length_replicate]
          omega
        · cases ht
  · cases ht

mutual
theorem enc_fixed (p : Program) (t : Ty) (v : Value) :
    ∀ (e : List UInt8) (k n : Nat), isFixed p k t = some true → tySize p k t = some n →
      encodeValue p t v = some e → e.length = n := by
  cases v <;> cases t <;> intro e k n hf hs he
  all_goals first | (cases he; done) | skip
  case text.text => exact absurd hf (isFixed_text p k _ (Or.inl rfl))
  case principal.principal => exact absurd hf (isFixed_text p k _ (Or.inr (Or.inl rfl)))
  case stepId.stepId => exact absurd hf (isFixed_text p k _ (Or.inr (Or.inr (Or.inl rfl))))
  case ticket.ticket => exact absurd hf (isFixed_text p k _ (Or.inr (Or.inr (Or.inr rfl))))
  case unit.unit =>
    simp [encodeValue] at he
    subst he
    cases k <;> simp_all [tySize, sizeTy]
  case bool.bool =>
    simp [encodeValue] at he
    subst he
    cases k <;> simp_all [tySize, sizeTy]
  case int.int =>
    simp [encodeValue, intField] at he
    obtain ⟨_, rfl⟩ := he
    cases k <;> simp_all [tySize, sizeTy, intBytes, leBytes_length]
  case time.time =>
    simp [encodeValue, intField] at he
    obtain ⟨_, rfl⟩ := he
    cases k <;> simp_all [tySize, sizeTy, intBytes, leBytes_length]
  case dur.duration =>
    simp [encodeValue, intField] at he
    obtain ⟨_, rfl⟩ := he
    cases k <;> simp_all [tySize, sizeTy, intBytes, leBytes_length]
  case f64.f64 =>
    simp [encodeValue] at he
    obtain ⟨_, rfl⟩ := he
    cases k <;> simp_all [tySize, sizeTy, leBytes_length]
  case f32.f32 =>
    simp [encodeValue] at he
    obtain ⟨_, rfl⟩ := he
    cases k <;> simp_all [tySize, sizeTy, leBytes_length]
  case dec.decimal =>
    simp [encodeValue] at he
    obtain ⟨_, rfl⟩ := he
    cases k <;> simp_all [tySize, sizeTy, intBytes, leBytes_length]
  case none.option t =>
    simp only [encodeValue] at he
    obtain ⟨m, _, rfl⟩ := tySize_option p k t n hs
    exact tagged_fixed_len p _ 0 [] [] e k _ he hf hs (by simp)
  case some.option w t =>
    simp only [encodeValue, Option.bind_eq_bind, Option.bind_eq_some_iff] at he
    obtain ⟨e', h1, h2⟩ := he
    obtain ⟨m, hm, rfl⟩ := tySize_option p k t n hs
    rw [isFixed_option] at hf
    have := enc_fixed p t w e' k m hf hm h1
    exact tagged_fixed_len p _ 1 [t] [e'] e k _ h2 (by rw [isFixed_option]; exact hf) hs (by simp; omega)
  case ok.result w a b =>
    simp only [encodeValue, Option.bind_eq_bind, Option.bind_eq_some_iff] at he
    obtain ⟨e', h1, h2⟩ := he
    obtain ⟨x, y, hx, hy, rfl⟩ := tySize_result p k a b n hs
    have := enc_fixed p a w e' k x (isFixed_result p k a b hf).1 hx h1
    exact tagged_fixed_len p _ 0 [a] [e'] e k _ h2 hf hs (by simp; omega)
  case err.result w a b =>
    simp only [encodeValue, Option.bind_eq_bind, Option.bind_eq_some_iff] at he
    obtain ⟨e', h1, h2⟩ := he
    obtain ⟨x, y, hx, hy, rfl⟩ := tySize_result p k a b n hs
    have := enc_fixed p b w e' k y (isFixed_result p k a b hf).2 hy h1
    exact tagged_fixed_len p _ 1 [b] [e'] e k _ h2 hf hs (by simp; omega)
  case con.named c args nm =>
    simp only [encodeValue] at he
    cases hr : findRecord p nm with
    | some fs => exact absurd hf (isFixed_record p k nm fs hr)
    | none =>
      cases hen : findEnum p nm with
      | some vs =>
        simp only [hr, hen] at he
        cases hv : findVariant c vs with
        | none => simp [hv] at he
        | some iv =>
          obtain ⟨i, v⟩ := iv
          simp only [hv, Option.bind_eq_bind, Option.bind_eq_some_iff] at he
          obtain ⟨es, h1, h2⟩ := he
          obtain ⟨j, rfl, hall⟩ := isFixed_enum p k nm vs hr hen hf
          obtain ⟨x, hx, rfl⟩ := tySize_enum p j nm vs hr hen n hs
          have hvm : v ∈ vs := List.mem_of_getElem? (findVariant_get c vs i v hv).1
          obtain ⟨s, hsum, hle⟩ := maxSizes_ge vs x hx v hvm
          have hfl := enc_fixedList p v.fields args es h1
          have hlen := fixLen_sum p j v.fields es s hfl (hall v hvm) hsum
          exact tagged_fixed_len p _ i v.fields es e (j + 1) _ h2 hf hs (by omega)
      | none =>
        cases hnt : findNewtype p nm with
        | some inner =>
          simp only [hr, hen, hnt] at he
          split at he
          · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at he
            obtain ⟨es, h1, h2⟩ := he
            obtain ⟨j, rfl, hfi⟩ := isFixed_newtype p k nm inner hr hen hnt hf
            rw [tySize_newtype p j nm inner hr hen hnt] at hs
            have hfl := enc_fixedList p [inner] args es h1
            match es, hfl, h2 with
            | [e'], hfl, h2 =>
              simp at h2
              subst h2
              exact hfl.1 j n hfi hs
          · cases he
        | none => simp [hr, hen, hnt] at he
termination_by structural v

theorem enc_fixedList (p : Program) (ts : List Ty) (vs : List Value) :
    ∀ (es : List (List UInt8)), encodeList p ts vs = some es → FixLen p ts es := by
  match ts, vs with
  | [], [] =>
    intro es h
    simp [encodeList] at h
    subst h
    trivial
  | t :: ts, v :: vs =>
    intro es h
    simp only [encodeList, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨e, h1, es', h2, h3⟩ := h
    cases h3
    exact ⟨fun j n hf hs => enc_fixed p t v e j n hf hs h1, enc_fixedList p ts vs es' h2⟩
  | [], _ :: _ => intro es h; simp [encodeList] at h
  | _ :: _, [] => intro es h; simp [encodeList] at h
termination_by structural vs
end


theorem ite_yes {α : Type} {c : Prop} [Decidable c] {a b : α} (h : c) :
    (if c then a else b) = a := by
  simp [h]

theorem padTo_eq (n : Nat) (x : UInt8) (a rest : List UInt8) (hn : n < frameLimit)
    (hlen : n = rest.length + 1) (hc : rest = a ++ List.replicate (rest.length - a.length) 0) :
    padTo n (x :: a) = some (x :: rest) := by
  have hl := congrArg List.length hc
  simp only [List.length_append, List.length_replicate] at hl
  have e : n - (x :: a).length = rest.length - a.length := by
    simp only [List.length_cons]
    omega
  simp only [padTo, ite_yes hn, e]
  conv => rhs; rw [hc]
  simp

theorem tagged_dec (p : Program) (T : Ty) (tag : Nat) (ts : List Ty) (es : List (List UInt8))
    (e : List UInt8) (ht : tagged p T tag ts es = some e) (hfl : FixLen p ts es)
    (hsub : isFixed p (startFuel p) T = some true → ∀ t ∈ ts, isFixed p (startFuel p) t = some true)
    (hlen : ∀ n, isFixed p (startFuel p) T = some true → tySize p (startFuel p) T = some n →
      e.length = n)
    (hlt : e.length < 2 ^ 32) :
    (∃ rest, e = UInt8.ofNat tag :: rest) ∧ tag < 256 ∧ variantSegments p T ts e = some es ∧
      ∀ s ∈ es, s.length ≤ e.length := by
  simp only [tagged] at ht
  split at ht
  · rename_i hg
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hg
    obtain ⟨htag, htn⟩ := hg
    cases hb : isFixed p (startFuel p) T with
    | none => simp [hb] at ht
    | some b =>
      cases b with
      | true =>
        simp only [hb] at ht
        cases hn : tySize p (startFuel p) T with
        | none => simp [hn] at ht
        | some n =>
          simp only [hn, Option.bind_eq_bind, Option.bind_some, padTo] at ht
          split at ht
          · cases ht
            have hl := hlen n hb hn
            obtain ⟨ks, hks, hall⟩ := slots_fixed p ts (hsub hb)
            have hf := fixLen_fits p ts es ks hfl hks
            refine ⟨⟨_, rfl⟩, by simpa using htag, ?_, ?_⟩
            · simp only [variantSegments, htn, hb, hn, ite_true, Option.bind_eq_bind, Option.bind_some]
              rw [ite_yes (by simpa using hl)]
              simp only [List.cons_append, List.drop_succ_cons, List.drop_zero]
              exact padded_fwd p ts ks es hks hall hf _
            · intro s hs
              have := le_flatten es s hs
              simp only [List.length_append, List.length_cons, List.length_replicate]
              omega
          · cases ht
      | false =>
        simp only [hb] at ht
        cases hks : slotsOf p ts with
        | none => simp [hks] at ht
        | some ks =>
          simp only [hks, Option.bind_eq_bind, Option.bind_some] at ht
          cases ht
          have hf := fixLen_fits p ts es ks hfl hks
          refine ⟨⟨_, rfl⟩, by simpa using htag, ?_, ?_⟩
          · simp only [variantSegments, htn, hb, ite_true]
            exact segments_fwd p [UInt8.ofNat tag] ts ks es hks hf hlt
          · intro s hs
            exact le_compose' _ ks es s hf hs
  · cases ht

theorem variant_enc (p : Program) (T : Ty) (ts : List Ty) (bs : List UInt8) (ss : List (List UInt8))
    (tg : UInt8) (rest : List UInt8) (hb : bs = tg :: rest) (h : variantSegments p T ts bs = some ss)
    (hlt : bs.length < 2 ^ 32) :
    tagged p T tg.toNat ts ss = some bs ∧ ∀ s ∈ ss, s.length ≤ bs.length := by
  simp only [variantSegments] at h
  split at h
  · rename_i htn
    have htag : tg.toNat < 2 ^ 8 := tg.toNat_lt
    cases hf : isFixed p (startFuel p) T with
    | none => simp [hf] at h
    | some b =>
      cases b with
      | true =>
        simp only [hf] at h
        cases hn : tySize p (startFuel p) T with
        | none => simp [hn] at h
        | some n =>
          simp only [hn, Option.bind_eq_bind, Option.bind_some] at h
          split at h
          · rename_i hl
            simp at hl
            obtain ⟨ks, hks, hfit, hc⟩ := padded_inv p ts _ ss h
            subst hb
            simp only [List.drop_succ_cons, List.drop_zero] at hc
            have hfl := le_flatten ss
            refine ⟨?_, ?_⟩
            · simp only [tagged, htag, htn, decide_true, Bool.and_self, ite_true, hf, hn,
                Option.bind_eq_bind, Option.bind_some]
              have hn' : n < frameLimit := by simp [frameLimit]; omega
              rw [UInt8.ofNat_toNat]
              exact padTo_eq n tg ss.flatten rest hn' (by simp at hl; omega) hc
            · intro s hs
              have h1 := hfl s hs
              have hcl := congrArg List.length hc
              simp only [List.length_append, List.length_replicate] at hcl
              simp
              omega
          · cases h
      | false =>
        simp only [hf] at h
        obtain ⟨ks, hks, hfit, hle, hc⟩ := segments_inv p 1 ts bs ss h
        have htake : bs.take 1 = [tg] := by simp [hb]
        rw [htake] at hc
        refine ⟨?_, ?_⟩
        · simp only [tagged, htag, htn, decide_true, Bool.and_self, ite_true, hf, hks,
            Option.bind_eq_bind, Option.bind_some, UInt8.ofNat_toNat, hc]
        · intro s hs
          have := le_compose' [tg] ks ss s hfit hs
          rw [hc] at this
          exact this
  · cases h

theorem intBytes_length (n : Nat) (x : Int) : (intBytes n x).length = n :=
  leBytes_length n _

theorem intFields_inv : ∀ (ns : List Int) (es : List (List UInt8)), intFields ns = some es →
    decodeInts es = some ns ∧ (∀ x ∈ es, x.length = 8) ∧ es.length = ns.length
  | [], es, h => by
    simp [intFields] at h
    subst h
    simp [decodeInts]
  | n :: ns, es, h => by
    simp only [intFields, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨e, h1, es', h2, rfl⟩ := h
    simp only [intField] at h1
    split at h1
    · rename_i hr
      cases h1
      obtain ⟨d1, d2, d3⟩ := intFields_inv ns es' h2
      refine ⟨by simp [decodeInts, decodeInt, intBytes_length, intOf8_intBytes n hr, d1], ?_,
        by simp [d3]⟩
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact intBytes_length 8 n
      · exact d2 x hx
    · cases h1

theorem fixLen_int (p : Program) : ∀ es : List (List UInt8), (∀ x ∈ es, x.length = 8) →
    FixLen p (List.replicate es.length .int) es
  | [], _ => trivial
  | e :: es, h => by
    have he := h e (by simp)
    refine ⟨fun j n _ hs => ?_, fixLen_int p es (fun x hx => h x (by simp [hx]))⟩
    cases j with
    | zero => simp [tySize] at hs
    | succ j =>
      simp [tySize, sizeTy] at hs
      omega

theorem stepBytes_inv (p : Program) (m : Name) (key : Ty) (ek : List UInt8) (ns : List Int)
    (e : List UInt8) (h : stepBytes p m key ek ns = some e) :
    ∃ es ks, intFields ns = some es ∧ slotsOf p (key :: List.replicate ns.length .int) = some ks ∧
      e = leBytes 4 (utf8 m).length ++ (utf8 m ++ compose [] (ks.zip (ek :: es))) := by
  simp only [stepBytes, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
  obtain ⟨es, h1, ks, h2, rfl⟩ := h
  exact ⟨es, ks, h1, h2, by simp⟩

theorem initValues_zero (p : Program) (n : Name) (fs : List Param) (h : findRecord p n = some fs) :
    initValues p n 0 = some [] := by
  obtain ⟨inits, hi⟩ := findInits_some p n fs h
  simp [initValues, hi, xvalues]

theorem initValues_zero' (p : Program) (n : Name) (r : List Value) (h : initValues p n 0 = some r) :
    r = [] := by
  simp only [initValues, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨inits, _, h2⟩ := h
  simp [xvalues] at h2
  exact h2


theorem tag0 : (UInt8.ofNat 0 == 0) = true := by decide
theorem tag1 : (UInt8.ofNat 1 == 1) = true := by decide
theorem tag10 : (UInt8.ofNat 1 == 0) = false := by decide

theorem fine_named {p : Program} {k : Nat} {n : Name} (h : Fine p k (.named n)) :
    ∃ j, k = j + 1 ∧ ∀ f : Ty, (∀ y ∈ tyNodes f, y ∈ edges p (.named n)) → Fine p j f := by
  have hk := fine_pos h (x := .named n) (by simp [tyNodes])
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  exact ⟨j, rfl, fun f hf => fine_step h (by simp [tyNodes]) hf⟩

theorem fine_special {p : Program} {k : Nat} {t : Ty} (ht : t = .stepId ∨ t = .ticket)
    (h : Fine p k t) : ∃ j, k = j + 1 ∧ ∀ f : Ty, (∀ y ∈ tyNodes f, y ∈ keyNodes p) → Fine p j f := by
  rcases ht with rfl | rfl
  · have hk := fine_pos h (x := .stepId) (by simp [tyNodes])
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    exact ⟨j, rfl, fun f hf => fine_step h (x := .stepId) (by simp [tyNodes]) hf⟩
  · have hk := fine_pos h (x := .ticket) (by simp [tyNodes])
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    exact ⟨j, rfl, fun f hf => fine_step h (x := .ticket) (by simp [tyNodes]) hf⟩

theorem step_dec (p : Program) (rec : Ty → List UInt8 → Option (Value × Bool)) (m : Name)
    (mach : Machine) (hm : findMachine p m = some mach) (kv : Value) (ek : List UInt8)
    (ns : List Int) (e : List UInt8) (h : stepBytes p m mach.key ek ns = some e)
    (hlt : e.length < 2 ^ 32)
    (hfix : ∀ j n, isFixed p j mach.key = some true → tySize p j mach.key = some n → ek.length = n)
    (hrec : ek.length < 2 ^ 32 → rec mach.key ek = some (kv, true)) :
    decodeStep p rec ns.length e = some (m, kv, ns, true) := by
  obtain ⟨es, ks, h1, h2, rfl⟩ := stepBytes_inv p m mach.key ek ns e h
  obtain ⟨d1, d2, d3⟩ := intFields_inv ns es h1
  have hfl : FixLen p (mach.key :: List.replicate ns.length .int) (ek :: es) :=
    ⟨hfix, by rw [← d3]; exact fixLen_int p es d2⟩
  have hf := fixLen_fits p _ _ ks hfl h2
  simp only [List.length_append, leBytes_length] at hlt
  have hu : leValue (leBytes 4 (utf8 m).length) = (utf8 m).length :=
    leValue_small 4 _ (by simp; omega)
  have hseg := segments_fwd p [] _ ks (ek :: es) h2 hf (by omega)
  have hek : ek.length < 2 ^ 32 := by
    have := le_compose' [] ks (ek :: es) ek hf (by simp)
    omega
  simp only [decodeStep, takeBytes_append _ _ 4 (leBytes_length 4 _), hu,
    takeBytes_append _ _ _ rfl, Option.bind_eq_bind, Option.bind_some, fromUtf8_utf8, hm]
  simp only [List.length_nil] at hseg
  simp only [hseg, Option.bind_some, hrec hek, d1]

mutual
theorem dec_enc (p : Program) (hc : check p = .ok ()) (t : Ty) (v : Value) :
    ∀ (k : Nat) (e : List UInt8), Fine p k t → encodeValue p t v = some e → e.length < 2 ^ 32 →
      decodeAt p (k + 1) t e = some (v, true) := by
  cases v <;> cases t <;> intro k e hfine he hlt
  all_goals first | (cases he; done) | skip
  case unit.unit =>
    simp [encodeValue] at he
    subst he
    simp [decodeAt, decodeTy]
  case bool.bool b =>
    simp [encodeValue] at he
    subst he
    cases b <;> simp [decodeAt, decodeTy]
  case int.int n =>
    simp only [encodeValue, intField] at he
    split at he
    · rename_i hr
      cases he
      simp [decodeAt, decodeTy, decodeInt, intBytes_length, intOf8_intBytes n hr]
    · cases he
  case time.time n =>
    simp only [encodeValue, intField] at he
    split at he
    · rename_i hr
      cases he
      simp [decodeAt, decodeTy, decodeInt, intBytes_length, intOf8_intBytes n hr]
    · cases he
  case dur.duration n =>
    simp only [encodeValue, intField] at he
    split at he
    · rename_i hr
      cases he
      simp [decodeAt, decodeTy, decodeInt, intBytes_length, intOf8_intBytes n hr]
    · cases he
  case f64.f64 b =>
    simp only [encodeValue] at he
    split at he
    · rename_i hok
      cases he
      have hv : leValue (leBytes 8 b.toNat) = b.toNat :=
        leValue_small 8 _ (by have := b.toNat_lt; simp at this ⊢; omega)
      simp [decodeAt, decodeTy, leBytes_length, hv, hok]
    · cases he
  case f32.f32 b =>
    simp only [encodeValue] at he
    split at he
    · rename_i hok
      cases he
      have hv : leValue (leBytes 4 b.toNat) = b.toNat :=
        leValue_small 4 _ (by have := b.toNat_lt; simp at this ⊢; omega)
      simp [decodeAt, decodeTy, leBytes_length, hv, hok]
    · cases he
  case dec.decimal s' c s =>
    simp only [encodeValue] at he
    split at he
    · rename_i hok
      cases he
      simp only [Bool.and_eq_true, beq_iff_eq] at hok
      obtain ⟨rfl, hd⟩ := hok
      simp [decodeAt, decodeTy, intBytes_length, intOf16_intBytes c hd, hd]
    · cases he
  case text.text s =>
    simp [encodeValue] at he
    subst he
    simp [decodeAt, decodeTy, fromUtf8_utf8]
  case principal.principal s =>
    simp [encodeValue] at he
    subst he
    simp [decodeAt, decodeTy, fromUtf8_utf8]
  case stepId.stepId m kv l q =>
    have he0 := he
    simp only [encodeValue] at he
    cases hm : findMachine p m with
    | none => simp [hm] at he
    | some mach =>
      simp only [hm, Option.bind_eq_bind, Option.bind_eq_some_iff] at he
      obtain ⟨ek, h1, h2⟩ := he
      obtain ⟨j, rfl, hf⟩ := fine_special (Or.inl rfl) hfine
      have hd : decodeStep p (decodeAt p (j + 1)) 2 e = some (m, kv, [l, q], true) :=
        step_dec p (decodeAt p (j + 1)) m mach hm kv ek [l, q] e h2 hlt
          (fun j' n hx hs => enc_fixed p mach.key kv ek j' n hx hs h1)
          (fun hl => dec_enc p hc mach.key kv j ek (hf _ (key_nodes p m mach hm)) h1 hl)
      show decodeTy p (decodeAt p (j + 1)) .stepId e = _
      simp only [decodeTy, Option.bind_eq_bind, hd, Option.bind_some]
  case ticket.ticket m kv l q i =>
    simp only [encodeValue] at he
    cases hm : findMachine p m with
    | none => simp [hm] at he
    | some mach =>
      simp only [hm, Option.bind_eq_bind, Option.bind_eq_some_iff] at he
      obtain ⟨ek, h1, h2⟩ := he
      obtain ⟨j, rfl, hf⟩ := fine_special (Or.inr rfl) hfine
      have hd : decodeStep p (decodeAt p (j + 1)) 3 e = some (m, kv, [l, q, i], true) :=
        step_dec p (decodeAt p (j + 1)) m mach hm kv ek [l, q, i] e h2 hlt
          (fun j' n hx hs => enc_fixed p mach.key kv ek j' n hx hs h1)
          (fun hl => dec_enc p hc mach.key kv j ek (hf _ (key_nodes p m mach hm)) h1 hl)
      show decodeTy p (decodeAt p (j + 1)) .ticket e = _
      simp only [decodeTy, Option.bind_eq_bind, hd, Option.bind_some]
  case none.option t =>
    have he0 := he
    simp only [encodeValue] at he
    obtain ⟨⟨rest, rfl⟩, _, hvs, _⟩ := tagged_dec p (.option t) 0 [] [] e he trivial
      (fun _ u hu => by simp at hu)
      (fun n h1 h2 => enc_fixed p (.option t) .none _ _ n h1 h2 he0) hlt
    show decodeTy p (decodeAt p k) (.option t) _ = _
    simp only [decodeTy, tag0, ite_true, hvs, Option.bind_eq_bind, Option.bind_some,
      List.isEmpty_nil]
  case some.option w t =>
    have he0 := he
    simp only [encodeValue, Option.bind_eq_bind, Option.bind_eq_some_iff] at he
    obtain ⟨e', h1, h2⟩ := he
    obtain ⟨⟨rest, rfl⟩, _, hvs, hsub⟩ := tagged_dec p (.option t) 1 [t] [e'] _ h2
      ⟨fun j n hx hs => enc_fixed p t w e' j n hx hs h1, trivial⟩
      (fun hx u hu => by simp at hu; subst hu; rwa [isFixed_option] at hx)
      (fun n hx hs => enc_fixed p (.option t) (.some w) _ _ n hx hs he0) hlt
    have ih : decodeTy p (decodeAt p k) t e' = some (w, true) :=
      dec_enc p hc t w k e' hfine h1 (by have := hsub e' (by simp); omega)
    show decodeTy p (decodeAt p k) (.option t) _ = _
    simp only [decodeTy, tag1, tag10, ite_true, ite_false, Bool.false_eq_true, hvs,
      Option.bind_eq_bind, Option.bind_some, ih, Option.map_some]
  case ok.result w a b =>
    have he0 := he
    simp only [encodeValue, Option.bind_eq_bind, Option.bind_eq_some_iff] at he
    obtain ⟨e', h1, h2⟩ := he
    obtain ⟨⟨rest, rfl⟩, _, hvs, hsub⟩ := tagged_dec p (.result a b) 0 [a] [e'] _ h2
      ⟨fun j n hx hs => enc_fixed p a w e' j n hx hs h1, trivial⟩
      (fun hx u hu => by simp only [List.mem_singleton] at hu; rw [hu]; exact (isFixed_result p _ a b hx).1)
      (fun n hx hs => enc_fixed p (.result a b) (.ok w) _ _ n hx hs he0) hlt
    have ih : decodeTy p (decodeAt p k) a e' = some (w, true) :=
      dec_enc p hc a w k e' (fine_left hfine) h1 (by have := hsub e' (by simp); omega)
    show decodeTy p (decodeAt p k) (.result a b) _ = _
    simp only [decodeTy, tag0, ite_true, hvs, Option.bind_eq_bind, Option.bind_some, ih,
      Option.map_some]
  case err.result w a b =>
    have he0 := he
    simp only [encodeValue, Option.bind_eq_bind, Option.bind_eq_some_iff] at he
    obtain ⟨e', h1, h2⟩ := he
    obtain ⟨⟨rest, rfl⟩, _, hvs, hsub⟩ := tagged_dec p (.result a b) 1 [b] [e'] _ h2
      ⟨fun j n hx hs => enc_fixed p b w e' j n hx hs h1, trivial⟩
      (fun hx u hu => by simp only [List.mem_singleton] at hu; rw [hu]; exact (isFixed_result p _ a b hx).2)
      (fun n hx hs => enc_fixed p (.result a b) (.err w) _ _ n hx hs he0) hlt
    have ih : decodeTy p (decodeAt p k) b e' = some (w, true) :=
      dec_enc p hc b w k e' (fine_right hfine) h1 (by have := hsub e' (by simp); omega)
    show decodeTy p (decodeAt p k) (.result a b) _ = _
    simp only [decodeTy, tag1, tag10, ite_true, ite_false, Bool.false_eq_true, hvs,
      Option.bind_eq_bind, Option.bind_some, ih, Option.map_some]
  case con.named c args nm =>
    have he0 := he
    simp only [encodeValue] at he
    obtain ⟨j, rfl, hf⟩ := fine_named hfine
    cases hr : findRecord p nm with
    | some fs =>
      simp only [hr] at he
      split at he
      · rename_i hcn
        simp only [beq_iff_eq] at hcn
        subst hcn
        simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at he
        obtain ⟨es, h1, h2⟩ := he
        simp only [recordBytes] at h2
        split at h2
        · rename_i hlen
          cases hks : slotsOf p (fs.map (·.ty)) with
          | none => simp [hks] at h2
          | some ks =>
            simp only [hks, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at h2
            subst h2
            simp only [List.length_map] at hlt ⊢
            have hfl := enc_fixedList p _ args es h1
            have hfit := fixLen_fits p _ es ks hfl hks
            simp only [List.length_map] at hlen
            have hcnt : leValue (leBytes 2 fs.length) = fs.length :=
              leValue_small 2 _ (by simp; omega)
            have hseg := segments_fwd p (leBytes 2 fs.length) _ ks es hks hfit
              (by simpa using hlt)
            rw [leBytes_length] at hseg
            have hfs := dec_encList p hc (fs.map (·.ty)) args j es
              (fun t ht => by
                obtain ⟨f, hfm, rfl⟩ := List.mem_map.mp ht
                exact hf _ (record_nodes p c fs hr f hfm))
              h1 (fun s hs => by
                have := le_compose' (leBytes 2 fs.length) ks es s hfit hs
                omega)
            have hta : takeBytes 2 (compose (leBytes 2 fs.length) (ks.zip es)) =
                some (leBytes 2 fs.length, slotBytes ((leBytes 2 fs.length).length + slotsWidth ks)
                  (ks.zip es) ++ partBytes (ks.zip es)) := by
              rw [compose_eq _ ks es hfit]
              exact takeBytes_append _ _ 2 (leBytes_length 2 _)
            show decodeTy p (decodeAt p (j + 1)) (.named c) _ = _
            simp only [decodeTy, hr, decodeRecord, hta, Option.bind_eq_bind, Option.bind_some]
            simp only [hcnt, Nat.le_refl, ite_true, List.take_length, hseg, Option.bind_some, hfs,
              Nat.sub_self, initValues_zero p c fs hr, List.append_nil, beq_self_eq_true,
              Bool.and_self]
        · cases h2
      · cases he
    | none =>
      cases hen : findEnum p nm with
      | some vs =>
        simp only [hr, hen] at he
        cases hv : findVariant c vs with
        | none => simp [hv] at he
        | some iv =>
          obtain ⟨i, v⟩ := iv
          simp only [hv, Option.bind_eq_bind, Option.bind_eq_some_iff] at he
          obtain ⟨es, h1, h2⟩ := he
          have hfl := enc_fixedList p v.fields args es h1
          obtain ⟨hget, hname⟩ := findVariant_get c vs i v hv
          have hvm : v ∈ vs := List.mem_of_getElem? hget
          obtain ⟨⟨rest, rfl⟩, hi, hvs, hsub⟩ := tagged_dec p (.named nm) i v.fields es _ h2 hfl
            (fun hx f hfm => by
              obtain ⟨j', hj', hall⟩ := isFixed_enum p _ nm vs hr hen hx
              exact isFixed_le p j' f true (hall v hvm f hfm) _ (by omega))
            (fun n hx hs => enc_fixed p (.named nm) (.con c args) _ _ n hx hs he0) hlt
          have hfs := dec_encList p hc v.fields args j es
            (fun f hfm => hf f (fun y hy => enum_nodes p nm vs hen v hvm f hfm y hy))
            h1 (fun s hs => by have := hsub s hs; omega)
          have htag : (UInt8.ofNat i).toNat = i := by simp; omega
          have hidx : (findVariant c vs).map (·.1) = some i := by
            rw [hv]
            rfl
          show decodeTy p (decodeAt p (j + 1)) (.named nm) _ = _
          simp only [decodeTy, hr, hen, htag, hget, hvs, Option.bind_eq_bind, Option.bind_some,
            hfs, hname, hidx, beq_self_eq_true, ite_true]
      | none =>
        cases hnt : findNewtype p nm with
        | some inner =>
          simp only [hr, hen, hnt] at he
          split at he
          · rename_i hcn
            simp only [beq_iff_eq] at hcn
            subst hcn
            match args, he with
            | [w], he =>
              simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at he
              obtain ⟨es, h1, h2⟩ := he
              simp only [encodeList, Option.bind_eq_bind, Option.bind_eq_some_iff,
                Option.some.injEq] at h1
              obtain ⟨e', h1, es', h3, rfl⟩ := h1
              simp at h3
              subst h3
              simp at h2
              subst h2
              have ih := dec_enc p hc inner w j _ (hf inner (newtype_nodes p c inner hnt)) h1 hlt
              show decodeTy p (decodeAt p (j + 1)) (.named c) _ = _
              simp only [decodeTy, hr, hen, hnt]
              rw [ih]
              rfl
            | [], he => simp [encodeList] at he
            | _ :: _ :: _, he => simp [encodeList] at he
          · cases he
        | none => simp [hr, hen, hnt] at he
termination_by structural v

theorem dec_encList (p : Program) (hc : check p = .ok ()) (ts : List Ty) (vs : List Value) :
    ∀ (k : Nat) (es : List (List UInt8)), (∀ t ∈ ts, Fine p k t) → encodeList p ts vs = some es →
      (∀ e ∈ es, e.length < 2 ^ 32) → decodeFields (decodeAt p (k + 1)) ts es = some (vs, true) := by
  match ts, vs with
  | [], [] =>
    intro k es _ h _
    simp [encodeList] at h
    subst h
    simp [decodeFields]
  | t :: ts, v :: vs =>
    intro k es hf h hl
    simp only [encodeList, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨e, h1, es', h2, h3⟩ := h
    cases h3
    have i1 := dec_enc p hc t v k e (hf t (by simp)) h1 (hl e (by simp))
    have i2 := dec_encList p hc ts vs k es' (fun u hu => hf u (by simp [hu])) h2
      (fun x hx => hl x (by simp [hx]))
    simp [decodeFields, i1, i2]
  | [], _ :: _ => intro k es _ h; simp [encodeList] at h
  | _ :: _, [] => intro k es _ h; simp [encodeList] at h
termination_by structural vs
end


theorem tagged_named (p : Program) (T : Ty) (tag : Nat) (ts : List Ty) (es : List (List UInt8))
    (e : List UInt8) (h : tagged p T tag ts es = some e) : typeNamed p T = true := by
  simp only [tagged] at h
  split at h
  · rename_i hg
    simp only [Bool.and_eq_true] at hg
    exact hg.2
  · cases h

theorem intFields_range : ∀ (ns : List Int) (es : List (List UInt8)), intFields ns = some es →
    ∀ n ∈ ns, inRange n = true
  | [], _, _, n, hn => by simp at hn
  | m :: ns, es, h, n, hn => by
    simp only [intFields, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨e, h1, es', h2, _⟩ := h
    rcases List.mem_cons.mp hn with rfl | hn
    · simp only [intField] at h1
      split at h1
      · assumption
      · cases h1
    · exact intFields_range ns es' h2 n hn

mutual
theorem enc_typed (p : Program) (t : Ty) (v : Value) :
    ∀ (e : List UInt8), encodeValue p t v = some e → Typed p t v := by
  cases v <;> cases t <;> intro e he
  all_goals first | (cases he; done) | skip
  case unit.unit => simp [Typed]
  case bool.bool => simp [Typed]
  case text.text => simp [Typed]
  case principal.principal => simp [Typed]
  case int.int n =>
    simp only [encodeValue, intField] at he
    split at he
    · simpa [Typed]
    · cases he
  case time.time n =>
    simp only [encodeValue, intField] at he
    split at he
    · simpa [Typed]
    · cases he
  case dur.duration n =>
    simp only [encodeValue, intField] at he
    split at he
    · simpa [Typed]
    · cases he
  case f64.f64 b =>
    simp only [encodeValue] at he
    split at he
    · simpa [Typed]
    · cases he
  case f32.f32 b =>
    simp only [encodeValue] at he
    split at he
    · simpa [Typed]
    · cases he
  case dec.decimal s' c s =>
    simp only [encodeValue] at he
    split at he
    · rename_i hok
      simp only [Bool.and_eq_true, beq_iff_eq] at hok
      simpa [Typed] using hok
    · cases he
  case stepId.stepId m kv l q =>
    simp only [encodeValue] at he
    cases hm : findMachine p m with
    | none => simp [hm] at he
    | some mach =>
      simp only [hm, Option.bind_eq_bind, Option.bind_eq_some_iff] at he
      obtain ⟨ek, h1, h2⟩ := he
      obtain ⟨es, ks, hi, _, _⟩ := stepBytes_inv p m mach.key ek [l, q] e h2
      have hr := intFields_range [l, q] es hi
      simp only [Typed, hm]
      exact ⟨enc_typed p mach.key kv ek h1, hr l (by simp), hr q (by simp)⟩
  case ticket.ticket m kv l q i =>
    simp only [encodeValue] at he
    cases hm : findMachine p m with
    | none => simp [hm] at he
    | some mach =>
      simp only [hm, Option.bind_eq_bind, Option.bind_eq_some_iff] at he
      obtain ⟨ek, h1, h2⟩ := he
      obtain ⟨es, ks, hi, _, _⟩ := stepBytes_inv p m mach.key ek [l, q, i] e h2
      have hr := intFields_range [l, q, i] es hi
      simp only [Typed, hm]
      exact ⟨enc_typed p mach.key kv ek h1, hr l (by simp), hr q (by simp), hr i (by simp)⟩
  case none.option t =>
    simp only [encodeValue] at he
    exact tagged_named p (.option t) _ _ _ _ he
  case some.option w t =>
    simp only [encodeValue, Option.bind_eq_bind, Option.bind_eq_some_iff] at he
    obtain ⟨e', h1, _⟩ := he
    exact enc_typed p t w e' h1
  case ok.result w a b =>
    simp only [encodeValue, Option.bind_eq_bind, Option.bind_eq_some_iff] at he
    obtain ⟨e', h1, h2⟩ := he
    have hn := tagged_named p _ _ _ _ _ h2
    simp only [typeNamed, Bool.and_eq_true] at hn
    exact ⟨enc_typed p a w e' h1, hn.2⟩
  case err.result w a b =>
    simp only [encodeValue, Option.bind_eq_bind, Option.bind_eq_some_iff] at he
    obtain ⟨e', h1, h2⟩ := he
    have hn := tagged_named p _ _ _ _ _ h2
    simp only [typeNamed, Bool.and_eq_true] at hn
    exact ⟨hn.1, enc_typed p b w e' h1⟩
  case con.named c args nm =>
    simp only [encodeValue] at he
    cases hr : findRecord p nm with
    | some fs =>
      simp only [hr] at he
      split at he
      · rename_i hcn
        simp only [beq_iff_eq] at hcn
        simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at he
        obtain ⟨es, h1, _⟩ := he
        simp only [Typed, hr]
        exact ⟨hcn, enc_typedList p _ args es h1⟩
      · cases he
    | none =>
      cases hen : findEnum p nm with
      | some vs =>
        simp only [hr, hen] at he
        cases hv : findVariant c vs with
        | none => simp [hv] at he
        | some iv =>
          obtain ⟨i, v⟩ := iv
          simp only [hv, Option.bind_eq_bind, Option.bind_eq_some_iff] at he
          obtain ⟨es, h1, _⟩ := he
          simp only [Typed, hr, hen, hv]
          exact enc_typedList p _ args es h1
      | none =>
        cases hnt : findNewtype p nm with
        | some inner =>
          simp only [hr, hen, hnt] at he
          split at he
          · rename_i hcn
            simp only [beq_iff_eq] at hcn
            simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at he
            obtain ⟨es, h1, _⟩ := he
            simp only [Typed, hr, hen, hnt]
            exact ⟨hcn, enc_typedList p _ args es h1⟩
          · cases he
        | none => simp [hr, hen, hnt] at he
termination_by structural v

theorem enc_typedList (p : Program) (ts : List Ty) (vs : List Value) :
    ∀ (es : List (List UInt8)), encodeList p ts vs = some es → TypedList p ts vs := by
  match ts, vs with
  | [], [] => intro _ _; simp [TypedList]
  | t :: ts, v :: vs =>
    intro es h
    simp only [encodeList, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨e, h1, es', h2, _⟩ := h
    simp only [TypedList]
    exact ⟨enc_typed p t v e h1, enc_typedList p ts vs es' h2⟩
  | [], _ :: _ => intro es h; simp [encodeList] at h
  | _ :: _, [] => intro es h; simp [encodeList] at h
termination_by structural vs
end

theorem slotsOf_length (p : Program) : ∀ (ts : List Ty) (ks : List (Option Nat)),
    slotsOf p ts = some ks → ks.length = ts.length
  | [], ks, h => by
    simp [slotsOf] at h
    subst h
    rfl
  | t :: ts, ks, h => by
    cases h1 : slotOf p t with
    | none => simp [slotsOf, h1] at h
    | some k =>
      cases h2 : slotsOf p ts with
      | none => simp [slotsOf, h1, h2] at h
      | some ks' =>
        simp [slotsOf, h1, h2] at h
        subst h
        simp [slotsOf_length p ts ks' h2]

theorem decodeInts_inv : ∀ (ss : List (List UInt8)) (ns : List Int), decodeInts ss = some ns →
    intFields ns = some ss
  | [], ns, h => by
    simp [decodeInts] at h
    subst h
    rfl
  | s :: ss, ns, h => by
    simp only [decodeInts, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨n, h1, ns', h2, h3⟩ := h
    cases h3
    simp only [decodeInt] at h1
    split at h1
    · rename_i hl
      cases h1
      simp at hl
      simp [intFields, intField, inRange_intOf8 s hl, intBytes8_intOf s hl,
        decodeInts_inv ss ns' h2]
    · cases h1

theorem step_enc (p : Program) (rec : Ty → List UInt8 → Option (Value × Bool))
    (hrec : ∀ t bs v, rec t bs = some (v, true) → bs.length < 2 ^ 32 → encodeValue p t v = some bs)
    (count : Nat) (bs : List UInt8) (m : Name) (kv : Value) (ns : List Int)
    (h : decodeStep p rec count bs = some (m, kv, ns, true)) (hlt : bs.length < 2 ^ 32) :
    ∃ mach, findMachine p m = some mach ∧ ∃ ek, encodeValue p mach.key kv = some ek ∧
      stepBytes p m mach.key ek ns = some bs := by
  simp only [decodeStep] at h
  cases h1 : takeBytes 4 bs with
  | none => simp [h1] at h
  | some r1 =>
    obtain ⟨len, rest⟩ := r1
    cases h2 : takeBytes (leValue len) rest with
    | none => simp [h1, h2] at h
    | some r2 =>
      obtain ⟨name, body⟩ := r2
      cases h3 : fromUtf8 name with
      | none => simp [h1, h2, h3] at h
      | some m' =>
        cases h4 : findMachine p m' with
        | none => simp [h1, h2, h3, h4] at h
        | some mach =>
          cases h5 : segments p 0 (mach.key :: List.replicate count .int) body with
          | none => simp [h1, h2, h3, h4, h5] at h
          | some ss =>
            cases ss with
            | nil => simp [h1, h2, h3, h4, h5] at h
            | cons sk sn =>
              cases h6 : rec mach.key sk with
              | none => simp [h1, h2, h3, h4, h5, h6] at h
              | some r6 =>
                obtain ⟨kv', f⟩ := r6
                cases h7 : decodeInts sn with
                | none => simp [h1, h2, h3, h4, h5, h6, h7] at h
                | some ns' =>
                  simp [h1, h2, h3, h4, h5, h6, h7] at h
                  obtain ⟨rfl, rfl, rfl, rfl⟩ := h
                  obtain ⟨hl1, rfl⟩ := takeBytes_inv 4 bs len rest h1
                  obtain ⟨hl2, rfl⟩ := takeBytes_inv _ rest name body h2
                  obtain ⟨ks, hks, hfit, _, hcomp⟩ := segments_inv p 0 _ body _ h5
                  have hsk : sk.length < 2 ^ 32 := by
                    have := le_compose' (body.take 0) ks (sk :: sn) sk hfit (by simp)
                    rw [hcomp] at this
                    simp at hlt
                    omega
                  have hek := hrec mach.key sk kv' h6 hsk
                  have hint := decodeInts_inv sn ns' h7
                  have hlen : ns'.length = count := by
                    have a1 := slotsOf_length p _ ks hks
                    have a2 := fits_length ks _ hfit
                    have a3 := (intFields_inv ns' sn hint).2.2
                    simp at a1 a2
                    omega
                  refine ⟨mach, h4, sk, hek, ?_⟩
                  have hu := utf8_fromUtf8 name m' h3
                  simp only [stepBytes, hint, hlen, hks, Option.bind_eq_bind, Option.bind_some]
                  rw [hu, hl2, leBytes_eq len 4 hl1]
                  simp only [List.take_zero] at hcomp
                  rw [hcomp]
                  simp

theorem enc_dec_fields (p : Program) (rec : Ty → List UInt8 → Option (Value × Bool))
    (hrec : ∀ t bs v, rec t bs = some (v, true) → bs.length < 2 ^ 32 → encodeValue p t v = some bs) :
    ∀ (ts : List Ty) (ss : List (List UInt8)) (vs : List Value),
      decodeFields rec ts ss = some (vs, true) → (∀ s ∈ ss, s.length < 2 ^ 32) →
        encodeList p ts vs = some ss
  | [], [], vs, h, _ => by
    simp [decodeFields] at h
    subst h
    rfl
  | t :: ts, s :: ss, vs, h, hl => by
    simp only [decodeFields, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨v, f⟩, h1, ⟨vs', g⟩, h2, h3⟩ := h
    simp at h3
    obtain ⟨rfl, hf, hg⟩ := h3
    subst hf
    subst hg
    have e1 := hrec t s v h1 (hl s (by simp))
    have e2 := enc_dec_fields p rec hrec ts ss vs' h2 (fun x hx => hl x (by simp [hx]))
    simp [encodeList, e1, e2]
  | [], _ :: _, _, h, _ => by simp [decodeFields] at h
  | _ :: _, [], _, h, _ => by simp [decodeFields] at h


theorem enc_dec_ty (p : Program) (rec : Ty → List UInt8 → Option (Value × Bool))
    (hrec : ∀ t bs v, rec t bs = some (v, true) → bs.length < 2 ^ 32 → encodeValue p t v = some bs) :
    ∀ (t : Ty) (bs : List UInt8) (v : Value), decodeTy p rec t bs = some (v, true) →
      bs.length < 2 ^ 32 → encodeValue p t v = some bs
  | .unit, bs, v, h, _ => by
    simp only [decodeTy] at h
    split at h
    · rename_i he
      cases h
      simp at he
      subst he
      rfl
    · cases h
  | .bool, bs, v, h, _ => by
    simp only [decodeTy] at h
    split at h
    · rename_i b
      split at h
      · rename_i hb
        cases h
        simp at hb
        subst hb
        rfl
      · split at h
        · rename_i _ hb
          cases h
          simp at hb
          subst hb
          rfl
        · cases h
    · cases h
  | .int, bs, v, h, _ => by
    simp only [decodeTy, decodeInt] at h
    split at h
    · rename_i hl
      simp at h hl
      subst h
      simp [encodeValue, intField, inRange_intOf8 bs hl, intBytes8_intOf bs hl]
    · simp at h
  | .time, bs, v, h, _ => by
    simp only [decodeTy, decodeInt] at h
    split at h
    · rename_i hl
      simp at h hl
      subst h
      simp [encodeValue, intField, inRange_intOf8 bs hl, intBytes8_intOf bs hl]
    · simp at h
  | .duration, bs, v, h, _ => by
    simp only [decodeTy, decodeInt] at h
    split at h
    · rename_i hl
      simp at h hl
      subst h
      simp [encodeValue, intField, inRange_intOf8 bs hl, intBytes8_intOf bs hl]
    · simp at h
  | .f64, bs, v, h, _ => by
    simp only [decodeTy] at h
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      obtain ⟨hl, hok⟩ := hc
      cases h
      have hlt := leValue_lt bs
      rw [hl] at hlt
      have ht : (UInt64.ofNat (leValue bs)).toNat = leValue bs := by
        simp
        simp at hlt
        omega
      simp [encodeValue, ht, hok, leBytes_eq bs 8 hl]
    · cases h
  | .f32, bs, v, h, _ => by
    simp only [decodeTy] at h
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      obtain ⟨hl, hok⟩ := hc
      cases h
      have hlt := leValue_lt bs
      rw [hl] at hlt
      have ht : (UInt32.ofNat (leValue bs)).toNat = leValue bs := by
        simp
        simp at hlt
        omega
      simp [encodeValue, ht, hok, leBytes_eq bs 4 hl]
    · cases h
  | .decimal s, bs, v, h, _ => by
    simp only [decodeTy] at h
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      obtain ⟨hl, hok⟩ := hc
      cases h
      simp [encodeValue, hok, intBytes16_intOf bs hl]
    · cases h
  | .text, bs, v, h, _ => by
    simp only [decodeTy, Option.map_eq_some_iff] at h
    obtain ⟨s, hs, he⟩ := h
    cases he
    simp [encodeValue, utf8_fromUtf8 bs s hs]
  | .principal, bs, v, h, _ => by
    simp only [decodeTy, Option.map_eq_some_iff] at h
    obtain ⟨s, hs, he⟩ := h
    cases he
    simp [encodeValue, utf8_fromUtf8 bs s hs]
  | .stepId, bs, v, h, hlt => by
    simp only [decodeTy, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨m, kv, ns, f⟩, h1, h2⟩ := h
    match ns, h2 with
    | [l, q], h2 =>
      simp at h2
      obtain ⟨rfl, rfl⟩ := h2
      obtain ⟨mach, hm, ek, hek, hsb⟩ := step_enc p rec hrec 2 bs m kv [l, q] h1 hlt
      simp [encodeValue, hm, hek, hsb]
    | [], h2 => simp at h2
    | [_], h2 => simp at h2
    | _ :: _ :: _ :: _, h2 => simp at h2
  | .ticket, bs, v, h, hlt => by
    simp only [decodeTy, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨m, kv, ns, f⟩, h1, h2⟩ := h
    match ns, h2 with
    | [l, q, i], h2 =>
      simp at h2
      obtain ⟨rfl, rfl⟩ := h2
      obtain ⟨mach, hm, ek, hek, hsb⟩ := step_enc p rec hrec 3 bs m kv [l, q, i] h1 hlt
      simp [encodeValue, hm, hek, hsb]
    | [], h2 => simp at h2
    | [_], h2 => simp at h2
    | [_, _], h2 => simp at h2
    | _ :: _ :: _ :: _ :: _, h2 => simp at h2
  | .option t, bs, v, h, hlt => by
    match bs, h, hlt with
    | tg :: rest, h, hlt =>
      simp only [decodeTy] at h
      split at h
      · rename_i h0
        simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
        obtain ⟨ss, hss, h2⟩ := h
        split at h2
        · rename_i hemp
          cases h2
          simp at hemp
          subst hemp
          simp at h0
          subst h0
          obtain ⟨ht, _⟩ := variant_enc p _ [] _ [] 0 rest rfl hss hlt
          simpa [encodeValue] using ht
        · cases h2
      · split at h
        · rename_i _ h1
          simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
          obtain ⟨ss, hss, h2⟩ := h
          match ss, hss, h2 with
          | [s], hss, h2 =>
            simp only [Option.map_eq_some_iff] at h2
            obtain ⟨⟨w, f⟩, hw, hv⟩ := h2
            simp at hv
            obtain ⟨rfl, rfl⟩ := hv
            simp at h1
            subst h1
            obtain ⟨ht, hsub⟩ := variant_enc p _ [t] _ [s] 1 rest rfl hss hlt
            have ih := enc_dec_ty p rec hrec t s w hw (by have := hsub s (by simp); omega)
            simp [encodeValue, ih]
            simpa using ht
          | [], _, h2 => simp at h2
          | _ :: _ :: _, _, h2 => simp at h2
        · cases h
    | [], h, _ => simp [decodeTy] at h
  | .result a b, bs, v, h, hlt => by
    match bs, h, hlt with
    | tg :: rest, h, hlt =>
      simp only [decodeTy] at h
      split at h
      · rename_i h0
        simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
        obtain ⟨ss, hss, h2⟩ := h
        match ss, hss, h2 with
        | [s], hss, h2 =>
          simp only [Option.map_eq_some_iff] at h2
          obtain ⟨⟨w, f⟩, hw, hv⟩ := h2
          simp at hv
          obtain ⟨rfl, rfl⟩ := hv
          simp at h0
          subst h0
          obtain ⟨ht, hsub⟩ := variant_enc p _ [a] _ [s] 0 rest rfl hss hlt
          have ih := enc_dec_ty p rec hrec a s w hw (by have := hsub s (by simp); omega)
          simp [encodeValue, ih]
          simpa using ht
        | [], _, h2 => simp at h2
        | _ :: _ :: _, _, h2 => simp at h2
      · split at h
        · rename_i _ h1
          simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
          obtain ⟨ss, hss, h2⟩ := h
          match ss, hss, h2 with
          | [s], hss, h2 =>
            simp only [Option.map_eq_some_iff] at h2
            obtain ⟨⟨w, f⟩, hw, hv⟩ := h2
            simp at hv
            obtain ⟨rfl, rfl⟩ := hv
            simp at h1
            subst h1
            obtain ⟨ht, hsub⟩ := variant_enc p _ [b] _ [s] 1 rest rfl hss hlt
            have ih := enc_dec_ty p rec hrec b s w hw (by have := hsub s (by simp); omega)
            simp [encodeValue, ih]
            simpa using ht
          | [], _, h2 => simp at h2
          | _ :: _ :: _, _, h2 => simp at h2
        · cases h
    | [], h, _ => simp [decodeTy] at h
  | .named n, bs, v, h, hlt => by
    simp only [decodeTy] at h
    cases hr : findRecord p n with
    | some fs =>
      simp only [hr, decodeRecord] at h
      cases h1 : takeBytes 2 bs with
      | none => simp [h1] at h
      | some r1 =>
        obtain ⟨count, rest⟩ := r1
        simp only [h1, Option.bind_eq_bind, Option.bind_some] at h
        split at h
        · rename_i hk
          simp only [List.map_take] at h
          cases h2 : segments p 2 ((fs.map (·.ty)).take (leValue count)) bs with
          | none => simp [h2] at h
          | some ss =>
            cases h3 : decodeFields rec ((fs.map (·.ty)).take (leValue count)) ss with
            | none => simp [h2, h3] at h
            | some r3 =>
              obtain ⟨vs, f⟩ := r3
              cases h4 : initValues p n (fs.length - leValue count) with
              | none => simp [h2, h4] at h
              | some rs =>
                simp only [h2, h3, h4, Option.bind_some, Option.some.injEq, Prod.mk.injEq,
                  Bool.and_eq_true, beq_iff_eq] at h
                obtain ⟨rfl, rfl, hfull⟩ := h
                have hkn : leValue count = fs.length := hfull
                rw [hkn, Nat.sub_self] at h4
                have hrs := initValues_zero' p n rs h4
                subst hrs
                have htk : (fs.map (·.ty)).take fs.length = fs.map (·.ty) :=
                  List.take_of_length_le (by simp)
                rw [hkn, htk] at h2 h3
                obtain ⟨hcl, hbs⟩ := takeBytes_inv 2 bs count rest h1
                obtain ⟨ks, hks, hfit, hle, hcomp⟩ := segments_inv p 2 _ bs ss h2
                have henc := enc_dec_fields p rec hrec _ ss vs h3 (fun s hs => by
                  have := le_compose' (bs.take 2) ks ss s hfit hs
                  rw [hcomp] at this
                  omega)
                have hcount : fs.length < 2 ^ 16 := by
                  have := leValue_lt count
                  rw [hcl] at this
                  simp at this
                  omega
                have htake : bs.take 2 = count := by
                  rw [hbs, ← hcl]
                  simp
                rw [htake] at hcomp
                simp only [encodeValue, hr, beq_self_eq_true, ite_true, henc, Option.bind_eq_bind,
                  Option.bind_some, List.append_nil, recordBytes, List.length_map, hcount, hks]
                rw [← hkn, leBytes_eq count 2 hcl, hcomp]
        · simp at h
    | none =>
      cases hen : findEnum p n with
      | some vs =>
        simp only [hr, hen] at h
        match bs, h, hlt with
        | tg :: rest, h, hlt =>
          simp only at h
          cases hget : vs[tg.toNat]? with
          | none => simp [hget] at h
          | some v' =>
            simp only [hget] at h
            split at h
            · rename_i hidx
              simp only [beq_iff_eq] at hidx
              simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
              obtain ⟨ss, hss, h2⟩ := h
              obtain ⟨⟨vals, f⟩, h3, h4⟩ := h2
              simp at h4
              obtain ⟨rfl, rfl⟩ := h4
              have hfv := findVariant_of_index vs _ v' hget hidx
              obtain ⟨ht, hsub⟩ := variant_enc p _ v'.fields _ ss tg rest rfl hss hlt
              have henc := enc_dec_fields p rec hrec _ ss vals h3 (fun s hs => by
                have := hsub s hs
                omega)
              simp only [encodeValue, hr, hen, hfv, henc, Option.bind_eq_bind, Option.bind_some]
              exact ht
            · cases h
        | [], h, _ => simp at h
      | none =>
        cases hnt : findNewtype p n with
        | some inner =>
          simp only [hr, hen, hnt, Option.map_eq_some_iff] at h
          obtain ⟨⟨w, f⟩, hw, hv⟩ := h
          simp at hv
          obtain ⟨rfl, rfl⟩ := hv
          have ih := hrec inner bs w hw hlt
          simp [encodeValue, hr, hen, hnt, encodeList, ih]
        | none => simp [hr, hen, hnt] at h

theorem enc_dec_at (p : Program) : ∀ (k : Nat) (t : Ty) (bs : List UInt8) (v : Value),
    decodeAt p k t bs = some (v, true) → bs.length < 2 ^ 32 → encodeValue p t v = some bs
  | 0, _, _, _, h, _ => by simp [decodeAt] at h
  | k + 1, t, bs, v, h, hl => enc_dec_ty p (decodeAt p k) (enc_dec_at p k) t bs v h hl


theorem taggedSize_fixed (p : Program) (hc : check p = .ok ()) (T : Ty) (k n x : Nat)
    (hf : isFixed p k T = some true) (hs : tySize p k T = some n) : taggedSize p T x = n := by
  obtain ⟨b, hb⟩ := fixed_all p hc T
  have hbt := isFixed_det p _ _ T b true hb hf
  subst hbt
  obtain ⟨n', hn'⟩ := fixed_size p _ T hb
  have hnn := tySize_det p _ _ T n' n hn' hs
  subst hnn
  simp [taggedSize, hb, hn']

theorem size_fixed (p : Program) (hc : check p = .ok ()) (k : Nat) :
    ∀ (t : Ty) (v : Value) (n : Nat), isFixed p k t = some true → tySize p k t = some n →
      Typed p t v → valueSize p t v = n := by
  induction k with
  | zero =>
    intro t v n hf
    simp [isFixed] at hf
  | succ j ih =>
    intro t v n hf hs hty
    cases v <;> cases t
    all_goals first | exact False.elim hty | skip
    case unit.unit =>
      simp [tySize, sizeTy] at hs
      simp [valueSize, hs]
    case bool.bool =>
      simp [tySize, sizeTy] at hs
      simp [valueSize, hs]
    case int.int =>
      simp [tySize, sizeTy] at hs
      simp [valueSize, hs]
    case time.time =>
      simp [tySize, sizeTy] at hs
      simp [valueSize, hs]
    case dur.duration =>
      simp [tySize, sizeTy] at hs
      simp [valueSize, hs]
    case f64.f64 =>
      simp [tySize, sizeTy] at hs
      simp [valueSize, hs]
    case f32.f32 =>
      simp [tySize, sizeTy] at hs
      simp [valueSize, hs]
    case dec.decimal =>
      simp [tySize, sizeTy] at hs
      simp [valueSize, hs]
    case text.text => exact absurd hf (isFixed_text p _ _ (Or.inl rfl))
    case principal.principal => exact absurd hf (isFixed_text p _ _ (Or.inr (Or.inl rfl)))
    case stepId.stepId => exact absurd hf (isFixed_text p _ _ (Or.inr (Or.inr (Or.inl rfl))))
    case ticket.ticket => exact absurd hf (isFixed_text p _ _ (Or.inr (Or.inr (Or.inr rfl))))
    case none.option t =>
      simp only [valueSize]
      exact taggedSize_fixed p hc _ _ _ _ hf hs
    case some.option w t =>
      simp only [valueSize]
      exact taggedSize_fixed p hc _ _ _ _ hf hs
    case ok.result w a b =>
      simp only [valueSize]
      exact taggedSize_fixed p hc _ _ _ _ hf hs
    case err.result w a b =>
      simp only [valueSize]
      exact taggedSize_fixed p hc _ _ _ _ hf hs
    case con.named c args nm =>
      cases hr : findRecord p nm with
      | some fs => exact absurd hf (isFixed_record p _ nm fs hr)
      | none =>
        cases hen : findEnum p nm with
        | some vs =>
          cases hv : findVariant c vs with
          | none => simp [Typed, hr, hen, hv] at hty
          | some iv =>
            obtain ⟨i, v⟩ := iv
            simp only [valueSize, hr, hen, hv]
            exact taggedSize_fixed p hc _ _ _ _ hf hs
        | none =>
          cases hnt : findNewtype p nm with
          | some inner =>
            simp only [Typed, hr, hen, hnt] at hty
            obtain ⟨_, hl⟩ := hty
            match args, hl with
            | [w], hl =>
              simp only [TypedList] at hl
              obtain ⟨j', hj', hfi⟩ := isFixed_newtype p _ nm inner hr hen hnt hf
              have hjj : j' = j := by omega
              subst hjj
              rw [tySize_newtype p j' nm inner hr hen hnt] at hs
              simp only [valueSize, hr, hen, hnt]
              exact ih inner w n hfi hs hl.1
            | [], hl => simp [TypedList] at hl
            | _ :: _ :: _, hl => simp [TypedList] at hl
          | none => simp [Typed, hr, hen, hnt] at hty

theorem fieldSize_ge (p : Program) (hc : check p = .ok ()) (t : Ty) (w : Value) (hty : Typed p t w) :
    valueSize p t w ≤ fieldSize p t (valueSize p t w) := by
  rcases slot_cases p hc t with ⟨_, hsl⟩ | ⟨n, hf, hs, hsl⟩
  · simp [fieldSize, hsl]
  · simp [fieldSize, hsl, size_fixed p hc _ t w n hf hs hty]

theorem field_fact (p : Program) (hc : check p = .ok ()) (t : Ty) (w : Value) (e : List UInt8)
    (hty : Typed p t w) (he : e.length = valueSize p t w) :
    ∃ k, slotOf p t = some k ∧ Fits [k] [e] ∧
      fieldSize p t (valueSize p t w) = slotWidth k + (partBytes [(k, e)]).length := by
  rcases slot_cases p hc t with ⟨_, hsl⟩ | ⟨n, hf, hs, hsl⟩
  · refine ⟨none, hsl, trivial, ?_⟩
    simp [fieldSize, hsl, slotWidth, partBytes, he]
  · have hv := size_fixed p hc _ t w n hf hs hty
    refine ⟨some n, hsl, ⟨by omega, trivial⟩, ?_⟩
    simp [fieldSize, hsl, slotWidth, partBytes]

theorem tagged_some (p : Program) (hc : check p = .ok ()) (T : Ty) (tag : Nat) (ts : List Ty)
    (es : List (List UInt8)) (ks : List (Option Nat)) (htag : tag < 256) (hn : typeNamed p T = true)
    (hks : slotsOf p ts = some ks)
    (hlt : ∀ n, isFixed p (startFuel p) T = some true → tySize p (startFuel p) T = some n →
      n < 2 ^ 32) :
    ∃ e, tagged p T tag ts es = some e := by
  obtain ⟨b, hb⟩ := fixed_all p hc T
  have hg : (decide (tag < 2 ^ 8) && typeNamed p T) = true := by simp [hn]; omega
  cases b with
  | true =>
    obtain ⟨n, hsz⟩ := fixed_size p _ T hb
    have hn' : n < frameLimit := by have := hlt n hb hsz; simp [frameLimit]; omega
    refine ⟨UInt8.ofNat tag :: es.flatten ++
      List.replicate (n - (UInt8.ofNat tag :: es.flatten).length) 0, ?_⟩
    simp only [tagged, hg, ite_true, hb, hsz, Option.bind_eq_bind, Option.bind_some, padTo, ite_yes hn']
  | false =>
    refine ⟨compose [UInt8.ofNat tag] (ks.zip es), ?_⟩
    simp only [tagged, hg, ite_true, hb, hks, Option.bind_eq_bind, Option.bind_some]

theorem tagged_len (p : Program) (hc : check p = .ok ()) (T : Ty) (v : Value) (tag : Nat)
    (ts : List Ty) (es : List (List UInt8)) (ks : List (Option Nat)) (e : List UInt8) (x : Nat)
    (he : encodeValue p T v = some e) (ht : tagged p T tag ts es = some e)
    (hks : slotsOf p ts = some ks) (hfit : Fits ks es)
    (hx : x = slotsWidth ks + (partBytes (ks.zip es)).length) : e.length = taggedSize p T x := by
  obtain ⟨b, hb⟩ := fixed_all p hc T
  cases b with
  | true =>
    obtain ⟨n, hsz⟩ := fixed_size p _ T hb
    rw [taggedSize_fixed p hc T _ n x hb hsz]
    exact enc_fixed p T v e _ n hb hsz he
  | false =>
    simp only [tagged] at ht
    split at ht
    · simp only [hb, hks, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at ht
      subst ht
      rw [compose_length _ ks es hfit]
      simp [taggedSize, hb, hx]
      omega
    · cases ht

theorem fieldsSize_fixed (p : Program) (hc : check p = .ok ()) (j : Nat) :
    ∀ (ts : List Ty) (vs : List Value) (s : Nat), TypedList p ts vs →
      (∀ t ∈ ts, isFixed p j t = some true) → sumSizes (tySize p j) ts = some s →
        fieldsSize p ts vs = s
  | [], [], s, _, _, h => by
    simp [sumSizes] at h
    simp [fieldsSize, h]
  | t :: ts, v :: vs, s, hty, hall, h => by
    cases h1 : tySize p j t with
    | none => simp [sumSizes, h1] at h
    | some x =>
      cases h2 : sumSizes (tySize p j) ts with
      | none => simp [sumSizes, h1, h2] at h
      | some y =>
        simp [sumSizes, h1, h2] at h
        have ih := fieldsSize_fixed p hc j ts vs y hty.2 (fun u hu => hall u (by simp [hu])) h2
        have hf := hall t (by simp)
        rcases slot_cases p hc t with ⟨hb, _⟩ | ⟨n, hb, hs, hsl⟩
        · have := isFixed_det p _ _ t false true hb hf
          cases this
        · have hnx := tySize_det p _ _ t n x hs h1
          simp [fieldsSize, fieldSize, hsl, ih]
          omega
  | [], _ :: _, _, hty, _, _ => hty.elim
  | _ :: _, [], _, hty, _, _ => hty.elim

theorem slotOf_int (p : Program) : slotOf p .int = some (some 8) := by
  rw [slotOf, startFuel_eq]
  simp [isFixed, fixedTy, tySize, sizeTy]


theorem typed_named (p : Program) : ∀ (t : Ty) (w : Value), Typed p t w → typeNamed p t = true
  | .option t, .none, h => h
  | .option t, .some w, h => typed_named p t w h
  | .result a b, .ok w, h => by
    simp only [typeNamed, Bool.and_eq_true]
    exact ⟨typed_named p a w h.1, h.2⟩
  | .result a b, .err w, h => by
    simp only [typeNamed, Bool.and_eq_true]
    exact ⟨h.1, typed_named p b w h.2⟩
  | .named n, .con c args, h => by
    simp only [Typed] at h
    cases hr : findRecord p n with
    | some fs => exact record_typeName p n fs hr
    | none =>
      cases hen : findEnum p n with
      | some vs => exact enum_typeName p n vs hen
      | none =>
        cases hnt : findNewtype p n with
        | some t => exact newtype_typeName p n t hnt
        | none => simp [hr, hen, hnt] at h
  | .unit, _, _ | .bool, _, _ | .int, _, _ | .text, _, _ | .time, _, _ | .duration, _, _
  | .principal, _, _ | .stepId, _, _ | .ticket, _, _ | .f64, _, _ | .f32, _, _
  | .decimal _, _, _ => rfl
  | .option _, .int _, h | .option _, .bool _, h | .option _, .unit, h | .option _, .text _, h
  | .option _, .dur _, h | .option _, .time _, h | .option _, .principal _, h
  | .option _, .stepId .., h | .option _, .ticket .., h | .option _, .con .., h
  | .option _, .ok _, h | .option _, .err _, h | .option _, .f64 _, h | .option _, .f32 _, h
  | .option _, .dec .., h => h.elim
  | .result .., .int _, h | .result .., .bool _, h | .result .., .unit, h | .result .., .text _, h
  | .result .., .dur _, h | .result .., .time _, h | .result .., .principal _, h
  | .result .., .stepId .., h | .result .., .ticket .., h | .result .., .con .., h
  | .result .., .some _, h | .result .., .none, h | .result .., .f64 _, h | .result .., .f32 _, h
  | .result .., .dec .., h => h.elim
  | .named _, .int _, h | .named _, .bool _, h | .named _, .unit, h | .named _, .text _, h
  | .named _, .dur _, h | .named _, .time _, h | .named _, .principal _, h
  | .named _, .stepId .., h | .named _, .ticket .., h | .named _, .some _, h | .named _, .none, h
  | .named _, .ok _, h | .named _, .err _, h | .named _, .f64 _, h | .named _, .f32 _, h
  | .named _, .dec .., h => h.elim

theorem tagged_bound (p : Program) (hc : check p = .ok ()) (T : Ty) (x : Nat)
    (hlt : taggedSize p T x < 2 ^ 32) :
    ∀ n, isFixed p (startFuel p) T = some true → tySize p (startFuel p) T = some n → n < 2 ^ 32 :=
  fun n hf hs => by
    rw [taggedSize_fixed p hc T _ n x hf hs] at hlt
    exact hlt

mutual
theorem enc_total (p : Program) (hc : check p = .ok ()) (t : Ty) (v : Value) :
    Typed p t v → valueSize p t v < 2 ^ 32 →
      ∃ e, encodeValue p t v = some e ∧ e.length = valueSize p t v := by
  cases v <;> cases t <;> intro hty hlt
  all_goals first | exact False.elim hty | skip
  case unit.unit => exact ⟨[], rfl, rfl⟩
  case bool.bool b => exact ⟨[if b then 1 else 0], rfl, rfl⟩
  case int.int n =>
    have hr : inRange n = true := hty
    exact ⟨intBytes 8 n, by simp [encodeValue, intField, hr], by simp [valueSize, intBytes_length]⟩
  case time.time n =>
    have hr : inRange n = true := hty
    exact ⟨intBytes 8 n, by simp [encodeValue, intField, hr], by simp [valueSize, intBytes_length]⟩
  case dur.duration n =>
    have hr : inRange n = true := hty
    exact ⟨intBytes 8 n, by simp [encodeValue, intField, hr], by simp [valueSize, intBytes_length]⟩
  case f64.f64 b =>
    have hok : floatOk .b64 b.toNat = true := hty
    exact ⟨leBytes 8 b.toNat, by simp [encodeValue, hok], by simp [valueSize, leBytes_length]⟩
  case f32.f32 b =>
    have hok : floatOk .b32 b.toNat = true := hty
    exact ⟨leBytes 4 b.toNat, by simp [encodeValue, hok], by simp [valueSize, leBytes_length]⟩
  case dec.decimal s' c s =>
    have h : s' = s ∧ decIn c = true := hty
    obtain ⟨rfl, hd⟩ := h
    exact ⟨intBytes 16 c, by simp [encodeValue, hd], by simp [valueSize, intBytes_length]⟩
  case text.text s => exact ⟨utf8 s, rfl, by simp [valueSize, utf8_length]⟩
  case principal.principal s => exact ⟨utf8 s, rfl, by simp [valueSize, utf8_length]⟩
  case stepId.stepId m kv l q =>
    cases hm : findMachine p m with
    | none => simp [Typed, hm] at hty
    | some mach =>
      simp only [Typed, hm] at hty
      obtain ⟨hk, hl, hq⟩ := hty
      simp only [valueSize, hm] at hlt
      have hge := fieldSize_ge p hc mach.key kv hk
      obtain ⟨ek, h1, h2⟩ := enc_total p hc mach.key kv hk (by omega)
      obtain ⟨k0, hsl, hfit0, hfs⟩ := field_fact p hc mach.key kv ek hk h2
      have hks : slotsOf p (mach.key :: List.replicate 2 .int) = some [k0, some 8, some 8] := by
        simp [slotsOf, hsl, slotOf_int]
      have hfit : Fits [k0, some 8, some 8] [ek, intBytes 8 l, intBytes 8 q] := by
        cases k0 with
        | none => exact ⟨intBytes_length 8 l, intBytes_length 8 q, trivial⟩
        | some n => exact ⟨hfit0.1, intBytes_length 8 l, intBytes_length 8 q, trivial⟩
      refine ⟨leBytes 4 (utf8 m).length ++ (utf8 m ++
        compose [] ([k0, some 8, some 8].zip [ek, intBytes 8 l, intBytes 8 q])), ?_, ?_⟩
      · have hi : intFields [l, q] = some [intBytes 8 l, intBytes 8 q] := by
          simp [intFields, intField, hl, hq]
        simp only [encodeValue, hm, h1, Option.bind_eq_bind, Option.bind_some, stepBytes, hi]
        rw [show [l, q].length = 2 from rfl, hks]
        rfl
      · rw [List.length_append, List.length_append, compose_length [] _ _ hfit, leBytes_length,
          utf8_length]
        simp only [valueSize, hm, hfs]
        cases k0 <;> simp [slotsWidth, slotWidth, partBytes] <;> omega
  case ticket.ticket m kv l q i =>
    cases hm : findMachine p m with
    | none => simp [Typed, hm] at hty
    | some mach =>
      simp only [Typed, hm] at hty
      obtain ⟨hk, hl, hq, hi⟩ := hty
      simp only [valueSize, hm] at hlt
      have hge := fieldSize_ge p hc mach.key kv hk
      obtain ⟨ek, h1, h2⟩ := enc_total p hc mach.key kv hk (by omega)
      obtain ⟨k0, hsl, hfit0, hfs⟩ := field_fact p hc mach.key kv ek hk h2
      have hks : slotsOf p (mach.key :: List.replicate 3 .int) =
          some [k0, some 8, some 8, some 8] := by
        simp [slotsOf, hsl, slotOf_int]
      have hfit : Fits [k0, some 8, some 8, some 8]
          [ek, intBytes 8 l, intBytes 8 q, intBytes 8 i] := by
        cases k0 with
        | none => exact ⟨intBytes_length 8 l, intBytes_length 8 q, intBytes_length 8 i, trivial⟩
        | some n =>
          exact ⟨hfit0.1, intBytes_length 8 l, intBytes_length 8 q, intBytes_length 8 i, trivial⟩
      refine ⟨leBytes 4 (utf8 m).length ++ (utf8 m ++
        compose [] ([k0, some 8, some 8, some 8].zip
          [ek, intBytes 8 l, intBytes 8 q, intBytes 8 i])), ?_, ?_⟩
      · have hii : intFields [l, q, i] = some [intBytes 8 l, intBytes 8 q, intBytes 8 i] := by
          simp [intFields, intField, hl, hq, hi]
        simp only [encodeValue, hm, h1, Option.bind_eq_bind, Option.bind_some, stepBytes, hii]
        rw [show [l, q, i].length = 3 from rfl, hks]
        rfl
      · rw [List.length_append, List.length_append, compose_length [] _ _ hfit, leBytes_length,
          utf8_length]
        simp only [valueSize, hm, hfs]
        cases k0 <;> simp [slotsWidth, slotWidth, partBytes] <;> omega
  case none.option t =>
    have htn : typeNamed p t = true := hty
    simp only [valueSize] at hlt ⊢
    obtain ⟨e, he⟩ := tagged_some p hc (.option t) 0 [] [] [] (by omega) htn rfl
      (tagged_bound p hc _ _ hlt)
    have he' : encodeValue p (.option t) .none = some e := by
      simp only [encodeValue]
      exact he
    exact ⟨e, he', tagged_len p hc _ _ 0 [] [] [] e 0 he' he rfl trivial
      (by simp [slotsWidth, partBytes])⟩
  case some.option w t =>
    have hw : Typed p t w := hty
    simp only [valueSize] at hlt ⊢
    have hb : valueSize p t w < 2 ^ 32 := by
      obtain ⟨b, hb⟩ := fixed_all p hc (.option t)
      cases b with
      | true =>
        obtain ⟨n, hn⟩ := fixed_size p _ _ hb
        rw [taggedSize_fixed p hc _ _ n _ hb hn] at hlt
        obtain ⟨m, hm, rfl⟩ := tySize_option p _ t n hn
        rw [isFixed_option] at hb
        have := size_fixed p hc _ t w m hb hm hw
        omega
      | false =>
        simp [taggedSize, hb] at hlt
        have := fieldSize_ge p hc t w hw
        omega
    obtain ⟨e', h1, h2⟩ := enc_total p hc t w hw hb
    obtain ⟨k0, hsl, hfit, hfs⟩ := field_fact p hc t w e' hw h2
    have hks : slotsOf p [t] = some [k0] := by simp [slotsOf, hsl]
    obtain ⟨e, he⟩ := tagged_some p hc (.option t) 1 [t] [e'] [k0] (by omega)
      (typed_named p (.option t) (.some w) hty) hks (tagged_bound p hc _ _ hlt)
    have he' : encodeValue p (.option t) (.some w) = some e := by
      simp only [encodeValue, h1, Option.bind_eq_bind, Option.bind_some]
      exact he
    exact ⟨e, he', tagged_len p hc _ _ 1 [t] [e'] [k0] e _ he' he hks hfit
      (by rw [hfs]; simp [slotsWidth])⟩
  case ok.result w a b =>
    have hw : Typed p a w := hty.1
    simp only [valueSize] at hlt ⊢
    have hb : valueSize p a w < 2 ^ 32 := by
      obtain ⟨bb, hbb⟩ := fixed_all p hc (.result a b)
      cases bb with
      | true =>
        obtain ⟨n, hn⟩ := fixed_size p _ _ hbb
        rw [taggedSize_fixed p hc _ _ n _ hbb hn] at hlt
        obtain ⟨x, y, hx, hy, rfl⟩ := tySize_result p _ a b n hn
        have := size_fixed p hc _ a w x (isFixed_result p _ a b hbb).1 hx hw
        omega
      | false =>
        simp [taggedSize, hbb] at hlt
        have := fieldSize_ge p hc a w hw
        omega
    obtain ⟨e', h1, h2⟩ := enc_total p hc a w hw hb
    obtain ⟨k0, hsl, hfit, hfs⟩ := field_fact p hc a w e' hw h2
    have hks : slotsOf p [a] = some [k0] := by simp [slotsOf, hsl]
    obtain ⟨e, he⟩ := tagged_some p hc (.result a b) 0 [a] [e'] [k0] (by omega)
      (typed_named p (.result a b) (.ok w) hty) hks (tagged_bound p hc _ _ hlt)
    have he' : encodeValue p (.result a b) (.ok w) = some e := by
      simp only [encodeValue, h1, Option.bind_eq_bind, Option.bind_some]
      exact he
    exact ⟨e, he', tagged_len p hc _ _ 0 [a] [e'] [k0] e _ he' he hks hfit
      (by rw [hfs]; simp [slotsWidth])⟩
  case err.result w a b =>
    have hw : Typed p b w := hty.2
    simp only [valueSize] at hlt ⊢
    have hb : valueSize p b w < 2 ^ 32 := by
      obtain ⟨bb, hbb⟩ := fixed_all p hc (.result a b)
      cases bb with
      | true =>
        obtain ⟨n, hn⟩ := fixed_size p _ _ hbb
        rw [taggedSize_fixed p hc _ _ n _ hbb hn] at hlt
        obtain ⟨x, y, hx, hy, rfl⟩ := tySize_result p _ a b n hn
        have := size_fixed p hc _ b w y (isFixed_result p _ a b hbb).2 hy hw
        omega
      | false =>
        simp [taggedSize, hbb] at hlt
        have := fieldSize_ge p hc b w hw
        omega
    obtain ⟨e', h1, h2⟩ := enc_total p hc b w hw hb
    obtain ⟨k0, hsl, hfit, hfs⟩ := field_fact p hc b w e' hw h2
    have hks : slotsOf p [b] = some [k0] := by simp [slotsOf, hsl]
    obtain ⟨e, he⟩ := tagged_some p hc (.result a b) 1 [b] [e'] [k0] (by omega)
      (typed_named p (.result a b) (.err w) hty) hks (tagged_bound p hc _ _ hlt)
    have he' : encodeValue p (.result a b) (.err w) = some e := by
      simp only [encodeValue, h1, Option.bind_eq_bind, Option.bind_some]
      exact he
    exact ⟨e, he', tagged_len p hc _ _ 1 [b] [e'] [k0] e _ he' he hks hfit
      (by rw [hfs]; simp [slotsWidth])⟩
  case con.named c args nm =>
    cases hr : findRecord p nm with
    | some fs =>
      simp only [Typed, hr] at hty
      obtain ⟨rfl, hl⟩ := hty
      simp only [valueSize, hr] at hlt ⊢
      obtain ⟨es, ks, h1, hks, hfit, hfs⟩ := enc_totalList p hc _ args hl (by omega)
      have hlen := record_len p hc c fs hr
      refine ⟨compose (leBytes 2 (fs.map (·.ty)).length) (ks.zip es), ?_, ?_⟩
      · simp only [encodeValue, hr, beq_self_eq_true, ite_true, h1, Option.bind_eq_bind,
          Option.bind_some, recordBytes, List.length_map]
        rw [ite_yes hlen]
        simp [hks]
      · rw [compose_length _ ks es hfit, leBytes_length, hfs]
        omega
    | none =>
      cases hen : findEnum p nm with
      | some vs =>
        cases hv : findVariant c vs with
        | none => simp [Typed, hr, hen, hv] at hty
        | some iv =>
          obtain ⟨i, v⟩ := iv
          simp only [Typed, hr, hen, hv] at hty
          simp only [valueSize, hr, hen, hv] at hlt ⊢
          obtain ⟨hget, _⟩ := findVariant_get c vs i v hv
          have hvm : v ∈ vs := List.mem_of_getElem? hget
          have hi : i < vs.length := by
            obtain ⟨hlt', _⟩ := List.getElem?_eq_some_iff.mp hget
            exact hlt'
          have hvl := enum_len p hc nm vs hen
          have hbnd : fieldsSize p v.fields args < 2 ^ 32 := by
            obtain ⟨b, hb⟩ := fixed_all p hc (.named nm)
            cases b with
            | true =>
              obtain ⟨n, hn⟩ := fixed_size p _ _ hb
              rw [taggedSize_fixed p hc _ _ n _ hb hn] at hlt
              obtain ⟨j, hj, hall⟩ := isFixed_enum p _ nm vs hr hen hb
              rw [hj] at hn
              obtain ⟨x, hx, rfl⟩ := tySize_enum p j nm vs hr hen n hn
              obtain ⟨s, hsum, hle⟩ := maxSizes_ge vs x hx v hvm
              have := fieldsSize_fixed p hc j v.fields args s hty (hall v hvm) hsum
              omega
            | false =>
              simp [taggedSize, hb] at hlt
              omega
          obtain ⟨es, ks, h1, hks, hfit, hfs⟩ := enc_totalList p hc _ args hty hbnd
          obtain ⟨e, he⟩ := tagged_some p hc (.named nm) i v.fields es ks (by omega)
            (enum_typeName p nm vs hen) hks (tagged_bound p hc _ _ hlt)
          have he' : encodeValue p (.named nm) (.con c args) = some e := by
            simp only [encodeValue, hr, hen, hv, h1, Option.bind_eq_bind, Option.bind_some]
            exact he
          exact ⟨e, he', tagged_len p hc _ _ i v.fields es ks e _ he' he hks hfit hfs⟩
      | none =>
        cases hnt : findNewtype p nm with
        | some inner =>
          simp only [Typed, hr, hen, hnt] at hty
          obtain ⟨rfl, hl⟩ := hty
          match args, hl with
          | [w], hl =>
            simp only [TypedList] at hl
            simp only [valueSize, hr, hen, hnt] at hlt ⊢
            obtain ⟨e, h1, h2⟩ := enc_total p hc inner w hl.1 hlt
            refine ⟨e, ?_, h2⟩
            simp [encodeValue, hr, hen, hnt, encodeList, h1]
          | [], hl => simp [TypedList] at hl
          | _ :: _ :: _, hl => simp [TypedList] at hl
        | none => simp [Typed, hr, hen, hnt] at hty
termination_by structural v

theorem enc_totalList (p : Program) (hc : check p = .ok ()) (ts : List Ty) (vs : List Value) :
    TypedList p ts vs → fieldsSize p ts vs < 2 ^ 32 →
      ∃ es ks, encodeList p ts vs = some es ∧ slotsOf p ts = some ks ∧ Fits ks es ∧
        fieldsSize p ts vs = slotsWidth ks + (partBytes (ks.zip es)).length := by
  match ts, vs with
  | [], [] =>
    intro _ _
    exact ⟨[], [], rfl, rfl, trivial, rfl⟩
  | t :: ts, v :: vs =>
    intro hty hlt
    simp only [TypedList] at hty
    simp only [fieldsSize] at hlt
    have hge := fieldSize_ge p hc t v hty.1
    obtain ⟨e, h1, h2⟩ := enc_total p hc t v hty.1 (by omega)
    obtain ⟨k0, hsl, hfit0, hfs0⟩ := field_fact p hc t v e hty.1 h2
    obtain ⟨es, ks, h3, hks, hfit, hfs⟩ := enc_totalList p hc ts vs hty.2 (by omega)
    refine ⟨e :: es, k0 :: ks, ?_, ?_, ?_, ?_⟩
    · simp [encodeList, h1, h3]
    · simp [slotsOf, hsl, hks]
    · cases k0 with
      | none => exact hfit
      | some n => exact ⟨hfit0.1, hfit⟩
    · simp only [fieldsSize, hfs0, hfs]
      cases k0 <;> simp [slotsWidth, partBytes] <;> omega
  | [], _ :: _ => intro h; exact h.elim
  | _ :: _, [] => intro h; exact h.elim
termination_by structural vs
end

theorem encode_typed (p : Program) (t : Ty) (v : Value) (b : List UInt8)
    (he : encode p t v = some b) : Typed p t v := by
  simp only [encode, Option.bind_eq_bind, Option.bind_eq_some_iff] at he
  obtain ⟨body, h1, _⟩ := he
  exact enc_typed p t v body h1

theorem decode_encode (p : Program) (t : Ty) (v : Value) (b : List UInt8) (hc : check p = .ok ())
    (_ht : Typed p t v) (he : encode p t v = some b) : decode p t b = some v := by
  simp only [encode, Option.bind_eq_bind, Option.bind_eq_some_iff] at he
  obtain ⟨body, h1, h2⟩ := he
  split at h2
  · rename_i hlen
    cases h2
    have hd := dec_enc p hc t v (nodeCount p) body (fine_all p hc t) h1
      (by simp [frameLimit] at hlen; omega)
    have hb : (leBytes 2 formatVersion ++ body).length < frameLimit := by
      simp [leBytes_length]
      omega
    simp only [decode, decodeFrame, hb, ite_true, takeBytes_append _ _ 2 (leBytes_length 2 _),
      startFuel_eq, hd]
    rfl
  · cases h2

theorem encode_decode (p : Program) (t : Ty) (v : Value) (b : List UInt8) (_hc : check p = .ok ())
    (hd : decode p t b = some v) (hf : full p t b = true) : encode p t v = some b := by
  have hframe : decodeFrame p t b = some (v, true) := by
    simp only [decode, Option.map_eq_some_iff] at hd
    obtain ⟨⟨v', f⟩, h1, h2⟩ := hd
    simp at h2
    subst h2
    simp only [full, h1] at hf
    subst hf
    exact h1
  simp only [decodeFrame] at hframe
  split at hframe
  · rename_i hlen
    cases ht : takeBytes 2 b with
    | none => simp [ht] at hframe
    | some r =>
      obtain ⟨ver, body⟩ := r
      simp only [ht] at hframe
      split at hframe
      · rename_i hver
        obtain ⟨hvl, rfl⟩ := takeBytes_inv 2 b ver body ht
        have hbl : body.length < 2 ^ 32 := by
          simp [frameLimit] at hlen
          omega
        have henc := enc_dec_at p _ t body v hframe hbl
        simp only [beq_iff_eq] at hver
        simp only [encode, henc, Option.bind_eq_bind, Option.bind_some]
        have hl2 : 2 + body.length < frameLimit := by
          simp at hlen
          omega
        rw [ite_yes hl2, ← hver, leBytes_eq ver 2 hvl]
      · cases hframe
  · cases hframe

theorem encode_total (p : Program) (t : Ty) (v : Value) (hc : check p = .ok ()) (ht : Typed p t v)
    (hs : size p t v < 2 ^ 32) : ∃ b, encode p t v = some b ∧ b.length = size p t v := by
  simp only [size] at hs ⊢
  obtain ⟨e, h1, h2⟩ := enc_total p hc t v ht (by omega)
  refine ⟨leBytes 2 formatVersion ++ e, ?_, ?_⟩
  · simp only [encode, h1, Option.bind_eq_bind, Option.bind_some]
    rw [ite_yes (by simp [frameLimit]; omega)]
  · simp [leBytes_length, h2]

end Borsuk
