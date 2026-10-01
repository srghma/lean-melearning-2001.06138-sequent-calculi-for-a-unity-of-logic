module

public import RequestProject.Logics.Translations

/-!
# Small tactics for manipulating multiset contexts
-/

public section

/-- `msimpa [lemmas] using e`: `simpa` normalising only `Multiset.map` over constructors
(plus the given lemmas, typically the equations of a translation). -/
syntax "msimpa" (" [" Lean.Parser.Tactic.simpLemma,* "]")? " using " term : tactic

macro_rules
  | `(tactic| msimpa using $e) =>
    `(tactic| simpa only [Multiset.map_cons, Multiset.map_add, Multiset.map_zero,
      Multiset.map_singleton, add_zero, zero_add] using $e)
  | `(tactic| msimpa [$ls,*] using $e) =>
    `(tactic| simpa only [Multiset.map_cons, Multiset.map_add, Multiset.map_zero,
      Multiset.map_singleton, add_zero, zero_add, $ls,*] using $e)

/-- Close an equality of multisets by normalising `::ₘ` to `+` and using commutativity. -/
macro "ms_eq" : tactic =>
  `(tactic| first
    | rfl
    | (simp only [← Multiset.singleton_add, Multiset.map_add, Multiset.map_zero,
        Multiset.map_singleton, add_zero, zero_add] <;> abel)
    | simp [add_comm, add_left_comm, Multiset.cons_swap])

end
