
import Star.SplitJoin.star

structure token (α : Type) where
  fst : α
  snd : α
  trd : α

def List.dequeue {α : Unit} (l: List α) : Option (List α × α) :=
  match l with
  | x :: xs => some (xs, x)
  | [] => none

inductive Event where
| input
| output
| null
deriving Inhabited

--specification module

structure split_join_spec (α : Type) where
  in_out : List (α × α × α)

inductive split_step_external_spec {α} : split_join_spec α → Event → split_join_spec α -> Prop where
| input : ∀ i a b c,
  split_step_external_spec i Event.input
    { i with
        in_out := i.in_out ++ [(a, b, c)]
    }
| output : ∀ i a b c l,
  List.dequeue i.in_out = some (l, (a, b, c)) →
  split_step_external_spec i Event.output
    { i with
        in_out := l
    }

inductive split_step_internal_spec {α} : split_join_spec α → Event → split_join_spec α -> Prop where
| in_spec : ∀ s,
  split_step_internal_spec s Event.null s

-- inductive split_step_internal_spec {α} : split_join_spec α → Event → split_join_spec α -> Prop where
-- | in_spec : ∀ i a b c l,
--   List.dequeue i.input = some (l, (a, b, c)) →
--   split_step_internal_spec i Event.enqueue
--     { i with
--         input := l,
--         state := i.state ++ [(a, b, c)]
--     }
-- | out_spec : ∀ i a b c l,
--   List.dequeue i.state = some (l, (a, b, c)) →
--   split_step_internal_spec i Event.dequeue
--     { i with
--         state := l,
--         output := i.output ++ [(a, b, c)]
--     }

inductive split_step_spec {α} : split_join_spec α → Event → split_join_spec α -> Prop where
| external_step : ∀ i e i' ,
    split_step_external_spec i e i' →
    split_step_spec i e i'
| internal_step : ∀ i e i' ,
    split_step_internal_spec i e i' →
    split_step_spec i e i'


--implementation module

structure split_join (α : Type) where
  ext_input : List (α × α × α)
  split_1_left : List (α × α)
  split_1_right : List α
  split_2_left : List α
  split_2_right : List α
  join_1 :  List (α × α)
  join_2 : List (α × α × α)
  ext_output : List (α × α × α)


inductive split_step_external {α} : split_join α → Event → split_join α -> Prop where
| input : ∀ i a b c,
  split_step_external i Event.input
    { i with
        ext_input := i.ext_input ++ [(a, b, c)]
    }
| output : ∀ i a b c l,
  List.dequeue i.ext_output = some (l, (a, b, c)) →
  split_step_external i Event.output
    { i with
        ext_output := l
    }


inductive split_step_internal {α} : split_join α → Event → split_join α -> Prop where
| split_1 : ∀ i a b c l,
  List.dequeue i.ext_input = some (l, (a, b, c)) →
  split_step_internal i Event.null
    { i with
        ext_input := l,
        split_1_left := i.split_1_left ++ [(a, b)],
        split_1_right := i.split_1_right ++ [c]
    }
| split_2 : ∀ i a b l,
  List.dequeue i.split_1_left = some (l, (a, b)) →
  split_step_internal i Event.null
    { i with
        split_1_left := l,
        split_2_left := i.split_2_left ++ [a],
        split_2_right := i.split_2_right ++ [b]
    }
| join_1 : ∀ i b c l l',
  List.dequeue i.split_1_right = some (l, c) →
  List.dequeue i.split_2_right = some (l', b) →
  split_step_internal i Event.null
    { i with
        split_1_right := l,
        split_2_right := l',
        join_1 := i.join_1 ++ [(b, c)]
    }
| join_2 : ∀ i a b c l l',
  List.dequeue i.join_1 = some (l, (b, c)) →
  List.dequeue i.split_2_left = some (l', a) →
  split_step_internal i Event.null
    { i with
        join_1 := l,
        split_2_left := l',
        join_2 := i.join_2 ++ [(a, b, c)]
    }
| join_2_out : ∀ i a b c l,
  List.dequeue i.join_2 = some (l, (a, b, c)) →
  split_step_internal i Event.null
    { i with
        join_2 := l
        ext_output := i.ext_output ++ [(a, b, c)]
    }

inductive split_step {α} : split_join α → Event → split_join α -> Prop where
| external_step : ∀ i e i' ,
    split_step_external i e i' →
    split_step i e i'
| internal_step : ∀ i e i' ,
    split_step_internal i e i' →
    split_step i e i'


/-!
# Proof of correctness between implementation and specification
-/

inductive φ {α} : split_join Unit → split_join_spec Unit → Prop where
| base : ∀ i s,
    i.split_1_left = [] →
    i.split_1_right = [] →
    i.split_2_left = [] →
    i.split_2_right = [] →
    i.join_1 = [] →
    i.join_2 = [] →
    i.ext_output ++ i.ext_input = s.in_out →
    φ i s
| step_input : ∀ i s i' s',
    ( ∀ a b c, φ (i' a b c) (s' a b c) →
    (∀ a b c, split_step_external i (Event.input a b c) (i' a b c)) →
    (split_step_external_spec s Event.input s') →
    φ i s
| step_output : ∀ i s i' s' ,
    φ i' s' →
    split_step_external i Event.output i' →
    split_step_external_spec s Event.output s' →
    φ i s
| step_null : ∀ i s s' i',
    φ i' s' →
    split_step_internal i Event.null i' →
    split_step_internal_spec s Event.null s'  →
    φ i s

@[simp]
theorem dequeue_head : ∀ {α} {l l' l'': List α} {a x : α},
    List.dequeue (a :: l) = some (l'', x) -> List.dequeue (a :: l ++ l') = some (l'' ++ l', x)  := by
    intro α l l' l'' a x h
    unfold List.dequeue at *
    simp
    simp at h
    assumption

@[simp]
theorem dequeue_conct : ∀ {α} {l l' l'' : List α} {x : α},
    List.dequeue l = some (l'', x) -> List.dequeue (l ++ l') = some (l'' ++ l', x)  := by
    intro α l l' l'' x h
    induction l
    . unfold List.dequeue at *
      simp_all only [List.reverse_nil, reduceCtorEq]
    . rename_i a l ih
      apply dequeue_head
      assumption


theorem dequeue_add : ∀ {α} {l l': List (α × α × α)} {a b c a' b' c' : α},
    List.dequeue (l ++ [(a, b, c)]) = some (l', (a', b', c')) -> l = l'  := by admit

theorem dequeue_add1 : ∀ {α} {l l': List (α × α × α)} {a' b' c' : α},
    List.dequeue (l) = some (l', (a', b', c')) -> l = l' ++ [(a', b', c')] := by admit



def indistinguishability (α : Type) : Prop := ∀ (i i' : split_join α) e (s : split_join_spec α), split_step i e i' -> ∃ s', split_step_spec s e s'


theorem enough {α} (i : split_join α) (s : split_join_spec α) :
  φ i s -> ∀ i' (e : Event), split_step i e i' ->
    indistinguishability α ->
    ∃ s', split_step_spec s e s' ∧ φ i' s' := by
  intro hφ i2 e hstep hi
  induction hφ generalizing i2 e
  . clear i s
    rename_i i s h1 h2 h3 h4 h5 h6 h7
    cases hstep
    . rename_i hstep
      cases hstep
      . constructor
        . constructor
          . constructor; constructor <;> rename_i a b c
            . exact a
            . exact b
            . exact c
          . constructor <;> try grind
      . constructor
        . constructor
          . constructor; constructor <;> rename_i a b c _ _
            rotate_left
            . exact a
            . exact b
            . exact c
            . rename_i l _
              exact l ++ i.ext_input
            . rw[← h7]
              apply dequeue_conct
              assumption
          . constructor <;> try grind
    . rename_i hstep
      constructor
      rotate_left
      . exact s
      . cases hstep
        . constructor
          . apply split_step_spec.internal_step; constructor
          . apply φ.step_null; rotate_left
            . apply split_step_internal.split_2
              rotate_left 1
              . rename_i a b c _ _
                exact a
              . rename_i a b c _ _
                exact b
              rotate_left
              . simp_all
                unfold List.dequeue
                simp_all
                assumption
            . constructor
            . apply φ.step_null; rotate_left
              . dsimp
                apply split_step_internal.join_1
                rotate_left 2
                . rename_i a b c _ _
                  exact b
                . rename_i a b c _ _
                  exact c
                . exact []
                . exact []
                . simp_all
                  unfold List.dequeue
                  simp_all
                . simp_all
                  unfold List.dequeue
                  simp_all
              . constructor
              . dsimp
                apply φ.step_null; rotate_left
                . apply split_step_internal.join_2
                  rotate_left 2
                  . rename_i a b c _ _
                    exact a
                  . rename_i a b c _ _
                    exact b
                  . rename_i a b c _ _
                    exact c
                  . exact []
                  . exact []
                  . simp
                    unfold List.dequeue
                    simp_all
                  . simp
                    unfold List.dequeue
                    simp_all
                . constructor
                . dsimp
                  apply φ.step_null; rotate_left
                  . apply split_step_internal.join_2_out
                    rotate_left 2
                    . rename_i a b c _ _
                      exact b
                    . rename_i a b c _ _
                      exact c
                    . exact []
                    rotate_left
                    . rename_i a b c _ _
                      exact a
                    . unfold List.dequeue
                      simp_all
                  . constructor
                  . dsimp; apply φ.base <;> simp_all
                    unfold List.dequeue at *
                    grind
        . constructor
          . apply split_step_spec.internal_step; constructor
          . constructor <;> try grind
            . unfold List.dequeue at *;simp_all
            . unfold List.dequeue at *;simp_all
            . unfold List.dequeue at *;simp_all
        . constructor
          . apply split_step_spec.internal_step; constructor
          . constructor <;> try grind
            . unfold List.dequeue at *;simp_all
            . unfold List.dequeue at *;simp_all
            . unfold List.dequeue at *;simp_all
        . constructor
          . apply split_step_spec.internal_step; constructor
          . constructor <;> try grind
            . unfold List.dequeue at *;simp_all
            . unfold List.dequeue at *;simp_all
            . unfold List.dequeue at *;simp_all
        . constructor
          . apply split_step_spec.internal_step; constructor
          . constructor <;> try grind
            . unfold List.dequeue at *;simp_all
            . unfold List.dequeue at *;simp_all
  . clear i s
    rename_i i1 s1 i3 s3 h1 h2 h3 h4
    unfold indistinguishability at *
    specialize hi _ _  _ s1 hstep
    cases hi
    rename_i s2 h
    constructor; rotate_left; exact s2
    constructor
    . assumption
    . cases hstep <;> rename_i hstep
      . cases hstep
        . cases h2
          specialize h4 _ Event.input
            (by apply split_step.external_step; apply split_step_external.input
                . rename_i a b c
                  exact a
                . rename_i a b c
                  exact b
                . rename_i a b c
                  exact c
            )
          simp_all
          cases h4; rename_i h4; cases h4; rename_i s4 H h4
          apply φ.step_input
          . assumption
          . cases h <;> rename_i h
            . cases h
              cases h3
            . cases h
              apply split_step_external.input
          . cases H <;> rename_i H
            . cases H
              cases h <;> rename_i h
              . cases h
                cases h3
                simp_all
                rename_i H
                have H1 := @dequeue_add α
                specialize H1 H
                rename_i hh _ _ _
                have HH := @dequeue_add1 α
                specialize HH hh
                rw[H1] at HH
                rw[HH]
                apply split_step_external_spec.input
              . cases h
            . cases H
        . cases h2
          specialize h4 _ Event.output
            (by apply split_step.external_step; apply split_step_external.output
                rotate_left
                . rename_i a b c  _ _ _ _ _
                  exact a
                . rename_i a b c _ _ _ _ _
                  exact b
                . rename_i a b c _ _ _ _ _
                  exact c
                . rename_i l _ _ _ _
                  exact l
                . simp_all
            )
          simp_all
          cases h4; rename_i h4; cases h4; rename_i s4 H h4
          apply φ.step_input
          . assumption
          . constructor
          . cases H <;> rename_i H
            . cases H
              cases h <;> rename_i h
              . cases h
                cases h3
                simp_all
                rename_i H
                have H1 := @dequeue_add α
                specialize H1 H
                rename_i hh _ _ _
                have HH := @dequeue_add1 α
                specialize HH hh
                rw[H1] at HH
                rw[HH]
                apply split_step_external_spec.input
              . cases h
            . cases H
