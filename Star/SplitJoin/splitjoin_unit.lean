
import Star.SplitJoin.star

structure token (α : Type) where
  fst : α
  snd : α
  trd : α

def List.dequeue {α : Type} (l: List α) : Option (List α × α) :=
  match l with
  | x :: xs => some (xs, x)
  | [] => none


inductive Event where
| input
| output
| null
deriving Inhabited

--specification module

structure split_join_spec where
  in_out : List (Unit × Unit × Unit)

inductive split_step_external_spec : split_join_spec → Event → split_join_spec -> Prop where
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

inductive split_step_internal_spec: split_join_spec→ Event → split_join_spec-> Prop where
| in_spec : ∀ s,
  split_step_internal_spec s Event.null s


inductive split_step_spec: split_join_spec→ Event → split_join_spec-> Prop where
| external_step : ∀ i e i' ,
    split_step_external_spec i e i' →
    split_step_spec i e i'
| internal_step : ∀ i e i' ,
    split_step_internal_spec i e i' →
    split_step_spec i e i'


--implementation module

structure split_join where
  ext_input : List (Unit × Unit × Unit)
  split_1_left : List (Unit × Unit)
  split_1_right : List Unit
  split_2_left : List Unit
  split_2_right : List Unit
  join_1 :  List (Unit × Unit)
  join_2 : List (Unit × Unit × Unit)
  ext_output : List (Unit × Unit × Unit)


inductive split_step_external: split_join→ Event → split_join -> Prop where
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


inductive split_step_internal: split_join→ Event → split_join-> Prop where
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

inductive split_step : split_join→ Event → split_join -> Prop where
| external_step : ∀ i e i' ,
    split_step_external i e i' →
    split_step i e i'
| internal_step : ∀ i e i' ,
    split_step_internal i e i' →
    split_step i e i'



/-!
# Proof of correctness between implementation and specification
-/
def indistinguishability (i : split_join) (s : split_join_spec) : Prop := ∀ (i' : split_join) e, split_step i e i' -> ∃ s', split_step_spec s e s'


inductive φ : split_join → split_join_spec → Prop where
| base : ∀ i s,
    i.split_1_left = [] →
    i.split_1_right = [] →
    i.split_2_left = [] →
    i.split_2_right = [] →
    i.join_1 = [] →
    i.join_2 = [] →
    i.ext_output ++ i.ext_input = s.in_out →
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
    List.dequeue (l ++ [(a, b, c)]) = some (l', (a', b', c')) <-> l = l' ∧ (a, b,c) = (a', b', c') := by admit

theorem dequeue_add1 : ∀ {α} {l l': List (α × α × α)} {a' b' c' : α},
    List.dequeue (l) = some (l', (a', b', c')) -> l = l' ++ [(a', b', c')] := by admit

theorem dequeue_add2 : ∀ {α} {l l': List (α × α )} {a b a' b' : α},
    List.dequeue (l ++ [(a, b)]) = some (l', (a', b')) <-> l = l' ∧ (a, b) = (a', b') := by admit

theorem dequeue_add4 : ∀ {α} {l l': List (α × α)} {a' b' : α},
    List.dequeue (l) = some (l', (a', b')) -> l = l' ++ [(a', b')] := by admit

theorem dequeue_add5 : ∀ {α} {l l': List α } {a a' : α},
    List.dequeue (l ++ [(a)]) = some (l', (a')) <-> l = l' ∧ (a) = (a') := by admit

theorem dequeue_add6 : ∀ {α} {l l': List (α)} {a': α},
    List.dequeue (l) = some (l', (a')) -> l = l' ++ [(a')] := by admit



theorem φ_implies_indistinguishability (i : split_join) (s : split_join_spec) :
  φ i s -> indistinguishability i s := by admit




theorem enough (i : split_join) (s : split_join_spec) :
  φ i s -> ∀ i' (e : Event), split_step i e i' ->
    ∃ s', split_step_spec s e s' ∧ φ i' s' := by
  intro hφ i2 e hstep
  have H := hφ
  induction hφ generalizing i2 e
  . clear i s
    rename_i i s h1 h2 h3 h4 h5 h6 h7
    cases hstep <;> rename_i hstep
    . cases hstep
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
    . constructor
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
  . have hi := φ_implies_indistinguishability _ _ H
    clear i s
    rename_i i1 s1 s3 i3 h1 h2 h3 h4
    unfold indistinguishability at *
    specialize hi _ _ hstep
    cases hi
    rename_i s2 h
    constructor; rotate_left; exact s2
    constructor
    . assumption
    . cases hstep <;> rename_i hstep
      . cases hstep
        . specialize h4 _ Event.input
            (by apply split_step.external_step; apply split_step_external.input <;> assumption)
          cases h3
          cases h <;> rename_i h
          . cases h
            cases h2
            . apply φ.step_null; rotate_left
              apply split_step_internal.split_1
              dsimp
              rotate_left
              . assumption
              . assumption
              . assumption
              . rename_i a b c l _
                exact l ++ [(a, b, c)]
              . constructor
              . simp_all
                cases h4; rename_i s4 h4
                cases h4; rename_i h4 _
                cases h4 <;> rename_i h4
                . cases h4; simp_all
                . cases h4
              . simp_all; grind[dequeue_add, dequeue_add1]
            . apply φ.step_null; rotate_left
              apply split_step_internal.split_2
              rotate_left
              . assumption
              . assumption
              . assumption
              . constructor
              . simp_all
                cases h4; rename_i s4 h4
                cases h4; rename_i h4 _
                cases h4 <;> rename_i h4
                . cases h4; simp_all
                . cases h4
              . simp_all
            . apply φ.step_null; rotate_left
              apply split_step_internal.join_1
              rotate_left 2
              . assumption
              . assumption
              . rename_i l l' _ _
                exact l
              . assumption
              . constructor
              . simp_all
                cases h4; rename_i s4 h4
                cases h4; rename_i h4 _
                cases h4 <;> rename_i h4
                . cases h4; simp_all
                . cases h4
              . simp_all
              . simp_all
            . apply φ.step_null; rotate_left
              apply split_step_internal.join_2
              rotate_left 2
              . assumption
              . assumption
              . assumption
              . rename_i l l' _ _
                exact l
              . assumption
              . constructor
              . simp_all
                cases h4; rename_i s4 h4
                cases h4; rename_i h4 _
                cases h4 <;> rename_i h4
                . cases h4; simp_all
                . cases h4
              . simp_all
              . simp_all
            . apply φ.step_null; rotate_left
              apply split_step_internal.join_2_out
              rotate_left
              . assumption
              . assumption
              . assumption
              . assumption
              . constructor
              . simp_all
                cases h4; rename_i s4 h4
                cases h4; rename_i h4 _
                cases h4 <;> rename_i h4
                . cases h4; simp_all
                . cases h4
              . simp_all
          . cases h
        . cases h3
          cases h <;> rename_i h
          . cases h
            cases h2
            . specialize h4 _ Event.output
                (by apply split_step.external_step; apply split_step_external.output
                    rotate_left
                    . assumption
                    . assumption
                    . assumption
                    . rename_i l _ _ _ _ _ _ _ _ _ _ _
                      exact l
                    . simp_all)
              apply φ.step_null; rotate_left
              apply split_step_internal.split_1
              rotate_left
              . assumption
              . assumption
              . assumption
              . rename_i a b c l _
                exact l
              . constructor
              . simp_all
                cases h4; rename_i s4 h4
                cases h4; rename_i h4 _
                cases h4 <;> rename_i h4
                . cases h4; simp_all
                . cases h4
              . simp_all
            . specialize h4 _ Event.output
                (by apply split_step.external_step; apply split_step_external.output
                    rotate_left
                    . assumption
                    . assumption
                    . assumption
                    . rename_i l _ _ _ _ _ _ _ _ _ _
                      exact l
                    . simp_all)
              apply φ.step_null; rotate_left
              apply split_step_internal.split_2
              rotate_left
              . assumption
              . assumption
              . assumption
              . constructor
              . simp_all
                cases h4; rename_i s4 h4
                cases h4; rename_i h4 _
                cases h4 <;> rename_i h4
                . cases h4; simp_all
                . cases h4
              . simp_all
            . specialize h4 _ Event.output
                (by apply split_step.external_step; apply split_step_external.output
                    rotate_left
                    . assumption
                    . assumption
                    . assumption
                    . rename_i l _ _ _ _ _ _ _ _ _ _ _ _
                      exact l
                    . simp_all)
              apply φ.step_null; rotate_left
              apply split_step_internal.join_1
              rotate_left 2
              . assumption
              . assumption
              . rename_i l l' _ _
                exact l
              . assumption
              . constructor
              . simp_all
                cases h4; rename_i s4 h4
                cases h4; rename_i h4 _
                cases h4 <;> rename_i h4
                . cases h4; simp_all
                . cases h4
              . simp_all
              . simp_all
            . specialize h4 _ Event.output
                (by apply split_step.external_step; apply split_step_external.output
                    dsimp
                    assumption
                   )
              apply φ.step_null; rotate_left
              apply split_step_internal.join_2
              rotate_left 2
              . assumption
              . assumption
              . assumption
              . rename_i l l' _ _
                exact l
              . assumption
              . constructor
              . simp_all
                cases h4; rename_i s4 h4
                cases h4; rename_i h4 _
                cases h4 <;> rename_i h4
                . cases h4; simp_all
                . cases h4
              . simp_all
              . simp_all
            . specialize h4 _ Event.output
                (by apply split_step.external_step; apply split_step_external.output
                    rotate_left
                    . assumption
                    . assumption
                    . assumption
                    . exact i1.ext_output
                    . grind[dequeue_add, dequeue_add1])
              apply φ.step_null; rotate_left
              apply split_step_internal.join_2_out
              rotate_left
              . assumption
              . assumption
              . assumption
              . assumption
              . constructor
              . simp_all
                cases h4; rename_i s4 h4
                cases h4; rename_i h4 _
                cases h4 <;> rename_i h4
                . cases h4; grind[dequeue_add, dequeue_add1]
                . cases h4
              . simp_all
          . cases h
      . cases hstep
        . cases h <;> rename_i h
          . cases h
          . cases h
            cases h3
            cases h2
            . grind
            . specialize h4 _ Event.null
                (by apply split_step.internal_step; apply split_step_internal.split_1
                    assumption)
              apply φ.step_null; rotate_left
              apply split_step_internal.split_2
              rotate_left
              . assumption
              . assumption
              . rename_i  a b l _
                exact l ++ [(a, b)]
              . constructor
              . simp_all
                cases h4; rename_i s4 h4
                cases h4; rename_i h4 _
                cases h4 <;> rename_i h4
                . cases h4
                . cases h4; simp_all
              . grind[dequeue_add, dequeue_add1, dequeue_add4, dequeue_add2]
            . specialize h4 _ Event.null
                (by apply split_step.internal_step; apply split_step_internal.split_1; assumption)
              apply φ.step_null; rotate_left
              apply split_step_internal.join_1
              rotate_left 6
              . constructor
              . simp_all
                cases h4; rename_i s4 h4
                cases h4; rename_i h4 _
                cases h4 <;> rename_i h4
                . cases h4
                . cases h4; simp_all; assumption
              . grind [dequeue_add, dequeue_add1, dequeue_add4, dequeue_add2,  dequeue_add5, dequeue_add6]
              . simp_all
            . specialize h4 _ Event.null
                (by apply split_step.internal_step; apply split_step_internal.split_1; assumption)
              apply φ.step_null; rotate_left
              apply split_step_internal.join_2
              rotate_left 7
              . constructor
              . simp_all
                cases h4; rename_i s4 h4
                cases h4; rename_i h4 _
                cases h4 <;> rename_i h4
                . cases h4
                . cases h4; simp_all; assumption
              . grind [dequeue_add, dequeue_add1, dequeue_add4, dequeue_add2,  dequeue_add5, dequeue_add6]
              . simp_all
            . specialize h4 _ Event.null
                (by apply split_step.internal_step; apply split_step_internal.split_1; assumption)
              apply φ.step_null; rotate_left
              apply split_step_internal.join_2_out
              rotate_left 5
              . constructor
              . simp_all
                cases h4; rename_i s4 h4
                cases h4; rename_i h4 _
                cases h4 <;> rename_i h4
                . cases h4
                . cases h4; simp_all; assumption
              . grind [dequeue_add, dequeue_add1, dequeue_add4, dequeue_add2,  dequeue_add5, dequeue_add6]
        . cases h <;> rename_i h
          . cases h
          . cases h
            cases h3
            cases h2
            . specialize h4 _ Event.null
                (by apply split_step.internal_step; apply split_step_internal.split_2
                    rotate_left
                    . assumption
                    . assumption
                    . exact i1.split_1_left
                    . dsimp; grind [dequeue_add, dequeue_add1, dequeue_add4, dequeue_add2,  dequeue_add5, dequeue_add6])
              apply φ.step_null; rotate_left
              apply split_step_internal.split_1
              rotate_left 5
              . constructor
              . simp_all
                cases h4; rename_i s4 h4
                cases h4; rename_i h4 _
                cases h4 <;> rename_i h4
                . cases h4
                . cases h4; rename_i H _ _ _ _ _ _
                  have H' :=  dequeue_add4 H
                  rename_i hh
                  rw[H'] at hh; assumption
              . grind [dequeue_add, dequeue_add1, dequeue_add4, dequeue_add2,  dequeue_add5, dequeue_add6]
            . grind
            . specialize h4 _ Event.null
                (by apply split_step.internal_step; apply split_step_internal.split_2
                    assumption)
              apply φ.step_null; rotate_left
              apply split_step_internal.join_1
              rotate_left 6
              . constructor
              . simp_all
                cases h4; rename_i s4 h4
                cases h4; rename_i h4 _
                cases h4 <;> rename_i h4
                . cases h4
                . cases h4; simp_all; assumption
              . grind [dequeue_add, dequeue_add1, dequeue_add4, dequeue_add2,  dequeue_add5, dequeue_add6]
              . grind [dequeue_add, dequeue_add1, dequeue_add4, dequeue_add2,  dequeue_add5, dequeue_add6]
            . specialize h4 _ Event.null
                (by apply split_step.internal_step; apply split_step_internal.split_2
                    assumption)
              apply φ.step_null; rotate_left
              apply split_step_internal.join_2
              rotate_left 7
              . constructor
              . simp_all
                cases h4; rename_i s4 h4
                cases h4; rename_i h4 _
                cases h4 <;> rename_i h4
                . cases h4
                . cases h4; simp_all; assumption
              . grind [dequeue_add, dequeue_add1, dequeue_add4, dequeue_add2,  dequeue_add5, dequeue_add6]
              . grind [dequeue_add, dequeue_add1, dequeue_add4, dequeue_add2,  dequeue_add5, dequeue_add6]
            . specialize h4 _ Event.null
                (by apply split_step.internal_step; apply split_step_internal.split_2
                    assumption)
              apply φ.step_null; rotate_left
              apply split_step_internal.join_2_out
              rotate_left 5
              . constructor
              . simp_all
                cases h4; rename_i s4 h4
                cases h4; rename_i h4 _
                cases h4 <;> rename_i h4
                . cases h4
                . cases h4; simp_all; assumption
              . grind [dequeue_add, dequeue_add1, dequeue_add4, dequeue_add2,  dequeue_add5, dequeue_add6]
        . cases h <;> rename_i h
          . cases h
          . cases h
            cases h3
            cases h2
            . specialize h4 _ Event.null
                (by apply split_step.internal_step; apply split_step_internal.join_1
                    rotate_left 2
                    . assumption
                    . assumption
                    . exact i1.split_1_right
                    . assumption
                    . dsimp; grind [dequeue_add, dequeue_add1, dequeue_add4, dequeue_add2,  dequeue_add5, dequeue_add6]
                    . dsimp; grind [dequeue_add, dequeue_add1, dequeue_add4, dequeue_add2,  dequeue_add5, dequeue_add6])
              apply φ.step_null; rotate_left
              apply split_step_internal.split_1
              rotate_left 5
              . constructor
              . simp_all
                cases h4; rename_i s4 h4
                cases h4; rename_i h4 _
                cases h4 <;> rename_i h4
                . cases h4
                . cases h4; rename_i H _ _ _ _ _ _ _
                  have H' :=  dequeue_add6 H
                  rename_i hh
                  rw[H'] at hh; assumption
              . grind [dequeue_add, dequeue_add1, dequeue_add4, dequeue_add2,  dequeue_add5, dequeue_add6]
            . specialize h4 _ Event.null
                (by apply split_step.internal_step; apply split_step_internal.join_1
                    rotate_left 2
                    . assumption
                    . assumption
                    . rename_i L _ _ _ _ _ _ _
                      exact L
                    . exact i1.split_2_right
                    . dsimp; grind [dequeue_add, dequeue_add1, dequeue_add4, dequeue_add2,  dequeue_add5, dequeue_add6]
                    . dsimp; grind [dequeue_add, dequeue_add1, dequeue_add4, dequeue_add2,  dequeue_add5, dequeue_add6])
              apply φ.step_null; rotate_left
              apply split_step_internal.split_2
              rotate_left 4
              . constructor
              . simp_all
                cases h4; rename_i s4 h4
                cases h4; rename_i h4 _
                cases h4 <;> rename_i h4
                . cases h4
                . cases h4;  simp_all
                  rename_i H _ _ _ _ _ _
                  have H' :=  dequeue_add6 H
                  rename_i hh
                  rw[H'] at hh; assumption
              . grind [dequeue_add, dequeue_add1, dequeue_add4, dequeue_add2,  dequeue_add5, dequeue_add6]
            . grind
            . specialize h4 _ Event.null
                (by apply split_step.internal_step; apply split_step_internal.join_1
                    rotate_left 2
                    . assumption
                    . assumption
                    . rename_i l' l _ _ _ _ _ _ _ _ _
                      exact l'
                    . rename_i l' l _ _ _ _ _ _ _ _ _
                      exact l
                    . dsimp; grind [dequeue_add, dequeue_add1, dequeue_add4, dequeue_add2,  dequeue_add5, dequeue_add6]
                    . dsimp; grind [dequeue_add, dequeue_add1, dequeue_add4, dequeue_add2,  dequeue_add5, dequeue_add6])
              apply φ.step_null; rotate_left
              apply split_step_internal.join_2
              rotate_left 7
              . constructor
              . simp_all
                cases h4; rename_i s4 h4
                cases h4; rename_i h4 _
                cases h4 <;> rename_i h4
                . cases h4
                . cases h4;  simp_all; assumption
              . grind [dequeue_add, dequeue_add1, dequeue_add4, dequeue_add2,  dequeue_add5, dequeue_add6]
              . grind [dequeue_add, dequeue_add1, dequeue_add4, dequeue_add2,  dequeue_add5, dequeue_add6]
            . specialize h4 _ Event.null
                (by apply split_step.internal_step; apply split_step_internal.join_1
                    rotate_left 2
                    . assumption
                    . assumption
                    . rename_i l' l _ _ _ _ _ _ _
                      exact l'
                    . rename_i l' l _ _ _ _ _ _ _
                      exact l
                    . dsimp; grind [dequeue_add, dequeue_add1, dequeue_add4, dequeue_add2,  dequeue_add5, dequeue_add6]
                    . dsimp; grind [dequeue_add, dequeue_add1, dequeue_add4, dequeue_add2,  dequeue_add5, dequeue_add6])
              apply φ.step_null; rotate_left
              apply split_step_internal.join_2_out
              rotate_left 5
              . constructor
              . simp_all
                cases h4; rename_i s4 h4
                cases h4; rename_i h4 _
                cases h4 <;> rename_i h4
                . cases h4
                . cases h4;  simp_all; assumption
              . grind [dequeue_add, dequeue_add1, dequeue_add4, dequeue_add2,  dequeue_add5, dequeue_add6]
        . cases h <;> rename_i h
          . cases h
          . cases h
            cases h3
            cases h2
            . specialize h4 _ Event.null
                (by apply split_step.internal_step; apply split_step_internal.join_2
                    rotate_left 2
                    . assumption
                    . assumption
                    . assumption
                    . assumption
                    . assumption
                    . dsimp; grind [dequeue_add, dequeue_add1, dequeue_add4, dequeue_add2,  dequeue_add5, dequeue_add6]
                    . dsimp; grind [dequeue_add, dequeue_add1, dequeue_add4, dequeue_add2,  dequeue_add5, dequeue_add6])
              apply φ.step_null; rotate_left
              apply split_step_internal.split_1
              rotate_left 5
              . constructor
              . simp_all
                cases h4; rename_i s4 h4
                cases h4; rename_i h4 _
                cases h4 <;> rename_i h4
                . cases h4
                . cases h4; simp_all; assumption
              . grind [dequeue_add, dequeue_add1, dequeue_add4, dequeue_add2,  dequeue_add5, dequeue_add6]
            . specialize h4 _ Event.null
                (by apply split_step.internal_step; apply split_step_internal.join_2
                    rotate_left 2
                    . assumption
                    . assumption
                    . assumption
                    . rename_i L _ _ _ _ _ _ _
                      exact L
                    . exact i1.split_2_left
                    . dsimp; grind [dequeue_add, dequeue_add1, dequeue_add4, dequeue_add2,  dequeue_add5, dequeue_add6]
                    . dsimp; grind [dequeue_add, dequeue_add1, dequeue_add4, dequeue_add2,  dequeue_add5, dequeue_add6])
              apply φ.step_null; rotate_left
              apply split_step_internal.split_2
              rotate_left 4
              . constructor
              . simp_all
                cases h4; rename_i s4 h4
                cases h4; rename_i h4 _
                cases h4 <;> rename_i h4
                . cases h4
                . cases h4; simp_all
                  rename_i H _ _ _ _ _ _
                  have H' :=  dequeue_add6 H
                  rename_i hh
                  rw[H'] at hh; assumption
              . grind [dequeue_add, dequeue_add1, dequeue_add4, dequeue_add2,  dequeue_add5, dequeue_add6]
            . specialize h4 _ Event.null
                (by apply split_step.internal_step; apply split_step_internal.join_2
                    rotate_left 2
                    . assumption
                    . assumption
                    . assumption
                    . exact i1.join_1
                    . rename_i L _ _ _ _ _ _ _ _
                      exact L
                    . dsimp; grind [dequeue_add, dequeue_add1, dequeue_add4, dequeue_add2,  dequeue_add5, dequeue_add6]
                    . dsimp; grind [dequeue_add, dequeue_add1, dequeue_add4, dequeue_add2,  dequeue_add5, dequeue_add6])
              apply φ.step_null; rotate_left
              apply split_step_internal.join_1
              rotate_left 6
              . constructor
              . simp_all
                cases h4; rename_i s4 h4
                cases h4; rename_i h4 _
                cases h4 <;> rename_i h4
                . cases h4
                . cases h4; simp_all
                  rename_i H _ _ _ _ _ _ _ _ _
                  have H' :=  dequeue_add6 H
                  rename_i hh
                  rw[H'] at hh; assumption
              . grind [dequeue_add, dequeue_add1, dequeue_add4, dequeue_add2,  dequeue_add5, dequeue_add6]
              . grind [dequeue_add, dequeue_add1, dequeue_add4, dequeue_add2,  dequeue_add5, dequeue_add6]
            . grind
            . specialize h4 _ Event.null
                (by apply split_step.internal_step; apply split_step_internal.join_2
                    rotate_left 2
                    . assumption
                    . assumption
                    . assumption
                    . rename_i L _ _ _ _ _ _ _ _
                      exact L
                    . assumption
                    . dsimp; grind [dequeue_add, dequeue_add1, dequeue_add4, dequeue_add2,  dequeue_add5, dequeue_add6]
                    . dsimp; grind [dequeue_add, dequeue_add1, dequeue_add4, dequeue_add2,  dequeue_add5, dequeue_add6])
              apply φ.step_null; rotate_left
              apply split_step_internal.join_2_out
              rotate_left 5
              . constructor
              . simp_all
                cases h4; rename_i s4 h4
                cases h4; rename_i h4 _
                cases h4 <;> rename_i h4
                . cases h4
                . cases h4; simp_all; assumption
              . grind [dequeue_add, dequeue_add1, dequeue_add4, dequeue_add2,  dequeue_add5, dequeue_add6]
        . cases h <;> rename_i h
          . cases h
          . cases h
            cases h3
            cases h2
            . specialize h4 _ Event.null
                (by apply split_step.internal_step; apply split_step_internal.join_2_out
                    assumption)
              apply φ.step_null; rotate_left
              apply split_step_internal.split_1
              rotate_left 5
              . constructor
              . simp_all
                cases h4; rename_i s4 h4
                cases h4; rename_i h4 _
                cases h4 <;> rename_i h4
                . cases h4
                . cases h4; simp_all; assumption
              . grind [dequeue_add, dequeue_add1, dequeue_add4, dequeue_add2,  dequeue_add5, dequeue_add6]
            . specialize h4 _ Event.null
                (by apply split_step.internal_step; apply split_step_internal.join_2_out
                    assumption)
              apply φ.step_null; rotate_left
              apply split_step_internal.split_2
              rotate_left 4
              . constructor
              . simp_all
                cases h4; rename_i s4 h4
                cases h4; rename_i h4 _
                cases h4 <;> rename_i h4
                . cases h4
                . cases h4; simp_all; assumption
              . grind [dequeue_add, dequeue_add1, dequeue_add4, dequeue_add2,  dequeue_add5, dequeue_add6]
            . specialize h4 _ Event.null
                (by apply split_step.internal_step; apply split_step_internal.join_2_out
                    assumption)
              apply φ.step_null; rotate_left
              apply split_step_internal.join_1
              rotate_left 6
              . constructor
              . simp_all
                cases h4; rename_i s4 h4
                cases h4; rename_i h4 _
                cases h4 <;> rename_i h4
                . cases h4
                . cases h4; simp_all; assumption
              . grind [dequeue_add, dequeue_add1, dequeue_add4, dequeue_add2,  dequeue_add5, dequeue_add6]
              . grind [dequeue_add, dequeue_add1, dequeue_add4, dequeue_add2,  dequeue_add5, dequeue_add6]
            . specialize h4 _ Event.null
                (by apply split_step.internal_step; apply split_step_internal.join_2_out
                    rotate_left
                    . assumption
                    . assumption
                    . assumption
                    . exact i1.join_2
                    . grind [dequeue_add, dequeue_add1, dequeue_add4, dequeue_add2,  dequeue_add5, dequeue_add6])
              apply φ.step_null; rotate_left
              apply split_step_internal.join_2
              rotate_left 7
              . constructor
              . simp_all
                cases h4; rename_i s4 h4
                cases h4; rename_i h4 _
                cases h4 <;> rename_i h4
                . cases h4
                . cases h4; simp_all
                  rename_i H _ _ _ _ _ _ _ _ _
                  have H' :=  dequeue_add6 H
                  rename_i hh
                  rw[H'] at hh; assumption
              . grind [dequeue_add, dequeue_add1, dequeue_add4, dequeue_add2,  dequeue_add5, dequeue_add6]
              . grind [dequeue_add, dequeue_add1, dequeue_add4, dequeue_add2,  dequeue_add5, dequeue_add6]
            . grind
