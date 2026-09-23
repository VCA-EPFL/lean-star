variable {State Event IntEvent : Type}
variable (init : State)
variable (step: State -> Event -> State -> Prop)
variable (external_step : State -> Event -> State -> Prop)
variable (internal_step : State -> IntEvent -> State -> Prop)

inductive star : State -> List Event -> State -> Prop where
  | refl : forall s1, star s1 [] s1
  | step : forall s1 s2 s3 l e1, star s1 l s2 -> step s2 e1 s3 -> star s1 (e1 :: l) s3

inductive star_extend : State -> List Event -> State -> Prop where
  | refl : ∀ s, star_extend s [] s
  | step_int : ∀ s l s' s'' ie, star_extend s l s' -> internal_step s' ie s'' -> star_extend s l s''
  | step_ext : ∀ s l s' s'' e, star_extend s l s' -> external_step s' e s'' -> star_extend s (e :: l) s''

def behaviour_extend (l : List Event): Prop :=
  exists s', star_extend external_step internal_step init l s'

def behaviour(l : List Event): Prop :=
  exists s', star external_step init l s'
