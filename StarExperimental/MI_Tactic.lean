import StarExperimental.Tatic
import StarExperimental.MI

/-!
# Variante del modello MI: anche il rilascio in volo

Il modello base è `MI2` in `StarExperimental/Tatic.lean`, dove il rilascio della
linea e la sua registrazione da parte del parent sono un passo solo. Qui sono
separati, quindi il token può stare in **tutti e tre** i posti che
`MIState.tokens` di MI.lean conta:

    CacheState.tokens cs = cs.state.tok                             -- `c`
                         + cs.queue_pc.countP PCEvent.isGrant       -- `g`
                         + cs.queue_cp.countP CPEvent.isRelease     -- `r`

Le due regole nuove rispetto a `MI2`:

* `release i` — `rq_data_not_available`: la cache lascia la linea (`c i := I`) e
  il rilascio parte (`r i := true`). La directory del parent è ancora `M`: non
  sa ancora niente;
* `recvRelease i` — `downgrade_from_M_rq1`: il parent consuma il rilascio e
  libera la directory (`d i := I`, `r i := false`).

Costo: la chiusura passa da 44 a **213 stati** su 256 — lo stesso ordine di
grandezza di `unreachable_setM`, che infatti è un'unione di quattro disgiunti.
Circa un minuto di compilazione, da cui `maxHeartbeats`.

Le semplificazioni rispetto a `MIState n` sono le stesse elencate in `Tatic.lean`.
-/

open THEORY
open Relation

namespace MIGrantRelease

structure St where
  c0 : Bstate
  c1 : Bstate
  d0 : Bstate
  d1 : Bstate
  g0 : Bool      -- `rsM` in volo parent -> cache 0
  g1 : Bool
  r0 : Bool      -- `rsIμ` in volo cache 0 -> parent
  r1 : Bool
deriving DecidableEq, Repr

inductive Rl where
  | grant0 | grant1
  | recvGrant0 | recvGrant1
  | release0 | release1
  | recvRelease0 | recvRelease1
deriving DecidableEq, Repr

inductive Step : Rl → St → St → Prop where
  | grant0 {s} : s.d0 = .I → s.d1 = .I → Step .grant0 s { s with d0 := .M, g0 := true }
  | grant1 {s} : s.d0 = .I → s.d1 = .I → Step .grant1 s { s with d1 := .M, g1 := true }
  | recvGrant0 {s} : s.g0 = true → s.c0 = .I → Step .recvGrant0 s { s with c0 := .M, g0 := false }
  | recvGrant1 {s} : s.g1 = true → s.c1 = .I → Step .recvGrant1 s { s with c1 := .M, g1 := false }
  | release0 {s} : s.c0 = .M → Step .release0 s { s with c0 := .I, r0 := true }
  | release1 {s} : s.c1 = .M → Step .release1 s { s with c1 := .I, r1 := true }
  | recvRelease0 {s} : s.r0 = true → Step .recvRelease0 s { s with d0 := .I, r0 := false }
  | recvRelease1 {s} : s.r1 = true → Step .recvRelease1 s { s with d1 := .I, r1 := false }

def initSt : St := ⟨.I, .I, .I, .I, false, false, false, false⟩

def miFull : LTS Rl where
  S := St
  transitions := Step
  init s := s = initSt
  flushed _ := True

def twoCachesM (s : St) : Prop := s.c0 = .M ∧ s.c1 = .M

set_option maxHeartbeats 4000000 in
/-- **Due cache in `M` è irraggiungibile**, anche con entrambi i messaggi in volo.
64 stati di partenza, 213 nella chiusura. -/
theorem twoCachesM_unreachable : ∀ s, twoCachesM s → ¬ miFull.reachable s := by
  backward_search_all initSt


--MI vero



#print axioms twoCachesM_unreachable
-- depends on axioms: [propext, Classical.choice, Quot.sound]

end MIGrantRelease


/-!
# `twoCachesM` su `MI` vero, via `backward_search_all`

I modelli sopra (`MI2` in Tatic.lean, `miFull` qui) sono astrazioni finite scritte a
mano, senza un legame formale con `MIState n` di MI.lean. Qui il legame c'è:

* `MISim.twoCachesM` è la `twoCachesM` di MI.lean (due cache distinte entrambe in `M`,
  su `MIState n` per `n` qualsiasi);
* `MISim.twoCachesM_unreachable : ∀ s : MIState n, twoCachesM s → ¬ MI.reachable s`
  è lo stesso enunciato di `reachable_MI1`, ma dimostrato con la tattica.

La tattica non può girare direttamente su `MI` — `MIState n` è infinito (`Value = Nat`,
code `List`, `n` generico) e `MI` è un `MI.LTS`, non un `THEORY.LTS` — quindi si passa
per un'astrazione finita **dimostrata corretta**:

1. **Il modello astratto `miAbs`** guarda una coppia di indici `i ≠ j` e, per ciascuno,
   tiene lo stato della cache (`c`), la riga della directory del parent (`d`) e un
   contatore saturo `m ∈ {0, 1, ≥2}` dei messaggi che portano il token (`rsM` in volo
   verso la cache più `rsIμ` in volo verso il parent). I messaggi senza token (`rqM`,
   `rqIμ`), i valori, e le code viste dagli altri indici sono astratti via. Il
   contatore saturo serve perché le code di MI sono illimitate: con un booleano la
   ricezione di un grant non saprebbe se ne restano altri, e l'astrazione sarebbe
   scorretta (o, resa nondeterministica, renderebbe raggiungibile lo stato cattivo).
   144 stati; `backward_search_all` chiude da 36 semi in 116 stati.

2. **La simulazione** (`abs_step`): ogni passo di `mi_step_internal` su uno stato
   con le code sincronizzate (`synced`, invariante preservato da `synced_step`)
   o non cambia l'astrazione, o è un passo di `miAbs`. Si dimostra indice per indice:
   `step_local` dice che un passo tocca la vista di un solo indice `q` e in uno dei
   cinque modi di `LocalStep`; `absV_step_i`/`absV_step_j` traducono quel modo in una
   regola astratta, secondo che `q` sia `i`, `j` o nessuno dei due (stutter).

3. **Il trasporto** (`reach_abs`): un cammino da `default` in `MI` diventa un cammino
   da `initSt` in `miAbs`; se `s` ha `i` e `j` in `M`, `abs i j s` ha `c0 = c1 = M`,
   contro `twoCachesM_abs_unreachable`.

Nota su `MI.reachable`: in MI.lean `mi_init` è `Inhabited.default`, cioè `True` su ogni
stato, quindi `¬ MI.reachable s` dice solo "esiste uno stato da cui `s` non è
raggiungibile" — ed è vero per *ogni* `s` (per `n ≥ 1` basta uno stato con una
`extqueue.rs` più lunga: nei passi interni quella coda non si accorcia mai). Vale quindi
anche per `reachable_MI1` di MI.lean. Il contenuto vero è la forma forte
`twoCachesM_not_reachable_from_default`, che è lo stesso enunciato di
`two_caches_M_not_reachable` di MI.lean (dimostrato lì a mano con `unreachable_setM`),
ridimostrato qui passando per la tattica.
-/

namespace MISim

inductive Cnt where
  | zero | one | many
deriving DecidableEq, Repr

structure St where
  c0 : Bstate
  c1 : Bstate
  d0 : Bstate
  d1 : Bstate
  m0 : Cnt
  m1 : Cnt
deriving DecidableEq, Repr

/-- Le regole, per la cache `0` e per la `1`:

* `grant`       ↔ `upgrade_to_M_data_avilable_rq1`: il parent concede la linea
                  (`d := M`, un `rsM` in più in volo), solo se tutta la directory è `I`;
* `recvGrant`   ↔ `upgrade_from_I_rs`: la cache riceve il grant (`c := M`, un messaggio in meno);
* `release`     ↔ `rq_data_not_available` / `downgrade_from_M_rs`: la cache lascia la linea
                  (`c := I`, un `rsIμ` in più in volo);
* `recvRelease` ↔ `downgrade_from_M_rq1`: il parent registra il rilascio (`d := I`, un
                  messaggio in meno). -/
inductive Rl where
  | grant0 | grant1
  | recvGrant0 | recvGrant1
  | release0 | release1
  | recvRelease0 | recvRelease1
deriving DecidableEq, Repr

/-- Ogni regola è scritta tre volte, una per valore del contatore saturo `m`:
`_z/_o/_m` = `m` vale `zero/one/many` prima del passo (incremento), `_o/_mo/_mm` =
`m` passa da `one` a `zero`, da `many` a `one`, da `many` a `many` (decremento, che su
`many` è nondeterministico). Così ogni conclusione è un letterale e la tattica inverte
per pura unificazione; le forme "aritmetiche" `Step.grant0'`, `Step.recvGrant0'`, … qui
sotto le ricompattano per la simulazione. -/
inductive Step : Rl → St → St → Prop where
  | grant0_z {s} : s.d0 = .I → s.d1 = .I → s.m0 = .zero → Step .grant0 s { s with d0 := .M, m0 := .one }
  | grant0_o {s} : s.d0 = .I → s.d1 = .I → s.m0 = .one  → Step .grant0 s { s with d0 := .M, m0 := .many }
  | grant0_m {s} : s.d0 = .I → s.d1 = .I → s.m0 = .many → Step .grant0 s { s with d0 := .M, m0 := .many }
  | grant1_z {s} : s.d0 = .I → s.d1 = .I → s.m1 = .zero → Step .grant1 s { s with d1 := .M, m1 := .one }
  | grant1_o {s} : s.d0 = .I → s.d1 = .I → s.m1 = .one  → Step .grant1 s { s with d1 := .M, m1 := .many }
  | grant1_m {s} : s.d0 = .I → s.d1 = .I → s.m1 = .many → Step .grant1 s { s with d1 := .M, m1 := .many }
  | recvGrant0_o  {s} : s.c0 = .I → s.m0 = .one  → Step .recvGrant0 s { s with c0 := .M, m0 := .zero }
  | recvGrant0_mo {s} : s.c0 = .I → s.m0 = .many → Step .recvGrant0 s { s with c0 := .M, m0 := .one }
  | recvGrant0_mm {s} : s.c0 = .I → s.m0 = .many → Step .recvGrant0 s { s with c0 := .M, m0 := .many }
  | recvGrant1_o  {s} : s.c1 = .I → s.m1 = .one  → Step .recvGrant1 s { s with c1 := .M, m1 := .zero }
  | recvGrant1_mo {s} : s.c1 = .I → s.m1 = .many → Step .recvGrant1 s { s with c1 := .M, m1 := .one }
  | recvGrant1_mm {s} : s.c1 = .I → s.m1 = .many → Step .recvGrant1 s { s with c1 := .M, m1 := .many }
  | release0_z {s} : s.c0 = .M → s.m0 = .zero → Step .release0 s { s with c0 := .I, m0 := .one }
  | release0_o {s} : s.c0 = .M → s.m0 = .one  → Step .release0 s { s with c0 := .I, m0 := .many }
  | release0_m {s} : s.c0 = .M → s.m0 = .many → Step .release0 s { s with c0 := .I, m0 := .many }
  | release1_z {s} : s.c1 = .M → s.m1 = .zero → Step .release1 s { s with c1 := .I, m1 := .one }
  | release1_o {s} : s.c1 = .M → s.m1 = .one  → Step .release1 s { s with c1 := .I, m1 := .many }
  | release1_m {s} : s.c1 = .M → s.m1 = .many → Step .release1 s { s with c1 := .I, m1 := .many }
  | recvRelease0_o  {s} : s.m0 = .one  → Step .recvRelease0 s { s with d0 := .I, m0 := .zero }
  | recvRelease0_mo {s} : s.m0 = .many → Step .recvRelease0 s { s with d0 := .I, m0 := .one }
  | recvRelease0_mm {s} : s.m0 = .many → Step .recvRelease0 s { s with d0 := .I, m0 := .many }
  | recvRelease1_o  {s} : s.m1 = .one  → Step .recvRelease1 s { s with d1 := .I, m1 := .zero }
  | recvRelease1_mo {s} : s.m1 = .many → Step .recvRelease1 s { s with d1 := .I, m1 := .one }
  | recvRelease1_mm {s} : s.m1 = .many → Step .recvRelease1 s { s with d1 := .I, m1 := .many }

def initSt : St := ⟨.I, .I, .I, .I, .zero, .zero⟩

def miAbs : LTS Rl where
  S := St
  transitions := Step
  init s := s = initSt
  flushed _ := True

def twoCachesM_abs (s : St) : Prop := s.c0 = .M ∧ s.c1 = .M

set_option maxHeartbeats 4000000 in
/-- **Due cache in `M` è irraggiungibile nel modello astratto.** 36 stati di
partenza (c0 = c1 = M, il resto libero), 116 nella chiusura all'indietro. -/
theorem twoCachesM_abs_unreachable : ∀ s, twoCachesM_abs s → ¬ miAbs.reachable s := by
  backward_search_all initSt

/-! ## Contatori saturi -/

/-- `0`, `1`, "almeno 2". (`Cnt.ofNat` è il nome generato automaticamente per gli enum.) -/
def Cnt.ofCount : Nat → Cnt
  | 0 => .zero
  | 1 => .one
  | _ => .many

def Cnt.succ : Cnt → Cnt
  | .zero => .one
  | _ => .many

theorem Cnt.ofCount_succ (k : Nat) : Cnt.ofCount (k + 1) = (Cnt.ofCount k).succ := by
  match k with
  | 0 => rfl
  | 1 => rfl
  | _ + 2 => rfl

/-! ## I passi astratti in forma "aritmetica" -/

theorem Step.grant0' {s : St} (h0 : s.d0 = .I) (h1 : s.d1 = .I) :
    Step .grant0 s { s with d0 := .M, m0 := s.m0.succ } := by
  cases hm : s.m0
  · exact Step.grant0_z h0 h1 hm
  · exact Step.grant0_o h0 h1 hm
  · exact Step.grant0_m h0 h1 hm

theorem Step.grant1' {s : St} (h0 : s.d0 = .I) (h1 : s.d1 = .I) :
    Step .grant1 s { s with d1 := .M, m1 := s.m1.succ } := by
  cases hm : s.m1
  · exact Step.grant1_z h0 h1 hm
  · exact Step.grant1_o h0 h1 hm
  · exact Step.grant1_m h0 h1 hm

theorem Step.release0' {s : St} (hc : s.c0 = .M) :
    Step .release0 s { s with c0 := .I, m0 := s.m0.succ } := by
  cases hm : s.m0
  · exact Step.release0_z hc hm
  · exact Step.release0_o hc hm
  · exact Step.release0_m hc hm

theorem Step.release1' {s : St} (hc : s.c1 = .M) :
    Step .release1 s { s with c1 := .I, m1 := s.m1.succ } := by
  cases hm : s.m1
  · exact Step.release1_z hc hm
  · exact Step.release1_o hc hm
  · exact Step.release1_m hc hm

theorem Step.recvGrant0' {s : St} {k : Nat} (hc : s.c0 = .I) (hm : s.m0 = Cnt.ofCount (k + 1)) :
    Step .recvGrant0 s { s with c0 := .M, m0 := Cnt.ofCount k } := by
  match k with
  | 0 => exact Step.recvGrant0_o hc hm
  | 1 => exact Step.recvGrant0_mo hc hm
  | _ + 2 => exact Step.recvGrant0_mm hc hm

theorem Step.recvGrant1' {s : St} {k : Nat} (hc : s.c1 = .I) (hm : s.m1 = Cnt.ofCount (k + 1)) :
    Step .recvGrant1 s { s with c1 := .M, m1 := Cnt.ofCount k } := by
  match k with
  | 0 => exact Step.recvGrant1_o hc hm
  | 1 => exact Step.recvGrant1_mo hc hm
  | _ + 2 => exact Step.recvGrant1_mm hc hm

theorem Step.recvRelease0' {s : St} {k : Nat} (hm : s.m0 = Cnt.ofCount (k + 1)) :
    Step .recvRelease0 s { s with d0 := .I, m0 := Cnt.ofCount k } := by
  match k with
  | 0 => exact Step.recvRelease0_o hm
  | 1 => exact Step.recvRelease0_mo hm
  | _ + 2 => exact Step.recvRelease0_mm hm

theorem Step.recvRelease1' {s : St} {k : Nat} (hm : s.m1 = Cnt.ofCount (k + 1)) :
    Step .recvRelease1 s { s with d1 := .I, m1 := Cnt.ofCount k } := by
  match k with
  | 0 => exact Step.recvRelease1_o hm
  | 1 => exact Step.recvRelease1_mo hm
  | _ + 2 => exact Step.recvRelease1_mm hm

/-! ## La vista locale di un indice -/

/-- Messaggi che portano il token, contati dal lato cache. -/
def cacheMsgs (cs : CacheState) : Nat :=
  cs.queue_pc.countP PCEvent.isGrant + cs.queue_cp.countP CPEvent.isRelease

/-- Gli stessi messaggi, contati dal lato parent. -/
def parentMsgs {n} (p : ParentState n) (k : Fin n) : Nat :=
  (p.queue_pci k).countP PCEvent.isGrant + (p.queue_cip k).countP CPEvent.isRelease

/-- Quello che l'astrazione vede dell'indice `k`: stato della cache, messaggi
con token in volo, riga della directory. -/
structure LV where
  c : Bstate
  m : Nat
  d : Bstate

def view {n} (s : MIState n) (k : Fin n) : LV :=
  ⟨(s.caches k).state, cacheMsgs (s.caches k), s.parent.shared_state k⟩

/-- Le due copie di ogni coda coincidono: è `¬ MIState.desynced` di MI.lean, in forma
positiva (cfr. `synced_of_not_desynced`). -/
def synced {n} (s : MIState n) : Prop :=
  ∀ k, s.parent.queue_cip k = (s.caches k).queue_cp ∧ s.parent.queue_pci k = (s.caches k).queue_pc

/-- Cosa può succedere alla vista di un indice in un passo. `allI` è la condizione
globale della concessione ("tutta la directory è `I`"). -/
inductive LocalStep (allI : Prop) : LV → LV → Prop where
  | stutter {v} : LocalStep allI v v
  | release {m d} : LocalStep allI ⟨.M, m, d⟩ ⟨.I, m + 1, d⟩
  | recvGrant {k d} : LocalStep allI ⟨.I, k + 1, d⟩ ⟨.M, k, d⟩
  | grant {c m} : allI → LocalStep allI ⟨c, m, .I⟩ ⟨c, m + 1, .M⟩
  | recvRelease {c k d} : LocalStep allI ⟨c, k + 1, d⟩ ⟨c, k, .I⟩

theorem LocalStep.stutter' {allI} {v v' : LV} (hc : v'.c = v.c) (hm : v'.m = v.m)
    (hd : v'.d = v.d) : LocalStep allI v v' := by
  obtain ⟨c, m, d⟩ := v; obtain ⟨c', m', d'⟩ := v'
  simp only at hc hm hd; subst hc hm hd
  exact LocalStep.stutter

theorem LocalStep.release' {allI} {v v' : LV} (hc : v.c = .M) (hc' : v'.c = .I)
    (hm : v'.m = v.m + 1) (hd : v'.d = v.d) : LocalStep allI v v' := by
  obtain ⟨c, m, d⟩ := v; obtain ⟨c', m', d'⟩ := v'
  simp only at hc hc' hm hd; subst hc hc' hm hd
  exact LocalStep.release

theorem LocalStep.recvGrant' {allI} {v v' : LV} (hc : v.c = .I) (hc' : v'.c = .M)
    (hm : v.m = v'.m + 1) (hd : v'.d = v.d) : LocalStep allI v v' := by
  obtain ⟨c, m, d⟩ := v; obtain ⟨c', m', d'⟩ := v'
  simp only at hc hc' hm hd; subst hc hc' hm hd
  exact LocalStep.recvGrant

theorem LocalStep.grant' {allI} {v v' : LV} (h : allI) (hc : v'.c = v.c)
    (hm : v'.m = v.m + 1) (hd : v.d = .I) (hd' : v'.d = .M) : LocalStep allI v v' := by
  obtain ⟨c, m, d⟩ := v; obtain ⟨c', m', d'⟩ := v'
  simp only at hc hm hd hd'; subst hc hm hd hd'
  exact LocalStep.grant h

theorem LocalStep.recvRelease' {allI} {v v' : LV} (hc : v'.c = v.c)
    (hm : v.m = v'.m + 1) (hd' : v'.d = .I) : LocalStep allI v v' := by
  obtain ⟨c, m, d⟩ := v; obtain ⟨c', m', d'⟩ := v'
  simp only at hc hm hd'; subst hc hm hd'
  exact LocalStep.recvRelease

/-! ## Passo di cache -/

theorem cache_step_local {cs cs' : CacheState} {e} (h : cache_mi_step_internal cs e cs')
    (d : Bstate) (allI : Prop) :
    LocalStep allI ⟨cs.state, cacheMsgs cs, d⟩ ⟨cs'.state, cacheMsgs cs', d⟩ := by
  cases h with
  | ld_rq_data_available rst h1 h2 => exact LocalStep.stutter' rfl rfl rfl
  | st_rq_M_state v rst h1 h2 => exact LocalStep.stutter' rfl rfl rfl
  | rq_data_not_available h2 =>
      refine LocalStep.release' h2 rfl ?_ rfl
      simp [cacheMsgs, List.countP_append, CPEvent.isRelease]; omega
  | upgrade_from_I_rq h2 =>
      refine LocalStep.stutter' rfl ?_ rfl
      simp [cacheMsgs, List.countP_append, CPEvent.isRelease]
  | upgrade_from_I_rs v j hj h2 =>
      have hc := countP_eraseIdx PCEvent.isGrant cs.queue_pc j (PCEvent.rsM v) hj
      simp [PCEvent.isGrant] at hc
      refine LocalStep.recvGrant' h2 rfl ?_ rfl
      simp [cacheMsgs]; omega
  | downgrade_from_M_rs j hj h2 =>
      have hc := countP_eraseIdx PCEvent.isGrant cs.queue_pc j PCEvent.rqIμ hj
      simp [PCEvent.isGrant] at hc
      refine LocalStep.release' h2 rfl ?_ rfl
      simp [cacheMsgs, List.countP_append, CPEvent.isRelease]; omega

/-! ## Passo del parent -/

theorem parent_step_local' {n} {p1 p2 : ParentState n} {e q}
    (h : parent_mi_step p1 (.upd_queue e q) p2) (c : Bstate) :
    LocalStep (∀ k, p1.shared_state k = Bstate.I)
      ⟨c, parentMsgs p1 q, p1.shared_state q⟩ ⟨c, parentMsgs p2 q, p2.shared_state q⟩ := by
  cases h with
  | downgrade_from_M_rq1 v i j hj =>
      have hc := countP_eraseIdx CPEvent.isRelease _ _ _ hj
      simp [CPEvent.isRelease] at hc
      refine LocalStep.recvRelease' rfl ?_ ?_
      · simp [parentMsgs]; omega
      · exact update_Fin_gss _ _ _
  | upgrade_to_M_data_avilable_rq1 i j hj hall =>
      have hc := countP_eraseIdx CPEvent.isRelease _ _ _ hj
      simp [CPEvent.isRelease] at hc
      refine LocalStep.grant' hall rfl ?_ (hall _) ?_
      · simp [parentMsgs, List.countP_append, PCEvent.isGrant]; omega
      · exact update_Fin_gss _ _ _
  | upgrade_to_M_invalid_all i i' j hj hne =>
      refine LocalStep.stutter' rfl ?_ rfl
      simp [parentMsgs, List.countP_append, PCEvent.isGrant]
  | invalid_all i hi =>
      refine LocalStep.stutter' rfl ?_ rfl
      simp [parentMsgs, List.countP_append, PCEvent.isGrant]

/-! ## Un passo di MI, visto indice per indice -/

theorem synced_msgs {n} {s : MIState n} (hs : synced s) (k : Fin n) :
    cacheMsgs (s.caches k) = parentMsgs s.parent k := by
  obtain ⟨h1, h2⟩ := hs k
  simp [cacheMsgs, parentMsgs, h1, h2]

theorem step_local {n} {s s' : MIState n} {t} (hs : synced s) (h : mi_step_internal s t s') :
    ∃ q, (∀ k, k ≠ q → view s' k = view s k)
      ∧ LocalStep (∀ k, s.parent.shared_state k = Bstate.I) (view s q) (view s' q) := by
  cases h with
  | cache cache' p e hc =>
      refine ⟨p, ?_, ?_⟩
      · intro k hk
        simp [view, update_Fin_gso2 _ _ _ _ hk]
      · simp only [view, update_Fin_gss]
        exact cache_step_local hc _ _
  | parent_upd_queue parent' e q hp =>
      refine ⟨q, ?_, ?_⟩
      · intro k hk
        obtain ⟨_, _, h3⟩ := parent_step_local hp k hk
        simp [view, update_Fin_gso2 _ _ _ _ hk, h3]
      · unfold view
        rw [synced_msgs hs q]
        simp only [update_Fin_gss, cacheMsgs]
        exact parent_step_local' hp _
  | parent_no_queue parent' e i hp =>
      cases hp

theorem synced_step {n} {s s' : MIState n} {t} (hs : synced s) (h : mi_step_internal s t s') :
    synced s' := by
  cases h with
  | cache cache' p e hc =>
      intro k
      by_cases hk : k = p
      · subst hk; simp [update_Fin_gss]
      · obtain ⟨h1, h2⟩ := hs k
        simp [update_Fin_gso2 _ _ _ _ hk, h1, h2]
  | parent_upd_queue parent' e q hp =>
      intro k
      by_cases hk : k = q
      · subst hk; simp [update_Fin_gss]
      · obtain ⟨h1, h2⟩ := hs k
        obtain ⟨h3, h4, _⟩ := parent_step_local hp k hk
        simp [update_Fin_gso2 _ _ _ _ hk, h1, h2, h3, h4]
  | parent_no_queue parent' e i hp =>
      cases hp

/-! ## L'astrazione su una coppia di indici -/

def absV (vi vj : LV) : St :=
  ⟨vi.c, vj.c, vi.d, vj.d, Cnt.ofCount vi.m, Cnt.ofCount vj.m⟩

def abs {n} (i j : Fin n) (s : MIState n) : St := absV (view s i) (view s j)

theorem absV_step_i {allI : Prop} {vi vi' vj : LV} (h : LocalStep allI vi vi') (hj : allI → vj.d = .I) :
    absV vi' vj = absV vi vj ∨ ∃ r, Step r (absV vi vj) (absV vi' vj) := by
  cases h with
  | stutter => exact Or.inl rfl
  | @release m d =>
      right; refine ⟨.release0, ?_⟩
      simpa [absV, Cnt.ofCount_succ] using Step.release0' (s := absV ⟨.M, m, d⟩ vj) rfl
  | @recvGrant k d =>
      right; refine ⟨.recvGrant0, ?_⟩
      exact Step.recvGrant0' (s := absV ⟨.I, k + 1, d⟩ vj) rfl rfl
  | @grant c m hall =>
      right; refine ⟨.grant0, ?_⟩
      simpa [absV, Cnt.ofCount_succ] using Step.grant0' (s := absV ⟨c, m, .I⟩ vj) rfl (hj hall)
  | @recvRelease c k d =>
      right; refine ⟨.recvRelease0, ?_⟩
      exact Step.recvRelease0' (s := absV ⟨c, k + 1, d⟩ vj) rfl

theorem absV_step_j {allI : Prop} {vi vj vj' : LV} (h : LocalStep allI vj vj') (hi : allI → vi.d = .I) :
    absV vi vj' = absV vi vj ∨ ∃ r, Step r (absV vi vj) (absV vi vj') := by
  cases h with
  | stutter => exact Or.inl rfl
  | @release m d =>
      right; refine ⟨.release1, ?_⟩
      simpa [absV, Cnt.ofCount_succ] using Step.release1' (s := absV vi ⟨.M, m, d⟩) rfl
  | @recvGrant k d =>
      right; refine ⟨.recvGrant1, ?_⟩
      exact Step.recvGrant1' (s := absV vi ⟨.I, k + 1, d⟩) rfl rfl
  | @grant c m hall =>
      right; refine ⟨.grant1, ?_⟩
      simpa [absV, Cnt.ofCount_succ] using Step.grant1' (s := absV vi ⟨c, m, .I⟩) (hi hall) rfl
  | @recvRelease c k d =>
      right; refine ⟨.recvRelease1, ?_⟩
      exact Step.recvRelease1' (s := absV vi ⟨c, k + 1, d⟩) rfl

theorem abs_step {n} (i j : Fin n) (hij : i ≠ j) {s s' : MIState n} {t}
    (hs : synced s) (h : mi_step_internal s t s') :
    abs i j s' = abs i j s ∨ ∃ r, Step r (abs i j s) (abs i j s') := by
  obtain ⟨q, hother, hq⟩ := step_local hs h
  unfold abs
  by_cases hqi : q = i
  · subst hqi
    rw [hother j (Ne.symm hij)]
    exact absV_step_i hq (fun hall => by simp [view, hall])
  · by_cases hqj : q = j
    · subst hqj
      rw [hother i hij]
      exact absV_step_j hq (fun hall => by simp [view, hall])
    · rw [hother i (Ne.symm hqi), hother j (Ne.symm hqj)]
      exact Or.inl rfl

/-! ## Trasporto della raggiungibilità -/

theorem reach_abs {n} (i j : Fin n) (hij : i ≠ j) {s0 s : MIState n} (hs0 : synced s0)
    (h : ReflTransGen MI.atrans s0 s) :
    synced s ∧ ReflTransGen miAbs.atrans (abs i j s0) (abs i j s) := by
  induction h with
  | refl => exact ⟨hs0, ReflTransGen.refl⟩
  | tail _ hstep ih =>
      obtain ⟨t, ht⟩ := hstep
      refine ⟨synced_step ih.1 ht, ?_⟩
      rcases abs_step i j hij ih.1 ht with heq | ⟨r, hr⟩
      · rw [heq]; exact ih.2
      · exact ReflTransGen.tail ih.2 (Exists.intro r hr)

theorem synced_default {n} : synced (default : MIState n) := fun _ => ⟨rfl, rfl⟩

theorem abs_default {n} (i j : Fin n) : abs i j (default : MIState n) = initSt := rfl

/-! ## Il teorema su MI -/

/-- `twoCachesM` di MI.lean: due cache distinte entrambe in `M`. -/
def twoCachesM {n} (s : MIState n) : Prop :=
  ∃ i j, i ≠ j ∧ (s.caches i).state = Bstate.M ∧ (s.caches j).state = Bstate.M

theorem twoCachesM_iff {n} (s : MIState n) : twoCachesM s ↔ _root_.twoCachesM s := Iff.rfl

/-- Forma forte: nessuno stato con due cache in `M` è raggiungibile dallo stato
iniziale `default` (tutte le cache in `I`, code vuote). È l'enunciato di
`two_caches_M_not_reachable` in MI.lean, ottenuto qui via `backward_search_all`. -/
theorem twoCachesM_not_reachable_from_default {n} (s : MIState n) (h : twoCachesM s) :
    ¬ ReflTransGen MI.atrans (default : MIState n) s := by
  intro hpath
  obtain ⟨i, j, hij, hi, hj⟩ := h
  have habs := (reach_abs i j hij synced_default hpath).2
  rw [abs_default] at habs
  have hbad : twoCachesM_abs (abs i j s) := And.intro hi hj
  apply twoCachesM_abs_unreachable (abs i j s) hbad
  intro s_init hs_init
  change s_init = initSt at hs_init
  subst hs_init
  exact habs

/-- **Due cache in `M` è irraggiungibile in `MI`**, per ogni `n`: lo stesso
enunciato di `reachable_MI1` in MI.lean, ma dimostrato passando per
`backward_search_all` sul modello astratto. -/
theorem twoCachesM_unreachable {n} : ∀ s : MIState n, twoCachesM s → ¬ MI.reachable s := by
  intro s h hreach
  dsimp [MI.LTS.reachable] at hreach
  exact twoCachesM_not_reachable_from_default s h (hreach (default : MIState n) (by trivial))

#print axioms twoCachesM_unreachable
-- depends on axioms: [propext, Classical.choice, Quot.sound]

end MISim
