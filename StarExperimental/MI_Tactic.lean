import StarExperimental.Tatic

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

#print axioms twoCachesM_unreachable
-- depends on axioms: [propext, Classical.choice, Quot.sound]

end MIGrantRelease
