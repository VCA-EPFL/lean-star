import StarExperimental.MI

/-!
# Backward search certificata per stati irraggiungibili

Questo file implementa (e dimostra corretta) la procedura descritta a voce:

> partendo da uno stato si va backward di uno step e si aggiungono tutti gli
> stati che si raggiungono a una lista di stati irraggiungibili; se lo stato è
> già nella lista ci si ferma ("fatto centro"); se no si fa l'induzione
> backward di nuovo; se da uno stato non si può andare backward, quel ramo ha
> vinto.

La corrispondenza con il codice:

* "andare backward di uno step"        → `BackModel.pre` (i predecessori di uno stato);
* "la lista di stati irraggiungibili"  → l'accumulatore `visited` di `search`;
* "se è già nella lista si ferma"      → il ramo `if s ∈ visited` di `search`;
* "se non si può andare backward"      → `pre s = []`: il ramo non produce nuova frontiera;
* "ha vinto"                           → `search` restituisce `some U`: `U` è un insieme
  chiuso all'indietro che contiene lo stato di partenza e nessuno stato iniziale,
  quindi lo stato di partenza è irraggiungibile (`search_not_reachable`).

C'è una condizione in più rispetto alla descrizione a voce, necessaria per la
correttezza: se durante la ricerca si incontra uno *stato iniziale* la ricerca
fallisce (`none`), perché in quel caso esiste un cammino in avanti dallo stato
iniziale allo stato di partenza, che quindi è raggiungibile.

Il teorema di chiusura `Closed.mem_of_path` è l'analogo automatico di
`back_reachable_MI` / `back_reachable_twoPC`: lì l'insieme chiuso all'indietro
va inventato a mano (`unreachable_set`), qui lo calcola la ricerca.

La tattica utente è `backward_search modello, stato_iniziale`.

In fondo al file la tattica è dimostrata su `MiniMI`, un'astrazione finita del
protocollo MI di `StarExperimental/MI.lean`.
-/

open THEORY
open Relation

namespace BackwardSearch

/-- Un modello "eseguibile" della parte backward di un `LTS`:

* `pre s` enumera i predecessori di `s` (lo step backward);
* `isInit` decide se uno stato è iniziale;
* `pre_complete` garantisce che `pre` non dimentica nessun predecessore;
* `isInit_complete` garantisce che `isInit` non dimentica nessuno stato iniziale.

Le due condizioni di completezza sono ciò che rende la ricerca un *certificato*:
se `pre` dimenticasse un arco, la "vittoria" della ricerca non proverebbe nulla. -/
structure BackModel {T : Type} (l : LTS T) where
  pre : l.S → List l.S
  isInit : l.S → Bool
  pre_complete : ∀ {p s : l.S}, l.atrans p s → p ∈ pre s
  isInit_complete : ∀ {s : l.S}, l.init s → isInit s = true

variable {T : Type} {l : LTS T} [DecidableEq l.S]

/-- La ricerca backward con worklist.

`visited` è la lista degli stati già dichiarati irraggiungibili, `frontier`
gli stati ancora da esplorare. Per ogni stato `s` della frontiera:

* se `s` è iniziale la ricerca fallisce (`none`): `s` è raggiungibile;
* se `s ∈ visited` il ramo si chiude ("fatto centro") e si prosegue;
* altrimenti `s` entra in `visited` e i suoi predecessori `pre s` entrano in
  frontiera (se `pre s = []`, non si può andare backward: il ramo ha vinto).

Quando la frontiera si svuota la ricerca restituisce `some visited`:
la chiusura all'indietro completa. `fuel` garantisce la terminazione. -/
def search (m : BackModel l) : Nat → List l.S → List l.S → Option (List l.S)
  | 0, _, _ => none
  | _ + 1, visited, [] => some visited
  | fuel + 1, visited, s :: frontier =>
    if m.isInit s then
      none
    else if s ∈ visited then
      search m fuel visited frontier
    else
      search m fuel (s :: visited) (m.pre s ++ frontier)

/-- `U` è un insieme chiuso all'indietro che non contiene stati iniziali:
è la nozione di "insieme di stati irraggiungibili" (cfr. `unreachable_set`). -/
def Closed (m : BackModel l) (U : List l.S) : Prop :=
  ∀ s ∈ U, m.isInit s = false ∧ ∀ p ∈ m.pre s, p ∈ U

/-- Invariante della ricerca: se `search` ha successo con risultato `U`, allora
`U` contiene `visited` e `frontier`, ed è chiuso all'indietro. -/
theorem search_inv (m : BackModel l) :
    ∀ (fuel : Nat) (visited frontier U : List l.S),
      search m fuel visited frontier = some U →
      (∀ s ∈ visited, m.isInit s = false ∧ ∀ p ∈ m.pre s, p ∈ visited ∨ p ∈ frontier) →
      (∀ s ∈ visited, s ∈ U) ∧ (∀ s ∈ frontier, s ∈ U) ∧ Closed m U := by
  intro fuel
  induction fuel with
  | zero =>
    intro visited frontier U h _
    simp [search] at h
  | succ fuel ih =>
    intro visited frontier U h hinv
    cases frontier with
    | nil =>
      simp only [search, Option.some.injEq] at h
      subst h
      refine ⟨fun s hs => hs, by simp, fun s hs => ⟨(hinv s hs).1, fun p hp => ?_⟩⟩
      simpa using (hinv s hs).2 p hp
    | cons s fr =>
      simp only [search] at h
      by_cases hini : m.isInit s = true
      · rw [if_pos hini] at h
        simp at h
      · rw [if_neg hini] at h
        by_cases hmem : s ∈ visited
        · rw [if_pos hmem] at h
          obtain ⟨hvU, hfU, hcl⟩ := ih visited fr U h (fun t ht =>
            ⟨(hinv t ht).1, fun p hp => by
              rcases (hinv t ht).2 p hp with hh | hh
              · exact Or.inl hh
              · rcases List.mem_cons.mp hh with rfl | hh
                · exact Or.inl hmem
                · exact Or.inr hh⟩)
          refine ⟨hvU, fun t ht => ?_, hcl⟩
          rcases List.mem_cons.mp ht with rfl | ht
          · exact hvU _ hmem
          · exact hfU _ ht
        · rw [if_neg hmem] at h
          have hini' : m.isInit s = false := by simpa using hini
          have hinv' : ∀ t ∈ s :: visited,
              m.isInit t = false ∧
                ∀ p ∈ m.pre t, p ∈ s :: visited ∨ p ∈ m.pre s ++ fr := by
            intro t ht
            rcases List.mem_cons.mp ht with rfl | ht
            · exact ⟨hini', fun p hp => Or.inr (List.mem_append.mpr (Or.inl hp))⟩
            · refine ⟨(hinv t ht).1, fun p hp => ?_⟩
              rcases (hinv t ht).2 p hp with hh | hh
              · exact Or.inl (List.mem_cons.mpr (Or.inr hh))
              · rcases List.mem_cons.mp hh with rfl | hh
                · exact Or.inl (List.mem_cons.mpr (Or.inl rfl))
                · exact Or.inr (List.mem_append.mpr (Or.inr hh))
          obtain ⟨hvU, hfU, hcl⟩ := ih (s :: visited) (m.pre s ++ fr) U h hinv'
          refine ⟨fun t ht => hvU _ (List.mem_cons.mpr (Or.inr ht)), fun t ht => ?_, hcl⟩
          rcases List.mem_cons.mp ht with rfl | ht
          · exact hvU _ (List.mem_cons.mpr (Or.inl rfl))
          · exact hfU _ (List.mem_append.mpr (Or.inr ht))

omit [DecidableEq l.S] in
/-- L'"induzione backward": un insieme chiuso all'indietro assorbe ogni cammino.
Se `x →* s` e `s ∈ U`, risalendo il cammino un passo alla volta (usando la
completezza di `pre`) anche `x ∈ U`. È l'analogo di `back_reachable_MI`. -/
theorem Closed.mem_of_path {m : BackModel l} {U : List l.S} (hU : Closed m U)
    {s x : l.S} (hpath : l.backwards_reachable_from s x) : s ∈ U → x ∈ U := by
  dsimp [LTS.backwards_reachable_from] at hpath
  induction hpath using ReflTransGen.head_induction_on with
  | refl => exact id
  | @head a c h1 h2 h3 =>
    intro ha
    dsimp [Function.swap] at h1
    exact h3 ((hU _ ha).2 _ (m.pre_complete h1))

/-- Se la ricerca partita da `s₀` ha successo, `s₀` non è raggiungibile
all'indietro da nessuno stato iniziale. -/
theorem search_not_reachable_from (m : BackModel l) {fuel : Nat} {s₀ : l.S}
    {U : List l.S} (h : search m fuel [] [s₀] = some U)
    {s_init : l.S} (hinit : l.init s_init) :
    ¬ l.backwards_reachable_from s₀ s_init := by
  intro hpath
  obtain ⟨-, hfr, hcl⟩ := search_inv m fuel [] [s₀] U h (by simp)
  have hs₀ : s₀ ∈ U := hfr s₀ (by simp)
  have hin : s_init ∈ U := hcl.mem_of_path hpath hs₀
  have h1 : m.isInit s_init = false := (hcl s_init hin).1
  have h2 : m.isInit s_init = true := m.isInit_complete hinit
  simp [h1] at h2

/-- Il teorema finale, nella forma usata da `reachable_twoPC` / `reachable_MI`:
se la ricerca backward da `s₀` ha successo (`isSome`), `s₀` non è raggiungibile.
Serve esibire almeno uno stato iniziale (`s_init`), come in `reachable_twoPC`. -/
theorem search_not_reachable (m : BackModel l) {fuel : Nat} {s₀ : l.S}
    (h : (search m fuel [] [s₀]).isSome = true)
    (s_init : l.S) (hinit : l.init s_init) :
    ¬ l.reachable s₀ := by
  intro hreach
  cases hU : search m fuel [] [s₀] with
  | none => rw [hU] at h; simp at h
  | some U =>
    exact search_not_reachable_from m hU hinit
      (backwards_reachable_not_init.mpr hreach s_init hinit)

end BackwardSearch

/-- La tattica: `backward_search m, s_init` dimostra `¬ l.reachable s` facendo
girare la ricerca backward del modello `m` a partire da `s` (per riflessione:
il lato computazionale è scaricato con `decide`). `s_init` è un testimone che
gli stati iniziali esistono. -/
macro "backward_search" m:term ", " s0:term : tactic =>
  `(tactic| exact BackwardSearch.search_not_reachable $m (fuel := 64)
      (by decide) $s0 (by first | decide | rfl | simp))

/-- Variante con fuel esplicito: `backward_search m, s_init, 512`. -/
macro "backward_search" m:term ", " s0:term ", " f:term : tactic =>
  `(tactic| exact BackwardSearch.search_not_reachable $m (fuel := $f)
      (by decide) $s0 (by first | decide | rfl | simp))


/-!
# Esempio: MiniMI, un'astrazione finita del protocollo MI

`MIState n` di `StarExperimental/MI.lean` è infinito (valori `Nat`, code
illimitate), quindi non si può esplorare per enumerazione. `MiniMI` ne tiene il
cuore booleano con 2 cache:

* `c0`, `c1`  ↔ `(s.caches i).state`          (lo stato M/I delle cache);
* `d0`, `d1`  ↔ `s.parent.shared_state i`     (la directory del parent);
* `grant i`   ↔ `upgrade_to_M_data_avilable_rq1` (il parent concede `M` solo se
  tutta la directory è `I`);
* `wb i`      ↔ `rq_data_not_available` + `downgrade_from_M_rq1` (la cache
  rilascia la linea e il parent aggiorna la directory), fusi in un passo solo
  perché qui non ci sono code.
-/

deriving instance DecidableEq for Bstate

namespace MiniMI

open BackwardSearch

structure MiniState where
  c0 : Bstate
  c1 : Bstate
  d0 : Bstate
  d1 : Bstate
deriving DecidableEq, Repr

inductive MiniRule where
  | grant0 | grant1 | wb0 | wb1
deriving DecidableEq, Repr

inductive MiniStep : MiniRule → MiniState → MiniState → Prop where
  | grant0 {s : MiniState} :
      s.c0 = .I → s.d0 = .I → s.d1 = .I →
      MiniStep .grant0 s { s with c0 := .M, d0 := .M }
  | grant1 {s : MiniState} :
      s.c1 = .I → s.d0 = .I → s.d1 = .I →
      MiniStep .grant1 s { s with c1 := .M, d1 := .M }
  | wb0 {s : MiniState} :
      s.c0 = .M →
      MiniStep .wb0 s { s with c0 := .I, d0 := .I }
  | wb1 {s : MiniState} :
      s.c1 = .M →
      MiniStep .wb1 s { s with c1 := .I, d1 := .I }

def initState : MiniState := ⟨.I, .I, .I, .I⟩

@[reducible] def miniMI : LTS MiniRule where
  S := MiniState
  transitions := MiniStep
  init s := s = initState
  flushed _ := True

/-- Lo step backward: i predecessori di `s`, per ispezione delle quattro regole.

* un `grant i` è arrivato in `s` se `c i = M`, `d i = M` e l'altra directory è
  `I`: il predecessore aveva `c i = I`, `d i = I`;
* un `wb i` è arrivato in `s` se `c i = I` e `d i = I`: il predecessore aveva
  `c i = M` e la *sua* `d i` è libera (il writeback la sovrascrive), quindi i
  predecessori sono due, uno per ciascun valore di `d i`. -/
def miniPre (s : MiniState) : List MiniState :=
  (if s.c0 = .M ∧ s.d0 = .M ∧ s.d1 = .I then [{ s with c0 := .I, d0 := .I }] else []) ++
  (if s.c1 = .M ∧ s.d1 = .M ∧ s.d0 = .I then [{ s with c1 := .I, d1 := .I }] else []) ++
  (if s.c0 = .I ∧ s.d0 = .I then
    [{ s with c0 := .M, d0 := .M }, { s with c0 := .M, d0 := .I }] else []) ++
  (if s.c1 = .I ∧ s.d1 = .I then
    [{ s with c1 := .M, d1 := .M }, { s with c1 := .M, d1 := .I }] else [])

/-- `miniPre` non dimentica nessun predecessore (per forza bruta sui 16 stati). -/
theorem miniPre_complete {p s : MiniState} (h : ∃ r, MiniStep r p s) : p ∈ miniPre s := by
  obtain ⟨r, h⟩ := h
  obtain ⟨c0, c1, d0, d1⟩ := p
  cases c0 <;> cases c1 <;> cases d0 <;> cases d1 <;>
    cases h <;> first | decide | simp_all

def miniModel : BackModel miniMI where
  pre := miniPre
  isInit s := decide (s = initState)
  pre_complete := fun h => miniPre_complete h
  isInit_complete := fun h => decide_eq_true h

/-!
## Le dimostrazioni

`bad1`: due cache contemporaneamente in `M` (la violazione di mutua esclusione,
cfr. `unreachable_set1` in MI.lean). La ricerca fa esattamente i passi
descritti a voce:

    frontier = [⟨M,M,M,I⟩]                        visited = []
    ⟨M,M,M,I⟩ nuovo, pre = [⟨I,M,I,I⟩]            visited = [⟨M,M,M,I⟩]
    ⟨I,M,I,I⟩ nuovo, pre = [⟨M,M,M,I⟩, ⟨M,M,I,I⟩] visited = [⟨I,M,I,I⟩, …]
    ⟨M,M,M,I⟩ già in lista → fatto centro
    ⟨M,M,I,I⟩ nuovo, pre = [] → non si può andare backward: vinto
    frontier vuota → some [⟨M,M,I,I⟩, ⟨I,M,I,I⟩, ⟨M,M,M,I⟩]

Si noti lo stato intermedio `⟨I,M,I,I⟩`: nessuna coppia di cache in `M`, ma
`c1 = M` con `d1 = I` — esattamente il tipo di stato "in volo" che in MI.lean
aveva reso `unreachable_set1` non chiuso all'indietro (`back_reachable_MI1`).
Qui la ricerca lo scopre e lo aggiunge alla lista da sola.
-/

def bad1 : MiniState := ⟨.M, .M, .M, .I⟩

/-- Due cache in `M`: irraggiungibile, via ricerca backward. -/
theorem bad1_not_reachable : ¬ miniMI.reachable bad1 := by
  backward_search miniModel, initState

/-- `bad2`: la cache 0 possiede `M` ma la directory dice `I`. Qui il "fatto
centro" avviene proprio sullo stato di partenza (ciclo backward su di esso). -/
def bad2 : MiniState := ⟨.M, .I, .I, .I⟩

theorem bad2_not_reachable : ¬ miniMI.reachable bad2 := by
  backward_search miniModel, initState

/-- `bad3`: tutto a `M`. Nessun predecessore: la ricerca vince al primo colpo. -/
def bad3 : MiniState := ⟨.M, .M, .M, .M⟩

theorem bad3_not_reachable : ¬ miniMI.reachable bad3 := by
  backward_search miniModel, initState

-- La chiusura calcolata dalla ricerca per `bad1` (la "lista di stati
-- irraggiungibili" costruita automaticamente):
#eval BackwardSearch.search miniModel 64 [] [bad1]
-- some [⟨M,M,I,I⟩, ⟨I,M,I,I⟩, ⟨M,M,M,I⟩]

#eval BackwardSearch.search miniModel 64 [] [bad2]
-- some [⟨M,M,I,I⟩, ⟨M,M,I,M⟩, ⟨M,I,I,I⟩]

/-! ## Controprova: su uno stato raggiungibile la ricerca fallisce -/

/-- `good`: la cache 0 possiede la linea e la directory è d'accordo. -/
def good : MiniState := ⟨.M, .I, .M, .I⟩

-- Andando backward da `good` si incontra lo stato iniziale → `none`:
#eval BackwardSearch.search miniModel 64 [] [good]
#guard (BackwardSearch.search miniModel 64 [] [good]).isNone

-- ... e infatti `good` è davvero raggiungibile (un solo `grant0` dallo stato
-- iniziale):
theorem good_reachable : miniMI.reachable good := by
  intro s_init hinit
  have hs : s_init = initState := hinit
  subst hs
  apply ReflTransGen.single
  exact ⟨.grant0, .grant0 rfl rfl rfl⟩

-- Sanity check compile-time: le tre ricerche cattive vincono.
#guard (BackwardSearch.search miniModel 64 [] [bad1]).isSome
#guard (BackwardSearch.search miniModel 64 [] [bad2]).isSome
#guard (BackwardSearch.search miniModel 64 [] [bad3]).isSome

end MiniMI
