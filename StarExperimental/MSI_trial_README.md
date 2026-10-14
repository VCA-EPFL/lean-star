# `MSI_trial`: confluenza senza terminazione, con i diagrammi decrescenti

Resoconto del lavoro del 6–7 ottobre 2026. Obiettivo: un modello MSI **non terminante** per cui
`has_diamond_property_on` si dimostra con i soli diamanti locali e il teorema dei diagrammi
decrescenti, senza invarianti scritti a mano, e poi la trace inclusion con le ipotesi di ARS.

## Risultato

```
MSITrial.msi_trial_confluent :
  ∀ {n}, has_diamond_property_on MSITrial.Reach (trans_refl (MSITrial.rule n))      -- dimostrato
MSITrial.trace_inclusion (l) :
  imp_behaviour (rule n) msi_step_external l default → spec_behaviour seq_step l (seq_init n)   -- dimostrato
```

Assiomi di entrambi: `propext`, `Classical.choice`, `Quot.sound`. Nessun `sorry` in tutto il
development (verificato il 7 ottobre 2026).

## Il teorema dei diagrammi decrescenti — `DecreasingDiagrams.lean`

`has_diamond_property_on_of_decreasing : Decreasing R step → has_diamond_property_on R (trans_refl (rule step))`
per `step : Nat → A → A → Prop` (passi etichettati da naturali) e `R` chiuso per passi.
Versione **lineare stretta** di van Oostrom: con `α ≤ β` il lato piccolo fa al più un passo `= β`
*subito* e poi solo passi `< β`, il lato grande solo passi `< β`; con `α = β` entrambi un passo
grande (`big`: `(<k)* · k? · (<k)*`). Dimostrazione elementare: induzione sull'etichetta massima,
il passo grande si spinge attraverso le catene di passi piccoli senza moltiplicarsi perché è il
primo (`pushK`). 391 righe, zero `sorry`. Non è il teorema generale (ordine ben fondato qualunque,
passi piccoli davanti): l'audit dei diamanti di MSI mostra che la versione stretta basta.

## Il modello — `MSI_trial_def.lean`

`MSI_def` con tre modifiche, tutte sulla cache; il parent è riusato tale e quale.

1. **Una richiesta per volta**: `upgrade_from_I_rq`/`rqS` solo con `¬ pending` (niente `rqM`/`rqS`
   già in `queue_cp`) e `¬ grantInFlight` (niente `rsM`/`rsS` in volo).
2. **Del tipo richiesto dal programma**: `rqM` solo con una store in testa (`wantsM`), `rqS` solo con
   una load (`wantsS`). Il *momento* resta spontaneo; i rilasci restano spontanei: il modello non
   termina.
3. **Scarto degli invalidate stantii**: una cache in `I` scarta un `rqIμ`/`rqIσ` (`drop_rqIμ`,
   `drop_rqIσ`), etichetta 0.

Perché: in `MSI.lean` 17 dei 120 picchi interni si chiudevano solo "a meno di" un messaggio
(`invMSt`, `dropSt`, `reqMSt`, `.caches`) o richiedevano cammini con richieste/invalidate dentro, che
nessuna etichettatura rende decrescenti. Con (1) i picchi "richiesta / presa del grant" sono vuoti;
con (2) il picco "`rqM` / `rqS` della stessa cache" è vuoto (il suo ricongiungimento avrebbe richiesto
di sgomberare tutta la directory); con (3) gli 11 picchi "a meno di un invalidate" chiudono in un
passo. Scartata l'alternativa "il parent cancella le richieste doppie": crea un picco non decrescente.

Etichette: richiesta 7 > invalidate 6 > grant 4 > presa del grant 3 > rilascio/risposta a invalidate 2
> consumo del rilascio 1 > scarto 0. Le richieste in cima perché compaiono nei ricongiungimenti solo
come ripetizione del passo del picco.

Raggiungibilità: `Reach` di ARS (da `default`, passi interni **ed esterni**). Nota: `MSI.reachable`
di `MSI_def` è a soli passi interni, quindi `¬ MSI.reachable s` vale per ogni stato con `extqueue`
non vuota o valori ≠ 0: le uscite dei 185 `comm_*` di `MSI.lean` sono vuote su quegli stati (le
dimostrazioni usano solo le viste, quindi gli enunciati "giusti" sono veri, ma non è ciò che è
scritto).

## I fatti sugli stati raggiungibili

* `MSI_trial_views.lean`: la tattica backward di `MSI.lean` sul setup di `MSI_trial` con
  `trans := step_any` (interni + esterni): 453 viste di partenza, chiusura 453, 2062 passi (gli stessi
  numeri del vecchio modello), 41 min, 3 GB. `badView_unreachable : (∃ i j, badView (msiView s i j)) → ¬ Reach s`.
  Trappola trovata: la tattica inverte le ipotesi per **nome della costante in testa**; un `abbrev`
  (`step_ext`) nel tipo di un costruttore non viene invertito e ogni vista riceve 81 predecessori.
* `MSI_trial_bridge.lean`: i 13 lemmi ponte di `MSI.lean` con conclusione `¬ Reach s`.
* `synced_of_reach`: le due copie delle code coincidono (artefatto dell'encoding).
* `MSI_trial_views15.lean` (in corso): `badView` + i pattern 14–15 "riga registrata senza
  portatore", per il lemma di progresso.

## I picchi locali — 153 + 1

| file | contenuto |
|---|---|
| `MSI_trial_old_{pp,cc,pc1,pc2}.lean` | copie testuali dei 120 `comm_*` di `MSI.lean` con conclusione `¬ Reach s` (`old_*`) |
| `MSI_trial_lift.lean` | `step_int_old` (nuovo ⇒ vecchio, salvo scarti), `step_int_of_old_*` (vecchio ⇒ nuovo, richieste con guardia), `req_guard_preserved` |
| `MSI_trial_dec.lean` | `DecJoin α β b c`: la forma richiesta dal teorema, con i costruttori `square`, `of_eq`, `absorb`, `top`, `mix`, `mix'`, `symm` |
| `MSI_trial_peaks_lift.lean` | 74 quadrati sollevati automaticamente (generati) |
| `MSI_trial_peaks_req.lean` | 24 picchi con una richiesta: 10 vuoti/identici, 14 quadrati con la guardia trasportata |
| `MSI_trial_peaks_long.lean` | 5 picchi con cammini lunghi (grant/grant 7+7, grant S/invalidate S 2+2, consumo/grant S 4+4) |
| `MSI_trial_peaks_new.lean` | i 17 riscritti: scarto in un passo, vuoti, o uscite per irraggiungibilità |
| `MSI_trial_peaks_dropA/B.lean` | 33 picchi con lo scarto: quadrati, vuoti, 4 ricongiungimenti a 3 passi |
| `MSI_trial_peaks_ne.lean` | `peak_cache_ne`: due passi di cache su indici diversi commutano |
| `MSI_trial.lean` | `local_peak` (smistamento generato su tutte le coppie di eventi), `decreasing`, `msi_trial_confluent` |

Le uscite usano solo `badView_unreachable` (13 pattern) e `¬ synced`.

## La relazione di flush — `MSI_trial_flush.lean`

La stessa di `MSI_final`: `Reach i ∧ extqueue uguali ∧ cinque clausole sul valore` (cache in `S`/`M`,
`rsM`, `rsS`, `rsIμ` in volo, parent quando nessuna riga è `M`: tutti uguali a `s.memory`). Nessuna
condizione di forma; conservata da ogni passo interno, quindi `relation_flush`, `relation_method_int`,
`relation_flush_method_int` valgono con `i'' := i'`. Viste usate solo in `st_rq_M_state` (sei fatti) e
in un caso di `downgrade_from_S_rq1S`. Lo spec `SeqState`/`seq_step` è copiato letteralmente in
`MSI_trial_spec.lean` perché `MSI_flush_proof.lean` e `MSI.lean` definiscono entrambi `isRequest`.

## `commutes_method_rule_upto_on` — lo stato canonico

In `MSI_final` sarebbe un quadrato (nessun passo interno toglie la linea a chi ha una richiesta
pendente). In `MSI_trial` i rilasci spontanei disabilitano il metodo: dopo passi interni qualsiasi la
cache deve **riprendere la linea** e servire con lo stesso valore, e i risultati devono ricongiungersi.
Si passa per uno stato canonico (`MSI_trial_canon.lean`):

* `active x j` := la cache tiene la linea, o ha una richiesta/grant in volo, o ha una richiesta del
  programma in testa (un rilascio in volo non conta: chi ha rilasciato ha già il valore giusto);
* `canon x m` := tutte le cache in `I`, nessun messaggio, righe `I`, parent `m`, `extqueue` di `x`,
  valore `m` per le cache attive e quello di `x` per le altre;
* `canon_step`: invariante lungo i passi interni (solo con le clausole di `flush`);
* `reach_canon` (svuotamento, `MSI_trial_drain1/2.lean`): tappa 1 rilasci/prese/consumi con misura
  pesata, righe a `I` per i pattern 14–15 (`MSI_trial_views15.lean`, tattica con 15 viste: 462 viste,
  chiusura 462, 2081 passi); tappa 2 scarto degli invalidate; tappa 3 ogni richiesta in volo viene
  servita (grant, presa, rilascio, consumo); tappa 4 ogni cache con una richiesta del programma in
  testa acquisisce la linea e prende `m`; `canon_of_drained`: lo stato in fondo è `canon x m`;
* `acquire_S`/`acquire_M` (`MSI_trial_commute.lean`): dal canonico la cache prende la linea in tre
  passi e può tornare al canonico; `step_int_enqueue`: i passi interni commutano con l'accodamento;
* `msi_trial_commutes_upto`: accodamenti → ripercorrere il cammino; load/store → `j := canon c m`
  (nuovo valore logico per la store), con `canon d m = canon c m` da `canon_ext`.

Fatti sugli stati raggiungibili usati, oltre alle viste e a `flush`: `demandOK` (quattro clausole
sulle richieste rispetto alla coda del programma: una richiesta/grant in volo ha ancora la sua
load/store in testa; chi tiene la linea non ha richieste né grant in volo; mai richiesta e grant
insieme; al più una richiesta per cache). Le viste non vedono la `extqueue`, quindi questi sono
dimostrati per induzione sulla raggiungibilità (`demandOK_of_reach`); servono nel ricongiungimento
dopo una store (una cache con una richiesta parcheggiata deve ancora avere la sua richiesta del
programma, altrimenti i due lati del diamante assegnerebbero valori diversi) e in fondo allo
svuotamento.

## Compilazione

Da repo root, senza `lake` (il lock può essere tenuto da altre sessioni):
```
LP="$(ls -d .lake/packages/*/.lake/build/lib/lean | tr '\n' ':').lake/build/lib/lean"
LEAN_PATH="$LP" ~/.elan/toolchains/leanprover--lean4---v4.29.0/bin/lean StarExperimental/MSI_trial.lean
```
Ordine: `DecreasingDiagrams`, `MSI_trial_def`, `MSI_trial_views` (41 min), `MSI_trial_bridge`,
`MSI_trial_lift`, `MSI_trial_dec`, `MSI_trial_old_*` (2–8 min ciascuno), `MSI_trial_peaks_*`,
`MSI_trial`, `MSI_trial_spec`, `MSI_trial_flush`, `MSI_trial_views15` (~40 min), `MSI_trial_canon`,
`MSI_trial_drain1`, `MSI_trial_drain2`, `MSI_trial_commute`, `MSI_trial_trace`. Tutti registrati nel
lakefile.
