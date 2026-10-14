import StarExperimental.MSI_trial
import StarExperimental.MSI_trial_flush
import StarExperimental.MSI_trial_commute

/-!
# `MSI_trial`: trace inclusion con `ReachingStar.trace_inclusion`

Le sei ipotesi di `ReachingStar.trace_inclusion` per `MSI_trial`:

| ipotesi | dove |
|---|---|
| `relation_flush`, `relation_flush_method_int`, `relation_method_int`, `relation_init` | `MSI_trial_flush.lean` (relazione conservata da ogni passo interno: zero passi) |
| `has_diamond_property_on` | `MSI_trial.lean` (diagrammi decrescenti, 153 picchi locali) |
| `commutes_method_rule_upto_on` | `MSI_trial_commute.lean` (stato canonico: `MSI_trial_canon.lean`, svuotamento `MSI_trial_drain1/2.lean`) |

Il teorema finale applica `ReachingStar.trace_inclusion` alla lettera.
-/

open THEORY Relation MSIView
open ReachingStar (trans_refl has_diamond_property_on commutes_method_rule_upto_on)

namespace MSITrial

variable {n : Nat}

/-- **Trace inclusion di `MSI_trial`** rispetto allo spec sequenziale `seq_step`, tramite
`ReachingStar.trace_inclusion`. -/
theorem trace_inclusion (l : List (MSIExternalEvent n)) :
    ReachingStar.imp_behaviour (rule n) msi_step_external l (default : MSIState n) →
    ReachingStar.spec_behaviour seq_step l (seq_init n) :=
  ReachingStar.trace_inclusion flush (rule n) msi_step_external seq_step l (default : MSIState n)
    (seq_init n) trial_relation_flush trial_relation_flush_method_int trial_relation_method_int
    msi_trial_confluent msi_trial_commutes_upto trial_relation_init

end MSITrial
