/-
// ===== LEADER =====
Leader:
  id: int            // identificatore del leader
  f: int             // numero di fault tollerati
  preferredValue: Value  // valore che preferisce proporre

  receivedPromises: set<AcceptorId>     // da chi ha ricevuto promise
  receivedValue: Value                  // valore che proporrà
  highestHeardBallot: int?              // ballot più alto sentito (null se nessuno)

// ===== ACCEPTOR =====
Acceptor:
  id: int

  pendingPrepare: int?     // prepare ricevuto in attesa di decisione
  promisedBallot: int?     // ballot promesso (nessuno = null)
  accepted: (Value, int)?  // valore e ballot accettato (null se nessuno)

// ===== LEARNER =====
Learner:
  id: int
  f: int

  receivedAccepts: map<(Value, int) → set<AcceptorId>>  // chi ha accettato cosa
  learned: Value?                                        // valore appreso


LEADER
// STEP 1: Send prepare
PrepareStep():
  send Prepare(id)
  // stato non cambia

// STEP 2: Riceve una promise
ReceivePromiseStep(Promise(ballot, accId, vbOpt)):
  if ballot == id and accId not in receivedPromises:
    add accId to receivedPromises

    if vbOpt ≠ null:
      vbBallot, vbValue = vbOpt
      if highestHeardBallot == null or vbBallot > highestHeardBallot:
        highestHeardBallot = vbBallot
        receivedValue = vbValue
    // altrimenti mantieni il valore preferito

// STEP 3: Propone il valore
ProposeStep():
  if |receivedPromises| ≥ f + 1
     and (highestHeardBallot == null or highestHeardBallot < id):
    send Propose(id, receivedValue)
  // stato non cambia

// STEP 4: Stutter (non fa nulla)
StutterStep():
  pass




ACCEPTOR
// STEP 1: Riceve prepare
ReceivePrepareStep(Prepare(ballot)):
  if pendingPrepare == null:
    pendingPrepare = ballot

// STEP 2: Decide se promettere
MaybePromiseStep():
  if pendingPrepare ≠ null:
    ballot = pendingPrepare
    if promisedBallot == null or ballot > promisedBallot:
      promisedBallot = ballot
      send Promise(ballot, id, accepted)  // accepted può essere null
    // in ogni caso resetto pending
    pendingPrepare = null

// STEP 3: Decide se accettare un valore
MaybeAcceptStep(Propose(ballot, value)):
  if pendingPrepare == null:
    if promisedBallot == null or ballot ≥ promisedBallot:
      promisedBallot = ballot
      accepted = (value, ballot)
      send Accept((value, ballot), id)

// STEP 4: Rispedisce accept già fatto
BroadcastAcceptedStep():
  if accepted ≠ null:
    (v, b) = accepted
    if pendingPrepare == null and promisedBallot == b:
      send Accept((v, b), id)

// STEP 5: Stutter
StutterStep():
  pass




LEARNER

// STEP 1: Riceve accept
ReceiveStep(Accept((val, bal), accId)):
  if (val, bal) not in receivedAccepts:
    receivedAccepts[(val, bal)] = {accId}
  else:
    receivedAccepts[(val, bal)] += {accId}

// STEP 2: Impara un valore
LearnStep((val, bal)):
  if (val, bal) in receivedAccepts
     and |receivedAccepts[(val, bal)]| ≥ f + 1:
    learned = val

// STEP 3: Stutter
StutterStep():
  pass

-/



/-
// ===============================================
// LEADER
// ===============================================

Variables:
  receivedPromises: set of acceptor IDs
  receivedValue: value  // inizialmente il valore preferito
  highestHeardBallot: nat or null

// STEP 1: Invia Prepare
PrepareStep():
  send Prepare(myId)

// STEP 2a: Riceve un Promise senza nuovo valore
ReceivePromiseNoUpdate(Promise(ballot, accId, null)):
  if ballot == myId and accId not in receivedPromises:
    receivedPromises.add(accId)

// STEP 2b: Riceve un Promise con nuovo valore
ReceivePromiseUpdate(Promise(ballot, accId, (vbBallot, vbValue))):
  if ballot == myId and accId not in receivedPromises:
    receivedPromises.add(accId)
    if highestHeardBallot == null or vbBallot > highestHeardBallot:
      highestHeardBallot = vbBallot
      receivedValue = vbValue

// STEP 3: Propone il valore
ProposeStep():
  if |receivedPromises| ≥ f + 1
     and (highestHeardBallot == null or highestHeardBallot < myId):
    send Propose(myId, receivedValue)

// ===============================================
// ACCEPTOR
// ===============================================

Variables:
  promisedBallot: nat or null
  accepted: (value, ballot) or null

// STEP 1: Riceve Prepare
ReceivePrepare(Prepare(ballot)):
  if promisedBallot == null or ballot > promisedBallot:
    promisedBallot = ballot
  send Promise(ballot, myId, accepted) // accepted può essere null

// STEP 2: Riceve Propose
ReceivePropose(Propose(ballot, value)):
  if promisedBallot == null or ballot ≥ promisedBallot:
    promisedBallot = ballot
    accepted = (value, ballot)
    send Accept((value, ballot), myId)

// ===============================================
// LEARNER
// ===============================================

Variables:
  receivedAccepts: map from (value, ballot) to set of acceptor IDs
  learned: value or null

// STEP 1: Riceve Accept
ReceiveAccept(Accept((value, ballot), accId)):
  receivedAccepts[(value, ballot)].add(accId)

// STEP 2: Decide valore imparato
LearnStep():
  for each (value, ballot) in receivedAccepts:
    if |receivedAccepts[(value, ballot)]| ≥ f + 1 and learned == null:
      learned = value


-/
