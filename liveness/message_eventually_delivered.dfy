// If every message that happens before m has been delivered, m is deliverable by n'
lemma {:isolate_assertions} MessageEventuallyDelivered(trace: Trace, schedule: Schedule, m: Message, n: nat)
  returns (n':nat)
  requires FairSchedule(schedule)
  requires IsTrace(trace, schedule)
  requires m.Unicast? && ValidUnicast(m)
  requires Valid(trace(n))
  requires (forall n : nat :: Valid(trace(n)))
  requires m in trace(n).arrived[(m.src, m.dst)] + trace(n).inTransit[(m.src, m.dst)] + trace(n).delivered[(m.src, m.dst)]
  requires forall m':Message | m'.Unicast? && ValidUnicast(m') && ((m' in trace(n).inTransit[(m'.src, m'.dst)] || m' in trace(n).arrived[(m'.src, m'.dst)] || m' in trace(n).delivered[(m'.src, m'.dst)]))
                               && HappensBefore(m', m) :: m' in trace(n).delivered[(m'.src, m'.dst)]
  ensures Valid(trace(n'))
  ensures m in trace(n').delivered[(m.src, m.dst)]
  ensures n' >= n
{
  n' := n;

  if(m in trace(n).inTransit[(m.src, m.dst)]){
    /* Arrive */
    n' := MessageArrival(trace, schedule, m.src, m.dst, n, m); // eventually message m must arrive
    assert m in trace(n').arrived[(m.src, m.dst)];
  }

  assert !(m in trace(n').inTransit[(m.src, m.dst)]);

  if(m in trace(n').arrived[(m.src, m.dst)])
  {

    var rows := P - {m.src};

    // Loop over each row in deliveredMCs and find the n' where the row is large enough
    while(rows != {})
      invariant forall row | row in P - rows - {m.src} :: m.payload.0[row] <= trace(n').deliveredMCs[(m.dst, row)]
      invariant n' >= n
    {
      var row :| row in rows;
      // If it is currently too small, deliver any minicasts at the front of the row until we are done or hit a concurrent message
      if(m.payload.0[row] < trace(n').deliveredMCs[(m.dst, row)]){
        // Loop through minicasts until we find a concurrent message. If we find one, it's value at row must be 1 larger than current deliveredMCs
        // because it is at the front of the queue
        // It's value at row must also be bigger than m.payload.0[row] (by definition of concurrent)
        // So, the value of deliveredMCs must be equal to m.payload.0[row]
        // while(|trace(n').arrived[(m.src, row)]| > 0 && trace(n').arrived[(m.src, row)][0].Minicast? && m.payload.0[row] <= trace(n').deliveredMCs[(m.dst, row)])
        // {

        // }

      }

      rows := rows - {row};

      assume {:axiom} m.payload.0[row] <= trace(n').deliveredMCs[(m.dst, row)];
    }

    assert LessThanEqSrc(m.payload.0, getPVectorFromMap(trace(n').deliveredMCs, P, m.dst), m.src);

    var n_del := messageDelivery(trace, schedule, m.src, m.dst, n', m); // eventually message m must be delivered
    assert m in trace(n_del+1).delivered[(m.src, m.dst)];
    n' := n_del + 1;

  } else {
    assert m in trace(n').delivered[(m.src, m.dst)];
  }
  assert m in trace(n').delivered[(m.src, m.dst)];
}

// Prove that if a message from src is at the front of a queue, m.MCs[src] must be exactly one more than deliveredMCs[src]
lemma FrontMessageIsOneMoreThanDMC(trace: Trace, n: nat, m: Message)
  requires m.Unicast? && ValidUnicast(m)
  requires Valid(trace(n))
  requires |trace(n).arrived[(m.src, m.dst)]| > 0 && m == trace(n).arrived[(m.src, m.dst)][0]
  requires MessagesInQueueIncrementAtSrc(trace, n, m.src, m.dst)
  ensures trace(n).deliveredMCs[(m.dst, m.src)] == 1 + m.payload.0[m.src]
{
  assert Valid(trace(n));
  assert m.src in P && m.dst in P;
  assert ValidMessage(m);
  var length := |trace(n).delivered[(m.src, m.dst)]|-1;
  if(length >= 0){
    var lastMsg := trace(n).delivered[(m.src, m.dst)][length];
    assume {:axiom} trace(n).deliveredMCs[(m.dst, m.src)] == MsgNum(lastMsg);
  } else {
    assume {:axiom} trace(n).deliveredMCs[(m.dst, m.src)] == 0;
  }
  assume {:axiom} trace(n).deliveredMCs[(m.dst, m.src)] == 1 + m.payload.0[m.src];

  // TODO make both axioms predicates
}

lemma messageDelivery(trace: Trace, schedule: Schedule, p: Process, q: Process, i: nat, m: Message)
  returns (result: nat)
  requires forall i: nat :: Valid(trace(i))
  requires FairSchedule(schedule)
  requires IsTrace(trace, schedule)
  requires p in P && q in P
  requires m in trace(i).arrived[(p,q)]
  requires m.Unicast? && ValidUnicast(m)
  requires LessThanEqSrc(m.payload.0, getPVectorFromMap(trace(i).deliveredMCs, P, m.dst), m.src)
  ensures exists j : nat :: j >= i && |trace(j).arrived[(p,q)]| > 0 && trace(j).arrived[(p,q)][0] == m
  ensures result >= i && m in trace(result+1).delivered[(p,q)]
  ensures schedule(result).0 == deliver
{
  assert |trace(i).arrived[(p,q)]| > 0;
  var j:nat;
  j := i;
  while trace(j).arrived[(p,q)][0] != m
    invariant m in trace(j).arrived[(p,q)]
    invariant j >= i
    decreases IndexOf(trace(j).arrived[(p,q)], m)
  {
    assert m in trace(j).arrived[(p,q)];
    assert IndexOf(trace(j).arrived[(p,q)], m) > 0;
    var metric := IndexOf(trace(j).arrived[(p,q)], m);

    var j_deliver := GetNextDelivery(trace, schedule, p, q, j);
    assert IndexOf(trace(j_deliver).arrived[(p,q)], m) > 0;
    assert schedule(j_deliver).0 == deliver;
    assert m in trace(j_deliver).arrived[(p,q)];
    assert Deliver(trace(j_deliver), (deliver, p, q), trace(j_deliver+1));
    assert |trace(j_deliver).arrived[(p,q)]| == |trace(j_deliver+1).arrived[(p,q)]| +1;
    assert IndexOf(trace(j_deliver).arrived[(p,q)], m) > IndexOf(trace(j_deliver+1).arrived[(p,q)], m);

    j := j_deliver+1;

    assert IndexOf(trace(j).arrived[(p,q)], m) < metric;
  }
  // Now that m is at the front of arrived, get the delivery of m (next delivery)
  assert trace(j).arrived[(p,q)][0] == m;
  var deliverj := GetNextDelivery(trace, schedule, p, q, j);
  assert trace(deliverj + 1).arrived == trace(deliverj).arrived[(p,q) := trace(deliverj).arrived[(p,q)][1..]];
  assert trace(deliverj).arrived[(p,q)][0] == m;
  assert trace(deliverj + 1).delivered == trace(deliverj).delivered[(p,q) := trace(deliverj).delivered[(p,q)] + [trace(deliverj).arrived[(p,q)][0]]];
  assert trace(deliverj + 1).delivered[(p,q)][|trace(deliverj + 1).delivered[(p,q)]|-1] == m;
  assert m in trace(deliverj + 1).delivered[(p,q)];
  assert deliverj + 1 > i;
  result := deliverj;
}

// Get the n' >= n where the event choice at n' is a delivery from p to q
lemma GetNextDelivery(trace: Trace, schedule: Schedule, p: Process, q: Process, n: nat)
  returns (n': nat)
  requires p in P && q in P
  requires FairSchedule(schedule)
  requires IsTrace(trace, schedule)
  ensures n <= n' && schedule(n') == (deliver, p, q)
  ensures trace(n).arrived[(p,q)] <= trace(n').arrived[(p,q)]
{
  var e := (deliver, p, q);
  assert HasNext(schedule, e, n+1);
  var u :| n < u && schedule(u) == e;
  n' := n;
  assert trace(n).arrived[(p,q)] <= trace(n').arrived[(p,q)];

  while schedule(n') != e
    invariant n' <= u
    invariant trace(n).arrived[(p,q)] <= trace(n').arrived[(p,q)]
    invariant n <= n'
    decreases u - n'
  {
    assert schedule(n') != e;
    n' := n' + 1;
  }

  assert trace(n).arrived[(p,q)] <= trace(n').arrived[(p,q)];
}

ghost predicate MaxDeliveredMCsatP(trace: Trace)
  requires forall n: nat :: Valid(trace(n))
  {
    && (forall n:nat, src <- P, dst <- P :: Valid(trace(n)) && InTransitInOrder(trace, n, src, dst))
    && (forall n:nat, src <- P, dst <- P :: ArrivedInOrder(trace, n, src, dst))
    && (forall n:nat, src <- P, dst <- P :: DeliveredInOrder(trace, n, src, dst))
    && (forall n:nat, src <- P, dst <- P :: ChannelsAreDisjoint(trace, n))
    && (forall n:nat, src <- P, dst <- P :: MessagesInQueueIncrementAtSrc(trace, n, src, dst))
    && (forall n:nat, p <- P, m:Message | m.Minicast? :: trace(n).deliveredMCs[(p,p)] > m.msgNum)
    && (forall n:nat, p <- P, m: Message | m.Unicast? && ValidUnicast(m) ::
      trace(n).deliveredMCs[(p,p)] > m.payload.0[p])
    && (forall n:nat, p <- P, q <- P | p != q :: trace(n).deliveredMCs[(p,p)] > trace(n).deliveredMCs[(q, p)])
    && (forall n:nat, q <- P, m: Message | m.Unicast? && ValidUnicast(m) && q != m.src && m in trace(n).arrived[(m.src, m.dst)] ::
      m.payload.0[m.src] > trace(n).deliveredMCs[(q, m.src)])
    && (forall n:nat, q <- P, m: Message | m.Unicast? && ValidUnicast(m) && q != m.src && m in trace(n).inTransit[(m.src, m.dst)] ::
      m.payload.0[m.src] > trace(n).deliveredMCs[(q, m.src)])
  }

  ghost predicate DeliveredInOrder(trace: Trace, n:nat, src: Process, dst: Process)
  requires forall n: nat :: Valid(trace(n))
  requires Valid(trace(n))
  requires src in P && dst in P
  {
    && (forall i:nat | i < |trace(n).delivered[(src, dst)]| -1 :: MsgNum(trace(n).delivered[(src, dst)][i]) < MsgNum(trace(n).delivered[(src, dst)][i+1]))
  }

  ghost predicate ArrivedInOrder(trace: Trace, n:nat, src: Process, dst: Process)
  requires forall n: nat :: Valid(trace(n))
  requires Valid(trace(n))
  requires src in P && dst in P
  {
    && (forall i:nat | i < |trace(n).arrived[(src, dst)]| -1 :: MsgNum(trace(n).arrived[(src, dst)][i]) < MsgNum(trace(n).arrived[(src, dst)][i+1]))
  }

  ghost predicate InTransitInOrder(trace: Trace, n:nat, src: Process, dst: Process)
  requires forall n: nat :: Valid(trace(n))
  requires Valid(trace(n))
  requires src in P && dst in P
  {
    && (forall i:nat | i < |trace(n).inTransit[(src, dst)]| -1 :: MsgNum(trace(n).inTransit[(src, dst)][i]) < MsgNum(trace(n).inTransit[(src, dst)][i+1]))
  }

  ghost predicate ChannelsAreDisjoint(trace: Trace, n:nat)
  requires forall n: nat :: Valid(trace(n))
  requires Valid(trace(n))
  {
    && !(exists m: Message | ValidMessage(m) :: (m in trace(n).inTransit[(m.src, m.dst)] && m in trace(n).arrived[(m.src, m.dst)]))
    && !(exists m: Message | ValidMessage(m) :: (m in trace(n).inTransit[(m.src, m.dst)] && m in trace(n).delivered[(m.src, m.dst)]))
    && !(exists m: Message | ValidMessage(m) :: (m in trace(n).arrived[(m.src, m.dst)] && m in trace(n).delivered[(m.src, m.dst)]))
  }

  ghost predicate MessagesInQueueIncrementAtSrc(trace: Trace, n: nat, src: Process, dst: Process)
  requires Valid(trace(n))
  requires src in P && dst in P
{
  && forall i:nat | i < |trace(n).arrived[(src, dst)]| - 1 :: MsgNum(trace(n).arrived[(src, dst)][i]) == MsgNum(trace(n).arrived[(src, dst)][i+1]) + 1
}


// Get the n' >= n where the event choice at n' is an arrival from p to q
lemma GetNextArrival(trace: Trace, schedule: Schedule, p: Process, q: Process, n: nat)
  returns (n': nat)
  requires p in P && q in P
  requires FairSchedule(schedule)
  requires IsTrace(trace, schedule)
  ensures n <= n' && schedule(n') == (arrive, p, q)
  ensures trace(n).inTransit[(p,q)] <= trace(n').inTransit[(p,q)]
{
  var e := (arrive, p, q);
  assert HasNext(schedule, e, n+1);
  var u :| n < u && schedule(u) == e;
  n' := n;
  assert trace(n).inTransit[(p,q)] <= trace(n').inTransit[(p,q)];

  while schedule(n') != e
    invariant n' <= u
    invariant trace(n).inTransit[(p,q)] <= trace(n').inTransit[(p,q)]
    invariant n <= n'
    decreases u - n'
  {
    assert schedule(n') != e;
    n' := n' + 1;
  }

  assert trace(n).inTransit[(p,q)] <= trace(n').inTransit[(p,q)];
}

lemma MessageArrival(trace: Trace, schedule: Schedule, p: Process, q: Process, i: nat, m: Message)
  returns (result: nat)
  requires forall i: nat :: Valid(trace(i))
  requires FairSchedule(schedule)
  requires IsTrace(trace, schedule)
  requires p in P && q in P
  requires m in trace(i).inTransit[(p,q)]
  ensures exists j : nat :: j >= i && |trace(j).inTransit[(p,q)]| > 0 && trace(j).inTransit[(p,q)][0] == m
  ensures result >= i && m in trace(result).arrived[(p,q)]
{
  assert |trace(i).inTransit[(p,q)]| > 0;
  var j:nat;
  j := i;
  while trace(j).inTransit[(p,q)][0] != m
    invariant m in trace(j).inTransit[(p,q)]
    invariant j >= i
    decreases IndexOf(trace(j).inTransit[(p,q)], m)
  {
    assert m in trace(j).inTransit[(p,q)];
    assert IndexOf(trace(j).inTransit[(p,q)], m) > 0;
    var metric := IndexOf(trace(j).inTransit[(p,q)], m);

    var j_arrive := GetNextArrival(trace, schedule, p, q, j);
    assert IndexOf(trace(j_arrive).inTransit[(p,q)], m) > 0;
    assert schedule(j_arrive).0 == arrive;
    assert m in trace(j_arrive).inTransit[(p,q)];
    assert Arrive(trace(j_arrive), (arrive, p, q), trace(j_arrive+1));
    assert |trace(j_arrive).inTransit[(p,q)]| == |trace(j_arrive+1).inTransit[(p,q)]| +1;
    assert IndexOf(trace(j_arrive).inTransit[(p,q)], m) > IndexOf(trace(j_arrive+1).inTransit[(p,q)], m);

    j := j_arrive+1;

    assert IndexOf(trace(j).inTransit[(p,q)], m) < metric;
  }
  // Now that m is at the front of inTransit, get the arrival of m (next arrival)
  assert trace(j).inTransit[(p,q)][0] == m;
  var arrivalj := GetNextArrival(trace, schedule, p, q, j);
  assert trace(arrivalj + 1).inTransit == trace(arrivalj).inTransit[(p,q) := trace(arrivalj).inTransit[(p,q)][1..]];
  assert trace(arrivalj).inTransit[(p,q)][0] == m;
  assert trace(arrivalj + 1).arrived == trace(arrivalj).arrived[(p,q) := trace(arrivalj).arrived[(p,q)] + [trace(arrivalj).inTransit[(p,q)][0]]];
  assert trace(arrivalj + 1).arrived[(p,q)][|trace(arrivalj + 1).arrived[(p,q)]|-1] == m;
  assert m in trace(arrivalj + 1).arrived[(p,q)];
  assert arrivalj + 1 > i;
  result := arrivalj + 1;
}