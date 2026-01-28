function IndexOf(xs: seq<Message>, v: Message): (i: int)
    ensures (!(v in xs)) ==> (i == -1)
    ensures i < |xs|
    ensures (v in xs) ==> i >= 0 && xs[i] == v
    ensures forall j :: 0 <= j < i ==> xs[j] != v
  {
    if !(v in xs) then -1 else
      assert v in xs;
      (if xs[0] == v then 0 else 1 + IndexOf(xs[1..], v))
  }

predicate LessThan(v1: Vector, v2: Vector)
requires v1.Keys == v2.Keys
{
  && (forall p <- v1.Keys :: v1[p] <= v2[p])
  && (exists p <- v1.Keys :: v1[p] < v2[p])
}

predicate Concurrent(m1: Message, m2:Message)
requires m1.Unicast? && m2.Unicast?
requires m1.payload.0.Keys == m2.payload.0.Keys
{
  && (exists p <- m1.payload.0.Keys :: m1.payload.0[p] < m2.payload.0[p])
  && (exists p <- m1.payload.0.Keys :: m1.payload.0[p] > m2.payload.0[p])
}

function getPVectorFromMap(vectorMap: map<(Process, Process), nat>, keys:set<Process>, p: Process) : Vector
requires forall r <- keys :: ((p, r) in vectorMap.Keys)
requires p in keys
ensures forall q <- getPVectorFromMap(vectorMap, keys, p).Keys :: getPVectorFromMap(vectorMap, keys, p)[q] == vectorMap[(p,q)]
ensures  getPVectorFromMap(vectorMap, keys, p).Keys == keys
//ensures forall q <- v.Keys :: v[q] == vectorMap[(p,q)]
{
  map i: Process | i in keys :: vectorMap[(p,i)]
}

method getVCsMaxAtP(VCs: map<(Process, Process), nat>, v1: Vector, q:Process)
returns (maxV: map<(Process, Process), nat>)
requires forall r <- v1.Keys :: ((r, q) in VCs.Keys)
requires q in v1.Keys
ensures maxV.Keys == VCs.Keys
ensures forall p:Process :: (p,q) in maxV.Keys && p in v1.Keys ==> ((maxV[(p, q)] == v1[p] || maxV[(p, q)] == VCs[(p, q)]) && (maxV[(p, q)] >= v1[p]) && (maxV[(p, q)] >= VCs[(p, q)]))
{
  // maxV := map p <- v1.Keys :: 0;
  // var keys := v1.Keys;

  // while keys != {} 
  //   decreases |keys|
  //   invariant keys <= v1.Keys
  //   invariant maxV.Keys == v1.Keys
  //   invariant forall p <- v1.Keys - keys :: if v1[p] > v2[p] then maxV[p] == v1[p] else maxV[p] == v2[p]
  //   {
  //     var q :| q in keys;
  //     if v1[q] > v2[q] {
  //       maxV := maxV[q := v1[q]];
  //     } else {
  //       maxV := maxV[q := v2[q]];
  //     }
  //     keys := keys - {q};
  //   }
  maxV := VCs;
  assume {:axiom}  forall p:Process :: (p,q) in maxV.Keys && p in v1.Keys ==> ((maxV[(p, q)] == v1[p] || maxV[(p, q)] == VCs[(p, q)]) && (maxV[(p, q)] >= v1[p]) && (maxV[(p, q)] >= VCs[(p, q)]));
}

// ghost predicate AllQueuesAreFinite(t: Trace, n: nat)
//   requires Valid(t(n))
// {
//   // && (forall p, q :: |t(n).inTransit[(p,q)]| <= n)
//   && (forall p <- P , q <- P :: |t(n).arrived[(p,q)]| <= n)
//   // && (forall p, q :: |t(n).delivered[(p,q)]| <= n)
// }

lemma MessagesInArrivedAtSrcDst(trace: Trace, n: nat, src: Process, dst: Process)
  returns (messages: set<Message>)
  requires Valid(trace(n))
  requires src in P && dst in P
  ensures forall m:Message :: ( m.Unicast? && ValidUnicast(m) && m.src == src && m.dst == dst
                                && m in trace(n).arrived[(m.src, m.dst)]) <==> m in messages
{
  messages := (set m:Message | m.Unicast? && ValidUnicast(m) && m.src == src && m.dst == dst
                               && m in trace(n).arrived[(src, dst)]);
}

// lemma MessagesInArrived2(trace: Trace, n: nat)
//   returns (messages: iset<Message>)
//   requires Valid(trace(n))
//   ensures forall m:Message | m.Unicast? && ValidUnicast(m) && m in trace(n).arrived[(m.src, m.dst)] :: m in messages
//   ensures forall m | m in messages :: m.Unicast? && ValidUnicast(m) && m in trace(n).arrived[(m.src, m.dst)]
//   {
//     messages := (iset m:Message | m in trace(n).arrived[(m.src, m.dst)] :: m);
//   }

// Get all of the messages in arrived at n
lemma MessagesInArrived(trace: Trace, n: nat)
  returns (messages: set<Message>)
  requires Valid(trace(n))
  ensures forall m:Message | m.Unicast? && ValidUnicast(m) && m in trace(n).arrived[(m.src, m.dst)] :: m in messages
  ensures forall m | m in messages :: m.Unicast? && ValidUnicast(m) && m in trace(n).arrived[(m.src, m.dst)]
{
  messages := {};
  var setofmessages:set<Message>;

  var setOfSrcs := P;
  var setOfDsts := P;

  while(setOfSrcs != {})
    invariant forall p <- setOfSrcs :: p in P
    invariant forall q <- setOfDsts :: q in P
    invariant forall m:Message | m.Unicast? && ValidUnicast(m) && m.src in P - setOfSrcs 
            && m in trace(n).arrived[(m.src, m.dst)] :: m in messages
    invariant forall m | m in messages :: m.Unicast? && ValidUnicast(m) && m in trace(n).arrived[(m.src, m.dst)]
  {
    var src :| src in setOfSrcs;
    setOfDsts := P;
    while(setOfDsts != {})
      invariant forall q <- setOfDsts :: q in P
      invariant forall m:Message | m.Unicast? && ValidUnicast(m) && m.src == src && m.dst in P - setOfDsts
        && m in trace(n).arrived[(m.src, m.dst)] :: m in messages
      invariant forall m:Message | m.Unicast? && ValidUnicast(m) && m.src in P - setOfSrcs 
        && m in trace(n).arrived[(m.src, m.dst)] :: m in messages
      invariant forall m | m in messages :: m.Unicast? && ValidUnicast(m) && m in trace(n).arrived[(m.src, m.dst)]
    {
      var dst :| dst in setOfDsts;
      var messagesAtSrcDst := MessagesInArrivedAtSrcDst(trace, n, src, dst);
      messages := messages + messagesAtSrcDst;
      setOfDsts := setOfDsts - {dst};
    }
    
    setOfSrcs := setOfSrcs - {src};
  }
}

predicate LessThanEqSrc(v1: Vector, v2: Vector, src: Process)
requires v1.Keys == v2.Keys
{
  && (forall p <- v1.Keys | p != src :: v1[p] <= v2[p])
}

function MsgNum(m:Message) : nat
  requires ValidMessage(m)
  {
    if m.Unicast? then
      m.payload.0[m.src]
    else
      m.msgNum
  }


lemma SetSizeRelation(a:set, b:set)
  requires a <= b
  ensures |a| <= |b|
{
  if a != b {
    var x :| x in b && x !in a;
    SetSizeRelation(a, b - {x});
  }
}