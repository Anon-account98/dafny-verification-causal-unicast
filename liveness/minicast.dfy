type Process(==)
const P: set<Process>
type UnicastMessage = nat

type Vector = map<Process, nat>
type Payload = (Vector, UnicastMessage)

datatype Choice = send | arrive | deliver | deliverMinicast
type Event = (Choice, Process, Process) // src, dest

type Trace = nat -> System
type Schedule = nat -> Event

datatype Message = Unicast(src:Process, dst:Process, VC:Vector, payload:Payload) | Minicast(src: Process, dst: Process, msgNum: nat)

datatype System = System( inTransit: map<(Process, Process), seq<Message>>,
                          arrived: map<(Process, Process), seq<Message>>,
                          delivered: map<(Process, Process), seq<Message>>,
                          deliveredMCs: map<(Process, Process), nat>,
                          VCs: map<(Process, Process), nat>)


predicate Valid(s : System)
{
  && (forall src <- P, dest <- P :: (src, dest) in s.inTransit.Keys)
  && (forall src <- P, dest <- P :: (src, dest) in s.arrived.Keys)
  && (forall src <- P, dest <- P :: (src, dest) in s.delivered.Keys)
  && (forall src <- P, dest <- P :: (src, dest) in s.deliveredMCs.Keys)
  && (forall src <- P, dest <- P :: (src, dest) in s.VCs.Keys)
  && (forall src <- P, dest <- P, m:Message | m in s.inTransit[(src, dest)] :: ValidMessage(m))
  && (forall src <- P, dest <- P, m:Message | m in s.arrived[(src, dest)] :: ValidMessage(m))
  && (forall src <- P, dest <- P, m:Message | m in s.delivered[(src, dest)] :: ValidMessage(m))
}

predicate Invariant(s : System)
{
  && Valid(s)
  // && forall p <- P, q <- P ::
  //   ((exists m : Message :: m in s.delivered[(p,q)] && m.1) ==> s.pState[q])
}

predicate ValidEvent(e : Event)
{
  && e.1 in P
  && e.2 in P
}

predicate ValidVector(v: Vector)
{
  v.Keys == P
}

predicate ValidUnicast(m: Message)
  requires m.Unicast?
{
  && m.src in P
  && m.dst in P
  && ValidVector(m.VC)
  && ValidVector(m.payload.0)
}

predicate ValidMinicast(m:Message)
  requires m.Minicast?
{
  && m.src in P
  && m.dst in P
}

predicate ValidMessage(m: Message)
{
  if m.Unicast? then
    ValidUnicast(m)
  else
    ValidMinicast(m)
}

ghost predicate NextState(s: System, e: Event, s': System)
  requires Valid(s) && ValidEvent(e)
{
  || Send(s, e, s') || (|s.inTransit[(e.1,e.2)]| > 0 && Arrive(s, e, s')) ||
  (|s.arrived[(e.1,e.2)]| > 0 && s.arrived[(e.1,e.2)][0].Unicast? && ValidUnicast(s.arrived[(e.1,e.2)][0]) && LessThanEqSrc(s.arrived[(e.1, e.2)][0].payload.0, getPVectorFromMap(s.deliveredMCs, P, e.2), e.1) && Deliver(s, e, s'))
}

predicate Init(s: System)
{
  && Valid(s)
  && (forall src <- P, dst <- P :: s.inTransit[(src, dst)] == [])
  && (forall src <- P, dst <- P :: s.arrived[(src, dst)] == [])
  && (forall src <- P, dst <- P :: s.delivered[(src, dst)] == [])
  && (forall src <- P, dst <- P | src != dst :: s.deliveredMCs[(src, dst)] == 0)
  && (forall src <- P, dst <- P | src == dst :: s.deliveredMCs[(src, dst)] == 1)
  && (forall src <- P, dst <- P :: s.VCs[(src, dst)] == 0)
}

ghost predicate Next(s: System, s': System)
{
  Valid(s) &&
  exists e :: (ValidEvent(e)) && NextState(s, e, s')
}

lemma NSImpliesN(s: System, e: Event, s': System)
  requires Valid(s) && ValidEvent(e)
  requires NextState(s, e, s')
  ensures Next(s, s')
{

}

lemma tracesAreLogs(schedule: Schedule, trace: Trace)
  requires (forall n : nat :: Valid(trace(n)))
  requires IsSchedule(schedule) && IsTrace(trace, schedule)
  ensures IsALog(trace)
{
}

// lemma PreservesInvariant(s: System, s': System)
//   requires Invariant(s)
//   requires Next(s, s')
//   ensures Invariant(s')
// {

// }

predicate Send(s: System, e: Event, s': System)
  requires Valid(s) && ValidEvent(e)
{
  && e.0 == send
  && s'.VCs == s.VCs[(e.1, e.2) := s.VCs[(e.1, e.2)] + 1]
  // Unicast + minicast to dst
  && s'.inTransit == s.inTransit[(e.1,e.2) := s.inTransit[(e.1,e.2)]
                       + [Message.Unicast(e.1, e.2, getPVectorFromMap(s'.VCs, P, e.1), (getPVectorFromMap(s.deliveredMCs, P, e.1), 1))]
                       + [Message.Minicast(e.1, e.2, s.deliveredMCs[(e.1, e.1)])]]
  // Minicast
  && (forall r <- P - {e.1} - {e.2} :: s'.inTransit[(e.1,r)] == s.inTransit[(e.1,r)] + [Message.Minicast(e.1, e.2, s.deliveredMCs[(e.1, e.1)])])
  && s'.deliveredMCs == s.deliveredMCs[(e.1, e.1) := s.deliveredMCs[(e.1,e.1)] + 1]
  && s'.arrived == s.arrived
  && s'.delivered == s.delivered
}

// MPL brings a message to q (sent by p)
// guard: exists m in transit from p to q
predicate Arrive(s: System, e: Event, s': System)
  requires Valid(s) && ValidEvent(e) && |s.inTransit[(e.1,e.2)]| > 0
{
  && e.0 == arrive
  && s'.inTransit == s.inTransit[(e.1,e.2) := s.inTransit[(e.1,e.2)][1..]]
  && s'.arrived == s.arrived[(e.1,e.2) := s.arrived[(e.1,e.2)] + [s.inTransit[(e.1,e.2)][0]]]
  && s'.delivered == s.delivered
  && s'.deliveredMCs == s.deliveredMCs
}

predicate DeliverMinicast(s: System, e: Event, s': System)
  requires Valid(s) && ValidEvent(e) && |s.arrived[(e.1,e.2)]| > 0 && s.arrived[(e.1,e.2)][0].Minicast?
{
  && e.0 == deliverMinicast
  && s'.inTransit == s.inTransit
  && s'.arrived == s.arrived[(e.1,e.2) := s.arrived[(e.1, e.2)][1..]]
  && s'.delivered == s.delivered
  && s'.deliveredMCs == s.deliveredMCs[(e.2, e.1) := s.arrived[(e.1, e.2)][0].msgNum]
}

predicate Deliver(s: System, e: Event, s': System)
  requires Valid(s) && ValidEvent(e) && |s.arrived[(e.1,e.2)]| > 0 && s.arrived[(e.1,e.2)][0].Unicast? && ValidUnicast(s.arrived[(e.1,e.2)][0])
  requires LessThanEqSrc(s.arrived[(e.1, e.2)][0].payload.0, getPVectorFromMap(s.deliveredMCs, P, e.2), e.1)
  requires e.1 in P && e.2 in P
{
  && e.0 == deliver
  && s'.inTransit == s.inTransit
  && s'.arrived == s.arrived[(e.1,e.2) := s.arrived[(e.1,e.2)][1..]]
  && s'.delivered == s.delivered[(e.1,e.2) := s.delivered[(e.1,e.2)] + [s.arrived[(e.1,e.2)][0]]]
  && s'.deliveredMCs == s.deliveredMCs[(e.2,e.1) := s.arrived[(e.1,e.2)][0].payload.0[e.1]]
  // && s'.VCs == getVCsMaxAtP(s.VCs, m.VC, dst)
}

ghost predicate IsSchedule(schedule: Schedule)
{
  forall i :: ValidEvent(schedule(i))
}

ghost predicate IsTrace(trace: Trace, schedule: Schedule)
  requires IsSchedule(schedule)
{
  && Init(trace(0))
  && (forall i: nat :: (Valid(trace(i)) && NextState(trace(i), schedule(i), trace(i+1))))
  && (forall n:nat, src <- P, dst <- P :: ChannelsAreDisjoint(trace, n))
  && (forall n:nat, n':nat, m:Message | n <= n' && MessageInQueue(m, trace, n) ::  MessageInQueue(m, trace, n'))
  && (forall n:nat, n':nat, m:Message | n <= n' && MessageInQueue(m, trace, n) && m in trace(n).delivered[(m.src, m.dst)] ::  m in trace(n').delivered[(m.src, m.dst)])
}

ghost predicate IsALog(trace: Trace) {
  Init(trace(0)) &&
  forall i: nat :: (Valid(trace(i)) && Next(trace(i), trace(i+1)))
}

// lemma InvariantHolds(trace: Trace, n: nat)
//   requires IsALog(trace)
//   ensures forall i: nat | i <= n :: Invariant(trace(i))
// {
//   if (n > 0) {
//      InvariantHolds(trace, n-1);
//      PreservesInvariant(trace(n-1), trace(n));
//   }
// }

// lemma NewsIsStable(t: Trace, s: Schedule)
//   requires IsSchedule(s) && IsTrace(t,s)
//   requires forall i : nat :: Valid(t(i))
//   ensures forall p <- P ::
//     (forall i : nat :: (t(i).pState[p] ==> t(i+1).pState[p]))
//   {

//   }

// lemma stablePrefixForGivenPoint(trace: Trace, i: nat, n: nat)
// requires forall i: nat :: Valid(trace(i))
// requires forall i: nat :: trace(i).pState.Keys == trace(i+1).pState.Keys
// requires forall i: nat :: trace(0).pState.Keys == trace(i).pState.Keys
// requires (forall p <- trace(0).pState.Keys ::
//   (forall i : nat :: (trace(i).pState[p] ==> trace(i+1).pState[p])))
// requires i < n
// ensures (forall p <- trace(0).pState.Keys ::
//   (trace(i).pState[p] ==> (forall j : nat | (j <= n && i < j) :: trace(j).pState[p])))
// {
//   var c := i;
//   while (c <= n)
//   invariant (forall p <- trace(0).pState.Keys ::
//     (trace(i).pState[p] ==> forall j | (j <= c && i < j) :: trace(j).pState[p]))
//   {
//       assert (forall p <- trace(0).pState.Keys ::
//                 (trace(i).pState[p] ==> trace(c).pState[p]));
//       c := c + 1;
//   }
//   assert (forall p <- trace(0).pState.Keys ::
//             (trace(i).pState[p] ==> forall j | (j <= n && i < j) :: trace(j).pState[p]));
// }

// lemma stablePrefix(trace:Trace, n: nat)
// requires forall i: nat :: Valid(trace(i))
// //requires forall i: nat :: trace(i).pState.Keys == trace(i+1).pState.Keys
// requires forall i: nat :: trace(i).pState.Keys == P
// requires (forall p <- P ::
//   (forall i : nat :: (trace(i).pState[p] ==> trace(i+1).pState[p])))
// ensures (forall p <- P ::
//         (forall i : nat | i < n :: trace(i).pState[p] ==> (forall j : nat | (j <= n && i < j) :: trace(j).pState[p])))
// {
//     forall i: nat | i < n
//     ensures (forall p <- trace(0).pState.Keys ::
//         (trace(i).pState[p] ==> (forall j : nat | (j <= n && i < j) :: trace(j).pState[p])))
//     {
//         stablePrefixForGivenPoint(trace, i, n);
//     }
// }

// lemma stablePState(trace: Trace)
// requires forall i: nat :: Valid(trace(i))
// requires forall i: nat :: trace(i).pState.Keys == P
// //requires forall i: nat :: trace(i).pState.Keys == trace(i+1).pState.Keys
// //requires forall i: nat :: trace(0).pState.Keys == trace(i).pState.Keys
// requires (forall p <- P ::
//   (forall i : nat :: (trace(i).pState[p] ==> trace(i+1).pState[p])))
// ensures (forall p <- P ::
//             (forall i : nat :: trace(i).pState[p] ==> (forall j : nat | (i < j) :: trace(j).pState[p])))

// {
//     // assert forall n : nat {:trigger} :: (forall p <- trace(0).pState.Keys ::
//     //                                       (forall i : nat | i <= n :: trace(i).pState[p] ==> trace(i+1).pState[p]));

//     forall n: nat {:trigger}
//     ensures (forall p <- P ::
//               (forall i : nat | i < n :: trace(i).pState[p] ==> (forall j : nat | (j <= n && i < j) :: trace(j).pState[p])))
//     {
//         stablePrefix(trace, n);
//     }

//     // assert (forall p <- trace(0).pState.Keys ::
//     //           (forall i : nat :: trace(i).pState[p] ==> (forall j | i < j :: trace(j).pState[p])));
// }


// does not require that sends happen infinitely often
ghost predicate FairSchedule(schedule: Schedule)
{
  IsSchedule(schedule) &&
  forall c : Choice, p <- P, q <- P , n : nat | c != send :: HasNext(schedule, (c, p, q), n)
}

ghost predicate HasNext(schedule: Schedule, e:Event, n: nat)
{
  exists n' :: n <= n' && schedule(n') == e
}

lemma GetNextStep(trace: Trace, schedule: Schedule, e: Event, n: nat)
  returns (n': nat)
  requires FairSchedule(schedule)
  requires HasNext(schedule, e, n)
  requires e.0 != send
  ensures n < n' && schedule(n') == e
{
  assert HasNext(schedule, e, n+1);
  var u :| n < u && schedule(u) == e;
  n' := n+1;
  while schedule(n') != e
    invariant n' <= u
    decreases u - n'
  {
    n' := n' + 1;
  }
}


// lemma PStateAtDelivery(trace: Trace, schedule: Schedule, p: Process, q: Process, m: Message, n: nat)
// requires forall i: nat :: Valid(trace(i))
// requires FairSchedule(schedule)
// requires IsTrace(trace, schedule)
// requires p in P && q in P
// requires schedule(n).0 == deliver
// requires !(m in trace(n).delivered[(p,q)])
// requires m in trace(n+1).delivered[(p,q)]
// requires m.1
// ensures trace(n+1).pState[q]
// {
//   assert trace(n+1).pState == trace(n).pState[q := (trace(n).pState[q] || trace(n).arrived[(p,q)][0].1)];
// }

// TODO
// if we include inTransit, p always has a message that is the smallest that is ready to be delivered
// (as soon as it has arrived)
// no new message can be sent that happens before any message in inTransit or arrived
// as trace increases, VC timestamps are increasing


// Get the minimal unicast message for this process
// lemma NextMessageToBeDelivered(trace: Trace, schedule: Schedule, n:nat, dst:Process)
//   returns (m: Message)
//   requires (forall n : nat :: Valid(trace(n)))
//   requires dst in P
//   requires FairSchedule(schedule) && IsTrace(trace, schedule)
//   ensures ValidMessage(m)
// {
//   // Check each m in inTransit and arrived and look for the smallest one (or one of the smallest)

//   // If there is a concurrent message, the message before that concurrent one must not be concurrent because
//   // to be concurrent, the value at that process must be bigger, and the value of the one before it must be the same

//   var allInTransitMessages := set m <- trace(n).inTransit[(dst, dst)];

//   var PCopy;
//   var n';

//   while PCopy != {}
//     decreases |PCopy|
//   {
//     var q :| q in PCopy;
//     var m := NextMessageToBeDelivered(trace, schedule, n, q);

//     // If m is still in transit, find the point that it is no longer in transit
//     while(m in trace(n').inTransit[(m.src,q)])
//     {
//       n' := n' + 1;
//     }

//     // m is in arrived and must be the smallest message
//     // wait until all minicasts have arrived?
//     // m must meet delivery condition
    

    
    

//     PCopy := PCopy - {q};
//   }
 
// }