// Processes in the system only need equality.
type Process(==)
type UnicastMessage = nat

type Vector = map<Process, nat>
type Payload = (Vector, UnicastMessage)

// Sender, Receiver, VCs, payload
//type Unicast = (Process, Process, Vector, Payload)

// Sender, Receiver, messageNum
//type Minicast = (Process, Process, nat)

datatype Message = Unicast(src:Process, dst:Process, VC:Vector, payload:Payload) | Minicast(src: Process, dst: Process, msgNum: nat)


// The state of each process is whether it has heard the news.
// The state of the message passing layer is:
//   a. the list of queues (ie for each sender) of in-transit messages (to all destinations) and
//   b. the list of buffers (ie for each destination) of arrived messages (from all senders).
//   c. the list of histories (ie for each process) of processed messages (from all senders).
class System {
  const P: set<Process>

  // Message passing layer
  var inTransit: map<(Process, Process), seq<Message>> // src, dest
  var arrived: map<(Process, Process), seq<Message>> // src, dest
  var delivered: map<(Process, Process), seq<Message>> // src, dest

  // Minicast Algorithm variables
  //var deliveredMCs: map<Process, Vector>
  var deliveredMCs: map<(Process, Process), nat> // p x all qs

  // Causal Ordering tracker variable
  // Each process maps to a "local" vector of how many messages it has seen to have been delivered from every other process
  //var VC: map<Process, Vector>
  var VCs: map<(Process, Process), nat> // p x all qs

  ghost predicate CausallyOrdered()
    reads this
    requires Valid()
  {
    && forall m1: Message, m2: Message | m1.dst == m2.dst && m1.Unicast? && m2.Unicast? && ValidUnicast(m1) && ValidUnicast(m2)
                                         && m1.dst != m1.src
                                         && (m1 in inTransit[(m1.src, m1.dst)] || m1 in arrived[(m1.src, m1.dst)] || m1 in delivered[(m1.src, m1.dst)])::
      (m2 in delivered[(m2.src, m2.dst)] && HappensBefore(m1, m2)) ==> m1 in delivered[(m1.src, m1.dst)]
  }

  ghost predicate CausallyOrdered2(dest: Process)
    requires dest in P
    reads this
    requires Valid()
  {
    && forall m1: Message, m2: Message | m1.Unicast? && m2.Unicast? && ValidUnicast(m1) && ValidUnicast(m2)
                                         && (m1 in inTransit[(m1.src, m1.dst)] || m1 in arrived[(m1.src, m1.dst)] || m1 in delivered[(m1.src, m1.dst)]) ::
      (m2 in delivered[(m2.src, dest)] && HappensBefore(m1, m2)) ==> m1 in delivered[(m1.src, dest)]
  }

  ghost predicate CausallyOrdered3()
    reads this
    requires Valid()
  {
    forall p <- P :: CausallyOrdered2(p)
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

  function MsgNum(m:Message) : nat
    requires ValidMessage(m)
  {
    if m.Unicast? then
      m.payload.0[m.src]
    else
      m.msgNum
  }

  predicate HappensBefore(m1: Message, m2: Message)
    requires m1.Unicast? && m2.Unicast?
    requires ValidUnicast(m1) && ValidUnicast(m2)
  {
    && LessThan(m1.VC, m2.VC)
  }

  ghost predicate Valid()
    reads this
  {
    && (forall src <- P, dest <- P :: (src, dest) in inTransit.Keys)
    && (forall src <- P, dest <- P :: (src, dest) in arrived.Keys)
    && (forall src <- P, dest <- P :: (src, dest) in delivered.Keys)
    && (forall p <- P, q <- P :: (p, q) in deliveredMCs.Keys)
    && (forall p <- P, q <- P :: (p, q) in VCs.Keys)
    && (forall src <- P, dest <- P, m:Message | m in inTransit[(src, dest)] :: ValidMessage(m))
    && (forall src <- P, dest <- P, m:Message | m in arrived[(src, dest)] :: ValidMessage(m))
    && (forall src <- P, dest <- P, m:Message | m in delivered[(src, dest)] :: ValidMessage(m))
  }

  constructor(processes: set<Process>)
    ensures Valid()
    ensures P == processes
    // ensures MaxDeliveredMCsatP()
    ensures CausallyOrdered()
  {
    P := processes;
    var tuples := set p <- processes, q <- processes :: (p, q);
    inTransit := map p <- tuples :: [];
    arrived := map p <- tuples :: [];
    delivered := map p <- tuples :: [];
    deliveredMCs := map p <- tuples :: 0;
    VCs := map p <- tuples :: 0;

    new;

    var keys := deliveredMCs.Keys;

    assert CausallyOrdered();

    var PCopy := P;
    while PCopy != {}
      invariant deliveredMCs.Keys == keys
      invariant Valid()
      invariant CausallyOrdered()
      invariant forall p <- P, q <- P | p != q :: deliveredMCs[(q, p)] == 0
      invariant forall p <- P - PCopy :: deliveredMCs[(p,p)] == 1
    {
      var r :| r in PCopy;
      deliveredMCs := deliveredMCs[(r,r) := 1];
      PCopy := PCopy - {r};
    }

    assert forall p <- P, q <- P | p != q :: deliveredMCs[(p,p)] > deliveredMCs[(q, p)];


  }

  // deliveredMCs is monotonically increasing?
  // If s1 -> s2, s1.m.deliveredMCs < s2.m.deliveredMCs
  ghost predicate StablePredicate()
    reads this
    requires Valid()
  {
    && (forall m1: Message, m2: Message | (m1.Unicast? && m2.Unicast? && ValidUnicast(m1) && ValidUnicast(m2)) ::
          (HappensBefore(m1, m2) ==> LessThan(m1.payload.0, m2.payload.0)))
  }

  ghost predicate StablePredicate2(dst: Process)
    reads this
    requires Valid()
  {
    && (forall m: Message | m.dst == dst && m.Unicast? && ValidUnicast(m) && m in delivered[(m.src, dst)] ::
          LessThan(m.payload.0, getPVectorFromMap(deliveredMCs, P, dst)))
  }

  // MCs at the sender's location is larger than deliveredMCs for everything in arrived
  ghost predicate StablePredicate3(dst: Process)
    reads this
    requires Valid()
  {
    && (forall m: Message | m.dst == dst && dst != m.src && m.Unicast? && ValidUnicast(m) &&
                            LessThanEq(m.payload.0, getPVectorFromMap(deliveredMCs, P, dst)) :: !(m in arrived[(m.src, dst)]) && !(m in inTransit[(m.src, dst)]))
  }

  lemma MCSMustBeBigEnough(q:Process)
    requires Valid()
    requires q in P
    requires (forall m: Message | m.dst == q && q != m.src && m.Unicast? && ValidUnicast(m)
                                  && m in arrived[(m.src, m.dst)] ::
                m.payload.0[m.src] > deliveredMCs[(q, m.src)] && LessThanEqSrc(m.payload.0, getPVectorFromMap(deliveredMCs, P, q), m.src))
    ensures (forall  m: Message | m.dst == q && q != m.src && m.Unicast? && ValidUnicast(m) &&
                                  LessThanEq(m.payload.0, getPVectorFromMap(deliveredMCs, P, q)) :: !(m in arrived[(m.src, q)]))
  {
    // know: everything in arrived has src component > dMC[src]
    // know: for all m :: m in arrived ==> m[src] > dMC[src]
    // know: for all m :: m[src] <= dMC[src] ==> m !in arrived

    // nothing in arrived is <= dMC
    // ! exist m in arrived :: all i m[i] <= dMC[i]
    // prove: for all m :: forall i m[i] <= dMC[i] ==> m !in arrived
  }

  lemma CausalOrderingFromPredicates()
    requires Valid()
    requires MaxDeliveredMCsatP()
    requires StablePredicate()
    requires forall dst <- P :: StablePredicate2(dst)
    requires forall dst <- P :: StablePredicate3(dst)
    ensures CausallyOrdered()
  {
    // assert forall m1: Message, m2: Message | m1.dst == m2.dst && m1.Unicast? && m2.Unicast? && ValidUnicast(m1) && ValidUnicast(m2)
    //                                          && m1.dst != m1.src
    //                                          && (m1 in inTransit[(m1.src, m1.dst)] || m1 in arrived[(m1.src, m1.dst)] || m1 in delivered[(m1.src, m1.dst)])
    //                                          && HappensBefore(m1, m2) && m2 in delivered[(m2.src, m2.dst)] ::
    //     (LessThan(m1.payload.0, m2.payload.0)) &&
    //     // (LessThan(m2.payload.0, getPVectorFromMap(deliveredMCs, P, m2.dst))) &&
    //     // (LessThan(m1.payload.0, getPVectorFromMap(deliveredMCs, P, m2.dst))) &&
    //     (LessThanEq(m1.payload.0, getPVectorFromMap(deliveredMCs, P, m2.dst)));
    //     // !(m1 in arrived[(m1.src, m2.dst)]) &&
    //     // !(m1 in inTransit[(m1.src, m2.dst)]);
    //     // (m1 in delivered[(m1.src, m2.dst)]);

  }

  // The value of deliveredMCs at p is higher at process p than any other process
  ghost predicate MaxDeliveredMCsatP()
    reads this
    requires Valid()
  {
    && (forall src <- P, dst <- P :: InTransitInOrder(src, dst))
    && (forall src <- P, dst <- P :: ArrivedInOrder(src, dst))
    && (forall src <- P, dst <- P :: DeliveredInOrder(src, dst))
    && (forall src <- P, dest <- P :: ChannelsAreDisjoint(src, dest))
    && (forall p <- P, m:Message | m.Minicast? :: deliveredMCs[(p,p)] > m.msgNum)
    && (forall p <- P, m: Message | m.Unicast? && ValidUnicast(m) ::
          deliveredMCs[(p,p)] > m.payload.0[p])
    && (forall p <- P, q <- P | p != q :: deliveredMCs[(p,p)] > deliveredMCs[(q, p)])
    && (forall q <- P, m: Message | m.Unicast? && ValidUnicast(m) && q != m.src && m in arrived[(m.src, m.dst)] ::
          m.payload.0[m.src] > deliveredMCs[(q, m.src)])
    && (forall q <- P, m: Message | m.Unicast? && ValidUnicast(m) && q != m.src && m in inTransit[(m.src, m.dst)] ::
          m.payload.0[m.src] > deliveredMCs[(q, m.src)])
  }

  ghost predicate DeliveredInOrder(src: Process, dst: Process)
    reads this
    requires Valid()
    requires src in P && dst in P
  {
    && (forall i:nat | i < |delivered[(src, dst)]| -1 :: MsgNum(delivered[(src, dst)][i]) < MsgNum(delivered[(src, dst)][i+1]))
  }

  ghost predicate ArrivedInOrder(src: Process, dst: Process)
    reads this
    requires Valid()
    requires src in P && dst in P
  {
    && (forall i:nat | i < |arrived[(src, dst)]| -1 :: MsgNum(arrived[(src, dst)][i]) < MsgNum(arrived[(src, dst)][i+1]))
  }

  ghost predicate InTransitInOrder(src: Process, dst: Process)
    reads this
    requires Valid()
    requires src in P && dst in P
  {
    && (forall i:nat | i < |inTransit[(src, dst)]| -1 :: MsgNum(inTransit[(src, dst)][i]) < MsgNum(inTransit[(src, dst)][i+1]))
  }

  ghost predicate ChannelsAreDisjoint(src: Process, dst: Process)
    reads this
    requires Valid() && src in P && dst in P
  {
    && !(exists m: Message | ValidMessage(m) :: (m in inTransit[(src, dst)] && m in arrived[(src, dst)]))
    && !(exists m: Message | ValidMessage(m) :: (m in inTransit[(src, dst)] && m in delivered[(src, dst)]))
    && !(exists m: Message | ValidMessage(m) :: (m in arrived[(src, dst)] && m in delivered[(src, dst)]))

    && (forall i:nat, j: nat | i < |inTransit[(src, dst)]| && j < |inTransit[(src, dst)]|
          :: (inTransit[(src, dst)][i] == inTransit[(src, dst)][j]) ==> i == j)
    && (forall i:nat, j: nat | i < |arrived[(src, dst)]| && j < |arrived[(src, dst)]|
          :: (arrived[(src, dst)][i] == arrived[(src, dst)][j]) ==> i == j)
    && (forall i:nat, j: nat | i < |delivered[(src, dst)]| && j < |delivered[(src, dst)]|
          :: (delivered[(src, dst)][i] == delivered[(src, dst)][j]) ==> i == j)
  }

  // p sends a message to q
  // guard: true
  method Send(p: Process, q: Process)
    returns (m:Message)
    requires Valid() && p in P && q in P
    requires p != q
    requires CausallyOrdered()
    requires StablePredicate()
    requires MaxDeliveredMCsatP()
    modifies this`inTransit, this`VCs, this`deliveredMCs
    ensures Valid()
    ensures inTransit[(p,q)] == old(inTransit)[(p,q)] + [m] + [Message.Minicast(p, q, old(deliveredMCs)[(p, p)])]
    ensures forall r <- P - {p} - {q} :: inTransit[(p,r)] == old(inTransit)[(p,r)] + [Message.Minicast(p, q, old(deliveredMCs)[(p, p)])]
    ensures deliveredMCs[(p,p)] == old(deliveredMCs)[(p,p)] + 1
    ensures MaxDeliveredMCsatP()
    ensures StablePredicate()
    ensures CausallyOrdered()
  {
    // Update p.VC at q
    VCs := VCs[(p, p) := VCs[(p, p)] + 1];

    // Create a message to send
    var unicastMessage: UnicastMessage := *;
    var payload := (getPVectorFromMap(deliveredMCs, P, p), unicastMessage);
    m := Message.Unicast(p, q, getPVectorFromMap(VCs, P, p), payload);

    // Unicast and Minicast to q
    inTransit := inTransit[(p,q) := inTransit[(p,q)] + [m]];
    assert inTransit[(p,q)] == old(inTransit)[(p,q)] + [m];
    var mini := Message.Minicast(p, q, deliveredMCs[(p, p)]);
    inTransit := inTransit[(p,q) := inTransit[(p,q)] + [mini]];
    assert inTransit[(p,q)] == old(inTransit)[(p,q)] + [m] + [Message.Minicast(p, q, deliveredMCs[(p, p)])];
    var qInTransit := inTransit[(p,q)];

    // Minicast
    var PCopy := P - {p} - {q};
    while PCopy != {}
      decreases |PCopy|
      invariant Valid() && PCopy <= P && !(q in PCopy)
      invariant inTransit[(p,q)] == qInTransit
      invariant deliveredMCs == old(deliveredMCs)
      invariant forall r <- (P - PCopy) | r != p && r != q :: inTransit[(p,r)] == old(inTransit)[(p,r)] + [Message.Minicast(p, q, deliveredMCs[(p, p)])]
      invariant forall r <- PCopy | r != q :: inTransit[(p, r)] == old(inTransit)[(p, r)]
    {
      var r :| r in PCopy;
      inTransit := inTransit[(p,r) := inTransit[(p,r)] + [mini]];
      PCopy := PCopy - {r};
    }

    // Update DeliveredMCs
    deliveredMCs := deliveredMCs[(p, p) := deliveredMCs[(p,p)] + 1];
  }

  // // MPL brings a message to q (sent by p)
  // // guard: exists m in transit from p to q
  method Arrive(p: Process, q: Process)
    requires Valid() && p in P && q in P
    requires CausallyOrdered()
    requires StablePredicate()
    requires inTransit[(p, q)] != [] // guard
    modifies this`inTransit, this`arrived
    ensures Valid()
    ensures inTransit == old(inTransit)[(p, q) := old(inTransit)[(p, q)][1..]]
    ensures arrived == old(arrived)[(p, q) := old(arrived)[(p, q)] + [old(inTransit)[(p, q)][0]]]
    ensures StablePredicate()
    ensures CausallyOrdered()
  {
    var m := inTransit[(p, q)][0];
    inTransit := inTransit[(p, q) := inTransit[(p, q)][1..]];
    arrived := arrived[(p, q) := arrived[(p, q)] + [m]];
  }

  method compare(v1: Vector, v2: Vector)
    requires ValidVector(v1) && ValidVector(v2)
  {
    var v := getMaxVector2(v1, v2);
    assert forall r <- v.Keys :: v[r] == v1[r] || v[r] == v2[r];
    assert forall r <- v.Keys :: v[r] >= v1[r] && v[r] >= v2[r];
  }


  // p delivers a minicast message
  // guard: exists a message in p's buffer of arrived messages
  method DeliverMinicast(src: Process, dst: Process)
    requires Valid() && src in P && dst in P
    requires src != dst
    requires StablePredicate()
    requires MaxDeliveredMCsatP()
    requires CausallyOrdered()
    requires arrived[(src, dst)] != [] // guard
    requires arrived[(src, dst)][0].Minicast? // guard
    modifies this`arrived, this`deliveredMCs
    ensures Valid()
    ensures arrived == old(arrived)[(src, dst) := old(arrived)[(src, dst)][1..]]
    ensures deliveredMCs[(dst, src)] == old(arrived)[(src, dst)][0].msgNum
    ensures StablePredicate()
    //ensures MaxDeliveredMCsatP()
    ensures CausallyOrdered()
  {
    var m:Message := arrived[(src, dst)][0];
    // assert ArrivedInOrder();
    arrived := arrived[(src, dst) := arrived[(src, dst)][1..]];
    //assert ArrivedInOrder();
    deliveredMCs := deliveredMCs[(dst, src) := m.msgNum];
  }
}
