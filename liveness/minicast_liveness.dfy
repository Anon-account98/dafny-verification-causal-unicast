include "minicast.dfy"

ghost predicate LivenessSpec(trace: Trace)
  requires (forall n : nat :: Valid(trace(n)))
{
  && (forall n : nat :: Valid(trace(n)))
  && forall n : nat  ::
       (forall m : Message | m.Unicast? && ValidUnicast(m) :: (m in trace(n).arrived[(m.src, m.dst)]) ==> (exists n' : nat | n' >= n :: m in trace(n').delivered[(m.src, m.dst)]))
}


lemma Liveness(trace: Trace, schedule: Schedule)
  requires (forall n : nat :: Valid(trace(n)))
  requires FairSchedule(schedule) && IsTrace(trace, schedule)
  ensures LivenessSpec(trace)
{
  forall n : nat
    ensures forall m: Message | m.Unicast? && ValidUnicast(m) && m in trace(n).arrived[(m.src, m.dst)]
              :: (exists n':nat | n' >= n && Valid(trace(n')) :: m in trace(n').delivered[(m.src, m.dst)]) {
    LivenessAtN(trace, schedule, n);
  }
}

ghost predicate StablePredicate(trace: Trace)
  requires forall num:nat :: Valid(trace(num))
{
  && (forall n:nat :: Valid(trace(n)))
  && forall m: Message, n:nat, n':nat | m.Unicast? && ValidUnicast(m) && n <= n' && (m in trace(n).delivered[(m.src, m.dst)]) ::
       m in trace(n').delivered[(m.src, m.dst)]
}


lemma LivenessAtN(trace: Trace, schedule: Schedule, n: nat)
  requires (forall n : nat :: Valid(trace(n)))
  requires FairSchedule(schedule)
  requires IsTrace(trace, schedule)
  requires Valid(trace(n))
  ensures forall m: Message | m.Unicast? && ValidUnicast(m) && m in trace(n).arrived[(m.src, m.dst)]
            :: (exists n':nat | n' >= n && Valid(trace(n')) :: m in trace(n').delivered[(m.src, m.dst)])
{
  // get every message in arrived at n to prove that they are delivered by n'
  var messagesInArrivedAtN := MessagesInArrived(trace, n);
  assert forall m | m in messagesInArrivedAtN :: m in trace(n).arrived[(m.src, m.dst)];

  forall m | m in messagesInArrivedAtN
    ensures exists n':nat | n' >= n && Valid(trace(n')) :: m in trace(n').delivered[(m.src, m.dst)]
  {
    var messages := MessagesHappenedBeforeM(trace, m, n);
    // assert forall m | m in messages :: m in trace(n).inTransit[(m.src, m.dst)] || m in trace(n).arrived[(m.src, m.dst)];
    // assert forall m':Message | m'.Unicast? && MessageInQueue(m', trace, n)
    //                           && ((m' in trace(n).arrived[(m'.src, m'.dst)] || m' in trace(n).inTransit[(m'.src, m'.dst)]) && HappensBefore(m', m)) :: m' in messages;

    // assert forall m':Message |  m'.Unicast? && MessageInQueue(m', trace, n)
    //                                      && HappensBefore(m', m) :: m' in messages || m' in trace(n).delivered[(m'.src, m'.dst)];
    MDelivered(trace, schedule, n, messages, m);
  }

}

ghost predicate MessageInQueue(m: Message, trace: Trace, n:nat)
  requires forall n' :: Valid(trace(n'))
  requires Valid(trace(n))
{
  && ValidMessage(m)
  && m in trace(n).arrived[(m.src, m.dst)] + trace(n).inTransit[(m.src, m.dst)] + trace(n).delivered[(m.src, m.dst)]
  && ChannelsAreDisjoint(trace, n)
}

// Find and return the message in the set that is minimal
lemma MinimalMessage(trace : Trace, messages: set<Message>, m: Message, n: nat)
  returns (minimalMsg:Message)
  requires messages != {}
  requires m.Unicast? && ValidUnicast(m)
  requires Valid(trace(n))
  requires forall n' :: Valid(trace(n'))
  requires forall m' | m' in messages :: m'.Unicast? && ValidUnicast(m')
  requires forall m':Message | m'.Unicast? && ValidUnicast(m') &&
                               (m' in trace(n).arrived[(m'.src, m'.dst)] || m' in trace(n).inTransit[(m'.src, m'.dst)]) :: HappensBefore(m', m) ==> m' in messages
  ensures minimalMsg in messages
  ensures !(exists m' | m' in messages && m'.Unicast? && ValidUnicast(m') :: HappensBefore(m', minimalMsg))
  ensures HappensBefore(minimalMsg, m)
  ensures Valid(trace(n))
  ensures MessageInQueue(minimalMsg, trace, n)

{
  var unseenMessages := messages;
  minimalMsg :| minimalMsg in messages;

  while(unseenMessages != {})
    // invariant !(exists m' | m' in messages - unseenMessages && m'.Unicast? && ValidUnicast(m') :: HappensBefore(m', minimalMsg))
    invariant minimalMsg in messages
  {
    var currentMsg :| currentMsg in unseenMessages;

    if(HappensBefore(currentMsg, minimalMsg)){
      minimalMsg := currentMsg;
    }

    // TODO lemma about happens before that if cuurent -> minimal and nothing in seen happened before minimal, it doesnt happen before current

    unseenMessages := unseenMessages - {currentMsg};
  }

  assume {:axiom} !(exists m' | m' in messages && m'.Unicast? && ValidUnicast(m') :: HappensBefore(m', minimalMsg));
  assume {:axiom} HappensBefore(minimalMsg, m);
  assume {:axiom} MessageInQueue(minimalMsg, trace, n);
}

// given a set of arrived messages that happened before m, at least one must have the property that everything that happened before it has been delivered
//TODO
// pick the smallest one in the set because if there were something smaller, it would also have to be in this happens before set

// return the set of messages that have not yet been delivered at n that happened before m
lemma MessagesHappenedBeforeM(trace: Trace, m: Message, n: nat)
  returns (messages : set<Message>)
  requires Valid(trace(n))
  requires m.Unicast? && ValidUnicast(m)
  requires m in trace(n).arrived[(m.src, m.dst)]
  ensures forall m':Message | m'.Unicast? && MessageInQueue(m', trace, n) &&
                              ((m' in trace(n).arrived[(m'.src, m'.dst)] || m' in trace(n).inTransit[(m'.src, m'.dst)]) && HappensBefore(m', m)) :: m' in messages
  ensures forall m' | m' in messages :: m'.Unicast? && ValidUnicast(m') && (m' in trace(n).arrived[(m'.src, m'.dst)] || m' in trace(n).inTransit[(m'.src, m'.dst)])
  // ensures m in messages
{
  messages := {};
  var allValidMs:iset<Message> := (iset m':Message | m'.Unicast? && ValidUnicast(m') && (m' in trace(n).arrived[(m'.src, m'.dst)] || m' in trace(n).inTransit[(m'.src, m'.dst)]) && HappensBefore(m', m) :: m');


  assume {:axiom} forall m':Message | m'.Unicast? && MessageInQueue(m', trace, n)
                                      && (m' in trace(n).arrived[(m'.src, m'.dst)] || m' in trace(n).inTransit[(m'.src, m'.dst)])
      :: HappensBefore(m', m) <==> m' in messages;
}

// TODO lemma that there are no cycles in happens before

predicate HappensBefore(m1: Message, m2: Message)
  requires m1.Unicast? && m2.Unicast?
  requires ValidUnicast(m1) && ValidUnicast(m2)
{
  && LessThan(m1.VC, m2.VC)
}

