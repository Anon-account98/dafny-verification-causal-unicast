lemma {:isolate_assertions} MDelivered(trace: Trace, schedule: Schedule, n:nat, allMessagesBeforeM:set<Message>, m:Message)
  requires forall num:nat :: Valid(trace(num))
  requires FairSchedule(schedule)
  requires IsTrace(trace, schedule)
  requires Valid(trace(n))
  requires m.Unicast? && ValidUnicast(m)
  requires m in trace(n).arrived[(m.src, m.dst)]
  requires forall msg | msg in allMessagesBeforeM :: MessageInQueue(msg, trace, n) && msg.Unicast?
  requires forall m':Message | m'.Unicast? && ValidUnicast(m') &&
                               (m' in trace(n).arrived[(m'.src, m'.dst)] || m' in trace(n).inTransit[(m'.src, m'.dst)]) :: HappensBefore(m', m) ==> m' in allMessagesBeforeM
  requires forall m':Message |  m'.Unicast? && ValidUnicast(m') && ((m' in trace(n).inTransit[(m'.src, m'.dst)] || m' in trace(n).arrived[(m'.src, m'.dst)] || m' in trace(n).delivered[(m'.src, m'.dst)]))
                                && HappensBefore(m', m) :: m' in allMessagesBeforeM || m' in trace(n).delivered[(m'.src, m'.dst)]
  ensures exists n':nat | n' >= n && Valid(trace(n')) :: m in trace(n').delivered[(m.src, m.dst)]
{
  var messages := allMessagesBeforeM;
  var n' := n;
  assert MessageInQueue(m, trace, n');

  while (messages != {})
    invariant messages <= allMessagesBeforeM
    invariant n' >= n
    invariant Valid(trace(n'))
    invariant forall m':Message | m'.Unicast? && ValidUnicast(m') &&
                                  (m' in trace(n').arrived[(m'.src, m'.dst)] || m' in trace(n').inTransit[(m'.src, m'.dst)]) && HappensBefore(m', m) :: m' in messages
    invariant forall m | m in allMessagesBeforeM - messages :: m in trace(n').delivered[(m.src, m.dst)]
    invariant MessageInQueue(m, trace, n')
    decreases |messages|
  {
    assert forall m':Message | m'.Unicast? && ValidUnicast(m') &&
                                        (m' in trace(n').arrived[(m'.src, m'.dst)] + trace(n').inTransit[(m'.src, m'.dst)]) && HappensBefore(m', m) :: m' in messages;

    var minimalMsg := MinimalMessage(trace, messages, m, n');
    var n1 := n';

    n1 := MessageEventuallyDelivered(trace, schedule, minimalMsg, n');
    assert n1 >= n';
    assert minimalMsg in trace(n1).delivered[(minimalMsg.src, minimalMsg.dst)];


    assert minimalMsg in trace(n1).delivered[(minimalMsg.src, minimalMsg.dst)];
    assert n1 >= n;
    assert Valid(trace(n1));

    assert !(minimalMsg in trace(n1).inTransit[(minimalMsg.src, minimalMsg.dst)] + trace(n1).arrived[(minimalMsg.src, minimalMsg.dst)]) by {
      assert ChannelsAreDisjoint(trace, n1);
    }

    // assert forall m':Message | MessageInQueue(m, trace, n) :: MessageInQueue(m, trace, n1);
    // assert forall m':Message | MessageInQueue(m, trace, n) && m' in messages :: MessageInQueue(m, trace, n1);

    
    HappensBeforeMeansSentFirst(m, trace, n, n1);

    assert forall m':Message | m'.Unicast? && ValidUnicast(m') &&
                                        (m' in trace(n').arrived[(m'.src, m'.dst)] + trace(n').inTransit[(m'.src, m'.dst)]) 
                                        && HappensBefore(m', m) 
                                        :: (m' in trace(n).arrived[(m'.src, m'.dst)] + trace(n).inTransit[(m'.src, m'.dst)]);

    assert forall m':Message | m'.Unicast? && ValidUnicast(m') &&
                                        (m' in trace(n1).arrived[(m'.src, m'.dst)] + trace(n1).inTransit[(m'.src, m'.dst)]) && HappensBefore(m', m) :: m' in messages;

    assert forall m | m in allMessagesBeforeM - messages :: m in trace(n1).delivered[(m.src, m.dst)];

    assert MessageInQueue(m, trace, n1);


    n' := n1;

    assert minimalMsg in trace(n').delivered[(minimalMsg.src, minimalMsg.dst)];

    messages := messages - {minimalMsg};

    assert MessageInQueue(minimalMsg, trace, n');
    assert !(minimalMsg in trace(n').arrived[(minimalMsg.src, minimalMsg.dst)] + trace(n').inTransit[(minimalMsg.src, minimalMsg.dst)]);
  }

  assert forall m | m in allMessagesBeforeM :: m in trace(n').delivered[(m.src, m.dst)];
  assert MessageInQueue(m, trace, n');

  n' := MessageEventuallyDelivered(trace, schedule, m, n');
}


// If a message happened before m, it must have been sent first
lemma HappensBeforeMeansSentFirst(m: Message, trace: Trace, n:nat, n':nat)
  requires forall n' :: Valid(trace(n'))
  requires n <= n'
  requires MessageInQueue(m, trace, n) && m.Unicast?
  ensures forall m':Message | m'.Unicast? && ValidUnicast(m') 
                                        && (m' in trace(n').arrived[(m'.src, m'.dst)] + trace(n').inTransit[(m'.src, m'.dst)]) 
                                        && HappensBefore(m', m) 
                                          :: (m' in trace(n).arrived[(m'.src, m'.dst)] + trace(n).inTransit[(m'.src, m'.dst)])
{
  assume {:axiom} forall m':Message | m'.Unicast? && ValidUnicast(m') &&
                                        (m' in trace(n').arrived[(m'.src, m'.dst)] + trace(n').inTransit[(m'.src, m'.dst)]) 
                                        && HappensBefore(m', m) 
                                        :: (m' in trace(n).arrived[(m'.src, m'.dst)] + trace(n).inTransit[(m'.src, m'.dst)]);
}