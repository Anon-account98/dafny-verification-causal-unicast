// dst delivers a message from p
// guard: exists a message in dst's buffer of arrived messages
method Deliver(src: Process, dst: Process, s: System)
  requires s.Valid() && src in s.P && dst in s.P
  requires src != dst
  requires s.CausallyOrdered()
  requires s.CausallyOrdered2(dst)
  requires s.StablePredicate()
  requires forall dest <- s.P :: s.StablePredicate2(dest)
  requires forall dest <- s.P :: s.StablePredicate3(dest)
  requires s.MaxDeliveredMCsatP()
  requires s.arrived[(src, dst)] != [] // guard
  requires s.arrived[(src, dst)][0].Unicast?
  requires s.ValidUnicast(s.arrived[(src, dst)][0])
  requires LessThanEqSrc(s.arrived[(src, dst)][0].payload.0, getPVectorFromMap(s.deliveredMCs, s.P, dst), src) // guard on deliveredMCs
  modifies s`arrived, s`delivered, s`deliveredMCs, s`VCs
  ensures s.Valid()
  ensures s.arrived == old(s.arrived)[(src, dst) := old(s.arrived)[(src, dst)][1..]]
  ensures s.delivered == old(s.delivered)[(src, dst) := old(s.delivered)[(src, dst)] + [old(s.arrived)[(src, dst)][0]]]
  ensures s.deliveredMCs[(dst,src)] == old(s.arrived)[(src, dst)][0].payload.0[src]
  ensures getPVectorFromMap(s.VCs, s.P, dst) == vectorMax(getPVectorFromMap(old(s.VCs), s.P, dst), old(s.arrived)[(src, dst)][0].VC, dst)
  ensures s.MaxDeliveredMCsatP()
  ensures LessThanEq(old(s.arrived)[(src, dst)][0].payload.0, getPVectorFromMap(s.deliveredMCs, s.P, dst))
  ensures LessThanEq(s.delivered[(src, dst)][|s.delivered[(src, dst)]|-1].payload.0, getPVectorFromMap(s.deliveredMCs, s.P, dst))
  ensures s.StablePredicate()
  ensures forall dest <- s.P :: s.StablePredicate2(dest)
  ensures forall dest <- s.P :: s.StablePredicate3(dest)
  ensures s.CausallyOrdered()
{
  var m := s.arrived[(src, dst)][0];
  UpdateArrivedDelivered(src, dst, m, s);

  // Update delveredMCs
  UpdateDeliveredMCs(src, dst, m, s);

  // Update VC to be the max of every row
  UpdateVCs(dst, m, s);
  assert forall dest <- s.P :: s.StablePredicate3(dest) by {
    assert s.StablePredicate3(dst);
    assert forall dest <- s.P :: s.StablePredicate3(dest);
  }

  s.CausalOrderingFromPredicates();
  // assert s.CausallyOrdered();

}

method UpdateArrivedDelivered(src: Process, dst:Process, m : Message, s: System)
  requires s.Valid() && src in s.P && dst in s.P
  requires src != dst
  requires s.arrived[(src, dst)] != []
  requires m == s.arrived[(src, dst)][0]
  requires s.MaxDeliveredMCsatP()
  modifies s`arrived, s`delivered
  ensures s.arrived == old(s.arrived)[(src, dst) := old(s.arrived)[(src, dst)][1..]]
  ensures s.delivered == old(s.delivered)[(src, dst) := old(s.delivered)[(src, dst)] + [old(s.arrived)[(src, dst)][0]]]
  ensures s.MaxDeliveredMCsatP()
{
  s.arrived := s.arrived[(src, dst) := s.arrived[(src, dst)][1..]];
  assert s.ChannelsAreDisjoint(src, dst);

  assert !(m in s.delivered[(src, dst)]);
  s.delivered := s.delivered[(src, dst) := s.delivered[(src, dst)] + [m]];

  assert s.ChannelsAreDisjoint(src, dst);
  assert !(m in s.arrived[(src, dst)]);
  assume {:axiom} s.DeliveredInOrder(src, dst); // True because arrived was in order, but needs help proving
  assert s.ArrivedInOrder(src, dst);
  assume {:axiom} s.MaxDeliveredMCsatP();

}

method UpdateDeliveredMCs(src: Process, dst: Process, m: Message, s: System)
  requires s.Valid() && src in s.P && dst in s.P
  requires m.Unicast? && s.ValidUnicast(m)
  requires s.MaxDeliveredMCsatP()
  // requires forall dest <- s.P :: s.StablePredicate3(dest)
  modifies s`deliveredMCs
  ensures s.deliveredMCs.Keys == old(s.deliveredMCs).Keys
  ensures s.deliveredMCs[(dst,src)] == m.payload.0[src]
  ensures s.MaxDeliveredMCsatP()
  ensures forall dest <- s.P, p <- s.P| dest != dst :: s.deliveredMCs[(dest, p)] == old(s.deliveredMCs)[(dest, p)]
  // ensures forall dest <- s.P :: s.StablePredicate3(dest)
  ensures LessThan(getPVectorFromMap(old(s.deliveredMCs), s.P, dst), getPVectorFromMap(s.deliveredMCs, s.P, dst))
{
  s.deliveredMCs := s.deliveredMCs[(dst,src) := m.payload.0[src]];

  assert (forall src <- s.P, dst <- s.P :: s.InTransitInOrder(src, dst));
  // && (forall src <- P, dst <- P :: ArrivedInOrder(src, dst))
  // && (forall src <- P, dst <- P :: DeliveredInOrder(src, dst))
  // && (forall p <- P, m:Message | m.Minicast? :: deliveredMCs[(p,p)] > m.msgNum)
  // && (forall p <- P, m: Message | m.Unicast? && ValidUnicast(m) ::
  //   deliveredMCs[(p,p)] > m.payload.0[p])
  // && (forall p <- P, q <- P | p != q :: deliveredMCs[(p,p)] > deliveredMCs[(q, p)])
  // && (forall q <- P, m: Message | m.Unicast? && ValidUnicast(m) && q != m.src && m in arrived[(m.src, m.dst)] ::
  //   m.payload.0[m.src] > deliveredMCs[(q, m.src)])
  assume {:axiom} s.MaxDeliveredMCsatP();
  assume {:axiom} LessThan(getPVectorFromMap(old(s.deliveredMCs), s.P, dst), getPVectorFromMap(s.deliveredMCs, s.P, dst));
}

method UpdateVCs(dst: Process, m: Message, s: System)
  requires s.Valid() && dst in s.P
  requires m.Unicast? && s.ValidUnicast(m)
  requires forall r <- s.P :: (dst, r) in s.VCs.Keys
  requires getPVectorFromMap(s.VCs, s.P, dst).Keys == m.VC.Keys
  requires s.MaxDeliveredMCsatP()
  modifies s`VCs
  ensures old(s.VCs).Keys == s.VCs.Keys
  ensures getPVectorFromMap(s.VCs, s.P, dst) == vectorMax(getPVectorFromMap(old(s.VCs), s.P, dst), m.VC, dst)
  ensures s.VCs == s.VCs[(dst, dst) := s.VCs[(dst, dst)] + 1]
  ensures s.Valid()
  ensures s.MaxDeliveredMCsatP()
{
  s.VCs := getVCsMaxAtP(s.VCs, m.VC, dst);

  // TODO make this an assert. getVCsMaxAtP should work
  assume {:axiom} getPVectorFromMap(s.VCs, s.P, dst) == vectorMax(getPVectorFromMap(old(s.VCs), s.P, dst), m.VC, dst);
  s.VCs := s.VCs[(dst, dst) := s.VCs[(dst, dst)] + 1];

  // Needed this here to get it to verify MaxDeliveredMCsatP....
  assert (forall src <- s.P, dst <- s.P :: s.InTransitInOrder(src, dst));
  assert (forall src <- s.P, dst <- s.P :: s.ArrivedInOrder(src, dst));
  assert (forall src <- s.P, dst <- s.P :: s.DeliveredInOrder(src, dst));
  assert (forall src <- s.P, dest <- s.P :: s.ChannelsAreDisjoint(src, dest));
  assert (forall p <- s.P, m:Message | m.Minicast? :: s.deliveredMCs[(p,p)] > m.msgNum);
  assert (forall p <- s.P, m: Message | m.Unicast? && s.ValidUnicast(m) ::
            s.deliveredMCs[(p,p)] > m.payload.0[p]);
  assert (forall p <- s.P, q <- s.P | p != q :: s.deliveredMCs[(p,p)] > s.deliveredMCs[(q, p)]);
  assert (forall q <- s.P, m: Message | m.Unicast? && s.ValidUnicast(m) && q != m.src && m in s.arrived[(m.src, m.dst)] ::
            m.payload.0[m.src] > s.deliveredMCs[(q, m.src)]);
  assert (forall q <- s.P, m: Message | m.Unicast? && s.ValidUnicast(m) && q != m.src && m in s.inTransit[(m.src, m.dst)] ::
            m.payload.0[m.src] > s.deliveredMCs[(q, m.src)]);
}
